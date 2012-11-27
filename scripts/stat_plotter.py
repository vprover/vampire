#!/usr/bin/python

#
# see https://docs.google.com/document/pub?id=1vsmC80shh7qCpwgaNTrLzRyz61I0BZWJFvIqiE9yIG8
# for documentation
#

import sys
import platform
import subprocess
import re
import time
import tempfile
import os
import math

timeDataRE = re.compile("^(.* t[0-9]+) at ([0-9]+): (.*)$")
labelRE = re.compile("^(.+) t([0-9]+)$")
lblDeclRE = re.compile("^stat: ([^ ]+) - (.+ t[0-9]+)$")
histogramSpecRE = re.compile("^[^ ]+@hist:[^ ]+$")
histSegmentRE = re.compile("^ *([0-9]+): ([0-9]+)")

tmpDataFile = tempfile.NamedTemporaryFile()
tmpHistFiles = []

useLogScale = False
vampCmdLine = None
plotGroups = None

def readPlotGroups(spec):
    """plot groups specification contain statistic indexes separated by commas in groups separated by semicolons"""
    grps=spec.split(";")
    res=[]
    for g in grps:
        idxStrings = g.split(",")
        gContent = map(int, idxStrings)
        res.append(gContent)
    return res

def readArgs(args):
    global useLogScale
    global plotGroups
    global vampCmdLine
    
    locArgsEnd = False
    while not locArgsEnd:
        if args[0]=="-log":
            useLogScale = True
            args = args[1:]
        elif args[0]=="-g":
            plotGroups = readPlotGroups(args[1])
            args = args[2:]
        else:
            locArgsEnd = True
    vampCmdLine = args
    for i in range(0,len(vampCmdLine)):
        if vampCmdLine[i]=="-tr":
            vampCmdLine[i+1] = "stat_labels,"+vampCmdLine[i+1]

readArgs(sys.argv[1:])

nextLblIdx = 0
lblIndexes = {}
idxLbls = {}
idx2HumanLabel = {}
# types:
#   num  - usual numbers
#   hist - histograms
idxTypes = {}
histIndexes = []
histTmpFiles = {}
histMaxCounts = {}
histMaxKeys = {}

def addLabel(specStr,lblStr):
    global nextLblIdx
    global lblIndexes
    global idxLbls
    global idx2HumanLabel
    global idxTypes
    global histIndexes
    global histTmpFiles
    global histMaxCounts
    if lblStr in lblIndexes:
        raise Exception("duplicate label: "+lblStr)
    
    newIdx = nextLblIdx
    nextLblIdx = nextLblIdx + 1
     
    lblIndexes[lblStr] = newIdx
    idxLbls[newIdx] = lblStr
    lblMO = labelRE.match(lblStr)
    if not lblMO:
        raise Exception("wrong label format: "+lblStr)
    idx2HumanLabel[newIdx] = lblMO.group(1)
    type = "num"
    if histogramSpecRE.match(specStr):
        type = "hist"
        histIndexes.append(newIdx)
        histTmpFiles[newIdx] = tempfile.NamedTemporaryFile()
        #histTmpFiles[newIdx] = open("/work/Dracula/pdata.txt","w")
        histMaxCounts[newIdx] = 0
        histMaxKeys[newIdx] = 0
        
    idxTypes[newIdx] = type
    
    

def getLblIdx(lbl):
    global lblIndexes
    if lbl not in lblIndexes:
        raise Exception("undeclared label: "+lbl)
    return lblIndexes[lbl]

def readHistData(histIdx,val):
    global histMaxCounts
    global histMaxKeys
    res = {}
    if val=="":
        return res
    segments = val.split(",");
    for seg in segments:
        mo = histSegmentRE.match(seg)
        if not mo:
            raise Exception("invalid segment: \""+seg+"\" in "+val)
        key = int(mo.group(1))
        ctr = int(mo.group(2))
        if key in res:
            raise Exception("duplicate key "+key+" in "+val)
        res[key]=ctr
        if ctr>histMaxCounts[histIdx]:
            histMaxCounts[histIdx] = ctr
        if key>histMaxKeys[histIdx]:
            histMaxKeys[histIdx] = key
    return res

#map from time points to map from indexes to data
data = {}
timePoints = []
def addDataPoint(lbl, t, v):
    global data
    global timePointsSet
    global timePoints
    global idxTypes
    idx = getLblIdx(lbl)
    if t not in data:
        data[t]={}
        timePoints.append(t)
    type = idxTypes[idx]
    if type=="num":
        if v!="?":
            data[t][idx]=float(v)
    elif type=="hist":
        data[t][idx]=readHistData(idx,v)
    else:
        raise "not implemented"

def outputHistFile(idx,f):
    global data
    global timePoints
    global histMaxKeys
    domEls = None
    if False:
        dom = set()
        for t in timePoints:
            if idx not in data[t]:
                continue
            distr = data[t][idx]
            dom.update(distr.keys())
        domEls = []
        domEls.extend(dom)
        domEls.sort()
    else:
        domEls = range(0,histMaxKeys[idx])
    
    f.seek(0)
    f.truncate()
    for el in domEls:
        for t in timePoints:
            if idx not in data[t]:
                continue
            distr = data[t][idx]
            if el in distr:
                f.write(str(distr[el])+"\t")
            else:
                f.write("0\t")
        f.write("\n")
    f.flush()

def updateDataFiles():
    """populate data files for graphs and histograms"""
    global tmpDataFile
    global data
    global timePoints
    global nextLblIdx
    global histIndexes
    global histTmpFiles
    global idxTypes
    tmpDataFile.truncate(0)
    for t in timePoints:
        tmpDataFile.write(str(t))
        dataLine = data[t]
        for idx in range(0,nextLblIdx):
            val = None
            if idxTypes[idx]!="num":
                val = "?"
            elif idx not in dataLine:
                val = "?"
            else:
                val = dataLine[idx]
            tmpDataFile.write("\t"+str(val))
        tmpDataFile.write("\n")
    tmpDataFile.flush()
    
    for hidx in histIndexes:
        tf = histTmpFiles[hidx]
        outputHistFile(hidx, tf)
        tf.flush()

gnuplotProc = subprocess.Popen(["gnuplot"], bufsize=1, stdin=subprocess.PIPE, shell=True)

if useLogScale:
    gnuplotProc.stdin.write("set logscale y\n")

def getIndexPlotStatement(idx):
    global idx2HumanLabel
    global tmpDataFile
    global idxTypes

    assert idxTypes[idx]=="num"
    
    dataIdx = str(idx+2)
    title = idx2HumanLabel[idx]
    return "\""+tmpDataFile.name+"\" using 1:($"+dataIdx+") title \""+title+"\" with linespoints"
    
    
def buildHistPaletteCmd(idx):
    global histMaxCounts
    maxVal = histMaxCounts[idx]
    if maxVal<2:
        return ['set palette defined (0 "white", 1 "black")']
    if maxVal<10:
        return ['set palette defined (0 "white", 1 "black", %d "red")' % maxVal]
    low = math.sqrt(maxVal)
    high = maxVal/2
    return ['set palette defined (0 "white", 1 "black", %d "purple", %d "red", %d "yellow")' % (low, high, maxVal)]

def buildHistRangeCmd(idx):
    global timePoints
    global histMaxKeys
    res = ["set xrange [-0.5:%d]" % (len(timePoints)+0.5),
           "set yrange [-0.5:%d]" % (histMaxKeys[idx]+0.5)]
    return res

def buildHistPlotCommand(idx):
    global histTmpFiles
    global idx2HumanLabel
    global idxTypes

    assert idxTypes[idx]=="hist"
    
    fname = histTmpFiles[idx].name
    title = idx2HumanLabel[idx]
    res = []
    res.extend(buildHistPaletteCmd(idx))
    res.extend(buildHistRangeCmd(idx))
    res.append("plot \""+fname+"\" matrix with image title \""+title+"\"")
    return res

def buildPlotCommand(idxList):
    global idxTypes
    
    if len(idxList)==1 and idxTypes[idxList[0]]=="hist":
        return buildHistPlotCommand(idxList[0])
    
    res = []
    res.append("set xrange [*:*]")
    res.append("set yrange [*:*]")

    mainCmd = "plot "
    first = True
    for idx in idxList:
        if idxTypes[idx]=="hist":
            raise Exception("histogram statistics must be in their own group")
        if first:
            first = False
        else:
            mainCmd += ", "
        mainCmd += getIndexPlotStatement(idx)
    res.append(mainCmd)
    return res

def buildGroupPlotScript(grps):
    res = []
    if len(grps)==1:
        res.extend(buildPlotCommand(grps[0]))
    else:
        res.append("set multiplot layout "+str(len(grps))+",1")
        res.append("unset title")
        
        for grp in grps:
            res.extend(buildPlotCommand(grp))
        res.append("unset multiplot")
    return res

def buildPlotScript():
    global plotGroups
    global nextLblIdx
    global idxTypes
    global histIndexes
    
    grps = plotGroups
    if not grps:
        grps = [[x for x in range(0,nextLblIdx) if idxTypes[x]=="num" ]]
        if len(grps[0])==0:
            grps = []
    if histIndexes:
        grps.extend([[x] for x in histIndexes])
    return buildGroupPlotScript(grps)

def redrawGnuplot():
    global gnuplotProc
    
    gpCmds = buildPlotScript()
    gpCmd = "\n".join(gpCmds)+"\n"
    gnuplotProc.stdin.write(gpCmd)
    gnuplotProc.stdin.flush()
    
vampProc = subprocess.Popen(vampCmdLine, bufsize=1, stderr=subprocess.PIPE)

lastUpdateTime = None

while True:
    line = vampProc.stderr.readline()
    if not line:
        break
    mo = lblDeclRE.match(line)
    if mo:
        addLabel(mo.group(1),mo.group(2))
        continue
    mo = timeDataRE.match(line)
    if not mo:
        sys.stderr.write(line)
        continue
    lbl = mo.group(1)
    timePnt = mo.group(2)
    valPnt = mo.group(3)
    addDataPoint(lbl, timePnt, valPnt)

    curTime = time.time()
    if len(timePoints)>3:
        if lastUpdateTime==None or curTime-lastUpdateTime>0.3:
            updateDataFiles()
            redrawGnuplot()
            lastUpdateTime = curTime


updateDataFiles()
redrawGnuplot()

time.sleep(0.25)

if platform.system()=="Linux":
	sys.stdin.readline()

gnuplotProc.kill()
