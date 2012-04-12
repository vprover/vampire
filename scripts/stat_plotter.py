#!/usr/bin/python

import sys
import subprocess
import re
import time
import tempfile
import os

timeDataRE = re.compile("^(.* t[0-9]+) at ([0-9]+): (.*)$")
labelRE = re.compile("^(.+) t([0-9]+)$")
lblDeclRE = re.compile("^stat: ([^ ]+) - (.+ t[0-9]+)$")
histogramSpecRE =re.compile("^[^ ]+@hist:[^ ]+$")

tmpDataFile = tempfile.NamedTemporaryFile()

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

def addLabel(specStr,lblStr):
    global nextLblIdx
    global lblIndexes
    global idxLbls
    global idx2HumanLabel
    global idxTypes
    if lblStr in lblIndexes:
        raise Exception("duplicate label: "+lblStr)
    lblIndexes[lblStr] = nextLblIdx
    idxLbls[nextLblIdx] = lblStr
    lblMO = labelRE.match(lblStr)
    if not lblMO:
        raise Exception("wrong label format: "+lblStr)
    idx2HumanLabel[nextLblIdx] = lblMO.group(1)
    type = "num"
    if histogramSpecRE.match(specStr):
        type = "hist"
        print "histogram: "+specStr
    idxTypes[nextLblIdx] = type
    nextLblIdx = nextLblIdx + 1
    

def getLblIdx(lbl):
    global lblIndexes
    if lbl not in lblIndexes:
        raise Exception("undeclared label: "+lbl)
    return lblIndexes[lbl]

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
            data[t][idx]=int(v)
    else:
        raise "not implemented"

def updateDataFile():
    """If the data rows aren't complete, returns False and the content of the file is undefined"""
    global tmpDataFile
    global data
    global timePoints
    global nextLblIdx
    tmpDataFile.truncate(0)
    for t in timePoints:
        tmpDataFile.write(str(t))
        dataLine = data[t]
        for idx in range(0,nextLblIdx):
            val = None
            if idx not in dataLine:
                val = "?"
            else:
                val = dataLine[idx]
            tmpDataFile.write("\t"+str(val))
        tmpDataFile.write("\n")
    tmpDataFile.flush()

gnuplotProc = subprocess.Popen(["gnuplot"], bufsize=1, stdin=subprocess.PIPE, shell=True)

if useLogScale:
    gnuplotProc.stdin.write("set logscale y\n")

def getIndexPlotStatement(idx):
    global idx2HumanLabel
    global tmpDataFile
    
    dataIdx = str(idx+2)
    title = idx2HumanLabel[idx]
    return "\""+tmpDataFile.name+"\" using 1:($"+dataIdx+") title \""+title+"\" with linespoints"
    

def buildPlotCommand(idxList):
    gpCmd = "plot "
    first = True
    for idx in idxList:
        if first:
            first = False
        else:
            gpCmd += ", "
        gpCmd += getIndexPlotStatement(idx)
    
    gpCmd += "\n"
    return gpCmd
    

def buildSimplePlotScript():
    global nextLblIdx
    return buildPlotCommand(range(0,nextLblIdx))

def buildGroupPlotScript():
    global plotGroups
    res = "set multiplot layout "+str(len(plotGroups))+",1\n"
    res += "unset title\n"
    
    for grp in plotGroups:
        res += buildPlotCommand(grp)
    res += "unset multiplot\n"
    return res

def buildPlotScript():
    global plotGroups
    if plotGroups:
        return buildGroupPlotScript()
    else:
        return buildSimplePlotScript()

def redrawGnuplot():
    global gnuplotProc
    
    gpCmd = buildPlotScript()
    gnuplotProc.stdin.write(gpCmd)
    gnuplotProc.stdin.flush()
    
    #subprocess.call(["cat",tmpDataFile.name])

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
            updateDataFile()
            redrawGnuplot()
            lastUpdateTime = curTime


updateDataFile()
redrawGnuplot()

time.sleep(0.25)
gnuplotProc.kill()