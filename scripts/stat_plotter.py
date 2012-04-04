#!/usr/bin/python

import sys
import subprocess
import re
import time
import tempfile
import os

timeDataRE = re.compile("^(.*) t([0-9]+) at ([0-9]+): (.*)$")

tmpDataFile = tempfile.NamedTemporaryFile()

useLogScale = False
args = sys.argv[1:]
if args[0]=="-log":
    args = args[1:]
    useLogScale = True
vampCmdLine = args


nextLblIdx = 0
lblIndexes = {}
idxLbls = {}

def getLblIdx(lbl):
    global nextLblIdx
    global lblIndexes
    if lbl not in lblIndexes:
        lblIndexes[lbl] = nextLblIdx
        idxLbls[nextLblIdx] = lbl
        nextLblIdx = nextLblIdx + 1
    return lblIndexes[lbl]

data = {}
timePoints = []
def addDataPoint(lbl, t, v):
    global data
    global timePoints
    idx = getLblIdx(lbl)
    if t not in data:
        data[t]={}
        timePoints.append(t)
    data[t][idx]=v

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
            if idx not in dataLine:
                return False
            val = dataLine[idx]
            tmpDataFile.write("\t"+str(val))
        tmpDataFile.write("\n")
    tmpDataFile.flush()
    return True

gnuplotProc = subprocess.Popen(["gnuplot"], bufsize=1, stdin=subprocess.PIPE, shell=True)

if useLogScale:
    gnuplotProc.stdin.write("set logscale y\n")

def redrawGnuplot():
    global tmpDataFile
    global gnuplotProc
    global nextLblIdx
    global idxLbls
    
    gpCmd = "plot "
    first = True
    for idx in range(0,nextLblIdx):
        if first:
            first = False
        else:
            gpCmd += ", "
        dataIdx = str(idx+2)
        title = str(idxLbls[idx])
        gpCmd += "\""+tmpDataFile.name+"\" using 1:($"+dataIdx+") title \""+title+"\" with linespoints"
    
    gpCmd += "\n"
    gnuplotProc.stdin.write(gpCmd)
    gnuplotProc.stdin.flush()
    
    #subprocess.call(["cat",tmpDataFile.name])

vampProc = subprocess.Popen(vampCmdLine, bufsize=1, stderr=subprocess.PIPE)

while True:
    line = vampProc.stderr.readline()
    if not line:
        break
    mo = timeDataRE.match(line)
    if not mo:
        sys.stderr.write(line)
        continue
    lbl = mo.group(1)
    timePnt = mo.group(3)
    valPnt = mo.group(4)
    addDataPoint(lbl, timePnt, valPnt)
    if updateDataFile():
        redrawGnuplot()


time.sleep(0.25)
gnuplotProc.kill()