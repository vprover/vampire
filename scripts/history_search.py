#!/opt/local/bin/python3.2
#!/usr/bin/python
"""
Will find a svn revision that is the last to give a specified output

Command line:
[-f first_revision] [-l last_revision] [-d regex] executable arg1 ...

default first_revision is 1500
default last_revision is the current one
default regex is "Refutation found."

Looks for the latest revision for which the output of
executable arg1 ...
contains line that matches regex.
"""

import sys
import platform
import subprocess
import re
import time
import tempfile
import os
import math

DEVNULL = open('/dev/null', 'w')

revisionRE = re.compile("^Revision: ([0-9]+)$")


def getCmdResult(cmdLine):
    """return output of a command in a string"""
    res = None
    try:
        resBytes = subprocess.check_output(cmdLine, stderr=subprocess.STDOUT)
    except subprocess.CalledProcessError as e:
        resBytes = e.output
    return str(resBytes,encoding="ascii")

def execCmd(cmdLine, report):
    if report:
        cmdStr = " ".join(cmdLine)
        print(cmdStr, end="... ")
        sys.stdout.flush()
    res = subprocess.call(cmdLine, stderr=DEVNULL, stdout=DEVNULL)
    #res = subprocess.call(cmdLine)
    if report:
        print("done")
        
    return res==0

def getFirstMatch(linesStr, regex, fullMatch):
    lines = linesStr.split("\n")
    for line in lines:
        mo = None
        if fullMatch:
            mo = regex.match(line)
        else:
            mo = regex.search(line)
        if mo:
            return mo
    return None

class Failure(Exception):
    def __init__(self, msg):
        self.msg = msg


def getCurrentRevision():
    infoOut = getCmdResult(["svn", "info"])
    revMO = getFirstMatch(infoOut, revisionRE, True)
    if revMO==None:
        raise Failure("SVN repository not found")
    revStr = revMO.group(1)
    return int(revStr)


vampCmdLine = None
buildTgt = "vampire"
desiredRE = re.compile("Refutation found.")
#firstRevision = 1400
firstRevision = 1500
lastRevision = None

def readVampCmdLine(args):
    global vampCmdLine
    global buildTgt
    
    vampCmdLine = args
    
    execFile = vampCmdLine[0]
    absExec = os.path.abspath(execFile)
    repositoryPath,fname = os.path.split(absExec)
    
    buildTgt = fname
    relExec = "./"+fname
    vampCmdLine[0] = relExec
    print("repository path: ", repositoryPath)
    os.chdir(repositoryPath)
    

def readArgs(args):
    global vampCmdLine
    global desiredRE
    global firstRevision
    global lastRevision
    
    while True:
        if args[0]=="-f":
            firstRevision = int(args[1])
            args = args[2:]
        elif args[0]=="-l":
            lastRevision = int(args[1])
            args = args[2:]
        elif args[0]=="-d":
            desiredRE = re.compile(args[1])
            args = args[2:]
        else:
            break
    readVampCmdLine(args)
    if lastRevision==None:
        lastRevision = getCurrentRevision()

def switchToRevision(revNum):
    global buildTgt
    
    if not execCmd(["svn","update","-r",str(revNum)], True):
        raise Failure("failed: svn update")
    if not execCmd(["make","depend"], True):
        raise Failure("failed: svn update")
    if not execCmd(["make","-j","2",buildTgt], True):
        raise Failure("failed: make %s" % buildTgt)

def checkSuccess():
    global vampCmdLine
    global desiredRE
    
    vampOut = getCmdResult(vampCmdLine)
    print(vampOut)
    mo = getFirstMatch(vampOut, desiredRE, False)
    return mo!=None


readArgs(sys.argv[1:])

print('Looking for regex "%s" in outputs of %s between revisions %d and %d' % 
      (desiredRE.pattern, buildTgt, firstRevision, lastRevision))

switchToRevision(lastRevision)
if checkSuccess():
    print ("The final revision %s succeeded" % lastRevision)
    sys.exit(0)
switchToRevision(firstRevision)
if not checkSuccess():
    print ("The fist revision %s did not succeed" % firstRevision)
    sys.exit(1)

minRev = firstRevision
maxRev = lastRevision-1
while minRev!=maxRev:
    assert minRev<maxRev
    mid = (minRev+maxRev+1)//2
    assert mid<=maxRev
    assert mid>minRev
    
    switchToRevision(mid)
    if checkSuccess():
        minRev = mid
    else:
        maxRev = mid-1
assert minRev==maxRev
resultRev = minRev
if getCurrentRevision()!=resultRev:
    switchToRevision(resultRev)
print('The last revision where regex "%s" is in outputs of %s is %d' % 
      (desiredRE.pattern, buildTgt, resultRev))
    
    