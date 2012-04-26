#!/usr/bin/python

import sys
import platform
import subprocess
import re
import time
import tempfile
import os
import math

tmpDataFile = tempfile.NamedTemporaryFile()
tmpHistFiles = []

vampCmdLine = None
printTraces = False
errFollowUpLines = 5

def readArgs(args):
    global printTraces
    global vampCmdLine
    
    while True:
        if args[0]=="-p":
            printTraces = True
            args = args[1:]
        else:
            break
    vampCmdLine = args
    
class Finished(Exception):
    def __init__(self, msg):
        self.msg = msg

readArgs(sys.argv[1:])

def createVampProc(blowUpEnviron):
    childEnv = os.environ
    if blowUpEnviron:
        childEnv = dict(childEnv)
        s = "a"
        for i in range(0,12):
            s = s+s
        childEnv["abcd"] = s
    return subprocess.Popen(vampCmdLine, bufsize=1, stderr=subprocess.PIPE, env=childEnv)

def trimEOL(str):
    if str[-1]=="\n":
        return str[:-1]
    else:
        return str

def printFollowUp(hdr, firstLine, proc):
    global errFollowUpLines
    
    print "%s: %s" % (hdr, trimEOL(firstLine))
    for i in range(0,errFollowUpLines):
        ln = proc.stderr.readline()
        if not ln:
            print "%s terminated" % hdr
            break
        print "%s: %s" % (hdr, trimEOL(ln))


vp1 = createVampProc(False)
vp2 = createVampProc(True)

try:
    while True:
        ln1 = vp1.stderr.readline()
        ln2 = vp2.stderr.readline()
        
        if ln1==ln2:
            if not ln1:
                raise Finished("Both vampires terminated")
            
            if printTraces:
                print trimEOL(ln1)
            
            continue
        if not ln1:
            raise Finished("First vampire terminated")
        if not ln2:
            raise Finished("Second vampire terminated")
        
        print "Vampire outputs differ:"
        print
        print "v1: %s" % trimEOL(ln1)
        print "v2: %s" % trimEOL(ln2)
        
        if errFollowUpLines:
            print
            printFollowUp("v1", ln1, vp1)
            print
            printFollowUp("v2", ln2, vp2)
        print
        raise Finished("Non-determinism detected")
except Finished as e:
    print e.msg
finally:
    vp1.kill()
    vp2.kill()

