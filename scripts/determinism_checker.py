#!/usr/bin/python
"""
Will run two vampires in parallel and compare their output.
Attempts to change the memory alignment of the second vampire by
creating a lot of environment variables (this should make stack 
start from a different place in memory).

Command line:
[-p] [-a alternative_executable] executable arg1 ...

default alternative_executable is the same as executable

Runs in parallel
executable arg1 ...
alternative_executable arg1 ...
and prints out a message when their outputs start to differ.

"-p" will cause the outputs to be printed out even if they do not 
differ.

This script is particularly useful in combination with the "-tr"
options of Vampire which enable tracing ouputs. For example,
"-tr sa" prints out details of all newly generated, processed, 
activated and simplified clauses. List of all possible arguments
to the "-tr" option can be obtained by running "-tr help".

"""

import sys
import platform
import subprocess
import re
import time
import tempfile
import os
import math

vampCmdLine = None
printTraces = False
altExecutable = None
errFollowUpLines = 5

def readArgs(args):
    global vampCmdLine
    global printTraces
    global altExecutable
    
    while True:
        if args[0]=="-p":
            printTraces = True
            args = args[1:]
        if args[0]=="-a":
            altExecutable = args[1]
            args = args[2:]
        else:
            break
    vampCmdLine = args
    
class Finished(Exception):
    def __init__(self, msg):
        self.msg = msg

readArgs(sys.argv[1:])

def createVampProc(isSecond):
    global vampCmdLine
    global altExecutable
    
    childEnv = os.environ
    cmdLine = list(vampCmdLine)
    if isSecond:
        #we try to make the second Vampire behave differently, so we put some large stuff 
        #into the system environment, which could change the memory alignment a bit
        childEnv = dict(childEnv)
        s = "a"
        for i in range(0,12):
            s = s+s
        childEnv["abcd"] = s
        #we also use the alternative executable if it was supplied
        if altExecutable:
            cmdLine[0] = altExecutable
    try:
        return subprocess.Popen(cmdLine, bufsize=1, stderr=subprocess.PIPE, env=childEnv)
    except OSError:
        print "Command line giving error:"
        print cmdLine
        raise 

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
        
        if ln2[0:len(ln1)]==ln1 and vp1.poll():
            print "v1: %s" % trimEOL(ln1)
            print "v2: %s" % trimEOL(ln2)
            raise Finished("First vampire terminated in the middle of a line")
        if ln1[0:len(ln2)]==ln2 and vp2.poll():
            print "v1: %s" % trimEOL(ln1)
            print "v2: %s" % trimEOL(ln2)
            raise Finished("Second vampire terminated in the middle of a line")
            
        
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
    if vp1.poll()==None:
        vp1.kill()
    if vp2.poll()==None:
        vp2.kill()

