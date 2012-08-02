#!/usr/bin/env python
import sys, os, time, getopt 
from subprocess import Popen, list2cmdline
import subprocess
import argparse
import insertInv
import tempfile


def cpu_count():
    if sys.platform =="win32": 
        try:
            num = int(os.environ['NUMBER_OF_PROCESORS'])
        except(ValueError, KeyError):
            pass
    elif sys.platform == 'darwin':
        try: 
            num = int(os.popen('sysctl -n hw.ncpu').read())
        except ValueError:
            pass
    else: 
        try: 
            num = os.sysconf('SC_NPROCESSORS_ONLN')
        except (ValueError, OSError, AttributeError):
            pass
    return num

#insert here work for parallel
#def worker(q):
#    item = q.get()
#    os.system(item)
#    q.task_done()

#def execute_parallel(cmds):
#    no_cpu = cpu_count()
    

def execute_commands(cmds):
    # execute the commands in parallel (multiple processes), 
    # on as many CPU's we have

    if not cmds: return #the list of commands is empty
    def done(p):
        return p.poll() is not None
    def success(p):
        return p.returncode == 0
    def fail():
        sys.exit(1)

    max_tasks = cpu_count()
    processes = []
    while True:
        while cmds and len(processes)< max_tasks: 
            task = cmds.pop()
            #print list2cmdline(task)
            #processes.append(os.system(task))
            processes.append(subprocess.Popen(task, shell=True))
        for p in processes: 
            if done(p): 
                if success(p):
                    processes.remove(p)
                else:
                    fail()
        if not processes and not cmds: 
            break
        else: 
            time.sleep(0.05)

#parse the command line arguments and create an object containing all the information passed as command line

def createCommands(args):
    commnadLine = ""
    parser = argparse.ArgumentParser(description = "Annotate C code with invariants")
    parser.add_argument('analyzer', metavar = 'ANALYZER',
                        help= "analyzer executable ")
    parser.add_argument('input',metavar = 'INPUT-FILENAME',
                        help="input file to be processed. ")
    parser.add_argument("-o","--output",action="store",
                      dest="outputFile",
                      help="output filename -- default value: output.txt")
    parser.add_argument("-v","--verbose", action="store_true",dest="verbose")
    parser.add_argument("-t","--time_limit",action="store", type=int, 
                        dest="timeLimit",
                        help="time limit for invariant generation , default value 10 seconds")
    parser.add_argument("--fno","--function_number", action="store",type=int,
                        dest="funcNO",
                        help="number of the function you want to process, default value is 0 - all functions")
    parser.add_argument("--wno","--while_number",action="store",type=int,
                      dest="whileNO",
                      help="while to be processed, default value 1 (first while loop from each function, 0 = treat all the loops in a function) ")
    parser.add_argument("-p","--parallel",action="store",
                      dest="parallel",
                      help="parallel execution, default value false -- under test now")
    parser.add_argument("--vamp",action="store",default="false",
                      dest="vampire",
                      help="vampire executable, by default this option is deactivated ")
    arg = parser.parse_args(args)
    if arg.whileNO == None: 
        arg.whileNO = 1
    else: 
        whileNo = arg.whileNO
    if arg.timeLimit == None: 
        arg.timeLimit = 10
 
    if arg.funcNO == None:
        arg.funcNO = 0
    if arg.input == None:
        print "You must provide input file! "
        parser.print_help()
        sys.exit(1)
    if arg.analyzer == None:
        print "You must provide the analyzer!"
        parser.print_help()
        sys.exit(1)
    if arg.outputFile == None: 
        arg.outputFile = "output.txt"
    return arg

def createCom(arg,tempFileName):
    commandLine=""
    try:
        if arg.vampire == "false":
            commandLine = arg.analyzer +" -t " +str(arg.timeLimit)+ " -wno " + str(arg.whileNO) + " -fno "+ str(arg.funcNO)
            commandLine = commandLine + " " + arg.input + " | grep \"tff(inv\" | " + \
        "sed -e \"s/tff(inv[^,]*,//g\" | sed -e \"s/claim/loop invariant/g\" | sed -e \"s/\$sum/+/g\" " 
            commandLine = commandLine +" |sed -e \"s/\$uminus/#/g\" | sed -e \"s/-/#/g\" | sed -e \"s/\$lesseq/</g\" | sed -e \"s/\$greatereq/>/g\"" 
    #final step put it in the temporary OutputFile
    #modify it accordingly 
            commandLine = commandLine +  ">"+tempFileName
            os.system(commandLine)
        else:
            #create temporary file 
            intermT = tempfile.NamedTemporaryFile()
            commandLine = arg.analyzer +" -t " +str(arg.timeLimit)+ " -wno " + str(arg.whileNO) + " -fno "+ str(arg.funcNO)
            commandLine = commandLine + " " + arg.input +" | grep tff >"+ intermT.name 
            os.system(commandLine)
            intermS = tempfile.NamedTemporaryFile()
            #launch vampire with different strategies
            os.system("./symel.sh "+arg.vampire+" "+intermT.name+" "+intermS.name)
            commandLine = "cat "+intermS.name+ " | grep \"tff(inv\" | " + \
        "sed -e \"s/tff(inv[^,]*,//g\" | sed -e \"s/claim/loop invariant/g\" | sed -e \"s/\$sum/+/g\" " 
            commandLine = commandLine +" |sed -e \"s/\$uminus/#/g\" | sed -e \"s/-/#/g\" | sed -e \"s/\$lesseq/</g\" | sed -e \"s/\$greatereq/>/g\"" 
    #final step put it in the temporary OutputFile
    #modify it accordingly 
            commandLine = commandLine +  ">"+tempFileName
            os.system(commandLine)
            #close all temporary files created - this action also takes care of deleting them 
            intermT.close()
            intermS.close()
    except Exception,e:
        sys.exit(1)
    return commandLine 

#count the number of occurences of a string in an array of strings
def getNoOccurance(inst, arg):
    counter = 0
    for i in inst:
        if arg in i:
            counter = counter + 1
    return counter

#retrieve the while location in the original code ( does not take into account 
#the function number 
def whileLocation(inst, no):
    function = 0
    wno = 0 
    line = 0 
    for i in range(0, len(inst)):
        if "WHILE" in inst[i]:
            wno = wno +1 
            if no == wno : 
                w = inst[i].split(":")
                line = int(w[1])
                break
        elif "Function" in inst[i]:
            w = inst[i].split(":")
            function = int(w[1])
    return (function, line)

#retrieve the location of a specific while - takes into account the function number
def whileLocationInFun(inst, fn , wn ):
    function = 0
    wno = 0
    line = 0
    for i in range(0, len(inst)):
        if "Function" in inst[i]:
            function = function + 1
        if function == fn and "WHILE" in inst[i]:
            wno = wno + 1
            if wno == wn :
                t = inst[i].split(":")
                line = int(t[1])
                break
    return line

#counts the number of while structures in a function
def countWhilesInFunction(inst, funcNo):
    wno = 0 
    fno = 0
    done = False
    for x in range(0,len(inst)):
        if "Function" in inst[x]:
            fno = fno + 1
            if fno == funcNo:
                fno = x + 1
                break
    while not done: 
        if "WHILE" in inst[fno]:
            wno = wno + 1
            if len(inst)-1 == fno:
                break
            else:
                fno = fno + 1
        else:
            done = True
    
    return wno  
        
#process all the whiles in a specific function
def workAllWhiles(parsedCmd, funcNO, sourceOrganization, fin,fout, start ):
    done = False
    print "function number: ", funcNO 
    
    WN=1
    while not done: 
        tempF = tempfile.NamedTemporaryFile()
        parsedCmd.whileNO = WN
        parsedCmd.funcNO = funcNO
        command = createCom(parsedCmd, tempF.name)
        #os.system(command)
        tempF.seek(0)
        invariant = tempF.readlines()
        tempF.close()
        invariantI = insertInv.work(invariant)
        for x in invariantI : 
            fout.write(x)
        WN = WN + 1
        stop = whileLocationInFun(sourceOrganization, funcNO, WN) 
        if stop == 0 :
            done = True
        else: 
            for i in range(start-1, stop-1):
                fout.write(fin[i])
            start = stop
        # in case there is more write the rest of the file
    print start
    return start

from os import path
#main like function to run all depending on the strategy created
def runAccordingToOptions(args):
    parsedCmd = createCommands(args)
    noFunc = 0
    if not path.exists(parsedCmd.analyzer) :
        print "There is no such file ", parsedCmd.analyzer
        sys.exit(1)
    if not path.exists(parsedCmd.input) or not path.isfile(parsedCmd.input):
        print "The input does not exist, or is not a file", parsedCmd.input
        sys.exit(1)
    with tempfile.NamedTemporaryFile() as tf:
    #in case of analyzing all the functions from the file, get the number of functions
        p = subprocess.Popen((parsedCmd.analyzer+" -wno -1 "+parsedCmd.input).split(), stdout = subprocess.PIPE, stderr=subprocess.PIPE)
        outp,err = p.communicate()
        if err != "":
            print err
            sys.exit(-1)
        else:
            ff = outp.split("\n")
        if parsedCmd.verbose == True:
            print outp
        
        sourceOrganization = []
        for x in ff : 
            if "WHILE LOCATION:" in x:
                sourceOrganization.append(x)
            elif "Function number:" in x:
                sourceOrganization.append(x)
    #occurences of while 
    noWhiles = getNoOccurance(sourceOrganization, "WHILE")
    #number of functions 
    noFunctions = getNoOccurance(sourceOrganization, "Function")
    #read the input C file
    f = open(parsedCmd.input,"r")
    fin = f.readlines()
    f.close()
    #store all the information in fin
    #the case when you request a specific function and a specific while loop
    if parsedCmd.whileNO != 0 and parsedCmd.funcNO != 0:
        tempF = tempfile.NamedTemporaryFile()
        command = createCom(parsedCmd,tempF.name)
        #read output and transform it and annotate the code 
        whileLoc = whileLocationInFun(sourceOrganization,parsedCmd.funcNO, parsedCmd.whileNO)
        tempF.seek(0)
        invs = tempF.readlines()
        if len(invs) == 0:
            print "Something went wrong... try change the timelimit, or the while number!"
            sys.exit(-1)
        invariant = insertInv.work(invs)
        tempF.close()
        fout = open(parsedCmd.outputFile,"w")
        for i in range(0, whileLoc-1):
            fout.write(fin[i])
        for x in invariant:
            fout.write(x)
        for i in range(whileLoc-1,len(fin)):
            fout.write(fin[i])
        fout.close()
    #case when you treat a specific function but all the whiles contained
    if parsedCmd.funcNO != 0 and parsedCmd.whileNO == 0:
        fout = open(parsedCmd.outputFile, "w")
        WN=1
        start =  whileLocationInFun(sourceOrganization, parsedCmd.funcNO, WN)
        for i in range(0,start-1):
            fout.write(fin[i])
        stop = workAllWhiles(parsedCmd, parsedCmd.funcNO, sourceOrganization, fin, fout, start)
        for i in range(stop-1, len(fin)):
            fout.write(fin[i])
        fout.close()

    #all functions and all whiles should be treated
    if parsedCmd.funcNO == 0 and parsedCmd.whileNO == 0:
        fout = open(parsedCmd.outputFile, "w")
        WN=1
        FNO = 1 
        noFN = getNoOccurance(sourceOrganization, "Function")
        start =  whileLocationInFun(sourceOrganization, FNO, WN)
        for i in range(0,start-1):
            fout.write(fin[i])
        s=0
        for x in range(1, noFN+1):
            s =  workAllWhiles(parsedCmd, x, sourceOrganization, fin, fout, start)
            start = whileLocationInFun(sourceOrganization, x+1, 1)
            if start != 0:
                for i in range(s-1, start-1):
                    fout.write(fin[i])
            
        for i in range(s-1, len(fin)):
            fout.write(fin[i])
        fout.close()
    #all functions special while
    if parsedCmd.funcNO == 0 and parsedCmd.whileNO != 0:
        noFN = getNoOccurance(sourceOrganization, "Function")
        start = whileLocationInFun(sourceOrganization, 1, parsedCmd.whileNO)
        if start == 0: 
            print "ERROR: there is no such while in function 1! try another one!"
            sys.exit(-1)
        fout = open(parsedCmd.outputFile, "w")
        for i in range(0, start-1):
            fout.write(fin[i])
        for i in range(1, noFN+1):
            tempF = tempfile.NamedTemporaryFile()
            parsedCmd.funcNO = i
            command = createCom(parsedCmd, tempF.name)
            #os.system(command)
            tempF.seek(0)
            inv = tempF.readlines()
            tempF.close()
            if len(inv)==0:
                print "Error: the while you try to analyze does not exist, functio: ", i
                sys.exit(-1)
            invariant = insertInv.work(inv)
            for x in invariant: 
                fout.write(x)
            stop = whileLocationInFun(sourceOrganization, i+1, parsedCmd.whileNO)
            if stop == 0:
                for t in range(start-1, len(fin)):
                    fout.write(fin[t])
            else:
                for t in range(start-1, stop-1):
                    fout.write(fin[t])
            start = stop 


if __name__ == '__main__':
    runAccordingToOptions(sys.argv[1:])
