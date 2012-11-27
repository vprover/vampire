#!/usr/bin/python

import fileinput
import os
import re


printLatex = os.getenv("PRINT_LATEX", "ON")=="ON"

#if variable is set, benchmark names will be restricted only to those appearing in the specified file
restrFName = os.getenv("RESTRICTING_FILE", "")


reIgnoredLine = re.compile("(%)|(sh: line 1: .* Alarm clock)|(Unknown reason of termination!)|(Alarm clock)")
benchSep = re.compile("========$")

reName =  re.compile("results for (.*)$")
reIgnoredName = re.compile(".*\?")
reKindExtractor = re.compile("../cpa/interpolation/([^/]*)/.*")

reOldItp =  re.compile("Old interpolant:")
reSzMinItp =  re.compile("Interpolant:")
reCntMinItp =  re.compile("Count minimized interpolant:")
reQuantMinItp =  re.compile("Quantifiers minimized interpolant:")

reSEGV = re.compile("Aborted by signal SIGSEGV")

reTimeOut = re.compile("(External time out \(SIGXCPU\))|(Time limit reached!)|(Aborted by signal SIGXCPU)")
reOutOfMem = re.compile("Memory limit exceeded!")

reSubvampireFailReport = re.compile("(Time limit reached!)|(Memory limit exceeded!)")

reMinimErrorLines = re.compile('(SMT solver gave "unknown" for cost value)'+
                               '|(Error: Undefined name "-2147483648.0".)'+
                               '|(cost overflow durint SMT minimization)')
reApproxVal = re.compile("Minimization gave approximate result")
reMinimFail = re.compile("Minimization timed failed to find a satisfiable assignment, generating basic interpolant") 

reOrigWeight = re.compile("Original interpolant weight cost: ([0-9]*)$")
reMinWeight = re.compile("Minimized interpolant weight cost: ([0-9]*)$")
reOrigCount = re.compile("Original interpolant count cost: ([0-9]*)$")
reMinCount = re.compile("Minimized interpolant count cost: ([0-9]*)$")
reOrigQuant = re.compile("Original interpolant quantifiers cost: ([0-9]*)$")
reMinQuant = re.compile("Minimized interpolant quantifiers cost: ([0-9]*)$")

intInfty = 10000000000000000

trSkipped = "Skipped"
trTimeOut = "TO"
trOutOfMem = "MO"
trCannotMakeLocal = "CML"
trCannotColor = "CCL"
trMinimFail = "Fail"
trSolvSegf = "SlvSEG"
trNotSolved = "NS"
trAprox = "Aprox"

class IncompleteBenchmark(Exception):
        pass
class ProcError(Exception):
        def __init__(self, value):
                self.value = value
        def __str__(self):
                return repr(self.value)
class EarlyRecEnd(Exception):
        def __init__(self, reason):
                self.reason = reason
        def __str__(self):
                return repr(self.reason)

class LookAheadIterator(object):
        def __init__(self,obj):
                self.it = obj.__iter__()
                self.reserve = []
        def __iter__(self):
                return self
                
        def hasNext(self):
                if self.reserve:
                        return True
                try:
                        next = self.it.next()
                        self.reserve.append(next)
                        return True
                except StopIteration:
                        return False
        def next(self):
                if self.reserve:
                        res = self.reserve[-1]
                        self.reserve = self.reserve[:-1]
                        return res
                return self.it.next()
        def peek(self):
                if self.reserve:
                        return self.reserve[-1]
                res = self.next()
                self.reserve.append(res)
                return res
                        

def getMatch(strList,regex):
        for s in strList:
                mo = regex.match(s)
                if mo:
                        return mo
        return None

def updateCounter(ctr,val):
        if val in ctr:
                ctr[val] += 1
        else:
                ctr[val] = 1

def outputTable(labels,maps,lblCnt,keyLst):
        for i in range(0,lblCnt):
                print "\t",
        for k in keyLst:
                print k, "\t",
        print

        cnt = len(labels)
        for i in range(0,cnt):
                print labels[i],"\t",
                m = maps[i]
                for k in keyLst:
                        if k in m:
                                print m[k],
                        print "\t",
                print
        print
def outputTableLatex(labels,maps,lblCnt,keyLst):
        print "\\begin{tabular}{",
        for i in range(0,lblCnt):
                print "l ",
        for k in keyLst:
                print "r ",
        print "}"
        
        for i in range(0,lblCnt-1):
                print "\t&",
        for k in keyLst:
                print "\t&",k,
        print "\\\\"

        cnt = len(labels)
        for i in range(0,cnt):
                print labels[i][0],
                for l in labels[i][1:]:
                        print "\t&",l,
                m = maps[i]
                for k in keyLst:
                        print "\t&",
                        if k in m:
                                print m[k],
                print "\\\\"
        print "\\end{tabular}"
        print

def printTable(labels,maps,lblCnt=1):
        keys = set()
        for m in maps:
                keys.update(m.keys())
        keyLst = list(keys)
        
        def getSortKey(k):
                if not isinstance(k,str):
                        return k
                if k=="TO":
                        return "zzzz"
                ks = k.split()
                v = ks[0]
                try:
                        nv = int(v)
                        return nv
                except ValueError:
                        return v
        
        def keyCmp(k1,k2):
                return cmp(getSortKey(k1),getSortKey(k2))
                
        
        keyLst.sort(keyCmp)
        
        if printLatex:
                outputTableLatex(labels,maps,lblCnt,keyLst)
        else:
                outputTable(labels,maps,lblCnt,keyLst)

restrNameSet = None
if restrFName:
    restrNameSet = set()
    f = open(restrFName, 'r')
    for line in f:
        line = line.strip('\n')
        restrNameSet.add(line)
def isHeadLineAllowed(nm):
    if not restrNameSet:
        return True
    return nm in restrNameSet

class Bench(object):
        def __init__(self):
                self.lines = []
                self.name = None
                self.kind = None
                
                #the ones below contain true if they are approximate or error
                self.origSz = None
                self.origCnt = None
                self.origQuant = None
                self.minSz = None
                self.minCnt = None
                self.minQuant = None
        def addLine(self,line):
                self.lines.append(line)
        def markRemaining(self,reason):
                for fld in self.__dict__:
                        if self.__dict__[fld]==None:
                                self.__dict__[fld] = (reason, True)
        
        def checkForResLimits(self, line):
                if reTimeOut.match(line):
                        raise EarlyRecEnd(trTimeOut)
                if reOutOfMem.match(line):
                        raise EarlyRecEnd(trOutOfMem)
        def readValue(self, iter, valRegex, valName):
                approx = False
                for line in iter:
                        self.checkForResLimits(line)
                        if reMinimErrorLines.match(line) or reApproxVal.match(line):
                                approx = True
                                continue
                        
                        resVal = None
                        if reMinimFail.match(line):
                                resVal = trMinimFail
                                approx = True
                        else:    
                                matchObj = valRegex.match(line)
                                if not matchObj:
                                        raise ProcError("unrecognized line: "+line)
                                resVal = int(matchObj.group(1))
                        self.__dict__[valName] = (resVal, approx)
                        return
                raise IncompleteBenchmark()
        def tryAcceptInterpolant(self, iter, valRegex):
                approx = False
                if not iter.hasNext():
                    return False
                line = iter.peek()
                self.checkForResLimits(line)
                if not valRegex.match(line):
                        return False
                        #raise ProcError("expected '"+valRegex.pattern+"' line: "+line)
                iter.next()
                return True
        def readName(self, line):
                nameMatch = reName.match(line)
                if not nameMatch:
                        raise ProcError("no name match")
                self.name = nameMatch.group(1)
                kindMatch = reKindExtractor.match(self.name)
                if kindMatch:
                        self.kind = kindMatch.group(1)
                if not isHeadLineAllowed(line):
                    raise EarlyRecEnd(trSkipped)
        def process(self):
                try:
                        lineIt = LookAheadIterator(self.lines)
                        self.readName(lineIt.next())
                        
                        if reIgnoredName.match(self.name):
                                raise IncompleteBenchmark()
                        
                        while lineIt.hasNext() and not reOldItp.match(lineIt.peek()) and not reOrigWeight.match(lineIt.peek()):
                                lineIt.next()
                                
                        if not lineIt.hasNext():
                                raise EarlyRecEnd(trNotSolved)
                        
                        self.tryAcceptInterpolant(lineIt, reOldItp)
                        self.readValue(lineIt, reOrigWeight, "origSz")
                        self.readValue(lineIt, reMinWeight, "minSz")
                        self.readValue(lineIt, reOrigCount, "origCnt")
                        self.readValue(lineIt, reMinCount, "minCnt")
                        self.readValue(lineIt, reOrigQuant, "origQuant")
                        self.readValue(lineIt, reMinQuant, "minQuant")

                        self.tryAcceptInterpolant(lineIt, reSzMinItp)
                        self.tryAcceptInterpolant(lineIt, reCntMinItp)
                        self.tryAcceptInterpolant(lineIt, reQuantMinItp)
                except StopIteration:
                        raise IncompleteBenchmark()
                except EarlyRecEnd as ere:
                        self.markRemaining(ere.reason)

class NullPostprocessor(object):
        def __call__(self,map):
                pass

class CompoundPostprocessor(object):
        def __init__(self,pps):
                self.pps=pps
        def __call__(self,map):
                for pp in self.pps:
                        pp(map)
class DeletingPostprocessor(object):
        def __init__(self,flds):
                self.flds=flds
        def __call__(self,map):
                for k in self.flds:
                        if k in map:
                                del map[k]
class MergingPostprocessor(object):
        def __init__(self,masterFld,mergedFlds):
                self.masterFld=masterFld
                self.mergedFlds=mergedFlds
        def __call__(self,map):
                for k in self.mergedFlds:
                        if k in map:
                                if self.masterFld!=False:
                                        if self.masterFld in map:
                                                map[self.masterFld] += map[k]
                                        else:
                                                map[self.masterFld] = map[k]
                                del map[k]
class GroupingPostprocessor(object):
        def getTgt(self,num):
                if not isinstance(num,int):
                        return num
                if num<3:
                        return num
                if num<6:
                        return "3 -- 5"
                if num<11:
                        return "6 -- 10"
                if num<21:
                        return "11 -- 20"
                if num<51:
                        return "21 -- 50"
                if num<101:
                        return "51 -- 100"
                if num<501:
                        return "101 -- 500"
                if num<1001:
                        return "501 -- 1,000"
                if num<10001:
                        return "1,000 -- 10,000"
                else:
                        return ">10,000"
                
        def __call__(self,map):
                keys = list(map.keys())
                for k in keys:
                        master = self.getTgt(k)
                        if master==k:
                                continue
                        if master in map:
                                map[master] += map[k]
                        else:
                                map[master] = map[k]
                        del map[k]

class DeletingPostprocessor(object):
        def __init__(self,flds):
                self.flds=flds
        def __call__(self,map):
                
                for k in self.flds:
                        if k in map:
                                del map[k]


class Observer(object):
        def __init__(self,name):
                self.name = name
        def observe(self,bench):
                pass
        def display(self):
                print name, " <display not implemented>"


class CountingObserver(Observer):
        def __init__(self,name, getter, postproc=NullPostprocessor()):
                super(CountingObserver,self).__init__(name)
                self.getter = getter
                self.ctr={}
                self.postproc=postproc
        def observe(self,bench):
                val = self.getter(bench)
                updateCounter(self.ctr,val)
                
        def display(self):
                self.postproc(self.ctr)
        
                print self.name
                printTable([["all"]],[self.ctr])
                return
        def getCounter(self):
                self.postproc(self.ctr)
                return self.ctr

class FldGetter(object):
        def __init__(self,fldName):
                self.fldName = fldName
        def __call__(self,rec):
                val = rec.__dict__[self.fldName]
                if isinstance(val,tuple) and isinstance(val[0],str):
                        val = val[0]
                return val
class FldValGetter(object):
        def __init__(self,fldName):
                self.fldName = fldName
        def __call__(self,rec):
                val = rec.__dict__[self.fldName]
                if isinstance(val,tuple):
                        val = val[0]
                return val

class MinGate(object):
        def __init__(self,measure,ignoreApprox):
                self.oGetter = FldGetter("orig"+measure)
                self.mGetter = FldGetter("min"+measure)
                self.ignoreApprox = ignoreApprox
        def __call__(self,rec):
                oVal = self.oGetter(rec)
                if isinstance(oVal,str):
                        return oVal
                mVal = self.mGetter(rec)
                if isinstance(mVal,str):
                        return "m"+mVal
                if oVal==None:
                        raise ProcError("oval none")
                if oVal[1]:
                        return trAprox 
                if self.ignoreApprox and mVal[1]:
                        return trAprox
                oNum = oVal[0]
                mNum = mVal[0]
                if oNum<mNum:
                        if self.ignoreApprox:
                                raise ProcError("minimal worse than original in unapproximate") 
                        return -1
                if oNum==mNum:
                        return 0
                if mNum==0:
                        return "to Zero"
                return oNum/mNum


locProofPreproc = MergingPostprocessor(False,[None])

clrFailRemover = DeletingPostprocessor([trCannotMakeLocal,trCannotColor])
complYicesFailPostpr = MergingPostprocessor("Fail",[None,"mFail"])
pproc = CompoundPostprocessor([clrFailRemover,complYicesFailPostpr])

pproc = NullPostprocessor()
pproc = CompoundPostprocessor([GroupingPostprocessor(),MergingPostprocessor("TO",["NS","mTO", trAprox]),MergingPostprocessor(False,[trSkipped])])

class ObserverMaster(object):
        def __init__(self):
                self.general = self.buildObservers()
                self.kinds = {}
        def buildObservers(self):
                return [
                        CountingObserver("size min", MinGate('Sz',True), pproc),
                        CountingObserver("count min", MinGate('Cnt',True), pproc),
                        CountingObserver("quant min", MinGate('Quant',True), pproc),
                        ]
        def observeByList(self,obsLst,bench):
                for o in obsLst:
                        o.observe(bench)
        def observe(self,bench):
                self.observeByList(self.general,bench)
                k = bench.kind
                if k:
                        if k not in self.kinds:
                                self.kinds[k] = self.buildObservers()
                        self.observeByList(self.kinds[k],bench)
        def collectObserversRes(self,prefix,obsLst,lblLstRef,mapLstRef):
                for o in obsLst:
                        lbl = [prefix,o.name]
                        lblLstRef.append(lbl)
                        mapLstRef.append(o.getCounter())
        def display(self):
                lbls = []
                maps = []
                self.collectObserversRes("all",self.general,lbls,maps)
                for k in self.kinds:
                        self.collectObserversRes(k,self.kinds[k],lbls,maps)
                printTable(lbls,maps,2)

class ObserverMaster2(ObserverMaster):
        def buildObservers(self):
                return [
                        CountingObserver("origSz", FldValGetter('origSz'), pproc),
                        CountingObserver("minSz", FldValGetter('minSz'), pproc),
                        ]


def onInvalidBench(bench):
        print "########### invalid benchmark ###########"
        if bench.error:
                print bench.error
        for line in bench.lines:
                print line

benchs = []


observers = [ObserverMaster(),ObserverMaster2()]

currBench = None
for line in fileinput.input():
        line = line.rstrip()
        if reIgnoredLine.match(line):
                continue
        if benchSep.match(line):
                if currBench:
                        try:
                                currBench.process()
                                for o in observers:
                                        o.observe(currBench)
                                benchs.append(currBench)
                                #print currBench.name+"\t"+str(currBench.origSz)+" "+str(currBench.minSz)
                        except ProcError as err:
                                currBench.error = err
                                onInvalidBench(currBench)
                        except IncompleteBenchmark:
                                pass
                currBench = Bench()
        elif currBench:
                currBench.addLine(line)

for o in observers:
        o.display()
        
