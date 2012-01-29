#!/usr/bin/python

import fileinput
import os
import re



reYicesGarbaggeLine = re.compile("sh: line 1: .* Alarm clock");
benchSep = re.compile("============#$")
colorSep = re.compile("------#$")

reName =  re.compile("F: (.*)$")
reRedStart = re.compile("Rq:$")
reBlueStart = re.compile("Bq:$")
reDerLocal = re.compile("Derivation was already local")
reDerNonLocal = re.compile("Derivation not local")
reTimeOut = re.compile("(External time out \(SIGXCPU\))|(Time limit reached!)")
reOutOfMem = re.compile("Memory limit exceeded!")
reErrorResult = re.compile("error result code")
reNonLocalUnit = re.compile("Non-local unit:")
reCannotMakeLocal = re.compile("Cannot make the colored proof local")
reCannotColorRefutation = re.compile("Cannot color the refutation")

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

trTimeOut = "TO"
trOutOfMem = "MO"
trCannotMakeLocal = "CML"
trCannotColor = "CCL"
trMinimFail = "Fail"

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

def printTable(labels,maps):
        keys = set()
        for m in maps:
                keys.update(m.keys())
        keyLst = list(keys)
        keyLst.sort()
        
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

class Rec(object):
        def __init__(self):
                self.lines = []
                self.derLocal = None
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
                        if reCannotMakeLocal.match(line):
                                raise EarlyRecEnd(trCannotMakeLocal)
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
                
        def process(self):
                lineIt = self.lines.__iter__()
                line = lineIt.next()
                
                try:
                        self.checkForResLimits(line)
                        if reNonLocalUnit.match(line):
                                line = lineIt.next()
                                if not reCannotColorRefutation.match(line):
                                        raise ProcError("non-colorability report expected: "+line)
                                raise EarlyRecEnd(trCannotColor)
                        if reDerNonLocal.match(line):
                                self.derLocal = False
                        elif reDerLocal.match(line):
                                self.derLocal = True
                        else:
                                raise ProcError("derivation locality not output on the first line")
                
                
                        self.readValue(lineIt, reOrigWeight, "origSz")
                        self.readValue(lineIt, reMinWeight, "minSz")
                        self.readValue(lineIt, reOrigCount, "origCnt")
                        self.readValue(lineIt, reMinCount, "minCnt")
                        self.readValue(lineIt, reOrigQuant, "origQuant")
                        self.readValue(lineIt, reMinQuant, "minQuant")
                        try:
                                line = lineIt.next()
                                raise ProcError("extra line: "+line)
                        except StopIteration:
                                pass
                except EarlyRecEnd as ere:
                        self.markRemaining(ere.reason)
                        if not reErrorResult.match(self.lines[-1]):
                                raise ProcError(str(ere)+" without error result")
                except StopIteration:
                        raise ProcError("more lines expected")
                        

class Bench(object):
        def __init__(self):
                self.lines = []
                self.name = None
                self.redRec = None
                self.blueRec = None
                self.error = None
        def addLine(self,line):
                self.lines.append(line)
        def process(self):
                try:
                        lineIt = self.lines.__iter__()
                        nameMatch = reName.match(lineIt.next())
                        if not nameMatch:
                                raise ProcError("no name match")
                        self.name = nameMatch.group(1)
                        if not reRedStart.match(lineIt.next()):
                                raise ProcError("no red start match")
                        curr = self.redRec = Rec()
                        for line in lineIt:
                                if colorSep.match(line):
                                        break
                                else:
                                        curr.addLine(line)
                                        
                        if not reBlueStart.match(lineIt.next()):
                                raise ProcError("no blue start match")
                        curr = self.blueRec = Rec()
                        for line in lineIt:
                                curr.addLine(line)
                        self.redRec.process()
                        self.blueRec.process()
                except StopIteration:
                        raise IncompleteBenchmark()

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
                                if self.masterFld in map:
                                        map[self.masterFld] += map[k]
                                else:
                                        map[self.masterFld] = map[k]
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
                self.redCtr={}
                self.blueCtr={}
                self.betterCtr={}
                self.allCtr={}
                self.postproc=postproc
        def observe(self,bench):
                redVal = self.getter(bench.redRec)
                blueVal = self.getter(bench.blueRec)
                updateCounter(self.redCtr,redVal)
                updateCounter(self.blueCtr,blueVal)
                updateCounter(self.allCtr,redVal)
                updateCounter(self.allCtr,blueVal)
                
                betterVal = None
                if isinstance(redVal,int):
                        if isinstance(blueVal,int):
                                betterVal = max(redVal, blueVal)
                        else:
                                betterVal = redVal
                else:
                        betterVal = blueVal
                updateCounter(self.betterCtr,betterVal)
                
        def display(self):
                self.postproc(self.allCtr)
                self.postproc(self.redCtr)
                self.postproc(self.blueCtr)
                self.postproc(self.betterCtr)
        
                print self.name
                printTable(["all","red","blue","better"],[self.allCtr,self.redCtr,self.blueCtr,self.betterCtr])
                return
                print "  all:    ", self.allCtr
                print "  red:    ", self.redCtr
                print "  blue:   ", self.blueCtr
                print "  better: ", self.betterCtr

class ComparingObserver(Observer):
        def __init__(self,name, getter):
                super(ComparingObserver,self).__init__(name)
                self.getter = getter
                self.redBetter=0
                self.blueBetter=0
                self.bothSame=0
                self.bothFail={}
        def observe(self,bench):
                redVal = self.getter(bench.redRec)
                blueVal = self.getter(bench.blueRec)
                if isinstance(redVal,tuple):
                        redVal = redVal[0]
                if isinstance(blueVal,tuple):
                        blueVal = blueVal[0]
                
                if isinstance(redVal,int):
                        if isinstance(blueVal,int):
                                if redVal==blueVal:
                                        self.bothSame += 1
                                elif redVal<blueVal:
                                        self.redBetter += 1
                                else:
                                        self.blueBetter += 1
                        else:
                                self.redBetter += 1
                else:
                        if isinstance(blueVal,int):
                                self.blueBetter += 1
                        else:
                                failVal = (redVal,blueVal)
                                if redVal==blueVal:
                                        failVal = redVal
                                updateCounter(self.bothFail,failVal)
                
        def display(self):
                print self.name
                print "red\t", self.redBetter
                print "blue\t", self.blueBetter
                print "same\t", self.bothSame
                print "both fail\t", self.bothFail


class LocGetter(object):
        def __call__(self,rec):
                if isinstance(rec.derLocal,tuple) and isinstance(rec.derLocal[0],str):
                        return rec.derLocal[0]
                if rec.derLocal:
                        return True
                if rec.origSz[0]==trCannotMakeLocal:
                        return trCannotMakeLocal
                if rec.origSz[0]==trTimeOut or rec.origSz[0]==trOutOfMem:
                        #here we don't know if it was timeout during localization or initial interpolant getting
                        return None
                return False
                
class FldGetter(object):
        def __init__(self,fldName):
                self.fldName = fldName
        def __call__(self,rec):
                val = rec.__dict__[self.fldName]
                if isinstance(val,tuple) and isinstance(val[0],str):
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
                        return None 
                if self.ignoreApprox and mVal[1]:
                        return None
                oNum = oVal[0]
                mNum = mVal[0]
                if oNum<mNum:
                        if self.ignoreApprox:
                                raise ProcError("minimal worse than original in unapproximate") 
                        return -1
                if oNum==mNum:
                        return 0
                return oNum/mNum


def onInvalidBench(bench):
        print "########### invalid benchmark ###########"
        if bench.error:
                print bench.error
        for line in bench.lines:
                print line


benchs = []

locProofPreproc = MergingPostprocessor(False,[None])

clrFailRemover = DeletingPostprocessor([trCannotMakeLocal,trCannotColor])
complYicesFailPostpr = MergingPostprocessor("Fail",[None,"mFail"])
pproc = CompoundPostprocessor([clrFailRemover,complYicesFailPostpr])

pproc({"a":1})

observers = [
        CountingObserver("local proof", LocGetter(), locProofPreproc),
        CountingObserver("size minimization", MinGate('Sz',True), pproc),
        CountingObserver("count minimization", MinGate('Cnt',True), pproc),
        CountingObserver("quantifier minimization", MinGate('Quant',True), pproc),
        CountingObserver("size minimization w. approx", MinGate('Sz',False), pproc),
        CountingObserver("count minimization w. approx", MinGate('Cnt',False), pproc),
        CountingObserver("quantifier minimization w. approx", MinGate('Quant',False), pproc),
        ComparingObserver("orig size", FldGetter('origSz')),
        ComparingObserver("min size", FldGetter('minSz')),
        ComparingObserver("orig cnt", FldGetter('origCnt')),
        ComparingObserver("min cnt", FldGetter('minCnt')),
        ComparingObserver("orig quant", FldGetter('origQuant')),
        ComparingObserver("min quant", FldGetter('minQuant'))
        ]

currBench = None
for line in fileinput.input():
        line = line.rstrip()
        if reYicesGarbaggeLine.match(line):
                continue
        if benchSep.match(line):
                if currBench:
                        try:
                                currBench.process()
                                for o in observers:
                                        o.observe(currBench)
                                benchs.append(currBench)
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
        
