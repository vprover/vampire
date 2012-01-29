#!/usr/bin/python

import fileinput
import os

strategyCnt = None
benchs = []

intInfty = 10000000000000000

def readInpVal(v):
        if v=="TO":
                return intInfty
        else:
                return int(v)
                

class Rec:
        idx = 0
        
        def __init__(self, idx, vals):
                self.idx = idx
                self.parseTime = readInpVal(vals[0])
                self.procTime = readInpVal(vals[1])
                self.clauseCnt = readInpVal(vals[2])
                self.atomCnt = readInpVal(vals[3])
                self.distAtomCnt = readInpVal(vals[4])
        
        def display(self):
                print(self.clauseCnt, self.atomCnt, self.distAtomCnt)

def findIdxsWithLowest(arr,fn):
        res = [arr[0].idx]
        bestVal = fn(arr[0])
        for r in arr[1:]:
                val = fn(r)
                if val==bestVal:
                        res.append(r.idx)
                elif val<bestVal:
                        bestVal = val
                        res = [r.idx]
        return res

class Bench:
        def __init__(self, name):
                self.name = name
                self.recs = []
        def display(self):
                print self.name
                for r in self.recs:
                        r.display()

class Observable:
        def __init__(self, g, n):
                self.getter = g
                self.name = n
                self.winners = []
                self.singleWinners = []
                self.TOs = []
                self.allEqualCnt = 0
                self.allTO = 0
                self.arraysInitialized = False
                
        def initArrays(self):
                #we cannot do this in the constructor as then we don't know the strategy count
                for i in range(0,strategyCnt):
                        self.winners.append(0)
                        self.singleWinners.append(0)
                        self.TOs.append(0)
                self.arraysInitialized = True

        def record(self,bench):
                if not self.arraysInitialized:
                        self.initArrays()
                winIdxs = findIdxsWithLowest(bench.recs, self.getter)
                for idx in winIdxs:
                        self.winners[idx] += 1
                if len(winIdxs)==strategyCnt:
                        self.allEqualCnt += 1
                        if self.getter(bench.recs[0])==intInfty:
                                self.allTO += 1
                else:
                        for i in range(0,strategyCnt):
                                if self.getter(bench.recs[i])==intInfty:
                                        self.TOs[i] += 1
                                self.winners.append(0)
                                self.TOs.append(0)
                if len(winIdxs)==1:
                        self.singleWinners[winIdxs[0]] += 1
        def display(self):
                print self.name + ":"
                for i in range(0,strategyCnt):
                        print i, "\t", self.winners[i],"\tTOs: ",self.TOs[i]
                print "all eq: ", self.allEqualCnt
                print "all TO: ", self.allTO
        def displayForTable(self):
                print self.name + "\t",
                for i in range(0,strategyCnt):
                        print str(self.winners[i])+"\t",
                print
        def displaySinglesForTable(self):
                print self.name + " O\t",
                for i in range(0,strategyCnt):
                        print str(self.singleWinners[i])+"\t",
                print
        def displayTOsForTable(self):
                print "TOs\t",
                for i in range(0,strategyCnt):
                        print str(self.TOs[i])+"\t",
                print
        
def getClauseCnt(r):
        return r.clauseCnt
def getAtomCnt(r):
        return r.atomCnt
def getDistAtomCnt(r):
        return r.distAtomCnt


observers = []
observers.append(Observable(getClauseCnt,"clause count"))
observers.append(Observable(getAtomCnt,"atom count"))
observers.append(Observable(getDistAtomCnt,"distinct atom count"))


for line in fileinput.input():
        args=line.split()
        if not strategyCnt:
                strategyCnt = (len(args)-1)/5
        if len(args)!=strategyCnt*5+1:
                #print " faulty benchmark: ", line
                continue
        bench = Bench(args[0])
        for i in range(0,strategyCnt):
                ofs = 1+(i*5)
                rec = Rec(i, args[ofs:ofs+5])
                bench.recs.append(rec)
        benchs.append(bench)
        
        for obs in observers:
                obs.record(bench)

for obs in observers:
        obs.displayForTable()
for obs in observers:
        obs.displaySinglesForTable()
observers[0].displayTOsForTable()
