#!/bin/bash

awk '
BEGIN {
FS=" "
cnt = 0;
succ = 0;
yicesTimeouts = 0;

maxMul=10
}

/^Original interpolant weight cost/ { owc = $5 }
/^Minimized interpolant weight cost/ { mwc = $5 }
/^Original interpolant count cost/ { occ = $5 }
/^Minimized interpolant count cost/ { mcc = $5 }
/^Problems/ { prob=$0 }
/CPU time/ { yicesTimeout=1 }
/^------/ {
if(yicesTimeout==0) {
	cnt++;
	if(owc!=mwc || occ!=mcc) {
	#	print owc "\t" mwc "\t" occ "\t" mcc "\t" prob
		succ++
	}
	
	for(i=1; i<=maxMul; i++) {
		if(owc>0 && owc>i*mwc) {
			succWCnt[i]++
		}
		if(occ>0 && occ>i*mcc) {
			succCCnt[i]++
		}
	}
	
	if(owc>0 && mwc==0) {
		succWCnt[maxMul+1]++
	}
	if(occ>0 && mcc==0) {
		succCCnt[maxMul+1]++
	}
}
if(yicesTimeout==1) {
	yicesTimeouts++
}
owc=0; mwc=0; occ=0; mcc=0; yicesTimeout=0;
}

END {
	print "Total problems with interpolants: " cnt
	print "Some success: " succ

	print ""
	print "Weight minimized: " succWCnt[1]
	print "Weight minimized more than 2 times: " succWCnt[2]
	for(i=2; i<maxMul; i++) {
		print "Weight minimized " i " to " (i+1) " times: " (succWCnt[i]-succWCnt[i+1])
	}
	print "Weight minimized more than 10 times but to non-zero: " (succWCnt[i]-succWCnt[i+1])
	print "Weight minimized to zero: " succWCnt[maxMul+1]

	print ""
	print "Count minimized: " succCCnt[1]
	print "Count minimized more than 2 times: " succCCnt[2]
	for(i=2; i<maxMul; i++) {
		print "Count minimized " i " to " (i+1) " times: " (succCCnt[i]-succCCnt[i+1])
	}
	print "Count minimized more than 10 times but to non-zero: " (succCCnt[i]-succCCnt[i+1])
	print "Count minimized to zero: " succCCnt[maxMul+1]
	
	print ""
	print "Problems with Yices timeouts: " yicesTimeouts
	
}

' $*
