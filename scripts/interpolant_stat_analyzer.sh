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
	if(owc<20 && owc>3*mwc && mwc!=0) {
	       print prob " " owc " --> " mwc
	}
	if(owc==0) { owc0Cnt+=1; }
        if(owc==1 && mwc!=0) { owc1Cnt+=1; }
        if(owc>0 && owc<5) { owcCnt[5]+=1; }
        if(owc>0 && owc<10) { owcCnt[10]+=1; }
        if(owc>0 && owc<20) { owcCnt[20]+=1; }
        if(owc>0 && owc<50) { owcCnt[50]+=1; }
        if(owc>0 && owc<100) { owcCnt[100]+=1; }
        if(owc>0 && owc<200) { owcCnt[200]+=1; }
        if(owc>0 && owc<500) { owcCnt[500]+=1; }
        if(owc>0 && owc<1000) { owcCnt[1000]+=1; }
        if(owc>0 && owc>=1000) { owcCnt[1001]+=1; }
        if(owc>0 && owc>=200) { owcCnt[201]+=1; }

        if(mwc>0 && mwc<5) { mwcCnt[5]+=1; }
        if(mwc>0 && mwc<10) { mwcCnt[10]+=1; }
        if(mwc>0 && mwc<20) { mwcCnt[20]+=1; }
        if(mwc>0 && mwc<50) { mwcCnt[50]+=1; }
        if(mwc>0 && mwc<100) { mwcCnt[100]+=1; }
        if(mwc>0 && mwc<200) { mwcCnt[200]+=1; }
        if(mwc>0 && mwc<500) { mwcCnt[500]+=1; }
        if(mwc>0 && mwc<1000) { mwcCnt[1000]+=1; }
        if(mwc>0 && mwc>=1000) { mwcCnt[1001]+=1; }
        if(mwc>0 && mwc>=200) { mwcCnt[201]+=1; }
}
if(yicesTimeout==1) {
	yicesTimeouts++
}
owc=0; mwc=0; occ=0; mcc=0; yicesTimeout=0;
}

END {
        print owcCnt[5]
        print owcCnt[10]-owcCnt[5]
        print owcCnt[20]-owcCnt[10]
        print owcCnt[50]-owcCnt[20]
        print owcCnt[100]-owcCnt[50]
        print owcCnt[200]-owcCnt[100]
        print owcCnt[201]
        print ""
        print mwcCnt[5]
        print mwcCnt[10]-mwcCnt[5]
        print mwcCnt[20]-mwcCnt[10]
        print mwcCnt[50]-mwcCnt[20]
        print mwcCnt[100]-mwcCnt[50]
        print mwcCnt[200]-mwcCnt[100]
        print mwcCnt[201]

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
        print "Problems with empty original interpolants: " owc0Cnt
        print "Problems with original interpolants of size 1 that were not minimized: " owc1Cnt
	print ""
	print "Problems with Yices timeouts: " yicesTimeouts
	
	printf " & some & $>2$"
	for(i=2; i<maxMul; i+=2) {
	       printf " & $" i "-" (i+2) "$"
	}
	printf "& to 0\\\\\n\\hline\n"
	printf "Weight & " succWCnt[1] " & " succWCnt[2]
        for(i=2; i<maxMul; i+=2) {
               printf " & " (succWCnt[i]-succWCnt[i+2])
        }
        printf " & " succWCnt[maxMul]-succWCnt[maxMul+1]
        printf "& "succWCnt[maxMul+1] "\\\\\n\\hline\n"
        printf "Count & " succCCnt[1] " & " succCCnt[2]
        for(i=2; i<maxMul; i+=2) {
               printf " & " (succCCnt[i]-succCCnt[i+2])
        }
        printf " & " succCCnt[maxMul]-succCCnt[maxMul+1]
        printf "& "succCCnt[maxMul+1] "\\\\\n\\hline\n"
}

' $*
