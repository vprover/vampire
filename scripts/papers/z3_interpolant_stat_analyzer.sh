#!/bin/bash

awk '
BEGIN {
FS=" "
cnt = 0;
succ = 0;
yicesTimeouts = 0;

maxMul=10
}

/^Original interpolant weight cost/ { owc = $5; firstRes=1 }
/^Minimized interpolant weight cost/ { mwc = $5 }
/^Original interpolant count cost/ { occ = $5 }
/^Minimized interpolant count cost/ { mcc = $5 }
/^Original interpolant quantifiers cost/ { oqc = $5 }
/^Minimized interpolant quantifiers cost/ { mqc = $5; full=1 }
/^Derivation not local/ { derivationNotLocal = 1 }
/^interp/ { prob=$0 }
/^results for / { prob= $3" "$4 }
/^SMT solver gave/ { yicesTimeout=1 }
/^========/ {
if(full==1) {
	cnt++;
	if(owc!=mwc || occ!=mcc) {
	#	print owc "\t" mwc "\t" occ "\t" mcc "\t" prob
		succ++
	}
	
	for(i=1; i<=maxMul; i++) {
		if(owc>0 && owc>i*mwc) {
			succWCnt[i]++
			if(mqc==0 && i==1) {
			     print "W ", owc, " --> ", mwc, " ", prob
			}
		}
		if(occ>0 && occ>i*mcc) {
			succCCnt[i]++
                        if(i==2) {
                             print "C ", occ, " --> ", mcc, " ", prob
                        }
		}
                if(oqc>0 && oqc>i*mqc) {
                        succQCnt[i]++
                        if(i==1) {
                             print "Q ", oqc, " --> ", mqc, " ", prob
                        }
                }
	}
	
	if(owc>0 && mwc==0) {
		succWCnt[maxMul+1]++
	}
	if(occ>0 && mcc==0) {
		succCCnt[maxMul+1]++
	}
	if(oqc>0 && mqc==0) {
		succQCnt[maxMul+1]++
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

        if(occ==0) { occ0Cnt+=1; }
        if(occ==1 && mcc!=0) { occ1Cnt+=1; }
        if(occ>0 && occ<5) { occCnt[5]+=1; }
        if(occ>0 && occ<10) { occCnt[10]+=1; }
        if(occ>0 && occ<20) { occCnt[20]+=1; }
        if(occ>0 && occ<50) { occCnt[50]+=1; }
        if(occ>0 && occ<100) { occCnt[100]+=1; }
        if(occ>0 && occ<200) { occCnt[200]+=1; }
        if(occ>0 && occ<500) { occCnt[500]+=1; }
        if(occ>0 && occ<1000) { occCnt[1000]+=1; }
        if(occ>0 && occ>=1000) { occCnt[1001]+=1; }
        if(occ>0 && occ>=200) { occCnt[201]+=1; }

        if(mcc>0 && mcc<5) { mccCnt[5]+=1; }
        if(mcc>0 && mcc<10) { mccCnt[10]+=1; }
        if(mcc>0 && mcc<20) { mccCnt[20]+=1; }
        if(mcc>0 && mcc<50) { mccCnt[50]+=1; }
        if(mcc>0 && mcc<100) { mccCnt[100]+=1; }
        if(mcc>0 && mcc<200) { mccCnt[200]+=1; }
        if(mcc>0 && mcc<500) { mccCnt[500]+=1; }
        if(mcc>0 && mcc<1000) { mccCnt[1000]+=1; }
        if(mcc>0 && mcc>=1000) { mccCnt[1001]+=1; }
        if(mcc>0 && mcc>=200) { mccCnt[201]+=1; }

        if(oqc==0) { oqc0Cnt+=1; }
        if(oqc==1 && mqc!=0) { oqc1Cnt+=1; }
        if(oqc>0 && oqc<5) { oqcCnt[5]+=1; }
        if(oqc>0 && oqc<10) { oqcCnt[10]+=1; }
        if(oqc>0 && oqc<20) { oqcCnt[20]+=1; }
        if(oqc>0 && oqc<50) { oqcCnt[50]+=1; }
        if(oqc>0 && oqc<100) { oqcCnt[100]+=1; }
        if(oqc>0 && oqc<200) { oqcCnt[200]+=1; }
        if(oqc>0 && oqc<500) { oqcCnt[500]+=1; }
        if(oqc>0 && oqc<1000) { oqcCnt[1000]+=1; }
        if(oqc>0 && oqc>=1000) { oqcCnt[1001]+=1; }
        if(oqc>0 && oqc>=200) { oqcCnt[201]+=1; }

        if(mqc>0 && mqc<5) { mqcCnt[5]+=1; }
        if(mqc>0 && mqc<10) { mqcCnt[10]+=1; }
        if(mqc>0 && mqc<20) { mqcCnt[20]+=1; }
        if(mqc>0 && mqc<50) { mqcCnt[50]+=1; }
        if(mqc>0 && mqc<100) { mqcCnt[100]+=1; }
        if(mqc>0 && mqc<200) { mqcCnt[200]+=1; }
        if(mqc>0 && mqc<500) { mqcCnt[500]+=1; }
        if(mqc>0 && mqc<1000) { mqcCnt[1000]+=1; }
        if(mqc>0 && mqc>=1000) { mqcCnt[1001]+=1; }
        if(mqc>0 && mqc>=200) { mqcCnt[201]+=1; }

}
else {
        if(first || yicesTimeout) {
                minimizingTimeouts++;
        }
        else if(derivationNotLocal) {
                localizingTimeouts++;
        }
        else {
                initialTimeouts++;
        }
}
if(yicesTimeout==1) {
	yicesTimeouts++
}
owc=0; mwc=0; occ=0; mcc=0; oqc=0; mqc=0; yicesTimeout=0; full=0; firstRes=0; derivationNotLocal=0
}

END {
        print "Minimizing timeouts: " minimizingTimeouts
        print "Localizing timeouts: " localizingTimeouts
        print "Initial timeouts: " initialTimeouts

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
        print"----"
        print occCnt[5]
        print occCnt[10]-occCnt[5]
        print occCnt[20]-occCnt[10]
        print occCnt[50]-occCnt[20]
        print occCnt[100]-occCnt[50]
        print occCnt[200]-occCnt[100]
        print occCnt[201]
        print ""
        print mccCnt[5]
        print mccCnt[10]-mccCnt[5]
        print mccCnt[20]-mccCnt[10]
        print mccCnt[50]-mccCnt[20]
        print mccCnt[100]-mccCnt[50]
        print mccCnt[200]-mccCnt[100]
        print mccCnt[201]
        print"----"
        print oqcCnt[5]
        print oqcCnt[10]-oqcCnt[5]
        print oqcCnt[20]-oqcCnt[10]
        print oqcCnt[50]-oqcCnt[20]
        print oqcCnt[100]-oqcCnt[50]
        print oqcCnt[200]-oqcCnt[100]
        print oqcCnt[201]
        print ""
        print mqcCnt[5]
        print mqcCnt[10]-mqcCnt[5]
        print mqcCnt[20]-mqcCnt[10]
        print mqcCnt[50]-mqcCnt[20]
        print mqcCnt[100]-mqcCnt[50]
        print mqcCnt[200]-mqcCnt[100]
        print mqcCnt[201]
        

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
        print "Quant minimized: " succQCnt[1]
        print "Quant minimized more than 2 times: " succQCnt[2]
        for(i=2; i<maxMul; i++) {
                print "Quant minimized " i " to " (i+1) " times: " (succQCnt[i]-succQCnt[i+1])
        }
        print "Quant minimized more than 10 times but to non-zero: " (succQCnt[i]-succQCnt[i+1])
        print "Quant minimized to zero: " succQCnt[maxMul+1]
        
        print ""
        print "Problems with empty original interpolants: " owc0Cnt
        print "Problems with original interpolants of size 1 that were not minimized: " owc1Cnt
        print "Problems with non-quantified original interpolants: " oqc0Cnt
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
        printf "& "succWCnt[maxMul+1] "\\\\\n\\hline\n"
        printf "Count & " succCCnt[1] " & " succCCnt[2]
        for(i=2; i<maxMul; i+=2) {
               printf " & " (succCCnt[i]-succCCnt[i+2])
        }
        printf "& "succCCnt[maxMul+1] "\\\\\n\\hline\n"
}

' $*
