#!/usr/bin/env python

# @Author Giles
import os
import sys
import subprocess 

if(len(sys.argv)<2):
  print "You should provide a command to proof_check i.e. ../vampire_rel_master -sa inst_gen TPTP/Problems/SYN/SYN001+1.p" 
  sys.exit(0)

TPTP='~/TPTP-v6.4.0/'
VAMPIRE_ROOT = sys.argv[1]+' --include '+TPTP
VAMPIRE_CHECK = './vampire_z3_rel_master --mode casc'#VAMPIRE_ROOT

# Set the time out for all proof attempts
time_out=str(30)
# Set the strings for each prover
EPROVER='~/Vampire/prover-bin/eprover --auto --tptp3-in --proof-object --cpu-limit='+time_out
VAMPIRE= VAMPIRE_CHECK+' -p off --time_limit '+time_out
IPROVER='~/Vampire/prover-bin/iproveropt --clausifier ../vampire_rel_master --clausifier_options "--mode clausify" --time_out_real '+time_out
CVC4='cvc4 --lang tptp --tlimit='+time_out+'000' # to convert seconds to ms
SPASS='~/Vampire/prover-bin/SPASS -Auto=1 -TPTP=1 -TimeLimit='+time_out  
CHECK_WITH=set()
#CHECK_WITH.add(EPROVER)
CHECK_WITH.add(VAMPIRE)
#CHECK_WITH.add(IPROVER)
#CHECK_WITH.add(CVC4)
#CHECK_WITH.add(SPASS)

verbose=True

ignores=set()#set(['%negated conjecture','%sat splitting component','%theory axiom','%cnf transformation','%flattening','%ennf transformation','%general splitting','%general splitting component introduction','%global subsumption','%sat splitting refutation','%rectify'])

ARGS= " -p proofcheck "+(' '.join(sys.argv[2:]))
print "Running vampire on "+ ARGS 
OUT=""
try:
	OUT=subprocess.check_output(VAMPIRE_ROOT+ARGS, shell = True)
except subprocess.CalledProcessError as err:
	print "The problem was not solved"
	print err
	sys.exit(0)

refutation=False
obligation=[]
checked=0
for line in OUT.split('\n'):
  line = line.strip()

  if '%#' in line and len(obligation)>0:

    if all(ignore not in o for o in obligation for ignore in ignores):
      #Finished obligation, run it

      checked+=1
      if verbose:
        print "Dealing with obligation:"
        print '\n'.join(obligation)

      #Create a temp file
      with open('proof_obligation_'+str(checked), 'w') as tmp:
        tmp.write('\n'.join(obligation))

      any_failed=False
      #Run provers
      for prover in CHECK_WITH:
      	prover_result=""
      	try:
        	prover_result = subprocess.check_output(prover+' proof_obligation_'+str(checked),shell=True)
      	except subprocess.CalledProcessError as err:
        	prover_result = err.output

      	proved=False
      	for prover_line in prover_result.split('\n'):
        	if 'SZS status' in prover_line:
          		if verbose:
            			print "Prover Output:\t"+prover_line
          		if 'Theorem' in prover_line or 'Unsatisfiable' in prover_line:
	            		proved=True
			break
		if 'SPASS beiseite: Proof found.' in prover_line:
			proved=True

      	if not proved:
        	print '************************'
        	print 'Failed proof obligation: ',checked,' using ',prover
		any_failed=True
        	
      if not any_failed:
          os.remove('proof_obligation_'+str(checked))
 
      #Reset obligation
      obligation=[]
    else:
      print "Skipped ",obligation
  elif refutation:
  	obligation.append(line)

  if 'Refutation found' in line:
    refutation=True
    print "There was a refutation, checking proof..."

if not refutation:
  print "There was no refutation"
else:
  print "Finished checking :)"
  print "We checked " + str(checked) +" obligations"

