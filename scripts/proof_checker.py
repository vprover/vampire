import sys
import subprocess 

VAMPIRE='../vampire_rel_master'

time_out=str(10)
EPROVER='~/Vampire/prover-bin/eprover --auto --tptp3-in --proof-object --cpu-limit='+time_out
US='../vampire_rel_master -p off --ignore_missing on --mode casc --time_limit '+time_out
IPROVER='~/Vampire/prover-bin/iproveropt --clausifier ../vampire_rel_master --clausifier_options "--mode clausify" --time_out_real '+time_out
CHECK_WITH=IPROVER

verbose=False

ignores=set(['%negated conjecture','%sat splitting component'])

if(len(sys.argv)<2):
  print "You should provide arguments"
  sys.exit(0)

VAMPIRE=sys.argv[1]
ARGS= " -p proofcheck "+(' '.join(sys.argv[2:]))

print "Running vampire on "+ ARGS 
OUT=subprocess.check_output(VAMPIRE+ARGS, shell = True)

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
      with open('tmp_proof_obligation', 'w') as tmp:
        tmp.write('\n'.join(obligation))

      #Run prover
      prover_result=""
      try:
        prover_result = subprocess.check_output(CHECK_WITH+' tmp_proof_obligation',shell=True)
      except subprocess.CalledProcessError as err:
        prover_result = err.output

      proved=False
      for prover_line in prover_result.split('\n'):
        if 'SZS status' in prover_line:
          if verbose:
            print prover_line
          if 'Theorem' in prover_line:
            proved=True

      if not proved:
        print '************************'
        print 'Failed proof obligation:'
        print '\n'.join(obligation)
 
    #Reset obligation
    obligation=[]
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

#TODO delete tmp_proof_obligation
