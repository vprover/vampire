import sys
import subprocess 

VAMPIRE='../vampire_rel_master'
EPROVER='~/Vampire/prover-bin/eprover --auto --tptp3-in --proof-object'

verbose=False

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

  if '%#' in line and len(obligation)>0 and all('%negated conjecture' not in o for o in obligation):
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
      prover_result = subprocess.check_output(EPROVER+' tmp_proof_obligation',shell=True)
    except subprocess.CalledProcessError as err:
      prover_result = err.output

    for prover_line in prover_result.split('\n'):
      if 'SZS status' in prover_line:
        if verbose:
          print prover_line
        if 'Theorem' not in prover_line:
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
