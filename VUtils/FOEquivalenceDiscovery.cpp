
/*
 * File FOEquivalenceDiscovery.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file FOEquivalenceDiscovery.cpp
 * Implements class FOEquivalenceDiscovery.
 */

#include <sstream>

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include "FOEquivalenceDiscovery.hpp"

namespace VUtils
{

vstring FOEquivalenceDiscovery::getArgStr(unsigned arity)
{
  if(arity==0) { return ""; }
  vostringstream res;
  res << "(X0";
  for(unsigned i=1; i<arity; i++) {
    res << ",X" << i;
  }
  res << ")";
  return res.str();
}

int FOEquivalenceDiscovery::perform(int argc, char** argv)
{
  if(argc<3) {
    USER_ERROR("file name expected as second argument");
  }
  vstring fname = argv[2];

  Options opts;
  opts.setTheoryAxioms(false);
  opts.setInputFile(fname);

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(opts));

  Stack<unsigned> preds;
  prb->collectPredicates(preds);
  makeUnique(preds);

  Stack<unsigned>::DelIterator pit(preds);
  while(pit.hasNext()) {
    unsigned pred = pit.next();
    if(pred==0) {
      //equivalence
      pit.del();
    }
  }

  ostream& pout = cout;

  unsigned sz = preds.size();
  for(unsigned i=0; i<sz; i++) {
    Signature::Symbol* sym1 = env.signature->getPredicate(preds[i]);
    PredicateType* t1 = sym1->predType();
    unsigned ar1 = sym1->arity();
    vstring n1 = sym1->name();
    vstring args = getArgStr(ar1);
    pout << "fof(t_" << n1 << ", claim, " << n1 << args << ")." << endl;
    pout << "fof(f_" << n1 << ", claim, ~" << n1 << args << ")." << endl;

    for(unsigned j=i+1; j<sz; j++) {
      Signature::Symbol* sym2 = env.signature->getPredicate(preds[j]);
      PredicateType* t2 = sym2->predType();
      if(*t1!=*t2) {
	continue;
      }

      vstring n2 = sym2->name();

      pout << "fof(e_" << n1 << "_" << n2 << ", claim, " << n1 << args << "<=>" << n2 << args << ")." << endl;
      pout << "fof(n_" << n1 << "_" << n2 << ", claim, " << n1 << args << "<=>~" << n2 << args << ")." << endl;

    }

  }

  return 0;
}

}
