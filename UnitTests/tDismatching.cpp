
/*
 * File tDismatching.cpp.
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
#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Sorts.hpp"

// #include "Indexing/LiteralSubstitutionTreeWithoutTop.hpp" << does not exsist anymore
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/Index.hpp"


#include "Test/UnitTesting.hpp"


#define UNIT_ID dm 
UT_CREATE;

using namespace Indexing;

#warning compile-time broken test
/* compile broken
TEST_FUN(index)
{
  cout << endl;
  LiteralIndexingStructure * is = new LiteralSubstitutionTreeWithoutTop();
  DismatchingLiteralIndex* dismatchIndex = new DismatchingLiteralIndex(is);

  unsigned f = env.signature->addFunction("f",2);
  TermList x(1,false);
  TermList y(2,false);
  TermList a(Term::createConstant(env.signature->addFunction("a",0)));
  TermList fxy(Term::create2(f,x,y));
  TermList fxa(Term::create2(f,x,a));
  Literal* lit = Literal::createEquality(true,fxy,a,Sorts::SRT_DEFAULT);

  Clause * cl = new(1) Clause(1,Unit::AXIOM,new Inference(Inference::INPUT));
  (* cl)[0] = lit;
  
  dismatchIndex->handleClause(cl,true);

  Literal* qlit = Literal::createEquality(false,fxa,a,Sorts::SRT_DEFAULT);

  SLQueryResultIterator it= dismatchIndex->getGeneralizations(qlit,true,false);

  cout << it.hasNext() << endl;
}
*/
