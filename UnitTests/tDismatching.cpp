#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Sorts.hpp"

#include "Indexing/LiteralSubstitutionTreeWithoutTop.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/Index.hpp"


#include "Test/UnitTesting.hpp"


#define UNIT_ID dm 
UT_CREATE;

using namespace Indexing;

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

  Literal* qlit = Literal::createEquality(true,fxa,a,Sorts::SRT_DEFAULT);

  SLQueryResultIterator it= dismatchIndex->getGeneralizations(qlit,false,false);

  cout << it.hasNext() << endl;
}
