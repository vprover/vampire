
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/SATSolver.hpp"
#include "SAT/TWLSolver.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID satSolver
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace SAT;

/**
 * c is either lower or upper case letter, upper
 * case is positive literals, lower negative.
 *
 * SATSolver to use these literals should have varCnt at least 27.
 */
SATLiteral getLit(char c)
{
  CALL("getLit");

  bool pol;
  unsigned var;
  if(c>='a' && c<='z') {
    var = c-'a'+1;
    pol = false;
  }
  else {
    ASS_REP(c>='A' && c<='Z',c)
    var = c-'A'+1;
    pol = true;
  }
  return SATLiteral(var, pol);
}

/**
 * spec consits of lower and upper case letters, upper
 * case are positive literals, lower negative.
 *
 * SATSolver to use these clauses should have varCnt at least 27.
 */
SATClause* getClause(const char* spec)
{
  CALL("getClause");

  SATLiteralStack lits;
  while(*spec) {
    char c = *spec;
    lits.push(getLit(c));
    spec++;
  }
  return SATClause::fromStack(lits);
}
void ensurePrepared(SATSolver& s)
{
  s.ensureVarCnt(27);
}

void testZICert1(SATSolver& s)
{
  CALL("testZICert1");

  ensurePrepared(s);
  s.addClauses(pvi(getSingletonIterator(getClause("ab"))));
  s.addClauses(pvi(getSingletonIterator(getClause("c"))));

  unsigned cVar = getLit('c').var();
  ASS(s.isZeroImplied(cVar));
  SATClause* ccert = s.getZeroImpliedCertificate(cVar);
  ASS_EQ(ccert->size(),1);
  ASS_EQ((*ccert)[0],getLit('c'));

  unsigned bVar = getLit('b').var();
  ASS(!s.isZeroImplied(bVar));
  s.addAssumption(getLit('A'));
  ASS(s.isZeroImplied(bVar));
  SATClause* bcert = s.getZeroImpliedCertificate(bVar);
  ASS_EQ(bcert->size(),2);
}


void testProofWithAssumptions(SATSolver& s)
{
  CALL("testProofWithAssumptions");

  s.ensureVarCnt(2);
  s.addClauses(pvi(getSingletonIterator(getClause("a"))));
  s.addClauses(pvi(getSingletonIterator(getClause("A"))));

  ASS_EQ(s.getStatus(),SATSolver::UNSATISFIABLE);

  SATClause* refutation = s.getRefutation();
  PropInference* inf = static_cast<PropInference*>(refutation->inference());

  cout << endl << "Refutation: " << refutation->toString() << endl;

  List<SATClause*>* prems = inf->getPremises();

  cout << "Inference length: " << prems->length() << endl;
  
  while(prems){
    cout << prems->head()->toString() << endl;
    prems = prems->tail();
  }

}

TEST_FUN(satSolverZeroImpliedCert)
{
  TWLSolver s1(*env.options,true);
  testZICert1(s1);
  TWLSolver s2(*env.options,true);
  testProofWithAssumptions(s2);
}

