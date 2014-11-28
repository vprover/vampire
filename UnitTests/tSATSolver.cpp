
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/SATSolver.hpp"
#include "SAT/TWLSolver.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/LingelingInterfacing.hpp"

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
 * spec consists of lower and upper case letters, upper
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

TEST_FUN(satSolverZeroImpliedCert)
{
  TWLSolver s(*env.options,true);
  testZICert1(s);
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

  // cout << endl << "Refutation: " << refutation->toString() << endl;

  List<SATClause*>* prems = inf->getPremises();

  // cout << "Inference length: " << prems->length() << endl;
  
  while(prems){
    // cout << prems->head()->toString() << endl;
    prems = prems->tail();
  }

}

TEST_FUN(testProofWithAssums)
{
  TWLSolver s(*env.options,true);
  testProofWithAssumptions(s);    
}

void testInterface(SATSolver &s) {
  ensurePrepared(s);
      
  ASS_EQ(s.getStatus(),SATSolver::SATISFIABLE);
  
  unsigned a = getLit('a').var();
  unsigned b = getLit('b').var();
  unsigned c = getLit('c').var();
  unsigned d = getLit('d').var();
  
  s.suggestPolarity(a,0);
  s.addClauses(SATClauseIterator::getEmpty());
  ASS(s.trueInAssignment(getLit('a')));
  s.suggestPolarity(a,1);
  s.addClauses(SATClauseIterator::getEmpty());
  ASS(!s.trueInAssignment(getLit('a')));
  
  s.forcePolarity(a,0);
  s.addClauses(SATClauseIterator::getEmpty());
  ASS(s.trueInAssignment(getLit('a')));
  s.forcePolarity(a,1);
  s.addClauses(SATClauseIterator::getEmpty());
  ASS(!s.trueInAssignment(getLit('a')));      
  
  s.addClauses(pvi(getSingletonIterator(getClause("ab"))),true);
  ASS_EQ(s.getStatus(),SATSolver::UNKNOWN);
  s.addClauses(pvi(getSingletonIterator(getClause("aB"))),true);
  ASS_EQ(s.getStatus(),SATSolver::UNKNOWN);
  s.addClauses(pvi(getSingletonIterator(getClause("Ab"))),true);
  ASS_EQ(s.getStatus(),SATSolver::UNKNOWN);
  s.addClauses(pvi(getSingletonIterator(getClause("C"))));
  ASS_EQ(s.getStatus(),SATSolver::SATISFIABLE);
  
  ASS(s.trueInAssignment(getLit('a')));
  ASS(s.trueInAssignment(getLit('b')));
  ASS(s.falseInAssignment(getLit('c')));
  
  
  
  // for a and b depends on learned clauses, which depend on decide polarity
  // but should be both at the same time, or none of the two
  ASS(s.isZeroImplied(a) == s.isZeroImplied(b));   
  
  ASS(s.isZeroImplied(c));
  ASS(!s.isZeroImplied(d));    

  cout << " Random: ";
  for (int i = 0; i < 10; i++) {    
    s.randomizeAssignment();
    cout << s.trueInAssignment(getLit('d'));
  }
  cout << "  Fixed: ";      
  for (int i = 0; i < 10; i++) {        
    cout << s.trueInAssignment(getLit('d'));
  }
  cout << endl;  
  
  s.addAssumption(getLit('a'));
  ASS(s.hasAssumptions());
  ASS_EQ(s.getStatus(),SATSolver::SATISFIABLE);
  s.retractAllAssumptions();
  ASS(!s.hasAssumptions());
  // bloody interface
  ASS(s.getStatus() == SATSolver::UNKNOWN || s.getStatus() == SATSolver::SATISFIABLE);  
  
  ASS(!s.hasAssumptions());
  s.addAssumption(getLit('A'));
  ASS(s.hasAssumptions());
  ASS_EQ(s.getStatus(),SATSolver::UNSATISFIABLE);
  s.retractAllAssumptions();
  ASS(!s.hasAssumptions());
  ASS_EQ(s.getStatus(),SATSolver::UNKNOWN);
    
  s.addAssumption(getLit('a'));  
  ASS(s.hasAssumptions());
  ASS_EQ(s.getStatus(),SATSolver::SATISFIABLE);
  s.retractAllAssumptions();
  ASS(!s.hasAssumptions());
  // bloody interface
  ASS(s.getStatus() == SATSolver::UNKNOWN || s.getStatus() == SATSolver::SATISFIABLE);  
  
  // stupid interface, must call addClauses with empty,
  //  to let it know the status again
  s.addClauses(SATClauseIterator::getEmpty());
  ASS_EQ(s.getStatus(),SATSolver::SATISFIABLE);    
}

TEST_FUN(testSATSolverInterface)
{ 
  cout << endl << "Minisat" << endl;  
  MinisatInterfacing sMini(*env.options,true);
  testInterface(sMini);
  
  cout << endl << "Lingeling" << endl;
  LingelingInterfacing sLing(*env.options,true);
  testInterface(sLing);
  
  cout << endl << "TWL" << endl;
  TWLSolver sTWL(*env.options,true);
  testInterface(sTWL);  
}

