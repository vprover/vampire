/**
 * @file SimpleSMT.cpp
 * Implements class SimpleSMT.
 */

#include <map>

#include "Debug/RuntimeStatistics.hpp"
#include "Debug/Tracer.hpp"
#include "Forwards.hpp"
#include "VUtils/SimpleSMT.hpp"

#include "DP/SimpleCongruenceClosure.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "SAT/SATClauseSharing.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/MinimizingSolver.hpp"
#include "SAT/TWLSolver.hpp"
#include "SAT/Preprocess.hpp"

#include "Shell/UIHelper.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Options.hpp"

#include "Test/CheckedSatSolver.hpp"

#include "PreprocessingEvaluator.hpp"

namespace VUtils {

using namespace Shell;
using namespace Kernel;
using namespace SAT;

/**
 * Convert literal l to a sat literal and store it in the map if is a new literal
 * @param l - literal to be converted
 * @return sat literal. The number of the literal if found in the map, or a new one of the literal 
 * is not in the map
 */
SAT::SATLiteral SimpleSMT::litTOSAT(Literal *l)
{
  CALL("SimpleSMT::litToSAT");
  unsigned var = _map.get(Literal::positiveLiteral(l));
  ASS_G(var, 0);
  return SATLiteral(var, l->isPositive());

}

/**
 * Return the stack of literals with assignment form the sat model
 * @return a stack of assigned literals 
 */
void SimpleSMT::getLiteralAssignmentStack(LiteralStack& litAsgn)
{
  CALL("SimpleSMT::getLiteralAssignmentStack");
  ASS(litAsgn.isEmpty());

  //for each positive literal appearing in the map
  for (unsigned i = 1; i <= _map.getNumberUpperBound(); i++) {
    Literal* posLiteral = _map.obj(i);
    ASS(posLiteral->isPositive());

    Literal* asgnLit;

    switch (_solver->getAssignment(i)) {
    case SATSolver::TRUE:
      asgnLit = posLiteral;
      break;

    case SATSolver::FALSE:
      asgnLit = Literal::complementaryLiteral(posLiteral);
      break;
    case SATSolver::DONT_CARE:
      //we don't add DONT_CARE literals into the assignment
      continue;
    case SATSolver::NOT_KNOWN:
      ASSERTION_VIOLATION;
    }
    litAsgn.push(asgnLit);
  }

}

/**
 * initializes the SAT solver which should be used
 * @param clite = problem clause iterator
 */

SATClauseIterator SimpleSMT::initSATClauses(ClauseIterator clite)
{
  CALL("SimpleSMT::initSATClauses");
  SATClauseList *clauses = 0;
  while (clite.hasNext()) {
    Clause* cl = clite.next();
    //iterate over the set of literals in the clause
    Clause::Iterator ite(*cl);
    //create a satLiteral stack, needed for the creation of SATClause
    SATLiteralStack *satLitStack = new SATLiteralStack();
    //as long as you have literals, check if they are in the map, if they are 
    //then do nothing otherwise add them to the map.

    while (ite.hasNext()) {
      Literal *literal = ite.next();
      //check if it is already in the map and/or add it 
      SAT::SATLiteral slit(litTOSAT(literal));
      //create a sat literal
      satLitStack->push(slit);
    }

    SAT::SATClause *clause;
    //create a clause from stack of literals
    clause = SAT::SATClause::fromStack(*satLitStack);
    //add the clause to the list of problem clauses

    clause = SAT::Preprocess::removeDuplicateLiterals(clause);
    if (clause != 0){
      SATClauseList::push(clause, clauses);
      //cout<<clause->toString()<<endl;
    }
    LOG("smt_sat_clauses", "initial: "<<clause->toString());
  }
  return pvi(SATClauseList::Iterator(clauses));

}


void SimpleSMT::initSATSolver(SATClauseIterator clauseIterator)
{
  CALL("SimpleSMT::initSATSolver");
   Shell::Options opt;
//  _solver = new Test::CheckedSatSolver(new MinimizingSolver(new TWLSolver(opt, false)));
//  _solver = new MinimizingSolver(new TWLSolver(opt, false));
  _solver = new TWLSolver(opt, false);
  _solver->ensureVarCnt(_map.getNumberUpperBound() + 1);
  _solver->addClauses(clauseIterator, false);
}


/**
 * Preprocess the problem to be solved and initializes the sat solver
 * @param argc 
 * @param argv 
 *
 */
void SimpleSMT::preprocessProblem(int argc, char** argv)
{
  CALL("SimpleSMT::preprocessProblem")

  string fname;
  if (argc < 3) {
    fname = "";
  } else {
    fname = argv[2];
  }

  if (fname.substr(fname.size() - 4) == ".smt")
    env.options->setInputSyntax(Options::IS_SMTLIB);

  cout << "Now we should be solving " << fname << endl;

  env.options->setInputFile(fname);
  env.options->set("aig_bdd_sweeping","on");
  env.options->set("flatten_top_level_conjunctions","on");
  env.options->set("distinct_processor","on");
  env.options->set("inequality_splitting","0");
  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  Shell::Preprocess prepro(*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(*prb);

  SAT::SATClauseIterator clauseIterator = (initSATClauses(prb->clauseIterator()));
  initSATSolver(clauseIterator); 
}


DecisionProcedure::Status SimpleSMT::addTheoryConflicts(LiteralStack& assignment)
{
  CALL("SimpleSMT::checkTheoryStatus");

  static DP::SimpleCongruenceClosure cClosure;
  cClosure.reset();
//  DP::SimpleCongruenceClosure cClosure;

  cClosure.addLiterals(pvi(LiteralStack::Iterator(assignment)));
  DP::DecisionProcedure::Status status; // = DP::DecisionProcedure::UNSATISFIABLE;

  status = cClosure.getStatus(true);
  if (status == DP::DecisionProcedure::SATISFIABLE || status == DP::DecisionProcedure::UNKNOWN) {
    LOG("smt_dp_status",(status == DP::DecisionProcedure::SATISFIABLE ? "DP::SATISFIABLE" : "DP::UNKNOWN"));
    return status;
  }
  //equivalent to ASS(status==DP::UNSATISFIABLE);
  ASS_EQ(status , DP::DecisionProcedure::UNSATISFIABLE);
  LOG("smt_dp_status", "UNSATISFIABLE");

  static LiteralStack unsatCore;
  static SATClauseStack conflictClauses;
  conflictClauses.reset();
  unsigned confCnt = cClosure.getUnsatCoreCount();
  for(unsigned i=0; i<confCnt; i++) {
    unsatCore.reset();
    cClosure.getUnsatCore(unsatCore, i);
    SATClause* cl = convertSATtoFO(&unsatCore);
    conflictClauses.push(cl);
  }
  addClausesToSAT(conflictClauses);
  
  RSTAT_CTR_INC("smt_conflict");
  RSTAT_CTR_INC_MANY("smt_conflict_clauses", confCnt);

  return status;
}

///**
// * Call the congruence closure procedure for the literals in the stack @param . If the
// * decision procedure returns SATISF/UNKNOWN return a stopping signal (false). Otherwise
// * create a new SAT clause and pass it to the SAT solver.
// * @param litAsgn stack with the literals assigned from the model generated by SAT
// * @return true if the decision procedure returns an unsatisfiable subset/false
// * if the decision procedure returns SATISFIABLE/UNKNOWN
// */
//
//DecisionProcedure::Status SimpleSMT::getCClosureClauseStatus()
//{
//  CALL("SimpleSMT::getCClosureClauseStatus");
//  static DP::SimpleCongruenceClosure cClosure;
//  cClosure.reset();
//
//  cClosure.addLiterals(pvi(LiteralStack::Iterator(*litAsgn)));
//  DP::DecisionProcedure::Status status; // = DP::DecisionProcedure::UNSATISFIABLE;
//
//  status = cClosure.getStatus(true);
//  if (status == DP::DecisionProcedure::SATISFIABLE || status == DP::DecisionProcedure::UNKNOWN) {
//    LOG("smt_dp_status",(status == DP::DecisionProcedure::SATISFIABLE ? "DP::SATISFIABLE" : "DP::UNKNOWN"));
//  }
//  else {
//    //equivalent to ASS(status==DP::UNSATISFIABLE);
//    ASS_EQ(status , DP::DecisionProcedure::UNSATISFIABLE);
//    LOG("smt_dp_status", "UNSATISFIABLE");
//    RSTAT_CTR_INC("smt_conflict");
//  }
//
//  return status;
//}


SATClause* SimpleSMT::convertSATtoFO(LiteralStack *litAsgn)
{
  CALL("SimpleSMT::convertSATtoFO");
  LiteralStack::Iterator lIterator(*litAsgn);
  SAT::SATLiteralStack slitStack;
  
  LOG("smt_confl_detail","building conflict clause:");

  while (lIterator.hasNext()) {
    Literal *literal = lIterator.next();
    SAT::SATLiteral slit(litTOSAT(literal));
    //negate the literal and add it to the stack of literals
    if(_solver->isZeroImplied(slit.var())) {
      LOG("smt_confl_detail","  - "<<(*literal)<<" zero implied");
    }
    else {
      LOG("smt_confl_detail","  + "<<(*literal));
      slitStack.push(slit.opposite());
    }
    ASS(_solver->trueInAssignment(slit));
  }
  
  return SAT::SATClause::fromStack(slitStack);  
}

void SimpleSMT::addClausesToSAT(SATClauseStack& clauses)
{
  CALL("SimpleSMT::addClausesToSAT");
  ASS(clauses.isNonEmpty());

  TRACE("smt_clause",
      SATClauseStack::ConstIterator cit(clauses);
      while(cit.hasNext()) {
	SATClause* cl = cit.next();
	tout << "Clause added:" << (*cl).toString()<<endl;
      }
    );

  unsigned minSz = clauses.top()->size();

  SATClauseStack::ConstIterator cit(clauses);
  while(cit.hasNext()) {
    SATClause* cl = cit.next();
    minSz = min(cl->size(), minSz);
  }

  SATClauseStack::DelIterator dcit(clauses);
  while(dcit.hasNext()) {
    SATClause* cl = dcit.next();
    if(cl->size()>minSz+1) {
      dcit.del();
      cl->destroy();
    }
  }

  //conflict clauses should never have duplicate variables,
  //so we don't need to do duplicate variable removal
  _solver->addClauses(pvi(SATClauseStack::Iterator(clauses)), false);

}


DecisionProcedure::Status SimpleSMT::compute()
{
  CALL("SimpleSMT::compute");
  
  LiteralStack asgnStack;
  SATSolver::Status satStatus = _solver->getStatus();
  while(satStatus==SATSolver::SATISFIABLE) {
    asgnStack.reset();
    getLiteralAssignmentStack(asgnStack);
    DecisionProcedure::Status theoryStatus = addTheoryConflicts(asgnStack);
    if(theoryStatus!=DecisionProcedure::UNSATISFIABLE) {
      return theoryStatus;
    }
    _conflictIndex++;
    satStatus = _solver->getStatus();
  }
  ASS_EQ(satStatus,SATSolver::UNSATISFIABLE);
  return DecisionProcedure::UNSATISFIABLE;

//  ASS(statusSAT == SAT::SATSolver::SATISFIABLE);
//  DecisionProcedure::Status theoryStatus;
//  do {
//    litAsgn.reset();
//    switch (statusSAT) {
//    case SAT::SATSolver::SATISFIABLE:
//      break;
//    case SAT::SATSolver::UNSATISFIABLE:
//      return 0;
//    default:
//      return 3;
//    }
//    (litAsgn);
//    SATClause* clause = convertSATtoFO(&litAsgn);
//    addClauseToSAT(clause);
//
//    statusSAT = _solver->getStatus();
//  } while (statusSAT == SAT::SATSolver::SATISFIABLE && CClosureStatus == 1);
//
//  return CClosureStatus;
}

int SimpleSMT::perform(int argc, char** argv)
{
  CALL("SimpleSMT::perform");
  //preprocess the problem and initialize the SAT solver for this problem
  preprocessProblem(argc, argv);
  
  switch (compute()) {
      case DecisionProcedure::SATISFIABLE:
        cout<<"SATISFIABLE"<<endl;
        break;
      case DecisionProcedure::UNSATISFIABLE:
        cout << "UNSATISFIABLE" << endl;
        break;
      case DecisionProcedure::UNKNOWN:
        cout << "UNKNOWN: \n";
        break;
      default: break;
      }
  return 0;
}

}
