
/*
 * File SimpleSMT.cpp.
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
 * @file SimpleSMT.cpp
 * Implements class SimpleSMT.
 */

#include <map>

#include "Debug/RuntimeStatistics.hpp"
#include "Debug/Tracer.hpp"
#include "Forwards.hpp"
#include "VUtils/SimpleSMT.hpp"

#include "DP/ShortConflictMetaDP.hpp"
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

#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Test/CheckedSatSolver.hpp"

#include "PreprocessingEvaluator.hpp"

using namespace VUtils;
using namespace Shell;
using namespace Kernel;
using namespace SAT;
using namespace DP;

SimpleSMT::SimpleSMT()
: _conflictIndex(0)
{
  CALL("SimpleSMT::SimpleSMT");

  Shell::Options opt;
//  _solver = new Test::CheckedSatSolver(new MinimizingSolver(new TWLSolver(opt, false)));
//  _solver = new MinimizingSolver(new TWLSolver(opt, false));
  _solver = new TWLSolver(opt, false);
  _dp = new ShortConflictMetaDP(new DP::SimpleCongruenceClosure(), _map, *_solver);
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
    SATClause* satCl = _map.toSAT(cl);
    if (satCl != 0){
      SATClauseList::push(satCl, clauses);
    }
  }
  return pvi(SATClauseList::DestructiveIterator(clauses));
} // SimpleSMT::initSATClauses

void SimpleSMT::initSATSolver(SATClauseIterator clauseIterator)
{
  CALL("SimpleSMT::initSATSolver");

  _solver->ensureVarCnt(_map.maxSATVar() + 1);
  _solver->addClauses(clauseIterator, false);
} // SimpleSMT::initSATSolver


/**
 * Preprocess the problem to be solved and initializes the sat solver.
 * The input file name is passed in the command line. If none, will read from
 * stdin.
 */
void SimpleSMT::preprocessProblem(int argc, char** argv)
{
  CALL("SimpleSMT::preprocessProblem")
    
  vstring fname;
  if (argc < 3) {
    fname = "";
  }
  else {
    fname = argv[2];
  }

  if (fname.substr(fname.size() - 4) == ".smt") {
    env.options->setInputSyntax(Options::IS_SMTLIB);
  }

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
} // preprocessProblem

DecisionProcedure::Status SimpleSMT::addTheoryConflicts(LiteralStack& assignment)
{
  CALL("SimpleSMT::checkTheoryStatus");

  _dp->reset();
  _dp->addLiterals(pvi(LiteralStack::Iterator(assignment)));
  DP::DecisionProcedure::Status status; // = DP::DecisionProcedure::UNSATISFIABLE;
  status = _dp->getStatus(true);
  if (status == DP::DecisionProcedure::SATISFIABLE || status == DP::DecisionProcedure::UNKNOWN) {
    return status;
  }
  //equivalent to ASS(status==DP::UNSATISFIABLE);
  ASS_EQ(status , DP::DecisionProcedure::UNSATISFIABLE);

  static LiteralStack unsatCore;
  static SATClauseStack conflictClauses;
  conflictClauses.reset();
  unsigned confCnt = _dp->getUnsatCoreCount();
  for(unsigned i=0; i<confCnt; i++) {
    unsatCore.reset();
    _dp->getUnsatCore(unsatCore, i);
    SATClause* cl = _map.createConflictClause(unsatCore);
//    SATClause* cl = convertSATtoFO(&unsatCore);
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
//  }
//  else {
//    //equivalent to ASS(status==DP::UNSATISFIABLE);
//    ASS_EQ(status , DP::DecisionProcedure::UNSATISFIABLE);
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
  
  while (lIterator.hasNext()) {
    Literal *literal = lIterator.next();
    SAT::SATLiteral slit(_map.toSAT(literal));
    //negate the literal and add it to the stack of literals
    if(!_solver->isZeroImplied(slit.var())) {      
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

  //conflict clauses should never have duplicate variables,
  //so we don't need to do duplicate variable removal
  _solver->addClauses(pvi(SATClauseStack::Iterator(clauses)), false);
}

/**
 * Call a preprocessed problem.
 */ 
DecisionProcedure::Status SimpleSMT::compute()
{
  CALL("SimpleSMT::compute");
  
  LiteralStack asgnStack;
  SATSolver::Status satStatus = _solver->getStatus();
  while(satStatus==SATSolver::SATISFIABLE) {
    asgnStack.reset();
    _map.collectAssignment(*_solver,asgnStack);
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
} // compute

/**
 * A simple SMT solver call: read a problem from the input file or stdin, solve
 * it and print the result (satisfiable, unsatisfiable or unknown)
 */
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
  default:
    break;
  }
  env.statistics->phase = Statistics::FINALIZATION;
  env.statistics->print(cout);
  return 0;
} // perform
