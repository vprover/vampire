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

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "SAT/SATLiteral.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/TWLSolver.hpp"
#include "SAT/Preprocess.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Options.hpp"
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
void SimpleSMT::getLiteralAssignmentStack(LiteralStack* litAsgn)
{

  CALL("SimpleSMT::getLiteralAssignmentStack");

  //for each positive literal appearing in the map
  for (unsigned i = 1; i <= _map.getNumberUpperBound(); i++) {
    Literal *literal;
    literal = _map.obj(i);
    ASS(literal->isPositive());

    switch (_solver->getAssignment(i)) {
    case SATSolver::TRUE:
      break;

    case SATSolver::FALSE:
      //# To my taste it would be better to have two variables -- positiveLiteral and then assignmentLiteral.
      //# I think it will make clearer the purpose of this switch statement (we'd have to have an assignment
      //# also in the TRUE case, but that doesn't seem as a high price to pay).
      literal = Literal::complementaryLiteral(literal);
      break;
    case SATSolver::DONT_CARE:
      //# one should probably add here a comment saying that we don't add DONT_CARE literals into the assignment
      continue;
    case SATSolver::NOT_KNOWN:
      ASSERTION_VIOLATION;
    }
    (*litAsgn).push(literal);
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
  env.options->set("inequality_splitting","0");
  env.options->set("flatten_top_level_conjunctions","on");
  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  Shell::Preprocess prepro(*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(*prb);

  SAT::SATClauseIterator clauseIterator = (initSATClauses(prb->clauseIterator()));
  initSATSolver(clauseIterator); 
}

/**
 * Call the congruence closure procedure for the literals in the stack @param . If the 
 * decision procedure returns SATISF/UNKNOWN return a stopping signal (false). Otherwise
 * create a new SAT clause and pass it to the SAT solver.
 * @param litAsgn stack with the literals assigned from the model generated by SAT
 * @return true if the decision procedure returns an unsatisfiable subset/false 
 * if the decision procedure returns SATISFIABLE/UNKNOWN
 */

unsigned SimpleSMT::getCClosureClauseStatus(LiteralStack *litAsgn)
{
  CALL("SimpleSMT::getCClosureClauseStatus");
  static DP::SimpleCongruenceClosure cClosure;
  cClosure.reset();

  cClosure.addLiterals(pvi(LiteralStack::Iterator(*litAsgn)));
  DP::DecisionProcedure::Status status; // = DP::DecisionProcedure::UNSATISFIABLE;

  status = cClosure.getStatus();
  litAsgn->reset();
  if (status == DP::DecisionProcedure::SATISFIABLE || status == DP::DecisionProcedure::UNKNOWN) {
    LOG("smt_dp_status",(status == DP::DecisionProcedure::SATISFIABLE ? "DP::SATISFIABLE" : "DP::UNKNOWN"));
    return (status == DP::DecisionProcedure::SATISFIABLE ? 2 : 3);
  }
  //equivalent to ASS(status==DP::UNSATISFIABLE);
  ASS_EQ(status , DP::DecisionProcedure::UNSATISFIABLE);
  LOG("smt_dp_status", "UNSATISFIABLE");
  RSTAT_CTR_INC("smt_conflict");
  
  cClosure.getUnsatisfiableSubset(*litAsgn);
  return 1;
}


SATClause* SimpleSMT::convertSATtoFO(LiteralStack *litAsgn)
{
  CALL("SimpleSMT::convertSATtoFO");
  LiteralStack::Iterator lIterator(*litAsgn);
  SAT::SATLiteralStack slitStack;
  
  while (lIterator.hasNext()) {
    Literal *literal = lIterator.next();
    literal = literal->complementaryLiteral(literal);
    SAT::SATLiteral slit(litTOSAT(literal));
    //negate the literal and add it to the stack of literals 
    slitStack.push(slit);
  }
  
  return SAT::SATClause::fromStack(slitStack);  
}

void SimpleSMT::addClauseToSAT(SATClause *clause)
{
  CALL("SimpleSMT::addClauseToSAT");
  LOG("smt_clause","Clause added:" << (*clause).toString());
  clause = SAT::Preprocess::removeDuplicateLiterals(clause);
  _solver->addClauses(pvi(getSingletonIterator(clause)), false);

}


unsigned SimpleSMT::compute()
{
  CALL("SimpleSMT::compute");
   LiteralStack litAsgn;
  SAT::SATSolver::Status statusSAT;
  statusSAT= _solver->getStatus();
  
  ASS(statusSAT == SAT::SATSolver::SATISFIABLE);
  unsigned CClosureStatus=1;
  do {
    statusSAT = _solver->getStatus();
    litAsgn.reset();
      switch (statusSAT) {
      case SAT::SATSolver::SATISFIABLE:
         getLiteralAssignmentStack(&litAsgn);
        break;
      case SAT::SATSolver::UNSATISFIABLE:
        return 0;
      default:
        return 3;
      }
   CClosureStatus = getCClosureClauseStatus(&litAsgn);
   SATClause* clause = convertSATtoFO(&litAsgn);
   addClauseToSAT(clause);
      
  } while (statusSAT == SAT::SATSolver::SATISFIABLE && CClosureStatus == 1);

  return CClosureStatus;
}

int SimpleSMT::perform(int argc, char** argv)
{
  CALL("SimpleSMT::perform");
  //preprocess the problem and initialize the SAT solver for this problem
  preprocessProblem(argc, argv);
  
  switch (compute()) {
      case 2:
        cout<<"SATISFIABLE"<<endl;
        break;
      case 0:
        cout << "UNSATISFIABLE" << endl;
        break;
      case 3:
        cout << "UNKNOWN: \n";
        break;
      default: break;
      }
  return 0;
}

}
