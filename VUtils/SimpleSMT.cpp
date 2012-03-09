/**
 * @file SimpleSMT.cpp
 * Implements class SimpleSMT.
 */

#include <map>

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

SAT::SATLiteral SimpleSMT::litTOSAT(Literal *l, TwoWayMap& map)
{
  CALL("SimpleSMT::litToSAT");
  unsigned var = map.get(Literal::positiveLiteral(l));
  ASS_G(var, 0);
  return SATLiteral(var, l->isPositive());

}

int SimpleSMT::perform(int argc, char** argv)
{
  CALL("SimpleSMT::perform");

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
  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  Shell::Preprocess prepro(*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(*prb);


  //keeps a map between the literals found in the clauses and the SAT literals
  TwoWayMap map;

  SATClauseList *clauses = 0;

  ClauseIterator clite = prb->clauseIterator();

  while (clite.hasNext()) {
    Clause* cl = clite.next();

    //iterate over the set of literals in the clause

    Clause::Iterator ite(*cl);

    //create a satLiteral stack, needed for the creation of SATClause
    SAT::SATLiteralStack *satLitStack = new SAT::SATLiteralStack();

    //as long as you have literals, check if they are in the map, if they are 
    //then do nothing otherwise add them to the map.

    while (ite.hasNext()) {

      Literal *literal = ite.next();

      //check if it is already in the map and/or add it 

      SAT::SATLiteral slit(litTOSAT(literal, map));
      //how to create a sat literal? 
      satLitStack->push(slit);


    }


    SAT::SATClause *clause;

    //create a clause from stack of literals
    clause = SAT::SATClause::fromStack(*satLitStack);
    //add the clause to the list of problem clauses

    clause = SAT::Preprocess::removeDuplicateLiterals(clause);
    if (clause == 0)
      ;
    else {
      SATClauseList::push(clause, clauses);
      //cout<<clause->toString()<<endl;
    }
  }

  //clauses - should contain the list of all cluases appearing in the problem
  SAT::SATClauseIterator clauseIterator = pvi(SATClauseList::Iterator(clauses));

  Shell::Options opt;

  ScopedPtr<SATSolver> solver(new TWLSolver(opt, false));

  solver->ensureVarCnt(map.getNumberUpperBound() + 1);
  solver->addClauses(clauseIterator, false);

  //better switch 

  LiteralStack litAsgn;

  switch (solver->getStatus()) {
  case SAT::SATSolver::SATISFIABLE:

    Literal *literal;
    //for each positive literal appearing in the map
    for (unsigned i = 1; i <= map.getNumberUpperBound(); i++) {
      literal = map.obj(i);
      ASS(literal->isPositive());

      switch (solver->getAssignment(i)) {
      case SAT::SATSolver::TRUE:
        break;

      case SAT::SATSolver::FALSE:
        literal = Literal::complementaryLiteral(literal);
        break;
      case SAT::SATSolver::DONT_CARE:
        continue;
      case SAT::SATSolver::NOT_KNOWN:
        ASSERTION_VIOLATION;
      }
      litAsgn.push(literal);
      //  cout<<(*literal)<<endl;
    }

    break;
  case SAT::SATSolver::UNSATISFIABLE:
    cout << "Unsat\n";
    return 0;
    break;
  default:
    cout << "Unknown: " << solver->getStatus() << "\n";
    break;
  }


  //general structure of the SMT 
  /**
   * while SAT procedure gives satisfiable and DP gives UNSAT 
   * 
   * construct a new clause from the unsatisfiable subset
   * run the SAT prover again 
   * if UNSAT - done 
   * if SATISFIABLE call the DP 
   * 
   */


  //at this point we are certain that SATSolver returned SATISFIABLE
  //and we have the literal assignments in litAsgn

  SAT::SATClause *clause;
  SAT::SATLiteralStack slitStack;
  SAT::SATSolver::Status statusSAT;

  DP::SimpleCongruenceClosure cClosure;
  DP::DecisionProcedure::Status status; // = DP::DecisionProcedure::UNSATISFIABLE; 
  
  statusSAT = solver->getStatus();

  while (statusSAT == SAT::SATSolver::SATISFIABLE ) {

   
    cClosure.addLiterals(pvi(LiteralStack::Iterator(litAsgn)));

    status = cClosure.getStatus();
    cout << (status == DP::DecisionProcedure::UNSATISFIABLE ? "DP::UNSAT" : " DP::SAT") << endl;
    litAsgn.reset();


    if (status == DP::DecisionProcedure::SATISFIABLE || status == DP::DecisionProcedure::UNKNOWN) {
      cout << (status == DP::DecisionProcedure::SATISFIABLE ? "DP::SATISFIABLE" : "DP::UNKNOWN");
      break;
    }

    ASS(status == DP::DecisionProcedure::UNSATISFIABLE);

    cClosure.getUnsatisfiableSubset(litAsgn);
    LiteralStack::Iterator lIterator(litAsgn);

    while (lIterator.hasNext()) {
      Literal *literal = lIterator.next();
      // cout<<literal->toString()<<" and its complement ";
      literal = literal->complementaryLiteral(literal);
      SAT::SATLiteral slit(litTOSAT(literal, map));
      //slit= slit.opposite();
      //negate the literal and add it to the stack of literals 
      //   cout<<literal->toString()<<"  "<<slit.toString()<<endl;
      slitStack.push(slit);
      //  cout<<slit.toString()<<"  "<<slit.opposite().toString()<<endl;

    }

    //create the clause needed
    clause = SAT::SATClause::fromStack(slitStack);
    cout << "Clause added:" << clause->toString() << endl;

    clause = SAT::Preprocess::removeDuplicateLiterals(clause);
    //  SAT::SATClauseList::push(clause, clauses);
    // SAT::SATClauseIterator clauseIterator = pvi(SAT::SATClauseList::Iterator(clauses));
    
    solver->addClauses(pvi(getSingletonIterator(clause)), false);
    statusSAT = solver->getStatus();

    cout << (statusSAT == SAT::SATSolver::SATISFIABLE ? "SAT" : "UNSAT") << endl;


    switch (statusSAT) {
    case SAT::SATSolver::SATISFIABLE:

      Literal *literal;
      //for each positive literal appearing in the map
      for (unsigned i = 1; i <= map.getNumberUpperBound(); i++) {
        literal = map.obj(i);
        ASS(literal->isPositive());
        //   cout<<solver->getAssignment(i)<<"  "<<i<<endl;
        switch (solver->getAssignment(i)) {
        case SAT::SATSolver::TRUE:
          break;

        case SAT::SATSolver::FALSE:
          literal = Literal::complementaryLiteral(literal);
          break;

        case SAT::SATSolver::DONT_CARE:
          continue;

        case SAT::SATSolver::NOT_KNOWN:
          ASSERTION_VIOLATION;
        }

        litAsgn.push(literal);
        // cout<<(*literal)<<endl;
      }

      break;
    case SAT::SATSolver::UNSATISFIABLE:
      cout << "SAT::SATSolver::UNSATISFIABLE \n";
      return 0;
      break;
    default: break;
    }

    ASS(statusSAT == SAT::SATSolver::SATISFIABLE);

    slitStack.reset();
  }

  return 0;
}

}
