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
LiteralStack SimpleSMT::getLiteralAssignmentStack()
{

  CALL("SimpleSMT::getLiteralAssignmentStack");

  //### Variables of simple datatypes should be declared only when first needed
  //### (in this case then inside the loop). It helps when reading the code.
  Literal *literal;

  LiteralStack litAsgn;
  //for each positive literal appearing in the map
  for (unsigned i = 1; i <= _map.getNumberUpperBound(); i++) {
    literal = _map.obj(i);
    ASS(literal->isPositive());

    switch (_solver->getAssignment(i)) {
    //## redundant namespace specification
    case SAT::SATSolver::TRUE:
      break;

    case SAT::SATSolver::FALSE:
      //# To my taste it would be better to have two variables -- positiveLiteral and then assignmentLiteral.
      //# I think it will make clearer the purpose of this switch statement (we'd have to have an assignment
      //# also in the TRUE case, but that doesn't seem as a high price to pay).
      literal = Literal::complementaryLiteral(literal);
      break;
    case SAT::SATSolver::DONT_CARE:
      //# one should probably add here a comment saying that we don't add DONT_CARE literals into the assignment
      continue;
    case SAT::SATSolver::NOT_KNOWN:
      ASSERTION_VIOLATION;
    }
    litAsgn.push(literal);
    //  cout<<(*literal)<<endl;
  }

  return litAsgn;
}

/**
 * initializes the SAT solver which should be used
 * @param clite = problem clause iterator
 */

void SimpleSMT::initializeSATSolver(ClauseIterator clite)
{

  CALL("SimpleSMT::initializeSATSolver");

  SATClauseList *clauses = 0;
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

      SAT::SATLiteral slit(litTOSAT(literal));
      //how to create a sat literal? 
      satLitStack->push(slit);

      //## too many empty lines. However it is of course good to use a single empty line to separate
      //## logical parts of the code (or perhaps two empty lines to separate larger blocks in presence of too
      //## many single line separators.. however in such case I'd consider splitting into multiple functions)


    }


    SAT::SATClause *clause;

    //create a clause from stack of literals
    clause = SAT::SATClause::fromStack(*satLitStack);
    //add the clause to the list of problem clauses

    clause = SAT::Preprocess::removeDuplicateLiterals(clause);
    if (clause == 0)
      ; //### better clause!=0 without else statement
    else {
      SATClauseList::push(clause, clauses);
      //cout<<clause->toString()<<endl;
    }
  }

  //## I'd separate creation of the SAT solver object from conversion of clauses into SATClauses into two functions.

  //clauses - should contain the list of all cluases appearing in the problem
  SAT::SATClauseIterator clauseIterator = pvi(SATClauseList::Iterator(clauses));

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
  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  Shell::Preprocess prepro(*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(*prb);

  initializeSATSolver(prb->clauseIterator());

}

//## I'm thinking about the CClosure function -- not sure whether it's the right way of
//## separating things into functions. On the input side the function takes a stack of FO literals
//## that was extracted from the SAT solver and converted to FO by some other code.
//## However on the "output side" it converts FO literals to SAT and modifies the SAT solver
//## by adding a new clause to it.
//## I'd probably use several functions for this -- one would just get FO literals and give back
//## their UNSAT core (or report satisfiability), another function would wrap the SAT<->FO
//## conversion around it (together with creation of the SAT clause), and the last would then get
//## the assignment from the SAT solver and add the SAT clause into it.

/**
 * Call the congruence closure procedure for the literals in the stack @param . If the 
 * decision procedure returns SATISF/UNKNOWN return a stopping signal (false). Otherwise
 * create a new SAT clause and pass it to the SAT solver.
 * @param litAsgn stack with the literals assigned from the model generated by SAT
 * @return true if the decision procedure returns an unsatisfiable subset/false 
 * if the decision procedure returns SATISFIABLE/UNKNOWN
 */
bool SimpleSMT::getCClosureClauseStatus(LiteralStack litAsgn)
{
  SAT::SATLiteralStack slitStack;
  DP::SimpleCongruenceClosure cClosure;
  cClosure.addLiterals(pvi(LiteralStack::Iterator(litAsgn)));
  DP::DecisionProcedure::Status status; // = DP::DecisionProcedure::UNSATISFIABLE;

  status = cClosure.getStatus();
  //cout << (status == DP::DecisionProcedure::UNSATISFIABLE ? "DP::UNSAT" : " DP::SAT") << endl;
  litAsgn.reset();
  if (status == DP::DecisionProcedure::SATISFIABLE || status == DP::DecisionProcedure::UNKNOWN) {
    //## If this is considered a debugging output, it's good to have a macro for debugging
    //## outputs, so they can be all easily disabled. Preferably one can use the stuff declared in Debug/Log.hpp
    //## provided you declare your tag in Debug/Log_TagDecls.cpp and enable it using the "-tr tag_name" command
    //## line switch, or use tag "bug" which is always enabled.
    //## If this is not considered a debugging output, it's better to separate the code that does actual work
    //## and code that does outputs into separate functions (or even better, classes).
    cout << (status == DP::DecisionProcedure::SATISFIABLE ? "DP::SATISFIABLE" : "DP::UNKNOWN");
    return false;
  }
  //## One can use ASS_EQ here
  ASS(status == DP::DecisionProcedure::UNSATISFIABLE);

  cClosure.getUnsatisfiableSubset(litAsgn);
  LiteralStack::Iterator lIterator(litAsgn);

  while (lIterator.hasNext()) {
    Literal *literal = lIterator.next();
    literal = literal->complementaryLiteral(literal);
    SAT::SATLiteral slit(litTOSAT(literal));
    //negate the literal and add it to the stack of literals 
    slitStack.push(slit);
  }
  //## I'd merge the following two lines and just write "SAT::SATClause *clause = SAT::SATClause::fromStack(slitStack);"
  SAT::SATClause *clause;
  clause = SAT::SATClause::fromStack(slitStack);
  //cout << "Clause added:" << clause->toString() << endl;
  clause = SAT::Preprocess::removeDuplicateLiterals(clause);

  _solver->addClauses(pvi(getSingletonIterator(clause)), false);

  return true;
}


int SimpleSMT::perform(int argc, char** argv)
{
  CALL("SimpleSMT::perform");
  //preprocess the problem and initialize the SAT solver for this problem
  preprocessProblem(argc, argv);

  LiteralStack litAsgn;
  SAT::SATSolver::Status statusSAT;
  statusSAT= _solver->getStatus();
  
  ASS(statusSAT == SAT::SATSolver::SATISFIABLE);
  do {
    statusSAT = _solver->getStatus();
    litAsgn.reset();
    // cout << (statusSAT == SAT::SATSolver::SATISFIABLE ? "SAT" : "UNSAT") << endl;
      switch (statusSAT) {
      case SAT::SATSolver::SATISFIABLE:
        litAsgn = getLiteralAssignmentStack();
        break;
      case SAT::SATSolver::UNSATISFIABLE:
	//## I believe this is an output of the result of the algorithm -- this shouldn't be in the code
	//## that does actual reasoning, but better separate (or in this case rather all the reasoning code
	//## should be put out of this "main-like" function).
        cout << "UNSATISFIABLE" << endl;
        break;
      default:
        cout << "UNKNOWN: " << statusSAT << "\n";
        break;
      }

  } while (statusSAT == SAT::SATSolver::SATISFIABLE && getCClosureClauseStatus(litAsgn));

  return 0;
}

}
