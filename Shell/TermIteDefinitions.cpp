/**
 * @file TermIteDefinitions.cpp
 * Implements class TermIteDefinitions.
 */

#include "Lib/List.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "TermIteDefinitions.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

/**
 * Add definitions for if-then-else expressions
 *
 * The followind two clauses are added for each predicate for
 * which an ITE functor was introduced:
 *
 * ~P(x1,...,xn) \/ p(x1,...,xn,z1,z2) = z1
 * P(x1,...,xn) \/ p(x1,...,xn,z1,z2) = z2
 */
void TermIteDefinitions::addDefinitions(UnitList*& units)
{
  CALL("TermIteDefinitions::addDefinitions");

  Stack<TermList> args;

  VirtualIterator<unsigned> funs = env.signature->getIteFunctors();
  while(funs.hasNext()) {
    unsigned fnNum = funs.next();
    unsigned predNum = env.signature->getIteFunctorPred(fnNum);
    unsigned fnArity = env.signature->functionArity(fnNum);
    ASS_EQ(fnArity, env.signature->predicateArity(predNum)+2);
    args.reset();
    for(unsigned i=0; i<fnArity; i++) {
      args.push(TermList(i, false));
    }
    //the two variables that are in the function but not in the predicate
    TermList z1(fnArity-2, false);
    TermList z2(fnArity-1, false);
    TermList func = TermList(Term::create(fnNum, fnArity, args.begin()));

    //For predicate construction, only the first fnArity-2 terms on the args stack are used.

    //Then branch:
    Literal* predThen = Literal::create(predNum, fnArity-2, false, false, args.begin());
    Literal* eqThen = Literal::createEquality(true, func, z1);
    Clause* thenCl = Clause::fromIterator(getConcatenatedIterator(getSingletonIterator(predThen),
	getSingletonIterator(eqThen)), Unit::AXIOM, new Inference(Inference::TERM_IF_THEN_ELSE_DEFINITION));
    UnitList::push(thenCl, units);

    //Else branch:
    Literal* predElse = Literal::create(predNum, fnArity-2, true, false, args.begin());
    Literal* eqElse = Literal::createEquality(true, func, z2);
    Clause* elseCl = Clause::fromIterator(getConcatenatedIterator(getSingletonIterator(predElse),
	getSingletonIterator(eqElse)), Unit::AXIOM, new Inference(Inference::TERM_IF_THEN_ELSE_DEFINITION));
    UnitList::push(elseCl, units);
  }
}

}
