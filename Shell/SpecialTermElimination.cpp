/**
 * @file SpecialTermElimination.cpp
 * Implements class SpecialTermElimination.
 */

#include "Lib/List.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "Rectify.hpp"

#include "SpecialTermElimination.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

SpecialTermElimination::SpecialTermElimination()
: _defs(0)
{

}

void SpecialTermElimination::apply(UnitList*& units)
{
  CALL("SpecialTermElimination::apply(UnitList*&)");

  UnitList::DelIterator us(units);
  while(us.hasNext()) {
    Unit* u = us.next();
    if(u->isClause()) {
#if VDEBUG
      Clause* cl=static_cast<Clause*>(u);
      for(unsigned i=0;i<cl->length();i++) {
	//we do not allow special terms in clauses so we check that all clause literals
	//are shared (special terms can not be shared)
	ASS(!(*cl)[i]->shared());
      }
#endif
      continue;
    }
    Unit* v = apply(static_cast<FormulaUnit*>(u));
    if(v != u) {
	us.replace(v);
    }
  }
  us.insert(_defs);
}

/**
 * Apply SpecialTermElimination to formula @b fu and add introduced definitions
 * into @b defs
 */
FormulaUnit* SpecialTermElimination::apply(FormulaUnit* fu, UnitList*& defs)
{
  CALL("SpecialTermElimination::apply(FormulaUnit*, UnitList*&)");

  swap(defs, _defs);
  FormulaUnit* res = apply(fu);
  swap(defs, _defs);
  return res;
}

FormulaUnit* SpecialTermElimination::apply(FormulaUnit* fu0)
{
  CALL("SpecialTermElimination::apply(FormulaUnit*)");
  ASS(_letStack.isEmpty())

  FormulaUnit* fu = static_cast<FormulaUnit*>(Rectify::rectify(fu0));
  ASS(!fu->isClause());

  Formula* f = fu->formula();
  Formula* g = process(f);
  if(f==g) {
    return fu;
  }
  return new FormulaUnit(g, new Inference1(Inference::SPECIAL_TERM_ELIMINATION,fu), fu->inputType());
}

bool SpecialTermElimination::checkForTermLetReplacement(TermList t, TermList& res)
{
  CALL("SpecialTermElimination::checkForTermReplacement");

  if(!t.isSafe() || !eliminatingTermLet() || !MatchingUtils::matchTerms(_letStack.top().tLhs(), t)) {
    return false;
  }
  //we are replacing an occurrence of a term let lhs
  //instance by an instance of term let rhs
  res = MatchingUtils::getInstanceFromMatch(_letStack.top().tLhs(), t, _letStack.top().tRhs());
  return true;
}

/**
 * Eliminate any let expressions inside @b t. If the @b _letStack is non-empty,
 * propagate the let expression at the top of the stack. Otherwise also eliminate
 * all term ITE expressions.
 */
TermList SpecialTermElimination::processSpecialTerm(Term* t)
{
  CALL("SpecialTermElimination::processSpecialTerm");
  ASS(t->isSpecial());

  Term::SpecialTermData* sd = t->getSpecialData();
  if(t->functor()==Term::SF_TERM_ITE) {
    Formula* cond = sd->getCondition();
    //here we process the condition of the term ITE
    Formula* newCond = process(cond);
    TermList thenBranch = process(*t->nthArgument(0));
    TermList elseBranch = process(*t->nthArgument(1));
    if(eliminatingTermIte()) {
      t = eliminateTermIte(newCond, thenBranch, elseBranch);
    }
    else if(cond!=newCond || thenBranch!=*t->nthArgument(0) || elseBranch!=*t->nthArgument(1)) {
      t = Term::createTermITE(newCond, thenBranch, elseBranch);
    }
    return TermList(t);
  }
  else {
    if(t->functor()==Term::SF_LET_FORMULA_IN_TERM) {
      _letStack.push(LetSpec(sd->getLhsLiteral(), sd->getRhsFormula()));
    }
    else {
      ASS_EQ(t->functor(), Term::SF_LET_TERM_IN_TERM);
      _letStack.push(LetSpec(sd->getLhsTerm(), sd->getRhsTerm()));
    }
    //eliminate inner let expressions
    TermList body = process(*t->nthArgument(0));
    _letStack.pop();
    //and now continue with what we were doing before we met the let in t0
    body = process(body);
    return body;
  }
  ASSERTION_VIOLATION;

}

/**
 * Eliminate any let expressions inside @b t. If the @b _letStack is non-empty,
 * propagate the let expression at the top of the stack. Otherwise also eliminate
 * all term ITE expressions.
 */
TermList SpecialTermElimination::process(TermList t)
{
  CALL("SpecialTermElimination::process(TermList)");

  TermList repRes;
  if(checkForTermLetReplacement(t, repRes)) {
    t = repRes;
  }
  if(t.isTerm()) {
    if(t.term()->isSpecial()) {
      t = processSpecialTerm(t.term());
    }
    else {
      t = TermList(process(t.term()));
    }
  }
  return t;
}


/**
 * Eliminate any let expressions inside @b t0. If the @b _letStack is non-empty,
 * propagate the let expression at the top of the stack. Otherwise also eliminate
 * all term ITE expressions.
 */
Term* SpecialTermElimination::process(Term* t0)
{
  CALL("SpecialTermElimination::process(Term*)");
  ASS(!t0->isSpecial());

  Stack<TermList*> toDo(8);
  Stack<Term*> terms(8);
  Stack<bool> modified(8);
  Stack<TermList> args(8);

  modified.push(false);
  toDo.push(t0->args());

  for(;;) {
    TermList* tt=toDo.pop();
    if(tt->isEmpty()) {
      if(terms.isEmpty()) {
	//we're done, args stack contains modified arguments
	//of the literal.
	ASS(toDo.isEmpty());
	break;
      }
      Term* orig=terms.pop();
      ASS(!orig->isSpecial());

      if(!modified.pop()) {
	args.truncate(args.length() - orig->arity());
	args.push(TermList(orig));
	continue;
      }

      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);

      Term* newTerm;
      newTerm = Term::create(orig,argLst);

      args.truncate(args.length() - orig->arity());
      args.push(TermList(newTerm));
      modified.setTop(true);
      continue;
    } else {
      toDo.push(tt->next());
    }

    TermList tl=*tt;
    TermList replacement;
    if(checkForTermLetReplacement(tl, replacement)) {
      tl = replacement;
      modified.setTop(true);
    }
    if(tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    if(t->isSpecial()) {
      TermList procRes = processSpecialTerm(t);
      args.push(procRes);
      if(!procRes.isTerm() || procRes.term()!=t) {
	modified.setTop(true);
      }
      continue;
    }
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),t0->arity());

  if(!modified.pop()) {
    return t0;
  }

  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (t0->arity()-1);
  if(t0->isLiteral()) {
    return Literal::create(static_cast<Literal*>(t0),argLst);
  }
  else {
    return Term::create(t0,argLst);
  }
}

/**
 * Eliminate any let expressions inside @b f. If the @b _letStack is non-empty,
 * propagate the let expression at the top of the stack. Otherwise also eliminate
 * all term ITE expressions.
 */
Formula* SpecialTermElimination::process(Formula* f)
{
  CALL("SpecialTermElimination::process(Formula*)");

  switch (f->connective()) {
  case LITERAL:
  {
    Literal* lit0 = f->literal();
    Literal* lit = static_cast<Literal*>(process(lit0));
    ASS(lit->isLiteral());
    if(eliminatingFormulaLet() && MatchingUtils::match(_letStack.top().fLhs(), lit, false)) {
      //perform the formula let replacement
      Formula* res = MatchingUtils::getInstanceFromMatch(_letStack.top().fLhs(), lit,
	  _letStack.top().fRhs());
      return res;
    }
    else {
      return lit == lit0 ? f : new AtomicFormula(lit);
    }
  }

  case AND:
  case OR:
  {
    FormulaList* newArgs = process(f->args());
    if (newArgs == f->args()) {
      return f;
    }
    return new JunctionFormula(f->connective(), newArgs);
  }

  case IMP:
  case IFF:
  case XOR:
  {
    Formula* l = process(f->left());
    Formula* r = process(f->right());
    if (l == f->left() && r == f->right()) {
      return f;
    }
    return new BinaryFormula(f->connective(), l, r);
  }

  case NOT:
  {
    Formula* arg = process(f->uarg());
    if (f->uarg() == arg) {
      return f;
    }
    return new NegatedFormula(arg);
  }

  case FORALL:
  case EXISTS:
  {
    Formula* arg = process(f->qarg());
    if (arg == f->qarg()) {
      return f;
    }
    return new QuantifiedFormula(f->connective(),f->vars(),arg);
  }

  case ITE:
  {
    Formula* c = process(f->condArg());
    Formula* t = process(f->thenArg());
    Formula* e = process(f->elseArg());
    if (c == f->condArg() && t == f->thenArg() && e == f->elseArg()) {
      return f;
    }
    return new IteFormula(f->connective(), c, t, e);
  }

  case TERM_LET:
  case FORMULA_LET:
  {
    if(f->connective()==TERM_LET) {
      _letStack.push(LetSpec(f->termLetLhs(), f->termLetRhs()));
    }
    else {
      ASS_EQ(f->connective(),FORMULA_LET);
      _letStack.push(LetSpec(f->formulaLetLhs(), f->formulaLetRhs()));
    }
    //eliminate inner let expression...
    Formula* b1 = process(f->letBody());
    _letStack.pop();
    //and proceed with what we've been eliminating before
    Formula* b2 = process(b1);
    return b2;
  }

  case TRUE:
  case FALSE:
    return f;
  }
  ASSERTION_VIOLATION;
}

/**
 * Eliminate any let expressions inside @b fs. If the @b _letStack is non-empty,
 * propagate the let expression at the top of the stack. Otherwise also eliminate
 * all term ITE expressions.
 */
FormulaList* SpecialTermElimination::process(FormulaList* fs)
{
  CALL ("Rectify::rectify (FormulaList*)");

  if (fs->isEmpty()) {
    return fs;
  }
  Formula* f = fs->head();
  FormulaList* tail = fs->tail();
  Formula* g = process(f);
  FormulaList* gs = process(tail);

  if (f == g && tail == gs) {
    return fs;
  }
  return new FormulaList(g,gs);
}


/**
 * Eliminate term ITE expression @b t and resurn the resulting term.
 * Add the definition for introduced function into the @b _defs list.
 */
Term* SpecialTermElimination::eliminateTermIte(Formula * condition, TermList thenBranch, TermList elseBranch)
{
  CALL("SpecialTermElimination::eliminateTermIte");

  Formula::VarList* freeVars = condition->freeVariables();

  //TODO: add reusing of definitions belonging to simple formulas

  unsigned varUpperBound = 0;
  Stack<TermList> args;
  while(freeVars) {
    unsigned v = Formula::VarList::pop(freeVars);
    if(v>=varUpperBound) {
      varUpperBound = v;
    }
    args.push(TermList(v, false));
  }

  unsigned fnArity = args.size()+2;
  unsigned fnNum = env.signature->addIteFunction(fnArity);

  //first build and add definition

  TermList z1(varUpperBound, false);
  TermList z2(varUpperBound+1, false);
  args.push(z1);
  args.push(z2);
  TermList func = TermList(Term::create(fnNum, fnArity, args.begin()));

  Literal* eqThen = Literal::createEquality(true, func, z1);
  Literal* eqElse = Literal::createEquality(true, func, z2);

  Formula* def = new IteFormula(ITE, condition, new AtomicFormula(eqThen), new AtomicFormula(eqElse));
  FormulaUnit* defUnit = new FormulaUnit(def, new Inference(Inference::TERM_IF_THEN_ELSE_DEFINITION), Unit::AXIOM);
  UnitList::push(defUnit, _defs);

  //now put the actual then and else branches on the argument
  //stack and build the new term
  args.pop();
  args.pop();
  args.push(thenBranch);
  args.push(elseBranch);
  return Term::create(fnNum, fnArity, args.begin());
}

}
