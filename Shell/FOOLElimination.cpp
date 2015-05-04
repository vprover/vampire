/**
 * @file FOOLElimination.cpp
 * Implements class FOOLElimination.
 */

#include "Lib/List.hpp"
#include "Lib/Environment.hpp"
#include "Lib/ScopedLet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/Options.hpp"

#include "Rectify.hpp"

#include "FOOLElimination.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

FOOLElimination::FOOLElimination()
: _defs(0), _currentPrb(0)
{

}

bool FOOLElimination::hasSpecials(FormulaUnit* fu)
{
  CALL("FOOLElimination::hasSpecials");

  SubformulaIterator sfit(fu->formula());
  while(sfit.hasNext()) {
    Formula* f = sfit.next();
    switch(f->connective()) {
    case LITERAL:
      if(!f->literal()->shared()) {
	return true;
      }
      break;
    case BOOL_TERM:
      return true;
    default:
      break;
    }
  }
  return false;
}

void FOOLElimination::apply(Problem& prb)
{
  CALL("FOOLElimination::apply(Problem*)");

  ScopedLet<Problem*> plet(_currentPrb, &prb);
  apply(prb.units());
  prb.reportFOOLEliminated();
  prb.invalidateProperty();
}

void FOOLElimination::apply(UnitList*& units)
{
  CALL("FOOLElimination::apply(UnitList*&)");

  UnitList::DelIterator us(units);
  while(us.hasNext()) {
    Unit* u = us.next();
    if(u->isClause()) {
#if VDEBUG
      Clause* cl=static_cast<Clause*>(u);
      for(unsigned i=0;i<cl->length();i++) {
	//we do not allow special terms in clauses so we check that all clause literals
	//are shared (special terms can not be shared)
	ASS((*cl)[i]->shared());
      }
#endif
      continue;
    }
    Unit* v = apply(static_cast<FormulaUnit*>(u));
    if(v != u) {
	us.replace(v);
    }
  }
  appendAxioms();
  units = UnitList::concat(_defs, units);
  _defs = 0;

}

/**
 * Apply FOOLElimination to formula @b fu and add introduced definitions
 * into @b defs
 */
FormulaUnit* FOOLElimination::apply(FormulaUnit* fu, UnitList*& defs)
{
  CALL("FOOLElimination::apply(FormulaUnit*, UnitList*&)");

  swap(defs, _defs);
  FormulaUnit* res = apply(fu);
  swap(defs, _defs);
  return res;
}

FormulaUnit* FOOLElimination::apply(FormulaUnit* fu0)
{
  CALL("FOOLElimination::apply(FormulaUnit*)");
  ASS(_letStack.isEmpty())

  if(!hasSpecials(fu0)) {
    return fu0;
  }

  FormulaUnit* fu = Rectify::rectify(fu0);

  Formula* f = fu->formula();

  _currentFormulaVarSorts.reset();
  SortHelper::collectVariableSorts(f, _currentFormulaVarSorts);

  Formula* g = process(f);
  if(f==g) {
    return fu;
  }
  FormulaUnit* res = new FormulaUnit(g, new Inference1(Inference::FOOL_ELIMINATION,fu), fu->inputType());
  if(fu0->included()) {
    res->markIncluded();
  }
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] " << fu0->toString() << std::endl;
    env.out() << "[PP] " << res->toString() << std::endl;
    env.endOutput();
  }
  return res;
}

void FOOLElimination::appendAxioms() {
  // append "$true != $false"
  TermList t(Term::createConstant(Signature::FOOL_TRUE));
  TermList f(Term::createConstant(Signature::FOOL_FALSE));

  Formula* dc = new AtomicFormula(Literal::createEquality(false, t, f, Sorts::SRT_BOOL));
  Unit* disjoint_constants = new FormulaUnit(dc, new Inference(Inference::FOOL_AXIOM), Unit::AXIOM);

  _defs = new UnitList(disjoint_constants, _defs);

  // append "![X : $o]: X = $true | X = $false"
  TermList x;
  x.makeVar(0);
  Formula* xet = new AtomicFormula(Literal::createEquality(true, x, t, Sorts::SRT_BOOL));
  Formula* xef = new AtomicFormula(Literal::createEquality(true, x, f, Sorts::SRT_BOOL));
  List<Formula*>* xb = new List<Formula*>(xet, new List<Formula*>(xef));
  Formula* fd = new QuantifiedFormula(FORALL, new List<int>(0), new JunctionFormula(OR, xb));
  Unit* finite_domain = new FormulaUnit(fd, new Inference(Inference::FOOL_AXIOM), Unit::AXIOM);

  _defs = new UnitList(finite_domain, _defs);
}

bool FOOLElimination::checkForTermLetReplacement(TermList t, TermList& res)
{
  CALL("FOOLElimination::checkForTermReplacement");

  if(!t.isSafe() || !eliminatingTermLet() || !MatchingUtils::matchTerms(_letStack.top().tLhs(), t)) {
    return false;
  }
  //we are replacing an occurrence of a term let lhs
  //instance by an instance of term let rhs
  res = MatchingUtils::getInstanceFromMatch(_letStack.top().tLhs(), t, _letStack.top().tRhs());
//  LOGS("Term replacement for "<<t.toString()<<" found: "<<res.toString());
  return true;
}

/**
 * Eliminate any let expressions inside @b t. If the @b _letStack is non-empty,
 * propagate the let expression at the top of the stack. Otherwise also eliminate
 * all term ITE expressions.
 */
TermList FOOLElimination::processSpecialTerm(Term* t)
{
  CALL("FOOLElimination::processSpecialTerm");
  ASS(t->isSpecial());

  Term::SpecialTermData* sd = t->getSpecialData();
  if(t->functor()==Term::SF_TERM_ITE) {
    Formula* cond = sd->getCondition();
    //here we process the condition of the term ITE
    Formula* newCond = process(cond);
    TermList thenBranch = process(*t->nthArgument(0));
    TermList elseBranch = process(*t->nthArgument(1));
    if(eliminatingTermIte()) {
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] ste_if: " << t->toString();
      }            
      t = eliminateTermIte(newCond, thenBranch, elseBranch);
      if (env.options->showPreprocessing()) {        
        env.out() << "\n After elimination of ite:"<<t->toString() << std::endl;
        env.endOutput();
      }
    }
    else if(cond!=newCond || thenBranch!=*t->nthArgument(0) || elseBranch!=*t->nthArgument(1)) {
      t = Term::createITE(newCond, thenBranch, elseBranch);
    }

    return TermList(t);
  }
  else if (t->functor()==Term::SF_FORMULA) {
    NOT_IMPLEMENTED;
  }
  else {
    _letStack.push(LetSpec(sd->getLhs(), sd->getRhs()));
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
TermList FOOLElimination::process(TermList t)
{
  CALL("FOOLElimination::process(TermList)");

  if(t.isVar()) {
    TermList repRes;
    if(checkForTermLetReplacement(t, repRes)) {
      t = repRes;
    }
  }
  else if(t.isTerm()) {
    if(t.term()->isSpecial()) {
      t = processSpecialTerm(t.term());
    }
    else {
      t = TermList(process(t.term()));
      TermList repRes;
      if(checkForTermLetReplacement(t, repRes)) {
        t = repRes;
      }
    }
  }
  return t;
}


/**
 * Eliminate any let expressions inside @b t0. If the @b _letStack is non-empty,
 * propagate the let expression at the top of the stack. Otherwise also eliminate
 * all term ITE expressions.
 */
Term* FOOLElimination::process(Term* t0)
{
  CALL("FOOLElimination::process(Term*)");
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
	//of the original term/literal.
	ASS(toDo.isEmpty());
	break;
      }
      Term* orig=terms.pop();
      ASS(!orig->isSpecial());
      TermList tgt;
      if(!modified.pop()) {
	tgt = TermList(orig);
      }
      else {
	//here we assume, that stack is an array with
	//second topmost element as &top()-1, third at
	//&top()-2, etc...
	TermList* argLst=&args.top() - (orig->arity()-1);

	Term* newTerm;
	newTerm = Term::create(orig,argLst);

	modified.setTop(true);
	tgt = TermList(newTerm);
      }
      args.truncate(args.length() - orig->arity());

      TermList replacement;
      if(checkForTermLetReplacement(tgt, replacement)) {
        tgt = replacement;
        modified.setTop(true);
      }

      args.push(tgt);
      continue;
    } else {
      toDo.push(tt->next());
    }

    TermList tl=*tt;
    if(tl.isVar()) {
      TermList replacement;
      if(checkForTermLetReplacement(tl, replacement)) {
        tl = replacement;
        modified.setTop(true);
      }
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
Formula* FOOLElimination::process(Formula* f)
{
  CALL("FOOLElimination::process(Formula*)");

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

  case BOOL_TERM:
  {
    return f->toEquality();
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
FormulaList* FOOLElimination::process(FormulaList* fs)
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
 * Eliminate term ITE expression @b t and return the resulting term.
 * Add the definition for introduced function into the @b _defs list.
 */
Term* FOOLElimination::eliminateTermIte(Formula * condition, TermList thenBranch, TermList elseBranch)
{
  CALL("FOOLElimination::eliminateTermIte");

  Formula::VarList* freeVars = condition->freeVariables();
  //TODO: add reusing of definitions belonging to simple formulas
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] ste_if: " << "\n condition "
            << condition->toString() <<"\n then "<<thenBranch.toString()
            << "\n else " << elseBranch.toString() << std::endl;    
    env.endOutput();
  }
  unsigned varUpperBound = 0;
  Stack<unsigned> argSorts;
  Stack<TermList> args;
  while(freeVars) {
    unsigned v = Formula::VarList::pop(freeVars);
    if(v>=varUpperBound) {
      varUpperBound = v;
    }
    argSorts.push(_currentFormulaVarSorts.get(v));
    args.push(TermList(v, false));
  }

  unsigned thenSort = SortHelper::getResultSort(thenBranch, _currentFormulaVarSorts);
  unsigned elseSort = SortHelper::getResultSort(elseBranch, _currentFormulaVarSorts);
  ASS_EQ(thenSort, elseSort);

  //first build and add definition

  TermList z1(varUpperBound, false);
  TermList z2(varUpperBound+1, false);
  args.push(z1);
  argSorts.push(thenSort);
  args.push(z2);
  argSorts.push(thenSort);

  ASS_EQ(argSorts.size(),args.size());

  unsigned fnArity = args.size();
  unsigned fnNum = env.signature->addIteFunction(fnArity, argSorts.begin(), thenSort);
  TermList func = TermList(Term::create(fnNum, fnArity, args.begin()));
  //TODO: properly determine sort of the ITE term
  unsigned iteSort = SortHelper::getResultSort(func.term());

  Literal* eqThen = Literal::createEquality(true, func, z1, iteSort);
  Literal* eqElse = Literal::createEquality(true, func, z2, iteSort);

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] ste_if: "<< "\n eqThen "<<eqThen->toString() 
            <<"\n eqElse "<<eqElse->toString();
  }

  NOT_IMPLEMENTED;

  //now put the actual then and else branches on the argument
  //stack and build the new term
  args.pop();
  args.pop();
  args.push(thenBranch);
  args.push(elseBranch);
  return Term::create(fnNum, fnArity, args.begin());
}

}
