/**
 * @file FunctionDefinition.cpp
 * Implements class FunctionDefinition implementing work with definitions.
 *
 * @since 28/05/2004 Manchester
 */

#include "../Debug/Tracer.hpp"

#include "../Lib/Allocator.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Formula.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/SubstHelper.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermVarIterator.hpp"
#include "../Kernel/TermFunIterator.hpp"

#include "FunctionDefinition.hpp"
// #include "Substitution.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Auxiliary structure to represent information about function definitions.
 * @since 29/05/2004 Manchester
 */
struct FunctionDefinition::Def
{
  enum Mark {
    UNTOUCHED,
    SAFE,
    UNFOLDED,
    BLOCKED,
    REMOVED
  };
  /** Unit containing a definition */
  Clause* defCl;
  /** The defined function symbol number */
  int fun;
  /** The lhs of the definition */
  const Term* lhs;
  /** The rhs of the definition */
  const Term* rhs;

  Mark mark;
  /** is the definition linear? */
  bool linear;
  /** strict means that all lhs variables occur in rhs */
  bool strict;
  /** first defined function that is used in @b rhs, or -1 if there isn't such */
  int containedFn;

  IntList* dependentFns;

  Def(const Term* l,const Term* r,bool lin,bool str)
    : fun(l->functor()),
      lhs(l),
      rhs(r),
      mark(UNTOUCHED),
      linear(lin),
      strict(str),
      containedFn(-1),
      dependentFns(0)
  {}

  CLASS_NAME("FunctionDefintion::Def");
  USE_ALLOCATOR(Def);
}; // class FunctionDefintion::Def


/**
 * Initialise a function definition.
 * Move all definitions from the problem to _definitions and _map.
 * @since 29/05/2004 Manchester
 */
FunctionDefinition::FunctionDefinition ()
  : _defStore(32),
    _found(0),
    _removed(0)
{
  CALL("FunctionDefinition::FunctionDefinition");
} // FunctionDefinition::FunctionDefinition


void FunctionDefinition::removeAllDefinitions(UnitList* units)
{
  CALL("FunctionDefinition::removeAllDefinitions");


  UnitList::DelIterator us(units);
  while(us.hasNext()) {
    Clause* cl=static_cast<Clause*>(us.next());
    ASS(cl->isClause());
    Def* d=isFunctionDefinition(cl);
    if(d) {
      d->defCl=cl;
      _defs.insert(d->fun, d);
      us.del();
    }

  }

  if(!_defs.size()) {
    return;
  }

  Stack<int> indep(16);
  Fn2DefMap::Iterator dit(_defs);
  while(dit.hasNext()) {
    Def* d=dit.next();



    TermFunIterator tfit(d->rhs);
    while(tfit.hasNext()) {
      int rhsFn=tfit.next();
      if(!_defs.find(rhsFn)) {
	continue;
      }
      d->containedFn=rhsFn;
      break;
    }
    if(d->containedFn==-1) {
      d->mark=Def::SAFE;
      indep.push(d->fun);
    }
  }
}

TermList FunctionDefinition::unfoldDefinition(Term* t)
{
  CALL("FunctionDefinition::unfoldDefinition");

  static DHMap<unsigned, TermList> bindings;
  bindings.reset();

  Def* d=_defs.get(t->functor());
  TermList* dargs=d->lhs->args();
  TermList* targs=t->args();
  while(dargs->isNonEmpty()) {
    ASS(targs->isNonEmpty());
    ALWAYS(bindings.insert(dargs->var(), *targs));
    dargs=dargs->next();
    targs=targs->next();
  }

  return SubstHelper::apply(d->rhs, SubstHelper::getMapApplicator(&bindings), false);
}

TermList FunctionDefinition::safeApplyDefinitions(Term* t)
{
  CALL("FunctionDefinition::safeApplyDefinitions");

//  static Stack<TermList*> toDo(8);
//  static Stack<Term*> terms(8);
//  static Stack<bool> modified(8);
//  static Stack<TermList> args(8);
//  ASS(toDo.isEmpty());
//  ASS(terms.isEmpty());
//  modified.reset();
//  args.reset();
//
//  modified.push(false);
//  toDo.push(trm->args());
//
//  for(;;) {
//    TermList* tt=toDo.pop();
//    if(tt->isEmpty()) {
//      if(terms.isEmpty()) {
//	//we're done, args stack contains modified arguments
//	//of the literal.
//	ASS(toDo.isEmpty());
//	break;
//      }
//      Term* orig=terms.pop();
//      if(!modified.pop()) {
//	args.truncate(args.length() - orig->arity());
//	args.push(TermList(orig));
//	continue;
//      }
//      //here we assume, that stack is an array with
//      //second topmost element as &top()-1, third at
//      //&top()-2, etc...
//      TermList* argLst=&args.top() - (orig->arity()-1);
//
//      Term* newTrm;
//      if(noSharing || !orig->shared()) {
//	newTrm=Term::createNonShared(orig,argLst);
//      } else {
//	newTrm=Term::create(orig,argLst);
//      }
//      args.truncate(args.length() - orig->arity());
//      args.push(TermList(newTrm));
//
//      modified.setTop(true);
//      continue;
//    }
//    toDo.push(tt->next());
//
//    TermList tl=*tt;
//    if(tl.isOrdinaryVar()) {
//      TermList tDest=applicator.apply(tl.var());
//      args.push(tDest);
//      if(tDest!=tl) {
//	modified.setTop(true);
//      }
//      continue;
//    }
//    if(tl.isSpecialVar()) {
//      args.push(tl);
//      continue;
//    }
//    ASS(tl.isTerm());
//    Term* t=tl.term();
//    if(t->shared() && t->ground()) {
//      args.push(tl);
//      continue;
//    }
//    terms.push(t);
//    modified.push(false);
//    toDo.push(t->args());
//  }
//  ASS(toDo.isEmpty());
//  ASS(terms.isEmpty());
//  ASS_EQ(modified.length(),1);
//  ASS_EQ(args.length(),trm->arity());
//
//  if(!modified.pop()) {
//    return trm;
//  }
//
//  //here we assume, that stack is an array with
//  //second topmost element as &top()-1, third at
//  //&top()-2, etc...
//  TermList* argLst=&args.top() - (trm->arity()-1);
//  if(trm->isLiteral()) {
//    ASS(!noSharing);
//    return Literal::create(static_cast<Literal*>(trm),argLst);
//  } else {
//    if(noSharing || !trm->shared()) {
//      return Term::createNonShared(trm,argLst);
//    } else {
//      return Term::create(trm,argLst);
//    }
//  }
}

///**
// * Scan a list of units and memorise information about them
// * in the stack.
// * @since 26/05/2007 Manchester
// */
//void FunctionDefinition::scan (const UnitList* units)
//{
//  CALL("FunctionDefinition::scan");
//
//  UnitList::Iterator is(units);
//  while (is.hasNext()) {
//    const Unit* unit = is.next();
//    Def* def = isFunctionDefinition(*unit);
//    if (! def) {
//      continue;
//    }
//    def->unit = unit;
//    _defs.push(def);
//    string prefix = "";
//    if (def->linear) {
//      prefix += "linear ";
//    }
//    if (! def->strict) {
//      prefix += "non-strict ";
//    }
//    cout << prefix << "definition found: " << unit->toString() << "\n";
//  }
//} // FunctionDefinition::FunctionDefinition

/**
 * Destroy by deallocating all Defs.
 * @since 26/05/2007 Manchester
 */
FunctionDefinition::~FunctionDefinition ()
{
  CALL("FunctionDefinition::~FunctionDefinition");

  while (_defStore.isNonEmpty()) {
    delete _defStore.pop();
  }
} // FunctionDefinition::~FunctionDefinition

///**
// * If the the unit if a function definition f(x1,...,xn) = t,
// * return the Def structure representing information about the definition.
// * @since 26/05/2007 Manchester
// */
FunctionDefinition::Def*
FunctionDefinition::isFunctionDefinition (const Unit& unit)
{
  CALL("FunctionDefinition::isFunctionDefinition(const Unit&)");
  if (unit.isClause()) {
    return isFunctionDefinition(const_cast<Clause*>(static_cast<const Clause*>(&unit)));
  }
  return isFunctionDefinition(static_cast<const FormulaUnit&>(unit));
} // Definition::isFunctionDefinition (const Clause& c)


/**
 * If the the clause if a function definition f(x1,...,xn) = t,
 * return the Def structure representing information about the definition.
 * @since 05/06/2004 Manchester
 * @since 26/05/2007 Manchester modified for new data structures
 */
FunctionDefinition::Def*
FunctionDefinition::isFunctionDefinition (Clause* clause)
{
  CALL("FunctionDefinition::isFunctionDefinition(Clause*)");

  if (clause->length() != 1) {
    return 0;
  }
  return isFunctionDefinition((*clause)[0]);
} // Definition::isFunctionDefinition (Clause* c)

/**
 * If the literal if a function definition f(x1,...,xn) = t.
 * return the Def structure representing information about the definition.
 * @since 09/05/2002 Manchester
 * @since 05/01/2004 Manchester, simplified
 * @since 26/05/2007 Manchester modified for new data structures
 */
FunctionDefinition::Def*
FunctionDefinition::isFunctionDefinition (const Literal* lit)
{
  CALL("FunctionDefinition::isFunctionDefinition(const Literal*)");

  if (! lit->isPositive() ||
      ! lit->isEquality()) {
    return 0;
  }

  // the atom is an equality
  const TermList* args = lit->args();
  if (args->isVar()) {
    return 0;
  }
  const Term* l = args->term();
  args = args->next();
  if (args->isVar()) {
    return 0;
  }
  const Term* r = args->term();
  Def* def = defines(l,r);
  if (def) {
    return def;
  }
  def = defines(r,l);
  if (def) {
    return def;
  }

  return 0;
} // FunctionDefinition::isFunctionDefinition (const Atom&...)


/**
 * If lhs=rhs if a function definition f(x1,...,xn) = t.
 * return the Def structure representing information about the definition.
  *
  * @since 09/05/2002, Manchester
  * @since 24/10/2002 Manchester, bug fixed
  * @since 05/01/2004, Manchester, completely reimplemented
  * @since 29/05/2004, Manchester, changed to check that the
  *   variables of t is a subset of {x1,...,xn} (before it was
  *   a check for equality.
  * @since 26/05/2007, Manchester, reimplemented for new datastructures
  *   and check for equality added
  */
FunctionDefinition::Def*
FunctionDefinition::defines (const Term* lhs, const Term* rhs)
{
  CALL("FunctionDefinition::defines");

  unsigned f = lhs->functor();

  if (occurs(f,*rhs)) {
    return 0;
  }
  if (lhs->arity() == 0) {
    if (rhs->arity() != 0) { // c = f(...)
      return 0;
    }
    if (rhs->functor() == f) {
      return 0;
    }
    return new Def(lhs,rhs,true,true);
  }

  int vars = 0; // counter of variables occurring in the lhs

  // First, iterate subterms in lhs and check that all of them are variables
  // and each of them occurs exactly once. counter will contain variables
  // occurring in lhs
  MultiCounter counter;
  for (const TermList* ts = lhs->args(); ts->isNonEmpty(); ts=ts->next()) {
    if (! ts->isVar()) {
      return false;
    }
    int w = ts->var();
    if (counter.get(w) != 0) { // more than one occurrence
      return false;
    }
    counter.inc(w);
    vars++;
  }

  bool linear = true;
  // now check that rhs contains only variables in the counter
  // Iterate over variables in rhs and check that they
  // are counted as 1 or 2.
  // found will be increased by the number of different variables
  // marked 1.
  TermVarIterator vs(rhs->args());
  while (vs.hasNext()) {
    int v = vs.next();
    switch (counter.get(v)) {
    case 0: // v does not occur in lhs
      return false;

    case 1: // v occurs in lhs, it is first occurrence in rhs
      counter.inc(v);
      vars--;
      break;

    default: // v occurs in lhs, it is not its first occurrence in rhs
      linear = false;
      break;
    }
  }

  return new Def(lhs,rhs,linear,! vars);
} // FunctionDefinition::defines


/**
 * True if function symbol f occurs in the term.
 * @since 28/09/2002 Manchester, changed to use numeric terms
 * @since 06/01/2004 Manchester, changed to use iterator
 */
bool FunctionDefinition::occurs (unsigned f, const Term& t)
{
  CALL ("FunctionDefinition::occurs");

  TermFunIterator funs(&t);
  while (funs.hasNext()) {
    if (f == funs.next()) {
      return true;
    }
  }
  return false;
} // FunctionDefinition::occurs (const FunctionSymbol& f, const Term& t)


/**
 * If lhs=rhs if a function definition f(x1,...,xn) = t.
 * return the Def structure representing information about the definition.
 *
 * @since 26/07/2002 Bolzano, changed
 * @since 26/05/2007 Manchester, reimplemented using new datastructures
 */
FunctionDefinition::Def*
FunctionDefinition::isFunctionDefinition (const FormulaUnit& unit)
{
  CALL ("Definition::isFunctionDefinition(FormulaUnit&)" );

  const Formula* f = unit.formula();
  // skip all universal quantifiers in front of the formula
  while (f->connective() == FORALL) {
    f = f->qarg();
  }

  if (f->connective() != LITERAL) {
    return 0;
  }
  return isFunctionDefinition(f->literal());
} // FunctionDefinition::isFunctionDefinition


// /**
//  * Remove all function definitions from the problem.
//  * @since 29/05/2004 Manchester.
//  */
// int FunctionDefinition::removeAllDefinitions ()
// {
//   CALL("FunctionDefinition::removeAllDefinitions");

//   // iterate over the problem clauses and move all definitions from it
//   // to _definitions
//   UnitChain::DelIterator us(_problem.giveUnits());
//   while (us.hasNext()) {
//     Unit u (us.next());
//     Clause c(u.clause());
//     Term l;
//     Term r;
//     if (isFunctionDefinition(c,l,r)) {
//       int n = l.functor().number();
//       Def& def = _defs[n];
//       if (def.mark != REMOVED) {
// 	// there is already a definition of this function
// 	count(c);
// 	continue;
//       }
//       _removed++;
//       // initialise the Def
//       def.mark = UNTOUCHED;
//       def.unit = u;
//       def.fun = n;
//       def.lhs = l;
//       def.rhs = r;
//       us.del();
//     }
//     else { // not a definition, count occurrences
//       count(c);
//     }
//   }
//   if (_removed == 0) {
//     return 0;
//   }

//   // there are some definitions, they will be removed
//   // try to unfold all definitions
//   while (! unfoldAllDefs()) {
//   }

//   // all definitions are unfolded, substitute them to the problem clauses
//   UnitChain::DelIterator cs(_problem.giveUnits());
//   while (cs.hasNext()) {
//     Unit u(cs.next());
//     LiteralList ls(u.clause().literals());
//     UnitList parents;
//     apply(ls,parents);
//     if (ls != u.clause().literals()) { // application changed the clause
//       Clause newClause(ls);
//       parents.push(u);
//       Unit newUnit(Inference::DEFINITION_UNFOLDING,newClause,parents);
//       cs.replace(newUnit);
//     }
//   }

//   return _removed;
// } // FunctionDefinition::removeAllDefinitions


// /**
//  * Count all occurrences of function symbols in c.
//  * @since 29/05/2004 Manchester
//  */
// void FunctionDefinition::count (const Clause& c)
// {
//   CALL("FunctionDefinition::count");

//   VL::Iterator<Literal> lits(c.literals());
//   while (lits.hasNext()) {
//     TermFunIterator funs(lits.next());
//     while (funs.hasNext()) {
//       _counter.inc(funs.next().number());
//     }
//   }
// } // FunctionDefinition::count

// /**
//  * The main algorithm. It takes all definitions f(X) = t such that
//  * f(X) occurs in the problem and unfolds t by other definitions.
//  * If cyclic definitions are found, one of them is pushed back to
//  * the problem to break the cycle. If this happens, unfolding is
//  * started again since some f's that previously did not occur in
//  * the problem may occur there now.
//  *
//  * @since 29/05/2004 Manchester
//  */
// bool FunctionDefinition::unfoldAllDefs ()
// {
//   CALL("FunctionDefinition::unfoldAllDefs");

//   bool result = true;
//   for (int i = _counter.lastCounter(); i >= 0; i--) {
//     Def& def = _defs[i];
//     if(_counter.get(i) != 0) { // the definition occurs in the problem
//       result = unfold(def) && result;
//     }
//   }
//   return result;
// } // FunctionDefinition::unfoldAllDefs

// /**
//  * Unfold one definition.
//  *
//  * @since 29/05/2004 Manchester
//  */
// bool FunctionDefinition::unfold (Def& def)
// {
//   CALL("FunctionDefinition::unfold (Def&...)");

//   switch (def.mark) {
//   case UNTOUCHED:
//     {
//       // check if any function symbol in the rhs is blocked
//       TermFunIterator funs(def.rhs);
//       while (funs.hasNext()) {
// 	if (_defs[funs.next().number()].mark == BLOCKED) {
// 	  // circular definitions found, this definition must be removed
// 	  def.mark = REMOVED; // marked removed
// 	  // return the unit back to the problem
// 	  _problem.addUnit(def.unit);
// 	  // add function symbols of the unit to the counter
// 	  count(def.unit.clause());
// 	  return false;
// 	}
//       }

//       def.mark = BLOCKED;
//       Term newRHS(def.rhs);
//       UnitList parents; // to mark parents of the new clause
//       bool result = unfold(newRHS,parents);
//       if (def.rhs != newRHS) { // unfolding changed the definition
// 	// build a new unit, a result of the unfolding
// 	parents.push(def.unit);
// 	Atom newEquality(def.lhs,newRHS);
// 	Literal newLit(true,newEquality);
// 	LiteralList newList(newLit);
// 	Clause newClause(newList);
// 	Unit newUnit(Inference::DEFINITION_UNFOLDING,newClause,parents);
// 	def.unit = newUnit;
// 	def.rhs = newRHS;
//       }
//       def.mark = UNFOLDED;
//       return result;
//     }

//   case REMOVED:
//   case UNFOLDED:
//     return true;

// #if VDEBUG
//   default:
//     ASSERTION_VIOLATION;
// #endif
//   }
// } // FunctionDefinition::unfold


// /**
//  * Apply unfolding to the term t, unfolding if necessary other
//  * definitions.
//  *
//  * @since 29/05/2004 Manchester
//  */
// bool FunctionDefinition::unfold (Term& t,UnitList& parents)
// {
//   CALL("FunctionDefinition::unfold (Term&...)");

//   if (t.isVar()) {
//     return true;
//   }

//   TermList newArgs(t.args());
//   bool result = unfold(newArgs,parents);
//   Def& def = _defs[t.functor().number()];
//   // check if the function symbol of t is defined
//   result = unfold(def) && result;

//   switch (def.mark) {
//   case UNFOLDED: // fully unfolded
//     {
//       // now newArgs has a form (t1,...,tn)
//       // and def has the form f(x1,...,xn) = r[x1,...,xn]
//       // we have to set t to r[t1,...,tn]
//       // to this end we form a substitution {x1->t1,...,xn->tn}
//       // and apply it to r
//       Substitution s;
//       ASS(def.lhs.args().length() == newArgs.length());
//       VL::Iterator<Term> xs(def.lhs.args());
//       VL::Iterator<Term> ts(newArgs);
//       while(xs.hasNext()) {
// 	s.bind(xs.next().var(),ts.next());
//       }

//       Term r(def.rhs);
//       s.apply(r);
//       t = r;
//       if (! parents.member(def.unit)) {
// 	parents.push(def.unit);
//       }
//     }
//     return result;

//   case REMOVED:
//     if (newArgs != t.args()) { // unfolding changed arguments
//       t = Term(t.functor(),newArgs);
//     }
//     return result;

// #if VDEBUG
//   default:
//     ASSERTION_VIOLATION;
// #endif
//   }
// } // FunctionDefinition::unfold (Term& t,UnitList& parents)


// /**
//  * Apply unfolding to the term list ts, unfolding if necessary other
//  * definitions.
//  *
//  * @since 29/05/2004 Manchester
//  */
// bool FunctionDefinition::unfold (TermList& ts,UnitList& parents)
// {
//   CALL("FunctionDefinition::unfold (TermList&...)");

//   if (ts.isEmpty()) {
//     return true;
//   }
//   Term hd(ts.head());
//   bool r1 = unfold(hd,parents);
//   TermList tl(ts.tail());
//   bool r2 = unfold(tl,parents);
//   if (ts.head() != hd || ts.tail() != tl) {
//     ts = TermList(hd,tl);
//   }
//   return r1 && r2;
// } // FunctionDefinition::unfold (TermList& t,UnitList& parents)


// /**
//  * Apply unfolded definitions to the term t.
//  *
//  * @since 29/05/2004 Manchester
//  */
// void FunctionDefinition::apply (Term& t,UnitList& parents)
// {
//   CALL("FunctionDefinition::apply (Term&...)");

//   if (t.isVar()) {
//     return;
//   }

//   TermList newArgs(t.args());
//   apply(newArgs,parents);
//   Def& def = _defs[t.functor().number()];

//   switch (def.mark) {
//   case UNFOLDED: // fully unfolded
//     {
//       // now newArgs has a form (t1,...,tn)
//       // and def has the form f(x1,...,xn) = r[x1,...,xn]
//       // we have to set t to r[t1,...,tn]
//       // to this end we form a substitution {x1->t1,...,xn->tn}
//       // and apply it to r
//       Substitution s;
//       ASS(def.lhs.args().length() == newArgs.length());
//       VL::Iterator<Term> xs(def.lhs.args());
//       VL::Iterator<Term> ts(newArgs);
//       while(xs.hasNext()) {
// 	s.bind(xs.next().var(),ts.next());
//       }

//       Term r(def.rhs);
//       s.apply(r);
//       t = r;
//       if (! parents.member(def.unit)) {
// 	parents.push(def.unit);
//       }
//     }
//     return;

//   case REMOVED:
//     if (newArgs != t.args()) { // unfolding changed arguments
//       t = Term(t.functor(),newArgs);
//     }
//     return;

// #if VDEBUG
//   default:
//     ASSERTION_VIOLATION;
// #endif
//   }
// } // FunctionDefinition::apply (Term& t,UnitList& parents)


// /**
//  * Apply unfolded definitions to the term list ts.
//  *
//  * @since 29/05/2004 Manchester
//  */
// void FunctionDefinition::apply (TermList& ts,UnitList& parents)
// {
//   CALL("FunctionDefinition::apply (TermList&...)");

//   if (ts.isEmpty()) {
//     return;
//   }
//   Term hd(ts.head());
//   apply(hd,parents);
//   TermList tl(ts.tail());
//   apply(tl,parents);
//   if (ts.head() != hd || ts.tail() != tl) {
//     ts = TermList(hd,tl);
//   }
// } // FunctionDefinition::apply (TermList& t,UnitList& parents)


// /**
//  * Apply unfolded definitions to the literal list ts.
//  *
//  * @since 29/05/2004 Manchester
//  */
// void FunctionDefinition::apply (LiteralList& ts,UnitList& parents)
// {
//   CALL("FunctionDefinition::apply (LiteralList&...)");

//   if (ts.isEmpty()) {
//     return;
//   }
//   Literal hd(ts.head());
//   apply(hd,parents);
//   LiteralList tl(ts.tail());
//   apply(tl,parents);
//   if (ts.head() != hd || ts.tail() != tl) {
//     ts = LiteralList(hd,tl);
//   }
// } // FunctionDefinition::apply (LiteralList& t,UnitList& parents)


// /**
//  * Apply unfolded definitions to the literal l.
//  *
//  * @since 29/05/2004 Manchester
//  */
// void FunctionDefinition::apply (Literal& l,UnitList& parents)
// {
//   CALL("FunctionDefinition::apply (LiteralList&...)");

//   Atom a(l.atom());
//   TermList ts(a.args());
//   apply(ts,parents);
//   if (ts != a.args()) {
//     l = Literal(l.sign(),Atom(a.functor(),ts));
//   }
// } // FunctionDefinition::apply (LiteralList& t,UnitList& parents)

/**
 * Delete the definition def.
 * @since 27/05/2007 flight Frankfurt-Lisbon
 */
void FunctionDefinition::deleteDef (Def* def)
{
  delete def;
} // FunctionDefinition::deleteDef


}
