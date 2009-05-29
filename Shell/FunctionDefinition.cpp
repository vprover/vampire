/**
 * @file FunctionDefinition.cpp
 * Implements class FunctionDefinition implementing work with definitions.
 *
 * @since 28/05/2004 Manchester
 */

#include "../Debug/Tracer.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/BitUtils.hpp"

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
    LOOP,
    BLOCKED,
    UNFOLDED,
    REMOVED
  };
  /** Unit containing a definition */
  Clause* defCl;
  /** The defined function symbol number */
  int fun;
  /** The lhs of the definition */
  Term* lhs;
  /** The rhs of the definition */
  Term* rhs;

  Mark mark;
  /** is the definition linear? */
  bool linear;
  /** strict means that all lhs variables occur in rhs */
  bool strict;
  /** first defined function that is used in @b rhs, or -1 if there isn't such */
  int containedFn;

  int examinedArg;

  IntList* dependentFns;
  bool* argOccurs;

  Def(Term* l, Term* r, bool lin, bool str)
    : fun(l->functor()),
      lhs(l),
      rhs(r),
      mark(UNTOUCHED),
      linear(lin),
      strict(str),
      containedFn(-1),
      dependentFns(0)
  {
    argOccurs=reinterpret_cast<bool*>(ALLOC_KNOWN(lhs->arity()*sizeof(bool),
	    "FunctionDefinition::Def::argOccurs"));
    BitUtils::zeroMemory(argOccurs, lhs->arity()*sizeof(bool));
  }

  ~Def()
  {
    DEALLOC_KNOWN(argOccurs, lhs->arity()*sizeof(bool), "FunctionDefinition::Def::argOccurs");
  }

  CLASS_NAME("FunctionDefintion::Def");
  USE_ALLOCATOR(Def);
}; // class FunctionDefintion::Def


/**
 * Initialise a function definition.
 * Move all definitions from the problem to _definitions and _map.
 * @since 29/05/2004 Manchester
 */
FunctionDefinition::FunctionDefinition ()
  :
//    _defStore(32),
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

  Stack<TermList> args;
  Stack<int> indep(16);
  Fn2DefMap::Iterator dit(_defs);
  while(dit.hasNext()) {
    Def* d=dit.next();

    if(d->mark==Def::SAFE) {
      continue;
    }

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

void FunctionDefinition::unfoldDefinitions(Def* def0)
{
  CALL("FunctionDefinition::unfoldDefinition");

  TermList t=TermList(def0->lhs);
  static Stack<TermList*> stack(4);
  static Stack<Def*> defStack(4);
  for(;;) {
    Definition* d;
    if(t.isEmpty()) {
      d=defStack.pop();
      if(d) {
	//leave the definition
	d->rhs=applyDefinitions(d->rhs);
	d->mark=Def::UNFOLDED;
      }
    } else if(t.isTerm()) {
      if(!_defs.find(t.term()->functor(), d)) {
	d=0;
      }
      if(ts->term()->arity()) {
	stack.push(ts->term()->args());
	defStack.push(0);
      }
      if(d) {
	if(d->mark==Def::UNFOLDED) {
	} else if(d->mark==Def::LOOP) {
	  //unroll stacks until the point when the current
	  //definition was entered
	  do{
	    while(!stack.pop().isEmpty()) {}
	    d=defStack.pop();
	  } while(d==0);
	  d->mark=Def::BLOCKED;
	} else {
	  ASS_EQ(d->mark, Def::UNTOUCHED);

	  //enter the definition
	  d->mark=Def::LOOP;
	  stack.push(d->rhs);
	  defStack.push(d);
	}
      }
    }
    if(stack.isEmpty()) {
      break;
    }
    TermList* ts=stack.pop();
    if(!ts->isEmpty()) {
      stack.push(ts->next());
    }
    t=*ts;
  }
  ASS(defStack.isEmpty());
}


bool FunctionDefinition::isDefined(Term* t)
{
  ASS(!t->isLiteral());
  Def* d;
  if(!_defs.find(t->functor()), d) {
    return false;
  }
  return d->mark!=Def::BLOCKED;
}

Term* FunctionDefinition::applyDefinition(Term* t)
{
  CALL("FunctionDefinition::applyDefinition/1");

  typedef DHMap<unsigned, TermList> BindingMap;
  static BindingMap bindings;
  bindings.reset();

  Def* d=_defs.get(t->functor());
  ASS_EQ(d->mark, Def::SAFE);

  TermList* dargs=d->lhs->args();
  TermList* targs=t->args();
  while(dargs->isNonEmpty()) {
    ASS(targs->isNonEmpty());
    ALWAYS(bindings.insert(dargs->var(), *targs));
    dargs=dargs->next();
    targs=targs->next();
  }

  SubstHelper::MapApplicator<BindingMap> applicator(&bindings);
  return SubstHelper::apply(d->rhs, applicator, false);
}

TermList FunctionDefinition::applyDefinition(unsigned fn, TermList* argArr)
{
  CALL("FunctionDefinition::applyDefinition/2");

  typedef DHMap<unsigned, TermList> BindingMap;
  static BindingMap bindings;
  bindings.reset();

  Def* d=_defs.get(fn);
  ASS_EQ(d->mark, Def::SAFE);

  TermList* dargs=d->lhs->args();
  int i=0;
  while(dargs->isNonEmpty()) {
    ALWAYS(bindings.insert(dargs->var(), argArr[i++]));
    dargs=dargs->next();
  }

  SubstHelper::MapApplicator<BindingMap> applicator(&bindings);
  return TermList(SubstHelper::apply(d->rhs, applicator, false));
}

void FunctionDefinition::finishTask()
{
  UnfoldingTaskRecord task=tasks.pop();
  switch(task.type) {
  case UnfoldingTaskRecord::EVAL_BINDING_ARGUMENT:
    BindingSpec spec=task.bSpec;
    defIndexes.pop();
    bindings.set(spec, args.top());
    unfolded.insert(spec, true);
    break;
  case UnfoldingTaskRecord::UNFOLD_DEFINITION:
    TermList unfolded=args.pop();
    ASS(unfolded.isTerm());
    task.def->rhs=unfolded.term();
    task.def->mark=Def::SAFE;
    break;
  }
}

TermList FunctionDefinition::evalVariableContent(unsigned var)
{
  if(defIndexes.top()) {
    modified.setTop(true);
    BindingSpec spec=make_pair(defIndexes.top(), var);
    TermList bound=bindings.get(spec);
    if(bound.isVar() || unfolded.find(spec)) {
      args.push(bound);
    } else {
      UnfoldingTaskRecord task(spec);
      defIndexes.push(0);
      tasks.push(task);
      toDo.push(0);
      terms.push(bound.term());
      modified.push(false);
      toDo.push(bound.term()->args());
    }
  } else {
    args.push(TermList(var, false));
  }
}

void FunctionDefinition::replaceByDefinition(Term* t)
{
  unsigned defIndex=nextDefIndex++;

  Def* d=_defs.get(t->functor());
  ASS_EQ(d->mark, Def::SAFE);

  TermList* dargs=d->lhs->args();
  TermList* targs=t->args();
  while(dargs->isNonEmpty()) {
    ASS(targs->isNonEmpty());
    ALWAYS(bindings.insert(make_pair(defIndex, dargs->var()), *targs));
    dargs=dargs->next();
    targs=targs->next();
  }

  defIndexes.push(defIndex);
  terms.push(d->rhs);
  modified.push(false);
  toDo.push(d->rhs->args());

}



Term* FunctionDefinition::applyDefinitions(Term* trm)
{
  CALL("FunctionDefinition::applyDefinitions");

  if(!trm->isLiteral() && isDefined(trm)) {
    return applyDefinition(trm);
  }

  bindings.reset();
  unfolded.reset();

  defIndexes.reset();
  unfoldedDefs.reset();
  toDo.reset();
  terms.reset();
  modified.reset();
  args.reset();

  defIndexes.push(0);
  modified.push(false);
  toDo.push(trm->args());

  for(;;) {
    TermList* tt=toDo.pop();
    if(!tt) {
      finishTask();
    }
    if(tt->isEmpty()) {
      if(terms.isEmpty()) {
	//we're done, args stack contains modified arguments
	//of the argument term.
	ASS(toDo.isEmpty());
	break;
      }
      Term* orig=terms.pop();
      if(!modified.pop()) {
	args.truncate(args.length() - orig->arity());
	args.push(TermList(orig));
	continue;
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);

      Term* newTrm=Term::create(orig,argLst);
      args.truncate(args.length() - orig->arity());
      args.push(TermList(newTrm));

      modified.setTop(true);
      continue;
    }
    toDo.push(tt->next());

    TermList tl=*tt;
    if(tl.isVar()) {
      ASS(tl.isOrdinaryVar());
      evalVariableContent(tl.var());
      continue;
    }

    ASS(tl.isTerm());
    Term* t=tl.term();
    if(isDefined(t)) {
      replaceByDefinition(t);
    } else {
      terms.push(t);
      modified.push(false);
      toDo.push(t->args());
    }
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),trm->arity());

  if(!modified.pop()) {
    return trm;
  }

  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (trm->arity()-1);
  if(trm->isLiteral()) {
    return Literal::create(static_cast<Literal*>(trm),argLst);
  } else {
    return Term::create(trm,argLst);
  }
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

  Fn2DefMap::Iterator dit(_defs);
  while(dit.hasNext()) {
    delete dit.next();
  }
} // FunctionDefinition::~FunctionDefinition

///**
// * If the the unit if a function definition f(x1,...,xn) = t,
// * return the Def structure representing information about the definition.
// * @since 26/05/2007 Manchester
// */
FunctionDefinition::Def*
FunctionDefinition::isFunctionDefinition (Unit& unit)
{
  CALL("FunctionDefinition::isFunctionDefinition(const Unit&)");
  if (unit.isClause()) {
    return isFunctionDefinition(static_cast<Clause*>(&unit));
  }
  return isFunctionDefinition(static_cast<FormulaUnit&>(unit));
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
FunctionDefinition::isFunctionDefinition (Literal* lit)
{
  CALL("FunctionDefinition::isFunctionDefinition(const Literal*)");

  if (! lit->isPositive() ||
      ! lit->isEquality()) {
    return 0;
  }

  // the atom is an equality
  TermList* args = lit->args();
  if (args->isVar()) {
    return 0;
  }
  Term* l = args->term();
  args = args->next();
  if (args->isVar()) {
    return 0;
  }
  Term* r = args->term();
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
FunctionDefinition::defines (Term* lhs, Term* rhs)
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
  static DHMap<unsigned, unsigned, IdentityHash> var2argIndex;
  var2argIndex.reset();
  for (const TermList* ts = lhs->args(); ts->isNonEmpty(); ts=ts->next()) {
    if (! ts->isVar()) {
      return 0;
    }
    int w = ts->var();
    if (counter.get(w) != 0) { // more than one occurrence
      return 0;
    }
    counter.inc(w);
    var2argIndex.insert(w, vars);
    vars++;
  }

  bool linear = true;
  Def* res=new Def(lhs,rhs,true,false);
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
      delete res;
      return 0;

    case 1: // v occurs in lhs, it is first occurrence in rhs
      counter.inc(v);
      vars--;
      res->argOccurs[var2argIndex.get(v)]=true;
      break;

    default: // v occurs in lhs, it is not its first occurrence in rhs
      res->linear=false;
      linear = false;
      break;
    }
  }
  res->strict=!vars;

  return res;
} // FunctionDefinition::defines


/**
 * True if function symbol f occurs in the term.
 * @since 28/09/2002 Manchester, changed to use numeric terms
 * @since 06/01/2004 Manchester, changed to use iterator
 */
bool FunctionDefinition::occurs (unsigned f, Term& t)
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
FunctionDefinition::isFunctionDefinition (FormulaUnit& unit)
{
  CALL ("Definition::isFunctionDefinition(FormulaUnit&)" );

  Formula* f = unit.formula();
  // skip all universal quantifiers in front of the formula
  while (f->connective() == FORALL) {
    f = f->qarg();
  }

  if (f->connective() != LITERAL) {
    return 0;
  }
  return isFunctionDefinition(f->literal());
} // FunctionDefinition::isFunctionDefinition

/**
 * Delete the definition def.
 * @since 27/05/2007 flight Frankfurt-Lisbon
 */
void FunctionDefinition::deleteDef (Def* def)
{
  delete def;
} // FunctionDefinition::deleteDef


}
