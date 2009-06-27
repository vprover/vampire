/**
 * @file PredicateDefinition.cpp
 * Implements class PredicateDefinition.
 */

#include "../Lib/Allocator.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Set.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Formula.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/FormulaVarIterator.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/SubformulaIterator.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Unit.hpp"

#include "Statistics.hpp"

#include "PredicateDefinition.hpp"

#define REPORT_PRED_DEF_SIMPL 0

namespace Shell
{

using namespace Lib;
using namespace Kernel;

struct PredicateDefinition::PredData
{
  Set<Unit*> containingUnits;

  int pred;

  int pocc;
  int nocc;
  int docc;

  bool enqueuedForDefEl;
  bool enqueuedForReplacement;

  FormulaUnit* defUnit;
  FormulaUnit* newDefUnit;

  PredData()
  : pocc(0), nocc(0), docc(0), enqueuedForDefEl(false),
  enqueuedForReplacement(false), defUnit(0), newDefUnit(0) {}

  void setDefUnit(FormulaUnit* u)
  {
    defUnit=u;
    newDefUnit=u;
  }

  void add(int polarity, int add, PredicateDefinition* pdObj)
  {
    CALL("PredicateDefinition::PredData::add");

    switch (polarity) {
    case -1:
      nocc += add;
      break;
    case 0:
      docc += add;
      break;
    case 1:
      pocc += add;
      break;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return;
#endif
    }
    if(add==-1) {
      check(pdObj);
    }
  }

  void check(PredicateDefinition* pdObj)
  {
    CALL("PredicateDefinition::PredData::check");
    if(!enqueuedForDefEl && isEliminable()) {
      ASS(!enqueuedForReplacement);
      pdObj->_eliminable.push(pred);
      enqueuedForDefEl=true;
#if REPORT_PRED_DEF_SIMPL
      cout<<"DE: "<<env.signature->predicateName(pred)<<endl;
#endif
    } else if(!enqueuedForReplacement && isPure()) {
      pdObj->_pureToReplace.push(pred);
      enqueuedForReplacement=true;
#if REPORT_PRED_DEF_SIMPL
      cout<<"PP: "<<env.signature->predicateName(pred)<<((nocc==0)?" +":" -")<<endl;
#endif
    }
  }

  bool isEliminable()
  {
    ASS_EQ(defUnit,newDefUnit);
    return defUnit && docc==1 && ( pocc==0 || nocc==0 );
  }
  bool isPure()
  {
    return docc==0 && ( (pocc==0) ^ (nocc==0) );
  }

  CLASS_NAME("PredicateDefintion::PredData");
  USE_ALLOCATOR(PredData);
};

PredicateDefinition::PredicateDefinition()
: _predCnt(env.signature->predicates())
{
  int predCnt=env.signature->predicates();
  _preds = new PredData[predCnt];
  for(int i=0;i<predCnt;i++) {
    _preds[i].pred=i;
  }
}

PredicateDefinition::~PredicateDefinition()
{
  delete[] _preds;
}

/**
 *
 * @pre Formulas must be rectified and flattened.
 */
void PredicateDefinition::removeUnusedDefinitionsAndPurePredicates(UnitList*& units)
{
  CALL("PredicateDefinition::removeUnusedDefinitionsAndPurePredicates");

  UnitList::Iterator scanIterator(units);
  while(scanIterator.hasNext()) {
    scan(scanIterator.next());
  }

  for(int pred=1; pred<_predCnt; pred++) {
    _preds[pred].check(this);
  }

  while(_eliminable.isNonEmpty() || _pureToReplace.isNonEmpty()) {
    while(_eliminable.isNonEmpty()) {
      int pred=_eliminable.pop();
      PredData& pd=_preds[pred];
      if(pd.pocc==0 && pd.nocc==0) {
	//pred does not occur anywhere else, hence can be deleted
	pd.newDefUnit=0;
      } else if(pd.pocc==0) {
	//elsewhere it occurs only negatively, so we can make
	//an equivalence into an implication
	makeImplFromDef(pred, false);
      } else {
	ASS_EQ(pd.nocc,0);
	//elsewhere it occurs only positively, so we can make
	//an equivalence into an implication
	makeImplFromDef(pred, true);
      }
      if(pd.newDefUnit) {
	count(pd.newDefUnit, 1);
      }
      count(pd.defUnit, -1);
      ALWAYS(_unitReplacements.insert(pd.defUnit, pd.newDefUnit));

      env.statistics->unusedPredicateDefinitions++;
#if REPORT_PRED_DEF_SIMPL
      cout<<"DE from: "<<pd.defUnit->toString()<<endl;
      cout<<"DE to: "<<(pd.newDefUnit?pd.newDefUnit->toString():"<deleted>")<<endl;
#endif
    }
    while(_pureToReplace.isNonEmpty()) {
      int pred=_pureToReplace.pop();
      PredData& pd=_preds[pred];
      ASS(pd.pocc==0 || pd.nocc==0);

      _purePreds.insert(pred, pd.nocc==0);
      Set<Unit*>::Iterator uit(pd.containingUnits);
      while(uit.hasNext()) {
	Unit* u=uit.next();
	if(_unitReplacements.find(u)) {
	  //The unit has already been replaced.
	  continue;
	}
	Unit* v=replacePurePredicates(u);

	ASS_NEQ(u,v);
#if REPORT_PRED_DEF_SIMPL
	cout<<"PP from: "<<u->toString()<<endl;
	cout<<"PP to: "<<v->toString()<<endl;
#endif
	if(u->isClause()) {
	  if(v!=0) {
	    ASS(v->isClause())
	    count(static_cast<Clause*>(v), 1);
	  }
	  count(static_cast<Clause*>(u), -1);
	} else {
	  count(static_cast<FormulaUnit*>(v), 1);
	  count(static_cast<FormulaUnit*>(u), -1);
	}
	ALWAYS(_unitReplacements.insert(u,v));
      }

      env.statistics->purePredicates++;
    }
  }

  UnitList::DelIterator replaceIterator(units);
  while(replaceIterator.hasNext()) {
    Unit* u=replaceIterator.next();
    Unit* v;
    if(!_unitReplacements.find(u,v)) {
      continue;
    }
    Unit* tgt=v;
    while(_unitReplacements.find(v,tgt)) {
      v=tgt;
    }
    if(!v || ( !v->isClause() && static_cast<FormulaUnit*>(v)->formula()->connective()==TRUE ) ) {
      replaceIterator.del();
    } else {
      replaceIterator.replace(v);
    }
  }

}

FormulaUnit* PredicateDefinition::replacePurePredicates(FormulaUnit* u)
{
  Formula* resf=replacePurePredicates(u->formula());
  if(resf!=u->formula()) {
    return new FormulaUnit(resf, new Inference1(Inference::PURE_PREDICATE_REMOVAL, u),
	    u->inputType());
  } else {
    return u;
  }
}

Clause* PredicateDefinition::replacePurePredicates(Clause* cl)
{
  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    bool val;
    if(_purePreds.find((*cl)[i]->functor(), val)) {
      ASS_EQ((*cl)[i]->isPositive(), val);
      return 0;
    }
  }
  return cl;
}

Unit* PredicateDefinition::replacePurePredicates(Unit* u)
{
  if(u->isClause()) {
    return replacePurePredicates(static_cast<Clause*>(u));
  } else {
    return replacePurePredicates(static_cast<FormulaUnit*>(u));
  }
}

Formula* PredicateDefinition::replacePurePredicates(Formula* f)
{
  CALL("SimplifyFalseTrue::replacePurePredicates");

  Connective con = f->connective();
  switch (con) {
  case LITERAL:
  {
    bool value;
    if(!_purePreds.find(f->literal()->functor(), value)) {
      return f;
    }
    return new Formula(value^f->literal()->isNegative());
  }
  case TRUE:
  case FALSE:
    return f;

  case AND:
  case OR:
  {
    bool changed = false;
    Stack<Formula*> gs(8);
    Stack<FormulaList*> mergees(8);
    gs.reset();
    mergees.reset();
    FormulaList::Iterator it(f->args());
    while (it.hasNext()) {
      Formula* h = it.next();
      Formula* g = replacePurePredicates(h);
      if(g->connective()==con) {
	//we want to keep the formula flattened
	mergees.push(g->args());
	changed = true;
	//BTW, we might want to delete g, as only its subformulas are going to be used
	continue;
      }
      switch (g->connective()) {
      case TRUE:
	if (con == OR) {
	  return g;
	}
	ASS_EQ(con, AND);
	changed = true;
	break;
      case FALSE:
	if (con == AND) {
	  return g;
	}
	ASS_EQ(con, OR);
	changed = true;
	break;

      default:
	gs.push(g);
	if (h != g) {
	  changed = true;
	}
	break;
      }
    }

    while(mergees.isNonEmpty()) {
      FormulaList::Iterator it(mergees.pop());
      while (it.hasNext()) {
        Formula* g = it.next();
        //g is already simplified
        ASS_NEQ(g->connective(), con);
        ASS_NEQ(g->connective(), TRUE);
        ASS_NEQ(g->connective(), FALSE);
  	gs.push(g);
      }
    }

    if (! changed) {
      return f;
    }
    switch (gs.size()) {
    case 0:
      return new Formula(con == OR ? false : true);
    case 1:
      return gs.top();
    default:
      FormulaList* res = 0;
      while(gs.isNonEmpty()) {
	FormulaList::push(gs.pop(),res);
      }
      return new JunctionFormula(con,res);
    }
  }

  case IMP:
  {
    Formula* right = replacePurePredicates(f->right());
    if (right->connective() == TRUE) {
      return right;
    }
    Formula* left = replacePurePredicates(f->left());

    switch (left->connective()) {
    case TRUE: // T -> R
      return right;
    case FALSE: // F -> R
      return new Formula(true);
    default: // L -> R;
      break;
    }

    if (right->connective() == FALSE) {
      return new NegatedFormula(left);
    }
    if (left == f->left() && right == f->right()) {
      return f;
    }
    return new BinaryFormula(con,left,right);
  }

  case IFF:
  case XOR:
    {
      Formula* left = replacePurePredicates(f->left());
      Formula* right = replacePurePredicates(f->right());

      Connective lc = left->connective();
      Connective rc = right->connective();

      switch (lc) {
      case FALSE: // F * _
	switch (rc) {
	case FALSE: // F * F
	  return con == XOR
	         ? right
	         : new Formula(true);
	case TRUE: // F * T
	  return con == XOR
	         ? right
     	         : left;
	default: // F * R
	  return con == XOR
	         ? right
 	         : new NegatedFormula(right);
	}
      case TRUE: // T * _
	switch (rc) {
	case FALSE: // T * F
	  return con == XOR
	         ? left
	         : right;
	case TRUE: // T * T
	  return con == XOR
 	         ? new Formula(false)
     	         : left;
	default: // T * R
	  return con == XOR
 	         ? new NegatedFormula(right)
     	         : right;
	}
      default: // L * _
	switch (rc) {
	case FALSE: // L * F
	  return con == XOR
	         ? left
 	         : new NegatedFormula(left);
	case TRUE:  // L * T
	  return con == XOR
 	         ? new NegatedFormula(left)
     	         : left;
	default:    // L * R
	  if (left == f->left() && right == f->right()) {
	    return f;
	  }
	  return new BinaryFormula(con,left,right);
	}
      }
    }

  case NOT:
  {
    Formula* arg = replacePurePredicates(f->uarg());
    switch (arg->connective()) {
    case FALSE:
      return new Formula(true);
    case TRUE:
      return new Formula(false);
    default:
      return arg == f->uarg() ? f : new NegatedFormula(arg);
    }
  }

  case FORALL:
  case EXISTS:
  {
    Formula* arg = replacePurePredicates(f->qarg());
    if(arg->connective()==con) {
      //Here we connect var-list from f and from arg. All three list
      //remain valid, but those from arg and result might share some
      //elements, which would lead to trouble e.g. if we were deleting
      //them both.
      Formula::VarList* vl=arg->vars();
      Formula::VarList::Iterator vit(f->vars());
      while(vit.hasNext()) {
	Formula::VarList::push(vit.next(), vl);
      }
      return new QuantifiedFormula(con,vl,arg->qarg());
    }
    switch (arg->connective()) {
    case FALSE:
    case TRUE:
      return arg;
    default:
      return arg == f->qarg()
	      ? f
	      : new QuantifiedFormula(con,f->vars(),arg);
    }
  }
  }
  ASSERTION_VIOLATION;
}


void PredicateDefinition::makeImplFromDef(int pred, bool forward)
{
  PredData& pd=_preds[pred];
  Formula* f0=pd.defUnit->formula();
  Formula* f;

  bool isQuantified=f0->connective()==FORALL;
  if(isQuantified) {
    f=f0->qarg();
  } else {
    f=f0;
  }
  Formula* lhs;
  Formula* rhs;
  ASS_EQ(f->connective(), IFF);
  if(f->left()->connective()==LITERAL && f->left()->literal()->functor()==pred) {
    lhs=f->left();
    rhs=f->right();
  } else {
    ASS_EQ(f->right()->connective(), LITERAL);
    ASS_EQ(f->right()->literal()->functor(), pred);
    lhs=f->right();
    rhs=f->left();
  }
  bool swapArgs=lhs->literal()->isPositive()^forward;

  Formula* resf;
  if(swapArgs) {
    resf=new BinaryFormula(IMP, rhs, lhs);
  } else {
    resf=new BinaryFormula(IMP, lhs, rhs);
  }

  Formula* resf0;
  if(isQuantified) {
    resf0=new QuantifiedFormula(FORALL, f0->vars(), resf);
  } else {
    resf0=resf;
  }
  pd.newDefUnit=new FormulaUnit(resf0,
	  new Inference1(Inference::UNUSED_PREDICATE_DEFINITION_REMOVAL, pd.defUnit),
	  pd.defUnit->inputType());
}

void PredicateDefinition::scan(Unit* u)
{
  if(u->isClause()) {
    scan(static_cast<Clause*>(u));
  } else {
    scan(static_cast<FormulaUnit*>(u));
  }
}

void PredicateDefinition::scan(Clause* cl)
{
  count(cl, 1);
}

void PredicateDefinition::scan(FormulaUnit* unit)
{
  CALL("PredicateDefinition::scan(FormulaUnit)");

  count(unit, 1);

  Formula* f=unit->formula();

  // skip universal quantifier in front of the formula
  if(f->connective() == FORALL) {
    f = f->qarg();
  }
  ASS_NEQ(f->connective(), FORALL); //formula is flattened

  if(f->connective() == IFF) {
    if(f->left()->connective()==LITERAL) {
      if(tryGetDef(f->left()->literal(), f->right(), unit)) {
	return;
      }
    }
    if(f->right()->connective()==LITERAL) {
      tryGetDef(f->right()->literal(), f->left(), unit);
    }
  }
}


void PredicateDefinition::count (Clause* cl,int add)
{
  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    Literal* l=(*cl)[i];
    int pred = l->functor();
    _preds[pred].add(l->isPositive() ? 1 : -1, add, this);
    if(add==1) {
	_preds[pred].containingUnits.insert(cl);
    }
  }
}

void PredicateDefinition::count (Formula* f,int polarity,int add, Unit* unit)
{
  CALL("PredicateDefinition::count(Formula*,...)");

  switch (f->connective()) {
    case LITERAL:
    {
      Literal* l=f->literal();
      if(l->isEquality()) {
	return;
      }
      int pred = l->functor();
      _preds[pred].add(l->isPositive() ? polarity : -polarity, add, this);
      if(add==1) {
	_preds[pred].containingUnits.insert(unit);
      }
      return;
    }

    case AND:
    case OR: {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
        count (fs.next(),polarity,add,unit);
      }
      return;
    }

    case IMP:
      count (f->left(), -polarity, add, unit);
      count (f->right(), polarity, add, unit);
      return;

    case NOT:
      count (f->uarg(), -polarity, add, unit);
      return;

    case IFF:
    case XOR:
      count (f->left(), 0, add, unit);
      count (f->right(), 0, add, unit);
      return;

    case FORALL:
    case EXISTS:
      count (f->qarg(), polarity, add, unit);
      return;

    case TRUE:
    case FALSE:
      return;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return;
#endif
  }
} // PredicateDefinition::count (Formula* f,...)

bool PredicateDefinition::tryGetDef(Literal* lhs, Formula* rhs, FormulaUnit* unit)
{
  CALL("PredicateDefinition::tryGetDef");

  if(lhs->isEquality()) {
    return false;
  }
  if(_defs.find(lhs->functor())) {
    //there already is one predicate definition
    return false;
  }

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
  }

  SubformulaIterator sfit(rhs);

  while(sfit.hasNext()) {
    Formula* sf=sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    Literal* lit=sf->literal();
    if(lit->functor()==lhs->functor()) {
      return false;
    }
    Term::VariableIterator vit(lit);
    while(vit.hasNext()) {
      unsigned v=vit.next().var();
      if(!counter.get(v)) {
	return false;
      }
    }
  }

  _preds[lhs->functor()].setDefUnit(unit);
  return true;
}

}
