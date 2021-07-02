/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file PredicateDefinition.cpp
 * Implements class PredicateDefinition.
 */

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Set.hpp"
#include "Lib/Int.hpp"
#include "Lib/MultiCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/FormulaVarIterator.hpp"

#include "Shell/Options.hpp"

#include "Statistics.hpp"

#include "PredicateDefinition.hpp"

#define REPORT_PRED_DEF_SIMPL 0

namespace Shell
{

using namespace Lib;
using namespace Kernel;

/**
 * Contains details about predicate presence in the problem and state
 * of definition elimination or predicate removal.
 */
struct PredicateDefinition::PredData
{
  /** Units that contain the predicate. */
  Set<Unit*> containingUnits;

  bool builtIn;
  int pred;

  int pocc;
  int nocc;
  int docc;

  bool enqueuedForDefEl;
  bool enqueuedForReplacement;

  FormulaUnit* defUnit;

  PredData()
  : builtIn(false), pocc(0), nocc(0), docc(0), enqueuedForDefEl(false),
  enqueuedForReplacement(false), defUnit(0) {}

  void setDefUnit(FormulaUnit* u)
  {
    defUnit=u;
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

    //we don't remove anything that concerns interpreted predicates
    if(builtIn) {
      return;
    }
    
    if(!enqueuedForDefEl && isEliminable()) {
      ASS(!enqueuedForReplacement);
      pdObj->_eliminable.push(pred);
      enqueuedForDefEl=true;
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] pred marked for removing unused predicate definition: " 
                << env.signature->predicateName(pred) << std::endl;
        env.endOutput();
      }            
    } else if(!enqueuedForReplacement && isPure()) {
      pdObj->_pureToReplace.push(pred);
      enqueuedForReplacement=true;
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] " << stateToString() << " to be replaced by " 
                << ((nocc==0) ? "$false" : "$true") << std::endl;
        env.endOutput();
      }
    }
  }

  bool isEliminable()
  {
    return defUnit && docc==1 && ( pocc==0 || nocc==0 );
  }
  bool isPure()
  {
    return docc==0 && ( (pocc==0) ^ (nocc==0) );
  }

  vstring stateToString() const {
    return env.signature->predicateName(pred) + ": +(" + Int::toString(pocc)
	+ ") -(" + Int::toString(nocc) + ") 0(" + Int::toString(docc) + ")";
  }

  CLASS_NAME(PredicateDefinition::PredData);  
  USE_ALLOCATOR_ARRAY;
};

PredicateDefinition::PredicateDefinition()
: _processedPrb(0), _predCnt(env.signature->predicates())
{
  int predCnt=env.signature->predicates();

  _preds = new PredData[predCnt];
  for(int i=0;i<predCnt;i++) {
    _preds[i].pred=i;
  }

  //mark built-in
  for(int i=0;i<predCnt;i++) {
    if(env.signature->getPredicate(i)->protectedSymbol()) {
      addBuiltInPredicate(i);
    }
  }
}

PredicateDefinition::~PredicateDefinition()
{
  delete[] _preds;
}

/**
 * Mark predicate @c pred not to be eliminated by the rule.
 */
void PredicateDefinition::addBuiltInPredicate(unsigned pred)
{
  CALL("PredicateDefinition::addBuiltInPredicate");  
  ASS_L(pred,_predCnt);

  _preds[pred].builtIn = true;

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] pred marked as built-in: " 
            << env.signature->predicateName(pred) << std::endl;
    env.endOutput();
  }  
}

Unit* PredicateDefinition::getReplacement(Unit* u, ReplMap& replacements)
{
  CALL("PredicateDefinition::getReplacement(Unit*,ReplMap&)");

  Unit* tgt;
  while(replacements.find(u,tgt)) {
    u=tgt;
  }
  return u;
}

FormulaUnit* PredicateDefinition::getReplacement(FormulaUnit* u, ReplMap& replacements)
{
  CALL("PredicateDefinition::getReplacement(FormulaUnit*,ReplMap&)");

  Unit* res0 = getReplacement(static_cast<Unit*>(u), replacements);
  ASS(!res0 || !res0->isClause()); //we never transform FormulaUnit into Clause
  return static_cast<FormulaUnit*>(res0);
}


void PredicateDefinition::eliminatePredicateDefinition(unsigned pred, ReplMap& replacements)
{
  CALL("PredicateDefinition::eliminatePredicateDefinition");

  PredData& pd=_preds[pred];
  ASS(pd.defUnit);
  FormulaUnit* def0 = pd.defUnit;
  FormulaUnit* def = getReplacement(def0, replacements);
  FormulaUnit* repl;

  pd.defUnit = 0; //we're eliminating the definition

  ASS(pd.pocc==0 || pd.nocc==0);
  if(pd.pocc==0 && pd.nocc==0) {
    //pred does not occur anywhere else, hence can be deleted
    repl = 0;
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] definition " << (*def) << " removed" << std::endl;
      env.endOutput();
    }
    _processedPrb->addEliminatedPredicate(pred,def);
  }
  else {
    //otherwise it occurs either only positively or only negatively,
    //so we can make an equivalence into an implication
    bool fwd = pd.nocc==0;
    ASS_EQ(fwd, pd.pocc!=0);

    repl = makeImplFromDef(def, pred, fwd);

    if(!repl) {
      //the definition formula was simplified by other transformation to the      
      //point it is no longer definition that can be eliminated
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] Formula " << (*def) 
                << " is no longer in the shape of definition of "
                << env.signature->predicateName(pred) 
                << ". The original definition was " << (*def0) 
                << "." << std::endl;
        env.endOutput();
      }
      
      return;
    }
    _processedPrb->addPartiallyEliminatedPredicate(pred,def);

    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] definition " << (*def) << " replaced by " 
              << (*repl) << std::endl;
      env.endOutput();
    }    
  }
  if(repl) {
    count(repl, 1);
  }
  count(def, -1);
  ALWAYS(replacements.insert(def, repl));

  env.statistics->unusedPredicateDefinitions++;
}

void PredicateDefinition::replacePurePred(unsigned pred, ReplMap& replacements)
{
  CALL("PredicateDefinition::replacePurePred");

  PredData& pd=_preds[pred];
  ASS(pd.pocc==0 || pd.nocc==0);

  _purePreds.insert(pred, pd.nocc==0);
  if(_processedPrb) {
    _processedPrb->addTrivialPredicate(pred, pd.nocc==0);
  }
  Set<Unit*>::Iterator uit(pd.containingUnits);
  while(uit.hasNext()) {
    Unit* u=uit.next();
    if(replacements.find(u)) {
      //The unit has already been replaced.
      continue;
    }
    Unit* v=replacePurePredicates(u);

    ASS_NEQ(u,v);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
        if (v) {
          env.out() << "unit " << (*u) << " replaced by " << (*v) << endl;
        } else {
          env.out() << "unit " << (*u) << " removed" << endl;
        }
      env.endOutput();
    }
    
    count(v,1);
    count(u,-1);
    ALWAYS(replacements.insert(u,v));
  }

  env.statistics->purePredicates++;
}

/**
 *
 * @pre Formulas must be rectified and flattened.
 */
void PredicateDefinition::collectReplacements(UnitList* units, ReplMap& replacements)
{
  CALL("PredicateDefinition::collectReplacements");

  UnitList::Iterator scanIterator(units);
  while(scanIterator.hasNext()) {
    scan(scanIterator.next());
  }

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    for (unsigned i = 0; i < _predCnt; ++i) {
      if (!_preds[i].pocc && !_preds[i].nocc && !_preds[i].docc)
        continue;      
      env.out() << _preds[i].stateToString() << endl;
    }    
    env.endOutput();
  }  

  for(unsigned pred=1; pred<_predCnt; pred++) {
    _preds[pred].check(this);
  }

  while(_eliminable.isNonEmpty() || _pureToReplace.isNonEmpty()) {
    while(_eliminable.isNonEmpty()) {
      int pred=_eliminable.pop();
      eliminatePredicateDefinition(pred, replacements);
    }
    while(_pureToReplace.isNonEmpty()) {
      int pred=_pureToReplace.pop();
      replacePurePred(pred, replacements);
    }
  }
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    for(unsigned i=0; i<_predCnt; ++i) {
      if(!_preds[i].pocc && !_preds[i].nocc  && !_preds[i].docc ) { continue; }
      env.out() << _preds[i].stateToString() << endl;
    }    
    env.endOutput();
  }
}

void PredicateDefinition::removeUnusedDefinitionsAndPurePredicates(Problem& prb)
{
  CALL("PredicateDefinition::removeUnusedDefinitionsAndPurePredicates");

  ScopedLet<Problem*> prbLet(_processedPrb, &prb);
  removeUnusedDefinitionsAndPurePredicates(prb.units());
}

void PredicateDefinition::removeUnusedDefinitionsAndPurePredicates(UnitList*& units)
{
  CALL("PredicateDefinition::removeUnusedDefinitionsAndPurePredicates");

  static DHMap<Unit*, Unit*> replacements;
  replacements.reset();

  collectReplacements(units, replacements);

  UnitList::DelIterator replaceIterator(units);
  while(replaceIterator.hasNext()) {
    Unit* u = replaceIterator.next();
    Unit* v = getReplacement(u, replacements);
    if(u==v) {
      continue;
    }
    if(!v || ( !v->isClause() && static_cast<FormulaUnit*>(v)->formula()->connective()==TRUE ) ) {
      replaceIterator.del();
    }
    else {
      replaceIterator.replace(v);
    }
  }

}

FormulaUnit* PredicateDefinition::replacePurePredicates(FormulaUnit* u)
{
  Formula* resf=replacePurePredicates(u->formula());
  if(resf!=u->formula()) {
    return new FormulaUnit(resf,NonspecificInference1(InferenceRule::PURE_PREDICATE_REMOVAL, u));
  }
  else {
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
  if(u->derivedFromGoal() && env.options->ignoreConjectureInPreprocessing()){
    return u;
  }
  if(u->isClause()) {
    return replacePurePredicates(static_cast<Clause*>(u));
  }
  else {
    return replacePurePredicates(static_cast<FormulaUnit*>(u));
  }
}

Formula* PredicateDefinition::replacePurePredicates(Formula* f)
{
  CALL("PredicateDefinition::replacePurePredicates");

  Connective con = f->connective();
  switch (con) {
  case LITERAL:
  {
    Literal* l = f->literal();
    bool value;
    if(!_purePreds.find(l->functor(), value)) {
      return f;
    }
    return new Formula(value^l->isNegative());
  }

  case BOOL_TERM:
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
      VList* vl=arg->vars();
      VList::Iterator vit(f->vars());
      while(vit.hasNext()) {
        VList::push(vit.next(), vl);
      }
      // sl should either be empty or the equivalent concatenation as vl
      // if the sorts of either arg or f are empty then sl should be empty
      SList* sl= SList::empty();
      if(arg->sorts() && f->sorts()){
        sl=arg->sorts();
        SList::Iterator sit(f->sorts());
        while(sit.hasNext()){
          SList::push(sit.next(),sl);
        }
      }

      return new QuantifiedFormula(con,vl,sl,arg->qarg());
    }
    switch (arg->connective()) {
    case FALSE:
    case TRUE:
      return arg;
    default:
      return arg == f->qarg()
	      ? f
	      : new QuantifiedFormula(con,f->vars(),f->sorts(),arg);
    }
  }
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Made definition in the form of equivalence into an implication
 * If the input formula is not a definition of predicate pred, return 0.
 */
FormulaUnit* PredicateDefinition::makeImplFromDef(FormulaUnit* def, unsigned pred, bool forward)
{
  Formula* f0=def->formula();
  Formula* f;

  bool isQuantified=f0->connective()==FORALL;
  if(isQuantified) {
    f=f0->qarg();
  } else {
    f=f0;
  }

  Formula* lhs;
  Formula* rhs;

  switch (f->connective()) {
    case IFF: {
      if(f->left()->connective()==LITERAL && f->left()->literal()->functor()==pred) {
        lhs=f->left();
        rhs=f->right();
      } else {
        lhs = f->right();
        rhs = f->left();
      }
      break;
    }

    default:
      return 0;
  }

  if(lhs->connective()!=LITERAL || lhs->literal()->functor()!=pred) {
    return 0;
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
    resf0=new QuantifiedFormula(FORALL, f0->vars(), f0->sorts(), resf);
  } else {
    resf0=resf;
  }
  return new FormulaUnit(resf0,NonspecificInference1(InferenceRule::UNUSED_PREDICATE_DEFINITION_REMOVAL, def));
}

void PredicateDefinition::scan(Unit* u)
{
  if(!(u->derivedFromGoal() && env.options->ignoreConjectureInPreprocessing())){
    if(u->isClause()) {
      scan(static_cast<Clause*>(u));
    } else {
      scan(static_cast<FormulaUnit*>(u));
    }
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

  switch (f->connective()) {
    case IFF:
      if(f->left()->connective()==LITERAL) {
        if(tryGetDef(f->left()->literal(), f->right(), unit)) {
          return;
        }
      }
      if(f->right()->connective()==LITERAL) {
        tryGetDef(f->right()->literal(), f->left(), unit);
      }
      break;

    case FORALL:
      ASSERTION_VIOLATION_REP(unit->toString()); //formula is flattened

    default:
      break;
  }
}

void PredicateDefinition::count (Unit* u,int add)
{
  CALL("PredicateDefinition::count(Unit*,int)");
  if(!u) {
    return;
  }
  if(u->isClause()) {
    count(static_cast<Clause*>(u), add);
  }
  else {
    count(static_cast<FormulaUnit*>(u), add);
  }
}

void PredicateDefinition::count (Clause* cl, int add)
{
  CALL("PredicateDefinition::count(Clause*,int)");
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
      int pred = l->functor();
      _preds[pred].add(l->isPositive() ? polarity : -polarity, add, this);
      if(add==1) {
        _preds[pred].containingUnits.insert(unit);
      }
      Term::Iterator args(l);
      while (args.hasNext()) {
        count(args.next(), add, unit);
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

    case BOOL_TERM:
      count (f->getBooleanTerm(), add, unit);
      return;

    case NAME:
    case NOCONN:
      ASSERTION_VIOLATION;
  }
} // PredicateDefinition::count (Formula* f,...)

void PredicateDefinition::count (TermList ts,int add, Unit* unit)
{
  CALL("PredicateDefinition::count(TermList,...)");

  if (ts.isVar()) {
    return;
  }

  Term* term = ts.term();

  if (term->shared()) {
    return;
  }

  if (term->isSpecial()) {
    Term::SpecialTermData* sd = term->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA:
        count(sd->getFormula(), 0, add, unit);
        break;

      case Term::SF_ITE:
        count(sd->getCondition(), 0, add, unit);
        break;

      case Term::SF_LET:
      case Term::SF_LET_TUPLE:
        count(sd->getBinding(), add, unit);
        break;

      case Term::SF_TUPLE:
        count(TermList(sd->getTupleTerm()), add, unit);
        break;

      case Term::SF_MATCH:
        break; // args are handled later

      default:
        ASSERTION_VIOLATION;
    }
  }

  Term::Iterator args(term);
  while (args.hasNext()) {
    count(args.next(), add, unit);
  }
} // PredicateDefinition::count (TermList ts,...)

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
  bool hasExtraVars = false;

  while(sfit.hasNext()) {
    Formula* sf=sfit.next();
    if(sf->connective()!=LITERAL) {
      continue;
    }
    Literal* lit=sf->literal();
    if(lit->functor()==lhs->functor()) {
      return false;
    }
    VariableIterator vit(lit);
    while(vit.hasNext()) {
      unsigned v=vit.next().var();
      if(!counter.get(v)) {
	hasExtraVars = true;
      }
    }
  }
  if(hasExtraVars) {
    bool extraFreeVars = false;
    FormulaVarIterator fvit(rhs);
    while(fvit.hasNext()) {
      unsigned v = fvit.next();
      if(!counter.get(v)) {
        extraFreeVars = true;
      }
    }
    if(extraFreeVars) {
      return false;
    }
  }

  _preds[lhs->functor()].setDefUnit(unit);
  return true;
}

}
