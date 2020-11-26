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
 * @file Interpolants.cpp
 * Implements class Interpolants.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "Flattening.hpp"
#include "SimplifyFalseTrue.hpp"
#include "NNF.hpp"

#include "Interpolants.hpp"

#define TRACE(x)

/** surprising colors occur when a clause which is a consequence of transparent clauses, is colored */
#define ALLOW_SURPRISING_COLORS 1

namespace Shell
{

using namespace Lib;
using namespace Kernel;

typedef pair<Formula*, Formula*> UIPair; //pair of unit U and the U-interpolant
typedef List<UIPair> UIPairList;

VirtualIterator<Unit*> Interpolants::getParents(Unit* u)
{
  CALL("Interpolants::getParents");

  if(!_slicedOff) {
    return InferenceStore::instance()->getParents(u);
  }

  static Stack<Unit*> toDo;
  static Stack<Unit*> parents;

  toDo.reset();
  parents.reset();

  for(;;) {
    UnitIterator pit = InferenceStore::instance()->getParents(u);
    while(pit.hasNext()) {
      Unit* par = pit.next();
      if(_slicedOff->find(par)) {
	toDo.push(par);
      }
      else {
	parents.push(par);
      }
    }
    if(toDo.isEmpty()) {
      break;
    }
    u = toDo.pop();
  }

  return getPersistentIterator(Stack<Unit*>::BottomFirstIterator(parents));
}

struct Interpolants::ItemState
{
  ItemState() : parCnt(0), inheritedColor(COLOR_INVALID), interpolant(0), leftInts(0), rightInts(0), processed(false), _us(nullptr), _usColor(COLOR_INVALID) {}

  ItemState(Unit* us) : parCnt(0), inheritedColor(COLOR_TRANSPARENT), interpolant(0),
      leftInts(0), rightInts(0), processed(false), _us(us)
  {
    CALL("ItemState::ItemState");
    _usColor = us->getColor();
  }

  void destroy()
  {
    CALL("ItemState::destroy");

    List<UIPair>::destroy(leftInts);
    List<UIPair>::destroy(rightInts);
  }

  Unit* us() const { return _us; }
  Color usColor() const { return _usColor; }
  /** Parents that remain to be traversed
   *
   * Parents in the sense of inferencing, but children in the sense of DFS traversal */
  VirtualIterator<Unit*> pars;
  /** number of parents */
  int parCnt;
  /** Color of premise formulas, or the declared color for input formulas */
  Color inheritedColor;
  /** If non-zero, interpolant of the current formula. */
  Formula* interpolant;
  /** Left interpolants of parent formulas */
  List<UIPair>* leftInts;
  /** Right interpolants of parent formulas */
  List<UIPair>* rightInts;
  /** This state was processed, and if it should have its invarient generated,
   * it was generated */
  bool processed;
private:
  /** The current formula */
  Unit* _us;
  Color _usColor;
};

Comparison compareUIP(const UIPair& a, const UIPair& b)
{
  CALL("compareUIP");

  Comparison res = Int::compare(a.first, b.first);
  if(res==EQUAL) {
    res = Int::compare(a.second, b.second);
  }
  return res;
}

/**
 * Assuming arguments are lists ordered by the @c compareUIP() function,
 * add non-destructively new elements from @c src into @c tgt.
 */
void mergeCopy(UIPairList*& tgt, UIPairList* src)
{
  CALL("mergeCopy");
  if(!tgt) {
    tgt = UIPairList::copy(src);
    return;
  }

  UIPairList** curr = &tgt;
  UIPairList::Iterator sit(src);
  while(sit.hasNext()) {
    UIPair spl = sit.next();
  retry_curr:
    if(*curr) {
      Comparison cmp = compareUIP((*curr)->head(), spl);
      if(cmp!=GREATER) {
	curr = (*curr)->tailPtr();
	if(cmp==EQUAL) {
	  continue;
	}
	else {
	  goto retry_curr;
	}
      }
    }
    *curr = new UIPairList(spl, *curr);
    curr = (*curr)->tailPtr();
  }
}

/**
 * Any pre-processing of the refutation before interpolation is considered.
 *
 * We remove the leafs corresponding to the conjecture
 * and leave the negated_conjecture child of this unit as the leaf instead.
 * (Inference::NEGATED_CONJECTURE is not sound).
 */
void Interpolants::removeConjectureNodesFromRefutation(Unit* refutation)
{
  CALL("Interpolants::removeConjectureNodesFromRefutation");

  Stack<Unit*> todo;
  DHSet<Unit*> seen;

  todo.push(refutation);
  while (todo.isNonEmpty()) {
    Unit* cur = todo.pop();
    if (!seen.insert(cur)) {
      continue;
    }

    if (cur->inference().rule() == InferenceRule::NEGATED_CONJECTURE) {
      VirtualIterator<Unit*> pars = InferenceStore::instance()->getParents(cur);

      // negating the conjecture is not a sound inference,
      // we want to consider the proof only from the point where it has been done already

      ASS(pars.hasNext()); // negating a conjecture should have exactly one parent
      Unit* par = pars.next();

      // so we steal parent's inherited color
      cur->setInheritedColor(par->inheritedColor());

      // and pretend there is no parent

      ASS(!pars.hasNext()); // negating a conjecture should have exactly one parent

      cur->inference().destroy();
      cur->inference() = Inference(NonspecificInference0(UnitInputType::NEGATED_CONJECTURE,InferenceRule::NEGATED_CONJECTURE)); // negated conjecture without a parent (non-standard, but nobody will see it)
    }

    todo.loadFromIterator(InferenceStore::instance()->getParents(cur));
  }
}

/**
* For any input unit marked as properly colored but which is, in fact, transparent,
* we add an artificial parent which is forced to pretend it was truly colored that way,
* so that InterpolantMinimizer can consider this input unit as a result of a symbol eliminating inference.
* (Without this, InterpolantMinimizer does not work properly in such cases.)
 */
void Interpolants::fakeNodesFromRightButGrayInputsRefutation(Unit* refutation)
{
  CALL("Interpolants::fakeNodesFromRightButGrayInputsRefutation");

  Stack<Unit*> todo;
  DHSet<Unit*> seen;

  todo.push(refutation);
  while (todo.isNonEmpty()) {
    Unit* cur = todo.pop();
    if (!seen.insert(cur)) {
      continue;
    }

    {
      VirtualIterator<Unit*> pars = InferenceStore::instance()->getParents(cur);

      if (!pars.hasNext() && // input-like, because no parents
          cur->inheritedColor() != COLOR_INVALID && cur->inheritedColor() != COLOR_TRANSPARENT && // proper inherited color
          cur->getColor() == COLOR_TRANSPARENT) {  // but in fact transparent

          Clause* fakeParent = Clause::fromIterator(LiteralIterator::getEmpty(), NonspecificInference0(cur->inputType(),InferenceRule::INPUT));
          fakeParent->setInheritedColor(cur->inheritedColor());
          fakeParent->updateColor(cur->inheritedColor());

          cur->inference().destroy();
          cur->inference() = Inference(NonspecificInference1(InferenceRule::INPUT,fakeParent)); // input inference with a parent (non-standard, but nobody will see it)
          cur->invalidateInheritedColor();
      }
    }

    todo.loadFromIterator(InferenceStore::instance()->getParents(cur));
  }
}


/**
 * Turn all Units in a refutation into FormulaUnits (casting Clauses to Formulas and wrapping these as Units).
 *
 * Keep the old refutation (= non-destructive). Possible sharing of the formula part of the original refutation.
 *
 * Assume that once we have formula on a parent path we can't go back to a clause.
 *
 */
Unit* Interpolants::formulifyRefutation(Unit* refutation)
{
  CALL("Interpolants::formulifyRefutation");

  Stack<Unit*> todo;
  DHMap<Unit*,Unit*> translate; // for caching results (we deal with a DAG in general), but also to distinguish the first call from the next

  todo.push(refutation);
  while (todo.isNonEmpty()) {
    Unit* cur = todo.top();

    if (translate.find(cur)) {  // the DAG hit case
      todo.pop();

      continue;
    }

    if (!cur->isClause()) {     // the formula case
      todo.pop();

      translate.insert(cur,cur);
      continue;
    }

    // are all children done?
    bool allDone = true;
    Inference& inf = cur->inference();
    Inference::Iterator iit = inf.iterator();
    while (inf.hasNext(iit)) {
      Unit* premUnit=inf.next(iit);
      if (!translate.find(premUnit)) {
        allDone = false;
        break;
      }
    }

    if (allDone) { // ready to return
      todo.pop();

      List<Unit*>* prems = 0;

      Inference::Iterator iit = inf.iterator();
      while (inf.hasNext(iit)) {
        Unit* premUnit=inf.next(iit);

        List<Unit*>::push(translate.get(premUnit), prems);
      }

      InferenceRule rule=inf.rule();
      prems = List<Unit*>::reverse(prems);  //we want items in the same order

      Formula* f = Formula::fromClause(cur->asClause());
      FormulaUnit* fu = new FormulaUnit(f,NonspecificInferenceMany(rule,prems));

      if (cur->inheritedColor() != COLOR_INVALID) {
        fu->setInheritedColor(cur->inheritedColor());
      }

      translate.insert(cur,fu);
    } else { // need "recursive" calls first

      Inference::Iterator iit = inf.iterator();
      while (inf.hasNext(iit)) {
        Unit* premUnit=inf.next(iit);
        todo.push(premUnit);
      }
    }
  }

  return translate.get(refutation);
}

Formula* Interpolants::getInterpolant(Unit* unit)
{
  CALL("Interpolants::getInterpolant");

  typedef DHMap<Unit*,ItemState> ProcMap;
  ProcMap processed;

  TRACE(cout << "===== getInterpolant for " << unit->toString() << endl);

  Stack<ItemState> sts;

  Unit* curr= unit;

  Formula* resultInterpolant = 0;

  int ctr=0;

  for(;;) {
    ItemState st;

    if(processed.find(curr)) {
      st = processed.get(curr);
      ASS(st.us()==curr);
      ASS(st.processed);
      ASS(!st.pars.hasNext());
    }
    else {
      st = ItemState(curr);
      st.pars = getParents(curr);
    }

    TRACE(cout << "curr  " << curr->toString() << endl);
    TRACE(cout << "cu_ic " << curr->inheritedColor() << endl);
    TRACE(cout << "st_co " << st.usColor() << endl);

    if(curr->inheritedColor()!=COLOR_INVALID) {
      //set premise-color information for input clauses
      st.inheritedColor=ColorHelper::combine(curr->inheritedColor(), st.usColor());
      ASS_NEQ(st.inheritedColor, COLOR_INVALID);
    }
#if ALLOW_SURPRISING_COLORS
    else {
      //we set inherited color to the color of the unit.
      //in the case of clause being conclusion of
      //transparent parents, the assigned color should be
      //transparent as well, but there are some corner cases
      //coming from proof transformations which can yield us
      //a colored clause in such case (when the colored premise
      //was removed by the transformation).
      st.inheritedColor=st.usColor();
    }
#else
    else if(!st.processed && !st.pars.hasNext()) {
      //we have unit without any parents. This case is reserved for
      //units introduced by some naming. In this case we need to set
      //the inherited color to the color of the unit.
      st.inheritedColor=st.usColor();
    }
#endif

    TRACE(cout << "st_ic " << st.inheritedColor << endl);

    if(sts.isNonEmpty()) {
      //update premise color information in the level above
      ItemState& pst=sts.top(); //parent state
      pst.parCnt++;
      if(pst.inheritedColor==COLOR_TRANSPARENT) {
        pst.inheritedColor=st.usColor();

        TRACE(cout << "updated parent's inh col to " << pst.inheritedColor << endl);
        TRACE(cout << "parent " << pst.us()->toString() << endl);

      }
#if VDEBUG
      else {
        Color clr=st.usColor();
        ASS_REP2(pst.inheritedColor==clr || clr==COLOR_TRANSPARENT, pst.us()->toString(), curr->toString());
      }
      ASS_EQ(curr->getColor(),st.usColor());
#endif
    }

    // keep initializing splitting components
    if (curr->isClause()) {
      Clause* cl = curr->asClause();

      if (cl->isComponent()) {
        SplitSet* splits = cl->splits();
        ASS_EQ(splits->size(),1);
        _splittingComponents.insert(splits->sval(),cl);
      }
    }

    sts.push(st);

    for(;;) {
      if(sts.top().pars.hasNext()) {
        curr=sts.top().pars.next();
        break;
      }
      //we're done with all children, now we can process what we've gathered
      st=sts.pop();
      ctr++;
      Color color = st.usColor();
      if(!st.processed) {
	if(st.inheritedColor!=color || sts.isEmpty()) {
	  //we either have a transparent clause justified by A or B, or the refutation
//	  ASS_EQ(color,COLOR_TRANSPARENT);
	    TRACE(cout<<"generate interpolant of transparent clause: "<<st.us()->toString()<<"\n");
	  ASS_REP2(color==COLOR_TRANSPARENT, st.us()->toString(), st.inheritedColor);
	  generateInterpolant(st);
	}
	st.processed = true;
	processed.insert(st.us(), st);
      }
      
      if(sts.isNonEmpty()) {
	//pass interpolants to the level above
        if(color!=COLOR_LEFT) {
          mergeCopy(sts.top().leftInts, st.leftInts);
        } 
        if(color!=COLOR_RIGHT) {
          mergeCopy(sts.top().rightInts, st.rightInts);
        }
      } 
      else {
	//empty sts (so refutation) with clause st justified by A or B (st is false). 
	//interpolant was already generated in st.interpolant
	//we have now the interpolant for refutation
        resultInterpolant = st.interpolant;
        goto fin;
      }
    }
  }

fin:

  //clean-up
  ProcMap::Iterator destrIt(processed);
  while(destrIt.hasNext()) {
    destrIt.next().destroy();
  }

  TRACE(cout << "result interpolant (before false/true - simplification) " << resultInterpolant->toString() << endl);

  cout << "Before simplification: " << resultInterpolant->toString() << endl;
  cout << "Weight before simplification: " << resultInterpolant->weight() << endl;

  //simplify the interpolant and exit
  return Flattening::flatten(NNF::ennf(Flattening::flatten(SimplifyFalseTrue::simplify(resultInterpolant)),true));
//  return resultInterpolant;
}

void Interpolants::generateInterpolant(ItemState& st)
{
  CALL("Interpolants::generateInterpolant");

  Unit* u=st.us();

  TRACE(cout << "GenerateInterpolant for " << u->toString() << endl);

  ASS_EQ(st.usColor(), COLOR_TRANSPARENT);

  Formula* interpolant;
  Formula* unitFormula=u->getFormula();//st.us().prop());

  // add assertions from splitting
  if (u->isClause()) {
    Clause* cl = u->asClause();

    if (cl->splits()) {
      FormulaList* disjuncts = FormulaList::empty();
      SplitSet::Iterator it(*cl->splits());
      while(it.hasNext()) {
        SplitLevel lv=it.next();
        Clause* ass = _splittingComponents.get(lv);
        FormulaList::push(new NegatedFormula(Formula::fromClause(ass)),disjuncts);
      }
      if (FormulaList::isNonEmpty(disjuncts)) {
        FormulaList::push(unitFormula,disjuncts);

        unitFormula = JunctionFormula::generalJunction(OR, disjuncts);
      }
    }
  }

  TRACE(cout	<<"unitFormula: "<<unitFormula->toString()<<endl);

  if(st.parCnt) {
    //interpolants from refutation proof with at least one inference (there are premises, i.e. parents)
    FormulaList* conj=0;
    List<UIPair>* src= (st.inheritedColor==COLOR_LEFT) //source of relevant parent interpolants
        ? st.rightInts
        : st.leftInts;
    //construct the common part of the interpolant
    List<UIPair>::Iterator sit(src);
    while(sit.hasNext()) {
      UIPair uip=sit.next();
      FormulaList* disj=0;
      FormulaList::push(uip.first, disj);
      FormulaList::push(uip.second, disj);
      FormulaList::push(JunctionFormula::generalJunction(OR, disj), conj);
    }

    if(st.inheritedColor==COLOR_LEFT) {
      //u is justified by A
      FormulaList* innerConj=0;
      List<UIPair>::Iterator sit2(src);
      while(sit2.hasNext()) {
        UIPair uip=sit2.next();
        FormulaList::push(uip.first, innerConj);
      }
      FormulaList::push(new NegatedFormula(JunctionFormula::generalJunction(AND, innerConj)), conj);
    }
    else {
      //u is justified by B or a refutation
    }
    interpolant=JunctionFormula::generalJunction(AND, conj);
  }
  else {
    //trivial interpolants (when there are no premises)
    if(st.inheritedColor==COLOR_RIGHT) {
      interpolant=new NegatedFormula(unitFormula); //this is for TRUE interpolant if the unitFormula is False
    }
    else {
      //a formula coming from left or a refutation
      interpolant=unitFormula; //this is for FALSE interpolant if the unitFormula is False
    }
  }
  st.interpolant=interpolant;
  TRACE(cout<<"Unit "<<u->toString()
	<<"\nto Formula "<<unitFormula->toString()
	<<"\ninterpolant "<<interpolant->toString()<<endl<<endl);
  UIPair uip=make_pair(unitFormula, interpolant);
  if(st.inheritedColor==COLOR_LEFT) {
    List<UIPair>::destroy(st.leftInts);
    st.leftInts=0;
    List<UIPair>::push(uip,st.leftInts);
  }
  else if(st.inheritedColor==COLOR_RIGHT) {
    List<UIPair>::destroy(st.rightInts);
    st.rightInts=0;
    List<UIPair>::push(uip,st.rightInts);
  }
}

}
