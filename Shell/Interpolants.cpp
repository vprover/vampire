/**
 * @file Interpolants.cpp
 * Implements class Interpolants.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "SimplifyFalseTrue.hpp"

#include "Interpolants.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

typedef InferenceStore::UnitSpec UnitSpec;
typedef pair<Formula*, Formula*> UIPair; //pair of unit U and the U-interpolant
typedef List<UIPair> UIPairList;

struct ItemState
{
  ItemState() : parCnt(0), inheritedColor(COLOR_TRANSPARENT), interpolant(0),
      leftInts(0), rightInts(0), processed(false) {}

  void destroy()
  {
    CALL("ItemState::destroy");

    leftInts->destroy();
    rightInts->destroy();
  }

  /** Parents that remain to be traversed
   *
   * Parents in the sense of inferencing, but children in the sense of DFS traversal */
  VirtualIterator<UnitSpec> pars;
  /** number of parents */
  int parCnt;
  /** Color of premise formulas, or the declared color for input formulas */
  Color inheritedColor;
  /** The current formula */
  UnitSpec us;
  /** If non-zero, interpolant of the current formula. */
  Formula* interpolant;
  /** Left interpolants of parent formulas */
  List<UIPair>* leftInts;
  /** Right interpolants of parent formulas */
  List<UIPair>* rightInts;
  /** This state was processed, and if it should have its invarient generated,
   * it was generated */
  bool processed;

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
    tgt = src->copy();
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

void generateInterpolant(ItemState& st);

Formula* Interpolants::getInterpolant(Clause* cl)
{
  CALL("Interpolants::getInterpolant");

  typedef DHMap<UnitSpec,ItemState> ProcMap;
  ProcMap processed;

  Stack<ItemState> sts;

  UnitSpec curr=UnitSpec(cl, cl->prop());

  Formula* resultInterpolant = 0;

  int ctr=0;

  for(;;) {
    ItemState st;

    if(processed.find(curr)) {
      st = processed.get(curr);
      ASS(st.us==curr);
      ASS(st.processed);
      ASS(!st.pars.hasNext());
    }
    else {
      st.us = curr;
      st.pars=InferenceStore::instance()->getParents(curr);
    }

    if(curr.unit()->inheritedColor()!=COLOR_INVALID) {
      //set premise-color information for input clauses
      st.inheritedColor=static_cast<Color>(curr.unit()->inheritedColor()|curr.unit()->getColor());
      ASS_NEQ(st.inheritedColor, COLOR_INVALID);
    }

    if(sts.isNonEmpty()) {
      //update premise color information in the level above
      ItemState& pst=sts.top(); //parent state
      pst.parCnt++;
      if(pst.inheritedColor==COLOR_TRANSPARENT) {
        pst.inheritedColor=curr.unit()->getColor();
      }
#if VDEBUG
      else {
        Color clr=curr.unit()->getColor();
        ASS(pst.inheritedColor==clr || clr==COLOR_TRANSPARENT);
      }
#endif
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
      Unit* u = st.us.unit();
      Color color = u->getColor();
      if(!st.processed) {
	if(st.inheritedColor!=color || sts.isEmpty()) {
	  //we either have a transparent clause justified by A or B, or the refutation
	  ASS_EQ(color, COLOR_TRANSPARENT);
	  generateInterpolant(st);
	}
	st.processed = true;
	processed.insert(st.us, st);
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

  //simplify the interpolant and exit
  return SimplifyFalseTrue::simplify(resultInterpolant);
}

void generateInterpolant(ItemState& st)
{
  CALL("generateInterpolant");

  Unit* u=st.us.unit();
  Color color=u->getColor();
  ASS_EQ(color, COLOR_TRANSPARENT);

  Formula* interpolant;
  Formula* unitFormula=u->getFormula(st.us.prop());

  if(st.parCnt) {
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
      interpolant=new NegatedFormula(unitFormula);
    }
    else {
      //a formula coming from left or a refutation
      interpolant=unitFormula;
    }
  }
  st.interpolant=interpolant;
//  cout<<"Unit "<<u->toString()
//	<<"\nto Formula "<<unitFormula->toString()
//	<<"\ninterpolant "<<interpolant->toString()<<endl;
  UIPair uip=make_pair(unitFormula, interpolant);
  if(st.inheritedColor==COLOR_LEFT) {
    st.leftInts->destroy();
    st.leftInts=0;
    List<UIPair>::push(uip,st.leftInts);
  }
  else if(st.inheritedColor==COLOR_RIGHT) {
    st.rightInts->destroy();
    st.rightInts=0;
    List<UIPair>::push(uip,st.rightInts);
  }
#if VDEBUG
  else {
    //we create interpolants either for A/B justified units, or for the refutation
    ASS(u->isClause() && static_cast<Clause*>(u)->isEmpty());
  }
#endif

}

}
