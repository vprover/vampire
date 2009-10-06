/**
 * @file Interpolants.cpp
 * Implements class Interpolants.
 */

#include "../Lib/Stack.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Formula.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/InferenceStore.hpp"
#include "../Kernel/SubstHelper.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Unit.hpp"

#include "SimplifyFalseTrue.hpp"

#include "Interpolants.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

typedef InferenceStore::UnitSpec UnitSpec;
typedef pair<Formula*, Formula*> UIPair; //pair of unit U and the U-interpolant

struct ItemState
{
  ItemState() : parCnt(0), inheritedColor(COLOR_TRANSPARENT), interpolant(0), leftInts(0), rightInts(0) {}

  //parents in the sense of inferencing, but children in the sense of DFS traversal
  VirtualIterator<UnitSpec> pars;
  int parCnt;
  Color inheritedColor;
  UnitSpec us;
  Formula* interpolant;
  List<UIPair>* leftInts;
  List<UIPair>* rightInts;

};

void generateInterpolant(ItemState& st);


Formula* Interpolants::getInterpolant(Clause* cl)
{
  CALL("Interpolants::getInterpolant");

  //TODO: all formulas should be probably quantified before used, not just clauses

  Stack<ItemState> sts;
  Stack<UnitSpec> todo;

  UnitSpec curr=UnitSpec(cl, cl->prop());
  
  for(;;) {
    ItemState st;
    st.us=curr;
    //cout<<"#:"<<curr.first->toString()<<endl;
    if(curr.first->inheritedColor()!=COLOR_INVALID) {
      //set premise-color information for input clauses
      st.inheritedColor=curr.first->inheritedColor();
    }

    if(sts.isNonEmpty()) {
      //update premise color information in the level above
      ItemState& pst=sts.top(); //parent state
      pst.parCnt++;
      if(pst.inheritedColor==COLOR_TRANSPARENT) {
        pst.inheritedColor=curr.first->getColor();
      }
#if VDEBUG
      else {
        Color clr=curr.first->getColor();
	//cout<<clr<<' '<<pst.inheritedColor<<endl;
        ASS(pst.inheritedColor==clr || clr==COLOR_TRANSPARENT);
      }
#endif
    }
    st.pars=InferenceStore::instance()->getUnitParents(curr.first, curr.second);

    sts.push(st);

    for(;;) {
      if(sts.top().pars.hasNext()) {
        curr=sts.top().pars.next();
        break;
      }
      //we're done with all children, now we can process what we've gathered
      st=sts.pop();
      Unit* u=st.us.first;
      Color color=u->getColor();
      if(st.inheritedColor!=color || sts.isEmpty()) {
	//we either have a transparent clause justified by A or B, or the refutation
        ASS_EQ(color, COLOR_TRANSPARENT);
	generateInterpolant(st);
      }
      
      if(sts.isNonEmpty()) {
	//pass interpolants to the level above
        if(color!=COLOR_LEFT) {
          sts.top().leftInts=List<UIPair>::concat(sts.top().leftInts, st.leftInts);
        } 
	else {
	  st.leftInts->destroy();
        }
        if(color!=COLOR_RIGHT) {
          sts.top().rightInts=List<UIPair>::concat(sts.top().rightInts, st.rightInts);
        }
        else {
          st.rightInts->destroy();
        }
      } 
      else {
	//we have now the interpolant for refutation, so we can
	//clean-up and exit
        st.leftInts->destroy();
        st.rightInts->destroy();
	return SimplifyFalseTrue::simplify(st.interpolant);
      }
    };
  }
}

void generateInterpolant(ItemState& st)
{
  CALL("generateInterpolant");

  Unit* u=st.us.first;
  Color color=u->getColor();
  ASS_EQ(color, COLOR_TRANSPARENT);

  Formula* interpolant;
  Formula* unitFormula=u->getFormula(st.us.second);

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
