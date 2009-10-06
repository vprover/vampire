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

#include "Interpolants.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

typedef InferenceStore::UnitSpec UnitSpec;
typedef pair<Formula*, Formula*> UIPair; //pair of unit U and the U-interpolant

struct ItemState
{
  ItemState() : parCnt(0), inheritedColor(COLOR_TRANSPARENT), leftInts(0), rightInts(0) {}

  //parents in the sense of inferencing, but children in the sense of DFS traversal
  VirtualIterator<UnitSpec> pars;
  int parCnt;
  Color inheritedColor;
  UnitSpec us;
  List<UIPair>* leftInts;
  List<UIPair>* rightInts;

};

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
    if(curr.first->inheritedColor()!=COLOR_INVALID) {
      st.inheritedColor=curr.first->inheritedColor();
    }

    if(sts.isNonEmpty()) {
      ItemState& pst=sts.top(); //parent state
      pst.parCnt++;
      if(pst.inheritedColor==COLOR_TRANSPARENT) {
        pst.inheritedColor=curr.first->getColor();
      }
#if VDEBUG
      else {
        Color clr=curr.first->getColor();
        ASS(pst.inheritedColor==clr || clr==COLOR_TRANSPARENT);
      }
#endif
    }
    st.pars=InferenceStore::instance()->getUnitParents(curr.first, curr.second);

    sts.push(st);

    do {
      if(sts.top().pars.hasNext()) {
        curr=sts.top().pars.next();
        break;
      }
      else {
        //we're done with all children, now we can process what we've gathered
        st=sts.pop();
        Unit* u=st.us.first;
        Color color=u->getColor();
        if(st.inheritedColor!=color) {
          ASS_EQ(color, COLOR_TRANSPARENT);
	  Formula* interpolant;
	  Formula* unitFormula=u->getFormula();

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
	      FormulaList::push(new JunctionFormula(OR, disj), conj);
	    }

            if(st.inheritedColor==COLOR_LEFT) {
	      //u is justified by A
              FormulaList* innerConj=0;
              List<UIPair>::Iterator sit2(src);
              while(sit2.hasNext()) {
                UIPair uip=sit2.next();
                FormulaList::push(uip.first, innerConj);
              }
	      FormulaList::push(new NegatedFormula(new JunctionFormula(AND, innerConj)), conj);
            } 
            else {
              ASS_EQ(st.inheritedColor, COLOR_RIGHT);
	      //u is justified by B
            }
            interpolant=new JunctionFormula(AND, conj);
          } 
          else {
	    //trivial interpolants (when there are no premises)
            if(st.inheritedColor==COLOR_LEFT) {
	      interpolant=unitFormula;
            }
            else {
              ASS_EQ(st.inheritedColor, COLOR_RIGHT);
	      interpolant=new NegatedFormula(unitFormula);
            }
          }
	  UIPair uip=make_pair(unitFormula, interpolant);
          if(st.inheritedColor==COLOR_LEFT) {
	    st.leftInts->destroy();
	    st.leftInts=0;
	    List<UIPair>::push(uip,st.leftInts);
          }
          else {
            ASS_EQ(st.inheritedColor, COLOR_RIGHT);
            st.rightInts->destroy();
            st.rightInts=0;
            List<UIPair>::push(uip,st.rightInts);
          }

        }
        if(sts.isNonEmpty()) {
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
      }
    } while(sts.isNonEmpty());
    if(sts.isEmpty()) {
      break;
    }

  }

}

}
