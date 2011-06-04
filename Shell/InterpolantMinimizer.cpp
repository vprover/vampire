/**
 * @file InterpolantMinimizer
 * Implements class InterpolantMinimizer.
 */

#include "Kernel/Inference.hpp"

#include "InterpolantMinimizer.hpp"

namespace Shell
{

PropFormula InterpolantMinimizer::pred(PredType t, string node)
{
  CALL("InterpolantMinimizer::pred");

  string n1;
  switch(t) {
  case R: n1 = "r"; break;
  case B: n1 = "b"; break;
  case G: n1 = "g"; break;
  case S: n1 = "s"; break;
  case D: n1 = "d"; break;
  default: ASSERTION_VIOLATION;
  }
  return PropFormula::name(n1, node);
}

PropFormula InterpolantMinimizer::distinctColorsFormula(string n)
{
  CALL("InterpolantMinimizer::distinctColorsFormula");

  PropFormula rN = pred(R, n);
  PropFormula bN = pred(B, n);
  PropFormula gN = pred(G, n);

  PropFormula res = bN | rN | gN;
  res = res & ( rN --> ((!bN) & (!gN)) );
  res = res & ( bN --> ((!rN) & (!gN)) );
  res = res & ( gN --> ((!rN) & (!bN)) );
  return res;
}

PropFormula InterpolantMinimizer::gNodePropertiesFormula(string n, ParentSummary& parents)
{
  CALL("InterpolantMinimizer::gNodePropertiesFormula");
  ASS(parents.rParents.isEmpty());
  ASS(parents.bParents.isEmpty());

  PropFormula rParDisj = PropFormula::getFalse();
  PropFormula bParDisj = PropFormula::getFalse();
  PropFormula gParConj = PropFormula::getTrue();

  Stack<string>::Iterator pit(parents.gParents);
  while(pit.hasNext()) {
    string par = pit.next();
    rParDisj = rParDisj | pred(R, par);
    bParDisj = bParDisj | pred(B, par);
    gParConj = gParConj & pred(G, par);
  }

  PropFormula rN = pred(R, n);
  PropFormula bN = pred(B, n);
  PropFormula gN = pred(G, n);
  PropFormula sN = pred(S, n);
  PropFormula dN = pred(D, n);

  PropFormula res = (sN & rParDisj)-->rN;
  res = res & ((sN & bParDisj)-->bN);
  res = res & ((sN & gParConj)-->gN);
  res = res & ( (!sN)-->gN );
  res = res & ( dN -=- ( (!sN) & !gParConj ) );
  return res;
}

PropFormula InterpolantMinimizer::coloredParentPropertiesFormula(string n, ParentSummary& parents)
{
  CALL("InterpolantMinimizer::coloredParentPropertiesFormula");
  ASS(parents.rParents.isNonEmpty()^parents.bParents.isNonEmpty());

  PredType parentType = parents.rParents.isNonEmpty() ? R : B;
  PredType oppositeType = (parentType==R) ? B : R;

  Stack<string>::Iterator gParIt(parents.gParents);

  PropFormula gParNegConj = PropFormula::getTrue();
  while(gParIt.hasNext()) {
    string par = gParIt.next();
    gParNegConj = gParNegConj & !pred(oppositeType, par);
  }

  PropFormula parN = pred(parentType, n);
  PropFormula gN = pred(G, n);
  PropFormula sN = pred(S, n);
  PropFormula dN = pred(D, n);

  PropFormula res = gParNegConj;
  res = res & (sN --> parN);
  res = res & ((!sN) --> gN);
  res = res & (dN -=- !sN);
  return res;
}

/////////////////////////
// Proof tree traversal
//

struct InterpolantMinimizer::TraverseStackEntry
{
  TraverseStackEntry(InterpolantMinimizer& im, UnitSpec u) : unit(u), _im(im)
  {
    CALL("InterpolantMinimizer::TraverseStackEntry::TraverseStackEntry");

    parentIterator = InferenceStore::instance()->getParents(u);

    //we don't create stack entries for already visited units,
    //so we must always be able to insert
    ALWAYS(im._infos.insert(unit, UnitInfo()));
    UnitInfo& info = getInfo();

    info.color = u.unit()->getColor();
    info.leadsToColor = info.color!=COLOR_TRANSPARENT;
  }

  void processParent(UnitSpec parent)
  {
    CALL("InterpolantMinimizer::TraverseStackEntry::processParent");

    UnitInfo& info = getInfo();

    Color pcol = parent.unit()->getColor();
    if(pcol==COLOR_LEFT) {
      ASS_NEQ(info.state, HAS_RIGHT_PARENT);
      info.state = HAS_LEFT_PARENT;
    }
    if(pcol==COLOR_RIGHT) {
      ASS_NEQ(info.state, HAS_LEFT_PARENT);
      info.state = HAS_RIGHT_PARENT;
    }

    UnitInfo& parInfo = _im._infos.get(parent);
    info.leadsToColor |= parInfo.leadsToColor;

    if(info.color==COLOR_LEFT) {
      parInfo.isParentOfLeft = true;
    }
    if(info.color==COLOR_RIGHT) {
      parInfo.isParentOfRight = true;
    }
  }

  /**
   * The returned reference is valid only before updating
   * InterpolantMinimizer::_infos
   */
  UnitInfo& getInfo()
  {
    return _im._infos.get(unit);
  }

  UnitSpec unit;
  VirtualIterator<UnitSpec> parentIterator;

  InterpolantMinimizer& _im;
};

void InterpolantMinimizer::traverse(Clause* refutationClause)
{
  CALL("InterpolantMinimizer::traverse");

  UnitSpec refutation=UnitSpec(refutationClause, refutationClause->prop());

  static Stack<TraverseStackEntry> stack;
  stack.reset();

  stack.push(TraverseStackEntry(*this, refutation));
  stack.top().getInfo().isRefutation = true;
  while(stack.isNonEmpty()) {
    TraverseStackEntry& top = stack.top();
    if(top.parentIterator.hasNext()) {
      UnitSpec parent = top.parentIterator.next();

      if(!_infos.find(parent)) {
	stack.push(TraverseStackEntry(*this, parent));
      }
      else {
	top.processParent(parent);
      }
    }
    else {
      if(stack.size()>1){
	TraverseStackEntry& child = stack[stack.size()-2];
	child.processParent(stack.top().unit);
      }
      stack.pop();
    }
  }

}



}
