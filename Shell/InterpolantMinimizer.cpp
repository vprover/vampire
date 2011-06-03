/**
 * @file InterpolantMinimizer
 * Implements class InterpolantMinimizer.
 */

#include "Kernel/Inference.hpp"

#include "InterpolantMinimizer.hpp"

namespace Shell
{

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
