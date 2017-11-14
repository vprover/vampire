
/*
 * File SubsumptionRemover.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file SubsumptionRemover.cpp
 * Implements class SubsumptionRemover.
 */
#if GNUMP

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Map.hpp"

#include "Kernel/Constraint.hpp"

#include "Statistics.hpp"

#include "SubsumptionRemover.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

struct SubsumptionRemover::CoeffArrayHash
{
  static unsigned hash(const Constraint::CoeffArray* ca)
  {
    CALL("SubsumptionRemover::CoeffArrayHash::hash");
    return ContainerHash<Constraint::Coeff>::hash(*ca);
  }
  static bool equals(const Constraint::CoeffArray* ca1, const Constraint::CoeffArray* ca2)
  {
    CALL("SubsumptionRemover::CoeffArrayHash::equal");
    if(ca1->size()!=ca2->size()) { return false; }
    size_t sz = ca1->size();
    for(size_t i=0; i!=sz; i++) {
      if((*ca1)[i].var!=(*ca2)[i].var) { return false; }
    }
    for(size_t i=0; i!=sz; i++) {
      if((*ca1)[i].value!=(*ca2)[i].value) { return false; }
    }
    return true;
  }

};

bool SubsumptionRemover::apply(ConstraintRCList*& lst)
{
  CALL("SubsumptionRemover::apply");

  typedef Map<const Constraint::CoeffArray*, Constraint*, CoeffArrayHash> CoeffsMap;

  CoeffsMap map;

  ConstraintRCList* pinned = 0;

  ConstraintRCList::Iterator cit(lst);
  while(cit.hasNext()) {
    Constraint* c = cit.next().ptr();

    Constraint** prevConstr;
    if(!map.getValuePtr(&c->coeffArray(), prevConstr, c)) {
      ASS(*prevConstr);
      if(firstIsSubsumed(**prevConstr, *c)) {
	*prevConstr = c;
      }
    }
    else {
      //Part of the constraint is referred to by a key in the map -- we do not want
      //it to be deleted too early.
      ConstraintRCList::push(ConstraintRCPtr(c), pinned);
    }
  }

  bool someRemoved = false;
  ConstraintRCList::DelIterator dcit(lst);
  while(dcit.hasNext()) {
    Constraint* c = dcit.next().ptr();

    if(map.get(&c->coeffArray())!=c) {
      dcit.del();
      someRemoved = true;
      env.statistics->subsumedConstraints++;
    }
  }
  pinned->destroy();
  return someRemoved;
}

bool SubsumptionRemover::firstIsSubsumed(Constraint& c1, Constraint& c2)
{
  CALL("SubsumptionRemover::firstIsSubsumed");
  ASS(c1.coeffArray()==c2.coeffArray());

  if(c1.freeCoeff()>c2.freeCoeff()) {
    return false;
  }
  if(c1==c2) {
    return c1.type()==CT_GREQ && c2.type()==CT_GR;
  }
  ASS_L(c1.freeCoeff(),c2.freeCoeff());
  return true;
}

}
#endif //GNUMP
