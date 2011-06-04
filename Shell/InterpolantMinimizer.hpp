/**
 * @file InterpolantMinimizer.hpp
 * Defines class InterpolantMinimizer.
 */

#ifndef __InterpolantMinimizer__
#define __InterpolantMinimizer__

#include "Lib/DHSet.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/InferenceStore.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

struct PropFormula__HalfImpl;
struct PropFormula__HalfEquiv;

class PropFormula
{
  PropFormula(string val) : _val(val) {}
public:
  static PropFormula getTrue() { return PropFormula("true"); }
  static PropFormula getFalse() { return PropFormula("false"); }
  static PropFormula name(string name) { return PropFormula(name); }
  static PropFormula name(string n1, string n2) { return PropFormula(n1 + "_" + n2); }

  operator string() const { return _val; }

  PropFormula operator!() const
  { return PropFormula("(not " + _val + ")"); }

  PropFormula operator&(const PropFormula& f) const
  { return PropFormula("(and " + _val + ", " + f._val + ")"); }

  PropFormula operator|(const PropFormula& f) const
  { return PropFormula("(or " + _val + ", " + f._val + ")"); }


  PropFormula__HalfImpl operator--(int) const;

  PropFormula__HalfEquiv operator-() const;
  PropFormula operator-=(const PropFormula__HalfEquiv& r) const;

private:
  friend class PropFormula__HalfImpl;
  friend class PropFormula__HalfEquiv;

  string _val;
};

//the following is to allow having --> stand for an implication
struct PropFormula__HalfImpl {
  PropFormula operator>(const PropFormula& r) const
  { return PropFormula("(=> " + pf._val + ", " + r._val + ")"); }
private:
  friend class PropFormula;
  PropFormula__HalfImpl(const PropFormula& pf) : pf(pf) {}
  PropFormula pf;
};
PropFormula__HalfImpl PropFormula::operator--(int) const { return PropFormula__HalfImpl(*this); }

//the following is to allow having -=- stand for an equivalence
struct PropFormula__HalfEquiv {
private:
  friend class PropFormula;
  PropFormula__HalfEquiv(const PropFormula& pf) : pf(pf) {}
  PropFormula pf;
};

PropFormula__HalfEquiv PropFormula::operator-() const { return PropFormula__HalfEquiv(*this); }
PropFormula PropFormula::operator-=(const PropFormula__HalfEquiv& r) const
{ return PropFormula("(= " + _val + ", " + r.pf._val + ")"); }



class InterpolantMinimizer
{
public:
  typedef InferenceStore::UnitSpec UnitSpec;


private:

  void traverse(Clause* refutation);

  struct TraverseStackEntry;

  enum UnitState {
    TRANSPARENT_PARENTS,
    HAS_LEFT_PARENT,
    HAS_RIGHT_PARENT
  };

  struct UnitInfo
  {
    UnitInfo() : state(TRANSPARENT_PARENTS), isRefutation(false),
	isParentOfLeft(false), isParentOfRight(false), leadsToColor(false) {}

    Color color;

    UnitState state;

    bool isRefutation;
    bool isParentOfLeft;
    bool isParentOfRight;

    /** True if unit has some non-transparent ancestor (doesn't need to be immediate) */
    bool leadsToColor;
  };

//  PropFormula

//  Unit* _refutation;
//
//  /** Either the refutation, or transparent units used as premise for a non */
//  Stack<Unit*> redSeeds;

//  MapToLIFO<UnitSpec,UnitSpec> _parents;
  DHMap<UnitSpec,UnitInfo> _infos;

private:
  //here is the code related to generating the SMT problem

  struct ParentSummary
  {
    Stack<string> rParents;
    Stack<string> bParents;
    Stack<string> gParents;
  };

  enum PredType
  {
    R, B, G, S, D
  };

  static PropFormula pred(PredType t, string node);

  PropFormula distinctColorsFormula(string n);

  PropFormula gNodePropertiesFormula(string n, ParentSummary& parents);
  PropFormula coloredParentPropertiesFormula(string n, ParentSummary& parents);
};

}

#endif // __InterpolantMinimizer__
