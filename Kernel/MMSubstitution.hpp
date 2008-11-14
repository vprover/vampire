/**
 * @file MMSubstitution.hpp
 * Defines class MMSubstitution.
 *
 */

#ifndef __MMSubstitution__
#define __MMSubstitution__

#include "../Lib/DHMap.hpp"
#include "Term.hpp"

namespace Kernel
{

using namespace Lib;

class MMSubstitution
{
public:
  MMSubstitution() : _nextUnboundAvailable(0) {}
private:
  static const int AUX_INDEX=0x3FFFFFFD;
  static const int SPECIAL_INDEX=0x3FFFFFFE;
  static const int UNBOUND_INDEX=0x3FFFFFFF;
  
  struct TermSpec
  {
    /** Create a new VarSpec struct */
    TermSpec() {}
    /** Create a new VarSpec struct */
    TermSpec(TermList term, int index) : term(term), index(index) {}

    /** term reference */
    TermList term;
    /** index of term to which it is bound */
    int index;
  };
  /** Specifies instance of a variable (i.e. (variable, variable bank) pair) */
  struct VarSpec
  {
    /** Create a new VarSpec struct */
    VarSpec() {}
    /** Create a new VarSpec struct */
    VarSpec(unsigned var, int index) : var(var), index(index) {}

    bool operator==(const VarSpec& o) 
    { return var==o.var && index==o.index; }
    bool operator!=(const VarSpec& o) 
    { return !(*this==o); }

    /** number of variable */
    unsigned var;
    /** index of variable bank */
    int index;
    
    /** class containing first hash function for DHMap object storing variable banks */
    class Hash1
    {
    public:
      static unsigned hash(VarSpec& o, int capacity);
    };
    /** class containing second hash function for DHMap object storing variable banks */
    class Hash2
    {
    public:
      static unsigned hash(VarSpec& o);
    };
  };

  bool isUnbound(VarSpec v);
  TermSpec deref(VarSpec v);
  
  void bind(const VarSpec& v, const TermSpec& b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  VarSpec root(VarSpec v);
  void add(VarSpec v, TermSpec b);
  void associate(TermSpec t1, TermSpec t2);
  void makeEqual(VarSpec v1, VarSpec v2);

  unsigned getAuxVar(TermSpec target)
  {
    unsigned res=_nextAuxAvailable++;
    bind(VarSpec(res,AUX_INDEX), target);
  }
  
  DHMap<VarSpec,TermSpec> _bank;
  unsigned _nextUnboundAvailable;
  unsigned _nextAuxAvailable;
};


};

#endif /*__MMSubstitution__*/
