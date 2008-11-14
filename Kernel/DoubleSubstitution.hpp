/**
 * @file DoubleSubstitution.hpp
 * Defines class DoubleSubstitution
 *
 * @since 04/01/2008 flight Manchester-Murcia
 */

#ifndef __DoubleSubstitution__
#define __DoubleSubstitution__

#if VDEBUG
#  include <string>
using namespace std;
#endif

#include "../Lib/Forwards.hpp"
#include "../Lib/DHMap.hpp"
#include "Forwards.hpp"
#include "Term.hpp"

using namespace Lib;

namespace Kernel {

/**
 * The class DoubleSubstitution implementing indexed substitutions.
 * @since 04/01/2008 flight Manchester-Murcia
 */
class DoubleSubstitution
{
public:
  DoubleSubstitution()
    : _nextVar(0)
  {}

  void reset();
  void bind(unsigned v,int vindex,TermList ts,int tindex);
  void unbind(unsigned var,int index);
  Literal* apply(Literal* lit,int index);
  void apply(TermList* ts,int index,TermList& to);
  void apply(TermList& to, int index);
  bool unify(Literal* lit1,int index1,Literal* lit2,int index2);
  bool unifyTerms(TermList* ts1,int index1,TermList* ts2,int index2);
  bool complementary(Literal* lit1,int index1,Literal* lit2,int index2);
  unsigned getVar(unsigned var,int index);

  void backtrackableBind(unsigned v,int vindex,TermList ts,int tindex,BacktrackData& bd);
  bool backtrackableUnifyTerms(TermList ts1,int index1,TermList ts2,int index2,BacktrackData& bd);
  
#if VDEBUG
  string toString() const;
#endif
private:
  static const int UNBOUND_INDEX=0x3FFFFFFF;
  
  /** structure storing the current binding */
  struct Binding
  {
    /** index of term to which it is bound */
    int index;
    /** term reference */
    TermList termref;
  };
  /** Specifies instance of a variable (i.e. (variable, variable bank) pair) */
  struct VarSpec
  {
    /** Create a new VarSpec struct */
    VarSpec() {}
    /** Create a new VarSpec struct */
    VarSpec(unsigned var, int index) : var(var), index(index) {}

    inline
    bool operator==(const VarSpec& o) 
    {
      return var==o.var && index==o.index;
    }
    inline
    bool operator!=(const VarSpec& o) 
    {
      return !(*this==o);
    }
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

  void deref(TermList from,int indexFrom,TermList& to,int& indexTo); 
  bool getBinding(unsigned var,int vindex, Binding& result);

  /** type used to store variable banks */
  typedef DHMap<VarSpec,Binding,VarSpec::Hash1,VarSpec::Hash2> BankStorage;
  
  /** DHMap storing all substitutions */
  BankStorage _bank;
  
  /** next variable number when the substitution is applied */
  unsigned _nextVar;

  bool unify(TermList* ts1,int index1,TermList* ts2,int index2);
  bool occurs(unsigned v1,int index1,TermList* t2,int index2);

  class BindBacktrackObject: public BacktrackObject {
  public:
    BindBacktrackObject(DoubleSubstitution* ds, unsigned v,int vindex)
    : ds(ds), varSpec(v,vindex) {}
    void backtrack() { ds->unbind(varSpec.var, varSpec.index); }
  private:
    DoubleSubstitution* ds;
    VarSpec varSpec;
  };
  
  bool backtrackableUnify(TermList* ts1,int index1,TermList* ts2,int index2, BacktrackData& bd);
}; // class DoubleSubstitution


}

namespace Lib 
{
/**
 * Traits structure specialisation. (See DHMap.hpp) 
 */
template<>
struct HashTraits<Kernel::DoubleSubstitution::VarSpec::Hash1>
{
  enum {SINGLE_PARAM_HASH=0};
};
};


#endif // __DoubleSubstitution__

