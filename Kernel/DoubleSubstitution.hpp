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

#include "../Lib/Array.hpp"
#include "../Lib/DArray.hpp"
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
  bool unify(Literal* lit1,int index1,Literal* lit2,int index2);
  bool complementary(Literal* lit1,int index1,Literal* lit2,int index2);
  unsigned getVar(unsigned var,int index);
#if VDEBUG
  string toString() const;
#endif
private:
  void deref(TermList from,int indexFrom,TermList& to,int& indexTo); 

  /** structure storing the current binding */
  struct Binding
  {
    /** Timestamp when this variable was instantiated */
    unsigned timestamp;
    /** index of term to which it is bound */
    int index;
    /** term reference */
    TermList termref;
  };
  /** A substitution is a flexible-sized array of bindings.
   */
  class Subst
    : public Array<Binding>
  {
  public:
    Subst() { reset(); }
    virtual ~Subst();
    virtual void fillInterval(size_t start, size_t end);
    /** Reset all timestamps to 0 */
    void reset() { fillInterval(0,_capacity); }
  }; // class Subst

  /** Array of Subst */
  class SubstBank
    : public DArray<Subst>
  {
  public:
    /** Initialise and set the number of substitutions to 2 */
    SubstBank() : DArray<Subst>(2) {}
    void reset();
    ~SubstBank();
  };

  /** Get the binding for the variable @b var and index @b vindex */
  inline Binding& get(unsigned var,int vindex)
  {
    return _bank[vindex][var];
  }

  /** current timestamp */
  unsigned _timestamp;
  /** Array storing all substitutions */
  SubstBank _bank;
  /** next variable number when the substitution is applied */
  unsigned _nextVar;

  bool unify(TermList* ts1,int index1,TermList* ts2,int index2);
  bool occurs(unsigned v1,int index1,TermList* t2,int index2);
}; // class DoubleSubstitution


}

#endif // __DoubleSubstitution__

