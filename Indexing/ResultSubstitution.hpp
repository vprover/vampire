/**
 * @file ResultSubstitution.hpp
 * Defines class ResultSubstitution.
 */


#ifndef __ResultSubstitution__
#define __ResultSubstitution__

#include "../Forwards.hpp"

#include "../Lib/SmartPtr.hpp"
#include "../Kernel/Term.hpp"


namespace Indexing {

using namespace Kernel;

/**
 * Represents a substitution, that has been retrieved from an
 * indexing structure.
 *
 * It distinguishes two classes of terms/literals --
 * query and result ones. Variables in query
 * terms/literals have the same meaning as variables in query
 * that was the indexing structure asked, and variables in
 * result terms/literals have the meaning of variables in the
 * term/literal that was retrieved from the index.
 */
class ResultSubstitution
{
public:
  virtual ~ResultSubstitution() {}
  virtual TermList applyToQuery(TermList t) { NOT_IMPLEMENTED; }
  virtual Literal* applyToQuery(Literal* l) { NOT_IMPLEMENTED; }
  virtual TermList applyToResult(TermList t) { NOT_IMPLEMENTED; }
  virtual Literal* applyToResult(Literal* l) { NOT_IMPLEMENTED; }

  template<typename T>
  T apply(T t, bool result)
  {
    if(result) {
      return applyToResult(t);
    } else {
      return applyToQuery(t);
    }
  }

  /**
   * Apply substitution to result term that fulfills the condition,
   * that all its variables are bound to some term of the query.
   *
   * Applying this substitution makes sense, when
   * @b isIdentityOnQueryWhenResultBound() method returns true,
   * as then there's no need to apply the substitution to any
   * query terms.
   */
  virtual TermList applyToBoundResult(TermList t)
  { return applyToResult(t); }

  /**
   * Return true if, when the substitution is applied to a result
   * term through @b applyToBoundResult method, the substitution
   * for query terms is identity.
   */
  virtual bool isIdentityOnQueryWhenResultBound() {return false;}

  virtual MMSubstitution* tryGetMMSubstitution() { return 0; }

  static ResultSubstitutionSP fromSubstitution(MMSubstitution* s,
	  int queryBank, int resultBank);
  static ResultSubstitutionSP fromSubstitution(RobSubstitution* s,
	  int queryBank, int resultBank);
};


class IdentitySubstitution
: public ResultSubstitution
{
public:
  TermList applyToQuery(TermList t) { return t; }
  Literal* applyToQuery(Literal* l) { return l; }
  TermList applyToResult(TermList t) { return t; }
  Literal* applyToResult(Literal* l) { return l; }
  bool isIdentityOnQueryWhenResultBound() {return true;}
};

};

#endif /* __ResultSubstitution__ */
