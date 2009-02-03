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

class ResultSubstitution
{
public:
  virtual ~ResultSubstitution() {}
  virtual TermList applyToQuery(TermList t) = 0;
  virtual Literal* applyToQuery(Literal* l) = 0;
  virtual TermList applyToResult(TermList t) = 0;
  virtual Literal* applyToResult(Literal* l) = 0;

  template<typename T>
  T apply(T t, bool result)
  {
    if(result) {
      return applyToResult(t);
    } else {
      return applyToQuery(t);
    }
  }

  virtual bool isIdentityOnQuery() {return false;}
  virtual bool isIdentityOnResult() {return false;}
  virtual MMSubstitution* tryGetMMSubstitution() { return 0; }

  static ResultSubstitutionSP fromMMSubstitution(MMSubstitution* s,
	  int queryBank, int resultBank);
};

};

#endif /* __ResultSubstitution__ */
