/**
 * @file EqResWithDeletion.hpp
 * Defines class EqResWithDeletion.
 */


#ifndef __Shell_EqResWithDeletion__
#define __Shell_EqResWithDeletion__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Term.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class EqResWithDeletion
{
public:
  void apply(UnitList*& units);

  TermList apply(unsigned var);
  Clause* apply(Clause* cl);
private:
  bool scan(Literal* lit);



  /** The substitution induced by resolved inequalities
   * (It is reset with each clause). */
  DHMap<unsigned, TermList, IdentityHash> _subst;
};

};

#endif /* __Shell_EqResWithDeletion__ */
