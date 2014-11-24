/**
 * @file Substitution.hpp
 * Defines class Substitution.
 *
 * @since 08/07/2007 Manchester, flight Manchester-Cork
 * @since 30/12/2007 Manchester, reimplemented from scratch using a skip list
 * like structure
 */

#ifndef __Substitution__
#define __Substitution__

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/VString.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;

/**
 * The class Substitution implementing substitutions.
 * @since 30/12/2007 Manchester
 */
class Substitution
{
public:
  Substitution() {}

  void bind(int v,Term* t);
  void bind(int v,TermList t);
  bool findBinding(int var, TermList& res) const;
  TermList apply(unsigned var);
  void unbind(int var);
  void reset();
#if VDEBUG
  vstring toString() const;
#endif
private:
  DHMap<unsigned,TermList> _map;
}; // class Substitution


}

#endif // __Substitution__

