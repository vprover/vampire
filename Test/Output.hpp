/**
 * @file Output.hpp
 * Defines class Output for writing various data structures in the
 * Prolog format
 * @since 25/04/2008 flight Frankfurt-Vienna
 */

#ifndef __Output__
#define __Output__

#include "Lib/VString.hpp"

#include "Forwards.hpp"

namespace Test {

using namespace std;
using namespace Kernel;

/**
 * Class for writing various data structures in the
 * Prolog format
 * @since 25/04/2008 flight Frankfurt-Vienna
 */
class Output
{
public:
  static vstring toString(const Term* t);
  static vstring toString(const Literal* l);
  static vstring toString(const TermList* ts);
  static vstring toString(const Clause* c);

  /** Convert only the first item of a term list to string */
  static vstring singleTermListToString(TermList ts)
  {
    TermList aux[2];
    aux[0].makeEmpty();
    aux[1]=ts;
    return Test::Output::toString(&aux[1]);
  }

};

}

#endif
