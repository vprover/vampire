/**
 * @file Output.hpp
 * Defines class Output for writing various data structures in the
 * Prolog format
 * @since 25/04/2008 flight Frankfurt-Vienna
 */

#ifndef __Output__
#define __Output__

#include <string>

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
  static string toString(const Term* t);
  static string toString(const Literal* l);
  static string toString(const TermList* ts);
  static string toString(const Clause* c);

  /** Convert only the first item of a term list to string */
  static string singleTermListToString(TermList ts)
  {
    TermList aux[2];
    aux[0].makeEmpty();
    aux[1]=ts;
    return Test::Output::toString(&aux[1]);
  }

};

}

#endif
