/**
 * @file Compit2Output.hpp
 * Defines class Compit2Output for writing COMPIT benchmark files.
 */

#ifndef __Compit2Output__
#define __Compit2Output__


#include "../Forwards.hpp"
#include "../compit2.hpp"

namespace Test {

using namespace std;
using namespace Kernel;

/**
 * Class for writing various data structures in the
 * Prolog format
 * @since 25/04/2008 flight Frankfurt-Vienna
 */
class Compit2Output
{
public:
  enum Operation {
    INSERT,
    DELETE,
    QUERY
  };

  static void print(Operation op, TermList t, unsigned resultCount=0);
  static void print(Operation op, Literal* t, unsigned resultCount=0, bool complementary=false);
private:
  static bool signaturePrinted;

  static void printSignature();
  static void printSignatureForLiterals();

  static WORD getFunctorRepr(unsigned fn);
  static WORD getPredSymbolRepr(unsigned header);
  static WORD getVarRepr(unsigned var);

  static size_t requiredSize(TermList t);
  static size_t requiredSize(Literal* lit);

  static void fail();
};

}

#endif
