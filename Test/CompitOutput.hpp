/**
 * @file CompitOutput.hpp
 * Defines class CompitOutput for writing COMPIT benchmark files.
 */

#ifndef __CompitOutput__
#define __CompitOutput__

#include <string>

#include "../Forwards.hpp"

namespace Test {

using namespace std;
using namespace Kernel;

/**
 * Class for writing various data structures in the
 * Prolog format
 * @since 25/04/2008 flight Frankfurt-Vienna
 */
class CompitOutput
{
public:
  enum CompitOperation {
    INSERT,
    DELETE,
    SUCCESSFUL_QUERY,
    UNSUCCESSFUL_QUERY
  };

  static void print(CompitOperation op, TermList t);
  static void print(CompitOperation op, Literal* t, bool complementary=false);
private:
  static bool signaturePrinted;

  static void printSignature();
  static void printSignatureForLiterals();
  static char getPredSymbolChar(unsigned header);
  static char getFunctorChar(unsigned fn);
  static char getVarChar(unsigned var);

  static void fail();
};

}

#endif
