/**
 * @file ArithmeticKB.hpp
 * Defines class ArithmeticKB.
 */

#ifndef __ArithmeticKB__
#define __ArithmeticKB__

#include "Forwards.hpp"

#include "Lib/Exception.hpp"

#include "Kernel/Theory.hpp"

namespace Kernel {
namespace Algebra {

class ArithmeticKB {
public:
  virtual bool isNonEqual(TermList t, InterpretedType val, Clause*& premise);
  virtual bool isGreater(TermList t, InterpretedType val, Clause*& premise);
  virtual bool isLess(TermList t, InterpretedType val, Clause*& premise);
};

}
}

#endif // __ArithmeticKB__
