/**
 * @file Polynomial.hpp
 * Defines class Polynomial.
 */

#ifndef __Polynomial__
#define __Polynomial__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"

namespace Kernel {
namespace Algebra {

#if 0

using namespace Lib;

class Polynomial
{
public:
  struct Summand
  {
    Summand(InterpretedType coef) : coef(coef) { term.makeEmpty(); }
    Summand(InterpretedType coef, TermList term) : coef(coef), term(term) {}

    TermList toTerm();

    static Comparison compare(const Summand& s1, const Summand& s2);

    bool constant() const { return term.isEmpty(); }

    InterpretedType coef;
    TermList term;
  };

  Polynomial() {};
  Polynomial(TermList t);

  void init(TermList t);
  void reset();

  CLASS_NAME("Polynomial");
  USE_ALLOCATOR(Polynomial);

  size_t size() const { return _data.size(); }
  Summand& operator[](size_t i) { return _data[i]; }


  void subtract(Polynomial& pol);
  bool simplify();
  bool mergeSummands();

  bool reduceCoeffitients();
  bool negate();

  void removeSingletonTerm(TermList trm);

  bool getMaximalCoefOneConstant(bool& positive, TermList& trm);
  bool isProperLinearPolynomial();

  TermList toTerm();
private:
  
  typedef Stack<Summand> SummandStack;
  SummandStack _data;
};

#endif

}
}

#endif // __Polynomial__
