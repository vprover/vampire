/**
 * @file Polynomial.hpp
 * Defines class Polynomial.
 */

#ifndef __Polynomial__
#define __Polynomial__

#include "../Forwards.hpp"

#include "../Lib/Stack.hpp"

#include "Term.hpp"
#include "Theory.hpp"

namespace Kernel {

using namespace Lib;

class Polynomial
{
public:
  Polynomial() {};
  Polynomial(TermList t);

  void subtract(Polynomial& pol);
  bool simplify();
  bool mergeSummands();

  bool reduceCoeffitients();
  bool negate();
  

  bool isProperLinearPolynomial();
  
  TermList toTerm();
private:
  struct Summand
  {
    Summand(InterpretedType coef) : coef(coef), constant(true) { term.makeEmpty(); }
    Summand(InterpretedType coef, TermList term) : coef(coef), constant(term.isEmpty()), term(term) {}
    
    TermList toTerm();
    
    InterpretedType coef;
    bool constant;
    TermList term;
  };
  
  typedef Stack<Summand> SummandStack;
  SummandStack _data;
};

}

#endif // __Polynomial__
