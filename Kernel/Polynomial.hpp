/**
 * @file Polynomial.hpp
 * Defines class Polynomial.
 */

#ifndef __Polynomial__
#define __Polynomial__

#include "Forwards.hpp"

#include "Lib/Comparison.hpp"
#include "Lib/Stack.hpp"

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

  void removeSingletonTerm(TermList trm);

  bool getMaximalCoefOneConstant(bool& positive, TermList& trm);
  bool isProperLinearPolynomial();

  void sort();
  
  TermList toTerm();
private:
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
  
  typedef Stack<Summand> SummandStack;
  SummandStack _data;
};

}

#endif // __Polynomial__
