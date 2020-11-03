#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/Statistics.hpp"
#include "Lib/VirtualIterator.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)
using namespace Lib;

namespace Inferences {

PolynomialEvaluation::Result PolynomialEvaluation::simplifyLiteral(Literal* lit) 
{ 
  return _normalizer.evaluate(lit).unwrapOrElse([&](){return Result::literal(lit);}); 
}

PolynomialEvaluation::~PolynomialEvaluation() {}

PolynomialEvaluation::PolynomialEvaluation(Ordering& ordering) : SimplifyingGeneratingLiteralSimplification(InferenceRule::EVALUATION, ordering) {}



} // Inferences
