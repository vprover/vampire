
/*
 * File InterpretedLiteralEvaluator.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file InterpretedLiteralEvaluator.hpp
 * Defines class InterpretedLiteralEvaluator.
 */

#ifndef __InterpretedLiteralEvaluator__
#define __InterpretedLiteralEvaluator__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Stack.hpp"

#include "TermTransformer.hpp"
#include "Theory.hpp"
#include "Lib/Coproduct.hpp"
#include "Shell/Options.hpp"

namespace Kernel {

class InterpretedLiteralEvaluator
  :  private TermTransformerTransformTransformed 
{
public:
  CLASS_NAME(InterpretedLiteralEvaluator);
  USE_ALLOCATOR(InterpretedLiteralEvaluator);
  
  InterpretedLiteralEvaluator(bool doNormalize = true);
  ~InterpretedLiteralEvaluator();

  bool evaluate(Literal* lit, bool& isConstant, Literal*& resLit, bool& resConst,Stack<Literal*>& sideConditions);
  TermList evaluate(TermList);
protected:
  class Evaluator;
  class EqualityEvaluator;
  class ConversionEvaluator;
  template<class T> class ACFunEvaluator;
  template<class T> class PolynomialNormalizer;
  template<class T> class InequalityNormalizer;
  template<class T> class TypedEvaluator;
  class IntEvaluator;
  class RatEvaluator;
  class RealEvaluator;

  typedef Stack<Evaluator*> EvalStack;
  virtual TermList transformSubterm(TermList trm);
  Evaluator* getFuncEvaluator(unsigned func);
  Evaluator* getPredEvaluator(unsigned pred);
  EvalStack _evals;
  DArray<Evaluator*> _funEvaluators;
  DArray<Evaluator*> _predEvaluators;

  bool balancable(Literal* lit);
  bool balance(Literal* lit,Literal*& res,Stack<Literal*>& sideConditions);
  
  // take AplusB, A and C and let result=C-B, AplusB might actually be BplusA
  bool balancePlus(Interpretation plus, Interpretation unaryMinus, Term* AplusB, TermList* A, TermList C, TermList& result);

  // take AmultiplyB, A and C and let result=C/B if B!=0, AmultiplyB might actually be BmultiplyA
  // rat and real versions only
  // note when using this we might need to add a side condition that B is positive if this is under lesseq, or B is negative if we switch the polarity
  template<typename ConstantType>
  bool balanceMultiply(Interpretation divide,ConstantType zero,             
                       Term* AmultiplyB, TermList* A, TermList C, TermList& result,
                       bool& swap, Stack<Literal*>& sideConditions);

  bool balanceIntegerMultiply(
                                                  Term* AmultiplyB, TermList* A, TermList C, TermList& result,
                                                  bool& swap, Stack<Literal*>& sideConditions);

  // take AoverB, A and C and let result=C*B, AoverB must be that way round
  // ignore the case of BoverA for now
  // rat and real versions only
  // like above, need to consider polairty of B
  bool balanceDivide(Interpretation multiply, 
                       Term* AmultiplyB, TermList* A, TermList C, TermList& result, bool& swap, Stack<Literal*>& sideConditions);
  
private:
  template<class Fn>
  Evaluator* getEvaluator(unsigned func, DArray<Evaluator*>& evaluators, Fn canEval);
  const bool _normalize;
};

// struct AnyPoly;
// using TermEvalResult = Lib::Either<TermList, AnyPoly>;
// struct NewEvaluator {
//
// public:
//   LitEvalResult evaluate(Literal* in) const;
//   TermList evaluate(TermList in) const;
//   TermList evaluate(Term* in) const;
//
// private:
//   struct RecursionState;
//   LitEvalResult evaluateStep(Literal* in) const;
//
//   TermEvalResult evaluateStep(Term* orig, TermEvalResult* evaluatedArgs) const;
//
//   template<Theory::Interpretation inter>
//   LitEvalResult evaluateLit(Literal* lit) const;
//
//   template<Theory::Interpretation inter>
//   TermEvalResult evaluateFun(Term* orig, TermEvalResult* evaluatedArgs) const;
//
//   // template<class number>
//   // TermEvalResult evaluateConst(typename number::ConstantType c) const;
//
//   template<class CommutativeMonoid>
//   TermEvalResult evaluateCommutativeMonoid(Term* orig, TermEvalResult* evaluatedArgs) const;
//
//   template<class ConstantType, class EvalIneq> 
//   LitEvalResult evaluateInequality(Literal* lit, bool strict, EvalIneq evalIneq) const;
//
//   template<class ConstantType, class EvalGround>
//   LitEvalResult tryEvalConstant1(Literal* lit, EvalGround fun) const;
//
//   template<class ConstantType, class EvalGround>
//   LitEvalResult tryEvalConstant2(Literal* lit, EvalGround fun) const;
//
//   template<class ConstantType, class EvalGround>
//   TermEvalResult tryEvalConstant1(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) const;
//
//   template<class ConstantType, class EvalGround>
//   TermEvalResult tryEvalConstant2(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) const;
// };
// }
//
// #endif // __InterpretedLiteralEvaluator__

}
#endif // __InterpretedLiteralEvaluator__
