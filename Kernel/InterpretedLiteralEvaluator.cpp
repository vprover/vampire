
/*
 * File InterpretedLiteralEvaluator.cpp.
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
 * @file InterpretedLiteralEvaluator.cpp
 * Implements class InterpretedLiteralEvaluator.
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Signature.hpp" 
#include "SortHelper.hpp"
#include "Sorts.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "num_traits.hpp"
#include "Debug/Tracer.hpp"
#include <algorithm>


#include "InterpretedLiteralEvaluator.hpp"

#if VDEBUG
// #define IDEBUG 0
#define IDEBUG 1
#else 
#define IDEBUG 0
#endif

#define _DEBUG(...) 
#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Kernel
{
using namespace Lib;

struct PredEvalResult {
  enum {
    Simplified,
    Trivial,
    Nop,
  } status;
  union {
    bool trivial_val;
    Literal* simplified_val;
  };
  static PredEvalResult nop() {return  PredEvalResult {.status = Nop}; }
  static PredEvalResult trivial(bool value) {return  PredEvalResult {.status = Trivial, .trivial_val = value}; }
  static PredEvalResult simplified(Literal* value) {return  PredEvalResult {.status = Simplified, .simplified_val = value}; }
};

/**
 * We use descendants of this class to evaluate various functions.
 *
 * One function can be evaluated only by one Evaluator object.
 */
class InterpretedLiteralEvaluator::Evaluator
{
public:
  CLASS_NAME(InterpretedLiteralEvaluator::Evaluator);
  USE_ALLOCATOR(InterpretedLiteralEvaluator::Evaluator);
  
  virtual ~Evaluator() {}

  virtual bool canEvaluateFunc(unsigned func) { return false; }
  virtual bool canEvaluatePred(unsigned pred) { return false; }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res) { return false; }
  virtual PredEvalResult tryEvaluatePred(Literal* trm)  { return PredEvalResult::nop(); }
};

  /* Traverses the given term. Only the subtree parts where pred is true are traversed.
   * For every traversed term where pred is *not* true, action is applied.
   *
   * The argument functions shall have the following signatures:
   * bool pred(const Term&)
   * void action(TermList)
   */
template<class Fn, class Predicate> 
void stackTraverseIf(TermList term, Predicate pred, Fn action) {

  Stack<TermList> todo;
  todo.push(term);

  while(!todo.isEmpty()){
    TermList t = todo.pop();
    if(t.isTerm()) {
      auto& trm = *t.term();
      if (pred(trm)) {
        for (auto i = 0; i < trm.arity(); i++) {
          todo.push(trm[i]);
        }
      } else {
        action(t);
      }
    } else {
      action(t);
    }
  }
}

struct TermTraverser {
    struct Node {
      Term* term;
      unsigned idx;
    };

    Node _cur;
    Stack<Node> _stack;

    bool inBounds() const {
      return _cur.idx < _cur.term->arity();
    }

  public:

    TermList operator*() const {
      return *_cur.term->nthArgument(_cur.idx);
    }

    void operator++() {
      _cur.idx++;
      while(!inBounds()) {
        if (_stack.isEmpty()) return;
        _cur = _stack.pop();
      }
    }

    void push() {
      ASS(inBounds())
      auto _new_term = (**this);
      ASS(_new_term.isTerm())
      auto new_term = _new_term.term();
      ASS(new_term->arity() > 0)
      _cur.idx++;
      _stack.push(_cur);
      _cur.term = new_term;
      _cur.idx = 0;
    }

    bool hasNext() const {
      return !_stack.isEmpty() || inBounds();
    }
};


// /**
//  * TODO document
//  *
//  * @author joe-hauns
//  * @since 12/05/20
//  */
// template<class ConstantType>
// class InterpretedLiteralEvaluator::PolynomialNormalizer
//    : public Evaluator
// {
// public:
// CLASS_NAME(InterpretedLiteralEvaluator::ACFunEvaluator<ConstantType>);
//   USE_ALLOCATOR(InterpretedLiteralEvaluator::ACFunEvaluator<ConstantType>);
//
//   using number = num_traits<ConstantType>;
//
//   PolynomialNormalizer() : _addF(number::addF()) { }
//   const unsigned _addF; 
//
//   virtual bool canEvaluateFunc(unsigned func) { return func == _addF; }
//
//   virtual bool tryEvaluateFunc(Term* trm, TermList& res) { 
//     CALL( "ACFunEvaluator::tryEvaluateFunc()" );
//     ASS_EQ(trm->functor(), _fun);
//     ASS_EQ(trm->arity(),2);
//
//     ConstantType acc = ConstantType::zero;
//     Stack<TermList> keep;
//     stackTraverseIf(TermList(trm), 
//         /* we traverse only the parts with the same operation */
//         [&](Term& t){ return t.functor() == _fun; },
//         [&](TermList t) {
//           ConstantType c;
//           /* we eval constant parts */
//           if (t.isTerm() && theory->tryInterpretConstant(t.term(), c)) {
//             acc = CommutativeMonoid::groundEval(acc, c);
//           } else {
//             keep.push(t);
//           }
//         });
//
//     if (acc != CommutativeMonoid::IDENTITY) {
//       keep.push(TermList(theory->representConstant(acc)));
//     }
//
//     auto iter = Stack<TermList>::Iterator(keep);
//     if (!iter.hasNext()) {
//       res = TermList(theory->representConstant(CommutativeMonoid::IDENTITY));
//       return TermList(trm) != res;
//     } else {
//       TermList out = iter.next();
//       while (iter.hasNext()) {
//         auto t = iter.next();
//         out = TermList(Term::create2(_fun, out, t));
//       }
//       res = out;
//       return TermList(trm) != res;
//     }
//   }
// };


/**
 * We want to smplify terms that are interpred by commutative monoids. e.g. (1+a)+1 -> 2 + a ... 
 * the standard evaluation will not do this. 
 *
 * Additionally evaluator has a weekly normalizing behaviour. Namely it re-brackets sums, such that the lhs 
 * of the operation is always a non-operator term. Further all interpreted constants will be collapsed into 
 * the 'left-most' term. The left most term is ommited if it is the identity element.
 *
 * x + ( y + ( t + 4 ) + r ) + 5  ==> ( ( (9 + x) + y ) + t ) + r
 * x + ( y + 0 )                  ==> x + y
 *
 * (The name of this class comes from the Associative Commutative operation of the Monoid)
 *
 * @author Giles (refactorings by joe-hauns)
 * @since 06/12/18
 */
template<class CommutativeMonoid>
class InterpretedLiteralEvaluator::ACFunEvaluator
   : public Evaluator
{
public:
CLASS_NAME(InterpretedLiteralEvaluator::ACFunEvaluator<CommutativeMonoid>);
  USE_ALLOCATOR(InterpretedLiteralEvaluator::ACFunEvaluator<CommutativeMonoid>);

  using ConstantType = typename CommutativeMonoid::ConstantType;

  ACFunEvaluator() : _fun(env.signature->getInterpretingSymbol(CommutativeMonoid::interpreation)) { }
  const unsigned _fun; 

  virtual bool canEvaluateFunc(unsigned func) { return func == _fun; }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res) { 
    CALL( "ACFunEvaluator::tryEvaluateFunc()" );
    ASS_EQ(trm->functor(), _fun);
    ASS_EQ(trm->arity(),2);

    ConstantType acc = CommutativeMonoid::IDENTITY;
    Stack<TermList> keep;
    stackTraverseIf(TermList(trm), 
        /* we traverse only the parts with the same operation */
        [&](Term& t){ return t.functor() == _fun; },
        [&](TermList t) {
          ConstantType c;
          /* we eval constant parts */
          if (t.isTerm() && theory->tryInterpretConstant(t.term(), c)) {
            acc = CommutativeMonoid::groundEval(acc, c);
          } else {
            keep.push(t);
          }
        });

    if (acc != CommutativeMonoid::IDENTITY) {
      keep.push(TermList(theory->representConstant(acc)));
    }

    auto iter = Stack<TermList>::Iterator(keep);
    if (!iter.hasNext()) {
      res = TermList(theory->representConstant(CommutativeMonoid::IDENTITY));
      return TermList(trm) != res;
    } else {
      TermList out = iter.next();
      while (iter.hasNext()) {
        auto t = iter.next();
        out = TermList(Term::create2(_fun, out, t));
      }
      res = out;
      return TermList(trm) != res;
    }
  }
};

template<class Inequality>
class InequalityNormalizer {

public:
  static Literal* normalize(Literal* in) {
    CALL("IntLess::normalize");
    ASS(in->functor() == Inequality::functor());

    if (Inequality::isNormalized(in)) {
      /* nothing to do */
      return in;
    } else {
      return Inequality::normalizedLit(
          in->polarity(),
          *in->nthArgument(0), 
          *in->nthArgument(1));
    }
  }

};

template<class ConstantType>
class FracLess { 
  template<class Inequality> friend class InequalityNormalizer;

  using number = num_traits<ConstantType>;
  inline static unsigned functor() { return number::lessF(); }

  static Literal* normalizedLit(bool polarity, TermList lhs, TermList rhs) {
    static auto zero = TermList(number::zeroT());
    return number::less(
              polarity,
              zero,
              number::add(rhs, number::minus(lhs)));
  }

  inline static bool isNormalized(Literal* in) {
    return number::isZero(*in->nthArgument(0));
  }

}; 


class IntLess { 
  template<class Inequality> friend class InequalityNormalizer;

  using number = num_traits<IntegerConstantType>;
  inline static unsigned functor() { return number::lessF(); }

  static Literal* normalizedLit(bool polarity, TermList lhs, TermList rhs) {
    static auto one  = TermList(number::oneT());
    static auto zero = TermList(number::zeroT());
    if (polarity) {
      return number::less(
              /* polarity */ true, 
              zero,
              number::add(rhs, number::minus(lhs)));
    } else {
      /* ~(l < r) ==> (r <= l) ==> r - 1 < l ==> 0 < l - r + 1 */
      return number::less(
              /* polarity */ true, 
              zero,
              number::add(number::add(lhs, one), number::minus(rhs)));
    }
  }

  inline static bool isNormalized(Literal* in) {
    return number::isZero(*in->nthArgument(0)) && in->polarity();
  }

}; 


/**
 * Interpreted equality has to be treated specially. We do not have separate
 * predicate symbols for different kinds of equality so the sorts must be 
 * detected and the correct intepretation of constants carried out.
 *
 * Equality is only decided between constant terms.
 *
 * @author Giles
 * @since 10/11/14
 */
class InterpretedLiteralEvaluator::EqualityEvaluator
  : public Evaluator
{
  bool canEvaluatePred(unsigned pred) override {
    return Signature::isEqualityPredicate(pred);
  }

  template<typename T>
  bool checkEquality(Literal* lit, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::EqualityEvaluator::checkEquality");
    T arg1;
    if(!theory->tryInterpretConstant(lit->nthArgument(0)->term(),arg1)){ 
      return false; 
    }
    T arg2;
    if(!theory->tryInterpretConstant(lit->nthArgument(1)->term(),arg2)){ 
      return false;
    }

    res = (arg1 == arg2);

    return true;
  }

  /** is to be called when interpreted functions were already evaluated */
  PredEvalResult tryEvaluatePred(Literal* lit_) override
  {
    auto& lit = *lit_;
    ASS(lit.isEquality());
    TermList l = lit[0];
    TermList r = lit[1];
    if (l == r) {
      return PredEvalResult::trivial(lit.polarity());
    } else {
      // l != r
      // TODO lift to evaluate inductive datatypes as well
      if (theory->isInterpretedNumber(l) && theory->isInterpretedNumber(r)) {
        return PredEvalResult::trivial(!lit.polarity());
      } else {
        return PredEvalResult::nop();
      }
    }
  }
};

/**
 * An evaluator for dealing with conversions between sorts
 *
 */
class InterpretedLiteralEvaluator::ConversionEvaluator
  : public Evaluator
{
public:
  bool canEvaluateFunc(unsigned func) override
  {
    CALL("InterpretedLiteralEvaluator::ConversionEvaluator::canEvaluateFunc");

    if (!theory->isInterpretedFunction(func)) {
      return false;
    }
    return theory->isConversionOperation(theory->interpretFunction(func));
  }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res) override
  {
    CALL("InterpretedLiteralEvaluator::ConversionEvaluator::tryEvaluateFunc");
    ASS(theory->isInterpretedFunction(trm));

    try {
      Interpretation itp = theory->interpretFunction(trm);
      ASS(theory->isFunction(itp));
      ASS(theory->isConversionOperation(itp));
      ASS_EQ(theory->getArity(itp), 1);

      TermList argTrm = *trm->nthArgument(0);
      switch(itp) {
      case Theory::INT_TO_RAT:
	{
	  IntegerConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) { 
	    return false;
	  }
	  RationalConstantType resNum(arg,1);
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::INT_TO_REAL:
	{
	  IntegerConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  RealConstantType resNum(RationalConstantType(arg,1));
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::RAT_TO_INT:
	{
	  RationalConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  IntegerConstantType resNum = IntegerConstantType::floor(arg);
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::RAT_TO_REAL:
	{
	  RationalConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  RealConstantType resNum(arg);
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::REAL_TO_INT:
	{
	  RealConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  IntegerConstantType resNum = IntegerConstantType::floor(RationalConstantType(arg));
	  res = TermList(theory->representConstant(resNum));
	  return true;
	}
      case Theory::REAL_TO_RAT:
	{
	  //this is correct only as long as we only represent rational real numbers
	  RealConstantType arg;
	  if (!theory->tryInterpretConstant(argTrm, arg)) {
	    return false;
	  }
	  RationalConstantType resNum(arg);
	  res = TermList(theory->representConstant(resNum));
	return true;
      }

      default:
	ASSERTION_VIOLATION;
      }
    }
    catch(ArithmeticException&)
    {
      return false;
    }
  }
};

/**
 * Evaluates constant theory expressions
 *
 * Evaluators for each sort implement tryEvaluate(Unary/Binary)(Func/Pred) 
 * 
 */
template<class T>
class InterpretedLiteralEvaluator::TypedEvaluator : public Evaluator
{
public:
  using Value = T;
  using number = num_traits<Value>;

  TypedEvaluator() {}

  bool isZero(T arg) const { return number::zeroC == arg; }
  TermList getZero() const {return number::zero(); }
  bool isOne(T arg) const { return number::oneC == arg; }
  bool isMinusOne(T arg) const { return typename number::ConstantType(-1) == arg; }
  TermList invert(TermList t) const { return number::minus(t); }
  bool isAddition(Interpretation interp) const { return interp == number::addI; }
  bool isProduct(Interpretation interp) const  { return interp == number::mulI; }
  virtual bool isDivision(Interpretation interp) const = 0;

  virtual bool canEvaluate(Interpretation interp)
  {
    CALL("InterpretedLiteralEvaluator::TypedEvaluator::canEvaluate");
    
    // This is why we cannot evaluate Equality here... we cannot determine its sort
    if (!theory->hasSingleSort(interp)) { return false; } //To skip conversions and EQUAL

    if (theory->isPolymorphic(interp)) { return false; } // typed evaulator not for polymorphic stuff

    unsigned opSort = theory->getOperationSort(interp);
    return opSort==T::getSort();
  }

  virtual bool tryEvaluateFunc(Term* trm, TermList& res) override
  {
    CALL("InterpretedLiteralEvaluator::tryEvaluateFunc");
    ASS(theory->isInterpretedFunction(trm));
    const auto num = num_traits<Value>{};

    _DEBUG( "try evaluate ", trm->toString() );

    try {
      Interpretation itp = theory->interpretFunction(trm);
      ASS(theory->isFunction(itp));
      unsigned arity = theory->getArity(itp);

      if (arity!=1 && arity!=2) {
	INVALID_OPERATION("unsupported arity of interpreted operation: "+Int::toString(arity));
      }
      T resNum;
      TermList arg1Trm = *trm->nthArgument(0);
      T arg1;
      if (arity==1) {
        if (theory->tryInterpretConstant(arg1Trm, arg1)){
          if (!tryEvaluateUnaryFunc(itp, arg1, resNum)) { return false;}
        } else if (itp == num.minusI){ 
          const unsigned umin = trm->functor();
          return trySimplifyUnaryMinus(umin, arg1Trm, res);
        } else{ 
          return false;
        }
      }
      else if(arity==2){

        // TODO handle addition x + -x ==> 0

        // If one argument is not a constant and the other is zero, one or minus one then
        // we might have some special cases
        T arg2;
        TermList arg2Trm = *trm->nthArgument(1);

        bool specialCase = true;
        T conArg;
        TermList nonConTerm;
        if (theory->tryInterpretConstant(arg1Trm, arg1) && (isZero(arg1) || isOne(arg1) || isMinusOne(arg1)) && 
            !theory->tryInterpretConstant(arg2Trm, arg2)) {
         conArg = arg1;
         nonConTerm = arg2Trm;
        }
        else if(theory->tryInterpretConstant(arg2Trm, arg2) && (isZero(arg2) || isOne(arg2) || isMinusOne(arg2)) && 
            !theory->tryInterpretConstant(arg1Trm, arg1)) {
         conArg = arg2;
         nonConTerm = arg1Trm;
        }
        else{
          specialCase = false;
        }
        if(specialCase){
	_DEBUG( "special case" );
 
          //Special case where itp is division and arg2 is '1'
          //   Important... this is a non-symmetric case!
          if(theory->tryInterpretConstant(arg2Trm, arg2) && isOne(arg2) && isDivision(itp)){
            res = arg1Trm;
            return true;
          }
          //Special case where itp is addition and conArg is '0'
          if(isZero(conArg) && isAddition(itp)){
            res = nonConTerm;
            return true;
          }
          //Special case where itp is multiplication and conArg  is '1'
          if(isOne(conArg) && isProduct(itp)){
            res = nonConTerm;
            return true;
          }
          //Special case where itp is multiplication and conArg  is '-1'
          if(isMinusOne(conArg) && isProduct(itp)){
            res = invert(nonConTerm); 
            return true;
          }
          //Special case where itp is multiplication and conArg is '0'
          if(isZero(conArg) && isProduct(itp)){
            res = getZero();
            return true;
          }
        }
        if(theory->tryInterpretConstant(arg1Trm, arg1) && theory->tryInterpretConstant(arg2Trm, arg2)){
	  if (!tryEvaluateBinaryFunc(itp, arg1, arg2, resNum)) { return false;}
        }
        else{ return false;}
      }
      // TODO FIXME: this point should not be reachable due to check for !(arity!=1 && arity!=2) before.
      res = TermList(theory->representConstant(resNum));
      return true;
    }
    catch(ArithmeticException)
    {
       DEBUG( "ArithmeticException" );
      return false;
    }
  }

  virtual PredEvalResult tryEvaluatePred(Literal* lit) override
  {
    CALL("InterpretedLiteralEvaluator::tryEvaluatePred");
    ASS(theory->isInterpretedPredicate(lit));
    bool res;

    try {
      Interpretation itp = theory->interpretPredicate(lit);
      ASS(!theory->isFunction(itp));
      unsigned arity = theory->getArity(itp);

      if (arity!=1 && arity!=2) {
	INVALID_OPERATION("unsupported arity of interpreted operation: "+Int::toString(arity));
      }
      TermList arg1Trm = *lit->nthArgument(0);
      T arg1;
      if (!theory->tryInterpretConstant(arg1Trm, arg1)) { return PredEvalResult::nop(); }
      if (arity==1) {
	if (!tryEvaluateUnaryPred(itp, arg1, res)) { return PredEvalResult::nop();}
      }
      else {
	TermList arg2Trm = *lit->nthArgument(1);
	T arg2;
	if (!theory->tryInterpretConstant(arg2Trm, arg2)) { return PredEvalResult::nop(); }
	if (!tryEvaluateBinaryPred(itp, arg1, arg2, res)) { return PredEvalResult::nop();}
      }
      if (lit->isNegative()) {
	res = !res;
      }
      return PredEvalResult::trivial(res);
    }
    catch(ArithmeticException&)
    {
      return PredEvalResult::nop();
    }

  }

  bool canEvaluateFunc(unsigned func) override
  {
    CALL("InterpretedLiteralEvaluator::TypedEvaluator::canEvaluateFunc");

    if (!theory->isInterpretedFunction(func)) {
      return false;
    }
    Interpretation interp = theory->interpretFunction(func);
    return canEvaluate(interp);
  }

  bool canEvaluatePred(unsigned pred) override
  {
    CALL("InterpretedLiteralEvaluator::TypedEvaluator::canEvaluatePred");

    if (!theory->isInterpretedPredicate(pred)) {
      return false;
    }
    Interpretation interp = theory->interpretPredicate(pred);
    return canEvaluate(interp);
  }

protected:
  /** Tries to simplify a term involving unary minus. 
   * the term to be simplified is uminus(innner)
   * uminus functor argument is passed for the sake of perfomance
   */
  bool trySimplifyUnaryMinus(const unsigned& uminus_functor, const TermList& inner, TermList& result)
  { 
    DEBUG("trySimplifyUnaryMinus(uminus(", inner, "))")
    ASS_EQ(uminus_functor, env.signature->getInterpretingSymbol(number::minusI));
    if (inner.isTerm()) {
      /* complex term */
      auto& t = *inner.term();
      if (theory->isInterpretedFunction(t.functor())) {

        /* interpreted function */
        auto itp = theory->interpretFunction(t.functor());
        switch (itp) {
          case number::minusI:
            ASS_EQ(t.arity(), 1);
            result = t[0];
            return true;

          case number::addI:
            ASS_EQ(t.arity(), 2);
            result = TermList(Term::create2(t.functor(), 
                simplifyUnaryMinus(uminus_functor, t[0]),
                simplifyUnaryMinus(uminus_functor, t[1])));
            return true; 

          default:
            /* interpreted function for which minus is not handled minus is not handled */
            return false;
        }

      } else {
        /* not an interpreted function */
        Value cons;
        if (theory->tryInterpretConstant(&t, cons)) {
          result = TermList(theory->representConstant(-cons));
          return true;
        } else {
          /* uninterpreted function */
          return false;
        }
      }
    } else {
      /* not a complex term */
      return false;
    }
  }

  TermList simplifyUnaryMinus(const unsigned& uminus_functor, const TermList& inner)
  {
    TermList out;
    if (trySimplifyUnaryMinus(uminus_functor, inner, out)) {
      return out;
    } else {
      return TermList(Term::create1(uminus_functor, inner));
    }
  }

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const T& arg, T& res)
  { return false; }
  virtual bool tryEvaluateBinaryFunc(Interpretation op, const T& arg1, const T& arg2, T& res)
  { return false; }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const T& arg1, bool& res)
  { return false; }
  virtual bool tryEvaluateBinaryPred(Interpretation op, const T& arg1, const T& arg2, bool& res)
  { return false; }
};

/**
 * Evaluates integer functions
 */
class InterpretedLiteralEvaluator::IntEvaluator : public TypedEvaluator<IntegerConstantType>
{
protected:

  virtual bool isDivision(Interpretation interp) const { 
    return interp==Theory::INT_QUOTIENT_E || interp==Theory::INT_QUOTIENT_T || 
           interp==Theory::INT_QUOTIENT_F; 
  }

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::IntEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::INT_UNARY_MINUS:
      res = -arg;
      return true;
    case Theory::INT_ABS:
      if (arg < 0) {
        res = -arg;
      } else {
        res = arg;
      }
      return true;
    case Theory::INT_SUCCESSOR:
      res = arg+1;
      return true;
    case Theory::INT_FLOOR:
    case Theory::INT_CEILING:
    case Theory::INT_TRUNCATE:
    case Theory::INT_ROUND:
       // For integers these do nothing
      res = arg;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::IntEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::INT_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::INT_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::INT_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::INT_QUOTIENT_E:
      res = arg1.quotientE(arg2); // should be equivalent to arg1/arg2
      return true;
    case Theory::INT_QUOTIENT_T:
      res = arg1.quotientT(arg2);
      return true;
    case Theory::INT_QUOTIENT_F:
      res = arg1.quotientF(arg2);
      return true;
    // The remainder is left - (quotient * right)
    case Theory::INT_REMAINDER_E:
      res = arg1 - (arg1.quotientE(arg2)*arg2);
      return true;
    case Theory::INT_REMAINDER_T:
      res = arg1 - (arg1.quotientT(arg2)*arg2);
      return true;
    case Theory::INT_REMAINDER_F:
      res = arg1 - (arg1.quotientF(arg2)*arg2);
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::IntEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::INT_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::INT_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::INT_LESS:
      res = arg1<arg2;
      return true;
    case Theory::INT_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    case Theory::INT_DIVIDES:
      res = (arg2%arg1)==0;
      return true;
    default:
      return false;
    }
  }
};

/**
 * Evaluations rational functions
 */
class InterpretedLiteralEvaluator::RatEvaluator : public TypedEvaluator<RationalConstantType>
{
protected:
  virtual bool isDivision(Interpretation interp) const { 
    return interp==Theory::RAT_QUOTIENT || interp==Theory::RAT_QUOTIENT_E || 
           interp==Theory::RAT_QUOTIENT_T || interp==Theory::RAT_QUOTIENT_F;
  }

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::RAT_UNARY_MINUS:
      res = -arg;
      return true;
    case Theory::RAT_FLOOR:
      res = arg.floor();
      return true;
    case Theory::RAT_CEILING:
      res = arg.ceiling();
      return true;
    case Theory::RAT_TRUNCATE:
      res = arg.truncate();
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::RAT_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::RAT_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::RAT_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::RAT_QUOTIENT:
      res = arg1/arg2;
      return true;
    case Theory::RAT_QUOTIENT_E:
      res = arg1.quotientE(arg2);
      return true;
    case Theory::RAT_QUOTIENT_T:
      res = arg1.quotientT(arg2);
      return true;
    case Theory::RAT_QUOTIENT_F:
      res = arg1.quotientF(arg2);
      return true;
    // The remainder is left - (quotient * right)
    case Theory::RAT_REMAINDER_E:
      res = arg1 - (arg1.quotientE(arg2)*arg2);
      return true;
    case Theory::RAT_REMAINDER_T:
      res = arg1 - (arg1.quotientT(arg2)*arg2);
      return true;
    case Theory::RAT_REMAINDER_F:
      res = arg1 - (arg1.quotientF(arg2)*arg2);
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::RAT_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::RAT_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::RAT_LESS:
      res = arg1<arg2;
      return true;
    case Theory::RAT_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const Value& arg1,
      bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RatEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::RAT_IS_INT:
      res = arg1.isInt();
      return true;
    default:
      return false;
    }
  }
};

/**
 * Evaluates real functions. 
 * As reals are represented as rationals the operations are for reals.
 * See Kernel/Theory.hpp for how these operations are defined
 */
class InterpretedLiteralEvaluator::RealEvaluator : public TypedEvaluator<RealConstantType>
{
protected:
  virtual bool isDivision(Interpretation interp) const { 
    return interp==Theory::REAL_QUOTIENT || interp==Theory::REAL_QUOTIENT_E ||
           interp==Theory::REAL_QUOTIENT_T || interp==Theory::REAL_QUOTIENT_F;
  }

  virtual bool tryEvaluateUnaryFunc(Interpretation op, const Value& arg, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateUnaryFunc");

    switch(op) {
    case Theory::REAL_UNARY_MINUS:
      res = -arg;
      return true;
    case Theory::REAL_FLOOR:
      res = arg.floor();
      return true;
    case Theory::REAL_CEILING:
      res = arg.ceiling();
      return true;
    case Theory::REAL_TRUNCATE:
      res = arg.truncate();
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryFunc(Interpretation op, const Value& arg1,
      const Value& arg2, Value& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateBinaryFunc");

    switch(op) {
    case Theory::REAL_PLUS:
      res = arg1+arg2;
      return true;
    case Theory::REAL_MINUS:
      res = arg1-arg2;
      return true;
    case Theory::REAL_MULTIPLY:
      res = arg1*arg2;
      return true;
    case Theory::REAL_QUOTIENT:
      res = arg1/arg2;
      return true;
    case Theory::REAL_QUOTIENT_E:
      res = arg1.quotientE(arg2);
      return true;
    case Theory::REAL_QUOTIENT_T:
      res = arg1.quotientT(arg2);
      return true;
    case Theory::REAL_QUOTIENT_F:
      res = arg1.quotientF(arg2);
      return true;
    // The remainder is left - (quotient * right)
    case Theory::REAL_REMAINDER_E:
      res = arg1 - (arg1.quotientE(arg2)*arg2);
      return true;
    case Theory::REAL_REMAINDER_T:
      res = arg1 - (arg1.quotientT(arg2)*arg2);
      return true;
    case Theory::REAL_REMAINDER_F:
      res = arg1 - (arg1.quotientF(arg2)*arg2);
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateBinaryPred(Interpretation op, const Value& arg1,
      const Value& arg2, bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::REAL_GREATER:
      res = arg1>arg2;
      return true;
    case Theory::REAL_GREATER_EQUAL:
      res = arg1>=arg2;
      return true;
    case Theory::REAL_LESS:
      res = arg1<arg2;
      return true;
    case Theory::REAL_LESS_EQUAL:
      res = arg1<=arg2;
      return true;
    default:
      return false;
    }
  }

  virtual bool tryEvaluateUnaryPred(Interpretation op, const Value& arg1,
      bool& res)
  {
    CALL("InterpretedLiteralEvaluator::RealEvaluator::tryEvaluateBinaryPred");

    switch(op) {
    case Theory::REAL_IS_INT:
      res = arg1.isInt();
      return true;
    case Theory::REAL_IS_RAT:
      //this is true as long as we can evaluate only rational reals.
      res = true;
      return true;
    default:
      return false;
    }
  }

};

template<class num>
struct mul_traits {
  using number = num;
  using ConstantType = typename number::ConstantType;
  static const Interpretation inter = number::mulI;
  static ConstantType identity() { return number::oneC;}
  static ConstantType groundEval(ConstantType l, ConstantType r) { return l * r; }
  static unsigned functor() { return number::mulF(); }
  static TermList iterate(int cnt, TermList t) { 
    if (cnt == 0) {
      return TermList(theory->representConstant(identity()));
    } else {
      ASS(cnt > 0);
      TermList out = t;
      for (int i = 1; i < cnt; i++) {
        out = TermList(number::mul(t, out));
      }
      return out;
    }
  }
};

template<class num>
struct add_traits {
  using number = num;
  using ConstantType = typename number::ConstantType;
  static constexpr Interpretation inter = number::addI;
  static ConstantType identity() { return number::zeroC;}
  static ConstantType groundEval(ConstantType l, ConstantType r) { return l + r; }
  static unsigned functor() { return number::addF(); }
  static TermList iterate(int cnt, TermList t) { 
    switch(cnt) {
      case 0:
        return number::zero();

      case 1:
        return t;

      default:
        TermList c = TermList(theory->representConstant(ConstantType(cnt)));
        return TermList(number::mul(c, t));
    }
  }
};

template<Theory::Interpretation op>
struct CommutativeMonoid;

/** Creates an instance of struct CommutativeMonoid<oper>, for the use in ACFunEvaluator. */
#define IMPL_OPERATOR(oper, type, identity, eval) \
  template<> struct CommutativeMonoid<num_traits<type>::oper##I> { \
    using ConstantType = type; \
    using number = num_traits<type>; \
    const static Theory::Interpretation interpreation = number::oper##I; \
    static unsigned functor() { return number::oper##F(); } \
    const static type IDENTITY; \
    static type groundEval(type l, type r) { return eval; } \
    /*const static unsigned FUNCTOR;*/ \
  }; \
  const type     CommutativeMonoid<num_traits<type>::oper##I>::IDENTITY = identity; \

/* int opeators */
IMPL_OPERATOR(mul, IntegerConstantType, IntegerConstantType(1), l * r)
IMPL_OPERATOR(add, IntegerConstantType, IntegerConstantType(0), l + r)

/* rational opeators */
IMPL_OPERATOR(mul, RationalConstantType, RationalConstantType(1), l * r)
IMPL_OPERATOR(add, RationalConstantType, RationalConstantType(0), l + r)

/* real opeators */
IMPL_OPERATOR(mul, RealConstantType, RealConstantType(RationalConstantType(1)), l * r)
IMPL_OPERATOR(add, RealConstantType, RealConstantType(RationalConstantType(0)), l + r)

////////////////////////////////
// InterpretedLiteralEvaluator
//
// This is where the evaluators defined above are used.

InterpretedLiteralEvaluator::InterpretedLiteralEvaluator(bool doNormalize) : _normalize(doNormalize)
{
  CALL("InterpretedLiteralEvaluator::InterpretedLiteralEvaluator");

  // For an evaluator to be used it must be pushed onto _evals
  // We search this list, calling canEvaluate on each evaluator
  // An invariant we want to maintain is that for any literal only one
  //  Evaluator will return true for canEvaluate
  _evals.push(new IntEvaluator());
  _evals.push(new RatEvaluator());
  _evals.push(new RealEvaluator());
  _evals.push(new ConversionEvaluator());
  _evals.push(new EqualityEvaluator());

  if(env.options->useACeval()){

  // Special AC evaluators are added to be tried first for Plus and Multiply

  _evals.push(new ACFunEvaluator<CommutativeMonoid<Theory::INT_PLUS>>()); 
  _evals.push(new ACFunEvaluator<CommutativeMonoid<Theory::INT_MULTIPLY>>());
  _evals.push(new ACFunEvaluator<CommutativeMonoid<Theory::RAT_PLUS>>());
  _evals.push(new ACFunEvaluator<CommutativeMonoid<Theory::RAT_MULTIPLY>> ());
  _evals.push(new ACFunEvaluator<CommutativeMonoid<Theory::REAL_PLUS>> ());
  _evals.push(new ACFunEvaluator<CommutativeMonoid<Theory::REAL_MULTIPLY>> ());

  }

  _funEvaluators.ensure(0);
  _predEvaluators.ensure(0);

}

InterpretedLiteralEvaluator::~InterpretedLiteralEvaluator()
{
  CALL("InterpretedEvaluation::LiteralSimplifier::~LiteralSimplifier");

  while (_evals.isNonEmpty()) {
    delete _evals.pop();
  }
}


/**
 * This checks if a literal is 'balancable' i.e. can be put into the form term=constant or term=var
 * 
 * This is still an experimental process and will be expanded/reworked later
 *
 * @author Giles
 * @since 11/11/14
 */
bool InterpretedLiteralEvaluator::balancable(Literal* lit)
{
  CALL("InterpretedLiteralEvaluator::balancable");
  // Check that lit is compatible with this balancing operation
  // One thing that we cannot check, but assume is that it has already been simplified once
  // balance applies further checks

  // we can only rebalance for equality. 
  // (Inequalities would be possible as well but this would interfer with the normalization ( t < s ==> 0 < s - t ))
  if (!lit->isEquality()) return false;
  ASS_EQ(lit->arity(), 2)

  // one side must be a constant and the other interpretted
  // the other side can contain at most one variable or uninterpreted subterm 
  // but we do not check this second condition here, instead we detect it in balance
  TermList t1 = *lit->nthArgument(0);
  TermList t2 = *lit->nthArgument(1);

  bool t1Number = theory->isInterpretedNumber(t1);
  bool t2Number = theory->isInterpretedNumber(t2);

  if(!t1Number && !t2Number){ return false; } // cannot balance
  if(t1Number && t2Number){ return true; } // already balanced

  // so here exactly one of t1Number and t2Number is true

  if(t1Number){
    if(t2.isVar()){ return false;} // already balanced
    if(!theory->isInterpretedFunction(t2)){ return false;} // cannot balance
  }
  if(t2Number){
    if(t1.isVar()){ return false;} // already balanced
    if(!theory->isInterpretedFunction(t1)){ return false;} // cannot balance
  }

  return true;
}

/**
 * This attempts to 'balance' a literal i.e. put it into the form term=constant
 *
 * The current implementation is only applicable to a restricted set of cases.
 *
 * This is still an experimental process and will be expanded/reworked later
 *
 * @author Giles
 * @since 11/11/14
 */
bool InterpretedLiteralEvaluator::balance(Literal* lit,Literal*& resLit,Stack<Literal*>& sideConditions)
{
  CALL("InterpretedLiteralEvaluator::balance");
  ASS(balancable(lit));

  _DEBUG( "try balance ", lit->toString() );

  ASS(theory->isInterpretedPredicate(lit->functor()));

  // at the end this tells us if the predicate needs to be swapped, only applies if non-equality
  bool swap = false; 

  // only want lesseq and equality
  if(lit->arity()!=2) return false;

  TermList t1;
  TermList t2;
  // ensure that t1 is the constant
  if(theory->isInterpretedNumber(*lit->nthArgument(0))){
    t1 = *lit->nthArgument(0); t2 = *lit->nthArgument(1);
  }else{
    t1 = *lit->nthArgument(1); t2 = *lit->nthArgument(0);
    swap=true;
  }
  // so we have t1 a constant and t2 something that has an interpreted function at the top

  Signature::Symbol* conSym = env.signature->getFunction(t1.term()->functor());
  unsigned srt = 0;
  if(conSym->integerConstant()) srt = Sorts::SRT_INTEGER;
  else if(conSym->rationalConstant()) srt = Sorts::SRT_RATIONAL;
  else if(conSym->realConstant()) srt = Sorts::SRT_REAL;
  else{
     ASSERTION_VIOLATION_REP(t1);
    return false;// can't work out the sort, that's odd!
  }

  // unwrap t2, applying the wrappings to t1 until we get to something we can't unwrap
  // this updates t1 and t2 as we go

  // This relies on the fact that a simplified literal with a single non-constant
  // subterm will look like f(c,f(c,f(c,t)))=c
  // If we cannot invert an interpreted function f then we fail

  bool modified = false;

  while(theory->isInterpretedFunction(t2)){
    TermList* args = t2.term()->args();
    
    // find which arg of t2 is the non_constant bit, this is what we are unwrapping 
    TermList* to_unwrap=0;
    while(args->isNonEmpty()){
      if(!theory->isInterpretedNumber(*args)){
        if(to_unwrap){
          return false; // If there is more than one non-constant term this will not work
        }
        to_unwrap=args;
      } 
      args= args->next();
    }
    //Should not happen if balancable passed and it was simplified
    if(!to_unwrap){ return false;} 
    
    // Now we do a case on the functor of t2
    Term* t2term = t2.term();
    Interpretation t2interp = theory->interpretFunction(t2term->functor());
    TermList result;
    bool okay=true;
    switch(t2interp){
      case Theory::INT_PLUS:
        okay=balancePlus(Theory::INT_PLUS,Theory::INT_UNARY_MINUS,t2term,to_unwrap,t1,result);
        break;
      case Theory::RAT_PLUS:
        okay=balancePlus(Theory::RAT_PLUS,Theory::RAT_UNARY_MINUS,t2term,to_unwrap,t1,result);
        break;
      case Theory::REAL_PLUS:
        okay=balancePlus(Theory::REAL_PLUS,Theory::REAL_UNARY_MINUS,t2term,to_unwrap,t1,result);
        break;

      case Theory::INT_MULTIPLY: 
      {
        okay=balanceIntegerMultiply(t2term,to_unwrap,t1,result,swap,sideConditions);
        break;
      }
      case Theory::RAT_MULTIPLY:
      {
        RationalConstantType zero(0,1);
        okay=balanceMultiply(Theory::RAT_QUOTIENT,zero,t2term,to_unwrap,t1,result,swap,sideConditions);
        break;
      }
      case Theory::REAL_MULTIPLY:
      {
        RealConstantType zero(RationalConstantType(0, 1));
        okay=balanceMultiply(Theory::REAL_QUOTIENT,zero,t2term,to_unwrap,t1,result,swap,sideConditions);
        break;
       }

      case Theory::RAT_QUOTIENT:
        okay=balanceDivide(Theory::RAT_MULTIPLY,t2term,to_unwrap,t1,result,swap,sideConditions);
        break;
      case Theory::REAL_QUOTIENT:
        okay=balanceDivide(Theory::REAL_MULTIPLY,t2term,to_unwrap,t1,result,swap,sideConditions);
        break;

      default:
        okay=false;
        break;
    }
    if(!okay){
        // cannot invert this one, finish here, either by giving up or going to the end
        if(!modified) return false;
        goto endOfUnwrapping; 
    }

    // update t1
    t1=result;
    // set t2 to the non-constant argument
    t2 = *to_unwrap;
    modified = true;
  }
endOfUnwrapping:

  //Evaluate t1
  // We have rearranged things so that t2 is a non-constant term and t1 is a number
  // of interprted functions applied to some constants. By evaluating t1 we will
  //  get a constant (unless evaluation is not possible)

  // don't swap equality
  if(lit->functor()==0){
   resLit = TermTransformerTransformTransformed::transform(Literal::createEquality(lit->polarity(),t2,t1,srt));
  }
  else{
    // important, need to preserve the ordering of t1 and t2 in the original!
    if(swap){
      resLit = TermTransformerTransformTransformed::transform(Literal::create2(lit->functor(),lit->polarity(),t2,t1));
    }else{
      resLit = TermTransformerTransformTransformed::transform(Literal::create2(lit->functor(),lit->polarity(),t1,t2));
    }
  }
  return true;
}


bool InterpretedLiteralEvaluator::balancePlus(Interpretation plus, Interpretation unaryMinus, 
                                              Term* AplusB, TermList* A, TermList C, TermList& result)
{
  CALL("InterpretedLiteralEvaluator::balancePlus");

    unsigned um = env.signature->getInterpretingSymbol(unaryMinus);
    unsigned ip = env.signature->getInterpretingSymbol(plus);
    TermList* B = 0;
    if(AplusB->nthArgument(0)==A){
      B = AplusB->nthArgument(1);
    }
    else{
      ASS(AplusB->nthArgument(1)==A);
      B = AplusB->nthArgument(0);
    }

    TermList mB(Term::create1(um,*B));
    result = TermList(Term::create2(ip,C,mB));
    return true;
}

template<typename ConstantType>
bool InterpretedLiteralEvaluator::balanceMultiply(Interpretation divide,ConstantType zero, 
                                                  Term* AmultiplyB, TermList* A, TermList C, TermList& result,
                                                  bool& swap, Stack<Literal*>& sideConditions)
{
    CALL("InterpretedLiteralEvaluator::balanceMultiply");
#if VDEBUG
    unsigned srt = theory->getOperationSort(divide); 
    ASS(srt == Sorts::SRT_REAL || srt == Sorts::SRT_RATIONAL); 
#endif

    unsigned div = env.signature->getInterpretingSymbol(divide);
    TermList* B = 0;
    if(AmultiplyB->nthArgument(0)==A){
      B = AmultiplyB->nthArgument(1);
    }
    else{
      ASS(AmultiplyB->nthArgument(1)==A);
      B = AmultiplyB->nthArgument(0);
    }
    result = TermList(Term::create2(div,C,*B));

    ConstantType bcon;
    if(theory->tryInterpretConstant(*B,bcon)){
      if(bcon.isZero()) return false;
      if(bcon.isNegative()){ swap=!swap; } // switch the polarity of an inequality if we're under one
      return true;
    }
    // Unsure exactly what the best thing to do here, so for now give up
    // This means we only balance when we have a constant on the variable side
    return false;

    // if B is not a constant we need to ensure that B!=0
    //Literal* notZero = Literal::createEquality(false,B,zero,srt);
    //sideConditions.push(notZero);
    //result = TermList(Term::create2(div,C,*B);
    //return true;
}

bool InterpretedLiteralEvaluator::balanceIntegerMultiply(
                                                  Term* AmultiplyB, TermList* A, TermList C, TermList& result,
                                                  bool& swap, Stack<Literal*>& sideConditions)
{
    CALL("InterpretedLiteralEvaluator::balanceIntegerMultiply");

    // only works if we in the end divid a number by a number
    IntegerConstantType ccon;
    if(!theory->tryInterpretConstant(C,ccon)){ return false; }

    // we are going to use rounding division but ensure that it is non-rounding
    unsigned div = env.signature->getInterpretingSymbol(Theory::INT_QUOTIENT_E);
    TermList* B = 0;
    if(AmultiplyB->nthArgument(0)==A){
      B = AmultiplyB->nthArgument(1);
    }
    else{
      ASS(AmultiplyB->nthArgument(1)==A);
      B = AmultiplyB->nthArgument(0);
    }
    result = TermList(Term::create2(div,C,*B));

    IntegerConstantType bcon;
    if(theory->tryInterpretConstant(*B,bcon)){
      if(bcon.isZero()){ return false; }
      if(!bcon.divides(ccon)){ return false;}
      if(bcon.isNegative()){ swap=!swap; } // switch the polarity of an inequality if we're under one
      return true;
    }
    return false;
}

bool InterpretedLiteralEvaluator::balanceDivide(Interpretation multiply, 
                       Term* AoverB, TermList* A, TermList C, TermList& result, bool& swap, Stack<Literal*>& sideConditions)
{
    CALL("InterpretedLiteralEvaluator::balanceDivide");
#if VDEBUG
    unsigned srt = theory->getOperationSort(multiply); 
    ASS(srt == Sorts::SRT_REAL || srt == Sorts::SRT_RATIONAL);
#endif

    unsigned mul = env.signature->getInterpretingSymbol(multiply);
    if(AoverB->nthArgument(0)!=A)return false;

    TermList* B = AoverB->nthArgument(1);

    result = TermList(Term::create2(mul,C,*B));

    RationalConstantType bcon;
    if(theory->tryInterpretConstant(*B,bcon)){
      ASS(!bcon.isZero());
      if(bcon.isNegative()){ swap=!swap; } // switch the polarity of an inequality if we're under one
      return true;
    }
    // Unsure exactly what the best thing to do here, so for now give up
    // This means we only balance when we have a constant on the variable side
    return false;    
}

// // TODO document me
// Literal& balance(Literal& in)
// {
//   /* we only rebalance equalities */
//   if (!in.isEquality()) {
//     return in;
//
//   } else {
//     ASS(in.arity() == 2);
//     unsigned sort;
//     if (!SortHelper::tryGetResultSort(in[0], sort) &&
//         !SortHelper::tryGetResultSort(in[1], sort)) {
//       return in;
//     } else {
//
//       Literal* out;
//       switch (sort) {
// #define _CASE(SRT, ConstantType) \
//         case Sorts::SRT: \
//           if (!balance<ConstantType>(in, out)){ \
//             return in; \
//           } 
//         _CASE(SRT_REAL    ,    RealConstantType)
//         _CASE(SRT_INTEGER , IntegerConstantType)
//         _CASE(SRT_RATIONAL,RationalConstantType)
// #undef _CASE
//         default: return in;
//       }
//       return *out;
//     }
//   }
// }

class LiteralNormalizer 
{
  // static bool canNormalizePred(Theory::Interpretation pred);
  // static bool canNormalize(const Literal& l)
  // {
  //   return canNormalize(env.signature->getPredicate(l.getPredicate))
  // }

public:
  static Literal* normalize(Literal* in) {
    CALL("LiteralNormalizer::normalize");
    auto functor = in->functor();

    if (theory->isInterpretedPredicate(functor)) {
      auto i = theory->interpretPredicate(functor);

      switch (i) {
        case Interpretation::INT_LESS: 
          return InequalityNormalizer<IntLess>::normalize(in);

        case Interpretation::RAT_LESS: 
          return InequalityNormalizer<FracLess<RationalConstantType>>::normalize(in);

        case Interpretation::REAL_LESS: 
          return InequalityNormalizer<FracLess<RealConstantType>>::normalize(in);

        default: 
          return in;
      }
    } else {
      /* uninterpreted predicate */
      return in;
    }
  }
};
TermList InterpretedLiteralEvaluator::evaluate(TermList t) {
  CALL("InterpretedLiteralEvaluator::evaluate")
  if (t.isTerm())
    t = TermList(TermTransformerTransformTransformed::transform(t.term()));
  return InterpretedLiteralEvaluator::transformSubterm(t);
}

/**
 * Used to evaluate a literal, setting isConstant, resLit and resConst in the process
 *
 * Returns true if it has been evaluated, in which case resLit is set 
 * isConstant is true if the literal predicate evaluates to a constant value
 * resConst is set iff isConstant and gives the constant value (true/false) of resLit 
 */
bool InterpretedLiteralEvaluator::evaluate(Literal* lit, bool& isConstant, Literal*& resLit, bool& resConst,Stack<Literal*>& sideConditions)
{
  CALL("InterpretedLiteralEvaluator::evaluate");

  DEBUG( "evaluate ", lit->toString() );

  // This tries to transform each subterm using tryEvaluateFunc (see transform Subterm below)

  resLit = _normalize ? LiteralNormalizer::normalize(lit)
                      : lit;
  DEBUG( "\t0 ==> ", resLit->toString() );

  resLit = TermTransformerTransformTransformed::transform( resLit);
  DEBUG( "\t1 ==> ", resLit->toString() );

//   // If it can be balanced we balance it
//   // A predicate on constants will not be balancable
// #if 0
//   resLit = &Kernel::balance(*resLit);
// #else // not NEW_BALANCE
//   if(balancable(resLit)){
//       Literal* new_resLit=resLit;
// #if VDEBUG
//       bool balance_result = 
// #endif
//         balance(resLit,new_resLit,sideConditions);
//       ASS(balance_result || resLit==new_resLit);
//       resLit=new_resLit;
//   }
// #endif
//   DEBUG( "\t2 ==> ", *resLit );

  // // If resLit contains variables the predicate cannot be interpreted
  // VariableIterator vit(lit);
  // if(vit.hasNext()){
  //   isConstant=false;
  //   return (lit!=resLit);
  // }
  // // If resLit contains uninterpreted functions then it cannot be interpreted
  // TermFunIterator tit(lit);
  // ASS(tit.hasNext()); tit.next(); // pop off literal symbol
  // while(tit.hasNext()){
  //   unsigned f = tit.next();
  //   if(!env.signature->getFunction(f)->interpreted()){
  //     isConstant=false;
  //     return (lit!=resLit);
  //   } 
  // }
  // _DEBUG( resLit->toString(, " is ground and interpreted, evaluating..." );


  unsigned pred = resLit->functor();

  // Now we try and evaluate the predicate
  Evaluator* predEv = getPredEvaluator(pred);
  if (predEv) {
    auto r = predEv->tryEvaluatePred(resLit);

    switch (r.status) {
      case PredEvalResult::Nop: 
        break;

      case PredEvalResult::Simplified: 
        // resLit = r.simplified_val;
        resLit = TermTransformerTransformTransformed::transform(r.simplified_val);
        break;

      case PredEvalResult::Trivial: 
        isConstant = true;
        resConst = r.trivial_val;
        DEBUG( "\t3 ==> ", resConst );
        return true;

    }
  }
  isConstant = false;
  auto out = resLit != lit;
  DEBUG( "\t3 ==> ", resLit->toString(), "(did evaluate: ", out, ")" );
  return out;
}




/**
 * This attempts to evaluate each subterm.
 * See Kernel/TermTransformerTransformTransformed for how it is used.
 * Terms are evaluated bottom-up
 */
TermList InterpretedLiteralEvaluator::transformSubterm(TermList trm)
{
  CALL("InterpretedLiteralEvaluator::transformSubterm");
  // Debug::Tracer::printStack(cout);

  DEBUG( "transformSubterm for ", trm.toString() );


  if (!trm.isTerm()) { return trm; }
  Term* t = trm.term();
  unsigned func = t->functor();

  Evaluator* funcEv = getFuncEvaluator(func);
  if (funcEv) {
    TermList res;
    if (funcEv->tryEvaluateFunc(t, res)) {
	return res;
    }
  } else {
    DEBUG("no transformer")
  }
  return trm;
}

/**
 * This searches for an Evaluator for a function
 */
template<class Fn>
InterpretedLiteralEvaluator::Evaluator* InterpretedLiteralEvaluator::getEvaluator(unsigned functor, DArray<Evaluator*>& evaluators, Fn canEval) 
{
  CALL("InterpretedLiteralEvaluator::getEvaluator");

  if (functor >= evaluators.size()) {
    unsigned oldSz = evaluators.size();
    unsigned newSz = functor + 1 ;
    evaluators.expand(newSz);
    for (unsigned i=oldSz; i<newSz; i++) {
        EvalStack::Iterator evit(_evals);
	while (evit.hasNext()) {
          Evaluator* ev = evit.next();
          // we only set the evaluator if it has not yet been set
	  if (canEval(ev, i)) {
	    evaluators[i] = ev;
            goto break_inner;
	  }
	}
break_inner:;
    }
  }
  return evaluators[functor];
}

/**
 * This searches for an Evaluator for a function
 */
InterpretedLiteralEvaluator::Evaluator* InterpretedLiteralEvaluator::getFuncEvaluator(unsigned func)
{
  CALL("InterpretedLiteralEvaluator::getFuncEvaluator");
   return getEvaluator(func, 
       this->_funEvaluators, 
       [] (Evaluator* ev, unsigned i) {return ev->canEvaluateFunc(i); });
}

/**
 * This searches for an Evaluator for a predicate
 */
InterpretedLiteralEvaluator::Evaluator* InterpretedLiteralEvaluator::getPredEvaluator(unsigned pred)
{
  CALL("InterpretedLiteralEvaluator::getPredEvaluator");
   return getEvaluator(pred, this->_predEvaluators,
       [] (Evaluator* ev, unsigned i) {return ev->canEvaluatePred(i); });
}

}

namespace Kernel {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Equality
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number> inline LitEvalResult interpret_equality(Literal* lit, bool polarity, TermList lhs, TermList rhs) {
  using Const = typename number::ConstantType;
  Const l;
  Const r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return polarity == (l == r);
  } else {
    return Literal::createEquality(lit->polarity(), lhs, rhs, number::sort);
  }
}

template<> LitEvalResult NewEvaluator::evaluateLit<Interpretation::EQUAL>(Literal* lit) const {
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  if (lhs == rhs) return lit->polarity();
  auto sort =  SortHelper::getEqualityArgumentSort(lit);
  switch (sort) {
    case Sorts::SRT_INTEGER:  return interpret_equality<num_traits<IntegerConstantType>>(lit, lit->polarity(), lhs, rhs);
    case Sorts::SRT_RATIONAL: return interpret_equality<num_traits<RationalConstantType>>(lit, lit->polarity(), lhs, rhs);
    case Sorts::SRT_REAL:     return interpret_equality<num_traits<RealConstantType>>(lit, lit->polarity(), lhs, rhs);
                             //TODO lift to term algebras
    default:
      return Literal::createEquality(lit->polarity(), lhs, rhs, sort);
  }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Inequalities
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalIneq> LitEvalResult NewEvaluator::evaluateInequality(Literal* lit, bool strict, EvalIneq evalIneq) const {
  ASS(lit->arity() == 2);
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  if (lhs == rhs) return lit->polarity() != strict;
  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return lit->polarity() == evalIneq(l, r);
  } else {
    return lit;
  }
}

#define __IMPL_INEQ(Const, name, STRICT, op) \
  template<> LitEvalResult NewEvaluator::evaluateLit<num_traits<Const>::name ## I>(Literal* lit) const \
  { return evaluateInequality<Const>(lit, STRICT, [](Const l, Const r) {return l op r;}); } \

#define IMPL_INEQUALTIES(Const) \
   /*                inequality| is strict? | operator */ \
  __IMPL_INEQ(Const, less      ,   true     ,  <        ) \
  __IMPL_INEQ(Const, leq       ,   false    ,  <=       ) \
  __IMPL_INEQ(Const, greater   ,   true     ,  >        ) \
  __IMPL_INEQ(Const, geq       ,   false    ,  >=       ) \


IMPL_INEQUALTIES(RationalConstantType)
IMPL_INEQUALTIES(RealConstantType) 
IMPL_INEQUALTIES(IntegerConstantType)

#undef  IMPL_NUM_EVALS
#undef  __IMPL_INEQ

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// INT_IS_RAT and similar functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//TODO
#define __IMPL_NUM_IS_NUM(INT, RAT) \
  template<> LitEvalResult NewEvaluator::evaluateLit<Interpretation::INT ## _IS_ ## RAT>(Literal* lit) const { \
    return lit; \
  } \

#define IMPL_NUM_IS_NUM(NUM) \
    __IMPL_NUM_IS_NUM(NUM, RAT) \
    __IMPL_NUM_IS_NUM(NUM, REAL) \
    __IMPL_NUM_IS_NUM(NUM, INT) \

IMPL_NUM_IS_NUM(INT)
IMPL_NUM_IS_NUM(RAT)
IMPL_NUM_IS_NUM(REAL)

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// INT_DIVIDES
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<> LitEvalResult NewEvaluator::evaluateLit<Interpretation::INT_DIVIDES>(Literal* lit) const {
  return tryEvalConstant2<IntegerConstantType>(lit, [](IntegerConstantType l, IntegerConstantType r) { 
      return (r % l) == 0;
  });
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// AC_FUNCTIONS
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//TODO sorting is ver inefficient. Indeterministic sorting instead?
int _sort_terms(const Term& lhs, const TermList& rhs);
int _sort_terms(TermList lhs, TermList rhs);

int _sort_terms(const Term& lhs, const Term& rhs) {

  int l_fun = lhs.functor();
  int r_fun = rhs.functor();

  int l_thry = theory->isInterpretedFunction(l_fun);
  int r_thry = theory->isInterpretedFunction(r_fun);
  int cmp_thry = l_thry - r_thry;

  if (cmp_thry != 0) return cmp_thry;
  if (l_thry) {
    ASS(r_thry)

    int l_inter = theory->interpretFunction(l_fun);
    int r_inter = theory->interpretFunction(r_fun);
    int cmp_inter = l_inter - r_inter;

    if (cmp_inter != 0) return cmp_inter;

  } else {
    ASS(!l_thry && !r_thry)
 
    int cmp_fun = l_fun - r_fun;
    if (cmp_fun != 0) return cmp_fun;
 }

  ASS(lhs.arity() == rhs.arity())
  for (int i = 0; i < lhs.arity(); i++) {
    auto cmp = _sort_terms(lhs[i], rhs[i]);
    if (cmp != 0) {
      return cmp;
    }
  }
  return 0;
}

bool sort_terms(TermList lhs, TermList rhs) {
  return _sort_terms(lhs, rhs) < 0;
}

int _sort_terms(TermList lhs, TermList rhs) {
  auto l_trm = lhs.isTerm();
  auto r_trm = rhs.isTerm();
  auto cmp_trm = l_trm - r_trm;
  if (cmp_trm != 0) return cmp_trm;

  if (l_trm) {
    ASS(r_trm);
    return _sort_terms(*lhs.term(), *rhs.term());
  } else {
    ASS(lhs.isVar() && rhs.isVar());
    return int(lhs.var()) - int(rhs.var());
  }

}

template<class CommutativeMonoid> 
TermList NewEvaluator::evaluateCommutativeMonoid(Term* orig, TermList* args) const {
    CALL("NewEvaluator::evaluateCommutativeMonoid(TermList* args)")
    DEBUG("orig: ", orig->toString())
    using ConstantType = typename CommutativeMonoid::ConstantType;

    const unsigned fun = CommutativeMonoid::functor();

    ConstantType acc = CommutativeMonoid::identity();
    DHMap<TermList, int> map;
    // Stack<TermList> keep;
    auto traverse = [&](TermList t) {
      DEBUG("arg: ", t)
      return stackTraverseIf(t,
        /* we traverse only the parts with the same operation */
        [&](Term& t){ return t.functor() == fun; },
        [&](TermList t) {
          ConstantType c;
          /* we eval constant parts */
          if (t.isTerm() && theory->tryInterpretConstant(t.term(), c)) {
            acc = CommutativeMonoid::groundEval(acc, c);
          } else {
            int* value;
            map.getValuePtr(t, value, 0);
            // DBG(*value, " x ", t);
            (*value) += 1;
            // keep.push(t);
          }
        });
    };

    traverse(args[1]);
    traverse(args[0]);

    Stack<TermList> keep;
    {
      decltype(map)::Iterator iter(map);
      while (iter.hasNext()) {
        TermList t;
        int cnt;
        iter.next(t, cnt);
        if (cnt != 0) {
          keep.push(CommutativeMonoid::iterate(cnt, t));
        }
      }
    }

    if (acc != CommutativeMonoid::identity()) {
      keep.push(TermList(theory->representConstant(acc)));
    }

    //TODO make it possile to turn off sorting
    std::sort(keep.begin(), keep.end(), [](TermList lhs, TermList rhs) -> bool {return sort_terms(lhs,rhs);});

    auto iter = Stack<TermList>::BottomFirstIterator(keep);
    if (!iter.hasNext()) {
      return TermList(theory->representConstant(CommutativeMonoid::identity()));
    } else {
      TermList out = iter.next();
      while (iter.hasNext()) {
        auto t = iter.next();
        out = TermList(Term::create2(fun, t, out));
      }
      DEBUG("out: ", out)
      return out;
    }
}


// template<class number> 
// TermList evaluateAdd(TermList evaluatedLhs, TermList evaluatedRhs) const {
//     CALL("NewEvaluator::evaluateCommutativeMonoid(TermList* args)")
//     using ConstantType = typename CommutativeMonoid::ConstantType;
//
//     const unsigned fun = CommutativeMonoid::functor();
//
//     ConstantType acc = CommutativeMonoid::IDENTITY;
//     Stack<TermList> keep;
//     auto traverse = [&](TermList t) {
//       return stackTraverseIf(t,
//         /* we traverse only the parts with the same operation */
//         [&](Term& t){ return t.functor() == fun; },
//         [&](TermList t) {
//           ConstantType c;
//           /* we eval constant parts */
//           if (t.isTerm() && theory->tryInterpretConstant(t.term(), c)) {
//             acc = CommutativeMonoid::groundEval(acc, c);
//           } else {
//             keep.push(t);
//           }
//         });
//     };
//     traverse(args[1]);
//     traverse(args[0]);
//
//     if (acc != CommutativeMonoid::IDENTITY) {
//       keep.push(TermList(theory->representConstant(acc)));
//     }
//
//     auto iter = Stack<TermList>::Iterator(keep);
//     if (!iter.hasNext()) {
//       return TermList(theory->representConstant(CommutativeMonoid::IDENTITY));
//     } else {
//       TermList out = iter.next();
//       while (iter.hasNext()) {
//         auto t = iter.next();
//         out = TermList(Term::create2(fun, out, t));
//       }
//       DEBUG("out: ", out)
//       return out;
//     }
// }

#define __IMPL_COMMUTATIVE_MONOID(Const, name) \
  template<> TermList NewEvaluator::evaluateFun<num_traits<Const>::name##I>(Term* orig, TermList* args) const  \
  { \
    CALL("NewEvaluator::evaluateFun<num_traits<" #Const ">::" #name "I>(Term*, TermList*)") \
    auto out = evaluateCommutativeMonoid<name ## _traits<num_traits<Const>>>(orig, args);  \
    DEBUG(orig->toString(), "->", out) \
    return out; \
  } \

#define IMPL_COMMUTATIVE_MONOIDS(Const) \
  __IMPL_COMMUTATIVE_MONOID(Const, add) \
  __IMPL_COMMUTATIVE_MONOID(Const, mul) \


  IMPL_COMMUTATIVE_MONOIDS(RationalConstantType)
  IMPL_COMMUTATIVE_MONOIDS(RealConstantType)
  IMPL_COMMUTATIVE_MONOIDS(IntegerConstantType)

#undef IMPL_COMMUTATIVE_MONOIDS
#undef __IMPL_COMMUTATIVE_MONOID

 

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// UNARY_MINUS 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

struct RecursionState {

};

template<class number>
TermList evaluateUnaryMinus(TermList inner_) {
  using Const = typename number::ConstantType;

  // auto inner_ = evaluatedArgs[0];

  if (inner_.isVar()) {
    return number::minus(TermList(inner_));

  } else {
    ASS(inner_.isTerm());

    auto& inner = *inner_.term();
    Const c;
    if (theory->isInterpretedFunction(&inner)) {
      switch (theory->interpretFunction(inner.functor())) {
        case number::addI:
          // NORMALIZATION
          // TODO de-recursify
          return number::add(
              evaluateUnaryMinus<number>(inner[0]),
              evaluateUnaryMinus<number>(inner[1])
              );
        case number::mulI:
          // NORMALIZATION
          return number::mul(
              evaluateUnaryMinus<number>(inner[0]),
              inner[1]
              );
        case number::minusI:
          return inner[0];
        default: 
          return number::minus(inner_);
      }
    } else if (theory->tryInterpretConstant(&inner, c)) {
      return TermList(theory->representConstant(-c));
    } else {
        return number::minus(inner_);
    }
  }
}

#define IMPL_UNARY_MINUS(Const) \
  template<> TermList NewEvaluator::evaluateFun<num_traits<Const>::minusI>(Term* orig, TermList* evaluatedArgs) const  \
  { \
    CALL("NewEvaluator::evaluateFun<num_traits<" #Const ">::minusI>(Term* trm, TermList* evaluatedArgs)") \
    auto out = evaluateUnaryMinus<num_traits<Const>>(evaluatedArgs[0]);  \
    DEBUG(orig->toString(), "\t->\t", out) \
    return out; \
  } \

  IMPL_UNARY_MINUS(RealConstantType    )
  IMPL_UNARY_MINUS(RationalConstantType)
  IMPL_UNARY_MINUS(IntegerConstantType )

#undef IMPL_UNARY_MINUS


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Functions that are only handled for constants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////


#define IMPL_EVAL_UNARY(Const, INTER, expr) \
  template<> TermList NewEvaluator::evaluateFun<Interpretation::INTER>(Term* orig, TermList* evaluatedArgs) const   \
  {  return tryEvalConstant1<Const>(orig, evaluatedArgs, [] (Const x) { return expr; }); } 

#define IMPL_EVAL_BINARY(Const, INTER, expr) \
  template<> TermList NewEvaluator::evaluateFun<Interpretation::INTER>(Term* orig, TermList* evaluatedArgs) const   \
  {  return tryEvalConstant2<Const>(orig, evaluatedArgs, [] (Const l, Const r) { return expr; }); } 


/////////////////// Integer only functions

IMPL_EVAL_UNARY(IntegerConstantType, INT_ABS      , x >= 0 ? x : -x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_SUCCESSOR, x + 1          )

/////////////////// INT_QUOTIENT_E and friends

#define IMPL_QUOTIENT_REMAINDER(Const, NUM, SUFFIX) \
  IMPL_EVAL_BINARY(Const, NUM ##  _QUOTIENT_ ## SUFFIX,  l.quotient ## SUFFIX(r)) \
  IMPL_EVAL_BINARY(Const, NUM ## _REMAINDER_ ## SUFFIX,  l - (l.quotient ## SUFFIX (r)*r)) \

#define IMPL_QUOTIENT_REMAINDERS(Const, NUM) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, E) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, T) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, F) \
  IMPL_EVAL_BINARY(Const, NUM ## _MINUS, l - r) \

  IMPL_QUOTIENT_REMAINDERS(RealConstantType    , REAL)
  IMPL_QUOTIENT_REMAINDERS(RationalConstantType, RAT )
  IMPL_QUOTIENT_REMAINDERS(IntegerConstantType , INT )

#undef IMPL_QUOTIENT_REMAINDER
#undef IMPL_QUOTIENT_REMAINDERS

/////////////////// INT_FLOOR and friends

// have no effect for ints
IMPL_EVAL_UNARY(IntegerConstantType, INT_FLOOR   , x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_CEILING , x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_TRUNCATE, x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_ROUND   , x)

// same impl for fractionals
#define IMPL_FRAC_FLOOR_FRIENDS(Const, NUM) \
  IMPL_EVAL_UNARY(Const, NUM ## _FLOOR, x.floor()) \
  IMPL_EVAL_UNARY(Const, NUM ## _CEILING, x.ceiling()) \
  IMPL_EVAL_UNARY(Const, NUM ## _TRUNCATE, x.truncate()) \

  IMPL_FRAC_FLOOR_FRIENDS(RealConstantType    , REAL)
  IMPL_FRAC_FLOOR_FRIENDS(RationalConstantType, RAT)

#undef IMPL_EVAL_FRAC_FLOOR_FRIENDS
 
/////////////////// RAT_TO_INT and friends

#define IMPL_NUM_CVT(Const, NUM) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_INT, IntegerConstantType::floor(x)) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_RAT, RationalConstantType(x)) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_REAL, RealConstantType(x)) \

  IMPL_NUM_CVT(RealConstantType    , REAL)
  IMPL_NUM_CVT(RationalConstantType, RAT )
  IMPL_NUM_CVT(IntegerConstantType , INT )

#undef IMPL_NUM_CVT

/////////////////// QUOTIENT 
//
#define IMPL_QUOTIENT(Const, NUM) \
    IMPL_EVAL_BINARY(Const, NUM ## _QUOTIENT, l / r) \

  IMPL_QUOTIENT(RealConstantType    , REAL)
  IMPL_QUOTIENT(RationalConstantType, RAT )

#undef IMPL_QUOTIENT
 

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalGround>
LitEvalResult NewEvaluator::tryEvalConstant1(Literal* lit, EvalGround fun) const {
  auto lhs = *lit->nthArgument(0);
  ConstantType l;
  if (theory->tryInterpretConstant(lhs, l)) {
    return fun(l);
  } else {
    return lit;
  }
}


template<class ConstantType, class EvalGround>
LitEvalResult NewEvaluator::tryEvalConstant2(Literal* lit, EvalGround fun) const {
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return fun(l,r);
  } else {
    return lit;
  }
}


template<class ConstantType, class EvalGround>
TermList NewEvaluator::tryEvalConstant1(Term* orig, TermList* evaluatedArgs, EvalGround fun) const {

  auto lhs = evaluatedArgs[0];

  ConstantType l;
  if (theory->tryInterpretConstant(lhs, l)) {
    return TermList(theory->representConstant(fun(l)));
  } else {
    return TermList(orig);
  }
}


template<class ConstantType, class EvalGround>
TermList NewEvaluator::tryEvalConstant2(Term* orig, TermList* evaluatedArgs, EvalGround fun) const {

  auto lhs = evaluatedArgs[0];
  auto rhs = evaluatedArgs[1];

  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return TermList(theory->representConstant(fun(l,r)));
  } else {
    return TermList(orig);
  }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Main literal evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

LitEvalResult NewEvaluator::evaluate(Literal* lit) const {
  Stack<TermList> terms;
  //TODO reserve arity
  for (int i = 0; i < lit->arity(); i++) {
    terms.push(evaluate(*lit->nthArgument(i)));
  }
  return evaluateStep(Literal::create(lit, terms.begin()));
}

LitEvalResult NewEvaluator::evaluateStep(Literal* lit) const {
  CALL("NewEvaluator::evaluateStep(Literal* term)")
  DEBUG("evaluating: ", lit->toString());

#define HANDLE_CASE(INTER) case Interpretation::INTER: return evaluateLit<Interpretation::INTER>(lit); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return lit;
#define HANDLE_NUM_CASES(NUM) \
      HANDLE_CASE(NUM ## _IS_INT) \
      HANDLE_CASE(NUM ## _IS_RAT) \
      HANDLE_CASE(NUM ## _IS_REAL) \
      HANDLE_CASE(NUM ## _GREATER) \
      HANDLE_CASE(NUM ## _GREATER_EQUAL) \
      HANDLE_CASE(NUM ## _LESS) \
      HANDLE_CASE(NUM ## _LESS_EQUAL) 

  //TODO create function theory->tryInterpret(Predicate|Function)
  auto sym = env.signature->getPredicate(lit->functor());
  if (sym->interpreted()) {
    auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();

    switch (inter) {
      /* polymorphic */
      HANDLE_CASE(EQUAL)

      /* common number predicates */
      HANDLE_NUM_CASES(INT)
      HANDLE_NUM_CASES(RAT)
      HANDLE_NUM_CASES(REAL)

      /* integer predicates */
      HANDLE_CASE(INT_DIVIDES)

      default:
        DBG("WARNING: unexpected interpreted predicate: ", lit->toString())
        ASSERTION_VIOLATION
        return lit;
    }
  } else {
    return lit;
  }

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Main Term
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////


TermList NewEvaluator::evaluate(TermList term) const {
  if (term.isTerm()) {
    return evaluate(term.term()); 
  } else {
    ASS_REP(term.isVar(), term);
    /* single variables can't be simplified */
    return term;
  }
}

// TermList NewEvaluator::evaluateStep(TermList term) const {
//   if (term.isTerm()) {
//     return evaluateStep(term.term()); 
//   } else {
//     ASS_REP(term.isVar(), term);
//     /* single variables can't be simplified */
//     return term;
//   }
// }

TermList NewEvaluator::evaluate(Term* term) const {
  CALL("NewEvaluator::evaluate(Term* term)")
  DEBUG("evaluating ", term->toString())

  static Stack<TermList*> position(8);

  static Stack<Term*> terms(8);
  static Stack<TermList> args(8);

  args.reset();
  position.reset();
  terms.reset();

  position.push(term->args());
  terms.push(term);

  TermList* cur;
  do {

    cur = position.pop();
    // DBG("recursing on ", *cur)

    // DBG("args: ", args)

    if (!cur->isEmpty()) {

      position.push(cur->next());

      if(cur->isVar()) {
        // variables are not evaluated
        args.push(*cur);

      } else {
        ASS(cur->isTerm());
        Term* t = cur->term();
        terms.push(t);
        position.push(t->args());
      }



    } else /* cur->isEmpty() */ { 

      ASS(!terms.isEmpty()) 

      Term* orig=terms.pop();

      TermList* argLst = 0;
      if (orig->arity() != 0) {
        //here we assume, that stack is an array with
        //second topmost element as &top()-1, third at
        //&top()-2, etc...
        argLst=&args.top() - (orig->arity()-1);
        args.truncate(args.length() - orig->arity());
      }

      // auto t = Term::create(orig,argLst);
      auto res = evaluateStep(orig, argLst);
      DEBUG("evaluated: ", orig->toString(), " -> ", res);
      args.push(res);
      
    }

  // } while (!( cur->isEmpty() && terms.isEmpty() ));
  } while (!position.isEmpty());
  ASS_REP(position.isEmpty(), position)

  return args.pop(); 
}

TermList NewEvaluator::evaluateStep(Term* orig, TermList* args) const {
  CALL("NewEvaluator::evaluateStep(Term* orig, TermList* args)")
  DEBUG("evaluateStep(", orig->toString(), ")")

#define HANDLE_CASE(INTER) case Interpretation::INTER: return evaluateFun<Interpretation::INTER>(orig, args); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return TermList(Term::create(orig, args));

#define HANDLE_NUM_CASES(NUM) \
    HANDLE_CASE(NUM ## _UNARY_MINUS) \
    HANDLE_CASE(NUM ## _PLUS) \
    HANDLE_CASE(NUM ## _MINUS) \
    HANDLE_CASE(NUM ## _MULTIPLY) \
    HANDLE_CASE(NUM ## _QUOTIENT_E) \
    HANDLE_CASE(NUM ## _QUOTIENT_T) \
    HANDLE_CASE(NUM ## _QUOTIENT_F) \
    HANDLE_CASE(NUM ## _REMAINDER_E) \
    HANDLE_CASE(NUM ## _REMAINDER_T) \
    HANDLE_CASE(NUM ## _REMAINDER_F) \
    HANDLE_CASE(NUM ## _FLOOR) \
    HANDLE_CASE(NUM ## _CEILING) \
    HANDLE_CASE(NUM ## _TRUNCATE) \
    HANDLE_CASE(NUM ## _TO_INT) \
    HANDLE_CASE(NUM ## _TO_RAT) \
    HANDLE_CASE(NUM ## _TO_REAL) \

  //TODO de-recursify
  auto sym = env.signature->getFunction(orig->functor());
  if (sym->interpreted()) {
    auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();
    switch (inter) {

      /* common number functions*/
      HANDLE_NUM_CASES(INT)
      HANDLE_NUM_CASES(RAT)
      HANDLE_NUM_CASES(REAL)

      /* integer functions */
      HANDLE_CASE(INT_SUCCESSOR)
      HANDLE_CASE(INT_ABS)

      /* rational functions */
      HANDLE_CASE(RAT_QUOTIENT)
      IGNORE_CASE(RAT_ROUND)  //TODO

      /* real functions */
      HANDLE_CASE(REAL_QUOTIENT)
      IGNORE_CASE(REAL_ROUND)  //TODO

      /* ignored */
      IGNORE_CASE(ARRAY_SELECT)
      IGNORE_CASE(ARRAY_BOOL_SELECT)
      IGNORE_CASE(ARRAY_STORE)

      default:
        ASS_REP(theory->isInterpretedNumber(orig), "unexpected interpreted function: " + orig->toString())
        return TermList(Term::create(orig, args));

    }

  } else {
      return TermList(Term::create(orig, args));
  }
}


#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}
