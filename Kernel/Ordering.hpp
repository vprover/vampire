/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Ordering.hpp
 * Defines (abstract) class Ordering for simplification orderings
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#ifndef __Ordering__
#define __Ordering__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Comparison.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/DArray.hpp"
#include "Kernel/Term.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Portability.hpp"

namespace Kernel {


namespace PredLevels {
  constexpr static int MIN_USER_DEF = 1; // equality has level 0, inequalities have level 1
  constexpr static int EQ = 0;
  constexpr static int INEQ = 0;
};

using namespace Shell;

/**
 * An abstract class for simplification orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class Ordering
{
public:
  /**
   * Represents the results of ordering comparisons
   *
   * Values of elements must be equal to values of corresponding elements
   * in the @c ArgumentOrderVals enum, so that one can convert between the
   * enums using static_cast.
   */
  enum [[nodiscard]] Result {
    GREATER=1,
    LESS=2,
    GREATER_EQ=3,
    LESS_EQ=4,
    EQUAL=5,
    INCOMPARABLE=6
  };

  friend std::ostream& operator<<(std::ostream& out, Kernel::Ordering::Result const& r)
  {
    switch (r) {
      case Kernel::Ordering::Result::GREATER: return out << "GREATER";
      case Kernel::Ordering::Result::LESS: return out << "LESS";
      case Kernel::Ordering::Result::GREATER_EQ: return out << "GREATER_EQ";
      case Kernel::Ordering::Result::LESS_EQ: return out << "LESS_EQ";
      case Kernel::Ordering::Result::EQUAL: return out << "EQUAL";
      case Kernel::Ordering::Result::INCOMPARABLE: return out << "INCOMPARABLE";
    }
    ASSERTION_VIOLATION
    return out << "UNKNOWN";
  }

  Ordering();
  Ordering(Ordering&&) = default;
  Ordering& operator=(Ordering&&) = default;
  virtual ~Ordering();

  /** Return the result of comparing @b l1 and @b l2 */
  virtual Result compare(Literal* l1,Literal* l2) const = 0;
  /** Return the result of comparing terms (not term lists!)
   * @b t1 and @b t2 */
  virtual Result compare(TermList t1,TermList t2) const = 0;
  /** Same as @b compare, for applied (substituted) terms. */
  virtual Result compare(AppliedTerm t1, AppliedTerm t2) const = 0;
  /** Optimised function used for checking that @b t1 is greater than @b t2,
   * under some substitutions captured by @b AppliedTerm. */
  virtual bool isGreater(AppliedTerm t1, AppliedTerm t2) const = 0;

  virtual void show(std::ostream& out) const = 0;

  static bool isGorGEorE(Result r) { return (r == GREATER || r == GREATER_EQ || r == EQUAL); }

  void removeNonMaximal(LiteralList*& lits) const;

  static Result fromComparison(Comparison c);
  static Comparison intoComparison(Result c);

  static Result reverse(Result r)
  {
    switch(r) {
    case GREATER:
      return LESS;
    case GREATER_EQ:
      return LESS_EQ;
    case LESS:
      return GREATER;
    case LESS_EQ:
      return GREATER_EQ;
    case EQUAL:
    case INCOMPARABLE:
      return r;
    default:
      ASSERTION_VIOLATION;
    }
  }
  static const char* resultToString(Result r);

  static Ordering* create(Problem& prb, const Options& opt);

  static bool trySetGlobalOrdering(OrderingSP ordering);
  static Ordering* tryGetGlobalOrdering();

  Result getEqualityArgumentOrder(Literal* eq) const;
protected:

  Result compareEqualities(Literal* eq1, Literal* eq2) const;

private:

  // enum ArgumentOrderVals {
  //   /**
  //    * Values representing order of arguments in equality,
  //    * to be stores in the term sharing structure.
  //    *
  //    * The important thing is that the UNKNOWN value is
  //    * equal to 0, as this will be the default value inside
  //    * the term objects
  //    *
  //    * Values of elements must be equal to values of corresponding elements
  //    * in the @c Result enum, so that one can convert between the
  //    * enums using static_cast.
  //    */
  //   AO_UNKNOWN=0,
  //   AO_GREATER=1,
  //   AO_LESS=2,
  //   AO_GREATER_EQ=3,
  //   AO_LESS_EQ=4,
  //   AO_EQUAL=5,
  //   AO_INCOMPARABLE=6
  // };


  class EqCmp
  {
  public:
    USE_ALLOCATOR(EqCmp);

#define BUF_SIZE 128

    EqCmp()
    {
#if VDEBUG
    inUse=false;
#endif
    }

    Result compareEqualities(Ordering const& ord, Literal* eq1, Literal* eq2) const;


#if VDEBUG
    mutable bool inUse;
#endif

  private:

    Result compare_s1Gt1(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1GEt1(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1It1(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1It1_s2It2(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1Gt1_s2It2(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1Gt1_s2Lt2(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1Gt1_s2LEt2(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1GEt1_s2It2(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1Gt1_s1It2_s2It1(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1Gt1_s1GEt2_s2It1(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1Gt1_s1GEt2_s2It2(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1GEt1_s1GEt2_s2It1(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1GEt1_s1It2_s2It1(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1GEt1_s2LEt2(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1Gt1_s1GEt2_s2Lt2(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;
    Result compare_s1GEt1_s1GEt2_s2LEt1(Ordering const& ord, TermList s1,TermList s2,TermList t1,TermList t2) const;

    mutable TermList s1,s2,t1,t2;
   
  };

  /** Object used to compare equalities */
  std::unique_ptr<EqCmp> _eqCmp;

  /**
   * We store orientation of equalities in this ordering inside
   * the term sharing structure. Setting an ordering to be global
   * does not change the behavior of Vampire, but may lead to
   * better performance, as the equality orientation will be cached
   * inside the sharing structure.
   */
  static OrderingSP s_globalOrdering;
}; // class Ordering

// orderings that rely on symbol precedence
class PrecedenceOrdering
: public Ordering
{
public:
  PrecedenceOrdering(PrecedenceOrdering&&) = default;
  PrecedenceOrdering& operator=(PrecedenceOrdering&&) = default;
  Result compare(Literal* l1, Literal* l2) const override;
  void show(std::ostream&) const override;
  virtual void showConcrete(std::ostream&) const = 0;

  static DArray<int> testLevels();

#ifdef VDEBUG
  bool usesQkboPrecedence() const { return _qkboPrecedence; }
#endif
  static DArray<int> funcPrecFromOpts(Problem& prb, const Options& opt);
  static DArray<int> predPrecFromOpts(Problem& prb, const Options& opt);

  Result comparePredicatePrecedences(unsigned fun1, unsigned fun2) const;
protected:
  // l1 and l2 are not equalities and have the same predicate
  virtual Result comparePredicates(Literal* l1,Literal* l2) const = 0;
  PrecedenceOrdering(const DArray<int>& funcPrec, const DArray<int>& typeConPrec, 
                     const DArray<int>& predPrec, const DArray<int>& predLevels, 
                     bool reverseLCM, bool qkboPrecedence = false);
  PrecedenceOrdering(Problem& prb, const Options& opt, const DArray<int>& predPrec, bool qkboPrecedence = false);
  PrecedenceOrdering(Problem& prb, const Options& opt, bool qkboPrecedence = false);


  static DArray<int> typeConPrecFromOpts(Problem& prb, const Options& opt);
  static DArray<int> predLevelsFromOptsAndPrec(Problem& prb, const Options& opt, const DArray<int>& predicatePrecedences);

  Result compareFunctionPrecedences(unsigned fun1, unsigned fun2) const;
  Result compareTypeConPrecedences(unsigned tyc1, unsigned tyc2) const;

  int predicatePrecedence(unsigned pred) const;
  int predicateLevel(unsigned pred) const;

  /** number of predicates in the signature at the time the order was created */
  unsigned _predicates;
  /** number of functions in the signature at the time the order was created */
  unsigned _functions;
  /** Array of predicate levels */
  DArray<int> _predicateLevels;
  /** Array of predicate precedences */
  DArray<int> _predicatePrecedences;
  /** Array of function precedences */
  DArray<int> _functionPrecedences;
  /** Array of type con precedences */
  DArray<int> _typeConPrecedences;

  static void checkLevelAssumptions(DArray<int> const&);

  bool _reverseLCM;
  bool _qkboPrecedence;
};


} // namespace Kernel

#endif
