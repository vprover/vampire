#ifndef __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__
#define __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__

#include "Kernel/Clause.hpp"
#include "Lib/macro_magic.h"
#include "Lib/vstd.h"
#include "Shell/Analysis/TheorySubclauseAnalyser/AbstractLiteralContainer.hpp"
#include <iostream>

#ifdef VDEBUG
#define IF_DEBUG(...) __VA_ARGS__
#else
#define IF_DEBUG(...)
#endif

/* template stuff */
#include <functional>
#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

/* ================================================= */
/* =================== collections ================= */
/* ================================================= */
class AbsTerm;

class AbsLiteral;
AbsLiteral& create_abs_lit(bool positive, unsigned functor, vvec<refw<AbsTerm>> terms);

class ACTerm;
class AbsTerm {
public:
  static AbsTerm &from(Kernel::TermList &t);

  friend ostream &operator<<(ostream &out, const AbsTerm &t);

  virtual void normalize() = 0;
  virtual void distributeLeft() = 0;
  virtual void distributeRight() = 0;
  virtual void mergeAssoc() = 0;
  virtual void sortCommut() = 0;
  virtual void pushMinus() = 0;
  virtual void write(ostream &out) const = 0;
  using on_unsigned_t = void (*)(const ACTerm &, vvec<unsigned> &);
  /** adds all variables contained in this term to @b v, ordered as they occur
   * in the term.
   * @b onUninterpreted will be called to handle uninterpreted terms it should
   * have the signature void onUninterpreted(const ACTerm& t, vvec<unsigned>&
   * v);
   */
  virtual void vars(vvec<unsigned> &v, on_unsigned_t onUnisgned) const = 0;

  /** adds all variables contained in this term to @b v. */
  virtual void var_set(vset<unsigned> &vs) const = 0;

  /** returns all variables contained in this term to @b v. */
  vset<unsigned> var_set() const {
    vset<unsigned> out;
    var_set(out);
    return out;
  }

  /** returns all variables contained in this term , ordered as they occur in
   * the term.
   * @b onUninterpreted will be called to handle uninterpreted terms it should
   * have the signature void onUninterpreted(const ACTerm& t, vvec<unsigned>&
   * v);
   */
  vvec<unsigned> vars(on_unsigned_t onUninterpreted) const {
    vvec<unsigned> out;
    vars(out, onUninterpreted);
    return out;
  }
  friend ostream &operator<<(ostream &out, const AbsTerm &t) {
    t.write(out);
    return out;
  }

  static void term(int t);
  static AbsTerm &var(int t);
  static AbsTerm &fun(unsigned functor, vvec<refw<AbsTerm>> args);
  friend bool operator<(const AbsTerm &, const AbsTerm &);
};

enum CmpResult {
  CMP_LESS,
  CMP_GREATER,
  CMP_EQUIV,
  CMP_NONE,
};
#define EQ_CLASSES 1, 2, 3, 4

#define DECLARE_EQ_CLASS(i)                                                    \
  template <class A> struct cmp##i {                                           \
    CmpResult operator()(const A &lhs, const A &rhs) const;                    \
                                                                               \
    template <class B> CmpResult cmp(const B &lhs, const B &rhs) const {       \
      return cmp##i<B>{}(lhs, rhs);                                            \
    }                                                                          \
  };                                                                           \
                                                                               \
  struct LitEquiv##i;                                                          \
  template <> struct EquivalenceClass<LitEquiv##i> {                           \
    using less = struct {                                                      \
      bool operator()(const rc<AbsLiteral> &lhs,                               \
                      const rc<AbsLiteral> &rhs) const;                        \
    };                                                                         \
  };

MAP(DECLARE_EQ_CLASS, EQ_CLASSES)
#undef DECLARE_EQ_CLASS

using namespace Kernel;
namespace Shell {
namespace Analysis {

class TheorySubclauseAnalyser {
  CLASS_NAME(TheorySubclauseAnalyser)
  USE_ALLOCATOR(TheorySubclauseAnalyser)
public:
  TheorySubclauseAnalyser();

  ~TheorySubclauseAnalyser();

  /**
   * Adds a new clause for analysis.
   *
   * This shall be an ordenary clause. The theory subclause will be extracted
   * within this function.
   */
  void addClause(Clause &c);

  /**
   * Dumps the result of the analysis to @b ostream.
   */
  void dumpStats(std::ostream &out) const;

private:
  using literals_type = Container<rc<AbsLiteral>, Equality<rc<AbsLiteral>>>;
  literals_type _literals;

#define DECLARE_EQ_CLAS_MEMBERS(i)                                             \
  using equiv_t_##i = Container<rc<AbsLiteral>, LitEquiv##i>;                  \
  equiv_t_##i _eq##i;

  MAP(DECLARE_EQ_CLAS_MEMBERS, EQ_CLASSES)

#undef DECLARE_EQ_CLAS_MEMBERS

public:
  static TheorySubclauseAnalyser *instance;
};

} // namespace Analysis
} // namespace Shell

#endif // __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__;
