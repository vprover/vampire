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
struct rect_map;

class AbsClause;
class AbsLiteral;

AbsLiteral& create_abs_lit(bool positive, unsigned functor, vvec<refw<AbsTerm>> terms);
void normalize_absliteral(AbsLiteral& lit);
bool equal_absliteral(const AbsLiteral&,const AbsLiteral&);

class ACTerm;
class AbsVarTerm;
class AbsTerm {
public:
  static AbsTerm &from(Kernel::TermList &t);
  virtual ~AbsTerm() = 0;

  friend ostream &operator<<(ostream &out, const AbsTerm &t);

  virtual void normalize() = 0;
  // virtual void rectify(rect_map& r) = 0;
  // void rectify();
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
  virtual void var_set(vset<AbsVarTerm> &vs) const = 0;

  /** returns all variables contained in this term to @b v. */
  vset<AbsVarTerm> var_set() const;

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
  virtual bool interpreted() const = 0;
  friend bool operator<(const AbsTerm &, const AbsTerm &);
};

enum CmpResult {
  CMP_LESS,
  CMP_GREATER,
  CMP_EQUIV,
  CMP_NONE,
};
#define EQ_CLASSES 4,5
#define EQ_CLASSES_ 1,4,5

#define DECLARE__LIT_EQUIV(i)                                                    \
  struct LitEquiv##i { \
    struct Config; \
    static void dump(std::ostream& out, const AbsClause&) ; \
    static CmpResult compare(AbsClause const&, AbsClause const&) ; \
    using less = struct {                                                      \
      bool operator()(const rc<AbsClause> &lhs,                               \
                      const rc<AbsClause> &rhs) const {\
        return LitEquiv##i::compare(*lhs.get(),*rhs.get()) == CMP_LESS;\
      }                        \
    };                                                                         \
  };                                                          \

MAP(DECLARE__LIT_EQUIV, EQ_CLASSES_)
#undef DECLARE_LIT_EQUIV


// template<class LitEquiv>
// struct ClauseEquiv { 
//   struct Config; 
//   static void dump(std::ostream& out, const AbsLiteral&) {
//
//   }
//   static CmpResult compare(AbsLiteral const&, AbsLiteral const&) ; 
//   using less = struct {                                                      
//     bool operator()(const rc<AbsLiteral> &lhs,                               
//                     const rc<AbsLiteral> &rhs) const {
//       return compare(*lhs.get(),*rhs.get()) == CMP_LESS;
//     }                        
//   };                                                                         
// };                                                          

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
  // using literals_type = Container<rc<AbsLiteral>, Equality<rc<AbsLiteral>>>;
  // literals_type _literals;
  size_t _total;

#define DECLARE_EQ_CLAS_MEMBERS(i)                                             \
  using equiv_t_##i = Container<rc<AbsClause>, LitEquiv##i>;                  \
  equiv_t_##i _eq##i;

  MAP(DECLARE_EQ_CLAS_MEMBERS, EQ_CLASSES_)

#undef DECLARE_EQ_CLAS_MEMBERS

public:
  static TheorySubclauseAnalyser *instance;
};

} // namespace Analysis
} // namespace Shell

#endif // __SHELL__ANALYSIS__THEORY_SUBCLAUSE_ANALYSER__;
