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
 * @file FiniteModelMultiSorted.hpp
 * Defines class for finite models
 *
 * @since 6/01/2016 Manchester
 * @author Giles
 */

#ifndef __FiniteModelMultiSorted__
#define __FiniteModelMultiSorted__

#include "Lib/DHMap.hpp"
#include "Lib/Exception.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Term.hpp"


namespace FMB {

using namespace Lib;
using namespace Kernel;

/**
 * Thrown by the evaluation the moment it needs a value the model does not have.
 * What that means depends on where the model came from: a model loaded from a file
 * is simply partial (a user error), while a model we have just built ourselves being
 * partial is a bug -- so the two callers of evaluate() catch this and say so.
 */
class UndefinedValueException : public Lib::Exception {
public:
  explicit UndefinedValueException(const std::string& symbolName)
   : Exception("no value for " + symbolName), _symbolName(symbolName) {}

  const std::string& symbolName() const { return _symbolName; }
private:
  std::string _symbolName;
};

// Temporary, assert-like sanity instrument: when 1, a single-strategy fmb run snapshots the
// parsed input (see preprocessProblem in vampire.cpp) and, at the end of onModelFound,
// checks the constructed model against it -- a false original unit raises USER_ERROR.
// To be set to 0 (or removed) once the symbolic-definitions work has been stress-tested.
#define FMB_CHECK_MODEL_AGAINST_INPUT 1

/**
 *
 *
 */
class FiniteModelMultiSorted {
  // the domain size of each vampire sort; 0 means this model has nothing to say about that
  // sort (it is not printed, and no represented symbol mentions it) -- where a value of such
  // a sort is nevertheless called for, it behaves as a one-element domain (cf. domainSize)
  DArray<unsigned> _sizes;

  inline static constexpr char INTP_UNDEF = 0;
  inline static constexpr char INTP_FALSE = 1;
  inline static constexpr char INTP_TRUE = 2;

  // per-symbol tables holding the interpretations of functions and predicates;
  // an empty table means the symbol is not represented explicitly
  // (it was eliminated during preprocessing, or is simply unused)
  DArray<DArray<unsigned>> _f_tables;
  DArray<DArray<char>> _p_tables; // values INTP_UNDEF / INTP_FALSE / INTP_TRUE

  bool funRepresented(unsigned f) const { return _f_tables[f].size() > 0; }
  bool predRepresented(unsigned p) const { return _p_tables[p].size() > 0; }

  DHMap<unsigned,Problem::FunDef*> _symbolicFuns;
  DHMap<unsigned,Problem::PredDef*> _symbolicPreds;

  // the recorded symbolic definition of an unrepresented symbol;
  // an implicitly eliminated symbol (no record) gets a trivial definition created
  // (and remembered) on first demand, so that printing and evaluation agree on it
  Problem::FunDef* symbolicFunDef(unsigned f);
  Problem::PredDef* symbolicPredDef(unsigned p);

  // uses _sizes to fillup _f_tables and _p_tables from scratch
  // (only symbols with usageCnt()>0 get a table)
  void initTables();

public:

  // sortSizes is a map from vampire sorts (defined in Kernel/Sorts) to the size of that sort
  FiniteModelMultiSorted(DArray<unsigned> sortSizes) : _sizes(std::move(sortSizes)) {
    initTables();
  }

  // Assume def is an equality literal with a
  // function application on lhs and constant on rhs
  void addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res);
  // Assume def is non-equality ground literal
  void addPredicateDefinition(unsigned f, const DArray<unsigned>& args, bool res);

  bool evaluate(Unit* unit);

  /**
   * The parser puts $true / $false in term position into a special FORMULA term (they are
   * formulas in TPTP, and only FOOL lets them stand as terms), while everything downstream --
   * this model included -- knows them as the ordinary constants FOOLElimination introduces.
   * Map the former to the latter; any other term passes through unchanged. Used where a model
   * is read rather than evaluated, i.e. where we need the constant and not its value.
   */
  static TermList deFool(TermList tl);

  // the domain element $true (or $false) sits on in this model
  unsigned boolValue(bool isTrue);

  void eliminateSortFunctionsAndPredicates(const Stack<unsigned>& sortFunctions, const Stack<unsigned>& sortPredicates);
  void restoreEliminatedDefinitions(Kernel::Problem* prob);

  std::string toString();

private:
  unsigned evaluateTerm(TermList, const DHMap<unsigned,unsigned>& subst);
  bool evaluateLiteral(Literal*, const DHMap<unsigned,unsigned>& subst);
  bool evaluateFormula(Formula*, DHMap<unsigned,unsigned>& subst);

  void restoreEliminatedFunDef(Problem::FunDef*);
  void restoreEliminatedPredDef(Problem::PredDef*);
  void restoreGlobalPredicateFlip(Problem::GlobalFlip*);
  void restoreViaCondFlip(Problem::CondFlip*);

  // give an unrepresented symbol an explicit table again, filled by evaluating its
  // symbolic definition (trivially, if there is no record); needed by the flips,
  // which cannot operate on a symbolic representation
  void materializeFun(unsigned f);
  void materializePred(unsigned p);

  // make p, and everything a recorded definition says about p, explicit, so that the
  // flip about to be replayed really does change the model on p alone;
  // false if the model has nothing to say about p yet and the flip should be skipped
  bool prepareForFlip(unsigned p);

  std::string prepend(const char* prefix, std::string name) {
    if (name.empty()) {
      return std::string(prefix);
    } else if(name[0] == '$') {
      return std::string("'") + prefix + name + "'";
    } else if (name[0] == '\'') {
      std::string dequoted = name.substr(1, name.length() - 1);
      return std::string("'") + prefix + dequoted;
    } else {
      return prefix + name;
    }
  }
  std::string append(std::string name, const char* suffix) {
    if (name.empty()) {
      return std::string(suffix);
    } else if(name[0] == '$') {
      return std::string("'") + name + suffix + "'";
    } else if (name[0] == '\'') {
      std::string dequoted = name.substr(0, name.length() - 1);
      return dequoted + suffix + "'";
    } else {
      return name + suffix;
    }
  }
};

} // namespace FMB
#endif
