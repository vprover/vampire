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

#include "Kernel/Unit.hpp"
#include "Kernel/Term.hpp"


namespace FMB {

using namespace Lib;
using namespace Kernel;

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
  DArray<unsigned> _sizes;

  inline static constexpr char INTP_UNDEF = 0;
  inline static constexpr char INTP_FALSE = 1;
  inline static constexpr char INTP_TRUE = 2;

  // per-symbol tables holding the interpretations of functions and predicates;
  // an empty table means the symbol is not represented explicitly
  // (it was eliminated during preprocessing, or is simply unused)
  DArray<DArray<unsigned>> _f_tables;
  DArray<DArray<char>> _p_tables; // 0 is undef, 1 false, 2 true

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

  // captures the encoding of a symbol's table:
  // the row index of the tuple args in the table of a symbol of type sig,
  // under the domain sizes sizes -- the first argument position changing fastest,
  // i.e. the very order in which ArgsEnumerator enumerates the tuples
  static size_t tableIndex(const DArray<unsigned>& args, const DArray<unsigned>& sizes, OperatorType* sig)
  {
    size_t idx = 0;
    size_t mult = 1;
    for(unsigned i=0;i<args.size();i++){
      idx += mult*(args[i]-1);
      unsigned s = sig->arg(i).term()->functor();
      mult *=sizes[s];
    }
    return idx;
  }

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

  void eliminateSortFunctionsAndPredicates(const Stack<unsigned>& sortFunctions, const Stack<unsigned>& sortPredicates);
  void restoreEliminatedDefinitions(Kernel::Problem* prob);

  std::string toString();

private:
  unsigned evaluateTerm(TermList, const DHMap<unsigned,unsigned>& subst);
  bool evaluateLiteral(Literal*, const DHMap<unsigned,unsigned>& subst);
  bool evaluateFormula(Formula*, DHMap<unsigned,unsigned>& subst);

  // symbols whose table entry was still undefined when evaluation read it
  // (during replay such reads consistently return the default -- function value 1, predicate false --
  // and the leftover undefined cells are made explicit at the end of restoreEliminatedDefinitions;
  // in model_check mode, on the other hand, a hit here means the model file was partial,
  // which evaluate() reports as an error)
  Set<unsigned> _implicitlyEliminatedFunctions;
  Set<unsigned> _implicitlyEliminatedPredicates;

  void restoreEliminatedFunDef(Problem::FunDef*);
  void restoreEliminatedPredDef(Problem::PredDef*);
  void restoreGlobalPredicateFlip(Problem::GlobalFlip*);
  void restoreViaCondFlip(Problem::CondFlip*);

  // give an unrepresented symbol an explicit table again, filled by evaluating its
  // symbolic definition (trivially, if there is no record); needed by the flips,
  // which cannot operate on a symbolic representation
  void materializeFun(unsigned f);
  void materializePred(unsigned p);

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
