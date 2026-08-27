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
#include "Lib/Stack.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Term.hpp"

#include "ModelLayer.hpp"


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

  // per-symbol stacks of interpretation layers, bottom-up (see ModelLayer.hpp); the model
  // owns them. An empty stack means the symbol is not represented explicitly (it was
  // eliminated during preprocessing, or is simply unused)
  DArray<Stack<FunLayer*>> _f_layers;
  DArray<Stack<PredLayer*>> _p_layers;

  // the replay step we are at; layers built by initTables belong to model_0, so the first
  // step of restoreEliminatedDefinitions is 1 and a read as of 1 sees exactly model_0
  Timestamp _now = MODEL_ZERO+1;

  // the base explicit table of a symbol, or nullptr if it does not have one
  TableFunLayer* funTable(unsigned f) const;
  TablePredLayer* predTable(unsigned p) const;

  bool funRepresented(unsigned f) const { return funTable(f) != nullptr; }
  bool predRepresented(unsigned p) const { return predTable(p) != nullptr; }

  void deleteAllLayers();

  // uses _sizes to fillup _f_layers and _p_layers from scratch, giving each represented
  // symbol a single base table layer (only symbols with usageCnt()>0 get one)
  void initTables();

public:

  // sortSizes is a map from vampire sorts (defined in Kernel/Sorts) to the size of that sort
  FiniteModelMultiSorted(DArray<unsigned> sortSizes) : _sizes(std::move(sortSizes)) {
    initTables();
  }

  ~FiniteModelMultiSorted() { deleteAllLayers(); }

  // the layers call these back while computing their own value; a layer reads as of its own
  // birth, so that it sees the model its own replay step transforms and nothing later
  unsigned evalFun(unsigned f, const DArray<unsigned>& args, Timestamp asOf);
  char evalPred(unsigned p, const DArray<unsigned>& args, Timestamp asOf);
  unsigned domainSizeOf(unsigned sort) const;
  size_t tableIndexOf(OperatorType* sig, const DArray<unsigned>& args) const;
  // evaluate a recorded definition's body with its head's variables bound to args
  unsigned applyFunDef(Problem::FunDef* fd, const DArray<unsigned>& args, Timestamp asOf);
  bool applyPredDef(Problem::PredDef* pd, const DArray<unsigned>& args, Timestamp asOf);

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
  unsigned boolValue(bool isTrue) { return boolValue(isTrue,_now); }

  /**
   * Give every symbol the model has no explicit table for a trivial layer, so that model_0 --
   * the model the replay starts from -- says something about every symbol on every argument
   * tuple. Only a model we built ourselves gets this: one loaded from a file is legitimately
   * partial, and there the absence of any layer is the UndefinedValueException to report.
   */
  void installTrivialLayers();

  void eliminateSortFunctionsAndPredicates(const Stack<unsigned>& sortFunctions, const Stack<unsigned>& sortPredicates);
  void restoreEliminatedDefinitions(Kernel::Problem* prob);

  std::string toString();

private:
  // walk a symbol's layer stack from the top, taking the first layer that has a value for
  // args; a layer with nothing to say falls through to the one below. Falling off the
  // bottom means the model does not say what the symbol is here
  unsigned boolValue(bool isTrue, Timestamp asOf);

  unsigned evaluateTerm(TermList, const DHMap<unsigned,unsigned>& subst, Timestamp asOf);
  bool evaluateLiteral(Literal*, const DHMap<unsigned,unsigned>& subst, Timestamp asOf);
  bool evaluateFormula(Formula*, DHMap<unsigned,unsigned>& subst, Timestamp asOf);

  void restoreViaCondFlip(Problem::CondFlip*);

  // snapshot what the model currently says about an unrepresented predicate into an explicit
  // table; needed by the flips, which write values and so cannot operate on a symbolic layer
  void materializePred(unsigned p);

  // make p, and everything a recorded definition says about p, explicit, so that the
  // flip about to be replayed really does change the model on p alone;
  // false if the model has nothing to say about p yet and the flip should be skipped
  void prepareForFlip(unsigned p);

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
