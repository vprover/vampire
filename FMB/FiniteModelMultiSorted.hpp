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

/**
 *
 *
 */
class FiniteModelMultiSorted {
  // the domain size of each vampire sort; 0 means this model has nothing to say about that
  // sort (no represented symbol mentions it) -- where a value of such a sort is nevertheless
  // called for, it behaves as a one-element domain (cf. domainSize), and that is also how it
  // is printed when an unrepresented symbol mentions it (see toString)
  DArray<unsigned> _sizes;

  // per-symbol stacks of interpretation layers, bottom-up (see ModelLayer.hpp); the model
  // owns them. An empty stack means the symbol is not represented explicitly (it was
  // eliminated during preprocessing, or is simply unused)
  DArray<Stack<FunLayer*>> _f_layers;
  DArray<Stack<PredLayer*>> _p_layers;

  // the replay step we are at; layers built by initTables belong to model_0, so the first
  // step of restoreEliminatedDefinitions is 1 and a read as of 1 sees exactly model_0
  Timestamp _now = MODEL_ZERO+1;

  // Which symbols the model is given an explicit table for; see the constructor. An index
  // past the end means "not used", which is the truthful answer for a symbol introduced
  // after these were collected (cf. Kernel::collectUsedSymbols).
  DArray<bool> _usedFunctions;
  DArray<bool> _usedPredicates;

  bool funUsed(unsigned f) const { return f < _usedFunctions.size() && _usedFunctions[f]; }
  bool predUsed(unsigned p) const { return p < _usedPredicates.size() && _usedPredicates[p]; }

  // the base explicit table of a symbol, or nullptr if it does not have one
  TableFunLayer* funTable(unsigned f) const;
  TablePredLayer* predTable(unsigned p) const;

  void deleteAllLayers();

  // uses _sizes to fillup _f_layers and _p_layers from scratch, giving each represented
  // symbol a single base table layer (only the used symbols get one)
  void initTables();

public:

  /**
   * sortSizes is a map from vampire sorts (defined in Kernel/Sorts) to the size of that sort.
   *
   * usedFunctions / usedPredicates say which symbols this model is about, i.e. which ones
   * get a table. Everything else gets no layer at all and the model says nothing about it
   * until some later step does. The caller has to state this because it is the only one
   * who knows: for FMB it is the symbols surviving into the clauses it encoded, for a model
   * read from a file the symbols that file mentions. (It used to be read off
   * Signature::Symbol::usageCnt, a global left behind by whichever Property scan ran last.)
   */
  FiniteModelMultiSorted(DArray<unsigned> sortSizes, DArray<bool> usedFunctions, DArray<bool> usedPredicates)
   : _sizes(std::move(sortSizes)), _usedFunctions(std::move(usedFunctions)),
     _usedPredicates(std::move(usedPredicates)) {
    initTables();
  }

  ~FiniteModelMultiSorted() {
    deleteAllLayers();
    for (Problem::PredDef* pd : iterTraits(_flipDefs.iter())) delete pd;
  }

  // does the model have an explicit table for this symbol? (i.e. was it among the used ones)
  bool funRepresented(unsigned f) const { return funTable(f) != nullptr; }
  bool predRepresented(unsigned p) const { return predTable(p) != nullptr; }

  // the layers call these back while computing their own value; a layer reads as of its own
  // birth, so that it sees the model its own replay step transforms and nothing later
  unsigned evalFun(unsigned f, const DArray<unsigned>& args, Timestamp asOf);
  char evalPred(unsigned p, const DArray<unsigned>& args, Timestamp asOf);
  unsigned domainSizeOf(unsigned sort) const;
  size_t tableIndexOf(OperatorType* sig, const DArray<unsigned>& args) const;
  // evaluate a recorded definition's body with its head's variables bound to args
  unsigned applyFunDef(Problem::FunDef* fd, const DArray<unsigned>& args, Timestamp asOf);
  bool applyPredDef(Problem::PredDef* pd, const DArray<unsigned>& args, Timestamp asOf);

  // Set one cell of f's (or p's) table, i.e. f(args) = res (or p(args) <=> res). Return what
  // the cell held before: FUNV_UNDEF (INTP_UNDEF) if it was not set yet, which is what lets a
  // model loader notice a cell given two different values
  unsigned addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res);
  char addPredicateDefinition(unsigned p, const DArray<unsigned>& args, bool res);

  // For a model loader: make a symbolic definition the whole interpretation of its head
  // symbol, which must have no layers yet. It reads the model as it stands when added, so
  // whatever its body mentions must be in place by then -- a definition after the
  // definitions it uses. The model keeps the definition but does not own it
  void addSymbolicDefinition(Problem::FunDef* fd);
  void addSymbolicDefinition(Problem::PredDef* pd);
  // For a model loader: an empty conditional-flip layer on top of p's stack, for the loader to
  // fill (CondFlipPredLayer::prescribe); a tuple it prescribes nothing for reads what is below
  CondFlipPredLayer* addCasesLayer(unsigned p);

  bool evaluate(Unit* unit);

  // can evaluate() handle this term / formula? (a parsed unit may contain FOOL constructs
  // it cannot, such as $let)
  static bool evaluable(TermList tl);
  static bool evaluable(Formula* f);

  // what a definition body mentions
  struct BodySymbols {
    Stack<unsigned> funs;
    Stack<unsigned> preds; // equality left out: it is not in the model
    Stack<unsigned> sorts; // of the variables the body quantifies over; $o for a formula in term position
  };
  // false if the body contains a special term other than a formula in term position, an
  // $ite or a $cond; then out is incomplete
  static bool collectBodySymbols(TermList body, BodySymbols& out);
  static bool collectBodySymbols(Formula* body, BodySymbols& out);

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

  // the model as TPTP, in the style -fmb_model_printing asks for
  std::string toString();

private:
  // every symbol of the input as a table of its final interpretation, and nothing else
  std::string toStringExplicit();
  // every needed version of every symbol, each printed as its own top layer
  std::string toStringLayered();

  // --- pieces both printing styles share ---

  // the TPTP names of the domain elements, per sort, 1-based; filled by printDomains
  using DomainNames = DArray<DArray<std::string>>;

  // the sort declarations, domain constants, finite_domain_* and distinct_domain_* axioms of
  // every sort sortPrinted marks
  void printDomains(std::ostream& out, const DArray<bool>& sortPrinted, DomainNames& names);
  // the name of the i-th domain element of sort s (not of $o, whose two are $true and $false)
  std::string domainConstantName(unsigned s, unsigned i);
  // the type declaration and the table of f (p), under the printed name name, of the values
  // f (p) has as of asOf
  void printFunType(std::ostream& out, unsigned f, const std::string& name);
  void printPredType(std::ostream& out, unsigned p, const std::string& name);
  void printFunTable(std::ostream& out, unsigned f, const std::string& name, Timestamp asOf, const DomainNames& names);
  void printPredTable(std::ostream& out, unsigned p, const std::string& name, Timestamp asOf, const DomainNames& names);

  // a conditional flip's layer, as the body of its version's definition (see toStringLayered)
  void printCases(std::ostream& out, unsigned p, unsigned layer, const std::string& below, const DomainNames& names);

  // --- the names of the versions toStringLayered prints ---

  // per symbol, the separator of its version names; empty while it has none to print
  DArray<std::string> _funVersionSep;
  DArray<std::string> _predVersionSep;
  void chooseVersionSeparators(const DArray<Stack<unsigned>>& funQueued, const DArray<Stack<unsigned>>& predQueued,
                               const DArray<bool>& sortPrinted);
  static std::string versionName(const std::string& base, const std::string& sep, unsigned depth);
  // the printed name of the version of a symbol whose top is the given layer of its stack
  std::string versionName(bool pred, unsigned sym, unsigned layer);

  // walk a symbol's layer stack from the top, taking the first layer that has a value for
  // args; a layer with nothing to say falls through to the one below. Falling off the
  // bottom means the model does not say what the symbol is here
  unsigned boolValue(bool isTrue, Timestamp asOf);

  unsigned evaluateTerm(TermList, const DHMap<unsigned,unsigned, FnvHash, IdentityHash>& subst, Timestamp asOf);
  bool evaluateBooleanTerm(TermList, const DHMap<unsigned,unsigned, FnvHash, IdentityHash>& subst, Timestamp asOf);
  bool evaluateLiteral(Literal*, const DHMap<unsigned,unsigned, FnvHash, IdentityHash>& subst, Timestamp asOf);
  bool evaluateFormula(Formula*, DHMap<unsigned,unsigned, FnvHash, IdentityHash>& subst, Timestamp asOf);

  void restoreViaCondFlip(Problem::CondFlip*);
  Problem::PredDef* condFlipAsDefinition(Problem::CondFlip*);
  // the definitions condFlipAsDefinition made, which the layers point to; ours to delete
  Stack<Problem::PredDef*> _flipDefs;


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
