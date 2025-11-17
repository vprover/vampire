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
 * @file AnswerLiteralManager.hpp
 * Defines class AnswerLiteralManager.
 */

#ifndef __AnswerLiteralManager__
#define __AnswerLiteralManager__

#include <vector>

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

/*
* If the given clause only contains answer literals, resolved them all away
* (formally via URR) by using the into-the-search-space-not-inserted ANSWER_LITERAL_RESOLVERs.
* the resulting clause is empty (modulo splits, which we tolarate).
*/
class AnswerLiteralResolver
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

}

namespace Shell {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class AnswerLiteralManager
{
public:
  friend class Inferences::AnswerLiteralResolver;
  /**
   * There should be at most one AnswerLiteralManager instance in the whole wide world.
   * Depending on env.options this will be
   * - either AnswerLiteralManager proper (for QuestionAnsweringMode::PLAIN)
   * - or a SynthesisALManager (for QuestionAnsweringMode::SYNTHESIS)
   */
  static AnswerLiteralManager* getInstance();

  void tryOutputAnswer(Clause* refutation, std::ostream& out);

  virtual ~AnswerLiteralManager() {}

  virtual bool tryGetAnswer(Clause* refutation, Stack<Clause*>& answer);

  void addAnswerLiterals(Problem& prb);
  bool addAnswerLiterals(UnitList*& units);

  virtual void onNewClause(Clause* cl) {}

  // The following function currently only make sense in SYNTHESIS:
  virtual Clause* recordAnswerAndReduce(Clause* cl) { return nullptr; };
  virtual Literal* makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit) { return nullptr; };

  /**
  * Record an association between a skolem symbol and the pair <the variable it replaces, in which formula>
  */
  void recordSkolemsOrigin(unsigned skSymb, unsigned var, Unit* unit) {
    ALWAYS(_skolemsOrigin.insert(skSymb,std::make_pair(var,unit)));
  }

protected:
  static TermList possiblyEvaluateAnswerTerm(TermList);

  /**
   * Tell the concrete implementation (our descentants) that we have just introduced
   * a new skolem symbol term skT to replace var in the conjecture/question;
   * Ideally ("the user might expect"), the var should be referred to as vName in the answers.
   */
  virtual void recordSkolemBinding(Term* skT,unsigned var,std::string vName) = 0;
  virtual bool closeFreeVariablesForPrinting() { return false; };
  virtual void optionalAnswerPrefix(std::ostream& out) {};
  virtual std::string postprocessAnswerString(std::string answer) { return answer; };

  Clause* getRefutation(Clause* answer);
  Literal* getAnswerLiteral(VList* vars,SList* srts,Formula* f);

private:
  Unit* tryAddingAnswerLiteral(Unit* unit);

  Clause* getResolverClause(unsigned pred);

  /**
   * So that for every answer-predicate-symbol (key)
   * we can retrieve the unit for which it was introduced
   * and the Literal that got injected into the conjecture
   * (which, in particular, has the variables for arguments
   * as they were in the conecture).
   */
  DHMap<unsigned, std::pair<Unit*,Literal*>> _originUnitsAndInjectedLiterals;

  DHMap<unsigned, Clause*> _resolverClauses;

  DHMap<unsigned,std::pair<unsigned,Unit*>> _skolemsOrigin;
};

class PlainALManager : public AnswerLiteralManager
{
protected:
  void recordSkolemBinding(Term*,unsigned,std::string) override;
  bool closeFreeVariablesForPrinting() override { return true; };
  void optionalAnswerPrefix(std::ostream& out) override;
  std::string postprocessAnswerString(std::string answer) override;
private:
  Stack<std::pair<Term*, std::string>> _skolemNames;
};

typedef std::pair<unsigned, Term*> Binding; 
typedef List<Binding> BindingList;

struct SkolemTracker { // used for tracking skolem terms in the structural induction axiom (recursive program synthesis)
  Binding binding;
  unsigned constructorId = 0; // A skolem constant will be considered computable only in the constructorId'th arg of rec(.)-term
  bool recursiveCall = false; // Whether the constant corresponds to a recursive call result
  unsigned indexInConstructor = 0; // The index of the variable/Skolem in the constructor OR if 'recursiveCall' is true, to which argument of the constructor the recursive call coresponds to.
  unsigned recFnId = 0; // ID number of the associated rec-function

  SkolemTracker() {}

  SkolemTracker(Binding b, unsigned c, bool rc, unsigned i, unsigned rf = 0) : binding(b), constructorId(c), recursiveCall(rc), indexInConstructor(i), recFnId(rf) {}

  std::string toString() const {
    std::string s;
    s += "SkolemTracker(";
    s += "var=X" + Int::toString(binding.first);
    s += ", skolem=";
    s += (binding.second ? binding.second->toString() : "");
    s += ", cnstrID=";
    s += Int::toString(constructorId);
    s += ", recursiveCall=";
    s += recursiveCall ? "true" : "false";
    s += ", idxInCons=";
    s += Int::toString(indexInConstructor);
    s += ", recFnId=";
    s += Int::toString(recFnId) + ")";
    return s;
  }
};

class SynthesisALManager : public AnswerLiteralManager
{
private:
  typedef DHMap<unsigned /*recFnId*/, DHMap<unsigned /*var*/, SkolemTracker>> RecursionMappings;
public:
  bool tryGetAnswer(Clause* refutation, Stack<Clause*>& answer) override;
  void onNewClause(Clause* cl) override;

  Clause* recordAnswerAndReduce(Clause* cl) override;

  Literal* makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit) override;

  // Register the skolem symbol of `recTerm` as rec-symbol, and add information about skolem constants from `binding` into `incompleteTrackers` and store them.
  void registerSkolemSymbols(Term* recTerm, const Substitution& subst, const std::vector<Term*>& functionHeadsByConstruction, std::vector<SkolemTracker>& incompleteTrackers, const VList* us);

  bool isRecTerm(const Term* t) const;

  bool hasRecTerm(Literal* lit);

  const SkolemTracker* getSkolemTracker(unsigned skolemFunctor) const;

  void outputRecursiveFunctions() { _skolemReplacement.outputRecursiveFunctions(); }

  unsigned numInputSkolems() { return _skolemReplacement.numInputSkolems(); }

  void printRecursionMappings();
  void printSkolemTrackers();

  static void pushEqualityConstraints(LiteralStack* ls, Literal* thenLit, Literal* elseLit);

  bool isFunctionComputable(unsigned functor) const;
  bool isPredicateComputable(unsigned functor) const;

  bool addDeclaredSymbolAnnotatedAsUncomputable(std::pair<unsigned, bool> p) { return _annotatedUncomputable.insert(p); }
  bool addIntroducedComputableSymbol(std::pair<unsigned, bool> p) { return _introducedComputable.insert(p); }

  bool isComputableOrVar(const Term* t) const;
  bool isComputableOrVar(const Literal* l) const;
  bool isComputable(const Term* t) const {
    ASS(t);
    return t->ground() && isComputableOrVar(t);
  }
  bool isComputable(const Literal* l) const {
    ASS(l);
    return l->ground() && isComputableOrVar(l);
  }
  bool isComputable(const Clause* c) const;

protected:
  void recordSkolemBinding(Term*,unsigned,std::string) override;

private:
  class ConjectureSkolemReplacement : public BottomUpTermTransformer {
   public:
    ConjectureSkolemReplacement() {}

    struct Function {
      Function() = default;
      Function(unsigned recFunctor, ConjectureSkolemReplacement* replacement);
      void addCases(Term* t);
      std::string toString() const {
        std::string s;
        std::string fname = env.signature->getFunction(_functor)->name();
        ASS(_cases.size() == _caseHeads->size());
        for (unsigned i = 0; i < _cases.size(); ++i) {
          s += fname + "(" + (*_caseHeads)[i]->toString();
          s += ") = " + _cases[i].toString() + "\n";
        }
        return s;
      }
      unsigned _functor;
      DArray<TermList> _cases;
      std::vector<Term*>* _caseHeads;
      // Mappings of skolems to terms they should be replaced with then construcing the functions for each case.
      DHMap<unsigned, DHMap<Term*, TermList>> _skolemToTermListForCase;
      // A union of replacements for all cases (for convenience).
      DHMap<Term*, TermList> _skolemToTermList;
    };

    void bindSkolemToTermList(Term* t, TermList&& tl);
    TermList transformTermList(TermList tl, TermList sort);
    void addCondPair(unsigned fn, unsigned pred) { _condFnToPred.insert(fn, pred); }
    void associateRecMappings(RecursionMappings* m, DHMap<unsigned, std::vector<Term*>>* f) { _recursionMappings = m; _functionHeads = f;}
    unsigned numInputSkolems() { return _numInputSkolems; }
    void outputRecursiveFunctions();

    DHMap<unsigned, std::vector<Term*>>* _functionHeads;
    const RecursionMappings* _recursionMappings;

   protected:
    TermList transformSubterm(TermList trm) override;

   private:
    unsigned _numInputSkolems = 0;
    // Mapping of input skolems to input variables.
    DHMap<Term*, TermList> _skolemToTermList;
    // Map from functions to predicates they represent in answer literal conditions
    DHMap<unsigned, unsigned> _condFnToPred;
    // Recursive functions indexed by their function symbol number.
    DHMap<unsigned, Function*> _functions; 

    // Term replacement based on a simple mapping with no additional logic.
    class SimpleSkolemReplacement : public TermTransformer {
     public:
      SimpleSkolemReplacement(DHMap<Term*, TermList>* m) : _skolemToTermList(m) {}
      void setMap(DHMap<Term*, TermList>* m) { _skolemToTermList = m; }
     protected:
      TermList transformSubterm(TermList trm) override {
        if (trm.isTerm()) {
          TermList* res = _skolemToTermList->findPtr(trm.term());
          if (res) {
            return *res;
          }
        }
        return trm;
      }
     private:
      DHMap<Term*, TermList>* _skolemToTermList;
    };

  };

  bool computableOrVarHelper(const Term* t, DHMap<unsigned, unsigned>* recAncestors) const;

  void getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Stack<Unit*>& conjectures, DHSet<Unit*>& allProofUnits);

  Formula* getConditionFromClause(Clause* cl);

  Term* translateToSynthesisConditionTerm(Literal* l);

  static Term* createRegularITE(Term* condition, TermList thenBranch, TermList elseBranch, TermList branchSort);

  static unsigned getITEFunctionSymbol(TermList sort) {
    std::string name = "$ite_" + sort.toString();
    bool added = false;
    unsigned fn = env.signature->addFunction(name, 3, added);
    if (added) {
      Signature::Symbol* sym = env.signature->getFunction(fn);
      sym->setType(OperatorType::getFunctionType({AtomicSort::defaultSort(), sort, sort}, sort));
    }
    return fn;
  }

  ConjectureSkolemReplacement _skolemReplacement;

  List<std::pair<unsigned,std::pair<Clause*, Literal*>>>* _answerPairs = nullptr;

  Literal* _lastAnsLit = nullptr;

  // All SkolemTrackers created during the proof search indexed first by the rec-function symbol number and then by the variable number.
  RecursionMappings _recursionMappings;
  // All SkolemTrackers created during the proof search indexed by the skolem function symbol number.
  DHMap<unsigned, SkolemTracker*> _skolemTrackers;
  // Function heads corresponding to all rec-symbols created in Induction, indexed by the rec-function symbol number.
  DHMap<unsigned, std::vector<Term*>> _functionHeads;

  // Sets of <functor, isPredicate> pairs representing symbols that are:
  // 1. Marked as uncomputable in the input file
  DHSet<std::pair<unsigned, bool>> _annotatedUncomputable;
  // 2. symbols introduced during proving, yet computable
  DHSet<std::pair<unsigned, bool>> _introducedComputable;
};

}

#endif // __AnswerLiteralManager__
