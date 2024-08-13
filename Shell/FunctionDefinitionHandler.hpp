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
 * @file FunctionDefinitionHandler.hpp
 * Defines helper classes for induction templates and preprocessing
 */

#ifndef __FunctionDefinitionHandler__
#define __FunctionDefinitionHandler__

#include "Forwards.hpp"
#include "Indexing/CodeTreeInterfaces.hpp"
#include "Kernel/TermTransformer.hpp"
#include "TermAlgebra.hpp"

namespace Shell {

using namespace Indexing;
using namespace Kernel;

/**
 * Corresponds to the branches of a function definition,
 * including recursive calls and the active argument positions
 * which are not variables in some branch.
 */
struct InductionTemplate {
  USE_ALLOCATOR(InductionTemplate);
  InductionTemplate() = default;
  InductionTemplate(const Term* t);

  void addBranch(std::vector<Term*>&& recursiveCalls, Term* header);
  bool finalize();
  const std::vector<bool>& inductionPositions() const { return _indPos; }
  bool matchesTerm(Term* t, std::vector<Term*>& inductionTerms) const;

  /**
   * Stores the template for a recursive case
   * This includes:
   * - the step case
   * - the recursive calls
   *   (if not present it is a base case)
   */
  struct Branch {
    Branch(std::vector<Term*>&& recursiveCalls, Term*&& header)
      : _recursiveCalls(recursiveCalls), _header(header) {}

    bool contains(const Branch& other) const;

    std::vector<Term*> _recursiveCalls;
    Term* _header;
  };

  const std::vector<Branch>& branches() const { return _branches; }

  std::string toString() const;

  unsigned _functor;
  unsigned _arity;
  bool _isLit;
  OperatorType* _type;

private:
  bool checkUsefulness() const;
  bool checkWellFoundedness();
  void checkWellDefinedness();

  std::vector<Branch> _branches;
  std::vector<bool> _indPos;
};

class FunctionDefinitionHandler
{
public:
  USE_ALLOCATOR(FunctionDefinitionHandler);

  bool static isHandlerEnabled(const Options& opts)
  {
    return opts.functionDefinitionRewriting() ||
      opts.inductionOnActiveOccurrences() ||
      opts.structInduction()==Options::StructuralInductionKind::RECURSION;
  }

  /* has to be called before using other functionality of the handler */
  void initAndPreprocessEarly(Problem& prb);
  void initAndPreprocessLate(Problem& prb,const Options& opts);

  void addFunctionBranch(Term* header, TermList body);
  void addPredicateBranch(Literal* header, const LiteralStack& conditions);

  auto getGeneralizations(TypedTermList t)
  {
    if (_is.isEmpty()) {
      return Lib::VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>>::getEmpty();
    }
    return _is->getGeneralizations(t, true);
  }

  InductionTemplate* getInductionTemplate(Term* t) {
    auto fn = t->functor();
    auto st = t->isLiteral() ? SymbolType::PRED : SymbolType::FUNC;
    return _templates.findPtr(std::make_pair(fn, st));
  }

private:
  Lib::ScopedPtr<CodeTreeTIS<TermLiteralClause>> _is;
  Lib::DHMap<std::pair<unsigned, SymbolType>, InductionTemplate> _templates;
};

/**
 * This class generates the induction templates based on
 * the marked recursive function definitions from the parser.
 */
struct InductionPreprocessor {
  static bool checkWellFoundedness(const std::vector<std::pair<Term*,Term*>>& relatedTerms);
  static bool checkWellDefinedness(const std::vector<Term*>& cases, std::vector<std::vector<TermList>>& missingCases);
};

} // Shell

#endif
