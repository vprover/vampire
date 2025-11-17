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

#include "Kernel/InductionTemplate.hpp"

namespace Shell {

using namespace Indexing;
using namespace Kernel;
using namespace Lib;

/**
 * Corresponds to the branches of a function definition,
 * including recursive calls and the active argument positions
 * which are not variables in some branch.
 */
struct RecursionTemplate {
  RecursionTemplate() = default;
  RecursionTemplate(const Term* t);

  void addBranch(std::vector<Term*>&& recursiveCalls, Term* header);
  bool finalize();
  const std::vector<bool>& inductionPositions() const { return _indPos; }

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
  const InductionTemplate* templ() const { return _templ.get(); }

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
  std::unique_ptr<const InductionTemplate> _templ;
};

class FunctionDefinitionHandler
{
public:
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
      return VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>>::getEmpty();
    }
    return _is->getGeneralizations(t, true);
  }

  const RecursionTemplate* getRecursionTemplate(Term* t) const {
    auto fn = t->functor();
    auto st = t->isLiteral() ? SymbolType::PRED : SymbolType::FUNC;
    return _templates.findPtr(std::make_pair(fn, st));
  }

  const InductionTemplate* matchesTerm(Term* t, Stack<Term*>& inductionTerms) const;

private:
  ScopedPtr<CodeTreeTIS<TermLiteralClause>> _is;
  DHMap<std::pair<unsigned, SymbolType>, RecursionTemplate> _templates;
};

/**
 * This class generates the recursion templates based on
 * the marked recursive function definitions from the parser.
 */
struct InductionPreprocessor {
  static bool checkWellFoundedness(const std::vector<std::pair<Term*,Term*>>& relatedTerms);
  static bool checkWellDefinedness(const std::vector<Term*>& cases, std::vector<std::vector<TermList>>& missingCases);
};

} // Shell

#endif
