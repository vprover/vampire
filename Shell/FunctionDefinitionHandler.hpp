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
#include "Lib/STL.hpp"

namespace Shell {

using namespace Indexing;
using namespace Kernel;
using namespace Lib;

/**
 * Corresponds to the branches of a function definition.
 * Stores the branches and the active positions
 * (i.e. the changing arguments) of the function.
 */
struct InductionTemplate {
  USE_ALLOCATOR(InductionTemplate);
  InductionTemplate(const Term* t);

  void addBranch(vvector<Term*>&& recursiveCalls, Term* header);
  bool finalize();
  const vvector<bool>& inductionPositions() const { return _indPos; }
  bool matchesTerm(Term* t, vvector<Term*>& inductionTerms) const;

  /**
   * Stores the template for a recursive case
   * This includes:
   * - the step case
   * - the recursive calls
   *   (if not present it is a base case)
   */
  struct Branch {
    Branch(vvector<Term*>&& recursiveCalls, Term*&& header)
      : _recursiveCalls(recursiveCalls), _header(header) {}

    bool contains(const Branch& other) const;

    vvector<Term*> _recursiveCalls;
    Term* _header;
  };

  const vvector<Branch>& branches() const { return _branches; }

  vstring toString() const;

  const unsigned _functor;
  const unsigned _arity;
  const bool _isLit;
  const OperatorType* _type;

private:
  bool checkUsefulness() const;
  bool checkWellFoundedness();
  void checkWellDefinedness();

  vvector<Branch> _branches;
  vvector<bool> _indPos;
};

class FunctionDefinitionHandler
{
public:
  USE_ALLOCATOR(FunctionDefinitionHandler);

  struct Branch {
    Term* header;
    TermList body;
    LiteralStack literals;
  };

  void preprocess(Problem& prb);
  bool preprocess(Formula* f, Stack<Branch>& branches);
  void addFunction(const Stack<Branch>& branches, Unit* unit);

  TermQueryResultIterator getGeneralizations(TypedTermList t) {
    return _is.getGeneralizations(t, true);
  }

  InductionTemplate* getInductionTemplate(unsigned fn, bool trueFun) {
    auto it = _templates.find(std::make_pair(fn, trueFun));
    return it == _templates.end() ? nullptr : it->second;
  }

private:
  Branch substituteBoundVariable(unsigned var, TermList t, const Branch& b, TermList body);
  Branch addCondition(Literal* lit, const Branch& b, TermList body);

  CodeTreeTIS _is;
  vmap<std::pair<unsigned, bool>, InductionTemplate*> _templates;
};

/**
 * This class generates the induction templates based on
 * the marked recursive function definitions from the parser.
 */
struct InductionPreprocessor {
  static bool checkWellFoundedness(const vvector<std::pair<Term*,Term*>>& relatedTerms);
  static bool checkWellDefinedness(const vvector<Term*>& cases, vvector<vvector<TermList>>& missingCases);
};

} // Shell

#endif
