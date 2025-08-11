/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __SymbolDefinitionInlining__
#define __SymbolDefinitionInlining__

#include "Forwards.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class SymbolDefinitionInlining {
  public:
    SymbolDefinitionInlining(Term* lhs, TermList rhs, unsigned freshVarOffset)
            : _isPredicate(lhs->isBoolean()), _lhs(lhs), _rhs(rhs),
              _bound(0), _counter(0), _freshVarOffset(freshVarOffset), _varRenames(0) {}

    Formula* process(Formula* formula);
    FormulaList* process(FormulaList* formulas);
    TermList process(TermList ts);

    List<std::pair<unsigned, unsigned>>* variableRenamings() { return _varRenames; };

  private:
    const bool _isPredicate;
    const Term* _lhs;
    const TermList _rhs;
    VList* _bound;

    TermList substitute(Term::Iterator tit);

    bool mirroredTuple(Term* tuple, TermList &tupleConstant);

    unsigned _counter;
    unsigned _freshVarOffset;
    List<std::pair<unsigned, unsigned>>* _varRenames;

    void collectBoundVariables(TermList);
    void collectBoundVariables(Term*);
    void collectBoundVariables(Formula*);

    Set<Formula*> _superformulas;
};

#endif // __SymbolDefinitionInlining__
