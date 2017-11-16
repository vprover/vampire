
/*
 * File SymbolDefinitionInlining.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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
    SymbolDefinitionInlining(unsigned symbol, Formula::VarList* bindingVariables, TermList binding, unsigned freshVarOffset)
            : _isPredicate(binding.isTerm() && binding.term()->isBoolean()), _symbol(symbol),
              _bindingVariables(bindingVariables), _binding(binding),
              _bound(0), _counter(0), _freshVarOffset(freshVarOffset), _varRenames(0) {}

    Formula* process(Formula* formula);
    FormulaList* process(FormulaList* formulas);
    TermList process(TermList ts);

    List<pair<unsigned, unsigned>>* variableRenamings() { return _varRenames; };

  private:
    const bool _isPredicate;
    const unsigned _symbol;
    const Formula::VarList* _bindingVariables;
    const TermList _binding;
    Formula::VarList* _bound;

    TermList substitute(Term::Iterator tit);

    bool mirroredTuple(Term* tuple, TermList &tupleConstant);

    unsigned _counter;
    unsigned _freshVarOffset;
    List<pair<unsigned, unsigned>>* _varRenames;

    void collectBoundVariables(TermList);
    void collectBoundVariables(Term*);
    void collectBoundVariables(Formula*);

    Set<Formula*> _superformulas;
};

#endif // __SymbolDefinitionInlining__
