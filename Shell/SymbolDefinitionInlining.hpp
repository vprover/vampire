#ifndef __SymbolDefinitionInlining__
#define __SymbolDefinitionInlining__

#include "Forwards.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Lib/Environment.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class SymbolDefinitionInlining {
  public:
    SymbolDefinitionInlining(unsigned symbol, Formula::VarList* bindingVariables, TermList binding)
            : _isPredicate(binding.isTerm() && binding.term()->isBoolean()), _symbol(symbol),
              _bindingVariables(bindingVariables), _binding(binding) {}

    Formula* process(Formula* formula);
    FormulaList* process(FormulaList* formulas);
    TermList process(TermList ts);

  private:
    const bool _isPredicate;
    const unsigned _symbol;
    const Formula::VarList* _bindingVariables;
    const TermList _binding;

    TermList substitute(Term::Iterator tit);
};

#endif // __SymbolDefinitionInlining__