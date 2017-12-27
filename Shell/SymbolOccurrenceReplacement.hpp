
/*
 * File SymbolOccurrenceReplacement.hpp.
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
#ifndef __SymbolOccurrenceReplacement__
#define __SymbolOccurrenceReplacement__

#include "Forwards.hpp"

#include "Kernel/Signature.hpp"
#include "Lib/Environment.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * A helper class that performs replacement of all terms/literals of the form
 * f(t1, ..., tk) by g(X1, ..., Xn, t1, ..., tk) for given f, g and X1,...,Xn
 */
// TODO: should a combination of MatcherUtils, SubstHelper be used instead?
class SymbolOccurrenceReplacement {
  public:
    /**
     * symbol = f
     * freshSymbol = g
     * freeVars = X1, ..., Xn
     * isPredicate = whether or not f and g are predicate symbols
     */
    SymbolOccurrenceReplacement(bool isPredicate, unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars)
            : _isPredicate(isPredicate), _symbol(symbol), _freshSymbol(freshSymbol), _freeVars(freeVars) {
        // An actual replacement should take place
        ASS_NEQ(symbol, freshSymbol);
        // The implementation of this class doesn't requite freeVars to be
        // non-empty, however, its use case expects this constraint
        ASS(freeVars || !env.signature->getFunction(symbol)->introduced());
        // Arities of symbols should coincide
        if (isPredicate) {
          ASS_EQ(env.signature->getPredicate(symbol)->arity() + Formula::VarList::length(freeVars),
                   env.signature->getPredicate(freshSymbol)->arity());
        } else {
          ASS_EQ(env.signature->getFunction(symbol)->arity() + Formula::VarList::length(freeVars),
                   env.signature->getFunction(freshSymbol)->arity());
        }
    }
    Formula* process(Formula* formula);
    FormulaList* process(FormulaList* formulas);
    Term* process(Term* term);
    TermList process(TermList ts);

  private:
    const bool _isPredicate;
    const unsigned _symbol;
    const unsigned _freshSymbol;
    const Formula::VarList* _freeVars;
};

#endif // __SymbolOccurrenceReplacement__
