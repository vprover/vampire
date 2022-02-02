/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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
 * f(s1, ..., sj,t1, ..., tk) by g(A1, ..., Am, s1, ..., sj,X1, ..., Xn, t1, ..., tk) 
 * for given f, g, A1, ..., Am, and X1,...,Xn
 */
// TODO: should a combination of MatcherUtils, SubstHelper be used instead?
class SymbolOccurrenceReplacement {
  public:
    /**
     * symbol = f
     * freshApplication = g(A1, ..., Am, B1, ..., Bj,X1, ..., Xn, Y1, ..., Yk)
     * argVars = B1, ..., Bj, Y1, ..., Yk
     * isPredicate = whether or not f and g are predicate symbols
     */
    SymbolOccurrenceReplacement(bool isPredicate, Term* freshApplication, unsigned symbol, VList* argVars)
            : _isPredicate(isPredicate), _freshApplication(freshApplication), _symbol(symbol), _argVars(argVars) {
        
        if(isPredicate){
          ASS(VList::length(argVars) == env.signature->getPredicate(symbol)->arity());
        } else {
          ASS(VList::length(argVars) == env.signature->getFunction(symbol)->arity());            
        }
        // The implementation of this class doesn't requite argVars to be
        // non-empty, however, its use case expects this constraint
        //ASS(argVars || !env.signature->getFunction(symbol)->introduced());
    }
    Formula* process(Formula* formula);
    FormulaList* process(FormulaList* formulas);
    Term* process(Term* term);
    TermList process(TermList ts);

  private:
    const bool _isPredicate;
    Term* _freshApplication;
    const unsigned _symbol;
    const VList* _argVars;
};

#endif // __SymbolOccurrenceReplacement__
