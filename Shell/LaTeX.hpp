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
 * @file LaTeX.hpp
 * Defines a class LaTeX translating Vampire data structures
 * into LaTeX.
 *
 * @since 04/01/2004 Manchester
 */

#ifndef __LaTeX__
#define __LaTeX__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VString.hpp"

#include "Kernel/Connective.hpp"
#include "Kernel/InferenceStore.hpp"

// #include "VS/Connective.hpp"
// #include "Var.hpp"

// namespace VS {
//   class Symbol;
//   class SymbolMap;
// }

// using namespace VS;

namespace Shell {

using namespace Kernel;

/**
 * Translates Vampire refutations into LaTeX.
 * @since 04/01/2004 Manchester
 */
class LaTeX
{
public:
  LaTeX() {}

  vstring header();
  vstring footer();
  vstring refutationToString(Unit* ref);

//  LaTeX(const Options& options,const SymbolMap* map);
//  void output (const Refutation&) const;
  vstring toString(const Term&) const;
  vstring toString(const vstring& funOrPred,const TermList& args) const;
  vstring toString(Unit*);
private:
//  /** options used for output */
//  const Options& _options;
//  /** symbol map for printing atoms, functions and variables */
//  const SymbolMap* _map;
  vstring varToString(unsigned num) const;
  vstring toString(TermList*,bool single=false) const;
  vstring toString(Literal*) const;
  vstring toString(Clause*);
  vstring toString(Formula*) const;
  vstring toString(Formula*, Connective c) const;

  vstring getClauseLatexId(Unit* cs);

  //vstring splittingToString(InferenceStore::SplittingRecord*);
  vstring toStringAsInference(Unit*);
  vstring toStringAsInference(Unit* cs, InferenceStore::FullInference* inf);

  vstring symbolToString (unsigned num, bool pred) const;


}; // class LaTeX


}

#endif // _LaTeX__

