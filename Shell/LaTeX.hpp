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

#include "Kernel/Connective.hpp"
#include "Kernel/InferenceStore.hpp"

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

  std::string header();
  std::string footer();
  std::string refutationToString(Unit* ref);

  std::string toString(const Term&) const;
  std::string toString(const std::string& funOrPred,const TermList& args) const;
  std::string toString(Unit*);
private:
  std::string varToString(unsigned num) const;
  std::string toString(TermList*,bool single=false) const;
  std::string toString(Literal*) const;
  std::string toString(Clause*);
  std::string toString(Formula*) const;
  std::string toString(Formula*, Connective c) const;

  std::string getClauseLatexId(Unit* cs);

  //std::string splittingToString(InferenceStore::SplittingRecord*);
  std::string toStringAsInference(Unit*);
  std::string toStringAsInference(Unit* cs, InferenceStore::FullInference* inf);

  std::string symbolToString (unsigned num, bool pred) const;


}; // class LaTeX

}

#endif // _LaTeX__
