/**
 * @file LaTeX.hpp
 * Defines a class LaTeX translating Vampire data structures
 * into LaTeX.
 *
 * @since 04/01/2004 Manchester
 */

#ifndef __LaTeX__
#define __LaTeX__

#include <string>

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

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
  LaTeX() : _nextNodeNum(0) {}

  string refutationToString(Unit* ref);

//  LaTeX(const Options& options,const SymbolMap* map);
//  void output (const Refutation&) const;
  string toString(const Term&) const;
  string toString(const string& funOrPred,const TermList& args) const;
  string toString(Unit*);
  string toString(Unit*,BDDNode*);
private:
//  /** options used for output */
//  const Options& _options;
//  /** symbol map for printing atoms, functions and variables */
//  const SymbolMap* _map;
  string varToString(unsigned num) const;
  string toString(TermList*) const;
  string toString(Literal*) const;
  string toString(Clause*);
  string toString(Clause*, BDDNode*);
  string toString(Formula*) const;
  string toString(Formula*, Connective c) const;

  string getClauseLatexId(InferenceStore::UnitSpec cs);

  string splittingToString(InferenceStore::SplittingRecord*);
  string toStringAsInference(Unit*);
  string toStringAsInference(InferenceStore::UnitSpec cs, InferenceStore::FullInference* inf);

  string symbolToString (unsigned num, bool pred) const;


  string toString(BDDNode*);
  string getBDDVarName(int var);

  Stack<string> definitionStack;
  int _nextNodeNum;
  DHMap<BDDNode*,string> _nodeNames;
}; // class LaTeX


}

#endif // _LaTeX__

