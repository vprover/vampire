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
 * @file InferenceStore.hpp
 * Defines class InferenceStore.
 */


#ifndef __InferenceStore__
#define __InferenceStore__

#include <ostream>
#include <set>
#include <vector>

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"

namespace Kernel {

using namespace Lib;

class InferenceStore
{
public:
  static InferenceStore* instance();

  void recordSplittingNameLiteral(Unit* us, Literal* lit);
  void recordIntroducedSymbol(Unit* u, const Signature::Symbol* sym);
  void recordIntroducedSkolemSymbol(Unit* u, const Signature::Symbol* sym, unsigned replacedVar, Term* symTerm);
  void recordIntroducedSplitName(Unit* u, std::string name);


  void outputUnsatCore(std::ostream& out, Unit* refutation);
  void outputProof(std::ostream& out, Unit* refutation);
  void outputProof(std::ostream& out, UnitList* units);
  /** Common proof scheduling, independent of any output format. */
  struct AbstractProofPrinter {
    AbstractProofPrinter(std::ostream& out, InferenceStore* is) : _is(is), out(out) {}
    virtual ~AbstractProofPrinter() = default;

    void scheduleForPrinting(Unit* us);
    virtual void print();

  protected:
    virtual bool hideProofStep(InferenceRule rule) { return false; }
    virtual void printStep(Unit* unit) = 0;

    struct CompareUnits {
      bool operator()(Unit* left, Unit* right) const;
    };

    InferenceStore* _is;
    std::ostream& out;
    std::set<Unit*, CompareUnits> proof;

  };

  struct ProofPrinter;

private:
  /** Shared SAT traversal; concrete printers choose their own SAT syntax. */
  struct AbstractSATProofPrinter : AbstractProofPrinter {
    using AbstractProofPrinter::AbstractProofPrinter;
    void print() override;

  protected:
    virtual void printSATStep(SAT::SATClause* clause) = 0;
  };
  struct TPTPProofPrinter;
  struct Smt2ProofCheckPrinter;
  struct ProofCheckPrinter;
  struct ProofPropertyPrinter;
  struct SMTCheckPrinter;

  AbstractProofPrinter* createProofPrinter(std::ostream& out);

  DHMultiset<unsigned, FnvHash, IdentityHash> _nextClIds;

  DHMap<unsigned, Literal*, FnvHash, IdentityHash> _splittingNameLiterals;

  typedef Stack<const Signature::Symbol*> SymbolStack;
  // unit id -> stack of introduced symbols (in order of introduction)
  DHMap<unsigned,SymbolStack, FnvHash, IdentityHash> _introducedSymbols;
  // symbol id -> existential variable name (number) that was replaced by the symbol
  DHMap<const Signature::Symbol*, unsigned, FnvHash, PtrIdentityHash> _introducedSymbolReplacedVars;
  // symbol id -> the term that is introduced when introducing the skolem symbol
  DHMap<const Signature::Symbol*, Term*, FnvHash, PtrIdentityHash> _introducedSkolemSymTerms;

  DHMap<unsigned,std::string, FnvHash, IdentityHash> _introducedSplitNames;
};

};

#endif /* __InferenceStore__ */
