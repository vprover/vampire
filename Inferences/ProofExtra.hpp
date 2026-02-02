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
 * @file ProofExtra.hpp
 * Various objects that include "extra information" about an inference,
 * e.g. selected literals, unifier, etc.
 *
 * @since 09/09/2024 Oxford
 */

#ifndef __Inferences_ProofExtra__
#define __Inferences_ProofExtra__


#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Lib/ProofExtra.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include <initializer_list>
#include <vector>

namespace Inferences {

// inferences that use one literal from their main premise
struct LiteralInferenceExtra : public InferenceExtra {
  LiteralInferenceExtra(Kernel::Literal *selected) : selectedLiteral(selected) {}

  void output(std::ostream &out) const override;

  // the literal from the main premise
  Kernel::Literal *selectedLiteral;
};

// inferences that use one literal from their side premise
struct TwoLiteralInferenceExtra : public InferenceExtra {

  struct SynthesisExtra {
    SynthesisExtra(Kernel::Literal *conditionLiteral, Kernel::Literal *thenLiteral, Kernel::Literal* elseLiteral) : condition(conditionLiteral), thenLit(thenLiteral), elseLit(elseLiteral) {}
    Kernel::Literal *condition;
    Kernel::Literal *thenLit;
    Kernel::Literal *elseLit;
  };

  TwoLiteralInferenceExtra(Kernel::Literal *selected, Kernel::Literal *other, Kernel::Literal *condition = nullptr, Kernel::Literal* thenLit = nullptr, Kernel::Literal* elseLit = nullptr)
    : selectedLiteral(selected), otherLiteral(other), synthesisExtra(condition, thenLit, elseLit) {}

  void output(std::ostream &out) const override;

  // selected literal
  LiteralInferenceExtra selectedLiteral;
  // the literal from the side premise
  Kernel::Literal *otherLiteral;
  // synthesis information: condition and branch literals for if-then-else
  SynthesisExtra synthesisExtra;
};

struct RewriteInferenceExtra : public InferenceExtra {
  RewriteInferenceExtra(Kernel::TermList lhs, Kernel::TermList target)
    : lhs(lhs), rewritten(target) {}

  void output(std::ostream &out) const override;

  // the LHS used to rewrite with
  Kernel::TermList lhs;
  // the rewritten term
  Kernel::TermList rewritten;
};

struct TwoLiteralRewriteInferenceExtra : public InferenceExtra {
  TwoLiteralRewriteInferenceExtra(
    Kernel::Literal *selected,
    Kernel::Literal *other,
    Kernel::TermList lhs,
    Kernel::TermList rewritten,
    Kernel::Literal *condition = nullptr,
    Kernel::Literal *thenLit = nullptr,
    Kernel::Literal *elseLit = nullptr)
    : selected(selected, other, condition, thenLit, elseLit), rewrite(lhs, rewritten) {}
  void output(std::ostream &out) const override;

  // selected literals
  TwoLiteralInferenceExtra selected;
  // rewrite information
  RewriteInferenceExtra rewrite;
};

struct UnifierInferenceExtra : public InferenceExtra {
  UnifierInferenceExtra(Indexing::ResultSubstitution* subst, std::initializer_list<std::pair<unsigned,VirtualIterator<unsigned>*>> banks) {
    substitutionForBanks.resize(banks.size());
    for(auto [index, iter]: banks)
    {
      unsigned int highestVar = 0;
      while(iter->hasNext()) {
        unsigned int var = iter->next();
        if(var > highestVar) {
          highestVar = var;
        }
      }
      for(unsigned v = 0; v <= highestVar; v++ ) {
        substitutionForBanks[index].emplace_back(subst->applyTo(TermList::var(v),index));
      }
    }
  }

  UnifierInferenceExtra(Kernel::RobSubstitution& subst, std::initializer_list<std::pair<unsigned,VirtualIterator<unsigned>*>> banks) {
    substitutionForBanks.resize(banks.size());
    for(auto [index, iter]: banks)
    {
      unsigned int highestVar = 0;
      while(iter->hasNext()) {
        unsigned int var = iter->next();
        if(var > highestVar) {
          highestVar = var;
        }
      }
      for(unsigned v = 0; v <= highestVar; v++ ) {
        substitutionForBanks[index].emplace_back(subst.apply(TermList::var(v),index));
      }
    }
  }

  UnifierInferenceExtra(Kernel::Substitution& subst) {
    substitutionForBanks.resize(1);
    unsigned int highestVar = 0;
    auto x = subst.items();
    while(x.hasNext()) {
      auto [var, term] = x.next();
      if(var > highestVar) {
        highestVar = var;
      }
    }
    for(unsigned v = 0; v <= highestVar; v++ ) {
      substitutionForBanks[0].emplace_back(subst.apply(v));
    }
  }
  UnifierInferenceExtra(){
  }
  void output(std::ostream &out) const override;
  // the unifier used
  
  std::vector<std::vector<Kernel::TermList>> substitutionForBanks;
};
} // namespace Inferences

#endif