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
 * @file InductionSchemeGenerator.hpp
 * Defines classes for generating induction schemes from function terms
 */

#ifndef __InductionSchemeGenerator__
#define __InductionSchemeGenerator__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "InductionPreprocessor.hpp"
#include "Lib/STL.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

/**
 * Replaces a subset of occurrences for given TermLists
 */
class TermOccurrenceReplacement : public TermTransformer {
public:
  TermOccurrenceReplacement(const vmap<TermList, TermList>& r,
                            const DHMap<TermList, DHSet<unsigned>*>& o,
                            const DHMap<TermList, unsigned>& oc, unsigned& v,
                            vmap<TermList, TermList>& r_g,
                            bool replaceSkolem = false)
                            : _r(r), _o(o), _oc(oc), _c(), _v(v), _r_g(r_g),
                              _replaceSkolem(replaceSkolem) {}
  TermList transformSubterm(TermList trm) override;

private:
  const vmap<TermList, TermList>& _r;          // replacements
  const DHMap<TermList, DHSet<unsigned>*>& _o; // set of occurrences to be replaced
  const DHMap<TermList, unsigned>& _oc;
  DHMap<TermList, unsigned> _c;                // current occurrence counts
  unsigned& _v;
  vmap<TermList, TermList>& _r_g;               // generalized replacements
  bool _replaceSkolem;
};

/**
 * Replaces all free variables of terms with new ones.
 * This is needed to ensure we have the minimum number of variables
 * in the induction hypothesis.
 */
class VarReplacement : public TermTransformer {
public:
  VarReplacement(DHMap<unsigned, unsigned>& varMap, unsigned& v) : _varMap(varMap), _v(v) {}
  TermList transformSubterm(TermList trm) override;

private:
  DHMap<unsigned, unsigned>& _varMap; // already replaced vars
  unsigned& _v;                       // current minimal unused var
};

inline TermList applyVarReplacement(TermList t, VarReplacement& vr) {
  return t.isVar() ? vr.transformSubterm(t)
    : TermList(vr.transform(t.term()));
}

class VarShiftReplacement : public TermTransformer {
public:
  VarShiftReplacement(unsigned shift) : _shift(shift) {}
  TermList transformSubterm(TermList trm) override;

private:
  unsigned _shift;
};

/**
 * Stores an instance for an RDescription which
 * consists of all substitutions in the step case
 * and the corresponding recursive calls. This
 * more general representation has the potential
 * to store merged instances as well.
 */
struct RDescriptionInst {
  RDescriptionInst() = default;
  RDescriptionInst(vvector<vmap<TermList, TermList>>&& recursiveCalls,
                   vmap<TermList, TermList>&& step)
    : _recursiveCalls(recursiveCalls), _step(step) {}
  bool contains(const RDescriptionInst& other) const;

  vvector<vmap<TermList, TermList>> _recursiveCalls;
  vmap<TermList, TermList> _step;
};

/**
 * An instantiated induction template for a term.
 */
struct InductionScheme {
  bool init(const vvector<TermList>& argTerms, const InductionTemplate& templ);
  void init(vvector<RDescriptionInst>&& rdescs);
  void clean();
  InductionScheme makeCopyWithVariablesShifted(unsigned shift) const;
  bool checkWellFoundedness();
  bool checkWellFoundedness(
    vvector<pair<vmap<TermList,TermList>&,vmap<TermList,TermList>&>> relations,
    vset<TermList> inductionTerms);

  vvector<RDescriptionInst> _rDescriptionInstances;
  unsigned _maxVar;
  vset<TermList> _inductionTerms;
};

ostream& operator<<(ostream& out, const InductionScheme& scheme);

/**
 * This class instantiates the induction templates from a literal
 * we want to induct on. Afterwards, stores these and filters them.
 * Also stores all active occurrences of possible induction terms.
 */
struct InductionSchemeGenerator {
  ~InductionSchemeGenerator();

  void generatePrimary(Clause* premise, Literal* lit);
  void generateSecondary(Clause* premise, Literal* lit);
  vvector<pair<Formula*, vmap<Literal*, pair<Literal*, Clause*>>>> instantiateSchemes();

  vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>> _primarySchemes;
  vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>> _secondarySchemes;
  DHMap<Literal*, DHMap<TermList, DHSet<unsigned>*>*> _actOccMaps;
  DHMap<Literal*, DHMap<TermList, unsigned>*> _currOccMaps;

private:
  bool generate(Clause* premise, Literal* lit,
    vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& schemes,
    bool returnOnMatch);
  bool process(TermList curr, bool active,
    Stack<bool>& actStack, Clause* premise, Literal* lit,
    vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& schemes,
    bool returnOnMatch);
  pair<Formula*, vmap<Literal*, pair<Literal*, Clause*>>> instantiateScheme(unsigned index) const;
};

} // Shell

#endif
