
/*
 * File InductionHelper.hpp.
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
/**
 * @file InductionHelper.hpp
 * Defines helper classes for induction and recursive functions
 */

#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/STL.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

/**
 * TermTransformer subclass for any TermList to TermList replacement
 */
class TermListReplacement : public TermTransformer {
public:
  TermListReplacement(TermList o, TermList r) : _o(o), _r(r) {}
  TermList transformSubterm(TermList trm) override;
private:
  TermList _o; // to be replaced
  TermList _r; // replacement
};

/**
 * Replaces a subset of occurrences for given TermLists
 */
class TermOccurrenceReplacement : public TermTransformer {
public:
  TermOccurrenceReplacement(const vmap<TermList, TermList>& r,
                            const DHMap<TermList, DHSet<unsigned>*>& o,
                            const DHMap<TermList, unsigned>& oc,
                            bool replaceSkolem, unsigned& v) : _r(r), _o(o), _oc(oc),
                              _c(), _replaceSkolem(replaceSkolem), _v(v), _r_g() {}
  TermList transformSubterm(TermList trm) override;

private:
  const vmap<TermList, TermList>& _r;          // replacements
  const DHMap<TermList, DHSet<unsigned>*>& _o; // set of occurrences to be replaced
  const DHMap<TermList, unsigned>& _oc;
  DHMap<TermList, unsigned> _c;                // current occurrence counts
  bool _replaceSkolem;
  unsigned& _v;
  vmap<TermList, TermList> _r_g;               // generalized replacements
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

/**
 * Iterator that only iterates through the active
 * occurrences of an inductive function header.
 */
class IteratorByInductiveVariables
{
public:
  IteratorByInductiveVariables(Term* term,
                               const vvector<bool>& indVars)
    : _it(term), _indVarIt(indVars.cbegin()), _end(indVars.cend())
  {}

  bool hasNext();
  TermList next();

private:
  Term::Iterator _it;
  vvector<bool>::const_iterator _indVarIt;
  vvector<bool>::const_iterator _end;
};

/**
 * Stores the template for a recursive case
 * This includes:
 * - the step case
 * - the recursive calls
 *   (if not present it is a base case)
 */
struct RDescription {
  RDescription(const vvector<TermList>& recursiveCalls,
               TermList step)
    : _recursiveCalls(recursiveCalls), _step(step) {}

  RDescription(TermList step)
    : _recursiveCalls(), _step(step) {}

  vvector<TermList> _recursiveCalls;
  TermList _step;
};

ostream& operator<<(ostream& out, const RDescription& rdesc);

/**
 * Stores an instance for an RDescription which
 * consists of all substitutions in the step case
 * and the corresponding recursive calls. This
 * more general representation has the potential
 * to store merged instances as well.
 */
struct RDescriptionInst {
  RDescriptionInst(vvector<vmap<TermList, TermList>>&& recursiveCalls,
                   vmap<TermList, TermList>&& step)
    : _recursiveCalls(recursiveCalls), _step(step) {}

  vvector<vmap<TermList, TermList>> _recursiveCalls;
  vmap<TermList, TermList> _step;
};

ostream& operator<<(ostream& out, const RDescriptionInst& inst);

/**
 * Corresponds to a recursive function definition.
 * Stores the RDescriptions and the active positions
 * (i.e. the induction variables) of the function.
 */
struct InductionTemplate {
  void postprocess();

  vvector<RDescription> _rDescriptions;
  vvector<bool> _inductionVariables;
};

ostream& operator<<(ostream& out, const InductionTemplate& templ);

/**
 * An instantiated induction template for a term.
 */
struct InductionScheme {
  bool init(Term* term, vvector<RDescription>& rdescs, const vvector<bool>& indVars);

  vvector<RDescriptionInst> _rDescriptionInstances;
  unsigned _maxVar;
};

ostream& operator<<(ostream& out, const InductionScheme& scheme);

/**
 * This class generates the induction templates based on
 * the marked recursive function definitions from the parser.
 */
class InductionPreprocessor {
public:
  void preprocess(Problem& prb);
private:
  void preprocess(UnitList* units);
  void processBody(TermList& body, TermList header, InductionTemplate& templ);

  void processCase(const unsigned recFun, TermList& body, vvector<TermList>& recursiveCalls);
  unsigned findMatchedArgument(unsigned matched, TermList& header);
};

/**
 * This class instantiates the induction templates from a literal
 * we want to induct on. Afterwards, stores these and filters them.
 * Also stores all active occurrences of possible induction terms.
 */
struct InductionSchemeGenerator {
  ~InductionSchemeGenerator();

  bool generate(Literal* lit);
  void filter();

  vvector<InductionScheme> _schemes;
  DHMap<TermList, DHSet<unsigned>*> _actOccMap;
  DHMap<TermList, unsigned> _currOccMap;

private:
  bool process(TermList curr, bool active, Stack<bool>& actStack);
};

} // Shell

#endif
