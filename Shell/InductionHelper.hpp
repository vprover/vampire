#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/Set.hpp"
#include "Lib/STL.hpp"

namespace Shell {

using TermPosition = Lib::vvector<unsigned>;

Lib::vstring positionToString(const TermPosition& pos);

class PositionalTermReplacement {
public:
  PositionalTermReplacement(Kernel::Term* o, Kernel::TermList r, TermPosition p) : _o(o), _r(r), _p(p) {} 
  Kernel::TermList replaceIn(Kernel::TermList trm);
private:
  Kernel::TermList replaceIn(Kernel::TermList trm, TermPosition rest);

  Kernel::Term* _o;
  Kernel::TermList _r;
  TermPosition _p;
};

class VarReplacement : public Kernel::TermTransformer {
public:
  VarReplacement(unsigned var, Kernel::TermList r) : _v(var), _r(r) {}
  Kernel::TermList transformSubterm(Kernel::TermList trm) override;

private:
  unsigned _v;
  Kernel::TermList _r;
};

class IteratorByInductiveVariables
{
public:
  IteratorByInductiveVariables(Kernel::Term* term,
                               const Lib::DArray<bool>& indVars)
    : _it(term), _indVarIt(indVars)
  {}

  bool hasNext();
  Kernel::TermList next();

private:
  Kernel::Term::Iterator _it;
  Lib::DArray<bool>::Iterator _indVarIt;
};

class RDescription {
public:
  RDescription(Kernel::List<Kernel::TermList>* recursiveCalls,
               Kernel::TermList step,
               Kernel::Formula* cond);

  Lib::vstring toString() const;
  Kernel::List<Kernel::TermList>::Iterator getRecursiveCalls() const;
  Kernel::TermList getStep() const;

private:
  Kernel::List<Kernel::TermList>* _recursiveCalls;
  Kernel::TermList _step;
  Kernel::Formula* _condition;
};

class InductionTemplate {
public:
  CLASS_NAME(InductionTemplate);
  USE_ALLOCATOR(InductionTemplate);

  InductionTemplate();

  void addRDescription(RDescription desc);
  void postprocess();

  const Lib::DArray<bool>& getInductionVariables() const;
  Kernel::List<RDescription>::Iterator getRDescriptions() const;

  Lib::vstring toString() const;

private:
  Kernel::List<RDescription>* _rDescriptions;
  Lib::DArray<bool> _inductionVariables;
};

class InductionScheme {
public:
  CLASS_NAME(InductionScheme);
  USE_ALLOCATOR(InductionScheme);

  InductionScheme(Kernel::Term* t, TermPosition pos, InductionTemplate* templ);

  void addTermPosPair(Kernel::Term* t, TermPosition pos);
  void addActiveOccurrences(Lib::vmap<Kernel::TermList, Lib::vvector<TermPosition>> m);

  Lib::List<pair<Kernel::Term*,TermPosition>>::Iterator getTermPosPairs() const;
  InductionTemplate* getTemplate() const;
  Lib::vmap<Kernel::TermList, Lib::vvector<TermPosition>> getActiveOccurrences() const;

  Lib::vstring toString() const;

private:
  Lib::List<pair<Kernel::Term*,TermPosition>>* _termPosPairs;
  InductionTemplate* _templ;
  Lib::vmap<Kernel::TermList, Lib::vvector<TermPosition>> _activeOccurrences;
};

class InductionHelper {
public:
  static void preprocess(Kernel::Problem& prb);
  static void filterSchemes(Lib::List<InductionScheme*>*& schemes);

private:
  static void preprocess(Kernel::UnitList*& units);
  static void processBody(Kernel::TermList& body, Kernel::TermList& header, InductionTemplate*& templ);

  static void processCase(const unsigned recFun, Kernel::TermList& body, Kernel::List<Kernel::TermList>*& recursiveCalls);
  static unsigned findMatchedArgument(unsigned matched, Kernel::TermList& header);

  static bool checkSubsumption(InductionScheme* sch1, InductionScheme* sch2);
  static Lib::List<Kernel::Term*>* getSubstitutedTerms(Kernel::Term* term, Kernel::Term* step,
                                                  Kernel::Term* recursiveCall, const Lib::DArray<bool>& indVars);
  static bool checkAllContained(Lib::List<Kernel::Term*>* lst1, Lib::List<Kernel::Term*>* lst2);
};

} // Shell

#endif