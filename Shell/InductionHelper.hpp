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

class VarShiftReplacement : public Kernel::TermTransformer {
public:
  VarShiftReplacement(unsigned shift) : _shift(shift) {}
  Kernel::TermList transformSubterm(Kernel::TermList trm) override;

private:
  unsigned _shift;
};

class VarReplacement : public Kernel::TermTransformer {
public:
  VarReplacement(Kernel::Map<unsigned, unsigned>& varMap, unsigned& v) : _varMap(varMap), _v(v) {}
  Kernel::TermList transformSubterm(Kernel::TermList trm) override;

private:
  Kernel::Map<unsigned, unsigned>& _varMap;
  unsigned& _v;
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
  CLASS_NAME(RDescription);
  USE_ALLOCATOR(RDescription);

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

class RDescriptionInst {
public:
  CLASS_NAME(RDescriptionInst);
  USE_ALLOCATOR(RDescriptionInst);

  RDescriptionInst(Kernel::List<Kernel::vmap<Kernel::TermList, Kernel::TermList>>* recursiveCalls,
                   Kernel::vmap<Kernel::TermList, Kernel::TermList> step,
                   Kernel::Formula* cond);

  Kernel::List<Kernel::vmap<Kernel::TermList, Kernel::TermList>>*& getRecursiveCalls();
  Kernel::vmap<Kernel::TermList, Kernel::TermList>& getStep();

  Lib::vstring toString() const;

private:
  Kernel::List<Kernel::vmap<Kernel::TermList, Kernel::TermList>>* _recursiveCalls;
  Kernel::vmap<Kernel::TermList, Kernel::TermList> _step;
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

  InductionScheme();

  void init(Kernel::Term* term, Kernel::List<RDescription>::Iterator rdescIt, const Lib::DArray<bool>& indVars);
  void addActiveOccurrences(Lib::vmap<Kernel::TermList, Lib::vvector<TermPosition>> m);
  void setMaxVar(unsigned maxVar);

  Kernel::List<RDescriptionInst>::RefIterator getRDescriptionInstances() const;
  Lib::vmap<Kernel::TermList, Lib::vvector<TermPosition>> getActiveOccurrences() const;
  unsigned getMaxVar() const;

  Lib::vstring toString() const;

private:
  void replaceFreeVars(Kernel::TermList t, unsigned& currVar, Lib::Map<unsigned, unsigned>& varMap);

  Kernel::List<RDescriptionInst>* _rDescriptionInstances;
  Lib::vmap<Kernel::TermList, Lib::vvector<TermPosition>> _activeOccurrences;
  unsigned _maxVar;
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

  static bool checkSubsumption(InductionScheme* sch1, InductionScheme* sch2, bool onlyCheckIntersection = false);
  static Lib::List<Kernel::Term*>* getSubstitutedTerms(Kernel::Term* term, Kernel::Term* step,
                                                  Kernel::Term* recursiveCall, const Lib::DArray<bool>& indVars,
                                                  unsigned& currVar, Kernel::Map<pair<Kernel::Term*, unsigned>, Lib::vvector<unsigned>>& varMap);
  static bool checkAllContained(Lib::List<Kernel::Term*>* lst1, Lib::List<Kernel::Term*>* lst2, bool onlyCheckIntersection = false);
  static void mergeSchemes(InductionScheme* sch1, InductionScheme* sch2);
};

} // Shell

#endif