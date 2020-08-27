#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/Set.hpp"
#include "Lib/STL.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

class TermListReplacement : public TermTransformer {
public:
  TermListReplacement(TermList o, TermList r) : _o(o), _r(r) {}
  TermList transformSubterm(TermList trm) override;
private:
  TermList _o;
  TermList _r;
};

class TermOccurrenceReplacement : public TermTransformer {
public:
  TermOccurrenceReplacement(const DHMap<TermList, TermList>& r,
                            const DHMap<TermList, DHSet<unsigned>*>& o) : _r(r), _o(o), _c() {}
  TermList transformSubterm(TermList trm) override;

private:
  const DHMap<TermList, TermList>& _r;
  const DHMap<TermList, DHSet<unsigned>*>& _o;
  DHMap<TermList, unsigned> _c;
};

class VarShiftReplacement : public TermTransformer {
public:
  VarShiftReplacement(unsigned shift) : _shift(shift) {}
  TermList transformSubterm(TermList trm) override;

private:
  unsigned _shift;
};

class VarReplacement : public TermTransformer {
public:
  VarReplacement(DHMap<unsigned, unsigned>& varMap, unsigned& v) : _varMap(varMap), _v(v) {}
  TermList transformSubterm(TermList trm) override;

private:
  DHMap<unsigned, unsigned>& _varMap;
  unsigned& _v;
};

class IteratorByInductiveVariables
{
public:
  IteratorByInductiveVariables(Term* term,
                               const DArray<bool>& indVars)
    : _it(term), _indVarIt(indVars), _c(0)
  {}

  bool hasNext();
  TermList next();
  unsigned count();

private:
  Term::Iterator _it;
  DArray<bool>::Iterator _indVarIt;
  unsigned _c;
};

class RDescription {
public:
  CLASS_NAME(RDescription);
  USE_ALLOCATOR(RDescription);

  RDescription(List<TermList>* recursiveCalls,
               TermList step,
               Formula* cond);

  vstring toString() const;
  List<TermList>::Iterator getRecursiveCalls() const;
  TermList getStep() const;

private:
  List<TermList>* _recursiveCalls;
  TermList _step;
  Formula* _condition;
};

class RDescriptionInst {
public:
  CLASS_NAME(RDescriptionInst);
  USE_ALLOCATOR(RDescriptionInst);

  RDescriptionInst(List<DHMap<TermList, TermList>>* recursiveCalls,
                   DHMap<TermList, TermList> step,
                   Formula* cond);

  List<DHMap<TermList, TermList>>*& getRecursiveCalls();
  DHMap<TermList, TermList>& getStep();

  vstring toString() const;

private:
  List<DHMap<TermList, TermList>>* _recursiveCalls;
  DHMap<TermList, TermList> _step;
  Formula* _condition;
};

class InductionTemplate {
public:
  CLASS_NAME(InductionTemplate);
  USE_ALLOCATOR(InductionTemplate);

  InductionTemplate();

  void addRDescription(RDescription desc);
  void postprocess();

  const DArray<bool>& getInductionVariables() const;
  List<RDescription>::Iterator getRDescriptions() const;

  vstring toString() const;

private:
  List<RDescription>* _rDescriptions;
  DArray<bool> _inductionVariables;
};

class InductionScheme {
public:
  InductionScheme();

  void init(Term* term, List<RDescription>::Iterator rdescIt, const DArray<bool>& indVars);
  void addRDescriptionInstance(RDescriptionInst inst);
  void setMaxVar(unsigned maxVar);

  List<RDescriptionInst>::RefIterator getRDescriptionInstances() const;
  unsigned getMaxVar() const;

  vstring toString() const;

private:
  List<RDescriptionInst>* _rDescriptionInstances;
  unsigned _maxVar;
};

class InductionHelper {
public:
  static void preprocess(Problem& prb);
  static void filterSchemes(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& primarySchemes,
    vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& secondarySchemes);
  static void filterSchemes(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& schemes);
  static void filterFlawedSchemes(vvector<InductionScheme>& schemes,
    const DHMap<TermList, DHSet<unsigned>*>& activeOccurrenceMap,
    const DHMap<TermList, unsigned>& occurrenceMap);

  static bool canInductOn(TermList t);
  static bool isTermAlgebraCons(TermList t);
  static vvector<TermList> getInductionTerms(TermList t);
  static DHSet<TermList> getInductionTerms(const vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& schemes);

private:
  static void preprocess(UnitList*& units);
  static void processBody(TermList& body, TermList& header, InductionTemplate*& templ);

  static void processCase(const unsigned recFun, TermList& body, List<TermList>*& recursiveCalls);
  static unsigned findMatchedArgument(unsigned matched, TermList& header);

  static bool checkSubsumption(const InductionScheme& sch1, const InductionScheme& sch2, bool onlyCheckIntersection = false);
};

} // Shell

#endif