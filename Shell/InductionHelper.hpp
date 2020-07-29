#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/Set.hpp"

namespace Shell {

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

  InductionScheme(Kernel::Term* t, InductionTemplate* templ);

  Kernel::Term* getTerm() const;
  InductionTemplate* getTemplate() const;

  Lib::vstring toString() const;

private:
  Kernel::Term* _t;
  InductionTemplate* _templ;
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