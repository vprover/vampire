#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Lib/Set.hpp"

namespace Shell {

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

  Lib::Set<unsigned>* getInductionVariables() const;

  Lib::vstring toString() const;

private:
  Kernel::List<RDescription>* _rDescriptions;
  Lib::Set<unsigned>* _inductionVariables;
};

class InductionHelper {
public:
  static void preprocess(Kernel::Problem& prb);

private:
  static void preprocess(Kernel::UnitList*& units);
  static void processBody(Kernel::TermList& body, Kernel::TermList& header, InductionTemplate*& templ);

  static void processCase(const unsigned recFun, Kernel::TermList& body, Kernel::List<Kernel::TermList>*& recursiveCalls);
  static unsigned findMatchedArgument(unsigned matched, Kernel::TermList& header);
};

} // Shell

#endif