#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"

namespace Shell {

class RecursiveCase {
public:
  RecursiveCase(Kernel::List<Kernel::TermList>* hypotheses, Kernel::TermList step);

  Lib::vstring toString() const;

private:
  Kernel::List<Kernel::TermList>* _hypotheses;
  Kernel::TermList _step;
};

class InductionScheme {
public:
  CLASS_NAME(InductionScheme);
  USE_ALLOCATOR(InductionScheme);

  InductionScheme();

  void addBaseCase(Kernel::TermList c);
  void addRecursiveCase(RecursiveCase c);

  Lib::vstring toString() const;

private:
  Kernel::List<Kernel::TermList>* _baseCases;
  Kernel::List<RecursiveCase>* _recursiveCases;
};

class InductionHelper {
public:
  static void preprocess(Kernel::Problem& prb);

private:
  static void preprocess(Kernel::UnitList*& units);
  static void processBody(Kernel::TermList& body, Kernel::TermList& header, InductionScheme*& scheme);

  static bool processCase(const unsigned recFun, Kernel::TermList& body, Kernel::List<Kernel::TermList>*& hypotheses);
  static unsigned findMatchedArgument(unsigned matched, Kernel::TermList& header);
};

} // Shell

#endif