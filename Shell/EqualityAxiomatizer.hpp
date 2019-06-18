
/*
 * File EqualityAxiomatizer.hpp.
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
 * @file EqualityAxiomatizer.hpp
 * Defines class EqualityAxiomatizer.
 */

#ifndef __EqualityAxiomatizer__
#define __EqualityAxiomatizer__

#include "Forwards.hpp"

#include "Lib/DHSet.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Adds specified equality axioms.
 *
 * We scan the problem and avoid adding unnecessary axioms (for functions
 * and predicates that do not appear in the problem, and for sorts that do
 * not occur in any equalities).
 */
class EqualityAxiomatizer {
private:
  Options::EqualityProxy _opt;

  typedef DHSet<unsigned> SymbolSet;
  typedef DHSet<unsigned> SortSet;

  SymbolSet _fns;
  SymbolSet _preds;
  SortSet _eqSorts;

  void saturateEqSorts();

  void addLocalAxioms(UnitList*& units, unsigned sort);
  void addCongruenceAxioms(UnitList*& units);
  Clause* getFnCongruenceAxiom(unsigned fn);
  Clause* getPredCongruenceAxiom(unsigned pred);
  bool getArgumentEqualityLiterals(BaseType* symbolType, LiteralStack& lits, Stack<TermList>& vars1,
      Stack<TermList>& vars2);

  void scan(UnitList* units);
  void scan(Literal* lit);
  UnitList* getAxioms();
public:
  /**
   * Which axioms to add. Can be one of EqualityProxy::RS, EqualityProxy::RST, EqualityProxy::RSTC.
   *
   * EqualityProxy::R is not an option, because since we're using the built-in equality literals,
   * symmetry is implicit due to normalization in term sharing.
   */
  EqualityAxiomatizer(Options::EqualityProxy opt) : _opt(opt)
  {
    ASS_REP(opt==Options::EqualityProxy::RS || opt==Options::EqualityProxy::RST || opt==Options::EqualityProxy::RSTC, static_cast<int>(opt));
  }

  void apply(Problem& prb);
  void apply(UnitList*& units);

};

}

#endif // __EqualityAxiomatizer__
