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
 * @file RobSubstitution.hpp
 * Defines class RobSubstitution.
 *
 */

#ifndef __HOLMatching__
#define __HOLMatching__

#if VHOL

#include "Forwards.hpp"

#include "Term.hpp"

#include "Kernel/RobSubstitution.hpp"


namespace Kernel
{

using namespace Indexing;

namespace UnificationAlgorithms {


/** At the moment, the classes below don't contain much
 *  logic and could easily be moved in HOLUnification.
 *  However, I am keeping them as separate classes in case
 *  I ever add pattern matching in the future which will probably require 
 *  big changes */
class HOLInstantiation {
public:

  using Constraint = UnificationConstraint<TermList,VarBank>;

  static bool match(TermList base, TermList instance, RobSubstitutionTL* sub, VarBank baseBank)
  { return sub->match(base, instance, baseBank); }

  void initSub(RobSubstitutionTL* sub) const { sub->setOutputIndex(VarBank::RESULT_BANK); }

  bool associate(unsigned specialVar, TermList node, RobSubstitutionTL* sub);

  SubstIterator postprocess(RobSubstitutionTL* sub, TermList t, TermList sort)
  { return pvi(getSingletonIterator(sub)); }

  bool usesUwa() const { return false; }  
};

class HOLGeneralisation {
public:

  void initSub(RobSubstitutionTL* sub) const { sub->setOutputIndex(VarBank::QUERY_BANK); }

  bool associate(unsigned specialVar, TermList node, RobSubstitutionTL* sub);

  SubstIterator postprocess(RobSubstitutionTL* sub, TermList t, TermList sort)
  { return pvi(getSingletonIterator(sub)); }

  bool usesUwa() const { return false; }  
};

}

}

#endif

#endif
