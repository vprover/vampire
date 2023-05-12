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
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"

namespace Kernel
{

using namespace Indexing;

namespace UnificationAlgorithms {


class HOLInstantiation {
public:

  static bool match(TermList term, TermList instance, RobSubstitutionTL* sub);

  void initSub(RobSubstitutionTL* sub) const { sub->setOutputIndex(VarBank::RESULT_BANK); }

  bool associate(unsigned specialVar, TermList node, bool splittable, RobSubstitutionTL* sub);

  SubstIterator postprocess(RobSubstitutionTL* sub)
  { return pvi(getSingletonIterator(sub)); }

  bool usesUwa() const { return false; }  
};

class HOLGeneralisation {
public:

  void initSub(RobSubstitutionTL* sub) const { sub->setOutputIndex(VarBank::QUERY_BANK); }

  bool associate(unsigned specialVar, TermList node, bool splittable, RobSubstitutionTL* sub);

  SubstIterator postprocess(RobSubstitutionTL* sub)
  { return pvi(getSingletonIterator(sub)); }

  bool usesUwa() const { return false; }  
};

}

}

#endif

#endif
