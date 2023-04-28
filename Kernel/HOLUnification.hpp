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

#ifndef __HOLUnification__
#define __HOLUnification__

#if VHOL

#include "Forwards.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"
#include "Term.hpp"
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

namespace Kernel
{

using namespace Indexing;

namespace UnificationAlgorithms {


class HOLUnification {

  bool unifyTreeTerms(TermList t1, TermList t2, bool splittable, RobSubstitutionTL* sub);

  // TODO if we implement solid fragment, this will not work...
  enum OracleResult
  {
    SUCCESS=1,
    FAILURE=2,
    OUT_OF_FRAGMENT=3
  };  

  OracleResult fixpointUnify(TermList var, TermList t, RobSubstitutionTL* sub);

  using UnificationConstraint = UnificationConstraint<TermList,VarBank>;

public:
  HOLUnification() { }

  bool associate(unsigned specialVar, TermList node, bool splittable, RobSubstitutionTL* sub);
  SubstIterator unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck = false);
  SubstIterator postprocess(RobSubstitutionTL*);

  // method used to decide whether to return all children of a node during tree
  // traversal or only the children with same top
  bool usesUwa() const { return false; }  
};

}

}

#endif

#endif
