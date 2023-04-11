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
 * @file TermSubstitutionTree.cpp
 * Implements class TermSubstitutionTree.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/Term.hpp"
#include "TermSubstitutionTree.hpp"

#if VHOL
#include "Indexing/HOLSubstitutionTree.hpp"
#endif

namespace Indexing
{

using namespace Lib;
using namespace Kernel;


TermSubstitutionTree::TermSubstitutionTree(bool extra)
:  _extra(extra)
#if VHOL
  ,_tree(env.property->higherOrder() ? new HOLSubstitutionTree() : new SubstitutionTree())
#else
  ,_tree(new SubstitutionTree())
#endif
{ }

} // namespace  Indexing
