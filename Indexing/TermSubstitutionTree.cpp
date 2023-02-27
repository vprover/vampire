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

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

TermSubstitutionTree::TermSubstitutionTree(Shell::Options::UnificationWithAbstraction uwa, bool uwaPostpro, bool extra)
: SubstitutionTree()
, _mismatchHandler(uwa)
, _uwaPostpro(uwaPostpro)
, _extra(extra)
{ }


} // namespace  Indexing
