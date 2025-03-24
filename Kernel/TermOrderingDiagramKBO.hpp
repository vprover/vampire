/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TermOrderingDiagramKBO__
#define __TermOrderingDiagramKBO__

#include "Forwards.hpp"

#include "TermOrderingDiagram.hpp"

namespace Kernel {

using namespace Lib;

/**
 * Runtime specialized KBO ordering check, based on the linear KBO check
 * also implemented in @b KBO.
 */
class TermOrderingDiagramKBO
: public TermOrderingDiagram
{
public:
  TermOrderingDiagramKBO(const Ordering& ord) : TermOrderingDiagram(ord) {}

  void processTermNode() override;
};

}
#endif
