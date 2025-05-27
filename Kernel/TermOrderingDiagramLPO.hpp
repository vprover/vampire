/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TermOrderingDiagramLPO__
#define __TermOrderingDiagramLPO__

#include "Forwards.hpp"

#include "TermOrderingDiagram.hpp"

namespace Kernel {

using namespace Lib;
using namespace std;

class TermOrderingDiagramLPO
: public TermOrderingDiagram
{
public:
  TermOrderingDiagramLPO(const Ordering& ord) : TermOrderingDiagram(ord) {}

  void processTermNode() override;
};

}
#endif
