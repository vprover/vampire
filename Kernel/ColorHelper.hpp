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
 * @file ColorHelper.hpp
 * Defines class ColorHelper.
 */

#ifndef __ColorHelper__
#define __ColorHelper__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"

namespace Kernel {

using namespace Lib;
using namespace Saturation;

class ColorHelper {
public:

  /**
   * The result may be COLOR_INVALID
   */
  static Color combine(Color c1, Color c2)
  {
    CALL("ColorHelper::combine");
    ASS(env.colorUsed || (c1|c2)!=COLOR_INVALID);
    return static_cast<Color>(c1|c2);
  }

  /**
   * Return true if colors @c c1 and @c c2 can appear together in
   * an inference.
   *
   * Function returns false iff one of the colors is @c COLOR_LEFT
   * and the other is @c COLOR_RIGHT.
   */
  static bool compatible(Color c1, Color c2) {
    CALL("ColorHelper::compatible");
    return combine(c1,c2)!=COLOR_INVALID;
  }

  static bool isTransparent(bool predicate, unsigned functor);
  static bool hasColoredPredicates(Clause* c);
  static Clause* skolemizeColoredConstants(Clause* c);
  static Clause* skolemizeColoredTerms(Clause* c);

  static void tryUnblock(Clause* c, SaturationAlgorithm* salg);

private:
  typedef DHMap<Term*, Term*> TermMap;

  static void ensureSkolemReplacement(Term* t, TermMap& map);
  static void collectSkolemReplacements(Clause* c, TermMap& map);

  static Term* applyReplacement(Term* t, TermMap& map);
  static void collectColoredConstants(Clause* c, Stack<Term*>& acc);
};

}

#endif // __ColorHelper__
