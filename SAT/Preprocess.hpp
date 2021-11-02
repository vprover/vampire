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
 * @file SAT/Preprocess.hpp
 * Defines class Preprocess.
 */


#ifndef __SATPreprocess__
#define __SATPreprocess__

#include "Forwards.hpp"

namespace SAT {

class Preprocess
{
public:
  static SATClause* removeDuplicateLiterals(SATClause* cl);
};

};

#endif /* __SATPreprocess__ */
