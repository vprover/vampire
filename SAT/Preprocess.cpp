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
 * @file SAT/Preprocess.cpp
 * Implements class Preprocess.
 */

#include "SATClause.hpp"
#include "SATInference.hpp"

#include "Preprocess.hpp"

namespace SAT
{

/**
 * If clause is a tautology, destroy it and return 0.
 * If clause contains duplicate literals, remove them and return
 * modified clause.
 * If none of the above applies, return the original clause object,
 * possibly with modified literal order.
 *
 * If we're removing a duplicate literal and @c cl contains an inference
 * object, create inference for the new clause as well. If it does not
 * have inference object, destroy the original clause.
 */
SATClause* Preprocess::removeDuplicateLiterals(SATClause* cl)
{
  CALL("Preprocess::removeDuplicateLiterals(SATClause*)");

  unsigned clen=cl->length();

  cl->sort();

  unsigned duplicate=0;
  for(unsigned i=1;i<clen;i++) {
    if((*cl)[i-1].var()==(*cl)[i].var()) {
      if((*cl)[i-1].polarity()==(*cl)[i].polarity()) {
        //We must get rid of the first occurrence of the duplicate (at i-1). Removing
        //the second would make us miss the case when there are three duplicates.
        std::swap((*cl)[duplicate], (*cl)[i-1]);
        duplicate++;
      } else {
        //delete tautology clauses
        cl->destroy();
        return 0;
      }
    }
  }
  if(duplicate) {
    unsigned newLen=clen-duplicate;
    SATClause* cl2=new(newLen) SATClause(newLen, true);

    for(unsigned i=0;i<newLen;i++) {
      (*cl2)[i]=(*cl)[duplicate+i];
    }
    cl2->sort();
    if(cl->inference()) {
      SATInference* cl2Inf = new PropInference(cl);
      cl2->setInference(cl2Inf);
    }
    else {
      cl->destroy();
    }
    cl=cl2;
  }
  return cl;
}

}; //namespace SAT
