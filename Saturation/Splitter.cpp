/**
 * @file Splitter.cpp
 * Implements class Splitter.
 */

#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/AnswerExtractor.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

#include "Splitter.hpp"

namespace Saturation
{

Splitter::CompRec::CompRec(Literal** lits, unsigned len)
{
  CALL("Splitter::CompRec::CompRec/2");

  _lits.loadFromIterator(getArrayishObjectIterator(lits, len));
}

void Splitter::init(SaturationAlgorithm* sa)
{
  CALL("Splitter::init");

  _sa = sa;  
}

const Options& Splitter::getOptions() const
{
  CALL("Splitter::getOptions");
  ASS(_sa);

  return _sa->getOptions();
}

/**
 * Register the reduction of the @b cl clause
 */
void Splitter::onClauseReduction(Clause* cl, Clause* premise, Clause* replacement)
{
  CALL("Splitter::onClauseReduction(Clause*,Clause*,Clause*)");
  
  if(!premise) {
    ASS(!replacement);
    return;
  }

  onClauseReduction(cl, pvi( getSingletonIterator(premise) ), replacement);
}

/**
 * Takes Clause cl and attempts to split it into Components i.e. produces C1...Cn = cl such that
 * all Ci's have a pairwise disjoint set of variables and no Ci can be split further - the
 * splitting is maximal.
 *
 * Returns true if this is possible and false otherwise. The result is placed in acc.
 *
 * This is implemented using the Union-Find algorithm.
 *
 * Comment by Giles. 
 */
bool Splitter::getComponents(Clause* cl, Stack<CompRec>& acc)
{
  CALL("Splitter::doSplitting");
  ASS_EQ(acc.size(), 0);

  unsigned clen=cl->length();
  ASS_G(clen,0);

  if(clen<=1) {
    return false;
  }

  //Master literal of an variable is the literal
  //with lowest index, in which it appears.
  static DHMap<unsigned, unsigned, IdentityHash> varMasters;
  varMasters.reset();
  IntUnionFind components(clen);
  //index of one literal that cannot be split-out, or -1 if there isn't any
  int coloredMaster=-1;

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    VariableIterator vit(lit);
    while(vit.hasNext()) {
      unsigned master=varMasters.findOrInsert(vit.next().var(), i);
      if(master!=i) {
	components.doUnion(master, i);
      }
    }
  }
  components.evalComponents();

  unsigned compCnt=components.getComponentCount();

  if(compCnt==1) {
    return false;
  }

  env.statistics->splitClauses++;
  env.statistics->splitComponents+=compCnt;

  IntUnionFind::ComponentIterator cit(components);
  ASS(cit.hasNext());
  while(cit.hasNext()) {
    IntUnionFind::ElementIterator elit=cit.next();

    acc.push(CompRec());

    while(elit.hasNext()) {
      int litIndex=elit.next();
      Literal* lit = (*cl)[litIndex];

      acc.top().add(lit);

      if(litIndex==coloredMaster) {
	acc.top().markSpecial();
      }
    }
  }
  ASS_EQ(acc.size(),compCnt);
  return true;
}

}
