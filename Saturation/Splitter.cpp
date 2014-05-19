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
  _ansLitMgr = _sa->getAnswerLiteralManager();
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
 * Return true if splitting is to be performed only if all
 * resulting clauses contain less positive literals than
 * the original one.
 */
bool Splitter::splitPositive()
{
  return false;//getOptions().splitPositive(); - no longer an option, should remove this function
}

/**
 * Return true if @b cl fulfills the constraints for clauses
 * to be split.
 */
bool Splitter::splittingAllowed(Clause* cl)
{
  CALL("Splitter::splittingAllowed");

 // if(getOptions().splitInputOnly() && !cl->isInput()) {
 //   return false;
 // }

 // if(getOptions().splitGoalOnly() && cl->inputType()!=Unit::CONJECTURE) {
 //   return false;
 // }

 // both of these options have been removed - perhaps remove splittingAllowed 

  return true;
}

bool Splitter::isAnswerLiteral(Literal* lit)
{
  CALL("Splitter::isAnswerLiteral");

  return _ansLitMgr && _ansLitMgr->isAnswerLiteral(lit);
}

bool Splitter::isSpecial(Literal* lit)
{
  CALL("Splitter::isSpecial");

  Signature::Symbol* predSym = env.signature->getPredicate(lit->functor());

  return lit->color()==COLOR_TRANSPARENT &&
    (!getOptions().showSymbolElimination() || lit->skip()) &&
    (!predSym->cfName()) && (!isAnswerLiteral(lit));
}

/**
 * Return false for literals that cannot have a splitting component
 * consisting only of them
 */
bool Splitter::canStandAlone(Literal* lit)
{
  if(lit->isNegative() && splitPositive()) {
    return false;
  }
  return true;
}

/**
 * Return true if there are can be literals that cannot stand alone
 */
bool Splitter::standAloneObligations()
{
  return splitPositive();
}


/**
 * Takes Clause cl and attempts to split it into Components i.e. produces C1...Cn = cl such that
 * all Ci's have a pairwise disjoint set of variables and no Ci can be split further - the
 * splitting is maximal.
 *
 * Returns true if this is possible and false otherwise. The result is placed in acc.
 *
 * The putSpecialsTogether option does not appear to be used. What does it do?
 *
 * This is implemented using the Union-Find algorithm.
 *
 * Comment by Giles. 
 */
bool Splitter::getComponents(Clause* cl, Stack<CompRec>& acc, bool putSpecialsTogether)
{
  CALL("Splitter::doSplitting");
  ASS_EQ(acc.size(), 0);

  if(!splittingAllowed(cl)) {
    return false;
  }

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
    if( putSpecialsTogether && isSpecial(lit) ) {
      if(coloredMaster==-1) {
	coloredMaster=i;
      } else {
	//colored literals must be in one component
	components.doUnion(coloredMaster, i);
      }
    }
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

  if(standAloneObligations() && compCnt>1) {

    //we will join components without literals that cannot stand alone
    //to ones that have such (an example of a literal that cannot stand
    //alone is a negative literal when splitPositive() is true)

    IntUnionFind::ComponentIterator cit(components);

    int someCompEl=-1;
    bool someCompOK=false;
    while(cit.hasNext()) {
      IntUnionFind::ElementIterator elit=cit.next();

      int compEl=elit.next();
      if(someCompEl==-1) {
	someCompEl=compEl;
      }
      bool saok=false; //ok to stand alone
      for(;;) {
	if(canStandAlone((*cl)[compEl])) {
	  saok=true;
	  break;
	}
	if(!elit.hasNext()) {
	  break;
	}
	compEl=elit.next();
      }
      if(!saok || !someCompOK) {
	components.doUnion(compEl, someCompEl);
	if(saok) {
	  someCompOK=true;
	}
      }
    }

    //recompute the components
    components.evalComponents();
    compCnt=components.getComponentCount();
  }

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
