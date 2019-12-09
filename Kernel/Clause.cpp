
/*
 * File Clause.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Clause.cpp
 * Implements class Clause for units consisting of clauses
 *
 * @since 18/05/2007 Manchester
 */

#include <ostream>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/BitUtils.hpp"

#include "Saturation/ClauseContainer.hpp"
#include "Saturation/Splitter.hpp"

#include "SAT/SATClause.hpp"

#include "Shell/Options.hpp"

#include "Inference.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "Clause.hpp"

#undef RSTAT_COLLECTION
#define RSTAT_COLLECTION 1

namespace Kernel
{

using namespace Lib;
using namespace Saturation;
using namespace Shell;

size_t Clause::_auxCurrTimestamp = 0;
#if VDEBUG
bool Clause::_auxInUse = false;
#endif


/** New clause */
Clause::Clause(unsigned length,InputType it,Inference* inf)
  : Unit(Unit::CLAUSE,inf,it),
    _length(length),
    _color(COLOR_INVALID),
    _input(0),
    _extensionality(false),
    _extensionalityTag(false),
    _component(false),
    _theoryDescendant(false),
    _inductionDepth(0),
    _numSelected(0),
    _age(0),
    _weight(0),
    _store(NONE),
    _refCnt(0),
    _reductionTimestamp(0),
    _literalPositions(0),
    _splits(0),
    _numActiveSplits(0),
    _auxTimestamp(0)
{

  if(it == Unit::EXTENSIONALITY_AXIOM){
    //cout << "Setting extensionality" << endl;
    _extensionalityTag = true;
    setInputType(Unit::AXIOM);
  }
  static bool check = env.options->theoryAxioms() != Options::TheoryAxiomLevel::OFF ||
                      env.options->induction() != Options::Induction::NONE;
  if(check){
    Inference::Iterator it = inf->iterator();
    bool td = inf->hasNext(it); // td should be false if there are no parents
    unsigned id = 0; 
    while(inf->hasNext(it)){
      Unit* parent = inf->next(it);
      if(parent->isClause()){
        td &= static_cast<Clause*>(parent)->isTheoryDescendant();
        id = max(id,static_cast<Clause*>(parent)->inductionDepth());
      }
      else{
        // if a parent is not a clause then it cannot be (i) a theory axiom itself, 
        // or (ii) a theory descendant clause
        td = false;
      }
    }
    _theoryDescendant=td;
    _inductionDepth=id;
  }
}

/**
 * Allocate a clause having lits literals.
 * @since 18/05/2007 Manchester
 */
void* Clause::operator new(size_t sz, unsigned lits)
{
  CALL("Clause::operator new");
  ASS_EQ(sz,sizeof(Clause));

  RSTAT_CTR_INC("clauses created");

  //We have to get sizeof(Clause) + (_length-1)*sizeof(Literal*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size = sizeof(Clause) + lits * sizeof(Literal*);
  size -= sizeof(Literal*);

  return ALLOC_KNOWN(size,"Clause");
}

void Clause::operator delete(void* ptr,unsigned length)
{
  CALL("Clause::operator delete");

  RSTAT_CTR_INC("clauses deleted by delete operator");

  //We have to get sizeof(Clause) + (_length-1)*sizeof(Literal*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size = sizeof(Clause) + length * sizeof(Literal*);
  size -= sizeof(Literal*);

  DEALLOC_KNOWN(ptr, size,"Clause");
}

void Clause::destroyExceptInferenceObject()
{
  if (_literalPositions) {
    delete _literalPositions;
  }

  RSTAT_CTR_INC("clauses deleted");

  //We have to get sizeof(Clause) + (_length-1)*sizeof(Literal*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size = sizeof(Clause) + _length * sizeof(Literal*);
  size -= sizeof(Literal*);

  DEALLOC_KNOWN(this, size,"Clause");
}


Clause* Clause::fromStack(const Stack<Literal*>& lits, InputType it, Inference* inf)
{
  CALL("Clause::fromStack");

  unsigned clen = lits.size();
  Clause* res = new (clen) Clause(clen, it, inf);

  for(unsigned i = 0; i < clen; i++) {
    (*res)[i] = lits[i];
  }

  return res;
}

/**
 * Create a clause with the same content as @c c. The inference of the
 * created clause refers to @c c using the REORDER_LITERALS inference.
 *
 * The age of @c c is used, however the selected literals are not kept.
 *
 * BDDs and splitting history from @c c is also copied into the new clause.
 */
Clause* Clause::fromClause(Clause* c)
{
  CALL("Clause::fromClause");

  Inference* inf = new Inference1(Inference::REORDER_LITERALS, c);
  Clause* res = fromIterator(Clause::Iterator(*c), c->inputType(), inf);

  res->setAge(c->age());
  //res->setProp(c->prop());
  res->setSplits(c->splits());

  return res;
}

bool Clause::shouldBeDestroyed()
{
  return (_store == NONE) && _refCnt == 0 &&
    !isFromPreprocessing();
}

/**
 * If storage is set to NONE, there are no references to this clause,
 * an it is not an input clause, destroy it.
 */
void Clause::destroyIfUnnecessary()
{
  if (shouldBeDestroyed()) {
    destroy();
  }
}

/**
 * Destroy the clause by deleting the clause itself and all of its
 * literals.
 * @since 19/05/2007 Manchester
 */
void Clause::destroy()
{
  CALL("Clause::destroy");

  static Stack<Clause*> toDestroy(32);
  Clause* cl = this;
  for(;;) {
    Inference::Iterator it = cl->_inference->iterator();
    while (cl->_inference->hasNext(it)) {
      Unit* refU = cl->_inference->next(it);
      if (!refU->isClause()) {
	continue;
      }
      Clause* refCl = static_cast<Clause*> (refU);
      refCl->_refCnt--;
      if (refCl->shouldBeDestroyed()) {
	toDestroy.push(refCl);
      }
    }
    delete cl->_inference;
    cl->destroyExceptInferenceObject();
    if (toDestroy.isEmpty()) {
      break;
    }
    cl = toDestroy.pop();
  }
} // Clause::destroy

/** Set the store to @b s
 *
 * Can lead to clause deletion if the store is @b NONE
 * and there Clause's reference counter is zero. */
void Clause::setStore(Store s)
{
  CALL("Clause::setStore");

#if VDEBUG
  //assure there is one selected clause
  static Clause* selected=0;
  if (_store==SELECTED) {
    ASS_EQ(selected, this);
    selected=0;
  }
  if (s==SELECTED) {
    ASS_EQ(selected, 0);
    selected=this;
  }
#endif
  _store = s;
  destroyIfUnnecessary();
}

/**
 * Return true iff clause contains no variables
 */
bool Clause::isGround()
{
  CALL("Clause::isGround");

  Iterator it(*this);
  while (it.hasNext()) {
    if (!it.next()->ground()) {
      return false;
    }
  }
  return true;
}

/**
 * Return true iff clause contains no literals of non-zero arity
 */
bool Clause::isPropositional()
{
  CALL("Clause::isPropositional");

  Iterator it(*this);
  while (it.hasNext()) {
    if (it.next()->arity() > 0) {
      return false;
    }
  }
  return true;
}

/**
 * Return true iff clause is Horn
 */
bool Clause::isHorn()
{
  CALL("Clause::isHorn");

  bool posFound=false;
  Iterator it(*this);
  while (it.hasNext()) {
    if (it.next()->isPositive()) {
      if (posFound) {
        return false;
      }
      else {
        posFound=true;
      }
    }
  }
  return true;
}

/**
 * Return iterator over clause variables
 */
VirtualIterator<unsigned> Clause::getVariableIterator()
{
  CALL("Clause::getVariableIterator");

  return pvi( getUniquePersistentIterator(
      getMappingIterator(
	  getMapAndFlattenIterator(
	      Iterator(*this),
	      VariableIteratorFn()),
	  OrdVarNumberExtractorFn())));
}

/**
 * Return true if the clause does not depend on any splits
 * in the backtracking splitting.
 */
bool Clause::noSplits() const
{
  CALL("Clause::noSplits");

  return !this->splits() || this->splits()->isEmpty();
}

/**
 * Convert non-propositional part of the clause to vstring.
 */
vstring Clause::literalsOnlyToString() const
{
  CALL("Clause::literalsOnlyToString");

  if (_length == 0) {
    return "$false";
  } else {
    vstring result;
    result += _literals[0]->toString();
    for(unsigned i = 1; i < _length; i++) {
      result += " | ";
      result += _literals[i]->toString();
    }
    return result;
  }
}

/**
 * Convert the clause to the TPTP-compatible vstring representation.
 *
 * The split history is omitted.
 */
vstring Clause::toTPTPString() const
{
  CALL("Clause::toTPTPString()");

  vstring result = literalsOnlyToString();

  return result;
}

/**
 * Convert the clause to easily readable vstring representation.
 */
vstring Clause::toNiceString() const
{
  CALL("Clause::toNiceString()");

  vstring result = literalsOnlyToString();

  if (splits() && !splits()->isEmpty()) {
    result += vstring(" {") + splits()->toString() + "}";
  }

  return result;
}

/**
 * Convert the clause to the vstring representation
 * Includes splitting, age, weight, selected and inference
 */
vstring Clause::toString() const
{
  CALL("Clause::toString()");

  vstring result = Int::toString(_number) + ". " + Int::toString(size()) + " " + literalsOnlyToString();

  // print avatar components clause depends on
  if (splits() && !splits()->isEmpty()) {
    result += vstring(" <- (") + Splitter::splitsToString(splits()) + ")";
  }

  // print inference and ids of parent clauses
  result += " " + inferenceAsString();

  if(env.options->proofExtra()!=Options::ProofExtra::OFF){
    // print statistics: each entry should have the form key:value
    result += vstring(" {");
      
    result += vstring("a:") + Int::toString(_age);
    result += vstring(",w:") + Int::toString(weight());
    
    float ew = const_cast<Clause*>(this)->getEffectiveWeight(const_cast<Shell::Options&>(*(env.options)));
    unsigned effective = static_cast<int>(ceil(ew));
    if(effective!=weight()){
      result += vstring(",effW:") + Int::toString(effective);
    }

    if (numSelected()>0) {
      result += vstring(",nSel:") + Int::toString(numSelected());
    }

    if (env.colorUsed) {
      result += vstring(",col:") + Int::toString(color());
    }

    if(isGoal()){
      result += vstring(",goal:1");
    }
    if(isTheoryDescendant()){
      result += vstring(",tD:1");
    }

    result += vstring(",inD:") + Int::toString(inductionDepth());
    result += vstring("}");
  }
  result +=  inferenceAsString();
  return result;
}


/**
 * Convert the clause into sequence of strings, each containing
 * a proper clause
 */
VirtualIterator<vstring> Clause::toSimpleClauseStrings()
{
  CALL("toSimpleClauseStrings");
    return pvi(getSingletonIterator(literalsOnlyToString()));

}

/**
 * Return true iff the clause is skipped for the purpose
 * of symbol elimination reporting.
 */
bool Clause::skip() const
{
  unsigned clen = length();
  for(unsigned i = 0; i < clen; i++) {
    const Literal* lit = (*this)[i];
    if (!lit->skip()) {
      return false;
    }
  }
  return true;
}

/**
 * Compute the color of the clause and store it in @b _color
 * @pre All literals are shared, so their color is computed properly.
 */
void Clause::computeColor() const
{
  CALL("Clause::computeColor");
  ASS_EQ(_color, COLOR_INVALID);

  Color color = COLOR_TRANSPARENT;

  if (env.colorUsed) {
    unsigned clen=length();
    for(unsigned i=0;i<clen;i++) {
      color = static_cast<Color>(color | (*this)[i]->color());
    }
    ASS_L(color, COLOR_INVALID);
  }

  _color=color;
}

/**
 * Compute the weight of the clause.
 * @pre All literals are shared, so their weight is computed properly.
 * @since 02/01/2008 Manchester.
 * @since 22/01/2015 include splitWeight in weight
 */
void Clause::computeWeight() const
{
  CALL("Clause::computeWeight");

  _weight = 0;
  for (int i = _length-1; i >= 0; i--) {
    ASS(_literals[i]->shared());
    _weight += _literals[i]->weight();
  }

  // We now include this directly in weight()
  // This is so that we can reduce the split set and keep the original weight
  // The alternative would be to remove the clause and reenter it into the passive queue whenever
  // The split set was changed
  if (env.options->nonliteralsInClauseWeight()) {
    _weight+=splitWeight(); // no longer includes propWeight
  }

  // If _weight is zero (empty clause) then no need to do this
  if(_weight){
    unsigned priority = getPriority();
    _weight *= priority;
  }

} // Clause::computeWeight


/**
 * Return weight of the split part of the clause
 *
 * This weight is not included in the number returned by the
 * @b weight() function.
 */
unsigned Clause::splitWeight() const
{
  return splits() ? splits()->size() : 0;
}

/**
 * Returns the numeral weight of a clause. The weight is defined as the sum of
 * binary sizes of all integers occurring in this clause.
 * @warning Each call to this function recomputes the numeral weight, so the call may
 *          potentially result in traversing the whole clause
 * @since 04/05/2013 Manchester, updated to use new NonVariableIterator
 * @author Andrei Voronkov
 */
unsigned Clause::getNumeralWeight() 
{
  CALL("Clause::getNumeralWeight");

  unsigned res=0;
  Iterator litIt(*this);
  while (litIt.hasNext()) {
    Literal* lit=litIt.next();
    if (!lit->hasInterpretedConstants()) {
      continue;
    }
    NonVariableIterator nvi(lit);
    while (nvi.hasNext()) {
      const Term* t = nvi.next().term();
      if (t->arity() != 0) {
	continue;
      }
      IntegerConstantType intVal;
      if (theory->tryInterpretConstant(t,intVal)) {
	int w = BitUtils::log2(abs(intVal.toInner()))-1;
	if (w > 0) {
	  res += w;
	}
	continue;
      }
      RationalConstantType ratVal;
      RealConstantType realVal;
      bool haveRat = false;
      if (theory->tryInterpretConstant(t,ratVal)) {
	haveRat = true;
      }
      else if (theory->tryInterpretConstant(t,realVal)) {
	ratVal = RationalConstantType(realVal);
	haveRat = true;
      }
      if (!haveRat) {
	continue;
      }
      int wN = BitUtils::log2(abs(ratVal.numerator().toInner()))-1;
      int wD = BitUtils::log2(abs(ratVal.denominator().toInner()))-1;
      int v = wN + wD;
      if (v > 0) {
	res += v;
      }
    }
  }
  return res;
} // getNumeralWeight

/**
 * Return effective weight of the clause (i.e. weight multiplied
 * by the nongoal weight coefficient, if applicable)
 * @since 22/1/15 weight uses splitWeight
 */
float Clause::getEffectiveWeight(const Options& opt) 
{
  CALL("Clause::getEffectiveWeight");

  static float nongoalWeightCoef=opt.nongoalWeightCoefficient();
  static bool restrictNWC = opt.restrictNWCtoGC();

  bool goal = isGoal();
  if(goal && restrictNWC){
    bool found = false;
    for(unsigned i=0;i<_length;i++){
      TermFunIterator it(_literals[i]);
      it.next(); // skip literal symbol
      while(it.hasNext()){
        found |= env.signature->getFunction(it.next())->inGoal();
      }
    }
    if(!found){ goal=false; }
  } 

  unsigned w=weight();
  if (opt.increasedNumeralWeight()) {
    return (2*w+getNumeralWeight()) * ( !goal ? nongoalWeightCoef : 1.0f);
  }
  else {
    return w * ( !goal ? nongoalWeightCoef : 1.0f);
  }
}

void Clause::collectVars(DHSet<unsigned>& acc)
{
  CALL("Clause::collectVars");

  Iterator it(*this);
  while (it.hasNext()) {
    Literal* lit = it.next();
    VariableIterator vit(lit);
    while (vit.hasNext()) {
      TermList var = vit.next();
      ASS(var.isOrdinaryVar());
      acc.insert(var.var());
    }
  }
}

unsigned Clause::varCnt()
{
  CALL("Clause::varCnt");

  static DHSet<unsigned> vars;
  vars.reset();
  collectVars(vars);
  return vars.size();
}

unsigned Clause::maxVar()
{
  CALL("Clause::maxVar()");
  
  unsigned max = 0;
  VirtualIterator<unsigned> it = getVariableIterator();

  while (it.hasNext()) {
    unsigned n = it.next();
    max = n > max ? n : max;
  }
  return max;
}

/**
 * Return index of @b lit in the clause
 *
 * @b lit has to be present in the clause
 */
unsigned Clause::getLiteralPosition(Literal* lit)
{
  switch(length()) {
  case 1:
    ASS_EQ(lit,(*this)[0]);
    return 0;
  case 2:
    if (lit==(*this)[0]) {
      return 0;
    } else {
      ASS_EQ(lit,(*this)[1]);
      return 1;
    }
  case 3:
    if (lit==(*this)[0]) {
      return 0;
    } else if (lit==(*this)[1]) {
      return 1;
    } else {
      ASS_EQ(lit,(*this)[2]);
      return 2;
    }
#if VDEBUG
  case 0:
    ASSERTION_VIOLATION;
#endif
  default:
    if (!_literalPositions) {
      _literalPositions=new InverseLookup<Literal>(_literals,length());
    }
    return static_cast<unsigned>(_literalPositions->get(lit));
  }
}

/**
 * This method should be called when literals of the clause are
 * reordered (e.g. after literal selection), so that the information
 * about literal positions can be updated.
 */
void Clause::notifyLiteralReorder()
{
  CALL("Clause::notifyLiteralReorder");
  if (_literalPositions) {
    _literalPositions->update(_literals);
  }
}

#if VDEBUG

void Clause::assertValid()
{
  ASS_ALLOC_TYPE(this, "Clause");
  if (_literalPositions) {
    unsigned clen=length();
    for (unsigned i = 0; i<clen; i++) {
      ASS_EQ(getLiteralPosition((*this)[i]),i);
    }
  }
}

bool Clause::contains(Literal* lit)
{
  for (int i = _length-1; i >= 0; i--) {
    if (_literals[i]==lit) {
      return true;
    }
  }
  return false;
}

#endif

}
