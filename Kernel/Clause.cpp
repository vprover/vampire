/**
 * @file Clause.cpp
 * Implements class Clause for units consisting of clauses
 *
 * @since 18/05/2007 Manchester
 */

#include <ostream>

#include "../Lib/Allocator.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Stack.hpp"

#include "../SAT/SATClause.hpp"

#include "../Shell/Options.hpp"

#include "Inference.hpp"
#include "Clause.hpp"
#include "Term.hpp"
#include "BDD.hpp"
#include "Signature.hpp"

namespace Kernel
{

using namespace Lib;
using namespace Shell;

size_t Clause::_auxCurrTimestamp = 0;
#if VDEBUG
bool Clause::_auxInUse = false;
#endif

/**
 * Allocate a clause having lits literals.
 * @since 18/05/2007 Manchester
 */
void* Clause::operator new(size_t sz, unsigned lits)
{
  CALL("Clause::operator new");

  //We have to get sizeof(Clause) + (_length-1)*sizeof(Literal*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size = sz + lits * sizeof(Literal*);
  size -= sizeof(Literal*);

  return ALLOC_KNOWN(size,"Clause");
}

Clause* Clause::fromStack(Stack<Literal*>& lits, InputType it, Inference* inf)
{
  unsigned clen = lits.size();
  Clause* res = new (clen) Clause(clen, it, inf);

  for(unsigned i = 0; i < clen; i++) {
    (*res)[i] = lits[i];
  }

  return res;
}

/** Set the propositional part of the clause */
void Clause::setProp(BDDNode* prop)
{
  //  if(_prop) {
  //    cout<<"%% prop change: " << (*this) << "-->" << BDD::instance()->toString(prop)<<endl;
  //  }
  _prop = prop;
}

bool Clause::shouldBeDestroyed()
{
  return _store == NONE && _inferenceRefCnt == 0 && _inference->rule()
      != Inference::INPUT;
}

/**
 * If storage is set to NONE, there are no references to this class,
 * an it is not an input clause, destroy it.
 */
void Clause::destroyIfUnnecessary()
{
  //TODO: perform unnecessary clause destruction
  if(shouldBeDestroyed()) {
    //    destroy();
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
    while(cl->_inference->hasNext(it)) {
      Unit* refU = cl->_inference->next(it);
      if(!refU->isClause()) {
	continue;
      }
      Clause* refCl = static_cast<Clause*> (refU);
      refCl->_inferenceRefCnt--;
      if(refCl->shouldBeDestroyed()) {
	toDestroy.push(refCl);
      }
    }
    delete cl->_inference;
    cl->destroyExceptInferenceObject();
    if(toDestroy.isEmpty()) {
      break;
    }
    cl = toDestroy.pop();
  }
} // Clause::destroy

void Clause::destroyExceptInferenceObject()
{
  if(_literalPositions) {
    delete _literalPositions;
  }

  //We have to get sizeof(Clause) + (_length-1)*sizeof(Literal*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size = sizeof(Clause) + _length * sizeof(Literal*);
  size -= sizeof(Literal*);

  DEALLOC_KNOWN(this, size,"Clause");
}

/**
 * Return true iff clause contains no literals of non-zero arity.
 */
bool Clause::isPropositional()
{
  CALL("Clause::isPropositional");

  for(unsigned i = 0; i < _length; i++) {
    if(_literals[i]->arity() > 0) {
      return false;
    }
  }
  return true;
}

//struct StrComparator {
//  Comparison compare(string s1, string s2)
//  {
//    int res=strcmp(s1.c_str(), s2.c_str());
//    return (res==0)?EQUAL:(res>0)?GREATER:LESS;
//  }
//};

/**
 * Convert non-propositional part of the clause to string.
 */
string Clause::nonPropToString() const
{
  CALL("Clause::nonPropToString");

  if(_length == 0) {
    return "$false";
  } else {
    string result;
    result += _literals[0]->toString();
    for(unsigned i = 1; i < _length; i++) {
      result += " | ";
      result += _literals[i]->toString();
    }
    return result;
  }
}

/**
 * Convert the clause to the TPTP-compatible string representation.
 */
string Clause::toTPTPString() const
{
  CALL("Clause::toTPTPString()");

  string result = nonPropToString();

  if(prop() && !BDD::instance()->isFalse(prop())) {
    result += " | " + BDD::instance()->toTPTPString(prop());
  }

  return result;
}

/**
 * Convert the clause to easily readable string representation.
 */
string Clause::toNiceString() const
{
  CALL("Clause::toNiceString()");

  string result = nonPropToString();

  if(prop() && !BDD::instance()->isFalse(prop())) {
    result += " | " + BDD::instance()->toString(prop());
  }

  return result;
}

/**
 * Convert the clause to the string representation, assuming its
 * propositional part is @b propPart.
 */
string Clause::toString(BDDNode* propPart) const
{
  CALL("Clause::toString(BDDNode*)");

  string result = Int::toString(_number) + ". " + nonPropToString();

  if(propPart && !BDD::instance()->isFalse(propPart)) {
    result += " | " + BDD::instance()->toString(propPart);
  }

  result += string(" (") + Int::toString(_age) + ':' + Int::toString(weight())
      + ") " + inferenceAsString();
  return result;
}

/**
 * Convert the clause to the string representation.
 * @since 20/05/2007 Manchester
 */
string Clause::toString() const
{
  CALL("Clause::toString()");

  return toString(prop());
} // Clause::toString

/**
 * Convert the clause into sequence of strings, each containing
 * a proper clause (no BDDs). Also BDD variables corresponding to
 * propositional predicates are output as those predicates.
 */
VirtualIterator<string> Clause::toSimpleClauseStrings()
{
  CALL("toSimpleClauseStrings");
  BDD* bdd = BDD::instance();
  if(bdd->isTrue(prop())) {
    return VirtualIterator<string>::getEmpty();
  }
  if(bdd->isFalse(prop())) {
    return pvi(getSingletonIterator(nonPropToString()));
  }

  string np(length() ? (nonPropToString() + " | ") : string(""));

  SATClauseList* scl = bdd->toCNF(prop());
  List<string>* res = 0;

  while(scl) {
    SATClause* sc = SATClauseList::pop(scl);
    string rstr(np);

    for(unsigned i = 0; i < sc->length(); i++) {
      if(i) {
	rstr += " | ";
      }
      if(!(*sc)[i].polarity()) {
	rstr += '~';
      }
      unsigned bddVar = (*sc)[i].var();
      string varName;
      if(!bdd->getNiceName(bddVar, varName)) {
	varName = bdd->getPropositionalPredicateName(bddVar);
      }
      rstr += varName;
    }

    List<string>::push(rstr, res);
    sc->destroy();
  }

  return pvi(List<string>::DestructiveIterator(res));
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
    if(!lit->skip()) {
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

  if(env.colorUsed) {
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
 */
void Clause::computeWeight() const
{
  CALL("Clause::computeWeight");

  _weight = 0;
  for (int i = _length-1; i >= 0; i--) {
    ASS(_literals[i]->shared());
    _weight += _literals[i]->weight();
  }
} // Clause::computeWeight

float Clause::getEffectiveWeight(unsigned originalWeight)
{
  static float nongoalWeightCoef=-1;
  if(nongoalWeightCoef<0) {
    nongoalWeightCoef=env.options->nongoalWeightCoefficient();
  }
  return originalWeight * ( (inputType()==0) ? nongoalWeightCoef : 1.0f);
}

/**
 * Return effective weight of the clause (i.e. weight multiplied
 * by the nongoal weight coefficient, if applicable)
 */
float Clause::getEffectiveWeight()
{
  return getEffectiveWeight(weight());
}

/**
 * Return index of @b lit in the clause
 */
unsigned Clause::getLiteralPosition(Literal* lit)
{
  switch(length()) {
  case 1:
    ASS_EQ(lit,(*this)[0]);
    return 0;
  case 2:
    if(lit==(*this)[0]) {
      return 0;
    } else {
      ASS_EQ(lit,(*this)[1]);
      return 1;
    }
  case 3:
    if(lit==(*this)[0]) {
      return 0;
    } else if(lit==(*this)[1]) {
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
    if(!_literalPositions) {
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
  if(_literalPositions) {
    _literalPositions->update(_literals);
  }
}

#if VDEBUG

void Clause::assertValid()
{
  ASS_ALLOC_TYPE(this, "Clause");
  if(_literalPositions) {
    unsigned clen=length();
    for (unsigned i = 0; i<clen; i++) {
      ASS_EQ(getLiteralPosition((*this)[i]),i);
    }
  }
}

bool Clause::contains(Literal* lit)
{
  for (int i = _length-1; i >= 0; i--) {
    if(_literals[i]==lit) {
      return true;
    }
  }
  return false;
}

#endif

}

std::ostream& Kernel::operator<<(ostream& out, const Clause& cl)
{
  return out << cl.toString();
}
