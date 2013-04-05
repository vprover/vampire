/**
 * @file AssignmentSelector.cpp
 * Implements class AssignmentSelector.
 */
#if GNUMP

#include "Lib/ArrayMap.hpp"
#include "Lib/Array.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Random.hpp"

#include "Kernel/Number.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "BoundsArray.hpp"
#include "Solver.hpp"

#include "AssignmentSelector.hpp"

#include <cmath>

#undef LOGGING
#define LOGGING 0

namespace Solving
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * Base class for assignment selectors that decide only based on the value
 * of the upper and lower bound
 *
 * The implementor must override either @c getAnyAssignment() or all of
 * @c getBoundedAssignment(), @c getLeftBoundedAssignment(),
 * @c getRightBoundedAssignment() and @c getUnboundedAssignment().
 */
class ConvenientAssignmentSelector : public AssignmentSelector
{
public:
  ConvenientAssignmentSelector(Solver& s)
  :
#if VDEBUG
    _inUse(false),
#endif
    _solver(s), _bounds(s.getBounds()) {}

  bool withinBounds(const BoundNumber& num) {
    CALL("ConvenientAssignmentSelector::withinBounds");

    if(_hasLeft) {
      if(_leftStrict) {
    	  if(num<=_leftBound) { return false; }
      }
      else {
    	  if(num<_leftBound) { return false; }
      }
    }
    if(_hasRight) {
      if(_rightStrict) {
	if(num>=_rightBound) {
		return false;
		}
      }
      else {
	if(num>_rightBound) { return false; }
      }
    }
    return true;
  }

  virtual void getAnyAssignment(BoundNumber& result)
  {
    CALL("ConvenientAssignmentSelector::getAnyAssignment");

    if(!_hasLeft && !_hasRight) {
      getUnboundedAssignment(result);
    }
    else if(!_hasLeft) {
      getRightBoundedAssignment(result);
    }
    else if(!_hasRight) {
      getLeftBoundedAssignment(result);
    }
    else {
      getBoundedAssignment(result);
    }
  }

  virtual void getAssignment(Var var, BoundNumber& result)
  {
    CALL("ConvenientAssignmentSelector::getAssignment");

#if VDEBUG
    ASS(!_inUse);
    _inUse = true;
#endif
    _var = var;
    _hasLeft = _bounds.getBound(BoundId(_var, true), _leftBound, _leftStrict);
    _hasRight = _bounds.getBound(BoundId(_var, false), _rightBound, _rightStrict);

    getAnyAssignment(result);
    if(!_hasLeft && !_hasRight) {
      LOG("tkv_assignment","Decided value for "<<env.signature->varName(_var)<<" from -oo...oo to be "<<result);
    }
    else if(!_hasLeft) {
      LOG("tkv_assignment","Decided value for "<<env.signature->varName(_var)<<" from -oo..."<<_rightBound<<" to be "<<result);
    }
    else if(!_hasRight) {
      LOG("tkv_assignment","Decided value for "<<env.signature->varName(_var)<<" from "<<_leftBound<<"...oo to be "<<result);
    }
    else {
      LOG("tkv_assignment","Decided value for "<<env.signature->varName(var)<<" from "<<_leftBound<<"..."<<_rightBound<<" to be "<<result);
    }
    if(_hasLeft && _leftStrict && !usingPreciseNumbers() && result==_leftBound) {
	throw Solver::NumberImprecisionException();
    }
    if(_hasRight && _rightStrict && !usingPreciseNumbers() && result==_rightBound) {
	throw Solver::NumberImprecisionException();
    }
#if VDEBUG
    ASS(withinBounds(result));
    _inUse = false;
#endif
  }

protected:
  virtual void getBoundedAssignment(BoundNumber& result) { NOT_IMPLEMENTED; }
  virtual void getLeftBoundedAssignment(BoundNumber& result) { NOT_IMPLEMENTED; }
  virtual void getRightBoundedAssignment(BoundNumber& result) { NOT_IMPLEMENTED; }
  virtual void getUnboundedAssignment(BoundNumber& result) { NOT_IMPLEMENTED; }

#if VDEBUG
  bool _inUse;
#endif
  Var _var;
  bool _hasLeft, _leftStrict, _hasRight, _rightStrict;
  BoundNumber _leftBound, _rightBound;

  Solver& _solver;
  BoundsArray& _bounds;
};

/**
 * Assignment selector that picks the number based of the rational decomposition
 */
class RationalAssignmentSelector : public ConvenientAssignmentSelector
{
public:
	RationalAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s) {}
protected:

	//perform the selection algorithm
	virtual void getBoundedAssignment(BoundNumber& result){
	CALL("RationalAssignmentSelector:getBoundedAssignment");
	//if the bounds are equal than just pick one
	if (_rightBound.abs() == _leftBound.abs() ){
		result = _rightBound;
		return;
		}
	if(_rightBound.isPositive() && _leftBound.isNegative()){
		if(Random::getBit()){
			result = BoundNumber::zero();
		}
		else {
			result = BoundNumber::getRandomValue(_leftBound, _rightBound);
		}
		return;
	}

	if(_rightBound.isZero()){
		/*
		if (_rightStrict){
			result = BoundNumber::getRandomValue(_leftBound, BoundNumber::zero());
			return;
		}
		if (Random::getBit()){
			result = _rightBound;
		}
		else {
			if(_leftStrict){
				result = BoundNumber::getRandomValue(_leftBound, _rightBound);
				return;
			}
			result = _leftBound;
			return;
		}*/
		result = BoundNumber::getRandomValue(_rightBound,BoundNumber::zero());

		return;
	}
	if (_leftBound.isZero()){
		/*if (_leftStrict){
			result = BoundNumber::getRandomValue(BoundNumber::zero(), _rightBound);
			return;
		}
		if (_rightStrict){
			result = BoundNumber::getRandomValue(_leftBound, _rightBound);
			return;
		}
		if (Random::getBit()){
			result=_rightBound;
			return;
		}
		else{
			result = _leftBound;
			return;
		}*/
		result = BoundNumber::getRandomValue(BoundNumber::zero(),_rightBound);
		return;
	}

	if(_leftBound.isNegative() && _rightBound.isNegative()){
		//we play nicely with the positive values
		BoundNumber absl = _leftBound.abs();
		BoundNumber absr = _rightBound.abs();
		result = -(absl.getMagicNumber(absr));
		return;
	}
	else {
		result = _leftBound.getMagicNumber(_rightBound);
		return;
	}

	}
	//if the left bound is not strict, than pick it
	virtual void getLeftBoundedAssignment(BoundNumber& result){
	CALL("RationalAssignmentSelector:getLeftBoundedAssignment");
	if (!_leftStrict) {
		result = _leftBound;
	}
	else{
		result = _leftBound + ( _leftBound.abs()/BoundNumber(10) );
	}

	}
	//if the right bound is not strict, than pick it
	virtual void getRightBoundedAssignment(BoundNumber& result){
	CALL("RationalAssignmentSelector:getRightBoundedAssignment");
	if (!_rightStrict){
		result = _rightBound;
	}
	else {
		result = _rightBound - ( _rightBound.abs()/BoundNumber(10) );
	}
	}

	//pick the bound number 0 or a random number between [-100,100]
	virtual void getUnboundedAssignment(BoundNumber& result){
	CALL("RationalAssignmentSelector:getUnboundedAssignment");
	if (Random::getBit()) {
		result = BoundNumber::zero();
	}
	else {
		result = BoundNumber::getRandomValue(BoundNumber(-1000), BoundNumber(1000));
	}

	}
};

/**
 * Assignment selector which picks the middle of the interval.
 */

class MiddleAssignmentSelector : public ConvenientAssignmentSelector
{
public:
  MiddleAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s) {}

protected:
  virtual void getBoundedAssignment(BoundNumber& result)
  {
    result = (_leftBound+_rightBound)/BoundNumber::two();
  }

  virtual void getLeftBoundedAssignment(BoundNumber& result)
  {
    if(_leftBound.isZero()) {
      result = BoundNumber::one();
    }
    else {
      result = _leftBound+_leftBound.abs();
    }
  }

  virtual void getRightBoundedAssignment(BoundNumber& result)
  {
    if(_rightBound.isZero()) {
      result = -BoundNumber::one();
    }
    else {
      result = _rightBound-_rightBound.abs();
    }
  }

  virtual void getUnboundedAssignment(BoundNumber& result)
  {
    result = BoundNumber::zero();
  }
};


/**
 * Assignment selector which returns the right bound in case this is not tight,
 * if that is the case, either subtract or add some small value to it.
 */
class UpperBoundAssignmentSelector : public ConvenientAssignmentSelector {
public:
  UpperBoundAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s) {}
protected:
  virtual void getBoundedAssignment(BoundNumber& result){
  CALL("UpperBoundAssignmentSelector:getBoundedAssignment");
  //right bound is not strict => pick it!
  if(!_rightStrict) {
    result = _rightBound;
    return;
  } //right bound is strict
  else {
	  //randomly choos to either pick right bound - some value or the left bound
	  if (Random::getBit()){
		  result = _rightBound - (_rightBound.abs()+_leftBound.abs())/BoundNumber::two();
		  return;
	  }
	  else {
		  if (!_leftStrict){
			  result = _leftBound;
			  return;
		  }
		  else {
			  result = _rightBound - (_rightBound.abs()+_leftBound.abs())/BoundNumber::two();
			  return;
		  }
	  }
  }
  }

  virtual void getLeftBoundedAssignment(BoundNumber& result){
    CALL("UpperBoundAssignmentSelector:getLeftBoundedAssignment");
    if( !_leftStrict ) {
      result = _leftBound;
      return;
    }
    else {
      result = _leftBound + BoundNumber(0.125);
    }
  }

  virtual void getRightBoundedAssginment(BoundNumber& result){
    CALL("UpperBoundAssignmentSelector:getRightBoundedAssignment");
    if ( !_rightStrict ) {
      result = _rightBound;
    }
    else {
      result = _rightBound - BoundNumber(0.125);
    }
  }
  virtual void getUnboundedAssignment(BoundNumber& result){
    CALL("UpperBoundedAssignmentSelector:getUnboundedAssignment");
    result = BoundNumber::zero();
  }
};

/**
 * Assignment selector which returns the left bound in case this is not tight.
 * it the bound is tight, then return the left bound plus some small value.
 */
class LowerBoundAssignmentSelector : public ConvenientAssignmentSelector {
public:
  LowerBoundAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s) {}
protected:

  virtual void getBoundedAssignment(BoundNumber& result){
  CALL("LowerBoundAssignmentSelector:getBoundedAssignmentSelector");
  if ( !_leftStrict ) {
    result = _leftBound;
  }
  else {
    result = _leftBound + (_leftBound.abs())/BoundNumber::two();
    }
  }

  virtual void getLeftBoundedAssignment(BoundNumber& result){
    CALL("LowerBoundAssignmentSelector:getLeftBoundedAssignment");
    if( !_leftStrict ) {
      result = _leftBound;
    }
    else {
      result = _leftBound + BoundNumber(0.125);
    }
  }
  virtual void getRightBoundedAssignment(BoundNumber& result){
    CALL("LowerBoundAssignmentSelector:getRightBoundedAssignment");
    if( !_rightStrict ) {
      result = _rightBound;
    }
    else {
      result = _rightBound - BoundNumber(0.125);
    }
  }
  virtual void getUnboundedAssignment(BoundNumber& result){
    CALL("LowerBoundAssignmentSelector:getUnboundedAssignment");
    result = BoundNumber::zero();
  }
};

/**
 * Assignment selector, which keeps track of what was selected last time. The idea is to
 * alternate choosing the upper bound and lower bound
 */
class AlternativeAssignmentSelector : public ConvenientAssignmentSelector {
public:
  AlternativeAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s), _upper(false) {}
protected:
  virtual void getBoundedAssignment(BoundNumber& result){
  CALL("AlternativeAssignmentSelector:getBoundedAssignment");
  if ( _upper ) {
    //pick the upper bound and set for future to select the lower bound
    if ( !_rightStrict ) {
      result = _rightBound;
    }
    else {
      result = _rightBound - BoundNumber(0.125);
    }
    _upper = false;
  }
  else {
    //pick the lower bound and set for future step to select the upper bound
    if ( !_leftStrict ) {
      result = _leftBound;
    }
    else {
      result = _leftBound + BoundNumber(0.125);
    }
    _upper = true;
  }

  }

  virtual void getLeftBoundedAssignment(BoundNumber& result){
    CALL("AlternativeAssignmentSelector:getLeftBoundedAssignment");
    if ( !_leftStrict ) {
      result = _leftBound;
    }
    else {
      result = _leftBound + BoundNumber(0.00125);
    }
  }

  virtual void getRightBoundedAssignment(BoundNumber& result){
    CALL("AlternativeAssignmentSelector:getRightBoundedAssignmetn");
    if ( !_rightStrict ) {
      result = _rightBound;
    }
    else {
      result = _rightBound - BoundNumber(0.125);
    }
  }
  virtual void getUnboundedAssignment(BoundNumber& result){
    CALL("AlternativeAssignmentSelector:getUnboundedAssignment");
    if (Random::getBit()){
    	result = BoundNumber::getRandomValue(BoundNumber(-100),BoundNumber(100));
    	return;
    }
    else {
    	result = BoundNumber::zero();
    	return;
    }
  }
private:
  bool _upper;
};

/**
 * Random assignment selector. This picks a random value from the interval defined
 * by [left,right] bounds.
 */

class RandomAssignmentSelector : public ConvenientAssignmentSelector
{
public:
  RandomAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s), _bigNum(100) {}

protected:
  void getRandomValue(const BoundNumber& min, const BoundNumber& max, BoundNumber& result)
  {
    CALL("RandomAssignmentSelector::getRandomValue");

    result = BoundNumber::getRandomValue(min, max);
  }

  virtual void getBoundedAssignment(BoundNumber& result)
  {
    CALL("RandomAssignmentSelector::getBoundedAssignment");
    getRandomValue(_leftBound, _rightBound, result);
  }

  virtual void getLeftBoundedAssignment(BoundNumber& result)
  {
    CALL("RandomAssignmentSelector::getLeftBoundedAssignment");
    if(_leftBound.isZero()) {
      getRandomValue(BoundNumber::zero(), _bigNum, result);
    }
    else {
      getRandomValue(_leftBound, _leftBound+_leftBound.abs(), result);
    }
  }

  virtual void getRightBoundedAssignment(BoundNumber& result)
  {
    CALL("RandomAssignmentSelector::getRightBoundedAssignment");
    if(_rightBound.isZero()) {
      getRandomValue(-_bigNum, BoundNumber::zero(), result);
    }
    else {
      getRandomValue(_rightBound-_rightBound.abs(), _rightBound, result);
    }
  }

  virtual void getUnboundedAssignment(BoundNumber& result)
  {
    CALL("RandomAssignmentSelector::getUnboundedAssignment");
    getRandomValue(-_bigNum, _bigNum, result);
  }
private:
  BoundNumber _bigNum;
};

class TightishAssignmentSelector : public ConvenientAssignmentSelector
{
public:
  TightishAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s) {}

protected:
  virtual void getBoundedAssignment(BoundNumber& result)
  {
  CALL("ThightishAssignmentSelector:getBoundedAssignment");

  BoundNumber delta = (_rightBound-_leftBound)/BoundNumber(10);
  if(Random::getBit()) {

      result = _leftBound+delta;
    }
    else {
      result = _rightBound-delta;
    }
  }

  virtual void getLeftBoundedAssignment(BoundNumber& result)
  {
    CALL("ThightishAssignmentSelector:getLeftBoundedAssignment");

    result = _leftBound+BoundNumber(0.25);
  }

  virtual void getRightBoundedAssignment(BoundNumber& result)
  {
    CALL("ThightishAssignmentSelector:getRightBoundedAssignmetn");

    result = _rightBound-BoundNumber(0.25);
  }

  virtual void getUnboundedAssignment(BoundNumber& result)
  {
    CALL("ThightishAssignmentSelector:getUnboundedAssignment");

    result = BoundNumber::zero();
  }
};


class TightAssignmentSelector : public ConvenientAssignmentSelector
{
public:
  TightAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s) {}

protected:
  virtual void getBoundedAssignment(BoundNumber& result)
  {
    if(!_leftStrict && !_rightStrict) {
      if(Random::getBit()) {
	result = _leftBound;
      }
      else {
	result = _rightBound;
      }
    }
    else {
      if(!_leftStrict) {
	result = _leftBound;
      }
      else if(!_rightStrict) {
	result = _rightBound;
      }
      else {
	BoundNumber delta = (_rightBound-_leftBound)/BoundNumber(32);
	if(Random::getBit()) {
	  result = _leftBound+delta;
	}
	else {
	  result = _rightBound-delta;
	}
      }
    }
  }

  virtual void getLeftBoundedAssignment(BoundNumber& result)
  {
    if(!_leftStrict) {
      result = _leftBound;
    }
    else {
      result = _leftBound+BoundNumber(0.125);
    }
  }

  virtual void getRightBoundedAssignment(BoundNumber& result)
  {
    if(!_rightStrict) {
      result = _rightBound;
    }
    else {
      result = _rightBound-BoundNumber(0.125);
    }
  }

  virtual void getUnboundedAssignment(BoundNumber& result)
  {
    result = BoundNumber::zero();
  }
};

class BiggestAssignmentSelector : public ConvenientAssignmentSelector{
public :
  BiggestAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s) {}
protected:
  virtual void getBoundedAssignment(BoundNumber& result){
  CALL("BiggestAssignmentSelector::getBoundedAssignment()");
  if ( _leftBound.isNegative() && _rightBound.isPositive()){
    result = _rightBound;
  }
  else if (_rightBound.isNegative()){
    ASS(_leftBound.isNegative());
    if (!_rightStrict) {
      result = _rightBound;
    }
    else {
      BoundNumber delta = (_rightBound - _leftBound)/BoundNumber(32);
      result = _rightBound + delta;
    }
  }
  else {
  ASS(_rightBound.isPositive());
    if(!_rightStrict) {
 	result = _rightBound;
       }
       else {
 	BoundNumber delta = (_rightBound-_leftBound.abs())/BoundNumber(32);
 	result = _rightBound - delta;
       }

  }
}

  virtual void getLeftBoundedAssignment(BoundNumber& result)
{
  if(_leftBound.isNegative()) {
    result = BoundNumber::zero();
  }
  else if(!_leftStrict) {
    result = _leftBound;
  }
  else {
    result = _leftBound+BoundNumber(0.125);
  }
}

  virtual void getRightBoundedAssignment(BoundNumber& result)
{
  if(_rightBound.isPositive()) {
    result = BoundNumber::zero();
  }
  else if(!_rightStrict) {
    result = _rightBound;
  }
  else {
    result = _rightBound-BoundNumber(0.125);
  }
}

  virtual void getUnboundedAssignment(BoundNumber& result)
{
  result = BoundNumber::zero();
}

};


class SmallestAssignmentSelector : public ConvenientAssignmentSelector
{
public:
  SmallestAssignmentSelector(Solver& s) : ConvenientAssignmentSelector(s) {}

protected:
  virtual void getBoundedAssignment(BoundNumber& result)
  {
    CALL("SmallestAssignmentSelector::getBoundedAssignment");

    if(_leftBound.isNegative() && _rightBound.isPositive()) {
      result = BoundNumber::zero();
    }
    else if(!_leftBound.isNegative()) {
      ASS(_rightBound.isPositive());
      if(!_leftStrict) {
        result = _leftBound;
      }
      else {
	BoundNumber delta = (_rightBound-_leftBound)/BoundNumber(32);
	result = _leftBound+delta;
      }
    }
    else {
      ASS(!_rightBound.isPositive());
      ASS(_leftBound.isNegative());
      if(!_rightStrict) {
	result = _rightBound;
      }
      else {
	BoundNumber delta = (_rightBound-_leftBound)/BoundNumber(32);
	result = _rightBound-delta;
      }
    }
  }

  virtual void getLeftBoundedAssignment(BoundNumber& result)
  {
    if(_leftBound.isNegative()) {
      result = BoundNumber::zero();
    }
    else if(!_leftStrict) {
      result = _leftBound;
    }
    else {
      result = _leftBound+BoundNumber(0.125);
    }
  }

  virtual void getRightBoundedAssignment(BoundNumber& result)
  {
    if(_rightBound.isPositive()) {
      result = BoundNumber::zero();
    }
    else if(!_rightStrict) {
      result = _rightBound;
    }
    else {
      result = _rightBound-BoundNumber(0.125);
    }
  }

  virtual void getUnboundedAssignment(BoundNumber& result)
  {
    result = BoundNumber::zero();
  }
};

class ConservativeAssignmentSelector : public ConvenientAssignmentSelector
{
public:
  ConservativeAssignmentSelector(Solver& s, AssignmentSelector* subSelector)
  : ConvenientAssignmentSelector(s),
    _prevAssignments(s.varCnt()),
    _subSelector(subSelector) {}

protected:
  virtual void getAnyAssignment(BoundNumber& result)
  {
    CALL("ConservativeAssignmentSelector::getAnyAssignment");

    if(_prevAssignments.find(_var)) {
      const BoundNumber& prevAsgn = _prevAssignments.get(_var);
      if(withinBounds(prevAsgn)) {
	result = prevAsgn;
	_solver.getStats().assignmentsReusedByConservative++;
	return;
      }
    }
    _subSelector->getAssignment(_var, result);
    _prevAssignments.set(_var, result);
    return;
  }

private:
  ArrayMap<BoundNumber> _prevAssignments;
  ScopedPtr<AssignmentSelector> _subSelector;
};

/**
 * Class implementing the binary middle point selection of a value.
 * The basic idea behind this is as follows: start with the given bounds,
 * get the interval [floor(_lowerBound), ceil(_upperBound)], get the mean,
 * if this value is in the original interval, than this is the value we want.
 * If not, if the value is greater than _upperBound, than take the interval
 * [floor(lowerBound), newValue] and repeat the procedure. Stop when you find
 * the value that is in the original interval.
 */

class BinaryMiddlePointSelector : public ConvenientAssignmentSelector{
public:
  BinaryMiddlePointSelector(Solver& s) : ConvenientAssignmentSelector(s) {}
protected:
  /**
   * We are getting in this case if we have both _left and _right bounds.
   * @param result
   */
  virtual void getBoundedAssignment(BoundNumber& result) {
  CALL("BinaryMiddlePointSelector::getBoundedAssignment");
  if ( _leftBound == _rightBound ) {
    result = _leftBound;
    return ;
  }
  if ( usingPreciseNumbers() ) {
    //in case we are already using precise numbers, than simply pick a random value
    // in the interval
    //result = BoundNumber::getRandomValue(_leftBound, _rightBound);
    getMiddlePoint(_leftBound.floor(), _rightBound.ceil(),result);
    return;
  }
  //in the case where we use long doubles
  ASS( !usingPreciseNumbers() );
  getMiddlePoint(_leftBound.floor(), _rightBound.ceil(),result);

  }

  /**
   * in case we have no bounds than simply assign zero to the result and return
   * @param result
   */
  virtual void getUnboundedAssignment(BoundNumber& result){
    CALL("BinaryMiddlePointSelector::getUnboundedAssignment");
    result = BoundNumber::zero();
  }
  virtual void getLeftBoundedAssignment(BoundNumber& result){
    CALL("BinaryMiddlePointSelector::getLeftBoundedAssignment");
    if(_leftBound.isNegative()) {
          result = BoundNumber::zero();
        }
        else if(!_leftStrict) {
          result = _leftBound;
        }
        else {
          result = _leftBound+BoundNumber(0.125);
        }
  }
  /**
   * In case we have only right bound available then we do as follows:
   * if the rightBound is positive
   * @param result
   */
  virtual void getRightBoundedAssignment(BoundNumber& result){
    CALL("BinaryMiddlePointSelector::getRightBoundedAssignment");
    if (_rightBound.isPositive()) {
      result = BoundNumber::zero();
      return;
    }
    //_rightBound is negative
    if ( !_rightStrict ) {
      result = _rightBound;
    }
    else {
      //it might be a good idea to choose a different value then 0.125
      result = _rightBound-BoundNumber(0.125);
    }
  }

private:
  void getMiddlePoint(BoundNumber f_left, BoundNumber c_right, BoundNumber& result)
  {
    CALL("BinaryMiddlePointSelector::getMiddlePoint");
    ASS( !usingPreciseNumbers() );
    //at this point we are assured that the leftBound != rightBound
    //this also means that floor != ceil

    if ( f_left.isNegative() && c_right.isPositive() ) {
      BoundNumber interm = f_left+c_right;
      if ( interm.isZero() ) {
	result = BoundNumber::zero();
      }
      else {
	result = interm / BoundNumber::two();
      }
    }
    else {
      result = (f_left + c_right)/BoundNumber::two();
    }
    if (!withinBounds(result))
      {
      if (_leftBound > result)
	getMiddlePoint(result, c_right, result);
      else
	if( _rightBound < result)
	  getMiddlePoint(f_left, result, result);
      }

    else return;
  }
};

AssignmentSelector* AssignmentSelector::create(Solver& s, Options& opt)
{
  CALL("AssignmentSelector::create");

  AssignmentSelector* res;
  switch(opt.assignmentSelector()) {
  case Options::ASG_ALTERNATIVE:
    res = new AlternativeAssignmentSelector(s);
    break;
  case Options::ASG_MIDDLE:
    res = new MiddleAssignmentSelector(s);
    break;
  case Options::ASG_RANDOM:
    res = new RandomAssignmentSelector(s);
    break;
  case Options::ASG_RATIONAL:
	res = new RationalAssignmentSelector(s);
	break;
  case Options::ASG_SMALLEST:
    res = new SmallestAssignmentSelector(s);
    break;
  case Options::ASG_BIGGEST:
    res = new BiggestAssignmentSelector(s);
    break;
  case Options::ASG_BMP:
    res = new BinaryMiddlePointSelector(s);
    break;
  case Options::ASG_TIGHT:
    res = new TightAssignmentSelector(s);
    break;
  case Options::ASG_TIGHTISH:
    res = new TightishAssignmentSelector(s);
    break;
  case Options::ASG_LOWER:
    res = new LowerBoundAssignmentSelector(s);
    break;
  case Options::ASG_UPPER:
    res = new UpperBoundAssignmentSelector(s);
    break;
  default:
    ASSERTION_VIOLATION;
  }
  if(opt.conservativeAssignmentSelection()) {
    res = new ConservativeAssignmentSelector(s, res);
  }
  return res;
}


}
#endif //GNUMP

