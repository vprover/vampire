
/*
 * File Number.hpp.
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
 * @file Number.hpp
 * Defines class Number.
 */

#ifndef __Number__
#define __Number__
#if GNUMP
#include <iosfwd>
#include <gmpxx.h>

#include "Forwards.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Rational.hpp"

#include <cmath>


namespace Kernel {

namespace __Aux_Number
{

typedef double NativeNumber;

bool nativeEqual(const NativeNumber& n1, const NativeNumber& n2);

class CommonNumberBase
{
public:
  static bool usePrecise() { return _usePrecise; }
  static void switchToPreciseNumbers() { _usePrecise = true; _useRational=false; }

  static bool useRational() {return _useRational;}
  static void switchToRationalNumbers() {_useRational = true; _usePrecise=false; }
protected:

  static NativeNumber parseString(vstring str);

  static bool _usePrecise;
  static bool _useRational;
};

/**
 * Flexible number representation.
 */
template<class T, class Rat, class PrecCl>
class NumberBase : protected CommonNumberBase
{
public:
  typedef PrecCl Precise;
  typedef Rat NativeRational;

  /** Created uninitialized number */
  NumberBase() : _isPrecise(false),_isRational(false) {}

  explicit NumberBase(const NativeNumber val) : _isPrecise(false), _isRational(false) {
    CALL("NumberBase(Native)");
	  if(usePrecise()) {
      initPrecise();
      precise() = static_cast<double>(val);
    }
    else if(useRational()){
    	initRational();
    	rational() = val;
    }
    else {
      native() = val;
    }

  }
  explicit NumberBase(const Precise& val) : _isPrecise(false), _isRational(false) {
    CALL("NumberBase(Precise)");
    ASS(usePrecise());
    initPrecise();
    precise() = val;
  }
  explicit NumberBase(Rational val) : _isPrecise(false), _isRational(false){
	  ASS(useRational());
	  initRational();
	  rational() = val;
  }
  template<class T2, class Ratio, class Prec2>
  explicit NumberBase(const NumberBase<T2,Ratio,Prec2>& val) : _isPrecise(false),_isRational(false) {
    if(usePrecise()) {
      initPrecise();
      precise() = val.precise();
    }
    else if(useRational()){
    	initRational();
    	rational() = val.native();
    }
    else {
    	native() = val.native();
    }
  }
  NumberBase(const NumberBase& val) : _isPrecise(false),_isRational(false) {
    if(usePrecise()) {
      initPrecise();
      precise() = val.precise();
    }else if(useRational()){
    	initRational();
    	rational() = val.rational();
    }
    else {
      native() = val.native();
    }
  }

  ~NumberBase() {
  /*  if(_isPrecise) {
      destroyPrecise();
  */
  }

  NumberBase& operator=(const NumberBase& val) {
    if(usePrecise()) {
      if(!_isPrecise) {
    	  initPrecise();
      }
      precise() = val.precise();
    }
    else if(useRational()){
    	if(!_isRational){
    		initRational();
    	}
    	rational() = val.rational();
    }
    else {
      native() = val.native();
    }
    return *this;
  }

  //basic operations
  T operator+(const T& o) const {
    if(usePrecise()) {
      return T(precise()+o.precise());
    }
    else if(useRational()){
    	return T(rational()+o.rational());
    }
    else {
      return T(native()+o.native());
    }
  }
  T operator-() const {
    if(usePrecise()) {
      return T(-precise());
    }
    else if(useRational()){
    	return T(-rational());
    }
    else {
      return T(-native());
    }
  }
  T operator-(const T& o) const {
    if(usePrecise()) {
      return T(precise()-o.precise());
    }
    else if(useRational()){
    	return T(rational()-o.rational());
    }
    else {
      return T(native()-o.native());
    }
  }
  T operator*(const T& o) const {
    if(usePrecise()) {
      return T(precise()*o.precise());
    }
    else if(useRational()){
    	return T(rational()*o.rational());
    }
    else {
      return T(native()*o.native());
    }
  }
  bool operator==(const T& o) const {
    if(usePrecise()) {
      return precise()==o.precise();
    }
    else if(useRational()){
    	return rational()==o.rational();
    }
    else {
      return nativeEqual(native(), o.native());
    }
  }
  bool operator>(const T& o) const {
    if(usePrecise()) {
      return precise()>o.precise();
    }
    else if(useRational()){
    	return rational()>o.rational();
    }
    else {
      return (*this)!=o && native()>o.native();
    }
  }
  /** Absolute value of the number */
  T abs() const {
    if(usePrecise()) {
      return T(::abs(precise()));
    }
    else if(useRational()){
    	return T(rational().isNegative() ? (-rational()) : rational());

    }
    else {
      return T((native()<0) ? (-native()) : native());
    }
  }
  /**Ceil of the number*/
  T ceil() const {
	  if(usePrecise()){
		  return T(::abs(::ceil((mpf_class)(precise()))));
	  }
	  else if(useRational()){
		  //check about ceil for rational numbers... this doesn't make sense
		  return T(rational());
	  }
	  else {
		  ASS(!usePrecise());
		  return T(ceill(native()));
	  }
  }

  /**Floor of the number*/
  T floor() const {
	  if(usePrecise()){
	  		  return T(::abs(::floor((mpf_class)(precise()))));
	  	  }
	  else if(useRational()){
		  return T(rational());
	  }
	  else {
	  	  ASS(!usePrecise());
	  	  return T(floorl(native()));
	  }
  }

  //useful constants
  static const T& zero() { static T res(0); return res; }
  static const T& one() { static T res(1); return res; }
  static const T& minusOne() { static T res(-1); return res; }
  static const T& two() { static T res(2); return res; }

  //derived operations
  bool operator!=(const T& o) const { return !(static_cast<const T&>(*this)==o); }
  bool operator<(const T& o) const { return o>static_cast<const T&>(*this); }
  bool operator>=(const T& o) const { return !(o>static_cast<const T&>(*this)); }
  bool operator<=(const T& o) const { return !(static_cast<const T&>(*this)>o); }

  T& operator+=(const T& o) {
    if(usePrecise()) {
      precise()+=o.precise();
    }
    else if(useRational()){
    	rational()+=o.rational();
    }
    else {
      native()+=o.native();
    }
    return static_cast<T&>(*this);
  }
  T& operator-=(const T& o) {
    if(usePrecise()) {
      precise()-=o.precise();
    }
    else if(useRational()){
    	rational()-=o.rational();
    }
    else {
      native()-=o.native();
    }
    return static_cast<T&>(*this);
  }
  T& operator*=(const T& o) {
    if(usePrecise()) {
      precise()*=o.precise();
    }
    else if(useRational()){
    	rational()*=o.rational();
    }
    else {
      native()*=o.native();
    }
    return static_cast<T&>(*this);
  }

  bool isPositive() const { return (*this)>zero(); }
  bool isNegative() const { return (*this)<zero(); }
  bool isZero() const { return (*this)==zero(); }

  bool isPositiveAssumingNonzero() const {
    if(usePrecise()) {
      return precise()>0;
    }
    else if(useRational()){
    	return rational().isPositiveNonZero();
    }
    else {
      return native()>0;
    }
  }
  bool isNegativeAssumingNonzero() const {
    return !isPositiveAssumingNonzero();
  }


  void transitionNativeToPrecise()
  {
    CALL("NumberBase::transitionNativeToPrecise");
    ASS(usePrecise());
    if(!useRational()){
    	NativeNumber val=_native;
    	if(static_cast<double>(val)!=static_cast<double>(val)){
    		cout<<_native<<static_cast<double>(val);
    		cout<<_native<<endl;
    		ASSERTION_VIOLATION;
    	}
    	
    	initPrecise();
    	precise() = static_cast<double>(val); //GMP does not accept long double
    }
    else {
    	double val = double(_rational);
    	initPrecise();
    	precise() = val;
    }
  }
  void transitionNativeToRational(){
	  CALL("NumberBase::transitionNativeToRational");
	  ASS(useRational());
	  NativeNumber val = _native;
	  initRational();
	  rational() = static_cast<double>(val);

  }

  NativeNumber native() const { ASS(!usePrecise()); return _native; }
  const Precise& precise() const { return const_cast<NumberBase&>(*this).precise(); }
  const Rational& rational() const {return const_cast<NumberBase&>(*this).rational();}
protected:
  NativeNumber& native() { ASS(!usePrecise()); return _native; }

  void initPrecise() {
    CALL("NumberBase::initPrecise");

    _isPrecise = true;
    _isRational = false;
    new(&precise()) Precise();
  }

  void initRational() {
	  CALL("NumberBase::initRational");

	  _isRational = true;
	  _isPrecise = false;

	  new(&rational()) NativeRational();

  }
  void destroyPrecise() {
    CALL("NumberBase::destroyPrecise")
    ASS(_isPrecise);

  //  precise().~Precise();
  }

  Precise& precise() {
    ASS(usePrecise());
    if(!_isPrecise) {
      transitionNativeToPrecise();
    }
    return _precise;
  }

  NativeRational& rational(){
	  ASS(useRational());
	  if(!_isRational){
		  initRational();
		  rational() = _native;
	  }
	  return _rational;
  }

private:
  /*//It is important that the placeholder is an array of chars -- otherwise
  //we would break aliasing assumpions made by the compiler.
  typedef char PrecisePlaceholder[sizeof(Precise)];

  union {
    NativeNumber _native;
    *
     * The precise number usually has a constructor and therefore
     * cannot be used inside a union. To go around this limitation
     * we have a placeholder and do the construction when it is
     * needed.

    PrecisePlaceholder _precise;
  };*/
  NativeNumber _native;
  Precise _precise;
  NativeRational _rational;

  bool _isPrecise;
  bool _isRational;
};

typedef NumberBase<CoeffNumber, Rational,  mpz_class> CoeffNumberBase;
typedef NumberBase<BoundNumber, Rational, mpq_class> BoundNumberBase;

}

using namespace __Aux_Number;

/** Type that represents values being used as coeffitients in constraints */
class CoeffNumber : public CoeffNumberBase
{
public:
  /** Created uninitialized number */
  CoeffNumber() {}
  explicit CoeffNumber(const NativeNumber val) : CoeffNumberBase(val) {}
  explicit CoeffNumber(const NativeRational val) : CoeffNumberBase(val) {}
  explicit CoeffNumber(const Precise& val) : CoeffNumberBase(val) {}
  explicit CoeffNumber(vstring val) : CoeffNumberBase(parseString(val)) {}

  static void reduceNumbers(size_t cnt, CoeffNumber** vals, bool allowDecimal=true);

  static unsigned hash(const CoeffNumber& n);
};

/** Type that represents values being used as bounds */
class BoundNumber : public BoundNumberBase
{
public:
  BoundNumber() {}
  explicit BoundNumber(const NativeNumber val) : BoundNumberBase(val) {}
  explicit BoundNumber(const NativeRational val) : BoundNumberBase(val){}
  explicit BoundNumber(const Precise& val) : BoundNumberBase(val) {}
  explicit BoundNumber(const CoeffNumber& val) : BoundNumberBase(val) {}
  explicit BoundNumber(vstring val) : BoundNumberBase(parseString(val)) {}

  static BoundNumber getRandomValue(const BoundNumber& min, const BoundNumber& max);
  BoundNumber getMagicNumber(BoundNumber& rhs);
  using BoundNumberBase::operator*;

  BoundNumber operator*(const CoeffNumber& o) const {
    if(usePrecise()) {
      return BoundNumber(precise()*o.precise());
    }
    else if(useRational()){
    	return BoundNumber(rational()*o.rational());
    }
    else {
      return BoundNumber(native()*o.native());
    }
  }

  BoundNumber operator/(const BoundNumber& o) const {
    CALL("BoundNumber::operator/(const BoundNumber&)");
    ASS(!o.isZero());
    if(usePrecise()) {
      return BoundNumber(precise()/o.precise());
    }
    else if(useRational()){
    	return BoundNumber(rational()/o.rational());
    }
    else {
      return BoundNumber(native()/o.native());
    }
  }
  BoundNumber operator/(const CoeffNumber& o) const {
    CALL("BoundNumber::operator/(const CoeffNumber&)");
    ASS(!o.isZero());

    if(usePrecise()) {
      return BoundNumber(precise()/o.precise());
    }
    else if(useRational()){
    	return BoundNumber(rational()/o.rational());
    }
    else {
      return BoundNumber(native()/o.native());
    }
  }
  BoundNumber& operator/=(const BoundNumber& o) {
    CALL("BoundNumber::operator/=");
    ASS(!o.isZero());
    if(usePrecise()) {
      precise()/=o.precise();
    }
    else if(useRational()){
    	rational()/=o.rational();
    }
    else {
      native()/=o.native();
    }
    return *this;
  }
  const NativeNumber getNative() const {ASS(!usePrecise() && !useRational()); return native();}
  const Precise& getPrecise() const {ASS(usePrecise() && !useRational()); return precise();}
  const Rational& getRational() const {ASS(useRational() && !usePrecise()); return rational();}
};

void switchToPreciseNumbers();
bool usingPreciseNumbers();
void switchToRationalNumbers();
bool usingRationalNumbers();

std::ostream& operator<< (ostream& out, const CoeffNumber& num);
std::ostream& operator<< (ostream& out, const BoundNumber& num);

}

#endif //IS_GNUMP
#endif // __Number__
