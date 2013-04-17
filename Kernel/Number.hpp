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
#include <cmath>

namespace Kernel {

namespace __Aux_Number
{

typedef long double NativeNumber;

bool nativeEqual(const NativeNumber& n1, const NativeNumber& n2);

class CommonNumberBase
{
public:
  static bool usePrecise() { return _usePrecise; }
  static void switchToPreciseNumbers() { _usePrecise = true; }

protected:

  static NativeNumber parseString(string str);

  static bool _usePrecise;
};

/**
 * Flexible number representation.
 */
template<class T, class PrecCl>
class NumberBase : protected CommonNumberBase
{
public:
  typedef PrecCl Precise;

  /** Created uninitialized number */
  NumberBase() : _isPrecise(false) {}

  explicit NumberBase(NativeNumber val) : _isPrecise(false) {
    if(usePrecise()) {
      initPrecise();
      precise() = static_cast<double>(val);
    }
    else {
      native() = val;
    }
  }
  explicit NumberBase(const Precise& val) : _isPrecise(false) {
    ASS(usePrecise());
    initPrecise();
    precise() = val;
  }
  template<class T2, class Prec2>
  explicit NumberBase(const NumberBase<T2,Prec2>& val) : _isPrecise(false) {
    if(usePrecise()) {
      initPrecise();
      precise() = val.precise();
    }
    else {
      native() = val.native();
    }
  }
  NumberBase(const NumberBase& val) : _isPrecise(false) {
    if(usePrecise()) {
      initPrecise();
      precise() = val.precise();
    }
    else {
      native() = val.native();
    }
  }
  ~NumberBase() {
    if(_isPrecise) {
      destroyPrecise();
    }
  }


  NumberBase& operator=(const NumberBase& val) {
    if(usePrecise()) {
      if(!_isPrecise) {
	initPrecise();
      }
      precise() = val.precise();
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
    else {
      return T(native()+o.native());
    }
  }
  T operator-() const {
    if(usePrecise()) {
      return T(-precise());
    }
    else {
      return T(-native());
    }
  }
  T operator-(const T& o) const {
    if(usePrecise()) {
      return T(precise()-o.precise());
    }
    else {
      return T(native()-o.native());
    }
  }
  T operator*(const T& o) const {
    if(usePrecise()) {
      return T(precise()*o.precise());
    }
    else {
      return T(native()*o.native());
    }
  }
  bool operator==(const T& o) const {
    if(usePrecise()) {
      return precise()==o.precise();
    }
    else {
      return nativeEqual(native(), o.native());
    }
  }
  bool operator>(const T& o) const {
    if(usePrecise()) {
      return precise()>o.precise();
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
    else {
      return T((native()<0) ? (-native()) : native());
    }
  }

  /**Ceil of the number*/
  T ceil() const {
	  if(usePrecise()){
		  return T(::abs(::ceil((mpf_class)(precise()))));
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
    else {
      native()+=o.native();
    }
    return static_cast<T&>(*this);
  }
  T& operator-=(const T& o) {
    if(usePrecise()) {
      precise()-=o.precise();
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

    NativeNumber val = _native;
    initPrecise();
    precise() = static_cast<double>(val); //GMP does not accept long double
  }
  
  const NativeNumber native() const { ASS(!usePrecise()); return _native; }
  const Precise& precise() const { return const_cast<NumberBase&>(*this).precise(); }
protected:
  NativeNumber& native() { ASS(!usePrecise()); return _native; }

  void initPrecise() {
    CALL("NumberBase::initPrecise");

    _isPrecise = true;
    new(&precise()) Precise();
  }
  void destroyPrecise() {
    CALL("NumberBase::destroyPrecise")
    ASS(_isPrecise);

    precise().~Precise();
  }

  Precise& precise() {
    ASS(usePrecise());
    if(!_isPrecise) {
      transitionNativeToPrecise();
    }
    return *reinterpret_cast<Precise*>(_precise);
  }

private:
  //It is important that the placeholder is an array of chars -- otherwise
  //we would break aliasing assumpions made by the compiler.
  typedef char PrecisePlaceholder[sizeof(Precise)];

  union {
    NativeNumber _native;
    /**
     * The precise number usually has a constructor and therefore
     * cannot be used inside a union. To go around this limitation
     * we have a placeholder and do the construction when it is
     * needed.
     */
    PrecisePlaceholder _precise;
  };
  bool _isPrecise;
};

typedef NumberBase<CoeffNumber, mpz_class> CoeffNumberBase;
typedef NumberBase<BoundNumber, mpq_class> BoundNumberBase;

}

using namespace __Aux_Number;

/** Type that represents values being used as coeffitients in constraints */
class CoeffNumber : public CoeffNumberBase
{
public:
  /** Created uninitialized number */
  CoeffNumber() {}
  explicit CoeffNumber(NativeNumber val) : CoeffNumberBase(val) {}
  explicit CoeffNumber(const Precise& val) : CoeffNumberBase(val) {}
  explicit CoeffNumber(string val) : CoeffNumberBase(parseString(val)) {}

  static void reduceNumbers(size_t cnt, CoeffNumber** vals, bool allowDecimal=true);

  static unsigned hash(const CoeffNumber& n);
};

/** Type that represents values being used as bounds */
class BoundNumber : public BoundNumberBase
{
public:
  BoundNumber() {}
  explicit BoundNumber(NativeNumber val) : BoundNumberBase(val) {}
  explicit BoundNumber(const Precise& val) : BoundNumberBase(val) {}
  explicit BoundNumber(const CoeffNumber& val) : BoundNumberBase(val) {}
  explicit BoundNumber(string val) : BoundNumberBase(parseString(val)) {}

  static BoundNumber getRandomValue(const BoundNumber& min, const BoundNumber& max);

  using BoundNumberBase::operator*;

  BoundNumber operator*(const CoeffNumber& o) const {
    if(usePrecise()) {
      return BoundNumber(precise()*o.precise());
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
    else {
      native()/=o.native();
    }
    return *this;
  }
  BoundNumber getMagicNumber(BoundNumber& rhs);
  const NativeNumber getNative() const {ASS(!usePrecise()); return native();}
  const Precise& getPrecise() const {ASS(usePrecise()); return precise();}
};

void switchToPreciseNumbers();
bool usingPreciseNumbers();

std::ostream& operator<< (ostream& out, const CoeffNumber& num);
std::ostream& operator<< (ostream& out, const BoundNumber& num);

}
#endif
#endif // __Number__
