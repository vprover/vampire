/**
 * @file Number.cpp
 * Implements class Number.
 */

#if GNUMP

#include <stdlib.h>
#include <cmath>
#include <limits>
#include <gmp.h>

#include "Lib/Exception.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Array.hpp"
#include "Number.hpp"

namespace Kernel
{

namespace __Aux_Number
{

bool nativeEqual(const NativeNumber& n1, const NativeNumber& n2)
{
  CALL("nativeEqual");

  NativeNumber diff=fabs(n1-n2);
  if(n1>1) {
    return diff<=(fabs(n1)*1E-11);
  }
  else {
    return diff<=1E-11;
  }
}

void reduceNumbers(size_t cnt, long double** vals)
{
  CALL("reduceNumbers");

  size_t i = 0;
  while(i<cnt && *vals[i]==0) { i++; }

  if(i==cnt) {
    return;
  }

  long double absVal = fabs(*vals[i]);
  long double smallest = absVal;
  long double largest = absVal;
  for(; i<cnt; i++) {
    absVal = fabs(*vals[i]);
    if(absVal==0) {
      continue;
    }
    if(smallest>absVal) {
      smallest = absVal;
    }
    if(largest<absVal) {
      largest = absVal;
    }
  }
  ASS_GE(largest,smallest);
  long double divisor;
  if(smallest>4) {
    divisor = smallest;
  }
  else if(largest<.25) {
    divisor = largest;
  }
  else {
    return;
  }
  ASS_G(divisor,0);
  for(size_t i=0; i<cnt; i++) {
    *vals[i]/=divisor;
  }
}

long long intGcd(long long a, long long b)
{
  long long tmp;
  while (b) {
    tmp = b;
    b = a % b;
    a = tmp;
  }
  return a;
}

bool getIntFromDouble(long double val, long long& res)
{
  CALL("getIntFromDouble");

  if(floorl(val)==val && val<numeric_limits<long long>::max()
      && val>numeric_limits<long long>::min()) {
    res = static_cast<long long>(val);
    return true;
  }
  return false;
}

void reduceIntNumbers(size_t cnt, long double** vals)
{
  CALL("reduceIntNumbers");

  size_t i = 0;
  while(i<cnt && *vals[i]==0) { i++; }

  if(i==cnt) {
    return;
  }

  long long ival;
  if(!getIntFromDouble(*vals[i], ival)) {
    return;
  }
  long long gcd_val = ::abs(ival);

  for(; i<cnt; i++) {
    if(!getIntFromDouble(*vals[i], ival)) {
      return;
    }
    if(ival==0) {
      continue;
    }
    gcd_val = intGcd(gcd_val, ::abs(ival));
  }

  if(gcd_val==1) {
    return;
  }
  ASS_G(gcd_val,1);
  for(size_t i=0; i<cnt; i++) {
    *vals[i]/=gcd_val;
  }
}

}

using namespace Lib;
using namespace __Aux_Number;


bool CommonNumberBase::_usePrecise = false;

NativeNumber CommonNumberBase::parseString(string str)
{
  CALL("CommonNumberBase::parseString");

  double dbl;
  Int::stringToDouble(str.c_str(), dbl);
  //ALWAYS(Int::stringToDouble(str.c_str(), dbl));
  return dbl;
}

unsigned CoeffNumber::hash(const CoeffNumber& n)
{
  CALL("CoeffNumber::hash");

  if(usePrecise()) {
    string str = n.precise().get_str(16);
    return Hash::hash(str);
  }
  else {
    if(n.isZero()) {
      return 1234; //some arbitrary number
    }
    //since we consider two numbers close enough to be equal, we need to
    //decrease precision before hashing in order to reduce the amount of cases
    //where two numbers we consider equal would have different hashes.
    float lowerPrec = static_cast<float>(n.native());
    return Hash::hash(lowerPrec);
  }
}

/**
 * If @c alowDecimal is true, the reduction of numbers may produce decimal numbers
 * if the imprecise representation is used.
 */
void CoeffNumber::reduceNumbers(size_t cnt, CoeffNumber** vals, bool allowDecimal)
{
  CALL("CoeffNumber::reduceNumbers");

  if(usePrecise()) {
    size_t i = 0;
    while(i<cnt && vals[i]->precise()==0) { i++; }

    if(i==cnt) {
      return;
    }

    mpz_class gcd_val = ::abs(vals[i]->precise());

    for(; i<cnt; i++) {
      if(vals[i]->precise()==0) {
	continue;
      }
      mpz_class absNum = ::abs(vals[i]->precise());
      mpz_gcd(gcd_val.get_mpz_t(), gcd_val.get_mpz_t(), absNum.get_mpz_t());
    }

    if(gcd_val==1) {
      return;
    }
    ASS_G(gcd_val,1);
    for(size_t i=0; i<cnt; i++) {
      vals[i]->precise()/=gcd_val;
    }
  }
  else {
    static Stack<long double*> numPtrs;
    numPtrs.reset();
    for(size_t i=0; i<cnt; i++) {
      numPtrs.push(&(vals[i]->native()));
    }
    if(allowDecimal) {
      __Aux_Number::reduceNumbers(cnt, numPtrs.begin());
    }
    else {
      __Aux_Number::reduceIntNumbers(cnt, numPtrs.begin());
    }
  }
}

BoundNumber BoundNumber::getRandomValue(const BoundNumber& min, const BoundNumber& max)
{
  CALL("BoundNumber::getRandomValue");

  ASS_L(min,max);
  if(usePrecise()) {
    static const unsigned randomDivisor = 64;
    Precise diff = max.precise()-min.precise();
    Precise part = (diff*(Random::getInteger(randomDivisor-2)+1))/randomDivisor;
    return BoundNumber(min.precise()+part);
  }
  else {
    return BoundNumber(Random::getDouble(min.native(), max.native()));
  }
}

BoundNumber BoundNumber::getMagicNumber(BoundNumber& rhs){
	CALL("BoundNumber::getMagicNumber");
	if (this->usePrecise()){
	    mpz_class intA(getPrecise().get_num()),
	    		intB(rhs.getPrecise().get_num()),
	    		decA(getPrecise().get_den()),
	    		decB(rhs.getPrecise().get_den());
		//intermediate integer part
	    int numb = 0;
	    Array<mpz_class>res;
	    //temporary results;
	    mpz_class tempA, tempDenA, tempB, tempDenB;

	    do{
	    	tempA = intA / decA;
	    	tempDenA = intA % decA;
	    	tempB = intB / decB;
	    	tempDenB = intB % decB;
	    	intA = decA;
	    	decA = tempDenA;
	    	intB = decB;
	    	decB = tempDenB;
	    	res[numb++] = tempA;
	    	}while(!mpz_cmp(tempA.__get_mp(), tempB.__get_mp()));

	    mpz_class den(1),num(1);
	    if(mpz_cmp(tempA.__get_mp(),tempB.__get_mp())>0){
	    	//take tempB
	    	den = tempB + den;
	    } else {
	    	//take tempA
	    	den = tempA + den;
	    }

	    for (int i = numb-2; i>0 ; i--) {
	    	mpz_class tempDen = den;
	    	den = (res[i] * den) + num;
	    	num = tempDen;
	    	}
	    num = res[0]*den + num;
	    mpq_class result(num, den);
	    return BoundNumber(result);
	}
	//if we are here that means we do not have to use precise representation
	ASS(!usePrecise());
    //this means we can pick any random value in the interval .. this is not the way it should be
	//but it serves the purpose of testing the precise pick of rational value
    return getRandomValue(BoundNumber(getNative()), rhs);


}

bool usingPreciseNumbers()
{
  CALL("usingPreciseNumbers");

  return CommonNumberBase::usePrecise();
}

/**
 * Switch from native number representation to a precise one.
 *
 * The member function @c transitionNativeToPrecise() must be
 * called on all currently existing numbers that are going to be
 * used after the switch.
 */
void switchToPreciseNumbers()
{
  CALL("switchToPreciseNumbers");
  ASS(!CommonNumberBase::usePrecise());
  LOG("tkv_precise","Switched to precise");
  CommonNumberBase::switchToPreciseNumbers();
  ASS(CommonNumberBase::usePrecise());
}

std::ostream& operator<< (ostream& out, const CoeffNumber& num)
{
  CALL("operator<<(ostream&,const CoeffNumber&)");

  if(CommonNumberBase::usePrecise()) {
    out<<num.precise();
  }
  else {
    out<<num.native();
  }
  return out;
}

std::ostream& operator<< (ostream& out, const BoundNumber& num)
{
  CALL("operator<<(ostream&,const BoundNumber&)");

  if(CommonNumberBase::usePrecise()) {
    out<<num.precise();
  }
  else {
    out<<num.native();
  }
  return out;
}

}
#endif

