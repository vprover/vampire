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
#include "Rational.hpp"


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

/**
 * Given a double number count how many decimals appear on the right hand side
 * of the "." The counting is done up to maximum MAX_DP precission. Default value
 * is 24, but precision can be increased if needed.
 * @param c dbVal - the double to count precision for
 */
int getDecimalPlaces(double dbVal)
{
  dbVal = fmod(dbVal, 1); /* NO NEED TO CONSIDER NUMBERS TO THE LEFT OF THE DECIMAL */
  static const int MAX_DP = 24;
  double THRES = pow(0.1, MAX_DP);
  if (dbVal == 0.0)
    return 0;
  int nDecimal = 0;

  /* MUST CHECK CEIL AND FLOOR DIFFERENCES */
  while (dbVal - floor(dbVal) > THRES &&
	 ceil(dbVal) - dbVal > THRES &&
	 nDecimal < MAX_DP)
    {
      dbVal *= 10.0;
      THRES *= 10.0; /* THRES MUST INCREASE AS THE NUMBER INCREASES */
      nDecimal++;
    }
  return nDecimal;
}

/**
 * Converts the value of
 * @param dbVal - the double to convert
 * into the rational number with
 * @param num - numerator
 * @param den - denominator .
 */
void doubleToRational(double dbVal, long long* num, long long* den){
	int noDec;
	noDec = getDecimalPlaces(dbVal);
	//if the number has no values after '.' than just set the denominator to 1
	//and the numerator to the casted value of the double
	if (noDec == 0){
		*den = 1;
		*num = (long long)dbVal;
		return;
	}
	//this approach does not normalize the rational number. An improvement would
	//be to divide both numbers by the gcd(den,num)
	*den = pow(10,noDec);
	dbVal = dbVal * (*den);
	//cut the integer part and store it into a temp
	long double temp;
	modf(dbVal, &temp);
	//cast and store the actual denominator
	*num = (long long)temp;
}

/**
 * Using the continuous fraction decomposition compute the number in the interval
 * [@param lhs, @param rhs]. And return a long double representation of the chosen
 * number
 */
long double getDoubleNumber(double lhs, double rhs) {
	long long numLhs, numRhs, denLhs, denRhs;
	//compute the rational numbers for lhs and rhs
	doubleToRational(lhs, &numLhs, &denLhs);
	doubleToRational(rhs, &numRhs, &denRhs);
	//if either of them is 0 then return 0 - this should never happen
	if ( nativeEqual(rhs,0) || nativeEqual(lhs,0) ){
		return 0.0;
	}
	//if the values are equal then return one of them
	if( nativeEqual(lhs,rhs)){
		return lhs;
	}
	//if the numbers have nothing after '.' do the mean
	if(denLhs==1 || denRhs==1){
		return (long double) (lhs+rhs)/2;
	}

	int noIntegerParts = 0;
	//intermediate integer part
	Array<long long> res;
	//temporary results;
	long long tempA, tempDenA, tempB, tempDenB;
	do {
		tempA = numLhs / denLhs;
		tempDenA = numLhs % denLhs;
		tempB = numRhs / denRhs;
		tempDenB = numRhs % denRhs;
		numLhs = denLhs;
		denLhs = tempDenA;
		numRhs = denRhs;
		denRhs = tempDenB;
		res[noIntegerParts++] = tempA;
	} while (tempA == tempB && denLhs != 0 && denRhs !=0);
	if (denLhs == 0 || denRhs==0){
		return (long double)(lhs+rhs)/2;
	}
	long long den = 1, num = 1;
	//we managed to find the first two different integer parts
	//if the difference occurs on the first step just do the mean
	if (noIntegerParts==1){
		return (long double)(rhs+lhs)/2;
	}
	//now pick the smallest one and add 1
	if (tempA > tempB) {
		//take tempB
		den = tempB + den;
	} else {
		//take tempA
		den = tempA + den;
	}

	long double result;
	//construct the new rational number
	for (int i = noIntegerParts - 2; i > 0; i--) {
		long long tempDen = den;
		den = (res[i] * den) + num;
		num = tempDen;
	}
	//add the initial integer part
	num = res[0] * den + num;
	//compute the actual value
	result = (long double) num / den;
	return result;
}


}

using namespace Lib;
using namespace __Aux_Number;



bool CommonNumberBase::_usePrecise = false;
bool CommonNumberBase::_useRationalRep = false;

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
  if (min == max) { return min; }
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

/**
 * get a number in the interval from this and the rhs. The value is computed
 * using the continued fraction decomposition algorithm.
 * details about the  algorithm:
 * @href http://en.wikipedia.org/wiki/Continued_fraction
 */
BoundNumber BoundNumber::getMagicNumber(BoundNumber& rhs){
	CALL("BoundNumber::getMagicNumber");
	if (this->usePrecise()){
		if(mpq_cmp( this->getPrecise().__get_mp(), rhs.getPrecise().__get_mp()))
			return rhs;

	    mpz_class numLhs(getPrecise().get_num()),
	    		numRhs(rhs.getPrecise().get_num()),
	    		denLhs(getPrecise().get_den()),
	    		denRhs(rhs.getPrecise().get_den());
		//intermediate integer part
	    if( !cmp(denLhs,1) || !cmp(denRhs,1)){
	    	mpq_class result(mpz_class(numLhs+numRhs),2);
	    	return BoundNumber(result);
	    }

	    int noIntegerParts = 0;
	    Array<mpz_class>res;
	    //temporary results;
	    mpz_class tempA, tempDenA, tempB, tempDenB;

	    do{
	    	tempA = numLhs / denLhs;
	    	tempDenA = numLhs % denLhs;
	    	tempB = numRhs / denRhs;
	    	tempDenB = numRhs % denRhs;
	    	numLhs = denLhs;
	    	denLhs = tempDenA;
	    	numRhs = denRhs;
	    	denRhs = tempDenB;
	    	res[noIntegerParts++] = tempA;
	    	}while(!mpz_cmp(tempA.__get_mp(), tempB.__get_mp()) && !mpz_cmp(denLhs.__get_mp(), 0) && !mpz_cmp(denRhs.__get_mp(),0));
	    if(!cmp(denRhs,0) || !cmp(denLhs,0)){
	    	return BoundNumber(mpq_class(getPrecise()+rhs.getPrecise())/2);
	    }
	    //special case if we manage to do only one computation, that means we differ at first division
	    if( noIntegerParts==1 ){
	    	return BoundNumber(mpq_class(getPrecise()+rhs.getPrecise())/2);
	    }

	    mpz_class den(1),num(1);
	    if(mpz_cmp(tempA.__get_mp(),tempB.__get_mp())>0){
	    	//take tempB
	    	den = tempB + den;
	    } else {
	    	//take tempA
	    	den = tempA + den;
	    }

	    for (int i = noIntegerParts-2; i>0 ; i--) {
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
	NativeNumber left, right;
	left = getNative();
	right = rhs.getNative();

    return BoundNumber(getDoubleNumber((double)left,(double)right));

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

void switchToRationalNumbers(){
	CALL("switchToRationalNumbers()");
	ASS(!CommonNumberBase::useRational());
	LOG("tkv_precise", "switched to rational");
	CommonNumberBase::switchToRational();
	ASS(CommonNumberBase::useRational());
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

