/*
 * Rational.cpp
 *
 *  Created on: Apr 15, 2013
 *      Author: ioan
 */
#if GNUMP
#include "Rational.hpp"

#include <stdlib.h>
#include <cmath>
#include <limits>
#include <gmp.h>
#include <gmpxx.h>

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
/**
 * Constructor that initializes the rational number from a double value
 * @b value
 */
Rational::Rational(double value){
	CALL("Rational::Rational(double value)");
	//this is not the best way to do the conversion, but at least is safe!
	//The implementation should be done by us.
	mpq_class number(value);
	number.canonicalize();
	if (number.get_den().fits_slong_p() && number.get_num().fits_slong_p()){
		_num = number.get_num().get_si();
		_den = number.get_den().get_si();
	}
	else {
		//this is the case when we cannot convert the double into a rational number
		throw NumberImprecisionException();
	}
}

Rational::Rational(long double value){
	CALL("Rational::Rational(double value)");
	//this is not the best way to do the conversion, but at least is safe!
	//The implementation should be done by us.
	mpq_class number(static_cast<double>(value));
	number.canonicalize();
	if (number.get_den().fits_slong_p() && number.get_num().fits_slong_p()){
		_num = number.get_num().get_si();
		_den = number.get_den().get_si();
	}
	else {
		//this is the case when we cannot convert the double into a rational number
		throw NumberImprecisionException();
	}
}

/**
 * Constructor that initializes the rational number from a string
 * @b value
 */
Rational::Rational(string value){
	CALL("Rational::Rational(string value)");
	double doubleNumber;
	if ( !(Int::stringToDouble(value, doubleNumber))){
		throw NumberImprecisionException();
	}
	//this is not the best way to do the conversion, but at least is safe!
	//The implementation should be done by us.
	mpq_class number(doubleNumber);
	number.canonicalize();
	if (number.get_den().fits_slong_p() && number.get_num().fits_slong_p()){
		_num = number.get_num().get_si();
		_den = number.get_den().get_si();
	}
	else {
		//this is the case when we cannot convert the double into a rational number
		throw NumberImprecisionException();
	}


}

Rational Rational::operator*(const Rational& o) const{
	CALL("Rational operator*");
	Rational result(safeMul(_num,o._num), safeMul(_den,o._den));
	result = result.canonical();
	return result;
}


Rational Rational::operator/(const Rational& o) const{
	CALL("Rational::operator/");
	//must take care of the sign first
	long long num1, num2;
	if ( (o._num < 0 && _num < 0) || o._num < 0 )
	{
		num1 = -_num;
		num2 = -o._num;
	}
	else {
		num1 = _num;
		num2 = o._num;
	}
	Rational r1 = Rational(num1, num2).canonical();
	Rational r2 = Rational(_den, o._den).canonical();
	return (r1*r2);
}

Rational Rational::operator+(const Rational& o) const{
	CALL("Rational::operator+");
	if ( _den == o._den){
		Rational result(safeAdd(_num,o._num), o._den);
		result = result.canonical();
		return result;
	}

	Rational result(_num, _den);
	result._den= safeMul(result._den,o._den);
	result._num = safeAdd( safeMul(result._num,o._den) , safeMul(o._num,result._den));
	result = result.canonical();
	return result;
}

Rational Rational::operator-() const{
	CALL("Rational::operator-(unary)");
	Rational result;
	result._den = _den;
	result._num = -_num;
	return result;
}

Rational Rational::operator-(const Rational& o) const{
	CALL("Rational::operator-(Rational )");
	double den, num;
	if (_den == o._den){
		return Rational(safeSub(_num,o._num), o._den).canonical();
	}

	den = safeSub(safeMul((_den),o._num) , safeMul((_num),o._den));
	num = safeMul(_den,o._den);
	return Rational(num, den).canonical();
}

Rational& Rational::operator+=(const Rational& o){
	CALL("Rational::operator+=");
	if(sameDenominator(*this, o)){
		*this = Rational(safeAdd(_num,o._num),o._den).canonical();
		return static_cast<Rational&>(*this);
	}
	else {
		_num = safeAdd(safeMul(_num, o._num),safeMul(_den,o._num));
		_den = safeMul(_den,o._den);
		*this = (*this).canonical();
		return static_cast<Rational&>(*this);
	}
}

Rational& Rational::operator-=(const Rational& o){
	CALL("Rational::operator-=");
	if(sameDenominator(*this, o)){
			*this = Rational(safeSub((*this)._num,o._num),o._den).canonical();
			return static_cast<Rational&>(*this);
		}
	else {
		_num = safeSub(safeMul(_num,o._den), safeMul(_den,o._num));
		_den = safeMul(_den,o._den);
		*this = (*this).canonical();
		return static_cast<Rational&>(*this);
	}
}

Rational& Rational::operator*=(const Rational& o){
	CALL("Rational::operator*=");
	*this = Rational((*this)*o).canonical();
	return static_cast<Rational&>(*this);
}

Rational& Rational::operator/=(const Rational& o){
	CALL( "Rational::operator/=");
	Rational v(*this);
	*this = Rational(v* o.inverse()).canonical();
	return static_cast<Rational&>(*this);
}

Rational& Rational::operator++(){
	CALL("Rational::operator++");
	*this = Rational((*this)+Rational::one());
	return static_cast<Rational&>(*this);
}
Rational& Rational::operator--(){
	CALL("Rational::operator--");
	*this = Rational((*this)-Rational::one());
	return static_cast<Rational&>(*this);
}

bool Rational::operator >(const Rational& o ) const{
	CALL("Rational::operator>");
	if ( (*this)._den == o._den && (*this)._num > o._num ){
		return true;
	}
	//this means they have different denominators
	return (safeMul( (*this)._num , o._den ) > safeMul( (*this)._den , o._num) );
}

bool Rational::operator <(const Rational& o) const{
	CALL("Rational::operator<");
	if ( (*this)._den == o._den && (*this)._num < o._num ){
			return true;
		}
	//this means they have different denominators
	return safeMul((*this)._num,o._den) < safeMul((*this)._den,o._num);
}

bool Rational::operator >=(const Rational& o) const{
	CALL("Rational::operator>=");
	if ( (*this)._den == o._den && (*this)._num >= o._num ){
			return true;
		}
	//this means they have different denominators
	return safeMul((*this)._num,o._den) >= safeMul((*this)._den,o._num);
}

bool Rational::operator <=(const Rational& o) const{
	CALL("Rational::operator<=");
	if ( (*this)._den == o._den && (*this)._num <= o._num ){
			return true;
		}
	//this means they have different denominators
	return safeMul((*this)._num,o._den) <= safeMul((*this)._den,o._num);
}

//this should divide both numerator and denominator by the gcd and return the obtained values
Rational Rational::canonical(){
	CALL("Rational::canonical");
	Rational result;
	bool isNeg = isNegative();
	result = abs();
	long long a;
	unsigned long long b;
	a = result._num;
	b = result._den;
	unsigned long long tmp = GCD(a,b);

	result = Rational( safeDiv(result._num, tmp), safeDiv(result._den, tmp));

	return isNeg ? -result : result;

}

string Rational::toString(){
	char tmp_num[256];
	sprintf(tmp_num, "%lld",_num);
	string num(tmp_num);
	char tmp_den[256];
	sprintf(tmp_den,"%lld",_den);
	string den(tmp_den);
	return num+"/"+den;
}


unsigned long long GCD(long long n1, long long n2){

	CALL("GCD(long long , unsigned long long )");
	ASS(n1 != 0 && n2 != 0);
	long long a, b;
	if (n1 < 0) {
		a = -(n1);
	}
	else {
		a = n1;
	}
	b = n2;

	long long tmp;
	while(b) {
		tmp = b;
		b = safeModulo(a,b);
		a = tmp;
	}
	return tmp;
}

//this solution is based on the #include <climits>
/**
 * Function for testing if by adding the numbers @b n1
 * and @b n2 produces an overflow. Returns true if the overflow is possible
 */
bool additionOverflow(long long n1, long long n2){
	return (((n2>0) && (n1 > (LLONG_MAX-n2)))
			 || ((n2<0) && (n1 < (LLONG_MIN-n2))));
}

/**
 * Function for testing if by subtracting @b n1 - @b n2 produces an overflow.
 * Returns true if this is the case.
 */
bool subtractionOverflow(long long n1, long long n2){
	return ((n2 > 0 && n1 < LLONG_MIN + n2) ||
		    (n2 < 0 && n1 > LLONG_MAX + n2));
}

/**
 * Function for testing if by the multiplication of @b n1 * @b n2 produces
 * overflow. Returns true if this is the case.
 */
bool multiplicationOverflow(long long n1, long long n2){
	if (n1 > 0){  /* n1 is positive */
	  if (n2 > 0) {  /* n1 and n2 are positive */
	    if (n1 > (LLONG_MAX / n2)) {
	      /* Handle error condition */
	    	return true;
	    }
	  } /* end if n1 and n2 are positive */
	  else { /* n1 positive, n2 non-positive */
	    if (n2 < (LLONG_MIN / n1)) {
	        /* Handle error condition */
	    	return true;
	    }
	  } /* n1 positive, n2 non-positive */
	} /* end if n1 is positive */
	else { /* n1 is non-positive */
	  if (n2 > 0) { /* n1 is non-positive, n2 is positive */
	    if (n1 < (LLONG_MIN / n2)) {
	      /* Handle error condition */
	    	return true;
	    }
	  } /* end if n1 is non-positive, n2 is positive */
	  else { /* n1 and n2 are non-positive */
	    if ( (n1 != 0) && (n2 < (LLONG_MAX / n1))) {
	      /* Handle error condition */
	    	return true;
	    }
	  } /* end if n1 and n2 are non-positive */
	} /* end if n1 */
	return false;
}

/**
 * Helping function which returns true if the long long division might overflow.
 * Order of the parameters is important, since we also consider the case of
 * division by zero.
 * @b numerator takes the numerator of the fraction
 * @b denominator takes the denominator of the fraction
 * Return true if the overflow occurs.
 */
bool divisionOverflow(long long numerator, long long denominator){
	return ( (denominator == 0) || ( (numerator == LLONG_MIN) && (denominator == -1) ) );
}

/**
 * Overflow can occur during a modulo operation when the dividend is equal to the
 * minimum (negative) value for the signed integer type and the divisor is equal to −1.
 * This occurs despite that the result of such a modulo operation should theoretically be 0.
 * Again order of the parameters matters so we have @b numerator % @b denominator.
 * Return true if the overflow occurs.
 * */
bool moduloOverflow(long long numerator, long long denominator){
	return ((denominator == 0) || ((numerator == LLONG_MIN) && (denominator == -1)));
}

//addition with overflow check
long long safeAdd(long long n1, long long n2){
		CALL("Rational::safeAdd");
		if (additionOverflow(n1, n2)){
			throw Rational::NumberImprecisionException();
		}
		return n1+n2;
}
//subtraction with overflow check
long long safeSub(long long n1, long long n2) {
	CALL("Rational::safeSub");
	if (subtractionOverflow(n1, n2)) {
		throw Rational::NumberImprecisionException();
	}
	return n1 - n2;
}
//multiplication with overflow check
long long safeMul(long long n1, long long n2) {
	CALL("Rational::safeMul");
	if (multiplicationOverflow(n1, n2)) {
		throw Rational::NumberImprecisionException();
	}
	return n1 * n2;
}
//division with overflow check
long long safeDiv(long long n1, long long n2) {
	CALL("Rational::safeDiv");
	if (divisionOverflow(n1, n2)) {
		throw Rational::NumberImprecisionException();
	}
	return n1 / n2;
}
//modulo operator with overflow check
long long safeModulo(long long n1, long long n2) {
	CALL("Rational::safeModulo");
	if (moduloOverflow(n1, n2)) {
		throw Rational::NumberImprecisionException();
	}
	return n1 % n2;
}

}//__AUX_NUMBER
}//Kernel

#endif //GNUMP

