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

Rational Rational::operator*(const Rational& o) const{
	CALL("Rational operator*");
	Rational result(_num*o._num, _den*o._den);
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
		Rational result(_num+o._num, o._den);
		result = result.canonical();
		return result;
	}

	Rational result(_num, _den);
	result._den= result._den*o._den;
	result._num = result._num*o._den + o._num*result._den;
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
		return Rational((_num-o._num), o._den).canonical();
	}

	den = (_den)*o._num - (_num)*o._den;
	num = (_den*o._den);
	return Rational(num, den).canonical();
}

Rational& Rational::operator+=(const Rational& o){
	CALL("Rational::operator+=");
	if(sameDenominator(*this, o)){
		*this = Rational(_num+o._num,o._den).canonical();
		return static_cast<Rational&>(*this);
	}
	else {
		_num = _num* o._num + _den*o._num;
		_den = _den*o._den;
		*this = (*this).canonical();
		return static_cast<Rational&>(*this);
	}
}

Rational& Rational::operator-=(const Rational& o){
	CALL("Rational::operator-=");
	if(sameDenominator(*this, o)){
			*this = Rational((*this)._num-o._num,o._den).canonical();
			return static_cast<Rational&>(*this);
		}
	else {
		_num = _num*o._den - _den*o._num;
		_den = _den*o._den;
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
	return ((*this)._num*o._den) > ((*this)._den*o._num);
}

bool Rational::operator <(const Rational& o) const{
	CALL("Rational::operator<");
	if ( (*this)._den == o._den && (*this)._num < o._num ){
			return true;
		}
	//this means they have different denominators
	return ((*this)._num*o._den) < ((*this)._den*o._num);
}

bool Rational::operator >=(const Rational& o) const{
	CALL("Rational::operator>=");
	if ( (*this)._den == o._den && (*this)._num >= o._num ){
			return true;
		}
	//this means they have different denominators
	return ((*this)._num*o._den) >= ((*this)._den*o._num);
}

bool Rational::operator <=(const Rational& o) const{
	CALL("Rational::operator<=");
	if ( (*this)._den == o._den && (*this)._num <= o._num ){
			return true;
		}
	//this means they have different denominators
	return ((*this)._num*o._den) <= ((*this)._den*o._num);
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

	result = Rational(result._num / tmp, result._den / tmp);

	return isNeg ? -result : result;

}


unsigned long long GCD(long long n1, unsigned long long n2){

	CALL("GCD(long long , unsigned long long )");
	ASS(n1 != 0 && n2 != 0);
	unsigned long long a, b;
	if (n1 < 0) {
		a = -(n1);
	}
	else {
		a = n1;
	}
	b = n2;

	unsigned long long tmp;
	while(b) {
		tmp = b;
		b = a % b;
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

}//__AUX_NUMBER

}//Kernel

#endif //GNUMP

