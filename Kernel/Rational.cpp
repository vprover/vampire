
/*
 * File Rational.cpp.
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
Rational::Rational(long long num, long long den):_num(num),_den(den){

	if(den == 0) {
		_num = 0;
		_den = 1;
		return;
	}
	ASS(den!=0);
	if( num >= LLONG_MAX || num <=LLONG_MIN || den <= LLONG_MIN || den >= LLONG_MAX ){
		throw NumberImprecisionException();
	}
	if (den < 0 && num >0 ){
		_num = -_num;
		_den = -_den;
	}
	else if (den < 0 && num < 0) {
		_num = -_num;
		_den = -_den;
	}
	else if ( num == 0 ) {
		_num = 0;
		_den = 1;
	}
	else {
		long long gcd = GCD(_num, _den);
		_num = safeDiv(_num, gcd);
		_den = safeDiv(_den, gcd);
	}

}
/**
 * Constructor that initializes the rational number from an integer
 * @b value
 */
Rational::Rational(int value){
	CALL("Rational::Rational(int value)");
	_num = value;
	_den = 1;
}

/**
 * Constructor that initializes the rational number from a double value
 * @b value
 */
Rational::Rational(double value){
	CALL("Rational::Rational(double value)");
	//this is not the best way to do the conversion, but at least is safe!
	//The implementation should be done by us.
	_num = value;
	_den = 1;
	/*
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
	*/
}

Rational::Rational(long double value){
	CALL("Rational::Rational(long double value)");
	//this is not the best way to do the conversion, but at least is safe!
	//The implementation should be done by us.
	double temp = static_cast<double>(value);
	//check if the static_cast does produce an error, meaning NaN
	if(temp != temp ){
		_num = 1987;
		_den = 1102;
		return;
		//throw NumberImprecisionException();
	}

	mpq_class number(temp);
	//number.canonicalize();
	if (number.get_den().fits_slong_p() && number.get_num().fits_slong_p()){
		_num = number.get_num().get_si();
		_den = number.get_den().get_si();
	}
	else {
		_num = 1102;
		_den = 1987;
		//this is the case when we cannot convert the double into a rational number
		//throw NumberImprecisionException();
	}
}

/**
 * Constructor that initializes the rational number from a vstring
 * @b value
 */
Rational::Rational(vstring value){
	CALL("Rational::Rational(vstring value)");
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
	//a/b * c/d = canonical(a/d) *canonical(c/b)
	//first create the canonical version of a/d , then c/b
	Rational r1(_num,o._den);
	Rational r2(o._num, _den);
 	Rational result(safeMul(r1._num,r2._num), safeMul(r1._den,r2._den));
	return result;
}


Rational Rational::operator/(const Rational& o) const{
	CALL("Rational::operator/");
	//must take care of the sign first
	long long num1, num2;
	num1 = _num;
	num2 = o._num;

	if (_num<0 && o._num<0)
	{
		num1 = -num1;
		num2 = -num2;

	}
	else
		if(o._num<0 ){
		num1 = -num1;
		num2 = -num2;
		}

/*
	if ( (o._num < 0 && _num < 0) || o._num < 0 )
	{
		num1 = -_num;
		num2 = -o._num;
	}
	else {
		num1 = _num;
		num2 = o._num;
	}
	*/
	ASS(_den != 0);
	ASS(num2 != 0);
	Rational r1 = Rational(num1, _den);
	Rational r2 = Rational(o._den, num2);
	Rational result = r1*r2;
	return result;
}

Rational Rational::operator+(const Rational& o) const{
	CALL("Rational::operator+");
	if (_num == 0){
		Rational result(o);
		return result;
	}else
		if(o._num==0 ){
			Rational result(_num, _den);
			return result;
		}
		else if(o._num == 0 && _num == 0){
			Rational result(0,1);
			return result;
		}
	if ( _den == o._den){
		Rational result(safeAdd(_num,o._num), o._den);
		return result;
	}

	long long num, den;
	long long gcd = GCD(_den, o._den);
	long long mul1, mul2;
	mul1= safeDiv(_den,gcd);
	mul2 = safeDiv(o._den,gcd);
	den= safeMul(mul1,mul2);
	num = safeAdd( safeMul(_num,mul2) , safeMul(o._num,mul1));
	Rational result(num,den);
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
	if (_den == o._den){
		return Rational(safeSub(_num,o._num), o._den).canonical();
	}

	long long gcd = GCD(_den, o._den);
	long long mul1, mul2;
	mul1= safeDiv(_den,gcd);
	mul2 = safeDiv(o._den,gcd);
	long long num, den;
	den= safeMul(mul1,mul2);
	num = safeSub( safeMul(_num,mul2) , safeMul(o._num,mul1));
	Rational result(num,den);
	return Rational(num, den);
}

Rational& Rational::operator+=(const Rational& o){
	CALL("Rational::operator+=");
	Rational result;
	if(sameDenominator(*this, o)){
		result = Rational(safeAdd(_num,o._num),o._den);
		*this = result;
		return *this;
	}
	else {
		result = (*this)+o;
		*this = result;
		return (*this);
	}
}

Rational& Rational::operator-=(const Rational& o){
	CALL("Rational::operator-=");
	Rational result;
	if(sameDenominator(*this, o)){
			result = Rational(safeSub(_num,o._num),o._den);
			*this = result;
			return *this;
		}
		else {
			result = (*this)-o;
			*this = result;
			return (*this);
		}
}

Rational& Rational::operator*=(const Rational& o){
	CALL("Rational::operator*=");
	if(o._num == 0){
		Rational result(0,1);
		return result;
	}
	Rational result=(*this)*o;
	*this = result;
	return (*this);
}

Rational& Rational::operator/=(const Rational& o){
	CALL( "Rational::operator/=");
	Rational v(*this);
	*this = Rational(v* o.inverse());
	return static_cast<Rational&>(*this);
}

Rational& Rational::operator++(){
	CALL("Rational::operator++");
	++(this->_num);
	return *this;
}
Rational& Rational::operator--(){
	CALL("Rational::operator--");
	--(this->_num);
	return *this;
}

Rational Rational::operator++(int){
	CALL("Rational::operator++ postfix");
	Rational temp = *this;
	this->_num+=1;
	return *this;
}

Rational Rational::operator--(int){
	CALL("Rational::operator-- postfix");
	Rational temp = *this;
	this->_num-=1;
	return *this;
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

vstring Rational::toString() const{
	char tmp_num[256];
	sprintf(tmp_num, "%lld",_num);
	vstring num(tmp_num);
	char tmp_den[256];
	sprintf(tmp_den,"%lld",_den);
	vstring den(tmp_den);
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

double safeConversionToDouble(double number){
	return static_cast<double>(number);
}

double safeConversionToDouble(long long number){
	if(number < DBL_MIN || number > DBL_MAX){
		throw Rational::NumberImprecisionException();
	}
	return static_cast<double>(number);
}
float safeConversionToFloat(long long number){
	if(number < FLT_MIN || number > FLT_MAX){
		throw Rational::NumberImprecisionException();
	}
	return float(number);
}

}//__AUX_NUMBER
}//Kernel

#endif //GNUMP

