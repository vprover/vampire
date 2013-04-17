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

using namespace Kernel;
using namespace __Aux_Number;

Rational Rational::operator*(const Rational& o){
	CALL("Rational operator*");
	Rational result((*this)._num*o._num, (*this)._den*o._den);
	result = canonical(result);
	return result;
}

Rational Rational::operator/(const Rational& o){
	CALL("Rational::operator/");
	return canonical(Rational((*this)._num*o._den, (*this)._den*o._num));
}

Rational Rational::operator+(const Rational& o){
	CALL("Rational::operator+");
	//if
	if ( (*this)._den == o._den){
		return canonical(Rational((*this)._num+o._num, o._den));
	}

	Rational result((*this)._num, (*this)._den);
	result._den= result._den*o._den;
	result._num = result._num*o._den + o._num*result._den;
	result = canonical(result);
	return result;
}

Rational& Rational::operator-(){
	CALL("Rational::operator-(unary)");
	(*this)._num=-(*this)._num;
	return (*this);
}

Rational Rational::operator-(const Rational& o){
	CALL("Rational::operator-(Rational )");
	double den, num;
	if ((*this)._den == o._den){
		return canonical(Rational(((*this)._num-o._num), o._den));
	}

	den = ((*this)._den)*o._num - ((*this)._num)*o._den;
	num = ((*this)._den*o._den);
	return canonical(Rational(num, den));
}

Rational& Rational::operator+=(const Rational& o){
	CALL("Rational::operator+=");
	if(sameDenominator(*this, o)){
		*this = canonical(Rational((*this)._num+o._num,o._den));
		return *this;
	}
	return *this;
}

Rational& Rational::operator-=(const Rational& o){
	CALL("Rational::operator-=");
	if(sameDenominator(*this, o)){
			*this = canonical(Rational((*this)._num-o._num,o._den));
			return *this;
		}
	return *this;
}

Rational& Rational::operator*=(const Rational& o){
	CALL("Rational::operator*=");
	*this = canonical((*this)*o);
	return *this;
}

Rational& Rational::operator/=(const Rational& o){
	CALL( "Rational::operator/=");
	Rational v(*this);
	*this = canonical(v* o.inverse());
	return *this;
}

Rational& Rational::operator++(){
	CALL("Rational::operator++");
	*this = canonical((*this)+Rational::one());
	return *this;
}

Rational& Rational::operator--(){
	CALL("Rational::operator--");
	*this = canonical((*this)-Rational::one());
	return *this;
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
Rational Rational::canonical(const Rational& o){
	CALL("Rational::canonical");
	Rational result;
	bool isNegative = o.isNegative();
	result = o.abs();
	long long a, b;
	a = static_cast<long long>(result._num);
	b = static_cast<long long>(result._den);

	long long tmp;
	  while (b) {
	    tmp = b;
	    b = a % b;
	    a = tmp;
	  }

	result = Rational(result._num / a, result._den/b);
	//the special case when they are both negative => make the number positive
	if (o._den < 0 && o._num < 0) return result;
	if (o._den < 0 && o._num > 0) {
		result._num = - result._num;
		result._den = - result._den;
		return result;
	}
	return isNegative ? -result : result;

}

#endif //GNUMP

