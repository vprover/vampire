/*
 * Rational.hpp
 *
 *  Created on: Apr 15, 2013
 *      Author: ioan
 */

#ifndef RATIONAL_HPP_
#define RATIONAL_HPP_

#if GNUMP

#include "Forwards.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"

#include <cmath>

namespace Kernel{

namespace __Aux_Number{

/**
 * Class designed in order to represent rational numbers. This should be used as
 * an alternative to the NativeNumber (long double) representation of numbers for
 * bound propagation.
 *
 * Some conventions about this class:
 * 	- the number is negative => only the numerator (_num) is negative
 * 	- the denominator is always different than 0
 * 	- canonical takes care of the placing the sign at the numerator
 */
class Rational{
public:
	Rational(){_num=1, _den=1;}
	Rational(long long value){_num = static_cast<double>(value); _den=1;}
	Rational(double val){_den=1; _num=val;}
	Rational(double num, double den): _num(num), _den(den){
		ASS(den!=0);
		if (den < 0 && num >0 ){
			_num = -_num;
		}
		if (den < 0 && num < 0) {
			_num = -_num;
			_den = -_den;
		}
		if ( num == 0 ) {
			_num = 0;
			_den = 1;
		}

	}

	~Rational(){}
	Rational& operator=(const Rational& o){
		(*this)._den = o._den;
		(*this)._num = o._num;
		return *this;
	}

	//assign in place
	Rational& assign(double num, double den){
		this->_den=den;
		this->_num=num;
		return *this;
	}

	Rational operator+(const Rational& o);
	//unary minus
	Rational& operator-();
	Rational operator-(const Rational& o);

	Rational operator*(const Rational& o);
	Rational operator/(const Rational& o);

	Rational& operator+=(const Rational& o);
	Rational& operator-=(const Rational& o);
	Rational& operator*=(const Rational& o);
	Rational& operator/=(const Rational& o);

	Rational& operator++();
	Rational& operator--();

	//comparators
	bool operator==(const Rational& o) const {
		CALL("Rational::operator==");
		//assumes that the rational numbers are canonicalized
		return ((*this)._num == o._num && (*this)._den == o._den);

	}

	//comparison with the same type of values
	//one could also add comparison with integers/long longs
	bool operator>(const Rational& o) const;
	bool operator<(const Rational& o) const;
	bool operator>=(const Rational& o) const;
	bool operator<=(const Rational& o) const;

	Rational canonical(const Rational& o);
	double toDouble() const{
		return static_cast<double>((*this)._num/(*this)._den);
	}
	//useful numbers
	static const Rational& zero(){static Rational res(0,1); return res;}
	static const Rational& one(){static Rational res(1,1); return res;}
	static const Rational& minusOne(){static Rational res(-1,1); return res;}
	static const Rational& two(){static Rational res(2,1);return res;}

	bool isPositive() const{ return *this >= zero();}
	bool isPositiveNonZero() const{return *this > zero();}

	bool isNegative() const{ return *this <= zero();}
	bool isNegativeNonZero() const{ return *this < zero();}

	bool isZero() const{ return *this == zero(); }

	Rational abs() const{
		if ((*this).isNegative()){
			return Rational( -(*this)._num, (*this)._den);
		}
		return (*this);
	}

	double Numerator() {return _num;}
	double Denomination() {return _den;}

	//cast operators
	operator double() const {return double(_num / _den);}
	operator float() const {return float(_num / _den);}

protected:
	bool sameDenominator(const Rational& a , const Rational& b) const{
		CALL("Rational::sameDenominator");
		return (a._den == b._den);
	}

	Rational inverse() const{
		CALL("Rational::inverse");
		if ((*this).isZero()){
			return zero();
		}
		Rational result((*this)._den, (*this)._num);
		return result;
	}
private:
	//numerator and denominator
	double _num, _den;
};

} //__Aux_Number
} //Kernel
#endif //GNUMP
#endif /* RATIONAL_HPP_ */
