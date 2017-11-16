
/*
 * File Rational.hpp.
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

unsigned long long GCD(long long n1, long long n2);

//overflow check functions
bool additionOverflow(long long n1, long long n2);
bool subtractionOverflow(long long n1, long long n2);
bool multiplicationOverflow(long long n1, long long n2);
bool divisionOverflow(long long numerator, long long denominator);
bool moduloOverflow(long long numerator, long long denominator);

double safeConversionToDouble(long long number);
double safeConversionToDouble(double number);
float safeConversionToFloat(long long number);
//addition with overflow check
long long safeAdd(long long n1, long long n2);
//subtraction with overflow check
long long safeSub(long long n1, long long n2);
//multiplication with overflow check
long long safeMul(long long n1, long long n2);
//division with overflow check
long long safeDiv(long long n1, long long n2);
//modulo operator with overflow check
long long safeModulo(long long n1, long long n2);

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
	class NumberImprecisionException {
		public:
		NumberImprecisionException() {}
	};
	//default constructor creates the number 1/1
	Rational(): _num(1), _den(1){}
	//construct a number which has denominator 1
	Rational(long long value):_num(value),_den(1){}
	//explicit creation
	Rational(long long num, long long den);
	//create a rational number from a vstring
	Rational(vstring value);
	//create a rational number from a double value
	Rational(double value);
	Rational(long double value);
	Rational(int value);

	~Rational(){}
	Rational& operator=(const Rational& o){
		(*this)._den = o._den;
		(*this)._num = o._num;
		return static_cast<Rational&>(*this);
	}
	Rational& operator=(const long double val){
		Rational r(val);
		(*this)._den = r._den;
		(*this)._num = r._num;
		return static_cast<Rational&>(*this);
	}
	//assign in place
	Rational& assign(double num, double den){
		_den=den;
		_num=num;
		return static_cast<Rational&>(*this);
	}

	Rational operator+(const Rational& o) const;
	//unary minus
	Rational operator-() const;
	Rational operator-(const Rational& o) const;

	Rational operator*(const Rational& o) const;
	Rational operator/(const Rational& o) const;

	Rational& operator+=(const Rational& o);
	Rational& operator-=(const Rational& o);
	Rational& operator*=(const Rational& o);
	Rational& operator/=(const Rational& o);

	//prefix operators
	Rational& operator++();
	Rational& operator--();
	//postfix operators
	Rational operator++(int);
	Rational operator--(int);


	//comparators
	bool operator==(const Rational& o) const {
		//assumes that the rational numbers are canonicalized
		return ((*this)._num == o._num && (*this)._den == o._den);

	}

	//comparison with the same type of values
	//one could also add comparison with integers/long longs
	bool operator>(const Rational& o) const;
	bool operator<(const Rational& o) const;
	bool operator>=(const Rational& o) const;
	bool operator<=(const Rational& o) const;


	double toDouble() const{
		double res = (double)_num/_den;
		return res;
	}

	vstring toString() const;

	bool isPositive() const{ return this->_num >= 0;}
	bool isPositiveNonZero() const{return this->_num > 0;}

	bool isNegative() const{ return this->_num <= 0;}
	bool isNegativeNonZero() const{ return this->_num < 0;}

	bool isZero() const{ return this->_num == 0; }

	Rational abs() const{
		if ((*this).isNegative()){
			return Rational( -(*this)._num, (*this)._den);
		}
		return static_cast<Rational>(*this);
	}
	Rational abs(Rational val){
		if(val.isNegative()){
			return -val;
		}
		else{
			return val;
		}


	}
	long long Numerator() const {return _num;}
	long long Denomination() const {return _den;}

	//cast operators this operators are not protected from overflow!
	//it might be a problem
	operator double() const {return safeConversionToDouble(_num) / safeConversionToDouble(_den);}
	operator float() const {return safeConversionToFloat(_num) / safeConversionToFloat(_den);}
	operator long double() const {return safeConversionToDouble(_num) / safeConversionToDouble(_den);}

	friend ostream& operator<< (ostream &out, Rational &val){
		out << val.toString();
		return out;
	}

protected:
	bool sameDenominator(const Rational& a , const Rational& b) const{
		return (a._den == b._den);
	}

	Rational inverse() const{
		if (isZero()){
			return Rational(0,1);
		}
		Rational result(_den, _num);
		return result;
	}

	Rational canonical();

private:
	//numerator
	long long _num;
	//keeping the denominator as unsigned long long might get us in trouble for overflow
	//detection. This is due to the size for this representation. So it is better to just
	//store it as a long long and not have any problems
	//denominator
	long long _den;
};

} //__Aux_Number
} //Kernel
#endif //GNUMP
#endif /* RATIONAL_HPP_ */
