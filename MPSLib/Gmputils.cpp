/**
 * @file gmputils.cpp
 * @brief Basic classes to for gmpRational arithmetic
 *
 * @author Domenico Salvagnin
 * @author Thorsten Koch
 */
#if GNUMP

#include "Gmputils.h"
#include <string.h>
#include <stdlib.h>
#include <assert.h>

char gmpRational::buffer[] = {'\0'};

gmpRational::gmpRational(int num, int den)
{
   mpq_init(number);
   mpq_set_si(number, num, den);
   mpq_canonicalize(number);
}

gmpRational::gmpRational(double val)
{
   mpq_init(number);
   mpq_set_d(number, val);
   mpq_canonicalize(number);
}

gmpRational::gmpRational(const gmpRational& rhs)
{
   mpq_init(number);
   mpq_set(number, rhs.number);
}

gmpRational::~gmpRational()
{
   mpq_clear(number);
}

gmpRational& gmpRational::operator=(const gmpRational& rhs)
{
   if (this != &rhs)
      mpq_set(number, rhs.number);
   return *this;
}

double gmpRational::toDouble() const
{
   return mpq_get_d(number);
}

bool gmpRational::operator==(const gmpRational& rhs) const
{
   return (mpq_equal(number, rhs.number) != 0);
}

bool gmpRational::operator!=(const gmpRational& rhs) const
{
   return (mpq_equal(number, rhs.number) == 0);
}

bool gmpRational::operator>(const gmpRational& rhs) const
{
   return (mpq_cmp(number, rhs.number) > 0);
}

bool gmpRational::operator<(const gmpRational& rhs) const
{
   return (mpq_cmp(number, rhs.number) < 0);
}

gmpRational& gmpRational::operator+=(const gmpRational& rhs)
{
   mpq_add(number, number, rhs.number);
   mpq_canonicalize(number);
   return *this;
}

gmpRational& gmpRational::operator-=(const gmpRational& rhs)
{
   mpq_sub(number, number, rhs.number);
   mpq_canonicalize(number);
   return *this;
}

void gmpRational::addProduct(const gmpRational& op1, const gmpRational& op2)
{
   mpq_t prod;
   mpq_init(prod);
   mpq_mul(prod, op1.number, op2.number);
   mpq_add(number, number, prod);
   mpq_canonicalize(number);
   mpq_clear(prod);
}

void gmpRational::abs()
{
   mpq_abs(number, number);
}

void gmpRational::integralityViolation(gmpRational& violation) const
{
   // if denominator is 1, then there is no integrality violation for sure
   if( mpz_cmp_ui(mpq_denref(number), 1) == 0 )
   {
      violation.toZero();
      return;
   }
   // otherwise, we must check w.r.t. the given tolerance
   // first calculate the fractional part 
   violation = (*this);
   violation.abs();
   mpz_t r;
   mpz_init(r);
   mpz_fdiv_r(r, mpq_numref(violation.number), mpq_denref(violation.number));
   mpq_set_num(violation.number, r);
   mpz_clear(r);
   // then integrality violation
   if( violation > gmpRational(1, 2) )
      sub(violation, gmpRational(1,1), violation);
}

void gmpRational::toZero()
{
   mpq_set_ui(number, 0, 1);
}

bool gmpRational::isInteger(const gmpRational& tolerance) const
{  
   // if denominator is 1, then it is an integer for sure
   if (mpz_cmp_ui(mpq_denref(number), 1) == 0) return true;
   // otherwise, we must check w.r.t. the given tolerance
   // first calculate the fractional part 
   gmpRational viol(*this);
   viol.abs();
   mpz_t r;
   mpz_init(r);
   mpz_fdiv_r(r, mpq_numref(viol.number), mpq_denref(viol.number));
   mpq_set_num(viol.number, r);
   mpz_clear(r);
   // then integrality violation
   if( viol > gmpRational(1, 2) )
      sub(viol, gmpRational(1,1), viol);
   return !(viol > tolerance);
}

bool gmpRational::isPositive() const
{
   return (mpq_sgn(number) > 0);
}

bool gmpRational::isNegative() const
{
   return (mpq_sgn(number) < 0);
}

bool gmpRational::isZero() const
{
   return (mpq_sgn(number) == 0);
}

void gmpRational::fromString(const char* num)
{
   char* tmp = &buffer[0];
   int   k = 0;
   int   exponent = 0;
   int   fraction = 0;
   
   assert(num != NULL);
   assert(strlen(num) <  32);

   // Skip initial whitespace
   while(isspace(*num))
      num++;

   // Skip initial +/-
   if (*num == '+')
      num++;
   else if (*num == '-')
      tmp[k++] = *num++;
   
   for(int i = 0; num[i] != '\0'; i++)
   {
      if (isdigit(num[i]))
      {
         tmp[k++]  = num[i];
         exponent -= fraction;
      }
      else if (num[i] == '.')
         fraction = 1;
      else if (tolower(num[i]) == 'e')
      {
         exponent += atoi(&num[i + 1]);
         break;
      }
   }
   while(exponent > 0)
   {
      tmp[k++] = '0';
      exponent--;
   }         
   tmp[k++] = '/';
   tmp[k++] = '1';

   while(exponent < 0)
   {
      tmp[k++] = '0';
      exponent++;
   }         
   tmp[k] = '\0';

   mpq_set_str(number, tmp, 10);
   mpq_canonicalize(number);
}

std::string gmpRational::toString() const
{
   // assure the buffer is big enough to store the result
   assert( mpz_sizeinbase(mpq_numref(number), 10 ) + mpz_sizeinbase(mpq_denref(number), 10) + 3 < 1024 );
   
   mpq_get_str(buffer, 10, number);
   return std::string(buffer);
}

void add(gmpRational& res, const gmpRational& op1, const gmpRational& op2)
{
   mpq_add(res.number, op1.number, op2.number);
   mpq_canonicalize(res.number);
}

void sub(gmpRational& res, const gmpRational& op1, const gmpRational& op2)
{
   mpq_sub(res.number, op1.number, op2.number);
   mpq_canonicalize(res.number);
}

void mult(gmpRational& res, const gmpRational& op1, const gmpRational& op2)
{
   mpq_mul(res.number, op1.number, op2.number);
   mpq_canonicalize(res.number);
}

void div(gmpRational& res, const gmpRational& op1, const gmpRational& op2)
{
   mpq_div(res.number, op1.number, op2.number);
   mpq_canonicalize(res.number);
}

void min(gmpRational& res, const gmpRational& op1, const gmpRational& op2)
{
   if( mpq_cmp(op1.number, op2.number) < 0 )
      res = op1;
   else
      res = op2;
}

void max(gmpRational& res, const gmpRational& op1, const gmpRational& op2)
{
   if( mpq_cmp(op1.number, op2.number) > 0 )
      res = op1;
   else
      res = op2;
}
#endif

