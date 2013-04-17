/**
 * @file Gmputils.h
 * @brief Basic classes to for gmpRational arithmetic
 *
 * @author Domenico Salvagnin
 */
#if GNUMP

#ifndef __GMPUTILS__
#define __GMPUTILS__

#include <gmp.h>
#include <string>

/**
 * @brief Simple wrapper class around GMP mpq_t.
 * Not a full-blown wrapper such as the ones in GMP++, but should be enough for the job.
 * Btw, official C++ wrappers are not built by default and we want an easy installation
 * process (and as few dependencies as possible).
 */
 
class gmpRational
{
public:
   /** @name constructors & destructor */
   // \{

   /**
    * Construct a gmpRational corresponding to num/den.
    * Acts also as default constructor (for the value zero).
    * @param num signed integer as numerator
    * @param den signed integer as denominator
    */
   gmpRational(int num = 0, int den = 1);

   /**
    * Construct a gmpRational from a double.
    * Note that the conversion is exact, so it may not be what you want...
    * @param val floating value to construct from
    */
   gmpRational(double val);

   /** Copy Constructor */
   gmpRational(const gmpRational& rhs);
   
   /** Destructor */
   ~gmpRational();
   // \}
   
   gmpRational& operator=(const gmpRational& rhs);
   
   /**
    * Convert to a double, truncating if necessary
    * @return the gmpRational number as a float
    */
   double toDouble() const;
   
   /** @name comparison operators */
   // \{
   
   /** equal operator */ 
   bool operator==(const gmpRational& rhs) const;
   
   /** not-equal operator */ 
   bool operator!=(const gmpRational& rhs) const;
   
   /** greater-than operator */ 
   bool operator>(const gmpRational& rhs) const;
   
   /** less-than operator */
   bool operator<(const gmpRational& rhs) const;
   // \}
   
   /** @name arithmetic operators */
   // \{
      
   /** compound plus operator: self = self + op */
   gmpRational& operator+=(const gmpRational& op);
   
   /** compound minus operator: self = self - op */
   gmpRational& operator-=(const gmpRational& op);
   
   /**
    * Add to the current value the product op1 * op2.
    * This is the equivalent of the operation self += op1*op2
    * for standard numeric types. It is provided here because it is
    * useful for computing dot products.
    * @param op1 first operand of the product
    * @param op2 second operand of the product
    */
   void addProduct(const gmpRational& op1, const gmpRational& op2);
   
   /**
    * Replaces the current value with its absolute value (inline operator)
    */
   void abs();
   
   /**
    * Calculate the integrality violation of a given number
    */
   void integralityViolation(gmpRational& violation) const;
   
   /**
    * Zero out number (i.e. set it to zero)
    */
    void toZero();
   
   // \}
   
   /** @name arithmetic global functions */
   // \{
   
   /** Addition: res = op1 + op2 */
   friend void add(gmpRational& res, const gmpRational& op1, const gmpRational& op2);
   
   /** Subtraction: res = op1 - op2 */
   friend void sub(gmpRational& res, const gmpRational& op1, const gmpRational& op2);
   
   /** Multiplication: res = op1 * op2 */
   friend void mult(gmpRational& res, const gmpRational& op1, const gmpRational& op2);

   /** Division: res = op1 / op2 */
   friend void div(gmpRational& res, const gmpRational& op1, const gmpRational& op2);
   
   /** Min: res = min(op1, op2) */
   friend void min(gmpRational& res, const gmpRational& op1, const gmpRational& op2);
   
   /** Max: res = max(op1, op2) */
   friend void max(gmpRational& res, const gmpRational& op1, const gmpRational& op2);
   // \}
   
   /** @name test operators */
   // \{
   
   /** Test if a number is integer (up to a given tolerance)  */
   bool isInteger(const gmpRational& tolerance) const;
   
   /** Test if a number is positive (exact, no tolerances) */
   bool isPositive() const;
   
   /** Test if a number is negative (exact, no tolerances) */
   bool isNegative() const;
   
   /** Test if a number is zero (exact, no tolerances) */
   bool isZero() const;
   // \}
   
   /** @name I/O functions */
   // \{
      
   /**
    * Read a gmpRational number from a string representation.
    * This functions essentially parses a number of the form
    * [+|-]?[0-9]*.[0-9]+[[e|E][+|-][0-9]+]?
    * and generates the corresponding fraction.
    */
   void fromString(const char* str);
   
   /**
    * Convert a gmpRational number to a string representation.
    * Note that the format is [+|-]?[0-9]+/[0-9]+.
    * Useful for printing.
    */
   std::string toString() const;
   // \}
protected:
   mpq_t number; //< gmpRational value
private:
   /**
    * static buffer for I/O operations
    * if a number does not fit in here, it does not fit in a double either
    */
   static char buffer[1024];
};

#endif /* GMPUTILS_H */
#endif //GNUMP

