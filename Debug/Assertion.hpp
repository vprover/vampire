
/*
 * File Assertion.hpp.
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
/**
 * @file Assertion.hpp
 * Defines several functions that
 * could be used to make assertions.
 */

#ifndef __Assertion__
#define __Assertion__

/** A static assertion. @b e has to be a constant expression. */

#define ASS_AUX_CONCAT_(x,y) x ## y
#define ASS_AUX_CONCAT(x,y) ASS_AUX_CONCAT_(x,y)

//#define ASS_STATIC(e) extern char (* ASS_AUX_CONCAT(ct_assert, __LINE__) (void)) [sizeof(char[1 - 2*!(e)])]
#define ASS_STATIC(e) extern char (*ct_assert (void)) [sizeof(char[1 - 2*!(e)])]


#define __PUSH_DIAGNOSTICS(diag, ...) \
    _Pragma("GCC diagnostic push") \
    _Pragma(diag) \
    __VA_ARGS__ \
    _Pragma("GCC diagnostic pop") \

#define __IGNORE_WEXCEPTIONS(...) __PUSH_DIAGNOSTICS("GCC diagnostic ignored \"-Wexceptions\"", __VA_ARGS__)

//#undef CONCAT

#if VDEBUG

#include <iostream>
#include <ostream>

#include "Tracer.hpp"

namespace Shell {
  bool outputAllowed(bool debug);
  void reportSpiderFail();
}

namespace Debug {

// any function. It can be declared in one module and called in
// another
extern void debug(void*);

class Assertion
{
public:
  static void violated(const char* file,int line,const char* condition);

  template<typename T>
  static void violated(const char* file,int line,const char* condition,
	  const T& rep, const char* repStr);

  template<typename T, typename U>
  static void violated(const char* file,int line,const char* condition,
	  const T& rep, const char* repStr,const U& rep2, const char* repStr2);


  static void checkType(const char* file,int line,const void* ptr,
	  const char* assumed, const char* ptrStr);

  template<typename T,typename U>
  static void violatedEquality(const char* file,int line,const char* val1Str,
	  const char* val2Str, const T& val1, const U& val2);
  template<typename T,typename U>
  static void violatedNonequality(const char* file,int line,const char* val1Str,
	  const char* val2Str, const T& val1, const U& val2);

  template<typename T,typename U>
  static void violatedComparison(const char* file,int line,const char* val1Str,
	  const char* val2Str, const T& val1, const U& val2, bool strict, bool greater);

  template<typename T>
  static void violatedMethod(const char* file,int line,const T& obj,
	  const char* objStr, const char* methodStr, const char* prefix);


  static void violatedStrEquality(const char* file,int line,const char* val1Str,
  	  const char* val2Str, const char* val1, const char* val2);


  static void reportAssertValidException(const char* file,int line,const char* obj);
private:
  static bool _violated;
};

/**
 * Class AssertionViolationException. It is thrown when any assertion
 * is violated.
 */
class AssertionViolationException
{
public:
  AssertionViolationException (const char* file, int line);
  ~AssertionViolationException () {}
  void cry (std::ostream&);
private:
  void outputFileAndLine (std::ostream&) const;
  /** file in which violation occurred */
  const char* _file;
  /** line number in the file */
  int _line;
}; // AssertionViolationException

} // namespace Debug

#define DEBUG_CODE(X)  X

#define ASS(Cond)                                               \
  if (! (Cond)) {                                               \
    Debug::Assertion::violated(__FILE__,__LINE__,#Cond);		\
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);)	\
  }

#define ASS_REP(Cond, ReportedVal)                                      \
  if (! (Cond)) {                                               \
    Debug::Assertion::violated(__FILE__,__LINE__,#Cond,ReportedVal,#ReportedVal); \
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);)	\
  }

#define ASS_REP2(Cond, ReportedVal, ReportedVal2)               \
  if (! (Cond)) {                                               \
    Debug::Assertion::violated(__FILE__,__LINE__,#Cond,ReportedVal,#ReportedVal,ReportedVal2,#ReportedVal2); \
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);)	\
  }


#define ALWAYS(Cond) ASS(Cond)
#define NEVER(Cond) ASS(!(Cond))


#define ASS_EQ(VAL1,VAL2)                                               \
  if (! ((VAL1)==(VAL2)) ) {                                               \
    Debug::Assertion::violatedEquality(__FILE__,__LINE__,#VAL1,#VAL2,VAL1,VAL2); \
    __IGNORE_WEXCEPTIONS( throw Debug::AssertionViolationException(__FILE__,__LINE__);)  \
  } \

#define ASS_NEQ(VAL1,VAL2)                                               \
  if (! ((VAL1)!=(VAL2)) ) {                                               \
    Debug::Assertion::violatedNonequality(__FILE__,__LINE__,#VAL1,#VAL2,VAL1,VAL2); \
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);)	\
  } \

#define ASS_STR_EQ(VAL1,VAL2)                                               \
  if (strcmp((VAL1),(VAL2)) ) {                                               \
    Debug::Assertion::violatedStrEquality(__FILE__,__LINE__,#VAL1,#VAL2,VAL1,VAL2); \
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);	)\
  } \


#define ASS_G(VAL1,VAL2)                                               \
  if (! ((VAL1)>(VAL2)) ) {                                               \
    Debug::Assertion::violatedComparison(__FILE__,__LINE__,#VAL1,#VAL2,VAL1,VAL2,true,true); \
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);)	\
  } \

#define ASS_L(VAL1,VAL2)                                               \
  if (! ((VAL1)<(VAL2)) ) {                                               \
    Debug::Assertion::violatedComparison(__FILE__,__LINE__,#VAL1,#VAL2,VAL1,VAL2,true,false); \
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);)	\
  } \

#define ASS_GE(VAL1,VAL2)                                               \
  if (! ((VAL1)>=(VAL2)) ) {                                               \
    Debug::Assertion::violatedComparison(__FILE__,__LINE__,#VAL1,#VAL2,VAL1,VAL2,false,true); \
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);)	\
  } \

#define ASS_LE(VAL1,VAL2)                                               \
  if (! ((VAL1)<=(VAL2)) ) {                                               \
    Debug::Assertion::violatedComparison(__FILE__,__LINE__,#VAL1,#VAL2,VAL1,VAL2,false,false); \
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);)	\
  } \

#define ASS_ALLOC_TYPE(PTR,TYPE)						\
  Debug::Assertion::checkType(__FILE__,__LINE__,(PTR),(TYPE), #PTR)

#define ASS_METHOD(OBJ,METHOD)							\
  if (! ((OBJ).METHOD) ) {							\
    Debug::Assertion::violatedMethod(__FILE__,__LINE__,(OBJ), #OBJ, #METHOD,"");\
    __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);)	\
  }

#define ASSERT_VALID(obj) try { (obj).assertValid(); } catch(...) \
  { Debug::Assertion::reportAssertValidException(__FILE__,__LINE__,#obj); \
    __IGNORE_WEXCEPTIONS(throw;) }

#define ASSERTION_VIOLATION \
  Debug::Assertion::violated(__FILE__,__LINE__,"true");		\
  __IGNORE_WEXCEPTIONS(throw Debug::AssertionViolationException(__FILE__,__LINE__);) \

#define ASSERTION_VIOLATION_REP(Val) \
  ASS_REP(false, Val)
#define ASSERTION_VIOLATION_REP2(Val1,Val2) \
  ASS_REP2(false, Val1, Val2)

#else // ! VDEBUG

#define DEBUG_CODE(X)

#define __IGNORE_WUNUSED(...) __PUSH_DIAGNOSTICS("GCC diagnostic ignored \"-Wreturn-type\"", __VA_ARGS__)

#define ASS(Cond) 
#define ALWAYS(Cond) (void) ( Cond );
#define NEVER(Cond) (void) ( Cond );

#define ASS_REP(Cond, ReportedVal)
#define ASS_REP2(Cond, ReportedVal, ReportedVal2)

#define ASS_EQ(VAL1,VAL2)
#define ASS_NEQ(VAL1,VAL2)
#define ASS_STR_EQ(VAL1,VAL2)

#define ASS_G(VAL1,VAL2)
#define ASS_L(VAL1,VAL2)
#define ASS_GE(VAL1,VAL2)
#define ASS_LE(VAL1,VAL2)

#define ASS_ALLOC_TYPE(PTR,TYPE)
#define ASS_METHOD(OBJ,METHOD)

#define ASSERTION_VIOLATION 
#define ASSERTION_VIOLATION_REP(Val) ASSERTION_VIOLATION
#define ASSERTION_VIOLATION_REP2(Val1,Val2)  ASSERTION_VIOLATION

#define ASSERT_VALID(obj)

#endif // VDEBUG

#if VDEBUG

template<typename T>
void Debug::Assertion::violated (const char* file,int line,const char* cond,
	const T& rep, const char* repStr)
{
  if (_violated) {
    return;
  }

  _violated = true;
  Shell::reportSpiderFail();
  if (Shell::outputAllowed(true)) {
    cout << "Condition in file " << file << ", line " << line
	 << " violated:\n" << cond << "\n"
	 << "Value of " << repStr << " is: " << rep
	 << "\n----- stack dump -----\n";
    Tracer::printStack(cout);
    cout << "----- end of stack dump -----\n";
  }
} // Assertion::violated

template<typename T,typename U>
void Debug::Assertion::violated (const char* file,int line,const char* cond,
	const T& rep, const char* repStr, const U& rep2, const char* repStr2)
{
  if (_violated) {
    return;
  }

  _violated = true;
  Shell::reportSpiderFail();
  if (Shell::outputAllowed(true)) {
    cout << "Condition in file " << file << ", line " << line
	<< " violated:\n" << cond << "\n"
	<< "Value of " << repStr << " is: " << rep << "\n"
	<< "Value of " << repStr2 << " is: " << rep2
	<< "\n----- stack dump -----\n";
    Tracer::printStack(cout);
    cout << "----- end of stack dump -----\n";
  }
} // Assertion::violated

template<typename T,typename U>
void Debug::Assertion::violatedEquality(const char* file,int line,const char* val1Str,
	  const char* val2Str, const T& val1, const U& val2)
{
  if (_violated) {
    return;
  }

  _violated = true;
  Shell::reportSpiderFail();
  if (Shell::outputAllowed(true)) {
    std::cout << "Condition " << val1Str << " == " << val2Str << " in file " << file << ", line " << line
	      << " was violated, as:\n" << val1Str << " == " << val1 << "\n"
	      << val2Str << " == " << val2 << "\n"
	      << "----- stack dump -----\n";
    Tracer::printStack(cout);
    std::cout << "----- end of stack dump -----\n";
  }
} // Assertion::violatedEquality


template<typename T,typename U>
void Debug::Assertion::violatedNonequality(const char* file,int line,const char* val1Str,
	  const char* val2Str, const T& val1, const U& val2)
{
  if (_violated) {
    return;
  }

  _violated = true;
  Shell::reportSpiderFail();
  if (Shell::outputAllowed(true)) {
    std::cout << "Condition " << val1Str << " != " << val2Str << " in file " << file << ", line " << line
	      << " was violated, as:\n" << val1Str << " == " << val1 <<"\n" << val2Str << " == " << val2 << "\n"
	      << "----- stack dump -----\n";
    Tracer::printStack(cout);
    std::cout << "----- end of stack dump -----\n";
  }
} // Assertion::violatedNonequality


template<typename T,typename U>
void Debug::Assertion::violatedComparison(const char* file,int line,const char* val1Str,
	  const char* val2Str, const T& val1, const U& val2, bool strict, bool greater)
{
  if (_violated) {
    return;
  }

  _violated = true;
  Shell::reportSpiderFail();
  if (Shell::outputAllowed(true)) {
    std::cout << "Condition " << val1Str;
    if (strict) {
      if (greater) {
	std::cout << " > ";
      }
      else {
	std::cout << " < ";
      }
    }
    else if (greater) {
      std::cout << " >= ";
    }
    else {
      std::cout << " <= ";
    }

    std::cout << val2Str << " in file " << file << ", line " << line
	      << " was violated, as:\n" << val1Str<<" == " << val1 << "\n"
	      << val2Str <<" == " << val2 << "\n"
	      << "----- stack dump -----\n";
    Tracer::printStack(cout);
    std::cout << "----- end of stack dump -----\n";
  }
} // Assertion::violatedComparison

template<typename T>
void Debug::Assertion::violatedMethod(const char* file,int line,const T& obj,
	  const char* objStr, const char* methodStr, const char* prefix)
{
  if (_violated) {
    return;
  }

  _violated = true;
  Shell::reportSpiderFail();
  if (Shell::outputAllowed(true)) {
    std::cout << "Condition " << prefix << "(" << objStr << ")." << methodStr << " in file "
	      << file << ", line " << line << " was violated for:\n"
	      << objStr << " == " << obj << "\n"
	      << "----- stack dump -----\n";
    Tracer::printStack(cout);
    std::cout << "----- end of stack dump -----\n";
  }
} // Assertion::violatedMethod

#endif

#endif // __Assertion__

