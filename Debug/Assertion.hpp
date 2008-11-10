/**
 * @file Assertion.hpp
 * Defines several functions that 
 * could be used to make assertions.
 */

#ifndef __Assertion__
#define __Assertion__

#if VDEBUG

#include <ostream>

namespace Debug {

// any function. It can be declared in one module and called in
// another
extern void debug(void*);

class Assertion
{
public:
  static void violated(const char* file,int line,const char* condition);
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
  /** file in which violatin occurred */
  const char* _file;
  /** line number in the file */
  int _line;
}; // AssertionViolationException

} // namespace Debug

#define ASS(Cond)                                               \
  if (! (Cond)) {                                               \
    Debug::Assertion::violated(__FILE__,__LINE__,#Cond);		\
    throw Debug::AssertionViolationException(__FILE__,__LINE__);	\
  }
#define ALWAYS(Cond) ASS(Cond)
#define NEVER(Cond) ASS(!(Cond))

#define ASSERTION_VIOLATION \
  Debug::Assertion::violated(__FILE__,__LINE__,"true");		\
  throw Debug::AssertionViolationException(__FILE__,__LINE__);
#else // ! VDEBUG

#define ASS(Cond)
#define ASSERT(Cond)
#define ALWAYS(Cond) Cond
#define NEVER(Cond) Cond
#define ASSERTION_VIOLATION

#endif // VDEBUG
#endif // __Assertion__

