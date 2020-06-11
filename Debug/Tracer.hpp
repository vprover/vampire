
/*
 * File Tracer.hpp.
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
 * @file Tracer.hpp
 * Implements call tracing.
 * @since 01/05/2002 Manchester
 * @since 24/10/2002 Manchester, changed after talking with Shura
 * @since 08/12/2005 Redmond, moved to the Debug namespace with the purpose
 *                   of making global to Vampire
 */


#ifndef __Tracer__
#  define __Tracer__

#if VDEBUG

#include <iostream>

using namespace std;

namespace Debug {

/**
 * What kind of control point it is.
 */
enum ControlPointKind {
  /** Entry to a function */
  CP_ENTRY,
  /** Exit from a function */
  CP_EXIT,
  /** Point inside a function */
  CP_MID
}; // enum ControlPointKind

class Tracer {
 public:
  explicit Tracer (const char* fun);
  virtual ~Tracer ();
  static void printStack (ostream&);
  static void printOnlyStack (ostream&);
  static void controlPoint (const char* name);
  static unsigned passedControlPoints () { return _passedControlPoints; }
  /** start outputting the trace independently of the first and last
   *  control point setting */
  static void forceOutput() { _forced = true; }
  /** stop outputting forced by startOutput */
  static void stopOutput() { _forced = false; }
  static bool canWatch;
 private:
  const char* _fun;
  Tracer* _previous;

  static void printStackRec (Tracer* current, ostream&, int& depth);
  static void spaces(ostream& str,int number);

  /** current trace point */
  static Tracer* _current;
  /** current depth */
  static unsigned _depth;
  /** description of the last control point (function name) */
  static const char* _lastControlPoint;
  /** total number of passed control points */
  static unsigned _passedControlPoints;
  /** kind of the last point */
  static ControlPointKind _lastPointKind;
  /** forced by startTrace */
  static bool _forced;
  static void controlPoint (const char*, ControlPointKind);
  static void outputLastControlPoint (ostream& str);
public:
  /* prints a message with indent in the of the same size as the current _depth */
  template<class... A>
  static void printDbg(A... msg);
};

template<class... As>
struct _printDbg {
  void operator()(const As&... msg);
};

template<> struct _printDbg<>{
  void operator()() { }
};

template<class A, class... As> struct _printDbg<A, As...>{
  void operator()(const A& a, const As&... as) {
    cout << a;
    _printDbg<As...>{}(as...);
  }
};

template<class... A> void Tracer::printDbg(A... msg)
{
  for (int i = 0; i< _depth; i++) {
    cout << "  ";
  }
  // cout << _lastControlPoint << ": ";
  cout << _current->_fun << ": ";

  _printDbg<A...>{}(msg...);
}


} // namespace Debug

#  define AUX_CALL_(SEED,Fun) Debug::Tracer _tmp_##SEED##_(Fun);
#  define AUX_CALL(SEED,Fun) AUX_CALL_(SEED,Fun)
#  define CALL(Fun) AUX_CALL(__LINE__,Fun)
#  define DBG(...) {\
  std::cout << "[ debug ] " << __FILE__ <<  "@" << __LINE__ << ":";\
  Debug::Tracer::printDbg(__VA_ARGS__); \
  std::cout << std::endl; \
  }
#  define CALLC(Fun,check) if (check){ AUX_CALL(__LINE__,Fun) }
#  define CONTROL(description) Debug::Tracer::controlPoint(description)
#  define AFTER(number,command) \
            if (Debug::Tracer::passedControlPoints() >= number) { command };
#  define BETWEEN(number1,number2,command) \
            if (Debug::Tracer::passedControlPoints() >= number1 &&	\
                Debug::Tracer::passedControlPoints() <= number2)	\
              { command };

#else // ! VDEBUG
#  define DBG(...) {}
#  define CALL(Fun) 
#  define CALLC(Fun,check) 
#  define CONTROL(description)
#endif

#ifndef CALL
#error BLIN
#endif

#endif // Tracer
