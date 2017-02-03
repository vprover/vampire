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
};

} // namespace Debug

#  define AUX_CALL_(SEED,Fun) Debug::Tracer _tmp_##SEED##_(Fun);
#  define AUX_CALL(SEED,Fun) AUX_CALL_(SEED,Fun)
#  define CALL(Fun) AUX_CALL(__LINE__,Fun)
#  define CALLC(Fun,check) if (check){ AUX_CALL(__LINE__,Fun) }
#  define CONTROL(description) Debug::Tracer::controlPoint(description)
#  define AFTER(number,command) \
            if (Debug::Tracer::passedControlPoints() >= number) { command };
#  define BETWEEN(number1,number2,command) \
            if (Debug::Tracer::passedControlPoints() >= number1 &&	\
                Debug::Tracer::passedControlPoints() <= number2)	\
              { command };

#else // ! VDEBUG
#  define CALL(Fun) 
#  define CALLC(Fun,check) 
#  define CONTROL(description)
#endif

#ifndef CALL
#error BLIN
#endif

#endif // Tracer
