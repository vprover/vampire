/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Tracer.cpp
 *
 * @since 01/05/2002 Manchester
 */


#include <climits>
#include <iostream>

#include "Tracer.hpp"

extern const char* VERSION_STRING;

#if VDEBUG

// output nothing
#define CP_FIRST_POINT UINT_MAX
#define CP_LAST_POINT 0u

// output all
// #define CP_FIRST_POINT 0u
// #define CP_LAST_POINT  1481000u

 //#define CP_FIRST_POINT UINT_MAX //185539 
 //#define CP_LAST_POINT UINT_MAX 

using namespace std;
using namespace Debug;

const char* Tracer::_lastControlPoint;
Tracer* Tracer::_current = 0;
unsigned Tracer::_depth = 0;
unsigned Tracer::_passedControlPoints = 0L;
ControlPointKind Tracer::_lastPointKind = CP_MID;
bool Tracer::_forced = false;

/** This variable is needed when all changes in the value of an
 *  an address are traced. To make it work one should define
 *  WATCH_ADDRESS in Allocator.cpp to the watched address. When
 *  the allocator discovers that WATCH_ADDRESS gets allocated
 *  it will set canWatch to true. Allocator will also print to
 *  cout all allocations and deallocations relevant to WATCH_ADDRESS.
 *  In order to watch also all changes of the address one should
 *  define WATCH_ADDR in this file. 
 */
bool Tracer::canWatch = false;

/** To understand how to use the following variable read documentation
 *  to Tracer::canWatch */
// #define WATCH_ADDR 0x38001a0
#define WATCH_ADDR 0
#if WATCH_ADDR
void* watchAddrLastValue = (void*)0;
#endif

Tracer::Tracer (const char* fun) 
  :
  _fun (fun),
  _previous (_current)
{
//   cout << '+' << fun << '\n';
  _current = this;
  controlPoint(_fun,CP_ENTRY);
  _depth++;
} // Tracer::Tracer


Tracer::~Tracer () 
{
//   cout << '-' << _fun << '\n';
  _current = _previous;
  _depth--;
  controlPoint(_fun,CP_EXIT);
} // Tracer::~Tracer


/**
 * Increase the control point counter and remember the description
 * of the last control point. If the control point number is
 * greater than CP_OUTPUT_THRESHOLD, then output the description to
 * cout.
 *
 * @since 12/12/2003 Manchester
 */
void Tracer::controlPoint (const char* description, ControlPointKind cpk)
{
//   AFTER(12339,
// 	cout << "A: " << *((int*)0x88d84b4) << "\n";);
//   if (Allocator<10>::_freeList) {
//     cout << (void*)Allocator<10>::_freeList << " "
// 	 << (void*)Allocator<10>::_freeList->_next
// 	 << " (" <<_passedControlPoints << ")\n";
//   }

  _lastPointKind = cpk;

#if WATCH_ADDR
  if (canWatch) {
    void* newVal = *((void**)WATCH_ADDR);
    if (newVal != watchAddrLastValue) {
      cout << "W! " << newVal << " (timestamp: "
	   << _passedControlPoints << ")\n";
      watchAddrLastValue = newVal;
      cout << "Stack on " << (cpk == CP_EXIT ? "exiting" : "entering")
	   << " the last function on the stack:\n";
      printStack(cout);
    }
  }
#endif

  _passedControlPoints++;

  _lastControlPoint = description;
  if (_forced ||
      (_passedControlPoints <= CP_LAST_POINT &&
       _passedControlPoints >= CP_FIRST_POINT)) {
    outputLastControlPoint(cout);
  }
} // Tracer::controlPoint


/**
 * Increase the control point counter and remember the description
 * of the last control point. If the control point number is
 * greater than CP_OUTPUT_THRESHOLD, then output the description to
 * cout.
 *
 * @since 12/12/2003 Manchester
 */
void Tracer::controlPoint (const char* description)
{
  controlPoint (description,CP_MID);
} // Tracer::controlPoint


/**
 * Output the last control point to an ostream.
 * @since 12/12/2003 Manchester
 */
void Tracer::outputLastControlPoint (ostream& str)
{
  spaces(str,_depth);
  str << (_lastPointKind == CP_ENTRY ? '+' : 
          _lastPointKind == CP_EXIT ? '-' : ' ')
      << _lastControlPoint 
      << " ("
      << _passedControlPoints 
      << ")\n";
} // Tracer::outputLastControlPoint


/**
 * Print the stack.
 * @since 24/10/2002 Manchester
 */
void Tracer::printOnlyStack (ostream& str)
{
  int depth = 0;
  printStackRec (_current, str, depth);
} // Tracer::printStack (ostream& str)


/**
 * Print the stack.
 * @since 24/10/2002 Manchester
 */
void Tracer::printStack (ostream& str)
{
  int depth = 0;

  str << "Version : " << VERSION_STRING << "\n";
  str << "Control points passed: " << _passedControlPoints << "\n"
      << "last control point:\n";
  outputLastControlPoint(str);
  printStackRec (_current, str, depth);
} // Tracer::printStack (ostream& str)


/**
 * Print the stack at a certain depth. The depth is used
 * for indentation.
 * @since 24/10/2002 Manchester
 */
void Tracer::printStackRec(Tracer* current, ostream& str, int& depth)
{
  if (!current) { // beginning of the stack
    return;
  }
  printStackRec(current->_previous,str,depth);
  spaces(str,depth);
  str << current->_fun << "\n";
  depth ++;
} // Tracer::printStack (ostream& str, int& depth)


/**
 * Print n spaces to the stream
 */
void Tracer::spaces (ostream& str,int n)
{
  while (n > 0) {
    n--;
    str << ' ';
  }
} // Tracer::spaces

#endif // VDEBUG
