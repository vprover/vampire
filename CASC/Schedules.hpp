/**
 * @file Schedules.hpp
 * Defines class Schedules.
 */

#ifndef __Schedules__
#define __Schedules__

#include "Lib/Stack.hpp"
#include "Shell/Property.hpp"

namespace CASC {

typedef Lib::Stack<Lib::vstring> Schedule;

class Schedules
{
public:
  static void getCasc2017Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCascSat2017Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getSmtcomp2017Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);

  static void getLtb2017Hh4Schedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017IsaSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017HllSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017MzrSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017DefaultSchedule(const Shell::Property& property, Schedule& sched);
};



}

#endif // __Schedules__
