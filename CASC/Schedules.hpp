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
  static void getCasc2014Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCasc2014EprSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCasc2016Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCasc2017Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);

  static void getCascSat2014Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCascSat2016Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCascSat2017Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);

  static void getSmtcomp2016Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getSmtcomp2017Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);

  static void getLtb2015Hh4FastSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2015Hh4MiddSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2015Hh4SlowSchedule(const Shell::Property& property, Schedule& sched);

  static void getLtb2015IsaFastSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2015IsaMiddSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2015IsaSlowSchedule(const Shell::Property& property, Schedule& sched);

  static void getLtb2015HllFastSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2015HllMiddSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2015HllSlowSchedule(const Shell::Property& property, Schedule& sched);

  static void getLtb2015MzrFastSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2015MzrMiddSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2015MzrSlowSchedule(const Shell::Property& property, Schedule& sched);

  static void getLtb2017Hh4Schedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017IsaSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017HllSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017MzrSchedule(const Shell::Property& property, Schedule& sched);

  static void getLtb2014Schedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2014MzrSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getLtb2017DefaultSchedule(const Shell::Property& property, Schedule& sched);
};



}

#endif // __Schedules__
