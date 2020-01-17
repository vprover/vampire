
/*
 * File Schedules.hpp.
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
  static void getCasc2018Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCasc2018PragmaticHOSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback); //big hack!

  static void getCascSat2014Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCascSat2016Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCascSat2017Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getCascSat2018Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);

  static void getSmtcomp2016Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getSmtcomp2017Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getSmtcomp2018Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);

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
