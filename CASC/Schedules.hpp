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
  static void getHigherOrderSchedule2020(Schedule& quick, Schedule& fallback);
  static void getCasc2019Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);

  static void getCascSat2019Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);

  static void getSmtcomp2018Schedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);

  static void getLtb2017Hh4Schedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017IsaSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017HllSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017MzrSchedule(const Shell::Property& property, Schedule& sched);
  static void getLtb2017DefaultSchedule(const Shell::Property& property, Schedule& sched);

  static void getInductionSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getIntegerInductionSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
  static void getStructInductionSchedule(const Shell::Property& property, Schedule& quick, Schedule& fallback);
};

}

#endif // __Schedules__
