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

  // veci soutezni (szs, ...) oddel od veci portfoliovych

  // from file, bude specialni value --schedule

  // "casc" je posledni casc, "casc2017" je navzdy zadratovany historicky

  // ignore missing should be on in porfolio mode and only give a warning (error in vampire mode - in combination with --decode)

  // vsechny souteze 1 kod (az na LTB)

  // pocet core 1 a vice by mel byt jeden kod

  // pores SLOWNESS

};



}

#endif // __Schedules__
