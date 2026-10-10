/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "CASC/Schedules.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Shell/SMTLIBLogic.hpp"
#include "Test/UnitTesting.hpp"

#include <atomic>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <string>
#include <system_error>

using namespace CASC;
using namespace Lib;
using namespace Shell;

namespace {

class ScopedOptions
{
public:
  explicit ScopedOptions(bool ignoreUnrecognized = false)
    : _previous(env.options)
  {
    _options.set("ignore_unrecognized_logic", ignoreUnrecognized ? "on" : "off");
    env.options = &_options;
  }

  ~ScopedOptions() { env.options = _previous; }
  ScopedOptions(const ScopedOptions&) = delete;
  ScopedOptions& operator=(const ScopedOptions&) = delete;

private:
  Options* _previous;
  Options _options;
};

// Create a private directory atomically. Cleanup removes only our known file
// and then the empty directory; it never follows a recursive removal path.
class TemporarySchedule
{
public:
  TemporarySchedule()
  {
    static std::atomic<unsigned> sequence{0};
    const auto stamp = std::chrono::steady_clock::now().time_since_epoch().count();
    for (unsigned attempt = 0; attempt < 32; ++attempt) {
      const auto candidate = std::filesystem::temp_directory_path() /
        ("vampire-schedules-" + std::to_string(stamp) + "-" +
         std::to_string(sequence.fetch_add(1)));
      std::error_code error;
      if (std::filesystem::create_directory(candidate, error)) {
        _directory = candidate;
        return;
      }
      ASS(!error);
    }
    ASSERTION_VIOLATION;
  }

  ~TemporarySchedule()
  {
    std::error_code ignored;
    std::filesystem::remove(_directory / "schedule.txt", ignored);
    std::filesystem::remove(_directory, ignored);
  }

  std::string filename() const { return (_directory / "schedule.txt").string(); }

  void write(const std::string& contents) const
  {
    std::ofstream output(filename(), std::ios::binary);
    ASS(output.is_open());
    output << contents;
    output.close();
    ASS(!output.fail());
  }

  TemporarySchedule(const TemporarySchedule&) = delete;
  TemporarySchedule& operator=(const TemporarySchedule&) = delete;

private:
  std::filesystem::path _directory;
};

template<class Action>
void expectUserError(Action action, const std::string& expected)
{
  bool rejected = false;
  try {
    action();
  } catch (UserErrorException& error) {
    ASS_EQ(error.msg(), expected);
    rejected = true;
  }
  ASS(rejected);
}

void assertScheduleEqual(const CASC::Schedule& actual, const CASC::Schedule& expected)
{
  ASS_EQ(actual.size(), expected.size());
  for (unsigned i = 0; i < expected.size(); ++i) {
    ASS_EQ(actual[i], expected[i]);
  }
}

void rejectLogic(SMTLIBLogic logic, const std::string& diagnostic)
{
  ScopedOptions options;
  Property property;
  property.setSMTLIBLogic(logic);
  CASC::Schedule quick;
  expectUserError([&] { Schedules::getSmtcomp2018Schedule(property, quick); }, diagnostic);
  ASS(quick.isEmpty());
}

}

TEST_FUN(schedule_file_rejects_empty_filename)
{
  ScopedOptions options;
  CASC::Schedule quick;
  expectUserError([&] { Schedules::getScheduleFromFile("", quick); }, "Schedule file was not set.");
  ASS(quick.isEmpty());
}

TEST_FUN(schedule_file_rejects_missing_file)
{
  ScopedOptions options;
  TemporarySchedule input;
  CASC::Schedule quick;
  expectUserError([&] { Schedules::getScheduleFromFile(input.filename(), quick); },
                  "Cannot open schedule file: " + input.filename());
  ASS(quick.isEmpty());
}

TEST_FUN(schedule_file_rejects_malformed_strategy)
{
  ScopedOptions options;
  TemporarySchedule input;
  // Unknown nonempty algorithm prefix reaches readFromEncodedOptions' user
  // error, without relying on its separate empty-input assertion.
  input.write("not-a-strategy\n");
  CASC::Schedule quick;
  expectUserError([&] { Schedules::getScheduleFromFile(input.filename(), quick); },
                  "Bad strategy: not-a-strategy");
  ASS(quick.isEmpty());
}

TEST_FUN(schedule_file_keeps_entry_order_and_ignores_empty_lines_and_comments)
{
  ScopedOptions options;
  TemporarySchedule input;
  const std::string first = "lrs+10_1_drc=ordering_90";
  const std::string second = "lrs+10_1_drc=ordering_50";
  input.write("% first comment\n\n" + first + "\n% middle comment\n" + second);
  CASC::Schedule quick;
  quick.push("existing-entry");
  Schedules::getScheduleFromFile(input.filename(), quick);
  ASS_EQ(quick.size(), 3);
  ASS_EQ(quick[0], "existing-entry");
  ASS_EQ(quick[1], first);
  ASS_EQ(quick[2], second);
}

TEST_FUN(smt_schedule_rejects_quantifier_free_logic)
{
  rejectLogic(SMTLIBLogic::QF_UF, "Kein Kinderspiel, Bruder, use Z3 for quantifier-free problems!");
}

TEST_FUN(smt_schedule_rejects_bitvector_logics)
{
  for (auto logic : {SMTLIBLogic::BV, SMTLIBLogic::UFBV}) {
    rejectLogic(logic, "Sorry, we don't deal with bit-vectors!");
  }
}

TEST_FUN(smt_schedule_rejects_undefined_logic_when_not_ignored)
{
  rejectLogic(SMTLIBLogic::UNDEFINED, "This version cannot be used with this logic!");
}

TEST_FUN(smt_schedule_ignored_undefined_logic_matches_all)
{
  ScopedOptions options(true);
  Property undefined;
  undefined.setSMTLIBLogic(SMTLIBLogic::UNDEFINED);
  Property all;
  all.setSMTLIBLogic(SMTLIBLogic::ALL);
  CASC::Schedule actual, expected;
  Schedules::getSmtcomp2018Schedule(undefined, actual);
  Schedules::getSmtcomp2018Schedule(all, expected);
  ASS(!actual.isEmpty());
  assertScheduleEqual(actual, expected);
  ASS(undefined.getSMTLIBLogic() == SMTLIBLogic::UNDEFINED);
}

TEST_FUN(induction_schedule_without_properties_has_two_fallback_entries)
{
  ScopedOptions options;
  Property property;
  CASC::Schedule quick;
  Schedules::getInductionSchedule(property, quick);
  ASS_EQ(quick.size(), 2);
  ASS_EQ(quick[0], "lrs+10_1_drc=ordering_90");
  ASS_EQ(quick[1], "lrs+10_1_drc=ordering_50");
}

TEST_FUN(induction_schedule_integer_only_dispatches_to_integer_schedule)
{
  ScopedOptions options;
  Property property;
  property.addProp(Property::PR_HAS_INTEGERS);
  CASC::Schedule actual, expected;
  Schedules::getInductionSchedule(property, actual);
  Schedules::getIntegerInductionSchedule(property, expected);
  expected.push("lrs+10_1_drc=ordering_50");
  assertScheduleEqual(actual, expected);
}

TEST_FUN(induction_schedule_datatype_only_dispatches_to_structural_schedule)
{
  ScopedOptions options;
  for (auto flag : {Property::PR_HAS_DT_CONSTRUCTORS, Property::PR_HAS_CDT_CONSTRUCTORS}) {
    Property property;
    property.addProp(flag);
    CASC::Schedule actual, expected;
    Schedules::getInductionSchedule(property, actual);
    Schedules::getStructInductionSchedule(property, expected);
    expected.push("lrs+10_1_drc=ordering_50");
    assertScheduleEqual(actual, expected);
  }
}

TEST_FUN(induction_schedule_both_properties_selects_combined_entries)
{
  ScopedOptions options;
  Property property;
  property.addProp(Property::PR_HAS_DT_CONSTRUCTORS | Property::PR_HAS_INTEGERS);
  CASC::Schedule quick;
  quick.push("existing-entry");
  Schedules::getInductionSchedule(property, quick);
  ASS_G(quick.size(), 3);
  ASS_EQ(quick[0], "existing-entry");
  ASS_EQ(quick[1], "dis+1002_1_drc=ordering:aac=none:anc=all:ind=both:sos=theory:sac=on:sstl=1:to=lpo_30");
  ASS_EQ(quick[quick.size() - 1], "lrs+10_1_drc=ordering_50");
}
