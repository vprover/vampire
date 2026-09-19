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
 * @file Options.cpp
 * Implements Vampire options.
 *
 * @since 06/06/2001 Manchester, completely rewritten
 *
 * @since Sep 14 rewritten by Giles
 *
 *
 * IMPORTANT --> see .hpp file for instructions on how to add an option
 */

// Visual does not know the round function
#include <cmath>
#include <fstream>
#include <random>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/StringUtils.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/Set.hpp"

#include "Shell/UIHelper.hpp"
#include "Shell/Property.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"

#include "Parse/TPTP.hpp"

#include "Options.hpp"
#include "Property.hpp"

using namespace std;
using namespace Lib;

static const int COPY_SIZE = 128;

namespace Shell {

template<typename C, typename T>
struct Message {
  const C &constraint;
  const OptionValue<T> &value;
};

template<typename T, typename C>
struct BoxedConstraint : OptionValueConstraint<T> {
  C constraint;
  BoxedConstraint(C c) : constraint(c) {}

  bool check(const OptionValue<T> &value) final {
    return constraint.check(value);
  }

  std::string msg(const OptionValue<T> &value) final {
    stringstream ss;
    ss << Message { constraint, value };
    return ss.str();
  }
};

template<typename T, typename C>
OptionValueConstraintUP<T> boxed(C c) {
  return std::make_unique<BoxedConstraint<T, C>>(c);
}

enum class OptionComparison {
  EQUAL,
  NOT_EQUAL,
  LESS,
  LESS_EQUAL,
  GREATER,
  GREATER_EQUAL
};

std::ostream &operator<<(std::ostream &out, OptionComparison c) {
  switch(c) {
  case OptionComparison::EQUAL:
    return out << "equal to";
  case OptionComparison::NOT_EQUAL:
    return out << "not equal to";
  case OptionComparison::LESS:
    return out << "less than";
  case OptionComparison::LESS_EQUAL:
    return out << "less than or equal";
  case OptionComparison::GREATER:
    return out << "greater than";
  case OptionComparison::GREATER_EQUAL:
    return out << "greater than or equal";
  }
}

template<OptionComparison C, typename T>
struct InequationConstraint {
  bool check(const OptionValue<T> &value) {
    switch(C) {
    case OptionComparison::EQUAL:
      return value.actualValue == ref;
    case OptionComparison::NOT_EQUAL:
      return value.actualValue != ref;
    case OptionComparison::LESS:
      return value.actualValue < ref;
    case OptionComparison::LESS_EQUAL:
      return value.actualValue <= ref;
    case OptionComparison::GREATER:
      return value.actualValue >  ref;
    case OptionComparison::GREATER_EQUAL:
      return value.actualValue >= ref;
    }
  }

  T ref;
};

template<OptionComparison C, typename T>
std::ostream &operator<<(std::ostream &out, Message<InequationConstraint<C, T>, T> message) {
  auto [constraint, value] = message;
  return out
    << value.longName
    << "(" << value.getStringOfActual() << ") is " << C << " "
    << value.getStringOfValue(constraint.ref);
}

template<typename T> static InequationConstraint<OptionComparison::EQUAL, T>
equal(T good) { return { good }; }

template<typename T> static InequationConstraint<OptionComparison::NOT_EQUAL, T>
notEqual(T bad) { return { bad }; }

template<typename T> static InequationConstraint<OptionComparison::LESS, T>
lessThan(T than) { return { than }; }

template<typename T> static InequationConstraint<OptionComparison::LESS_EQUAL, T>
lessThanEq(T than) { return { than }; }

template<typename T> static InequationConstraint<OptionComparison::GREATER, T>
greaterThan(T than) { return { than }; }

template<typename T> static InequationConstraint<OptionComparison::GREATER_EQUAL, T>
greaterThanEq(T than) { return { than }; }

enum class Connective {
  AND,
  OR
};

std::ostream &operator<<(std::ostream &out, Connective c) {
  switch(c) {
  case Connective::AND:
    return out << "and";
  case Connective::OR:
    return out << "or";
  }
}

template<Connective C, typename L, typename R>
struct BinaryConstraint {
  L left;
  R right;

  template<typename T>
  bool check(const OptionValue<T> &value) {
    switch(C) {
    case Connective::AND:
      return left.check(value) && right.check(value);
    case Connective::OR:
      return left.check(value) || right.check(value);
    }
  }
};

template<Connective C, typename L, typename R, typename T>
std::ostream &operator<<(std::ostream &out, Message<BinaryConstraint<C, L, R>, T> message) {
  auto [constraint, value] = message;
  return out
    << Message { constraint.left,  value }
    << C
    << Message { constraint.right, value };
}

template<typename R>
R Or(R r) { return r; }
template<typename L, typename...Rs>
auto Or(L l, Rs...rs) {
  auto r = Or(rs...);
  return BinaryConstraint<Connective::OR, L, decltype(r)> { l, r };
}

template<typename R>
R And(R r) { return r; }
template<typename L, typename...Rs>
auto And(L l, Rs...rs) {
  auto r = And(rs...);
  return BinaryConstraint<Connective::AND, L, decltype(r)> { l, r };
}

template<typename If, typename Then>
struct IfThenConstraint {
  template<typename T>
  bool check(const OptionValue<T> &value) {
    return !if_.check(value) || then.check(value);
  }

  If if_;
  Then then;
};

template<typename If, typename Then, typename T>
std::ostream &operator<<(std::ostream &out, Message<IfThenConstraint<If, Then>, T> message) {
  auto [constraint, value] = message;
  return out
    << "if " << Message {constraint.if_, value}
    << " then " << Message {constraint.then, value};
}

template<typename If>
struct IfPart {
  template<typename Then>
  IfThenConstraint<If, Then> then(Then then) { return { if_, then }; }
  If if_;
};

template<typename If_>
static IfPart<If_> If(If_ if_) { return { if_ }; }

/**
 * Option-(explicitly)-set constraint
 */
struct HasBeenSetConstraint {
  template<typename T>
  bool check(const OptionValue<T> &value) {
    return value.is_set;
  }

  template<typename T>
  void msg(std::ostream &out, const OptionValue<T> &value) {
  }
};

template<typename T>
std::ostream &operator<<(std::ostream &out, Message<HasBeenSetConstraint, T> message) {
  auto [constraint, value] = message;
  return out
    << value.longName
    << "(" << value.getStringOfActual() << ") has been set";
}

static HasBeenSetConstraint hasBeenSet() { return {}; }

/**
 * Default Value constraints
 */
struct NotDefaultConstraint {
  template<typename T>
  bool check(const OptionValue<T> &value) {
    return value.actualValue != value.defaultValue;
  }
};

template<typename T>
std::ostream &operator<<(std::ostream &out, Message<NotDefaultConstraint, T> message) {
  auto [constraint, value] = message;
  return out
    << value.longName
    << "(" << value.getStringOfActual() << ") is not default("
    << value.getStringOfValue(value.defaultValue) << ")";
}

static NotDefaultConstraint isNotDefault() { return {}; }

struct LookAheadSelectionConstraint {
  bool check(const OptionValue<int> &value) {
    return value.actualValue == 11 || value.actualValue == 1011 || value.actualValue == -11 || value.actualValue == -1011;
  }
};

std::ostream &operator<<(std::ostream &out, Message<LookAheadSelectionConstraint, int> message) {
  auto [constraint, value] = message;
  return out
    << value.longName
    << "(" << value.getStringOfActual() << ") is not lookahead selection";
}

template<typename T, typename C>
struct IsConstraint {
  template<typename S>
  bool check(const OptionValue<S> &) {
    return constraint.check(value);
  }

  const OptionValue<T> &value;
  C constraint;
};

template<typename C, typename T, typename S>
std::ostream &operator<<(std::ostream &out, Message<IsConstraint<C, T>, S> message) {
  auto [constraint, value] = message;
  return out << Message {constraint.constraint, constraint.value};
}

template<typename T>
template<typename C>
void OptionValue<T>::addConstraint(C c) {
  _constraints.push(boxed<T>(c));
}

template<typename T>
template<typename C>
void OptionValue<T>::addHardConstraint(C c) {
  auto b = boxed<T>(c);
  b->hard = true;
  _constraints.push(std::move(b));
}

template<typename T>
template<typename C>
void OptionValue<T>::onlyUsefulWith(C c) {
  addConstraint(If(hasBeenSet()).then(c));
}

template<typename T>
template<typename C>
void OptionValue<T>::onlyUsefulWith2(C c) {
  addConstraint(If(isNotDefault()).then(c));
}

template<typename T>
template<typename C>
void OptionValue<T>::reliesOn(C c) {
  addHardConstraint(If(isNotDefault()).then(c));
}

template<typename T>
template<typename C>
auto OptionValue<T>::is(C con) { return IsConstraint { *this, con }; }

auto Options::SelectionOptionValue::isLookAheadSelection() {
  return is(LookAheadSelectionConstraint {});
}

struct CategoryCondition : OptionProblemConstraint{
  CategoryCondition(Property::Category c,bool h) : cat(c), has(h) {}
  bool check(Property*p) override{
      ASS(p);
      return has ? p->category()==cat : p->category()!=cat;
  }
  std::string msg() override{
    std::string m =" not useful for property ";
    if(has) m+="not";
    return m+" in category "+Property::categoryToString(cat);
  }
  Property::Category cat;
  bool has;
};

struct HasTheories : OptionProblemConstraint {
  static bool actualCheck(Property*p);

  bool check(Property*p) override;
  std::string msg() override{ return " only useful with theories"; }
};

struct HasFormulas : OptionProblemConstraint {
  bool check(Property*p) override {
    return p->hasFormulas();
  }
  std::string msg() override{ return " only useful with (non-cnf) formulas"; }
};

struct HasGoal : OptionProblemConstraint {
  bool check(Property*p) override{
    return p->hasGoal();
  }
  std::string msg() override{ return " only useful with a goal: (conjecture) formulas or (negated_conjecture) clauses"; }
};

struct UsesEquality : OptionProblemConstraint{
  bool check(Property*p) override{
    ASS(p)
    return (p->equalityAtoms() != 0) ||
      // theories may introduce equality at various places of the pipeline!
      HasTheories::actualCheck(p) || p->hasFOOL();
  }
  std::string msg() override{ return " only useful with equality"; }
};

struct HasHigherOrder : OptionProblemConstraint{
  bool check(Property*p) override{
    ASS(p)
    return (p->higherOrder());
  }
  std::string msg() override{ return " only useful with higher-order problems"; }
};

struct OnlyFirstOrder : OptionProblemConstraint{
  bool check(Property*p) override{
    ASS(p)
    return (!p->higherOrder());
  }
  std::string msg() override{ return " not compatible with higher-order problems"; }
};

struct MayHaveNonUnits : OptionProblemConstraint{
  bool check(Property*p) override{
    return (p->formulas() > 0) // let's not try to guess what kind of clauses these will give rise to
      || (p->clauses() > p->unitClauses());
  }
  std::string msg() override{ return " only useful with non-unit clauses"; }
};

struct NotJustEquality : OptionProblemConstraint{
  bool check(Property*p) override{
    return (p->category()!=Property::PEQ || p->category()!=Property::UEQ);
  }
  std::string msg() override{ return " not useful with just equality"; }
};

// Factory methods
static OptionProblemConstraintUP notWithCat(Property::Category c){
  return OptionProblemConstraintUP(new CategoryCondition(c,false));
}
static OptionProblemConstraintUP hasEquality(){ return OptionProblemConstraintUP(new UsesEquality); }
static OptionProblemConstraintUP hasHigherOrder(){ return OptionProblemConstraintUP(new HasHigherOrder); }
static OptionProblemConstraintUP onlyFirstOrder(){ return OptionProblemConstraintUP(new OnlyFirstOrder); }
static OptionProblemConstraintUP mayHaveNonUnits(){ return OptionProblemConstraintUP(new MayHaveNonUnits); }
static OptionProblemConstraintUP notJustEquality(){ return OptionProblemConstraintUP(new NotJustEquality); }
static OptionProblemConstraintUP hasFormulas() { return OptionProblemConstraintUP(new HasFormulas); }
static OptionProblemConstraintUP hasTheories() { return OptionProblemConstraintUP(new HasTheories); }
static OptionProblemConstraintUP hasGoal() { return OptionProblemConstraintUP(new HasGoal); }

void AbstractOptionValue::output(std::ostream &out, bool linewrap) const
{
  out << "--" << longName;
  if (shortName) {
    out << " (-" << shortName << ")";
  }
  out << std::endl;

  if (experimental) {
    out << "\t[experimental]" << std::endl;
  }

  if (description) {
    // Break a the description into lines where there have been at least 70 characters
    // on the line at the next space
    out << "\t";
    int count = 0;
    for (const char *p = description; *p; p++) {
      out << *p;
      count++;
      if (linewrap && count > 70 && *p == ' ') {
        out << std::endl
            << '\t';
        count = 0;
      }
      if (*p == '\n') {
        count = 0;
        out << '\t';
      }
    }
    out << std::endl;
  }
  else {
    out << "\tno description provided!" << std::endl;
  }
}

struct AbstractOptionValueCompatator{
  Comparison compare(AbstractOptionValue* o1, AbstractOptionValue* o2)
  {
    int value = strcmp(o1->longName, o2->longName);
    return value < 0 ? LESS : (value==0 ? EQUAL : GREATER);
  }
};

/**
 * Initialize options to the default values.
 *
 * Options are divided by the mode they are applicable to.
 * We then divid by tags where appropriate.
 * If an option is applicable to multiple modes but is not global it should be
 *  put in the most obvious mode - usually Vampire.
 *
 * IMPORTANT --> see .hpp file for instructions on how to add an option
 *
 * @since 10/07/2003 Manchester, _normalize added
 */
Options::Options ()
  : _decode(DecodeOptionValue("decode","",this))

#define VAMPIRE_INIT_BOOL(member, longName, shortName, def, desc, tag, exp) , member(longName, shortName, def)
#define VAMPIRE_INIT_INT(member, longName, shortName, def, desc, tag, exp) , member(longName, shortName, def)
#define VAMPIRE_INIT_UNSIGNED(member, longName, shortName, def, desc, tag, exp) , member(longName, shortName, def)
#define VAMPIRE_INIT_FLOAT(member, longName, shortName, def, desc, tag, exp) , member(longName, shortName, def)
#define VAMPIRE_INIT_LONG(member, longName, shortName, def, desc, tag, exp) , member(longName, shortName, def)
#define VAMPIRE_INIT_STRING(member, longName, shortName, def, desc, tag, exp) , member(longName, shortName, def)
#define VAMPIRE_INIT_CHOICE(enumType, member, longName, shortName, def, choices, desc, tag, exp) \
  , member(longName, shortName, def, {VAMPIRE_EXPAND_CHOICES choices})
  FOR_EACH_VAMPIRE_OPTION(VAMPIRE_INIT_BOOL, VAMPIRE_INIT_INT, VAMPIRE_INIT_UNSIGNED, VAMPIRE_INIT_FLOAT,
                           VAMPIRE_INIT_LONG, VAMPIRE_INIT_STRING, VAMPIRE_INIT_CHOICE)
#undef VAMPIRE_INIT_BOOL
#undef VAMPIRE_INIT_INT
#undef VAMPIRE_INIT_UNSIGNED
#undef VAMPIRE_INIT_FLOAT
#undef VAMPIRE_INIT_LONG
#undef VAMPIRE_INIT_STRING
#undef VAMPIRE_INIT_CHOICE
  , _ageWeightRatio("age_weight_ratio","awr",{1,1},':')
  , _fmbSymmetryWidgetOrders("fmb_symmetry_widget_order","fmbswo",
                                                     FMBWidgetOrders::FUNCTION_FIRST,
                                                     {"function_first","argument_first","diagonal"})
  , _fmbDetectSortBoundsTimeLimit("fmb_detect_sort_bounds_time_limit","fmbdsbt",10)
  , _memoryLimit("memory_limit","m",
#if VDEBUG
                                       1024     //   1 GB
#else
                                       131072   // 128 GB (current max on the StarExecs)
#endif
                                       )
  , _simulatedTimeLimit("simulated_time_limit","stl",0)
  , _predicateWeights("predicate_weights","pw","")
  , _timeLimitInDeciseconds("time_limit","t",600)
  , _tagNames({
                 "Unused",
                 "Other",
                 "Development",
                 "Output",
                 "Portfolio",
                 "Finite Model Building",
                 "SAT Solving",
                 "AVATAR",
                 "Inferences",
                 "Induction",
                 "Theories",
                 "LRS Specific",
                 "Saturation",
                 "Preprocessing",
                 "Input",
                 "Help",
                 "Higher-order",
                 "Global"
                })
  , _nonGoalWeightCoefficient("nongoal_weight_coefficient","nwc")
  , _selection("selection","s",10)
  , _inputFile("input_file","","",this)
{
// NB: the macro parameters below are deliberately NOT called "tag"/"description"/"experimental":
// the preprocessor substitutes them textually, so a parameter named e.g. "tag" would also
// (wrongly) replace the ".tag" in "member.tag" below.
#define VAMPIRE_REG_COMMON(optMember, optDesc, optTag, optExp) \
  optMember.description = optDesc; optMember.tag = optTag; optMember.experimental = optExp; _lookup.insert(optMember);
#define VAMPIRE_REG_BOOL(member, longName, shortName, def, desc, tag, exp) VAMPIRE_REG_COMMON(member, desc, tag, exp)
#define VAMPIRE_REG_INT(member, longName, shortName, def, desc, tag, exp) VAMPIRE_REG_COMMON(member, desc, tag, exp)
#define VAMPIRE_REG_UNSIGNED(member, longName, shortName, def, desc, tag, exp) VAMPIRE_REG_COMMON(member, desc, tag, exp)
#define VAMPIRE_REG_FLOAT(member, longName, shortName, def, desc, tag, exp) VAMPIRE_REG_COMMON(member, desc, tag, exp)
#define VAMPIRE_REG_LONG(member, longName, shortName, def, desc, tag, exp) VAMPIRE_REG_COMMON(member, desc, tag, exp)
#define VAMPIRE_REG_STRING(member, longName, shortName, def, desc, tag, exp) VAMPIRE_REG_COMMON(member, desc, tag, exp)
#define VAMPIRE_REG_CHOICE(enumType, member, longName, shortName, def, choices, desc, tag, exp) VAMPIRE_REG_COMMON(member, desc, tag, exp)
  // Bulk-register the description/tag/experimental-flag/lookup-entry for every "plain"
  // option listed in the FOR_EACH_VAMPIRE_OPTION table above. Per-option value/problem
  // constraints, onlyUsefulWith/reliesOn declarations etc. remain below, next to the
  // (now much shorter) per-option code they always lived next to.
  FOR_EACH_VAMPIRE_OPTION(VAMPIRE_REG_BOOL, VAMPIRE_REG_INT, VAMPIRE_REG_UNSIGNED, VAMPIRE_REG_FLOAT,
                           VAMPIRE_REG_LONG, VAMPIRE_REG_STRING, VAMPIRE_REG_CHOICE)
#undef VAMPIRE_REG_BOOL
#undef VAMPIRE_REG_INT
#undef VAMPIRE_REG_UNSIGNED
#undef VAMPIRE_REG_FLOAT
#undef VAMPIRE_REG_LONG
#undef VAMPIRE_REG_STRING
#undef VAMPIRE_REG_CHOICE
#undef VAMPIRE_REG_COMMON

    _memoryLimit.description="Attempt to limit memory use (in MB). Limits less than 20MB are ignored to allow Vampire to start. Known not to work on MacOS for mysterious reasons: https://forums.developer.apple.com/forums/thread/702803";
    _lookup.insert(_memoryLimit);

    _mode.addHardConstraint(If(equal(Mode::CONSEQUENCE_ELIMINATION)).then(_splitting.is(notEqual(true))));

    auto UsingPortfolioTechnology = [this] {
      // Consider extending this list when adding a new Casc-like mode
      return Or(_mode.is(equal(Mode::CASC)),
                _mode.is(equal(Mode::SMTCOMP)),
                _mode.is(equal(Mode::PORTFOLIO)));
    };

    // Warn about combinations of Intent::SAT and incomplete settings
    _intent.addConstraint(If(equal(Intent::SAT)).then(_sineSelection.is(equal(SineSelection::OFF))));
    _intent.addConstraint(If(equal(Intent::SAT)).then(_equalityProxy.is(equal(EqualityProxy::OFF))));

    _schedule.reliesOn(UsingPortfolioTechnology());

    _scheduleFile.onlyUsefulWith(_schedule.is(equal(Schedule::FILE)));

    _multicore.reliesOn(UsingPortfolioTechnology());

    _slowness.onlyUsefulWith(UsingPortfolioTechnology());

    _randomizeSeedForPortfolioWorkers.onlyUsefulWith(UsingPortfolioTechnology());

    _shuffleOnScheduleRepeats.onlyUsefulWith(UsingPortfolioTechnology());

    _decode.description="Decodes an encoded strategy. Can be used to replay a strategy. To make Vampire output an encoded version of the strategy use the encode option.";
    _lookup.insert(_decode);
    _decode.tag = OptionTag::DEVELOPMENT;

    _sampleStrategy.reliesOn(_mode.is(equal(Mode::VAMPIRE)));

    _randomStrategySeed.reliesOn(_sampleStrategy.is(notEqual(std::string(""))));

    _proof.addHardConstraint(If(equal(Proof::SMTCHECK)).then(_proofExtra.is(equal(ProofExtra::FULL))));

    // stores deciseconds, but reads seconds from the user by default
    _timeLimitInDeciseconds.description="Time limit in wall clock seconds, you can use d,s,m,h,D suffixes also i.e. 60s, 5m. Setting it to 0 effectively gives no time limit.";
    _lookup.insert(_timeLimitInDeciseconds);

#if VTIME_PROFILING
    _timeStatisticsFocus.onlyUsefulWith(_timeStatistics.is(equal(true)));
#endif // VTIME_PROFILING

    _inputFile.description="Problem file to be solved (if not specified, standard input is used)";
    _lookup.insert(_inputFile);
    _inputFile.tag = OptionTag::INPUT;
    _inputFile.experimental = true;

    _guessTheGoalLimit.onlyUsefulWith(_guessTheGoal.is(notEqual(GoalGuess::OFF)));

    _inequalitySplitting.addProblemConstraint(hasEquality());
    _inequalitySplitting.addProblemConstraint(onlyFirstOrder());

    _equalityProxy.addProblemConstraint(hasEquality());
    _equalityProxy.addProblemConstraint(onlyFirstOrder());

    _equalityResolutionWithDeletion.addProblemConstraint(hasEquality());

    _functionDefinitionElimination.addProblemConstraint(hasEquality());

    _generalSplitting.addProblemConstraint(mayHaveNonUnits());

    _unusedPredicateDefinitionRemoval.addProblemConstraint(notWithCat(Property::UEQ));

    _blockedClauseElimination.addProblemConstraint(notWithCat(Property::UEQ));

    _predicateElimination.addProblemConstraint(notWithCat(Property::UEQ));

    _predicateEliminationTotalLimit.addConstraint(greaterThanEq(0.0f));
    _predicateEliminationTotalLimit.onlyUsefulWith(_predicateElimination.is(notEqual(PredicateElimination::OFF)));

    _predicateEliminationSubsumption.onlyUsefulWith(_predicateElimination.is(notEqual(PredicateElimination::OFF)));

    _sineDepth.onlyUsefulWith(_sineSelection.is(notEqual(SineSelection::OFF)));
    _sineGeneralityThreshold.onlyUsefulWith(_sineSelection.is(notEqual(SineSelection::OFF)));
    _sineTolerance.onlyUsefulWith(_sineSelection.is(notEqual(SineSelection::OFF)));
    _sineTolerance.addConstraint(Or(equal(-1.0f),greaterThanEq(1.0f) ));

    _naming.addProblemConstraint(hasFormulas());
    _naming.addHardConstraint(lessThan(32768));
    _naming.addHardConstraint(greaterThan(-1));
    _naming.addHardConstraint(notEqual(1));

    _newCNF.addProblemConstraint(hasFormulas());
    _newCNF.addProblemConstraint(onlyFirstOrder());

    _inlineLet.onlyUsefulWith(_newCNF.is(equal(true)));

#if VZ3
    _problemExportSyntax.reliesOn(Or(_exportAvatarProblem.is(notEqual(std::string(""))), _exportThiProblem.is(notEqual(std::string("")))));
    _exportAvatarProblem.onlyUsefulWith(And(_splitting.is(equal(true)), _satSolver.is(equal(Options::SatSolver::Z3))));
    _exportThiProblem.onlyUsefulWith(_theoryInstAndSimp.is(notEqual(TheoryInstSimp::OFF)));
#endif

    // make the next hard - RSTC will make FMB crash (as RSTC correctly does not trigger hadIncompleteTransformation; still it probably does not make sense to use ep with fmb)
    _saturationAlgorithm.addHardConstraint(If(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)).then(_equalityProxy.is(notEqual(EqualityProxy::RSTC))));

    auto ProperSaturationAlgorithm = [this] {
      return Or(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)),
                _saturationAlgorithm.is(equal(SaturationAlgorithm::OTTER)),
                _saturationAlgorithm.is(equal(SaturationAlgorithm::DISCOUNT)));
    };

    _sos.onlyUsefulWith(ProperSaturationAlgorithm());

    _sosTheoryLimit.onlyUsefulWith(_sos.is(equal(Sos::THEORY)));

    _fmbStartSize.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));

    _fmbSymmetryRatio.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));

    _fmbSymmetryOrderSymbols.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));

    _fmbSymmetryWidgetOrders.description = "The order of constructed principal terms used in symmetry avoidance. See Symmetry Avoidance in MACE-Style Finite Model Finding.";
    // TODO: put back only when debugged (see https://github.com/vprover/vampire/issues/393)
    // _lookup.insert(_fmbSymmetryWidgetOrders);
    _fmbSymmetryWidgetOrders.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbSymmetryWidgetOrders.tag = OptionTag::FMB;

    _fmbAdjustSorts.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbAdjustSorts.addHardConstraint(
      If(equal(FMBAdjustSorts::EXPAND)).then(_fmbEnumerationStrategy.is(notEqual(FMBEnumerationStrategy::CONTOUR))));

    _fmbDetectSortBounds.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbDetectSortBounds.addHardConstraint(If(equal(true)).then(_fmbAdjustSorts.is(notEqual(FMBAdjustSorts::PREDICATE))));
    _fmbDetectSortBounds.addHardConstraint(If(equal(true)).then(_fmbAdjustSorts.is(notEqual(FMBAdjustSorts::FUNCTION))));

    _fmbDetectSortBoundsTimeLimit.description = "The time limit for performing sort bound detection";
    _lookup.insert(_fmbDetectSortBoundsTimeLimit);
    _fmbDetectSortBoundsTimeLimit.onlyUsefulWith(_fmbDetectSortBounds.is(equal(true)));
    _fmbDetectSortBoundsTimeLimit.tag = OptionTag::FMB;

    _fmbSizeWeightRatio.onlyUsefulWith(_fmbEnumerationStrategy.is(equal(FMBEnumerationStrategy::CONTOUR)));
    _fmbSizeWeightRatio.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));

    _fmbEnumerationStrategy.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));

    _fmbKeepSbeamGenerators.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbKeepSbeamGenerators.onlyUsefulWith(_fmbEnumerationStrategy.is(equal(FMBEnumerationStrategy::SBMEAM)));

    _fmbUseSimplifyingSolver.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbUseSimplifyingSolver.onlyUsefulWith(_satSolver.is(equal(SatSolver::MINISAT)));

    _selection.description=
    "Selection methods 2,3,4,10,11 are complete by virtue of extending Maximal i.e. they select the best among maximal. Methods 1002,1003,1004,1010,1011 relax this restriction and are therefore not complete.\n"
    " 0     - Total (select everything)\n"
    " 1     - Maximal\n"
    " 2     - ColoredFirst, MaximalSize then Lexicographical\n"
    " 3     - ColoredFirst, NoPositiveEquality, LeastTopLevelVariables,\n          LeastDistinctVariables then Lexicographical\n"
    " 4     - ColoredFirst, NoPositiveEquality, LeastTopLevelVariables,\n          LeastVariables, MaximalSize then Lexicographical\n"
    " 10    - ColoredFirst, NegativeEquality, MaximalSize, Negative then Lexicographical\n"
    " 11    - Lookahead\n"
    " 666   - Random\n"
    " 1002  - Incomplete version of 2\n"
    " 1003  - Incomplete version of 3\n"
    " 1004  - Incomplete version of 4\n"
    " 1010  - Incomplete version of 10\n"
    " 1011  - Incomplete version of 11\n"
    " 1666  - Incomplete version of 666\n"
    "Or negated, which means that reversePolarity is true i.e. for selection we treat all negative non-equality literals as "
    "positive and vice versa (can only apply to non-equality literals).\n";

    _lookup.insert(_selection);
    _selection.tag = OptionTag::SATURATION;
    _selection.onlyUsefulWith2(ProperSaturationAlgorithm());

    _lookaheadDelay.onlyUsefulWith(_selection.isLookAheadSelection());

    _ageWeightRatio.description=
    "Ratio in which clauses are being selected for activation i.e. A:W means that for every A clauses selected based on age "
    "there will be W selected based on weight. (At most one of A and W can be zero, which means that that queue won't be used at all.)";
    _lookup.insert(_ageWeightRatio);
    _ageWeightRatio.tag = OptionTag::SATURATION;
    _ageWeightRatio.onlyUsefulWith2(ProperSaturationAlgorithm());

    _useTheorySplitQueues.onlyUsefulWith(ProperSaturationAlgorithm());
    // _useTheorySplitQueues.addProblemConstraint(hasTheories()); // recall how they helped even on non-theory problems during CACS 2021?

    _theorySplitQueueExpectedRatioDenom.onlyUsefulWith(_useTheorySplitQueues.is(equal(true)));

    _theorySplitQueueCutoffs.onlyUsefulWith(_useTheorySplitQueues.is(equal(true)));

    _theorySplitQueueRatios.onlyUsefulWith(_useTheorySplitQueues.is(equal(true)));

    _theorySplitQueueLayeredArrangement.onlyUsefulWith(_useTheorySplitQueues.is(equal(true)));

    _useAvatarSplitQueues.onlyUsefulWith(ProperSaturationAlgorithm());
    _useAvatarSplitQueues.onlyUsefulWith(_splitting.is(equal(true)));

    _avatarSplitQueueCutoffs.onlyUsefulWith(_useAvatarSplitQueues.is(equal(true)));

    _avatarSplitQueueRatios.onlyUsefulWith(_useAvatarSplitQueues.is(equal(true)));

    _avatarSplitQueueLayeredArrangement.onlyUsefulWith(_useAvatarSplitQueues.is(equal(true)));

    _useSineLevelSplitQueues.onlyUsefulWith(ProperSaturationAlgorithm());
    _useSineLevelSplitQueues.addProblemConstraint(hasGoal());

    _sineLevelSplitQueueCutoffs.onlyUsefulWith(_useSineLevelSplitQueues.is(equal(true)));

    _sineLevelSplitQueueRatios.onlyUsefulWith(_useSineLevelSplitQueues.is(equal(true)));

    _sineLevelSplitQueueLayeredArrangement.onlyUsefulWith(_useSineLevelSplitQueues.is(equal(true)));

    _usePositiveLiteralSplitQueues.onlyUsefulWith(ProperSaturationAlgorithm());

    _positiveLiteralSplitQueueCutoffs.onlyUsefulWith(_usePositiveLiteralSplitQueues.is(equal(true)));

    _positiveLiteralSplitQueueRatios.onlyUsefulWith(_usePositiveLiteralSplitQueues.is(equal(true)));

    _positiveLiteralSplitQueueLayeredArrangement.onlyUsefulWith(_usePositiveLiteralSplitQueues.is(equal(true)));

    _hoSplitQueues.onlyUsefulWith(ProperSaturationAlgorithm()); // could be "IncludingInstgen"? (not with theories...)
    _hoSplitQueues.addProblemConstraint(hasHigherOrder());

    _hoSplitQueueLambdaWeight.onlyUsefulWith(_hoSplitQueues.is(equal(true)));
    _hoSplitQueueLambdaWeight.addProblemConstraint(hasHigherOrder());

    _hoSplitQueueAppVarWeight.onlyUsefulWith(_hoSplitQueues.is(equal(true)));
    _hoSplitQueueAppVarWeight.addProblemConstraint(hasHigherOrder());

    _hoSplitQueueCutoffs.onlyUsefulWith(_hoSplitQueues.is(equal(true)));

    _hoSplitQueueRatios.onlyUsefulWith(_hoSplitQueues.is(equal(true)));

    _hoSplitQueueLayeredArrangement.onlyUsefulWith(_hoSplitQueues.is(equal(true)));

    _literalMaximalityAftercheck.onlyUsefulWith(ProperSaturationAlgorithm());

    _sineToAge.onlyUsefulWith(ProperSaturationAlgorithm());

    _sineToPredLevels.onlyUsefulWith(ProperSaturationAlgorithm());
    _sineToPredLevels.addHardConstraint(If(notEqual(PredicateSineLevels::OFF)).then(_literalComparisonMode.is(notEqual(LiteralComparisonMode::PREDICATE))));
    _sineToPredLevels.addHardConstraint(If(notEqual(PredicateSineLevels::OFF)).then(_literalComparisonMode.is(notEqual(LiteralComparisonMode::REVERSE))));

    _sineToAgeGeneralityThreshold.onlyUsefulWith(Or(
      _sineToAge.is(equal(true)),
      _sineToPredLevels.is(notEqual(PredicateSineLevels::OFF)),
      _useSineLevelSplitQueues.is(equal(true))));

    _sineToAgeTolerance.addConstraint(Or(equal(-1.0f),greaterThanEq(1.0f)));
    // Captures that if the value is not 1.0 then sineSelection must be on
    _sineToAgeTolerance.onlyUsefulWith(Or(
      _sineToAge.is(equal(true)),
      _sineToPredLevels.is(notEqual(PredicateSineLevels::OFF)),
      _useSineLevelSplitQueues.is(equal(true))));

    _lrsFirstTimeCheck.addConstraint(greaterThanEq(0));
    _lrsFirstTimeCheck.addConstraint(lessThan(100));

    _lrsWeightLimitOnly.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));

    _lrsRetroactiveDeletes.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));

    _lrsPreemptiveDeletes.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));

    _simulatedTimeLimit.description=
    "Time limit in seconds for the purpose of reachability estimations of the LRS saturation algorithm (if 0, the actual time limit is used)";
    _simulatedTimeLimit.onlyUsefulWith(Or(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)),_splittingAvatimer.is(notEqual(1.0f))));
    _lookup.insert(_simulatedTimeLimit);
    _simulatedTimeLimit.tag = OptionTag::LRS;

    _lrsEstimateCorrectionCoef.addConstraint(greaterThan(0.0f));
    _lrsEstimateCorrectionCoef.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));

    _lrsSaveTraceFile.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));

    _lrsLoadTraceFile.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));


#if VZ3
    _theoryInstAndSimp.addProblemConstraint(hasTheories());

    _thiGeneralise.onlyUsefulWith(_theoryInstAndSimp.is(notEqual(TheoryInstSimp::OFF)));

    _thiTautologyDeletion.onlyUsefulWith(_theoryInstAndSimp.is(notEqual(TheoryInstSimp::OFF)));
#endif

    _useACeval.onlyUsefulWith(_alasca.is(equal(false)));

    _inequalityNormalization.addProblemConstraint(hasTheories());

    _cancellation.addProblemConstraint(hasTheories());
    _cancellation.addHardConstraint(If(equal(ArithmeticSimplificationMode::CAUTIOUS))
        .then(And(
              _termOrdering.is(notEqual(TermOrdering::QKBO))
            , _termOrdering.is(notEqual(TermOrdering::LAKBO))
            )));

    _pushUnaryMinus.addProblemConstraint(hasTheories());

    auto addRecommendationConstraint = [](auto& opt, auto constr) {
      // MS: TODO: implement meaningful soft warnings / reminsders to the effect
      // -- this option should best be combined with those values of those other options
      // -- however, note that with alasca on by default but silently disabled when running on non-arith problems
      //    the warnings should only appear when alasca really kicks in, i.e.
      //    only when "env.options->alasca() && prb.hasAlascaArithmetic()"
    };

    addRecommendationConstraint(_alasca, Or(
           _termOrdering.is(equal(TermOrdering::AUTO_KBO)),
           _termOrdering.is(equal(TermOrdering::QKBO)),
           _termOrdering.is(equal(TermOrdering::LAKBO)),
           _termOrdering.is(equal(TermOrdering::ALL_INCOMPARABLE))
           ));
    addRecommendationConstraint(_alasca, _cancellation.is(equal(ArithmeticSimplificationMode::OFF)));
    addRecommendationConstraint(_alasca, _unificationWithAbstraction.is(Or(
              equal(UnificationWithAbstraction::ALASCA_CAN_ABSTRACT)
            , equal(UnificationWithAbstraction::ALASCA_MAIN)
            , equal(UnificationWithAbstraction::ALASCA_MAIN_FLOOR)
            , equal(UnificationWithAbstraction::ALASCA_ONE_INTERP)
            , equal(UnificationWithAbstraction::AUTO)
            )));

    _viras.onlyUsefulWith(_alasca.is(equal(true)));

    _alascaDemodulation.onlyUsefulWith(_alasca.is(equal(true)));

    _alascaStrongNormalization.onlyUsefulWith(_alasca.is(equal(true)));

    _alascaIntegerConversion.onlyUsefulWith(_alasca.is(equal(true)));
    addRecommendationConstraint(_alascaIntegerConversion, _unificationWithAbstraction.is(equal(UnificationWithAbstraction::ALASCA_MAIN_FLOOR)));

    _alascaAbstraction.onlyUsefulWith(_alasca.is(equal(true)));

    _gaussianVariableElimination.addProblemConstraint(hasTheories());

    _arithmeticSubtermGeneralizations.addProblemConstraint(hasTheories());

    _evaluationMode.addProblemConstraint(hasTheories());

    //_induction.setRandomChoices

    _structInduction.onlyUsefulWith(Or(_induction.is(equal(Induction::STRUCTURAL)),_induction.is(equal(Induction::BOTH))));
    _structInduction.addHardConstraint(If(equal(StructuralInductionKind::RECURSION)).then(_newCNF.is(equal(true))));
    _structInduction.addHardConstraint(If(equal(StructuralInductionKind::RECURSION)).then(_equalityResolutionWithDeletion.is(equal(true))));
    _structInduction.addHardConstraint(If(equal(StructuralInductionKind::ALL)).then(_newCNF.is(equal(true))));
    _structInduction.addHardConstraint(If(equal(StructuralInductionKind::ALL)).then(_equalityResolutionWithDeletion.is(equal(true))));

    _intInduction.onlyUsefulWith(Or(_induction.is(equal(Induction::INTEGER)),_induction.is(equal(Induction::BOTH))));

    _inductionChoice.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));
    //_inductionChoice.addHardConstraint(If(equal(InductionChoice::GOAL)->Or(equal(InductionChoice::GOAL_PLUS))).then(
    //  _inputSyntax.is(equal(InputSyntax::TPTP))->Or<InductionChoice>(_guessTheGoal.is(equal(true)))));

    _maxInductionDepth.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));
    _maxInductionDepth.addHardConstraint(lessThan(33u));

    _inductionNegOnly.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));

    _inductionUnitOnly.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));

    _inductionGen.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));

    _maxInductionGenSubsetSize.onlyUsefulWith(_inductionGen.is(equal(true)));
    _maxInductionGenSubsetSize.addHardConstraint(lessThan(10u));

    _inductionStrengthenHypothesis.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));

    _inductionOnComplexTerms.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));

    _inductionGroundOnly.onlyUsefulWith(Or(_induction.is(equal(Induction::STRUCTURAL)),_induction.is(equal(Induction::BOTH))));

    _functionDefinitionRewriting.addHardConstraint(If(equal(true)).then(_newCNF.is(equal(true))));
    _functionDefinitionRewriting.addHardConstraint(If(equal(true)).then(_equalityResolutionWithDeletion.is(equal(true))));

    _integerInductionDefaultBound.onlyUsefulWith(Or(_induction.is(equal(Induction::INTEGER)),_induction.is(equal(Induction::BOTH))));

    _integerInductionInterval.onlyUsefulWith(Or(_induction.is(equal(Induction::INTEGER)),_induction.is(equal(Induction::BOTH))));

    _integerInductionStrictnessEq.onlyUsefulWith(Or(_induction.is(equal(Induction::INTEGER)),_induction.is(equal(Induction::BOTH))));

    _integerInductionStrictnessComp.onlyUsefulWith(Or(_induction.is(equal(Induction::INTEGER)),_induction.is(equal(Induction::BOTH))));

    _integerInductionStrictnessTerm.onlyUsefulWith(Or(_induction.is(equal(Induction::INTEGER)),_induction.is(equal(Induction::BOTH))));

    _nonUnitInduction.reliesOn(_induction.is(notEqual(Induction::NONE)));

    _inductionOnActiveOccurrences.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));

    _backwardDemodulation.addProblemConstraint(hasEquality());
    _backwardDemodulation.onlyUsefulWith(ProperSaturationAlgorithm());

    _backwardSubsumption.onlyUsefulWith(ProperSaturationAlgorithm());
    // bs without fs may lead to rapid looping (when a newly derived clause subsumes its own ancestor already in active) and makes little sense
    _backwardSubsumption.addHardConstraint(
        If(notEqual(Subsumption::OFF)).then(_forwardSubsumption.is(notEqual(false))));

    _backwardSubsumptionResolution.onlyUsefulWith(ProperSaturationAlgorithm());

    _backwardSubsumptionDemodulation.onlyUsefulWith(ProperSaturationAlgorithm());
    _backwardSubsumptionDemodulation.addProblemConstraint(hasEquality());

    _backwardSubsumptionDemodulationMaxMatches.onlyUsefulWith(_backwardSubsumptionDemodulation.is(equal(true)));

    _binaryResolution.onlyUsefulWith(ProperSaturationAlgorithm());
    
    // If urr is off then binary resolution should be on
    // _binaryResolution.addConstraint(If(equal(false)).then(_unitResultingResolution.is(notEqual(URResolution::OFF))));

    _superposition.onlyUsefulWith(ProperSaturationAlgorithm());

    _condensation.onlyUsefulWith(ProperSaturationAlgorithm());

    _demodulationRedundancyCheck.onlyUsefulWith(ProperSaturationAlgorithm());
    _demodulationRedundancyCheck.onlyUsefulWith(Or(_forwardDemodulation.is(notEqual(Demodulation::OFF)),
                                                   _backwardDemodulation.is(notEqual(Demodulation::OFF)),
                                                   _partialRedundancyCheck.is(notEqual(false))));
    _demodulationRedundancyCheck.addProblemConstraint(hasEquality());

    _forwardDemodulationTermOrderingDiagrams.onlyUsefulWith(ProperSaturationAlgorithm());
    _forwardDemodulationTermOrderingDiagrams.onlyUsefulWith(_forwardDemodulation.is(notEqual(Demodulation::OFF)));
    _forwardDemodulationTermOrderingDiagrams.addProblemConstraint(hasEquality());

    _demodulationOnlyEquational.onlyUsefulWith(ProperSaturationAlgorithm());
    _demodulationOnlyEquational.onlyUsefulWith(Or(_forwardDemodulation.is(notEqual(Demodulation::OFF)),_backwardDemodulation.is(notEqual(Demodulation::OFF))));
    _demodulationOnlyEquational.addProblemConstraint(hasEquality());

    _extensionalityAllowPosEq.onlyUsefulWith(_extensionalityResolution.is(equal(ExtensionalityResolution::FILTER)));

    // 0 means infinity, so it is intentionally not if (unsignedValue < 2).
    _extensionalityMaxLength.addConstraint(notEqual(1u));
    _extensionalityMaxLength.onlyUsefulWith(_extensionalityResolution.is(notEqual(ExtensionalityResolution::OFF)));
    //TODO does this depend on anything?

    // Captures that if ExtensionalityResolution is not off then inequality splitting must be 0
    _extensionalityResolution.onlyUsefulWith(_inequalitySplitting.is(equal(0)));

    _forwardDemodulation.onlyUsefulWith(ProperSaturationAlgorithm());

    _forwardGroundJoinability.onlyUsefulWith(ProperSaturationAlgorithm());

    _forwardLiteralRewriting.addProblemConstraint(mayHaveNonUnits());
    _forwardLiteralRewriting.onlyUsefulWith(ProperSaturationAlgorithm());

    _forwardSubsumptionResolution.addHardConstraint(If(equal(true)).then(_forwardSubsumption.is(equal(true))));

    _forwardSubsumptionResolution.onlyUsefulWith(ProperSaturationAlgorithm());

    _forwardSubsumptionDemodulation.onlyUsefulWith(ProperSaturationAlgorithm());
    _forwardSubsumptionDemodulation.addProblemConstraint(hasEquality());

    _forwardSubsumptionDemodulationMaxMatches.onlyUsefulWith(_forwardSubsumptionDemodulation.is(equal(true)));

    _simultaneousSuperposition.onlyUsefulWith(ProperSaturationAlgorithm());

    _innerRewriting.onlyUsefulWith(ProperSaturationAlgorithm());
    _innerRewriting.addProblemConstraint(hasEquality());

    _equationalTautologyRemoval.onlyUsefulWith(ProperSaturationAlgorithm());

    _subsumptionEqualityResolution.onlyUsefulWith(ProperSaturationAlgorithm());

    _partialRedundancyCheck.onlyUsefulWith(ProperSaturationAlgorithm());
    _partialRedundancyCheck.addHardConstraint(If(equal(true)).then(Or(_unificationWithAbstraction.is(equal(UnificationWithAbstraction::AUTO)),
                                                                          _unificationWithAbstraction.is(equal(UnificationWithAbstraction::OFF)))));

    _partialRedundancyOrderingConstraints.onlyUsefulWith(_partialRedundancyCheck.is(equal(true)));

    _partialRedundancyAvatarConstraints.onlyUsefulWith(_partialRedundancyCheck.is(equal(true)));
    _partialRedundancyAvatarConstraints.onlyUsefulWith(_splitting.is(equal(true)));

    _partialRedundancyLiteralConstraints.onlyUsefulWith(_partialRedundancyCheck.is(equal(true)));

    _unitResultingResolution.onlyUsefulWith(ProperSaturationAlgorithm());
    _unitResultingResolution.addProblemConstraint(notJustEquality());
    _unitResultingResolution.addConstraint(If(equal(URResolution::FULL)).then(_splitting.is(equal(true))));
    // If br has already been set off then this will be forced on, if br has not yet been set
    // then setting this to off will force br on

    _superpositionFromVariables.addProblemConstraint(hasEquality());
    _superpositionFromVariables.onlyUsefulWith(ProperSaturationAlgorithm());

    _choiceAxiom.addProblemConstraint(hasHigherOrder());

    _choiceReasoning.addProblemConstraint(hasHigherOrder());
    _choiceReasoning.onlyUsefulWith(_choiceAxiom.is(equal(false))); //no point having two together

    _injectivity.addProblemConstraint(hasHigherOrder());

    _functionExtensionality.addProblemConstraint(hasHigherOrder());

    _clausificationOnTheFly.addProblemConstraint(hasHigherOrder());

    _piSet.addProblemConstraint(hasHigherOrder());

    // equalityToEquivalence: potentially could be useful for FOOL, so am not adding the HOL constraint

    _complexBooleanReasoning.addProblemConstraint(hasHigherOrder());

    // booleanEqTrick: potentially could be useful for FOOL, so am not adding the HOL constraint

    _heuristicInstantiation.onlyUsefulWith(ProperSaturationAlgorithm());
    _heuristicInstantiation.addProblemConstraint(hasHigherOrder());   
    _heuristicInstantiation.addHardConstraint(If(notEqual(false)).then(_clausificationOnTheFly.is(equal(CNFOnTheFly::CONJ_EAGER)))); 

    _higherOrderUnifDepth.addProblemConstraint(hasHigherOrder());    
    _higherOrderUnifDepth.addHardConstraint(lessThan(100u));

    _casesSimp.onlyUsefulWith(_cases.is(equal(false)));
    // casesSimp: potentially could be useful for FOOL, so am not adding the HOL constraint

    //TODO, sort out the mess with cases and FOOLP.
    //One should be removed. AYB
    _cases.onlyUsefulWith(_casesSimp.is(equal(false)));
    // cases: potentially could be useful for FOOL, so am not adding the HOL constraint
    // newTautologyDel: potentially could be useful for FOOL, so am not adding the HOL constraint

    _positiveExt.addProblemConstraint(hasHigherOrder());
    _positiveExt.onlyUsefulWith(_functionExtensionality.is(notEqual(FunctionExtensionality::AXIOM)));

    _iffXorRewriter.addProblemConstraint(hasHigherOrder());

    _globalSubsumption.onlyUsefulWith(ProperSaturationAlgorithm());
    // _globalSubsumption.addProblemConstraint(mayHaveNonUnits()); - this is too strict, think of a better one

    _splitting.onlyUsefulWith(ProperSaturationAlgorithm());
    //_splitting.addProblemConstraint(mayHaveNonUnits());

    _splitAtActivation.onlyUsefulWith(_splitting.is(equal(true)));

    _cleaveNonsplittables.onlyUsefulWith(_splitting.is(equal(true)));

    _splittingAddComplementary.onlyUsefulWith(_splitting.is(equal(true)));

    _splittingCongruenceClosure.onlyUsefulWith(_splitting.is(equal(true)));
#if VZ3
    _splittingCongruenceClosure.onlyUsefulWith(_satSolver.is(notEqual(SatSolver::Z3)));
#endif
    // _splittingCongruenceClosure.addProblemConstraint(hasEquality()); -- not a good constraint for the minimizer

    _splittingLiteralPolarityAdvice.onlyUsefulWith(_splitting.is(equal(true)));

    _splittingMinimizeModel.onlyUsefulWith(_splitting.is(equal(true)));

    _splittingDeleteDeactivated.onlyUsefulWith(_splitting.is(equal(true)));

    _splittingAvatimer.addConstraint(greaterThanEq(0.0f)); //if you want to stop splitting right-away, just turn AVATAR off
    _splittingAvatimer.addConstraint(lessThanEq(1.0f));
    _splittingAvatimer.onlyUsefulWith(_splitting.is(equal(true)));

    _splittingNonsplittableComponents.onlyUsefulWith(_splitting.is(equal(true)));

    _nonliteralsInClauseWeight.onlyUsefulWith(_splitting.is(equal(true)));
    // _nonliteralsInClauseWeight.addProblemConstraint(mayHaveNonUnits()); (for the same reason this is disabled in splitting)

#if VZ3
    _satSolver.addHardConstraint(If(equal(SatSolver::Z3)).then(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::FINITE_MODEL_BUILDING))));
#endif
    _satSolver.onlyUsefulWith(_splitting.is(equal(true)));

#if VZ3

    _satFallbackForSMT.addProblemConstraint(hasTheories()); // Z3 won't be incomplete for pure FOL
    _satFallbackForSMT.onlyUsefulWith(_satSolver.is(equal(SatSolver::Z3)));
#endif

    _increasedNumeralWeight.onlyUsefulWith(ProperSaturationAlgorithm());

    _literalComparisonMode.onlyUsefulWith(ProperSaturationAlgorithm());
    _literalComparisonMode.addProblemConstraint(mayHaveNonUnits());
    _literalComparisonMode.addProblemConstraint(notJustEquality());

    _nonGoalWeightCoefficient.description=
             "coefficient that will multiply the weight of non-conjecture clauses (those marked as 'axiom' in TPTP)";
    _lookup.insert(_nonGoalWeightCoefficient);
    _nonGoalWeightCoefficient.onlyUsefulWith(ProperSaturationAlgorithm());
    _nonGoalWeightCoefficient.tag = OptionTag::SATURATION;

    _restrictNWCtoGC.onlyUsefulWith(_nonGoalWeightCoefficient.is(notEqual(1.0f)));

    _questionAnswering.addHardConstraint(If(equal(QuestionAnsweringMode::PLAIN)).then(ProperSaturationAlgorithm()));
    _questionAnswering.addHardConstraint(If(equal(QuestionAnsweringMode::SYNTHESIS)).then(ProperSaturationAlgorithm()));
    _questionAnswering.addProblemConstraint(onlyFirstOrder()); // currently not supported; but should work in principle when reconciled with the HO-saturation invariants

    _questionAnsweringGroundOnly.onlyUsefulWith(_questionAnswering.is(equal(QuestionAnsweringMode::PLAIN)));

    _questionAnsweringAvoidThese.onlyUsefulWith(_questionAnswering.is(equal(QuestionAnsweringMode::PLAIN)));

    // Even if AUTO_KBO resolves to "qkbo" or "lakbo", we still allow KBO suboptions (and possibly ignore them)
    // this is better than the default (to=auto_kbo) warning whenever we touch "kws" or "kmz" ...
    auto KboLike = [this] {
      return Or(_termOrdering.is(equal(TermOrdering::KBO)),
                _termOrdering.is(equal(TermOrdering::AUTO_KBO)));
    };

    _termOrdering.onlyUsefulWith(ProperSaturationAlgorithm());
    _termOrdering.addHardConstraint(
        If(Or(equal(TermOrdering::QKBO), equal(TermOrdering::LAKBO)))
          .then(_alasca.is(equal(true)))); // <- alasca must be enabled, because the orderings rely on AlascaState to be set

    _symbolPrecedence.onlyUsefulWith(ProperSaturationAlgorithm());

    _kboWeightGenerationScheme.onlyUsefulWith(KboLike());

    _kboMaxZero.onlyUsefulWith(KboLike());

    _kboAdmissabilityCheck.onlyUsefulWith(KboLike());

    _functionWeights.onlyUsefulWith(KboLike());

    _symbolPrecedenceBoost.onlyUsefulWith(ProperSaturationAlgorithm());
} // Options::init

/**
 * Set option by its name and value.
 * @since 13/11/2004 Manchester
 * @since 18/01/2014 Manchester, changed to use _ignoreMissing
 * @since 14/09/2014 updated to use _lookup
 * @author Andrei Voronkov
 */
void Options::set(const char* name,const char* value, bool longOpt)
{
  AbstractOptionValue *option = longOpt ? _lookup.findLong(name) : _lookup.findShort(name);
  if(option) {
    if(!option->set(value)) {
      switch (ignoreMissing()) {
      case IgnoreMissing::OFF:
        USER_ERROR((std::string) value +" is an invalid value for "+(std::string)name+"\nSee vampire -explain "+std::string(name) + " for help.");
        break;
      case IgnoreMissing::WARN:
        if (outputAllowed()) {
          addCommentSignForSZS(std::cout);
          std::cout << "% WARNING: invalid value "<< value << " for option " << name << endl;
        }
        break;
      case IgnoreMissing::ON:
        break;
      }
    }
  } else {
    if (_ignoreMissing.actualValue != IgnoreMissing::ON) {
      std::string msg = (std::string)name + (longOpt ? " is not a valid option" : " is not a valid short option (did you mean --?)");
      if (_ignoreMissing.actualValue == IgnoreMissing::WARN) {
        if (outputAllowed()) {
          addCommentSignForSZS(std::cout);
          std::cout << "% WARNING: " << msg << endl;
        }
        return;
      } // else:
      auto sim = getSimilarOptionNames(name,false);
      decltype(sim)::Iterator sit(sim);
      if(sit.hasNext()){
        auto first = sit.next();
        msg += "\n\tMaybe you meant ";
        if(sit.hasNext()) msg += "one of:\n\t\t";
        msg += first;
        while(sit.hasNext()){ msg+="\n\t\t"; msg+=sit.next();}
        msg+="\n\tYou can use -explain <option> to explain an option";
      }
      USER_ERROR(msg);
    }
  }
} // Options::set/2

/**
 * Set option by its name and value.
 * @since 06/04/2005 Torrevieja
 */
void Options::set(const std::string& name,const std::string& value)
{
  set(name.c_str(),value.c_str(),true);
} // Options::set/2

bool HasTheories::actualCheck(Property*p)
{
  return (p->hasNumerals() || p->hasInterpretedOperations() || env.signature->hasTermAlgebras());
}

bool HasTheories::check(Property*p) {
  // this was the condition used in Preprocess::preprocess guarding the addition of theory axioms
  return actualCheck(p);
}

/**
 * Output options to a stream.
 *
 * @param str the stream
 * @since 02/01/2003 Manchester
 * @since 28/06/2003 Manchester, changed to treat XML output as well
 * @since 10/07/2003 Manchester, "normalize" added.
 * @since 27/11/2003 Manchester, changed using new XML routines and iterator
 *        of options
 */
void Options::output (std::ostream& str) const
{
  if(printAllTheoryAxioms()){
    cout << "Sorry, not implemented yet!" << endl;

    return;
  }

  if(!explainOption().empty()){
     std::string name = explainOption();
     AbstractOptionValue *option = getOptionValueByName(name.c_str());
     if(!option){
       str << name << " not a known option" << endl;
       auto sim_s = getSimilarOptionNames(name.c_str(),true);
       auto sim_l = getSimilarOptionNames(name.c_str(),false);
       auto sit = pvi(concatIters(
           decltype(sim_s)::Iterator(sim_s),decltype(sim_l)::Iterator(sim_l)));
        if(sit.hasNext()){
          auto first = sit.next();
          str << "\tMaybe you meant ";
          if(sit.hasNext()) str << "one of:\n\t\t";
          str << first;
          while(sit.hasNext()){ str << "\n\t\t" << sit.next();}
          str << endl;
        }
     }
     else{
       std::stringstream vs;
       option->output(vs,lineWrapInShowOptions());
       str << vs.str();
     }

  }

  if (showHelp())
    str <<
      "Usage: vampire [OPTIONS] PROBLEM\n\n"
      "Supported options:\n\n"
      "\t--mode portfolio (execute a schedule of many different proof attempts)\n"
      "\t--schedule <schedule> (in portfolio mode, use the builtin <schedule>)\n"
      "\t--input_syntax {tptp,smtlib2} (read TPTP or SMT-LIB 2.x input)\n"
      "\t--proof tptp (use the TSTP proof format)\n"
      "\t--output_mode {smtcomp,ucore} (output only sat/unsat with an optional core)\n"
      "\t--time_limit <seconds> (limit Vampire's runtime)\n\n"
      "Use '--show_options on' to see all available options.\n";

  bool normalshow = showOptions();
  bool experimental = showExperimentalOptions();

  if(normalshow || experimental) {
    //str << "=========== Options ==========\n";

    auto options = _lookup.values();

    int num_tags = static_cast<int>(OptionTag::LAST_TAG);
    Stack<Stack<AbstractOptionValue*>> groups;
    for(int i=0; i<=num_tags;i++){
        Stack<AbstractOptionValue*> stack;
        groups.push(stack);
    }


    while(options.hasNext()){
      AbstractOptionValue* option = options.next();
      if(((experimental && option->experimental) ||
          (normalshow && !option->experimental))) {
        unsigned tag = static_cast<unsigned>(option->tag);
        //option->output(*groups[tag]);
        (groups[tag]).push(option);
      }
    }

    //output them in reverse order
    for(int i=num_tags;i>=0;i--){
      if(groups[i].isEmpty()) continue;
      std::string label = "  "+std::string(_tagNames[i])+"  ";
      ASS(label.length() < 40);
      std::string br = "******************************";
      std::string br_gap = br.substr(0,(br.length()-(label.length()/2)));
      str << endl << br << br;
      if (label.length() % 2 == 0) {
        str << endl;
      } else {
        str << "*" << endl;
      }
      str << br_gap << label << br_gap << endl;
      str << br << br;
      if (label.length() % 2 == 0) {
        str << endl << endl;
      } else {
        str << "*" << endl << endl;
      }

      // Sort
      Stack<AbstractOptionValue*> os = groups[i];
      DArray<AbstractOptionValue*> osa;
      osa.initFromIterator(Stack<AbstractOptionValue*>::Iterator(os));
      osa.sort(AbstractOptionValueCompatator());
      DArray<AbstractOptionValue*>::Iterator oit(osa);
      while(oit.hasNext()){
        oit.next()->output(str,lineWrapInShowOptions());
      }
      //str << (*groups[i]).str();
      //delete groups[i];
    }

    //str << "======= End of options =======\n";
  }

} // Options::output (std::ostream& str) const

bool AbstractOptionValue::checkProblemConstraints(Property* prop){
    Lib::Stack<OptionProblemConstraintUP>::RefIterator it(_prob_constraints);
    while(it.hasNext()){
      OptionProblemConstraintUP& con = it.next();
      // Constraint should hold whenever the option is set
      if(is_set && !con->check(prop)){

         if (env.options->mode() == Options::Mode::SPIDER){
           reportSpiderFail();
           USER_ERROR("% WARNING: " + std::string(longName) + con->msg());
         }

         switch(env.options->getBadOptionChoice()){
         case Options::Options::BadOption::OFF: break;
         default:
           cout << "% WARNING: " << longName << con->msg() << endl;
         }
         return false;
      }
    }
    return true;
}

/**
 * Read age-weight ratio from a string. The string can be an integer
 * or an expression "a:w", where a,w are unsigned integers.
 *
 * @since 25/05/2004 Manchester
 */
bool Options::RatioOptionValue::readRatio(const char* val, char separator)
{
  // search the string for ":"
  bool found = false;
  int colonIndex = 0;
  while (val[colonIndex]) {
    if (val[colonIndex] == separator) {
      found = true;
      break;
    }
    colonIndex++;
  }

  if (found) {
    if (strlen(val) >= COPY_SIZE) {
      return false;
    }
    char copy[COPY_SIZE];
    strncpy(copy,val,COPY_SIZE - 1); // leave space for trailing NUL
    copy[colonIndex] = 0;
    unsigned age;
    if (! Int::stringToUnsignedInt(copy,age)) {
      return false;
    }
    actualValue.first = age;
    unsigned weight;
    if (! Int::stringToUnsignedInt(copy+colonIndex+1,weight)) {
      return false;
    }
    actualValue.second = weight;

    // don't allow ratios 0:0
    if (!actualValue.first && !actualValue.second) {
      return false;
    }

    return true;
  }
  actualValue.first = 1;
  unsigned weight;
  if (! Int::stringToUnsignedInt(val,weight)) {
    return false;
  }
  actualValue.second = weight;
  return true;
}

bool Options::NonGoalWeightOptionValue::setValue(const std::string& value)
{
 float newValue;
 if(!Int::stringToFloat(value.c_str(),newValue)) return false;

 if(newValue <= 0.0) return false;

 actualValue=newValue;

  // actualValue contains numerator
  numerator=static_cast<int>(newValue*100);
  // otherValue contains denominator
  denominator=100;

  return true;
}

bool Options::SelectionOptionValue::setValue(const std::string& value)
{
  int sel;
  if(!Int::stringToInt(value,sel)) return false;
  switch (sel) {
  case 0:
  case 1:
  case 2:
  case 3:
  case 4:
  case 10:
  case 11:
  case 20:
  case 21:
  case 22:

  case 30:
  case 31:
  case 32:
  case 33:
  case 34:
  case 35:

  case 666:

  case 1002:
  case 1003:
  case 1004:
  case 1010:
  case 1011:
  case 1666:
  case -1:
  case -2:
  case -3:
  case -4:
  case -10:
  case -11:
  case -20: // almost same as 20 (but factoring will be on negative and not positive literals)
  case -21:
  case -22:
  case -30: // almost same as 30 (but factoring will be on negative and not positive literals)
  case -31:
  case -32:
  case -33:
  case -34:
  case -35:

  case -666:

  case -1002:
  case -1003:
  case -1004:
  case -1010:
  case -1011: // almost same as 1011 (but factoring will be on negative and not positive literals)
  case -1666:
    actualValue = sel;
    return true;
  default:
    return false;
  }
}

bool Options::InputFileOptionValue::setValue(const std::string& value)
{
  actualValue=value;
  if(value.empty()) return true;

  //update the problem name

  int length = value.length();
  const char* name = value.c_str();

  int b = length - 1;
  while (b >= 0 && name[b] != '/') {
    b--;
  }
  b++;

  int e = length - 1;
  while (e >= b && name[e] != '.') {
    e--;
  }
  if (e < b) {
    e = length;
  }

  parent->problemName=value.substr(b,e-b);

  return true;
}


bool Options::TimeLimitOptionValue::setValue(const std::string& value)
{
  int length = value.size();
  if (length == 0 || length >= COPY_SIZE) {
    USER_ERROR((std::string)"wrong value for time limit: " + value);
  }

  char copy[COPY_SIZE];
  strncpy(copy,value.c_str(),COPY_SIZE - 1); // leave space for trailing NUL
  char* end = copy;
  // search for the end of the string for
  while (*end) {
    end++;
  }
  end--;
  float multiplier = 10.0; // by default assume seconds
  switch (*end) {
  case 'd': // deciseconds
      multiplier = 1.0;
      *end = 0;
      break;
  case 's': // seconds
    multiplier = 10.0;
    *end = 0;
    break;
  case 'm': // minutes
    multiplier = 600.0;
    *end = 0;
    break;
  case 'h': // minutes
    multiplier = 36000.0;
    *end = 0;
    break;
  case 'D': // days
    multiplier = 864000.0;
    *end = 0;
    break;
  default:
    break;
  }

  float number;
  if (! Int::stringToFloat(copy,number)) {
    USER_ERROR((std::string)"wrong value for time limit: " + value);
  }

#ifdef _MSC_VER
  // Visual C++ does not know the round function
  actualValue= (int)floor(number * multiplier);
#else
  actualValue= (int)round(number * multiplier);
#endif

  return true;
} // Options::readTimeLimit(const char* val)

/**
 * During strategy sampling, this assigns a value to an option
 * (but checks these make sense and issues an error if not).
 *
 * An optname starting with $ is not meant to be a real option, but a fake one.
 * Fakes get stored in the map fakes and can be referenced later, during the sampling process.
 */
void Options::strategySamplingAssign(std::string optname, std::string value, DHMap<std::string,std::string, FnvHash, LengthHash>& fakes)
{
  // dollar sign signifies fake options
  if (optname[0] == '$') {
    fakes.set(optname,value);
    return;
  }

  AbstractOptionValue* opt = getOptionValueByName(optname.c_str());
  if (opt) {
    if (!opt->set(value,/* dont_touch_if_defaulting =*/ true)) {
      USER_ERROR("Sampling file processing error -- unknown option value: " + value + " for option " + optname);
    }

  } else {
    USER_ERROR("Sampling file processing error -- unknown option: " + optname);
  }
}

/**
 * During strategy sampling, this reads a value of an option
 * (but checks the name make sense and issues an error if not).
 *
 * An optname starting with $ is not meant to be a real option, but a fake one.
 * Fakes get read from the given map fakes.
 */
std::string Options::strategySamplingLookup(std::string optname, DHMap<std::string,std::string, FnvHash, LengthHash>& fakes)
{
  if (optname[0] == '$' || optname[0] == '@') {
    std::string* foundVal = fakes.findPtr(optname);
    if (!foundVal) {
      USER_ERROR("Sampling file processing error -- unassigned fake option: " + optname);
    }
    return *foundVal;
  }

  AbstractOptionValue* opt = getOptionValueByName(optname.c_str());
  if (opt) {
    return opt->getStringOfActual();
  } else {
    USER_ERROR("Sampling file processing error -- unknown option to look up: " + optname);
  }
  return "";
}

void Options::sampleStrategy(const std::string& strategySamplerFilename, DHMap<std::string,std::string, FnvHash, LengthHash> fakes)
{
  std::ifstream input(strategySamplerFilename.c_str());

  if (input.fail()) {
    USER_ERROR("Cannot open sampler file: "+strategySamplerFilename);
  }

  // our local randomizing engine (randomly seeded)
  auto rng = _randomStrategySeed.actualValue == 0
    ? std::mt19937((std::random_device())())
    : std::mt19937(_randomStrategySeed.actualValue);

  std::string line; // parsed lines
  Stack<std::string> pieces; // temp stack used for splitting
  while (std::getline(input, line))
  {
    if (line.length() == 0 || line[0] == '#') { // empty lines and comments (starting with # as the first! character)
      continue;
    }

    StringUtils::splitStr(line.c_str(),'>',pieces);
    if (pieces.size() != 2) {
      USER_ERROR("Sampling file parse error -- each rule must contain exactly one >. Here: "+line);
    }

    std::string cond = pieces[0];
    std::string body = pieces[1];
    pieces.reset();

    // evaluate condition, if false, will skip the rest
    bool fireRule = true;
    {
      StringUtils::splitStr(cond.c_str(),' ',pieces);
      StringUtils::dropEmpty(pieces);

      Stack<std::string> pair;
      Stack<std::string>::BottomFirstIterator it(pieces);
      while(it.hasNext()) {
        std::string equation = it.next();
        StringUtils::splitStr(equation.c_str(),'=',pair);
        StringUtils::dropEmpty(pair);
        if (pair.size() != 2) {
          USER_ERROR("Sampling file parse error -- invalid equation: "+equation);
        }
        bool negated = false;
        std::string optName = pair[0];
        if (optName.back() == '!') {
          negated = true;
          optName.pop_back();
        }
        std::string storedVal = strategySamplingLookup(optName,fakes);
        if ((storedVal != pair[1]) != negated) {
          fireRule = false;
          break;
        }
        pair.reset();
      }

      pieces.reset();
    }

    if (!fireRule) {
      continue;
    }

    // now it's time to read the body
    // cout << "fire: " << body << endl;

    StringUtils::splitStr(body.c_str(),' ',pieces);
    StringUtils::dropEmpty(pieces);
    if (pieces.size() != 3) {
      USER_ERROR("Sampling file parse error -- rule body must consist of three space-separated parts. Here: "+body);
    }

    std::string optname = pieces[0];
    std::string sampler = pieces[1];
    std::string args = pieces[2];
    pieces.reset();

    if (sampler == "~set") {
      ASS_NEQ(args,"");
      strategySamplingAssign(optname,args,fakes);
    } else if (sampler == "~cat") { // categorical sampling, e.g., "~cat group:36,predicate:4,expand:4,off:1,function:1" provides a list of value with frequencies
      StringUtils::splitStr(args.c_str(),',',pieces);

      unsigned total = 0;
      Stack<std::pair<unsigned,std::string>> mulvals; //values with multiplicities, e.g. "off:5", or "on:1"

      // parse the mulvals
      {
        Stack<std::string> pair;
        Stack<std::string>::BottomFirstIterator it(pieces);
        while(it.hasNext()) {
          std::string mulval = it.next();
          StringUtils::splitStr(mulval.c_str(),':',pair);
          // StringUtils::dropEmpty(pair);
          if (pair.size() != 2) {
            USER_ERROR("Sampling file parse error -- invalid mulval: "+mulval);
          }

          int multiplicity = 0;
          if (!Int::stringToInt(pair[1],multiplicity) || multiplicity <= 0) {
            USER_ERROR("Sampling file parse error -- invalid multiplicity in mulval: "+mulval);
          }
          total += multiplicity;
          mulvals.push(std::make_pair(multiplicity,pair[0]));
          pair.reset();
        }
        pieces.reset();
      }

      // actual sampling
      std::string value;
      unsigned sample = std::uniform_int_distribution<unsigned>(1,total)(rng);
      Stack<std::pair<unsigned,std::string>>::BottomFirstIterator it(mulvals);
      while (it.hasNext()) {
        auto mulval = it.next();
        if (sample <= mulval.first) {
          value = mulval.second;
          break;
        }
        sample -= mulval.first;
      }
      ASS_NEQ(value,"");

      strategySamplingAssign(optname,value,fakes);
    } else if (sampler == "~u2r") { // "uniform to ratio", given e.g. "~u2r -10;4;:" takes a uniform float f between -10 and 4, computes 2^r and turns this into a ratio with ":" as the separator
      StringUtils::splitStr(args.c_str(),';',pieces);
      StringUtils::dropEmpty(pieces);

      if (pieces.size() != 3) {
        USER_ERROR("Sampling file parse error -- ~u2r sampler expects exactly three simecolon-separated arguments but got: "+args);
      }
      if (pieces[2].length() != 1) {
        USER_ERROR("Sampling file parse error -- the third argument of the ~u2r sampler needs to be a single character and not: "+pieces[2]);
      }
      float low,high;
      if (!Int::stringToFloat(pieces[0].c_str(),low) || !Int::stringToFloat(pieces[1].c_str(),high)) {
        USER_ERROR("Sampling file parse error -- can't convert one of ~u2r sampler arguments to float: "+args);
      }
      std::uniform_real_distribution<float> dis(low,high);
      float raw = dis(rng);
      float exped = powf(2.0,raw);
      unsigned denom = 1 << 20;
      unsigned numer = exped*denom;
      // don't generate factions in non-base form
      while (numer % 2 == 0 && denom % 2 == 0) {
        numer /= 2;
        denom /= 2;
      }
      strategySamplingAssign(optname,Int::toString(numer)+pieces[2]+Int::toString(denom),fakes);

      pieces.reset();
    } else if (sampler == "~sgd") { // "shifted geometric distribution", e.g. "~sgd 0.07,2" (used for naming) means: value 2+i, i from N, has probability 0.07*(1-0.07)^i. This has a mean of 2+0.07*(1-0.07)
      StringUtils::splitStr(args.c_str(),',',pieces);
      StringUtils::dropEmpty(pieces);

      if (pieces.size() != 2) {
        USER_ERROR("Sampling file parse error -- ~sgd sampler expects exactly two comma-separated arguments but got: "+args);
      }
      double prob;
      int offset;
      if (!Int::stringToDouble(pieces[0].c_str(),prob) || !Int::stringToInt(pieces[1].c_str(),offset)) {
        USER_ERROR("Sampling file parse error -- can't convert one of ~sgd sampler arguments to numbers: "+args);
      }
      std::geometric_distribution<int> dis(prob);
      int nval = offset+dis(rng);
      strategySamplingAssign(optname,Int::toString(nval),fakes);

      pieces.reset();
    } else if (sampler == "~uf") { // uniform float (with lower and upper bound given, as in "~uf 0.0,0.5")
      StringUtils::splitStr(args.c_str(),',',pieces);
      StringUtils::dropEmpty(pieces);

      if (pieces.size() != 2) {
        USER_ERROR("Sampling file parse error -- ~uf sampler expects exactly two comma-separated arguments but got: "+args);
      }
      float low,high;
      if (!Int::stringToFloat(pieces[0].c_str(),low) || !Int::stringToFloat(pieces[1].c_str(),high)) {
        USER_ERROR("Sampling file parse error -- can't convert one of ~uf sampler arguments to float: "+args);
      }
      std::uniform_real_distribution<float> dis(low,high);
      float raw = dis(rng);
      strategySamplingAssign(optname,Int::toString(raw),fakes);

      pieces.reset();
    } else if (sampler == "~ui") { // uniform int (with lower and upper bound given, as in "~ui 1,500")
      StringUtils::splitStr(args.c_str(),',',pieces);
      StringUtils::dropEmpty(pieces);

      if (pieces.size() != 2) {
        USER_ERROR("Sampling file parse error -- ~ui sampler expects exactly two comma-separated arguments but got: "+args);
      }
      int low,high;
      if (!Int::stringToInt(pieces[0].c_str(),low) || !Int::stringToInt(pieces[1].c_str(),high)) {
        USER_ERROR("Sampling file parse error -- can't convert one of ~ui sampler arguments to integer: "+args);
      }
      std::uniform_int_distribution<int> dis(low,high);
      int raw = dis(rng);
      strategySamplingAssign(optname,Int::toString(raw),fakes);

      pieces.reset();
    } else {
      USER_ERROR("Sampling file parse error -- unrecognized sampler: " + sampler);
    }

    /*
    Stack<std::string>::BottomFirstIterator it(pieces);
    while(it.hasNext()) {
      cout << "tok:" << it.next() << endl;
    }
    */
  }

  cout << "% Random strategy: " + generateEncodedOptions() << endl;
}

/**
 * Assign option values as encoded in the option std::string if assign=true, otherwise check that
 * the option values are not currently set to those values.
 * according to the argument in the format
 * opt1=val1:opt2=val2:...:optn=valN,
 * for example bs=off:cond=on:drc=off:nwc=1.5:nicw=on:sos=on:sio=off:spl=sat:ssnc=none
 */
void Options::readOptionsString(std::string optionsString,bool assign)
{
  // repeatedly look for param=value
  while (optionsString != "") {
    size_t index1 = optionsString.find('=');
    if (index1 == std::string::npos) {
      error: USER_ERROR("bad option specification '" + optionsString+"'");
    }
    size_t index = optionsString.find(':');
    if (index!=std::string::npos && index1 > index) {
      goto error;
    }

    std::string param = optionsString.substr(0,index1);
    std::string value;
    if (index==std::string::npos) {
      value = optionsString.substr(index1+1);
    }
    else {
      value = optionsString.substr(index1+1,index-index1-1);
    }
    AbstractOptionValue* opt = getOptionValueByName(param.c_str());
    if(opt){
        if(assign){
            if (!opt->set(value)) {
              switch (ignoreMissing()) {
              case IgnoreMissing::OFF:
                USER_ERROR("value "+value+" for option "+ param +" not known");
                break;
              case IgnoreMissing::WARN:
                if (outputAllowed()) {
                  addCommentSignForSZS(std::cout);
                  std::cout << "% WARNING: value " << value << " for option "<< param <<" not known" << endl;
                }
                break;
              case IgnoreMissing::ON:
                break;
              }
            }
        }
        else{
            std::string current = opt->getStringOfActual();
            if(value==current){
                USER_ERROR("option "+param+" uses forbidden value "+value);
            }
        }
    }
    else{
      switch (ignoreMissing()) {
      case IgnoreMissing::OFF:
        USER_ERROR("option "+param+" not known");
        break;
      case IgnoreMissing::WARN:
        if (outputAllowed()) {
          addCommentSignForSZS(std::cout);
          std::cout << "% WARNING: option "<< param << " not known." << endl;
        }
        break;
      case IgnoreMissing::ON:
        break;
      }
    }

    if (index==std::string::npos) {
      return;
    }
    optionsString = optionsString.substr(index+1);
  }
} // readOptionsString/1

/**
 * Build options from a Spider test id.
 * @since 30/05/2004 Manchester
 * @since 21/06/2005 Manchester time limit in the test id must be
 *        in deciseconds
 * @throws UserErrorException if the test id is incorrect
 */
void Options::readFromEncodedOptions (std::string testId)
{
  ASS(!testId.empty())
  _testId.actualValue = testId;

  std::string ma(testId,0,3); // the first 3 characters
  if (ma == "dis") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::DISCOUNT;
  }
  else if (ma == "lrs") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::LRS;
  }
  else if (ma == "ott") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::OTTER;
  }
  else if (ma == "fmb") {
    _saturationAlgorithm.actualValue = SaturationAlgorithm::FINITE_MODEL_BUILDING;
  }
  else {
  error: USER_ERROR("bad test id " + _testId.actualValue);
  }

  // after last '_' we have time limit
  size_t index = testId.find_last_of('_');
  if (index == std::string::npos) { // not found
    goto error;
  }
  std::string timeString = testId.substr(index+1);
  _timeLimitInDeciseconds.set(timeString);
  // setting assumes seconds as default, but encoded strings use deciseconds
  _timeLimitInDeciseconds.actualValue = _timeLimitInDeciseconds.actualValue/10;

  testId = testId.substr(3,index-3);
  switch (testId[0]) {
  case '+':
    testId = testId.substr(1);
    break;
  case '-':
    break;
  default:
    goto error;
  }

  index = testId.find('_');
  std::string sel = testId.substr(0,index);
  _selection.set(sel);
  testId = testId.substr(index+1);

  if (testId == "") {
    goto error;
  }

  index = testId.find('_');
  std::string awr = testId.substr(0,index);
  _ageWeightRatio.set(awr.c_str());
  if (index==string::npos) {
    //there are no extra options
    return;
  }
  testId = testId.substr(index+1);
  //now read the rest of the options
  readOptionsString(testId);
} // Options::readFromTestId

void Options::setForcedOptionValues()
{
  if(_forcedOptions.actualValue.empty()) return;
  readOptionsString(_forcedOptions.actualValue);
}

/**
 * Return testId std::string that represents current values of the options
 */
std::string Options::generateEncodedOptions() const
{
  std::ostringstream res;
  //saturation algorithm
  std::string sat;
  switch(_saturationAlgorithm.actualValue){
    case SaturationAlgorithm::LRS : sat="lrs"; break;
    case SaturationAlgorithm::DISCOUNT : sat="dis"; break;
    case SaturationAlgorithm::OTTER : sat="ott"; break;
    case SaturationAlgorithm::FINITE_MODEL_BUILDING : sat="fmb"; break;
    default : ASSERTION_VIOLATION;
  }

  res << sat;

  //selection function
  res << (selection() < 0 ? "-" : "+") << abs(selection());
  res << "_";

  //age-weight ratio
  if (ageRatio()!=1) {
    res << ageRatio() << ":";
  }
  res << weightRatio();
  res << "_";

  // Record options that do not want to be in encoded string
  // TODO this could just be a field on AbstractOptionValue
  static Set<const AbstractOptionValue*, FnvHash> forbidden;
  //we initialize the set if there's nothing inside
  if (forbidden.size()==0) {
    //things we output elsewhere
    forbidden.insert(&_saturationAlgorithm);
    forbidden.insert(&_selection);
    forbidden.insert(&_ageWeightRatio);
    forbidden.insert(&_timeLimitInDeciseconds);

    // not filenames, please
    forbidden.insert(&_lrsSaveTraceFile);
    forbidden.insert(&_lrsLoadTraceFile);

    //things we don't want to output (showHelp etc won't get to here anyway)
    forbidden.insert(&_mode);
    forbidden.insert(&_intent);
    forbidden.insert(&_testId); // is this old version of decode?
    forbidden.insert(&_include);
    forbidden.insert(&_printProofToFile);
    forbidden.insert(&_inputFile);
    forbidden.insert(&_encode);
    forbidden.insert(&_decode);
    forbidden.insert(&_sampleStrategy);
    forbidden.insert(&_normalize);
    forbidden.insert(&_randomizeSeedForPortfolioWorkers);
    forbidden.insert(&_schedule);
    forbidden.insert(&_scheduleFile);

    forbidden.insert(&_memoryLimit);
    forbidden.insert(&_proof);
    forbidden.insert(&_inputSyntax);
    forbidden.insert(&_multicore);
    forbidden.insert(&_statistics);
    forbidden.insert(&_forcedOptions);
#if VAMPIRE_PERF_EXISTS
    forbidden.insert(&_parsingDoesNotCount);
#endif
    forbidden.insert(&_ignoreMissing); // or maybe we do!
  }

  auto options = _lookup.values();

  bool first=true;
  while(options.hasNext()){
    AbstractOptionValue* option = options.next();
    if (!forbidden.contains(option) && !option->isDefault()){
      auto name = option->shortName;
      if(!name) name = option->longName;
      if(!first){ res<<":";}else{first=false;}
      res << name << "=" << option->getStringOfActual();
    }
  }

  if(!first){ res << "_"; }
  res << Lib::Int::toString(_timeLimitInDeciseconds.actualValue);

  return res.str();
}

/**
 * Some options have auto-values,
 * which should be resolved away BEFORE preprocessing.
 *
 * @since 9/03/2025 Prague
 */
void Options::resolveAwayAutoValues0()
{
  if (questionAnswering() == Options::QuestionAnsweringMode::AUTO) {
    setQuestionAnswering(
        (Parse::TPTP::seenQuestions() && saturationAlgorithm() != Options::SaturationAlgorithm::FINITE_MODEL_BUILDING ) ?
          Options::QuestionAnsweringMode::PLAIN : Options::QuestionAnsweringMode::OFF);
  }
}

/**
 * Some options have auto-values, which should be resolved away
 * after preprocessing and before we enter saturation.
 *
 * @since 9/03/2025 Prague
 */
void Options::resolveAwayAutoValues(const Problem& prb)
{
  if (termOrdering() == TermOrdering::AUTO_KBO) {
    if (alasca() && prb.hasAlascaArithmetic()) {
      if (prb.hasAlascaMixedArithmetic()) {
        _termOrdering.actualValue = Options::TermOrdering::QKBO;
      } else {
        _termOrdering.actualValue = Options::TermOrdering::LAKBO;
      }
    } else {
      _termOrdering.actualValue = Options::TermOrdering::KBO;
    }
  }

  if (unificationWithAbstraction() == Options::UnificationWithAbstraction::AUTO) {
    if (alasca() && prb.hasAlascaArithmetic() &&
      !partialRedundancyCheck()) { // TODO: Marton is planning a PR that will remove this constraint
      setUWA(Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR);
    } else if (prb.isHigherOrder()) {
      setUWA(Options::UnificationWithAbstraction::HOL);
      setUWAFPI(true);
    } else {
      setUWA(Options::UnificationWithAbstraction::OFF);
    }
  }
}

/**
 * True if the options are complete.
 * @since 23/07/2011 Manchester
 */
bool Options::complete(const Problem& prb) const
{
  if(prb.isHigherOrder()){
    //safer for competition
    return false;
  }

  if (unificationWithAbstraction() != UnificationWithAbstraction::OFF) {
    // unification with abstraction might cause in "spurious saturations"
    return false;
  }

  if (_showInterpolant.actualValue != InterpolantMode::OFF) {
    return false;
  }

  //we did some transformation that made us lose completeness
  //(e.g. equality proxy replacing equality for reflexive predicate)
  if (prb.hadIncompleteTransformation()) {
    return false;
  }

  if (prb.hasFOOL() && _casesSimp.actualValue) {
    // casesSimp is not complete 
    return false;
  }

  Property& prop = *prb.getProperty();

  // general properties causing incompleteness
  if (prop.hasInterpretedOperations()
      || prop.hasProp(Property::PR_HAS_INTEGERS)
      || prop.hasProp(Property::PR_HAS_REALS)
      || prop.hasProp(Property::PR_HAS_RATS)
      || prop.hasProp(Property::PR_HAS_ARRAYS)
      || (!prop.onlyFiniteDomainDatatypes() && prop.hasProp(Property::PR_HAS_DT_CONSTRUCTORS))
      || (!prop.onlyFiniteDomainDatatypes() && prop.hasProp(Property::PR_HAS_CDT_CONSTRUCTORS))
      || prop.hasAnswerLiteral()) {
    return false;
  }

  // preprocessing
  if (env.signature->hasDistinctGroups()) {
    return false;
  }

  // preprocessing for resolution-based algorithms
  if (_sos.actualValue != Sos::OFF) return false;
  // run-time rule causing incompleteness
  if (_forwardLiteralRewriting.actualValue) return false;

  bool unitEquality = prop.category() == Property::UEQ;
  bool hasEquality = (prop.equalityAtoms() != 0);

  if (hasEquality && !_superposition.actualValue) return false;

  //TODO update once we have another method of dealing with bools
  if (prop.hasLogicalProxy() || prop.hasBoolVar()) {
    return false;
  }

  if (!unitEquality) {
    if (_selection.actualValue <= -1000 || _selection.actualValue >= 1000) return false;
    if (_literalComparisonMode.actualValue == LiteralComparisonMode::REVERSE) return false;
  }

  if (!hasEquality) {
    if (_binaryResolution.actualValue) return true;
    // binary resolution is off
    if (_unitResultingResolution.actualValue!=URResolution::FULL &&
       (_unitResultingResolution.actualValue!=URResolution::ON || _splitting.actualValue) ) return false;
    return prop.category() == Property::HNE; // enough URR is complete for Horn problems
  }

  if (_demodulationRedundancyCheck.actualValue == DemodulationRedundancyCheck::OFF) {
    return false;
  }

  if (!_superpositionFromVariables.actualValue) {
    return false;
  }

  // only checking resolution rules remain
  bool pureEquality = (prop.atoms() == prop.equalityAtoms());
  if (pureEquality) return true;
  return (_binaryResolution.actualValue); // MS: we are in the equality case, so URR cannot help here even for horn problems
} // Options::complete

/**
 * Check constraints necessary for options to make sense
 *
 * The function is called after all options are parsed.
 */
bool Options::checkGlobalOptionConstraints(bool fail_early)
{
  //Check forbidden options
  readOptionsString(_forbiddenOptions.actualValue,false);

  bool result = true;

  // Check recorded option constraints
  auto options = _lookup.values();
  while(options.hasNext()){
    result = options.next()->checkConstraints() && result;
    if(fail_early && !result) return result;
  }

  return result;
}

template <typename T>
bool OptionValue<T>::checkConstraints()
{
  typename Lib::Stack<OptionValueConstraintUP<T>>::RefIterator it(_constraints);
  while (it.hasNext()) {
    const OptionValueConstraintUP<T> &con = it.next();
    if (!con->check(*this)) {

      if (env.options->mode() == Options::Mode::SPIDER) {
        reportSpiderFail();
        USER_ERROR("\nBroken Constraint: " + con->msg(*this));
      }

      if (con->hard) {
        USER_ERROR("\nBroken Constraint: " + con->msg(*this));
      }
      switch (env.options->getBadOptionChoice()) {
      case Options::BadOption::HARD:
        USER_ERROR("\nBroken Constraint: " + con->msg(*this));
      case Options::BadOption::SOFT:
        addCommentSignForSZS(cout);
        cout << "WARNING Broken Constraint: " + con->msg(*this) << endl;
        return false;
      case Options::BadOption::FORCED:
        if (con->force(this)) {
          cout << "Forced constraint " + con->msg(*this) << endl;
          break;
        }
        else {
          USER_ERROR("\nCould not force Constraint: " + con->msg(*this));
        }
      case Options::BadOption::OFF:
        return false;
      default:
        ASSERTION_VIOLATION;
      }
    }
  }
  return true;
}

/**
 * Check whether the option values make sense with respect to the given problem
 *
 * This check should be done at least twice; before preprocessing and after.
 * With before_preprocessing on, only options tagged as PREPROCESSING are queried
 * With before_preprocessing off, it's all the remaining ones.
 *
 **/
bool Options::checkProblemOptionConstraints(Property* prop, bool before_preprocessing, bool fail_early)
{
  bool result = true;

  auto options = _lookup.values();
  while(options.hasNext()){
    AbstractOptionValue* opt = options.next();

    bool tagIsPreprocessing = opt->tag == OptionTag::PREPROCESSING;
    if (before_preprocessing != tagIsPreprocessing) {
      continue;
    }

    result = opt->checkProblemConstraints(prop) && result;
    if(fail_early && !result) return result;
  }

  return result;
}

template<class A>
std::vector<A> parseCommaSeparatedList(std::string const& str)
{
  std::stringstream stream(str);
  std::vector<A> parsed;
  std::string cur;
  while (std::getline(stream, cur, ',')) {
    parsed.push_back(StringUtils::parse<A>(cur));
  }
  return parsed;
}

std::vector<int> Options::theorySplitQueueRatios() const
{
  auto inputRatios = parseCommaSeparatedList<int>(_theorySplitQueueRatios.actualValue);

  // sanity checks
  if (inputRatios.size() < 2) {
    USER_ERROR("Wrong usage of option '-thsqr'. Needs to have at least two values (e.g. '10,1')");
  }
  for (unsigned i = 0; i < inputRatios.size(); i++) {
    if(inputRatios[i] <= 0) {
      USER_ERROR("Wrong usage of option '-thsqr'. Each ratio needs to be a positive integer");
    }
  }

  return inputRatios;
}

std::vector<float> Options::theorySplitQueueCutoffs() const
{
  // initialize cutoffs
  std::vector<float> cutoffs;

  /*
  if (_theorySplitQueueCutoffs.isDefault()) {
    // if no custom cutoffs are set, use heuristics: (0,4*d,10*d,infinity)
    auto d = _theorySplitQueueExpectedRatioDenom.actualValue;
    cutoffs.push_back(0.0f);
    cutoffs.push_back(4.0f * d);
    cutoffs.push_back(10.0f * d);
    cutoffs.push_back(std::numeric_limits<float>::max());
  } else */
  {
    // if custom cutoffs are set, parse them and add float-max as last value
    cutoffs = parseCommaSeparatedList<float>(_theorySplitQueueCutoffs.actualValue);
    cutoffs.push_back(std::numeric_limits<float>::max());
  }

  // sanity checks
  for (unsigned i = 0; i < cutoffs.size(); i++)
  {
    auto cutoff = cutoffs[i];

    if (i > 0 && cutoff <= cutoffs[i-1])
    {
      USER_ERROR("Wrong usage of option '-thsqc'. The cutoff values must be strictly increasing");
    }
  }

  return cutoffs;
}

std::vector<int> Options::avatarSplitQueueRatios() const
{
  std::vector<int> inputRatios = parseCommaSeparatedList<int>(_avatarSplitQueueRatios.actualValue);

  // sanity checks
  if (inputRatios.size() < 2) {
    USER_ERROR("Wrong usage of option '-avsqr'. Needs to have at least two values (e.g. '10,1')");
  }
  for (unsigned i = 0; i < inputRatios.size(); i++) {
    if(inputRatios[i] <= 0) {
      USER_ERROR("Each ratio (supplied by option '-avsqr') needs to be a positive integer");
    }
  }

  return inputRatios;
}

std::vector<float> Options::avatarSplitQueueCutoffs() const
{
  // initialize cutoffs and add float-max as last value
  auto cutoffs = parseCommaSeparatedList<float>(_avatarSplitQueueCutoffs.actualValue);
  cutoffs.push_back(std::numeric_limits<float>::max());

  // sanity checks
  for (unsigned i = 0; i < cutoffs.size(); i++)
  {
    auto cutoff = cutoffs[i];

    if (i > 0 && cutoff <= cutoffs[i-1])
    {
      USER_ERROR("The cutoff values (supplied by option '-avsqc') must be strictly increasing");
    }
  }

  return cutoffs;
}

std::vector<int> Options::sineLevelSplitQueueRatios() const
{
  auto inputRatios = parseCommaSeparatedList<int>(_sineLevelSplitQueueRatios.actualValue);

  // sanity checks
  if (inputRatios.size() < 2) {
    USER_ERROR("Wrong usage of option '-slsqr'. Needs to have at least two values (e.g. '1,3')");
  }
  for (unsigned i = 0; i < inputRatios.size(); i++) {
    if(inputRatios[i] <= 0) {
      USER_ERROR("Each ratio (supplied by option '-slsqr') needs to be a positive integer");
    }
  }

  return inputRatios;
}

std::vector<float> Options::sineLevelSplitQueueCutoffs() const
{
  // initialize cutoffs and add float-max as last value
  auto cutoffs = parseCommaSeparatedList<float>(_sineLevelSplitQueueCutoffs.actualValue);
  cutoffs.push_back(std::numeric_limits<float>::max());

  // sanity checks
  for (unsigned i = 0; i < cutoffs.size(); i++)
  {
    auto cutoff = cutoffs[i];

    if (i > 0 && cutoff <= cutoffs[i-1])
    {
      USER_ERROR("The cutoff values (supplied by option '-slsqc') must be strictly increasing");
    }
  }

  return cutoffs;
}

std::vector<int> Options::positiveLiteralSplitQueueRatios() const
{
  auto inputRatios = parseCommaSeparatedList<int>(_positiveLiteralSplitQueueRatios.actualValue);

  // sanity checks
  if (inputRatios.size() < 2) {
    USER_ERROR("Wrong usage of option '-plsqr'. Needs to have at least two values (e.g. '1,3')");
  }
  for (unsigned i = 0; i < inputRatios.size(); i++) {
    if(inputRatios[i] <= 0) {
      USER_ERROR("Each ratio (supplied by option '-plsqr') needs to be a positive integer");
    }
  }

  return inputRatios;
}

std::vector<float> Options::positiveLiteralSplitQueueCutoffs() const
{
  // initialize cutoffs and add float-max as last value
  auto cutoffs = parseCommaSeparatedList<float>(_positiveLiteralSplitQueueCutoffs.actualValue);
  cutoffs.push_back(std::numeric_limits<float>::max());

  // sanity checks
  for (unsigned i = 0; i < cutoffs.size(); i++)
  {
    auto cutoff = cutoffs[i];

    if (i > 0 && cutoff <= cutoffs[i-1])
    {
      USER_ERROR("The cutoff values (supplied by option '-plsqc') must be strictly increasing");
    }
  }

  return cutoffs;
}

vector<int> Options::hoSplitQueueRatios() const
{
  auto inputRatios = parseCommaSeparatedList<int>(_hoSplitQueueRatios.actualValue);

  // sanity checks
  if (inputRatios.size() < 2) {
    USER_ERROR("Wrong usage of option '-hfsqr'. Needs to have at least two values (e.g. '10,1')");
  }
  for (const auto& r : inputRatios) {
    if (r <= 0) {
      USER_ERROR("Each ratio (supplied by option '-hfsqr') needs to be a positive integer");
    }
  }

  return inputRatios;
}

vector<float> Options::hoSplitQueueCutoffs() const
{
  // initialize cutoffs and add float-max as last value
  auto cutoffs = parseCommaSeparatedList<float>(_hoSplitQueueCutoffs.actualValue);
  cutoffs.push_back(std::numeric_limits<float>::max());

  // sanity checks
  for (unsigned i = 0; i < cutoffs.size(); i++) {
    auto cutoff = cutoffs[i];
    if (i > 0 && cutoff <= cutoffs[i-1]) {
      USER_ERROR("The cutoff values (supplied by option '-hfsqc') must be strictly increasing");
    }
  }
  return cutoffs;
}

Stack<const char *> Options::getSimilarOptionNames(const char *name, bool is_short) const {
  Stack<const char *> similar_names;

  auto options = _lookup.values();
  while(options.hasNext()){
    AbstractOptionValue* opt = options.next();
    auto opt_name = is_short ? opt->shortName : opt->longName;
    size_t dif = 2;
    size_t len = strlen(name);
    if(!is_short) dif += len/4;
    if(len!=0 && StringUtils::distance(name,opt_name) < dif)
      similar_names.push(opt_name);
  }

  return similar_names;
}

AbstractOptionValue *Options::getOptionValueByName(const char *name) const
{
  AbstractOptionValue *result = _lookup.findLong(name);
  if(!result) result = _lookup.findShort(name);
  return result;
}

} // namespace Shell
