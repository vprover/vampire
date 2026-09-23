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
    return (p->category()!=Property::PEQ && p->category()!=Property::UEQ);
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

AbstractOptionValue::AbstractOptionValue(const char *l, Options* owner, OptionMeta meta)
  : longName(l), shortName(meta.short_name),
    description(meta.description), experimental(meta.experimental), tag(meta.tag)
{
  owner->_lookup.insert(*this);
}

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
  : _decode("decode",this,
      {.description="Decodes an encoded strategy. Can be used to replay a strategy. To make Vampire output an encoded version of the strategy use the encode option.",
       .tag = OptionTag::DEVELOPMENT})
  , _encode("encode",this,false,
      {.description = "Output an encoding of the strategy to be used with the decode option",
       .tag = OptionTag::DEVELOPMENT})
  , _ageWeightRatio("age_weight_ratio",this,{1,1},':',
      {.short_name = "awr",
       .description = "Ratio in which clauses are being selected for activation i.e. A:W means that for every A clauses selected based on age "
    "there will be W selected based on weight. (At most one of A and W can be zero, which means that that queue won't be used at all.)",
       .tag = OptionTag::SATURATION})
  , _useTheorySplitQueues("theory_split_queue",this,false,
      {.short_name = "thsq",
       .description = "Turn on clause selection using multiple queues containing different clauses (split by amount of theory reasoning)",
       .tag = OptionTag::SATURATION})
  , _theorySplitQueueRatios("theory_split_queue_ratios",this, "1,1",
      {.short_name = "thsqr",
       .description = "The ratios for picking clauses from the split-queues using weighted round robin. If a queue is empty, the clause will be picked from the next non-empty queue to the right. Note that this option implicitly also sets the number of queues.",
       .tag = OptionTag::SATURATION})
  , _theorySplitQueueCutoffs("theory_split_queue_cutoffs",this, "0",
      {.short_name = "thsqc",
       .description = "The cutoff-values for the split-queues (the cutoff value for the last queue has to be omitted, as it is always infinity). Any split-queue contains all clauses which are assigned a feature-value less or equal to the cutoff-value of the queue. If no custom value for this option is set, the implementation will use cutoffs 0,4*d,10*d,infinity (where d denotes the theory split queue expected ratio denominator).",
       .tag = OptionTag::SATURATION})
  , _theorySplitQueueExpectedRatioDenom("theory_split_queue_expected_ratio_denom",this, 8,
      {.short_name = "thsqd",
       .description = "The denominator n such that we expect the final proof to have a ratio of theory-axioms to all-axioms of 1/n.",
       .tag = OptionTag::SATURATION})
  , _theorySplitQueueLayeredArrangement("theory_split_queue_layered_arrangement",this,true,
      {.short_name = "thsql",
       .description = "If turned on, use a layered arrangement to split clauses into queues. Otherwise use a tammet-style-arrangement.",
       .tag = OptionTag::SATURATION})
  , _useAvatarSplitQueues("avatar_split_queue",this,false,
      {.short_name = "avsq",
       .description = "Turn on experiments: clause selection with multiple queues containing different clauses (split by amount of avatar-split-set-size)",
       .tag = OptionTag::AVATAR})
  , _avatarSplitQueueRatios("avatar_split_queue_ratios",this, "1,1",
      {.short_name = "avsqr",
       .description = "The ratios for picking clauses from the split-queues using weighted round robin. If a queue is empty, the clause will be picked from the next non-empty queue to the right. Note that this option implicitly also sets the number of queues.",
       .tag = OptionTag::AVATAR})
  , _avatarSplitQueueCutoffs("avatar_split_queue_cutoffs",this, "0",
      {.short_name = "avsqc",
       .description = "The cutoff-values for the avatar-split-queues (the cutoff value for the last queue is omitted, since it has to be infinity).",
       .tag = OptionTag::AVATAR})
  , _avatarSplitQueueLayeredArrangement("avatar_split_queue_layered_arrangement",this,false,
      {.short_name = "avsql",
       .description = "If turned on, use a layered arrangement to split clauses into queues. Otherwise use a tammet-style-arrangement.",
       .tag = OptionTag::AVATAR})
  , _useSineLevelSplitQueues("sine_level_split_queue",this,false,
      {.short_name = "slsq",
       .description = "Turn on experiments: clause selection with multiple queues containing different clauses (split by sine-level of clause)",
       .tag = OptionTag::SATURATION})
  , _sineLevelSplitQueueRatios("sine_level_split_queue_ratios",this, "1,1",
      {.short_name = "slsqr",
       .description = "The ratios for picking clauses from the sine-level-split-queues using weighted round robin. If a queue is empty, the clause will be picked from the next non-empty queue to the right. Note that this option implicitly also sets the number of queues.",
       .tag = OptionTag::SATURATION})
  , _sineLevelSplitQueueCutoffs("sine_level_split_queue_cutoffs",this, "0",
      {.short_name = "slsqc",
       .description = "The cutoff-values for the sine-level-split-queues (the cutoff value for the last queue is omitted, since it has to be infinity).",
       .tag = OptionTag::SATURATION})
  , _sineLevelSplitQueueLayeredArrangement("sine_level_split_queue_layered_arrangement",this,true,
      {.short_name = "slsql",
       .description = "If turned on, use a layered arrangement to split clauses into queues. Otherwise use a tammet-style-arrangement.",
       .tag = OptionTag::SATURATION})
  , _usePositiveLiteralSplitQueues("positive_literal_split_queue",this,false,
      {.short_name = "plsq",
       .description = "Turn on experiments: clause selection with multiple queues containing different clauses (split by number of positive literals in clause)",
       .tag = OptionTag::SATURATION})
  , _positiveLiteralSplitQueueRatios("positive_literal_split_queue_ratios",this, "1,4",
      {.short_name = "plsqr",
       .description = "The ratios for picking clauses from the positive-literal-split-queues using weighted round robin. If a queue is empty, the clause will be picked from the next non-empty queue to the right. Note that this option implicitly also sets the number of queues.",
       .tag = OptionTag::SATURATION})
  , _positiveLiteralSplitQueueCutoffs("positive_literal_split_queue_cutoffs",this, "0",
      {.short_name = "plsqc",
       .description = "The cutoff-values for the positive-literal-split-queues (the cutoff value for the last queue is omitted, since it has to be infinity).",
       .tag = OptionTag::SATURATION})
  , _positiveLiteralSplitQueueLayeredArrangement("positive_literal_split_queue_layered_arrangement",this,false,
      {.short_name = "plsql",
       .description = "If turned on, use a layered arrangement to split clauses into queues. Otherwise use a tammet-style-arrangement.",
       .tag = OptionTag::SATURATION})
  , _hoSplitQueues("ho_split_queue",this,false,
      {.short_name = "hsq",
       .description = "Turn on clause selection using multiple queues containing different clauses (split by amount of higher-order featues)",
       .tag = OptionTag::SATURATION})
  , _hoSplitQueueLambdaWeight("ho_split_queue_lambda_weight",this,1,
      {.short_name = "hsqlw",
       .description = "How much should lambda occurrences count in the HO features",
       .tag = OptionTag::SATURATION})
  , _hoSplitQueueAppVarWeight("ho_split_queue_appvar_weight",this,1,
      {.short_name = "hsqaw",
       .description = "How much should app-var occurrences count in the HO features",
       .tag = OptionTag::SATURATION})
  , _hoSplitQueueRatios("ho_split_queue_ratios",this, "1,1",
      {.short_name = "hsqr",
       .description = "The ratios for picking clauses from the split-queues using weighted round robin. If a queue is empty, the clause will be picked from the next non-empty queue to the right. Note that this option implicitly also sets the number of queues.",
       .tag = OptionTag::AVATAR})
  , _hoSplitQueueCutoffs("ho_split_queue_cutoffs",this, "0",
      {.short_name = "hsqc",
       .description = "The cutoff-values for the split-queues (the cutoff value for the last queue has to be omitted, as it is always infinity). Any split-queue contains all clauses which are assigned a feature-value less or equal to the cutoff-value of the queue. If no custom value for this option is set, the implementation will use cutoffs 0,4*d,10*d,infinity (where d denotes the theory split queue expected ratio denominator).",
       .tag = OptionTag::SATURATION})
  , _hoSplitQueueLayeredArrangement("ho_split_queue_layered_arrangement",this,true,
      {.short_name = "hsql",
       .description = "If turned on, use a layered arrangement to split clauses into queues. Otherwise use a tammet-style-arrangement.",
       .tag = OptionTag::SATURATION})
  , _randomAWR("random_awr",this,false,
      {.short_name = "rawr",
       .description = "Respecting age_weight_ratio, always choose the next clause selection queue probabilistically (rather than deterministically).",
       .tag = OptionTag::SATURATION,
       .experimental = true})
  , _literalMaximalityAftercheck("literal_maximality_aftercheck",this,true,
      {.short_name = "lma",
       .description = "Allows to disable a secondary (literal maximality) ordering check (in the superposition calculus) after a substitution is applied."
                                   " The check costs something but sometimes helps to skip some generating inferences",
       .tag = OptionTag::SATURATION})
  , _arityCheck("arity_check",this,false,
      {.description = "Enforce the condition that the same symbol name cannot be used with multiple arities."
       "This also ensures a symbol is not used as a function and predicate.",
       .tag = OptionTag::DEVELOPMENT})
  , _parseGoalAnnotations("parse_goal_annotations",this,true,
      {.description = "Enable parsing :goal annotations in smtlib problems."
       "They can be used like this: (assert (! <formula> :goal <goal-name>))",
       .tag = OptionTag::INPUT})
  , _randomTraversals("random_traversals",this,false,
      {.short_name = "rtra",
       .tag = OptionTag::SATURATION,
       .experimental = true})
  , _badOption("bad_option",this,BadOption::SOFT,{"hard","forced","off","soft"},
      {.description = "What should be done if a bad option value (wrt hard and soft constraints) is encountered:\n"
       " - hard: will cause a user error\n"
       " - soft: will only report the error (unless it is unsafe)\n"
       " - forced: <under development> \n"
       " - off: will ignore safe errors\n"
       "Note that unsafe errors will always lead to a user error",
       .tag = OptionTag::HELP})
  , _backwardDemodulation("backward_demodulation",this,
                  Demodulation::OFF,
                  {"all","off","preordered"},
      {.short_name = "bd",
       .description = "Oriented rewriting of kept clauses by newly derived unit equalities\n"
       "s = t     L[sθ] \\/ C\n"
       "---------------------   where sθ > tθ (replaces RHS)\n"
       " L[tθ] \\/ C\n",
       .tag = OptionTag::INFERENCES})
  , _backwardSubsumption("backward_subsumption",this,
                Subsumption::OFF,{"off","on","unit_only"},
      {.short_name = "bs",
       .description = "Perform subsumption deletion of kept clauses by newly derived clauses. Unit_only means that the subsumption will be performed only by unit clauses",
       .tag = OptionTag::INFERENCES})
  , _backwardSubsumptionResolution("backward_subsumption_resolution",this,
                    Subsumption::OFF,{"off","on","unit_only"},
      {.short_name = "bsr",
       .description = "Perform subsumption resolution on kept clauses using newly derived clauses. Unit_only means that the subsumption resolution will be performed only by unit clauses",
       .tag = OptionTag::INFERENCES})
  , _backwardSubsumptionDemodulation("backward_subsumption_demodulation",this, false,
      {.short_name = "bsd",
       .description = "Perform backward subsumption demodulation.",
       .tag = OptionTag::INFERENCES})
  , _backwardSubsumptionDemodulationMaxMatches("backward_subsumption_demodulation_max_matches",this, 0,
      {.short_name = "bsdmm",
       .description = "Maximum number of multi-literal matches to consider in backward subsumption demodulation. 0 means to try all matches (until first success).",
       .tag = OptionTag::INFERENCES})
  , _binaryResolution("binary_resolution",this,true,
      {.short_name = "br",
       .description = "Standard binary resolution i.e.\n"
        "C \\/ t     D \\/ s\n"
        "---------------------\n"
        "(C \\/ D)θ\n"
        "where θ = mgu(t,-s) and t selected",
       .tag = OptionTag::INFERENCES})
  , _superposition("superposition",this,true,
      {.short_name = "sup",
       .description = "Control superposition. Turning off this core inference leads to an incomplete calculus on equational problems.",
       .tag = OptionTag::INFERENCES})
  , _condensation("condensation",this,Condensation::OFF,{"fast","off","on"},
      {.short_name = "cond",
       .description = "Perform condensation. If 'fast' is specified, we only perform condensations that are easy to check for.",
       .tag = OptionTag::INFERENCES})
  , _demodulationRedundancyCheck("demodulation_redundancy_check",this,
       DemodulationRedundancyCheck::ENCOMPASS,{"off","ordering","encompass"},
      {.short_name = "drc",
       .description = "The following cases of backward and forward demodulation do not preserve completeness:\n"
       "s = t     s = t1 \\/ C \t s = t     s != t1 \\/ C\n"

       "--------------------- \t ---------------------\n"
       "t = t1 \\/ C \t\t t != t1 \\/ C\n"
       "where t > t1 and s = t > C (RHS replaced)\n"
       "With `encompass`, we treat demodulations (both forward and backward) as encompassment demodulations (as defined by Duarte and Korovin in 2022's IJCAR paper).\n"
       "With `ordering`, we check this condition and don't demodulate if we could violate completeness.\n"
       "With `off`, we skip the checks, save time, but become incomplete.",
       .tag = OptionTag::INFERENCES})
  , _forwardDemodulationTermOrderingDiagrams("forward_demodulation_term_ordering_diagrams",this,true,
      {.short_name = "fdtod",
       .description = "Use term ordering diagrams (TODs) to runtime specialize post-ordering checks in forward demodulation.",
       .tag = OptionTag::INFERENCES})
  , _demodulationOnlyEquational("demodulation_only_equational",this,false,
      {.short_name = "doe",
       .description = "Disables demodulation of non-equational literals. In combination with -ins > 0 simulates the effect of Waldmeister's `Enlarging the Hypothesis` trick.",
       .tag = OptionTag::INFERENCES,
       .experimental = true})
  , _equalityProxy( "equality_proxy",this,EqualityProxy::OFF,{"R","RS","RST","RSTC","off"},
      {.short_name = "ep",
       .description = "Applies the equality proxy transformation to the problem. It works as follows:\n"
     " - All literals s=t are replaced by E(s,t)\n"
     " - All literals s!=t are replaced by ~E(s,t)\n"
     " - If S the symmetry clause ~E(x,y) \\/ E(y,x) is added\n"
     " - If T the transitivity clause ~E(x,y) \\/ ~E(y,z) \\/ E(x,z) is added\n"
     " - If C the congruence clauses are added as follows:\n"
     "    for predicates p that are not E or equality add\n"
     "     ~E(x1,y1) \\/ ... \\/ ~E(xN,yN) \\/ ~p(x1,...,xN) \\/ p(y1,...,yN)\n"
     "    for non-constant functions f add\n"
     "     ~E(x1,y1) \\/ ... \\/ ~E(xN,yN) \\/ E(f(x1,...,xN),f(y1,...,yN))\n"
     " R stands for reflexivity.\n"
     " E is a single polymorphic predicate for a polymorphic problem and one predicate"
     " per sort for a monomorphic one",
       .tag = OptionTag::PREPROCESSING})
  , _equalityResolutionWithDeletion("equality_resolution_with_deletion",this,true,
      {.short_name = "erd",
       .description = "Perform equality resolution with deletion.",
       .tag = OptionTag::PREPROCESSING})
  , _extensionalityResolution("extensionality_resolution",this,
                      ExtensionalityResolution::OFF,{"filter","known","tagged","off"},
      {.short_name = "er",
       .description = "Turns on the following inference rule:\n"
      "  x=y \\/ C    s != t \\/ D\n"
      "  -----------------------\n"
      "  C{x → s, y → t} \\/ D\n"
      "Where s!=t is selected in s!=t \\/D and x=y \\/ C is a recognised as an extensionality clause - how clauses are recognised depends on the value of this option.\n"
      "If filter we attempt to recognise all extensionality clauses i.e. those that have exactly one X=Y, no inequality of the same sort as X-Y (and optionally no equality except X=Y, see extensionality_allow_pos_eq).\n"
      "If known we only recognise a known set of extensionality clauses. At the moment this includes the standard and subset-based formulations of the set extensionality axiom, as well as the array extensionality axiom.\n"
      "If tagged we only use formulas tagged as extensionality clauses.",
       .tag = OptionTag::INFERENCES})
  , _extensionalityMaxLength("extensionality_max_length",this,0,
      {.short_name = "erml",
       .description = "Sets the maximum length (number of literals) an extensionality"
      " clause can have when doing recognition for extensionality resolution. If zero there is no maximum.",
       .tag = OptionTag::INFERENCES})
  , _extensionalityAllowPosEq( "extensionality_allow_pos_eq",this,true,
      {.short_name = "eape",
       .description = "If extensionality resolution equals filter, this dictates"
      " whether we allow other positive equalities when recognising extensionality clauses",
       .tag = OptionTag::INFERENCES})
  , _FOOLParamodulation("fool_paramodulation",this,false,
      {.short_name = "foolp",
       .description = "Turns on the following inference rule:\n"
      "        C[s]\n"
      "--------------------,\n"
      "C[true] \\/ s = false\n"
      "where s is a boolean term that is not a variable, true or false, C[true] is "
      "the C clause with s substituted by true. This rule is needed for efficient "
      "treatment of boolean terms.",
       .tag = OptionTag::INFERENCES})
  , _termAlgebraInferences("term_algebra_rules",this,true,
      {.short_name = "tar",
       .description = "Activates some rules that improve reasoning with term algebras (such as algebraic datatypes in SMT-LIB):\n"
      "If the problem does not contain any term algebra symbols, activating this options has no effect\n"
      "- distinctness rule:\n"
      "f(...) = g(...) \\/ A\n"
      "--------------------\n"
      "          A         \n"
      "where f and g are distinct term algebra constructors\n"
      "- distinctness tautology deletion: clauses of the form f(...) ~= g(...) \\/ A are deleted\n"
      "- injectivity rule:\n"
      "f(s1 ... sn) = f(t1 ... tn) \\/ A\n"
      "--------------------------------\n"
      "         s1 = t1 \\/ A\n"
      "               ...\n"
      "         sn = tn \\/ A",
       .tag = OptionTag::THEORIES})
  , _termAlgebraCyclicityCheck("term_algebra_acyclicity",this,
                                                                     TACyclicityCheck::OFF,{"off","axiom","rule","light"},
      {.short_name = "tac",
       .description = "Activates the cyclicity rule for term algebras (such as algebraic datatypes in SMT-LIB):\n"
      "- off : the cyclicity rule is not enforced (this is sound but incomplete)\n"
      "- axiom : the cyclicity rule is axiomatized with a transitive predicate describing the subterm relation over terms\n"
      "- rule : the cyclicity rule is enforced by a specific hyper-resolution rule\n"
      "- light : the cyclicity rule is enforced by rule generating disequality between a term and its known subterms",
       .tag = OptionTag::THEORIES})
  , _termAlgebraExhaustivenessAxiom("term_algebra_exhaustiveness_axiom",this,true,
      {.short_name = "taea",
       .description = "Enable term algebra exhaustiveness axiom",
       .tag = OptionTag::THEORIES})
  , _fmbStartSize("fmb_start_size",this,1,
      {.short_name = "fmbss",
       .description = "Set the initial model size for finite model building",
       .tag = OptionTag::FMB})
  , _fmbSymmetryRatio("fmb_symmetry_ratio",this,1.0,
      {.short_name = "fmbsr",
       .description = "Usually we use at most n principal terms for symmetry avoidance where n is the current model size. This option allows us to supply a multiplier for that n. See Symmetry Avoidance in MACE-Style Finite Model Finding.",
       .tag = OptionTag::FMB})
  , _fmbSymmetryOrderSymbols("fmb_symmetry_symbol_order",this,
                                                     FMBSymbolOrders::OCCURRENCE,
                                                     {"occurrence","usage"},
      {.short_name = "fmbsso",
       .description = "The order of symbols considered for symmetry avoidance: either as they come in the signature, or by how often they occur in the clauses finite model building has preprocessed. See Symmetry Avoidance in MACE-Style Finite Model Finding.",
       .tag = OptionTag::FMB})
  , _fmbAdjustSorts("fmb_adjust_sorts",this,
                                                           FMBAdjustSorts::GROUP,
                                                           {"off","expand","group","predicate","function"},
      {.short_name = "fmbas",
       .description = "Detect monotonic sorts. If <expand> then expand monotonic subsorts into proper sorts. If <group> then collapse monotonic sorts into a single sort. If <predicate> then introduce sort predicates for non-monotonic sorts and collapse all sorts into one. If <function> then introduce sort functions for non-monotonic sorts and collapse all sorts into one",
       .tag = OptionTag::FMB})
  , _fmbDetectSortBounds("fmb_detect_sort_bounds",this,false,
      {.short_name = "fmbdsb",
       .description = "Use a saturation loop to detect sort bounds introduced by (for example) injective functions",
       .tag = OptionTag::FMB})
  , _fmbDetectSortBoundsTimeLimit("fmb_detect_sort_bounds_time_limit",this,10,
      {.short_name = "fmbdsbt",
       .description = "The time limit for performing sort bound detection",
       .tag = OptionTag::FMB})
  , _fmbSizeWeightRatio("fmb_size_weight_ratio",this,1,
      {.short_name = "fmbswr",
       .description = "Controls the priority the next sort size vector is given based on a ratio. 0 is size only, 1 means 1:1, 2 means 1:2, etc.",
       .tag = OptionTag::FMB})
  , _fmbEnumerationStrategy("fmb_enumeration_strategy",this,FMBEnumerationStrategy::SBMEAM,{"sbeam",
#if VZ3
        "smt",
#endif
        "contour"},
      {.short_name = "fmbes",
       .description = "How model sizes assignments are enumerated in the multi-sorted setting. (Only smt and contour are known to be finite model complete and can therefore return UNSAT.)",
       .tag = OptionTag::FMB})
  , _fmbKeepSbeamGenerators("fmb_keep_sbeam_generators",this,false,
      {.short_name = "fmbksg",
       .description = "A modification of the sbeam enumeration strategy which (for a performance price) makes it more enumeration-complete.",
       .tag = OptionTag::FMB})
  , _fmbUseSimplifyingSolver("fmb_use_simplifying_solver",this,true,
      {.short_name = "fmbuss",
       .description = "Allow the SAT solver to internally simplify the instance.",
       .tag = OptionTag::FMB})
  , _forbiddenOptions("forbidden_options",this,"",
      {.description = "If some of the specified options are set to a forbidden state, vampire will fail to start, or in portfolio modes it will skip such strategies. The expected syntax is <opt1>=<val1>:<opt2>:<val2>:...:<optn>=<valN>",
       .tag = OptionTag::INPUT})
  , _forcedOptions("forced_options",this,"",
      {.description = "Options in the format <opt1>=<val1>:<opt2>=<val2>:...:<optn>=<valN> that override the option values set by other means (also inside portfolio mode strategies)",
       .tag = OptionTag::INPUT})
  , _forwardDemodulation("forward_demodulation",this,Demodulation::ALL,{"all","off","preordered"},
      {.short_name = "fd",
       .description = "Oriented rewriting of newly derived clauses by kept unit equalities\n"
    "s = t     L[sθ] \\/ C\n"
    "---------------------  where sθ > tθ\n"
    " L[tθ] \\/ C\n"
    "If 'preordered' is set, only equalities s = t where s > t are used for rewriting.",
       .tag = OptionTag::INFERENCES})
  , _forwardGroundJoinability("forward_ground_joinability",this,false,
      {.short_name = "fgj",
       .description = "Perform forward ground joinability.",
       .tag = OptionTag::INFERENCES})
  , _forwardLiteralRewriting("forward_literal_rewriting",this,false,
      {.short_name = "flr",
       .description = "Perform forward literal rewriting.",
       .tag = OptionTag::INFERENCES})
  , _forwardSubsumption("forward_subsumption",this,true,
      {.short_name = "fs",
       .description = "Perform forward subsumption deletion.",
       .tag = OptionTag::INFERENCES})
  , _forwardSubsumptionResolution("forward_subsumption_resolution",this,true,
      {.short_name = "fsr",
       .description = "Perform forward subsumption resolution.",
       .tag = OptionTag::INFERENCES})
  , _forwardSubsumptionDemodulation("forward_subsumption_demodulation",this, false,
      {.short_name = "fsd",
       .description = "Perform forward subsumption demodulation.",
       .tag = OptionTag::INFERENCES})
  , _forwardSubsumptionDemodulationMaxMatches("forward_subsumption_demodulation_max_matches",this, 0,
      {.short_name = "fsdmm",
       .description = "Maximum number of multi-literal matches to consider in forward subsumption demodulation. 0 means to try all matches (until first success).",
       .tag = OptionTag::INFERENCES})
  , _functionDefinitionElimination("function_definition_elimination",this,
                                                                                      FunctionDefinitionElimination::ALL,{"all","none","unused"},
      {.short_name = "fde",
       .description = "Attempts to eliminate function definitions. A function definition is a unit clause of the form f(x1,..,xn) = t where x1,..,xn are the pairwise distinct free variables of t and f does not appear in t."
        " If 'all', definitions are eliminated by replacing every occurrence of f(s1,..,sn) by t{x1 -> s1, .., xn -> sn}. If 'unused' only unused definitions are removed.",
       .tag = OptionTag::PREPROCESSING})
  , _functionDefinitionIntroduction(
      "function_definition_introduction",this,
      0,
      {.short_name = "fdi",
       .description = "If non-zero, introduces function definitions with generalisation for repeated compound terms in the active set. "
      "For example, if f(a, g(a)) and f(b, g(b)) occur frequently, we might define d(X) = f(X, g(X)). "
      "The parameter value 'n' is a threshold: terms that occur more than n times have a definition created.",
       .tag = OptionTag::INFERENCES}
    )
  , _tweeGoalTransformation("twee_goal_transformation",this, TweeGoalTransformation::OFF, {"off","ground","full"},
      {.short_name = "tgt",
       .description = "Add definitions for `ground` subterms in the conjecture, inspired by Twee. "
      "This adds a goal-directed flavour to equational reasoning. "
      "`full` is a generalization, where also non-ground subterms are considered.",
       .tag = OptionTag::PREPROCESSING,
       .experimental = true})
    // At least on higher-order TPTP, tgt with tsa=off sucks badly
    // TODO(HOL): investigate perhaps less invasive options of restraining
    // general tgt in HOL, that would still be performant
  , _tweeSkipArrows("twee_skip_arrows",this,true,
      {.short_name = "tsa",
       .description = "During twee_goal_transformation, when in HOL, don't introduce definitions for arrow-typed subterms.",
       .tag = OptionTag::PREPROCESSING,
       .experimental = true})
  , _codeTreeSubsumption("code_tree_subsumption",this, true,
      {.short_name = "cts",
       .description = "Use code tree implementation of forward subsumption and subsumption resolution.",
       .tag = OptionTag::INFERENCES,
       .experimental = true})
  , _generalSplitting("general_splitting",this,false,
      {.short_name = "gsp",
       .description = "Splits clauses in order to reduce number of different variables in each clause. "
    "A clause C[X] \\/ D[Y] with subclauses C and D over non-equal sets of variables X and Y can be split into S(Z) \\/ C[X] and ~S(Z) \\/ D[Y] where Z is the intersection of X and Y.",
       .tag = OptionTag::PREPROCESSING})
  , _globalSubsumption("global_subsumption",this,false,
      {.short_name = "gs",
       .description = "Perform global subsumption. Use a set of groundings of generated clauses G to replace C \\/ L by C if the grounding of C is implied by G. A SAT solver is used for ground reasoning.",
       .tag = OptionTag::INFERENCES})
  , _guessTheGoal("guess_the_goal",this,GoalGuess::OFF,{"off","all","exists_top","exists_all","exists_sym","position"},
      {.short_name = "gtg",
       .description = "Use heuristics to guess formulas that correspond to the goal. Doesn't "
                                "really make sense if there is already a goal but it will still do something. "
                                "This is really designed for use with SMTLIB problems that don't have goals",
       .tag = OptionTag::INPUT})
  , _guessTheGoalLimit("guess_the_goal_limit",this,1,
      {.short_name = "gtgl",
       .description = "The maximum number of input units a symbol appears for it to be considered in a goal",
       .tag = OptionTag::INPUT})
  , _simultaneousSuperposition("simultaneous_superposition",this,true,
      {.short_name = "sims",
       .description = "Rewrite the whole RHS clause during superposition, not just the target literal.",
       .tag = OptionTag::INFERENCES})
  , _innerRewriting("inner_rewriting",this,false,
      {.short_name = "irw",
       .description = "C[t_1] | t1 != t2 ==> C[t_2] | t1 != t2 when t1>t2",
       .tag = OptionTag::INFERENCES})
  , _equationalTautologyRemoval("equational_tautology_removal",this,false,
      {.short_name = "etr",
       .description = "A reduction which uses congruence closure to remove logically valid clauses.",
       .tag = OptionTag::INFERENCES})
  , _subsumptionEqualityResolution("subsumption_equality_resolution",this,false,
      {.short_name = "ser",
       .description = "Similar to subsumption resolution but uses the implicit x = x clause to resolve a literal.",
       .tag = OptionTag::INFERENCES})
  , _partialRedundancyCheck("partial_redundancy_check",this,false,
      {.short_name = "prc",
       .description = "Skip generating inferences on clause instances on which we already performed a simplifying inference.",
       .tag = OptionTag::INFERENCES})
  , _partialRedundancyOrderingConstraints("partial_redundancy_ordering_constraints",this,false,
      {.short_name = "proc",
       .description = "Strengthen partial redundancy with ordering constraints.",
       .tag = OptionTag::INFERENCES})
  , _partialRedundancyAvatarConstraints("partial_redundancy_avatar_constraints",this,false,
      {.short_name = "prac",
       .description = "Strengthen partial redundancy with AVATAR constraints.",
       .tag = OptionTag::INFERENCES})
  , _partialRedundancyLiteralConstraints("partial_redundancy_literal_constraints",this,false,
      {.short_name = "prlc",
       .description = "Strengthen partial redundancy with literals from clauses.",
       .tag = OptionTag::INFERENCES})
  , _ignoreMissing("ignore_missing",this,IgnoreMissing::OFF,{"on","off","warn"},
      {.description = "Ignore any options that have been removed (useful in portfolio modes where this can cause strategies to be skipped). If set to warn "
      "this will print a warning when ignoring. This is set to warn in CASC mode.",
       .tag = OptionTag::DEVELOPMENT})
  , _include("include",this,"",
      {.description = "Path prefix for the 'include' TPTP directive",
       .tag = OptionTag::INPUT})
  , _increasedNumeralWeight("increased_numeral_weight",this,false,
      {.short_name = "inw",
       .description = "This option only applies if the problem has interpreted numbers. The weight of integer constants depends on the logarithm of their absolute value (instead of being 1)",
       .tag = OptionTag::SATURATION})
  , _ignoreConjectureInPreprocessing("ignore_conjecture_in_preprocessing",this,false,
      {.short_name = "icip",
       .description = "Make sure we do not delete the conjecture in preprocessing even if it can be deleted.",
       .tag = OptionTag::PREPROCESSING})
  , _inequalitySplitting("inequality_splitting",this,0,
      {.short_name = "ins",
       .description = "When greater than zero, ins defines a weight threshold w such that any clause C \\/ s!=t "
    "where s (or conversely t) is ground and has weight greater or equal than w "
    "is replaced by C \\/ p(s) with the additional unit clause ~p(t) being added "
    "for fresh predicate p.",
       .tag = OptionTag::PREPROCESSING})
  , _inputSyntax("input_syntax",this,InputSyntax::AUTO,{"smtlib2","tptp","auto"},
      {.description = "Input syntax. Historic input syntaxes have been removed as they are not actively maintained. Contact developers for help with these.",
       .tag = OptionTag::INPUT})
  , _instantiation("instantiation",this,false,
      {.short_name = "inst",
       .description = "Heuristically instantiate variables. Often wastes a lot of effort. Consider using thi instead.",
       .tag = OptionTag::THEORIES})
  , _induction("induction",this,Induction::NONE,
                      {"none","struct","int","both"},
      {.short_name = "ind",
       .description = "Apply structural and/or integer induction on datatypes and integers.",
       .tag = OptionTag::INDUCTION})
  , _structInduction("structural_induction_kind",this,
                         StructuralInductionKind::ONE,{"one","two","three","recursion","all"},
      {.short_name = "sik",
       .description = "The kind of structural induction applied",
       .tag = OptionTag::INDUCTION})
  , _intInduction("int_induction_kind",this,
                         IntInductionKind::ONE,{"one","two","all"},
      {.short_name = "iik",
       .description = "The kind of integer induction applied",
       .tag = OptionTag::INDUCTION})
  , _inductionSkolemOnly("induction_skolem_only",this,false,
      {.short_name = "indso",
       .description = "Induct only on terms containing Skolems",
       .tag = OptionTag::INDUCTION})
  , _inductionGoalClausesOnly("induction_goal_clauses_only",this,false,
      {.short_name = "indgco",
       .description = "Induct only on clauses derived from the goal",
       .tag = OptionTag::INDUCTION})
  , _maxInductionDepth("induction_max_depth",this,0,
      {.short_name = "indmd",
       .description = "Set maximum depth of induction where 0 means no max.",
       .tag = OptionTag::INDUCTION})
  , _inductionNegOnly("induction_neg_only",this,true,
      {.short_name = "indn",
       .description = "Only apply induction to negative literals",
       .tag = OptionTag::INDUCTION})
  , _inductionUnitOnly("induction_unit_only",this,true,
      {.short_name = "indu",
       .description = "Only apply induction to unit clauses",
       .tag = OptionTag::INDUCTION})
  , _inductionGen("induction_gen",this,false,
      {.short_name = "indgen",
       .description = "Apply induction with generalization (on both all & selected occurrences)",
       .tag = OptionTag::INDUCTION})
  , _inductionStrengthenHypothesis("induction_strengthen_hypothesis",this,false,
      {.short_name = "indstrhyp",
       .description = "Strengthen induction formulas with the remaining skolem constants"
                                                  " replaced with universally quantified variables in hypotheses",
       .tag = OptionTag::INDUCTION})
  , _maxInductionGenSubsetSize("max_induction_gen_subset_size",this,3,
      {.short_name = "indgenss",
       .description = "Set maximum number of occurrences of the induction term to be"
                                              " generalized, where 0 means no max. (Regular induction will"
                                              " be applied without this restriction.)",
       .tag = OptionTag::INDUCTION})
  , _inductionOnComplexTerms("induction_on_complex_terms",this,false,
      {.short_name = "indoct",
       .description = "Apply induction on complex (ground) terms vs. only on constants",
       .tag = OptionTag::INDUCTION})
  , _inductionGroundOnly("induction_ground_only",this,true,
      {.short_name = "indgo",
       .description = "Apply induction only on ground literals vs. literals with at most one free variable",
       .tag = OptionTag::INDUCTION})
  , _functionDefinitionRewriting("function_definition_rewriting",this,false,
      {.short_name = "fnrw",
       .description = "Use function definitions as rewrite rules with the intended orientation rather than the term ordering one",
       .tag = OptionTag::INFERENCES})
  , _integerInductionDefaultBound("int_induction_default_bound",this,false,
      {.short_name = "intinddb",
       .description = "Always apply integer induction with bound 0",
       .tag = OptionTag::INDUCTION})
  , _integerInductionInterval("int_induction_interval",this,
                         IntegerInductionInterval::BOTH,{"infinite","finite","both"},
      {.short_name = "intindint",
       .description = "Whether integer induction is applied over infinite or finite intervals, or both",
       .tag = OptionTag::INDUCTION})
  , _integerInductionStrictnessEq(
        "int_induction_strictness_eq",this,
        IntegerInductionLiteralStrictness::NONE,
        OptionChoiceValues{"none","toplevel_not_in_other","only_one_occurrence","not_in_both","always"},
      {.short_name = "intindsteq",
       .description = "Exclude induction term t/literal l combinations from integer induction.\n"
      "Induction is not applied to _equality_ literals l:\n"
      "  - none: no exclusion\n"
      "  - toplevel_not_in_other: t is a top-level argument of l,\n"
      "    but it does not occur in the other argument of l\n"
      "  - only_one_occurrence: t has only one occurrence in l\n"
      "  - not_in_both: t does not occur in both arguments of l\n"
      "  - always: induction on l is not allowed at all\n",
       .tag = OptionTag::INDUCTION}
    )
  , _integerInductionStrictnessComp(
        "int_induction_strictness_comp",this,
        IntegerInductionLiteralStrictness::TOPLEVEL_NOT_IN_OTHER,
        OptionChoiceValues{"none","toplevel_not_in_other","only_one_occurrence","not_in_both","always"},
      {.short_name = "intindstcomp",
       .description = "Exclude induction term t/literal l combinations from integer induction.\n"
      "Induction is not applied to _comparison_ literals l:\n"
      "  - none: no exclusion\n"
      "  - toplevel_not_in_other: t is a top-level argument of l,\n"
      "    but it does not occur in the other argument of l\n"
      "  - only_one_occurrence: t has only one occurrence in l\n"
      "  - not_in_both: t does not occur in both arguments of l\n"
      "  - always: induction on l is not allowed at all\n",
       .tag = OptionTag::INDUCTION}
    )
  , _integerInductionStrictnessTerm(
      "int_induction_strictness_term",this,
      IntegerInductionTermStrictness::INTERPRETED_CONSTANT,
      {"none", "interpreted_constant", "no_skolems"},
      {.short_name = "intindstterm",
       .description = "Exclude induction term t/literal l combinations from integer induction.\n"
      "Induction is not applied to the induction term t:\n"
      "  - none: no exclusion\n"
      "  - interpreted_constant: t is an interpreted constant\n"
      "  - no_skolems: t does not contain a skolem function",
       .tag = OptionTag::INDUCTION}
    )
  , _nonUnitInduction("non_unit_induction",this,false,
      {.short_name = "nui",
       .description = "Induction on certain clauses or clause sets instead of just unit clauses",
       .tag = OptionTag::INDUCTION})
  , _inductionOnActiveOccurrences("induction_on_active_occurrences",this,false,
      {.short_name = "indao",
       .description = "Only use induction terms from active occurrences, generalize over active occurrences",
       .tag = OptionTag::INDUCTION})
  , _literalComparisonMode("literal_comparison_mode",this,
                                                                      LiteralComparisonMode::STANDARD,
                                                                      {"predicate","reverse","standard"},
      {.short_name = "lcm",
       .description = "Vampire uses term orderings which use an ordering of predicates. Standard places equality (and certain other special predicates) first and all others second. Predicate depends on symbol precedence (see symbol_precedence). Reverse reverses the order.",
       .tag = OptionTag::SATURATION})
  , _lookaheadDelay("lookahaed_delay",this,0,
      {.short_name = "lsd",
       .description = "Delay the use of lookahead selection by this many selections"
                                  " the idea is that lookahead selection may behave erratically"
                                  " at the start",
       .tag = OptionTag::SATURATION})
  , _lrsFirstTimeCheck("lrs_first_time_check",this,5,
      {.short_name = "lftc",
       .description = "Percentage of time limit at which the LRS algorithm will for the first time estimate the number of reachable clauses.",
       .tag = OptionTag::LRS})
  , _lrsWeightLimitOnly("lrs_weight_limit_only",this,false,
      {.short_name = "lwlo",
       .description = "If off, the lrs sets both age and weight limit according to clause reachability, otherwise it sets the age limit to 0 and only the weight limit reflects reachable clauses",
       .tag = OptionTag::LRS})
  , _lrsRetroactiveDeletes("lrs_retroactive_deletes",this,false,
      {.short_name = "lrd",
       .description = "Not only deleted new clauses that exceed current estimated limits in passive,"
    " but also visit active and passive and delete clauses that exceed the new limit or would only generate children exceeding the limit.",
       .tag = OptionTag::LRS})
  , _lrsPreemptiveDeletes("lrs_preemptive_deletes",this,true,
      {.short_name = "lpd",
       .description = "If false, LRS will not use limits to delete clauses entering passive."
     " (Only the retroactive deletes might apply.)",
       .tag = OptionTag::LRS})
  #if VAMPIRE_PERF_EXISTS
  , _instructionLimit("instruction_limit",this,0,
      {.short_name = "i",
       .description = "Limit the number (in millions) of executed instructions (excluding the kernel ones)."})
  , _simulatedInstructionLimit("simulated_instruction_limit",this,0,
      {.short_name = "sil",
       .description = "Instruction limit (in millions) of executed instructions for the purpose of reachability estimations of the LRS saturation algorithm (if 0, the actual instruction limit is used)",
       .tag = OptionTag::LRS})
  , _parsingDoesNotCount("parsing_does_not_count",this,false,
      {.description = "Extend the instruction limit by the amount of instructions it took to parse the input problem.",
       .tag = OptionTag::DEVELOPMENT})
  #endif
  , _memoryLimit("memory_limit",this,
#if VDEBUG
                                       1024     //   1 GB
#else
                                       131072   // 128 GB (current max on the StarExecs)
#endif
                                       ,
      {.short_name = "m",
       .description="Attempt to limit memory use (in MB). Limits less than 20MB are ignored to allow Vampire to start. Known not to work on MacOS for mysterious reasons: https://forums.developer.apple.com/forums/thread/702803"}
                                       )
  , _interactive("interactive",this,false,
      {.description = "An experimental interactive mode (commands to use: load <file to parse>, read <line to parse>, pop (to drop the last added set of formulas), run [options to supply], exit).",
       .experimental = true})
  , _mode("mode",this,Mode::VAMPIRE,
                                    {"axiom_selection",
                                        "casc",
                                        "clausify",
                                        "consequence_elimination",
                                        "model_check",
                                        "output",
                                        "portfolio",
                                        "preprocess",
                                        "preprocess2",
                                        "profile",
                                        "smtcomp",
                                        "spider",
                                        "tclausify",
                                        "tpreprocess",
                                        "vampire"},
      {.description = "Select the mode of operation. Choices are:\n"
    "  -vampire: the standard mode of operation for first-order theorem proving\n"
    "  -portfolio: a portfolio mode running a specified schedule (see schedule)\n"
    "  -casc, casc_sat, smtcomp - like portfolio mode, with competition-specific presets for other options, including output. "
    "If you wish to use e.g. the CASC portfolio without the presets, use --mode portfolio --schedule casc.\n"
    "  -preprocess,axiom_selection,clausify: modes for producing output\n      for other solvers.\n"
    "  -tpreprocess,tclausify: output modes for theory input (clauses are quantified\n      with sort information; tclausify outputs TPTP tcf).\n"
    "  -output,profile: output information about the problem\n"
    "Some modes are not currently maintained (get in touch if interested):\n"
    "  -bpa: perform bound propagation\n"
    "  -consequence_elimination: perform consequence elimination\n"})
  , _intent("intent",this,Intent::UNSAT,{"unsat","sat"},
      {.short_name = "intent",
       .description = "Describes what the system should be striving to show."
      " By default a prover tries to show `unsat` and find a refutation (a proof of the negated conjecture)."
      " Discovering a finite saturations while using a complete strategy and thus testifying satisfiability is a nice bonus in that case."
      " On the other hand, with the intent `sat` the main focus is on finding models."
      " (Please use `--mode casc --intent sat` to achieve what was previously triggered via `--mode CASC_SAT`)."})
  , _schedule("schedule",this,Schedule::CASC,
        {"casc",
         "casc_2024",
         "casc_2025",
         "casc_sat",
         "casc_sat_2024",
         "casc_sat_2025",
         "file",
         "induction",
         "integer_induction",
         "intind_oeis",
         "ltb_default_2017",
         "ltb_hh4_2017",
         "ltb_hll_2017",
         "ltb_isa_2017",
         "ltb_mzr_2017",
         "smtcomp",
         "smtcomp_2018",
         "snake_tptp_uns",
         "snake_tptp_sat",
         "struct_induction",
         "struct_induction_tip"},
      {.short_name = "sched",
       .description = "Schedule to be run by the portfolio mode. casc and smtcomp usually point to the most recent schedule in that category. file loads the schedule from a file specified in --schedule_file. Note that some old schedules may contain option values that are no longer supported - see ignore_missing.",
       .tag = OptionTag::PORTFOLIO})
  , _scheduleFile("schedule_file",this, "",
      {.description = "Path to the input schedule file. Each line contains an encoded strategy. Disabled unless `--schedule file` is set.",
       .tag = OptionTag::PORTFOLIO})
  , _multicore("cores",this,1,
      {.description = "When running in portfolio modes (including casc or smtcomp modes) specify the number of cores, set to 0 to use maximum",
       .tag = OptionTag::PORTFOLIO})
  , _slowness("slowness",this,1.0,
      {.description = "The factor by which is multiplied the time limit of each configuration in casc/casc_sat/smtcomp/portfolio mode",
       .tag = OptionTag::PORTFOLIO})
  , _randomizeSeedForPortfolioWorkers("randomize_seed_for_portfolio_workers",this,true,
      {.description = "In portfolio mode, let each worker process start from its own independent random seed.",
       .tag = OptionTag::PORTFOLIO})
  , _shuffleOnScheduleRepeats("shuffle_on_schedule_repeats",this,true,
      {.description = "In portfolio mode, when we run out of strategies in the selected schedule, we restart from the beginning while doubling the limits,"
                                             " under this option, we also force si=on:rtra=on to increase the chance that the repeated strategies `do something else`.",
       .tag = OptionTag::PORTFOLIO})
  , _naming("naming",this,8,
      {.short_name = "nm",
       .description = "Introduce names for subformulas. Given a subformula F(x1,..,xk) of formula G a new predicate symbol is introduced as a name for F(x1,..,xk) by adding the axiom n(x1,..,xk) <=> F(x1,..,xk) and replacing F(x1,..,xk) with n(x1,..,xk) in G. The value indicates how many times a subformula must be used before it is named.",
       .tag = OptionTag::PREPROCESSING})
  , _nonliteralsInClauseWeight("nonliterals_in_clause_weight",this,false,
      {.short_name = "nicw",
       .description = "Non-literal parts of clauses (such as its split history) will also contribute to the weight",
       .tag = OptionTag::AVATAR})
  , _normalize("normalize",this,false,
      {.short_name = "norm",
       .description = "Normalize the problem so that the ordering of clauses etc does not effect proof search.",
       .tag = OptionTag::PREPROCESSING})
  , _shuffleInput("shuffle_input",this,false,
      {.short_name = "si",
       .description = "Randomly shuffle the input problem. (Runs after and thus destroys normalize.)",
       .tag = OptionTag::PREPROCESSING})
  , _randomPolarities("random_polarities",this,false,
      {.short_name = "rp",
       .description = "As part of preprocessing, randomly (though consistently) flip polarities of non-equality predicates in the whole CNF.",
       .tag = OptionTag::PREPROCESSING})
  , _randomizedSimplifications("randomized_simplifications",this,false,
      {.short_name = "rsi",
       .description = "Make selected saturation-loop simplifications (including AVATAR splitting) \"leaky\":"
       " under a coin toss, some of their candidate operations are randomly skipped, as a source of noise injection.",
       .tag = OptionTag::INFERENCES})
  , _randomizedPreprocessing("randomized_preprocessing",this,false,
      {.short_name = "rpr",
       .description = "Make selected preprocessing steps \"leaky\": under a coin toss, some of their operations are randomly skipped,"
       " producing a mixture of half-completed (but still sound) results as a source of noise injection.",
       .tag = OptionTag::PREPROCESSING})
  , _printProofToFile("print_proofs_to_file",this,"",
      {.short_name = "pptf",
       .description = "If Vampire finds a proof, it is printed to the here specified file instead of to stdout.\n"
                                  "Currently, this option only works in portfolio mode.",
       .tag = OptionTag::OUTPUT})
  , _printClausifierPremises("print_clausifier_premises",this,false,
      {.description = "Output how the clausified problem was derived.",
       .tag = OptionTag::OUTPUT})
  , _proof("proof",this,Proof::ON,{"off","on","proofcheck","tptp","property","smt2_proofcheck","smtcheck"},
      {.short_name = "p",
       .description = "Specifies whether proof (or similar e.g. model/saturation) will be output and in which format:\n"
      "- off gives no proof output\n"
      "- on gives native Vampire proof output\n"
      "- proofcheck will output proof as a sequence of TPTP problems to allow for proof-checking by external solvers\n"
      "- tptp gives TPTP output\n"
      "- property is a developmental option. It allows developers to output statistics about the proof using a ProofPrinter "
      "object (see Kernel/InferenceStore::ProofPropertyPrinter\n"
      "- smtcheck produces a ground SMT script for proof checking\n",
       .tag = OptionTag::OUTPUT})
  , _minimizeSatProofs("minimize_sat_proofs",this,true,
      {.short_name = "msp",
       .description = "Perform premise minimization when a sat solver finds a clause set UNSAT\n"
        "(such as with AVATAR proofs or with global subsumption).",
       .tag = OptionTag::OUTPUT})
  , _proofExtra("proof_extra",this,ProofExtra::OFF,{"off","free","full"},
      {.description = "Add extra detail to proofs:\n "
      "- free uses known information only\n"
      "- full may perform expensive operations to achieve this so may"
      " significantly impact on performance.\n"
      " The option is still under development and the format of extra information (mainly from full) may change between minor releases",
       .tag = OptionTag::OUTPUT})
  , _traceback("traceback",this,false,
      {.description = "Try decoding backtrace into a sequence of human readable function names using addr2line/atos/etc.",
       .tag = OptionTag::OUTPUT})
  , _protectedPrefix("protected_prefix",this,"",
      {.description = "Symbols with this prefix are immune against elimination during preprocessing",
       .tag = OptionTag::PREPROCESSING,
       .experimental = true // Does not work for all (any?) preprocessing steps currently
      })
  , _questionAnswering("question_answering",this,QuestionAnsweringMode::AUTO,
                                                                  {"auto","plain","synthesis","off"},
      {.short_name = "qa",
       .description = "Determines whether (and how) we attempt to answer questions:"
       " plain - answer-literal-based, supports disjunctive answers; synthesis - designed for synthesising programs from proofs.",
       .tag = OptionTag::OTHER})
  , _questionAnsweringGroundOnly("question_answering_ground_only",this,false,
      {.short_name = "qago",
       .description = "In qa plain mode: if set, only ground answers will be considered.",
       .tag = OptionTag::OTHER})
  , _questionAnsweringAvoidThese("question_answering_avoid_these",this,"",
      {.short_name = "qaat",
       .description = "A |-separated list of answer literal atoms (e.g., `ans0(sK1)|ans0(f(c))`) that should not be considered as answers to return."
      " The atoms may contain variables. Matching against any of those disqualifies a potential answer.",
       .tag = OptionTag::OTHER})
  , _randomSeed("random_seed",this,1 /* this should be the value of Random::_seed from Random.cpp */,
      {.description = "Some parts of vampire use random numbers. This seed allows for reproducibility of results. By default the seed is not changed."
      " Use the non-default value 0 to have vampire query a random_device for always different behaviour.",
       .tag = OptionTag::INPUT})
  , _randomStrategySeed("random_strategy_seed",this,0,
      {.description = "Sets the seed for generating random strategies."
      " This option is necessary because --random_seed <value> will be included as a fixed value in the generated random strategy,"
      " hence won't have any effect on the random strategy generation. Set to non-0 for this to have effect; the default 0 still calls a random_device.",
       .tag = OptionTag::INPUT,
       .experimental = true})
  , _sampleStrategy("sample_strategy",this,"",
      {.description = "Specify a path to a filename (of homemade format) describing how to sample a random strategy.",
       .tag = OptionTag::DEVELOPMENT,
       .experimental = true})
  , _activationLimit("activation_limit",this,0,
      {.short_name = "al",
       .description = "Terminate saturation after this many iterations of the main loop. 0 means no limit.",
       .tag = OptionTag::SATURATION})
  , _satSolver("sat_solver",this,SatSolver::MINISAT, {
      "minisat",
      "cadical"
#if VZ3
      ,"z3"
#endif
    },
      {.short_name = "sas",
       .description = "Select the SAT solver to be used throughout Vampire."
      " This will be used in AVATAR (for splitting) when the saturation algorithm is discount, lrs or otter."
      " And for finite model finding when the saturation algorithm is fmb.",
       .tag = OptionTag::SAT})
  , _saturationAlgorithm("saturation_algorithm",this,SaturationAlgorithm::LRS,
                                                                  {"discount","fmb","lrs","otter"
#if VZ3
      ,"z3"
#endif
    },
      {.short_name = "sa",
       .description = "Select the saturation algorithm:\n"
    " - discount:\n"
    " - otter:\n"
    " - limited resource:\n"
    " - fmb : finite model building for satisfiable problems.\n"
    " - z3 : pass the preprocessed problem to z3, will terminate if the resulting problem is not ground.\n"
    "z3 and fmb aren't influenced by options for the saturation algorithm, apart from those under the relevant heading",
       .tag = OptionTag::SATURATION})
  , _showAll("show_everything",this,false,
      {.description = "Turn (almost) all of the showX commands on",
       .tag = OptionTag::DEVELOPMENT})
  , _showActive("show_active",this,false,
      {.description = "Print activated clauses.",
       .tag = OptionTag::DEVELOPMENT})
  , _showBlocked("show_blocked",this,false,
      {.description = "Show generating inferences blocked due to coloring of symbols",
       .tag = OptionTag::DEVELOPMENT})
  , _showDefinitions("show_definitions",this,false,
      {.description = "Show definition introductions.",
       .tag = OptionTag::DEVELOPMENT})
  , _showInterpolant("show_interpolant",this,InterpolantMode::OFF,
                                                          {"new_heur",
#if VZ3
                                                          "new_opt",
#endif
                                                          "off"},
      {.tag = OptionTag::OTHER,
       .experimental = true})
  , _showNew("show_new",this,false,
      {.description = "Show new (generated) clauses",
       .tag = OptionTag::DEVELOPMENT})
  , _sineToAge("sine_to_age",this,false,
      {.short_name = "s2a",
       .description = "Use SInE levels to postpone introducing clauses more distant from the conjecture to proof search by artificially making them younger (age := sine_level).",
       .tag = OptionTag::SATURATION})
  , _sineToPredLevels("sine_to_pred_levels",this,PredicateSineLevels::OFF,{"no","off","on"},
      {.short_name = "s2pl",
       .description = "Assign levels to predicate symbols as they are used to trigger axioms during SInE computation. "
        "Then use them as predicateLevels determining the ordering. 'on' means conjecture symbols are larger, 'no' means the opposite. (equality keeps its standard lowest level).",
       .tag = OptionTag::SATURATION})
  , _showSplitting("show_splitting",this,false,
      {.description = "Show updates within AVATAR",
       .tag = OptionTag::DEVELOPMENT})
  , _showNonconstantSkolemFunctionTrace("show_nonconstant_skolem_function_trace",this,false,
      {.description = "Show introduction of non-constant skolem functions.",
       .tag = OptionTag::DEVELOPMENT})
  , _showOptions("show_options",this,false,
      {.description = "List all available options",
       .tag = OptionTag::HELP})
  , _showOptionsLineWrap("show_options_line_wrap",this,true,
      {.description = "Line wrap in show options. Mainly used when options are read by another tool that applies its own line wrap.",
       .tag = OptionTag::HELP,
       .experimental = true})
  , _showExperimentalOptions("show_experimental_options",this,false,
      {.description = "Include experimental options in showOption",
       .tag = OptionTag::HELP,
       .experimental = true // only we know about it!
      })
  , _showHelp("help",this,false,
      {.short_name = "h",
       .description = "Display the help message",
       .tag = OptionTag::HELP})
  , _printAllTheoryAxioms("print_theory_axioms",this,false,
      {.description = "Just print all theory axioms and terminate",
       .tag = OptionTag::DEVELOPMENT,
       .experimental = true})
  , _explainOption("explain_option",this,"",
      {.short_name = "explain",
       .description = "Use to explain a single option i.e. -explain explain",
       .tag = OptionTag::HELP})
  , _showPassive("show_passive",this,false,
      {.description = "Show clauses added to the passive set.",
       .tag = OptionTag::DEVELOPMENT})
  , _showReductions("show_reductions",this,false,
      {.description = "Show reductions.",
       .tag = OptionTag::DEVELOPMENT})
  , _showPreprocessing("show_preprocessing",this,false,
      {.description = "Show preprocessing.",
       .tag = OptionTag::DEVELOPMENT})
  , _showSkolemisations("show_skolemisations",this,false,
      {.description = "Show Skolemisations.",
       .tag = OptionTag::DEVELOPMENT})
  , _showSymbolElimination("show_symbol_elimination",this,false,
      {.description = "Show symbol elimination.",
       .tag = OptionTag::DEVELOPMENT})
  , _showTheoryAxioms("show_theory_axioms",this,false,
      {.description = "Show the added theory axioms.",
       .tag = OptionTag::DEVELOPMENT})
  , _showFOOL("show_fool",this,false,
      {.description = "Reveal the internal representation of FOOL terms",
       .tag = OptionTag::OUTPUT})
  , _showFMBsortInfo("show_fmb_sort_info",this,false,
      {.description = "Print information about sorts in FMB",
       .tag = OptionTag::OUTPUT})
  , _showInduction("show_induction",this,false,
      {.description = "Print information about induction",
       .tag = OptionTag::OUTPUT})
  , _showSimplOrdering("show_ordering",this,false,
      {.description = "Display the used simplification ordering's parameters.",
       .tag = OptionTag::OUTPUT})
  , _showPropDict("show_property_dict",this,false,
      {.description = "Display a (python-formatted) dictionary summing up the main properties of the parsed problem.",
       .tag = OptionTag::OUTPUT,
       .experimental = true})
  #if VAMPIRE_CLAUSE_TRACING
  , _traceBackward("trace_bwd",this,0,
      {.description = "The id of a clause you want to see all predecessors (unites used to derive the clause).",
       .tag = OptionTag::OUTPUT})
  , _traceForward("trace_fwd",this,-1,
      {.description = "The id of a clause you want to see all consequences of.",
       .tag = OptionTag::OUTPUT})
  #endif
  #if VZ3
  , _showZ3("show_z3",this,false,
      {.description = "Print the clauses being added to Z3",
       .tag = OptionTag::DEVELOPMENT})
  , _problemExportSyntax("export_syntax",this,ProblemExportSyntax::SMTLIB, {"smtlib", "api_calls",},
      {.description = "Set the syntax for exporting z3 problems.",
       .tag = OptionTag::DEVELOPMENT})
  , _exportAvatarProblem("export_avatar",this,"",
      {.description = "Export the avatar problems to solve in smtlib syntax.",
       .tag = OptionTag::DEVELOPMENT})
  , _exportThiProblem("export_thi",this,"",
      {.description = "Export the theory instantiation problems to solve in smtlib syntax.",
       .tag = OptionTag::DEVELOPMENT})
  , _satFallbackForSMT("sat_fallback_for_smt",this,false,
      {.short_name = "sffsmt",
       .description = "If using z3 run a sat solver alongside to use if the smt"
       " solver returns unknown at any point",
       .tag = OptionTag::SAT})
  , _theoryInstAndSimp("theory_instantiation",this,
                                        TheoryInstSimp::OFF, {"off", "all", "strong", "neg_eq", "overlap", "full", "new"},
      {.short_name = "thi",
       .description = ""
    "\nEnables theory instantiation rule: "
    "\nT[x_1, ..., x_n] \\/ C[x_1, ..., x_n]"
    "\n-------------------------------------"
    "\n           C[t_1, ..., t_n]          "
    "\nwhere  "
    "\n -  T[x_1, ..., x_n] is a pure theory clause  "
    "\n - ~T[t_1, ...., t_n] is valid "
    "\n"
    "\nThe rule uses an smt solver (i.e. z3 atm) to find t_1...t_n that satisfy the requirement for the rule."
    "\n"
    "\nThe different option values define the behaviour of which theory literals to select."
    "\n- all    : hmmm.. what could that mean?!"
    "\n- neg_eq : only negative equalities"
    "\n- strong : interpreted predicates, but no positive equalities"
    "\n- overlap: all literals that contain variables that are also contained in a strong literal"
    "\n- new    : deprecated"
    "\n- full   : deprecated"
    "",
       .tag = OptionTag::THEORIES})
  , _thiGeneralise("theory_instantiation_generalisation",this, false,
      {.short_name = "thigen",
       .description = "Enable retrieval of generalised instances in theory instantiation. This can help with datatypes but requires thi to call the smt solver twice. "
    "\n"
    "\n An example of such a generalisation is:"
    "\n first(x) > 0 \\/ P[x]"
    "\n ==================== "
    "\n     P[(-1, y)]"
    "\n"
    "\n instead of the more concrete instance"
    "\n first(x) > 0 \\/ P[x]"
    "\n ==================== "
    "\n     P[(-1, 0)]",
       .tag = OptionTag::THEORIES,
       .experimental = true})
  , _thiTautologyDeletion("theory_instantiation_tautology_deletion",this, false,
      {.short_name = "thitd",
       .description = "Enable deletion of tautology theory subclauses detected via theory instantiation.",
       .tag = OptionTag::THEORIES,
       .experimental = true})
  #endif
  , _unificationWithAbstraction("unification_with_abstraction",this,
                                      UnificationWithAbstraction::AUTO,
                                      {"auto","off","interpreted_only","one_side_interpreted","one_side_constant","all","ground", "func_ext", "alasca_one_interp", "alasca_can_abstract", "alasca_main", "alasca_main_floor", "hol"},
      {.short_name = "uwa",
       .description = "During unification, if two terms s and t fail to unify we will introduce a constraint s!=t and carry on. For example, "
      "resolving p(1) \\/ C with ~p(a+2) would produce C \\/ 1 !=a+2. This is controlled by a check on the terms. The expected "
      "use case is in theory reasoning. The possible values are:"
      "- auto: boils down to off for non-theory problems, and to alasca_main whenever alasca (on by default) kicks in (except under alasca_integer_conversion, when it becomes alasca_main_floor)\n"
      "- off: do not introduce a constraint\n"
      "- interpreted_only: only if s and t have interpreted top symbols\n"
      "- one_side_interpreted: only if one of s or t have interpreted top symbols\n"
      "- one_side_constant: only if one of s or t is an interpreted constant (e.g. a number)\n"
      "- all: always apply\n"
      "- ground: only if both s and t are ground\n"
      "- alasca_one_interp, alasca_can_abstract, alasca_main: strategies used for the real-arithmetic version of alasca. these are described in  the LPAR2023 paper  \"Refining Unification with Abstraction\""
      "- alasca_main_floor: an extension of the alasca_main strategy to work with mixed integer-real arithmetic. this option is experimental\n"
      "- hol: introduce constraints for all higher-order parts whose unification is undecidable\n"
      "See Unification with Abstraction and Theory Instantiation in Saturation-Based Reasoning for further details.",
       .tag = OptionTag::THEORIES})
  , _unificationWithAbstractionFixedPointIteration("unification_with_abstraction_fixed_point_iteration",this,
                                     false,
      {.short_name = "uwa_fpi",
       .description = "The order in which arguments are being processed in unification with absraction can yield different results. i.e. unnecessary unifiers. This can be resolved by applying unification with absraction multiple times. This option enables this fixed point iteration. For details have a look at the paper \"Refining Unification with Abstraction\" from LPAR 2023.",
       .tag = OptionTag::INFERENCES})
  , _useACeval("use_ac_eval",this,false,
      {.short_name = "uace",
       .description = "Evaluate associative and commutative operators e.g. + and *.",
       .tag = OptionTag::THEORIES})
  , _simulatedTimeLimit("simulated_time_limit",this,0,
      {.short_name = "stl",
       .description = "Time limit in seconds for the purpose of reachability estimations of the LRS saturation algorithm (if 0, the actual time limit is used)",
       .tag = OptionTag::LRS})
  , _lrsEstimateCorrectionCoef("lrs_estimate_correction_coef",this,1.0,
      {.short_name = "lecc",
       .description = "Make lrs more (<1.0) or less (>1.0) aggressive by multiplying by this coef its estimate of how many clauses are still reachable.",
       .tag = OptionTag::LRS})
  , _lrsSaveTraceFile("lrs_save_trace_file",this,"",
      {.short_name = "lstf",
       .description = "When set, vampire will output a trace of decistions in the LRS estimate module, which can be used to reproduce a lucky run.",
       .tag = OptionTag::LRS})
  , _lrsLoadTraceFile("lrs_load_trace_file",this,"",
      {.short_name = "lltf",
       .description = "When set, vampire will load a previously saved trace of decistions of the LRS estimate module, which be used instead of the module's logic to guide the estimates.",
       .tag = OptionTag::LRS})
  , _sineDepth("sine_depth",this,0,
      {.short_name = "sd",
       .description = "Limit number of iterations of the transitive closure algorithm that selects formulas based on SInE's D-relation (see SInE description). 0 means no limit, 1 is a maximal limit (least selected axioms), 2 allows two iterations, etc...",
       .tag = OptionTag::PREPROCESSING})
  , _sineGeneralityThreshold("sine_generality_threshold",this,0,
      {.short_name = "sgt",
       .description = "Generality of a symbol is the number of input formulas in which a symbol appears."
    " If the generality of a symbol is smaller than the threshold, it is always included into the D-relation with formulas in which it appears."
    " Note that with the default value (0) this actually never happens."
    " (And with 1, there would be no difference, because the 1 is used up on the occurrence in the already included unit.)",
       .tag = OptionTag::PREPROCESSING})
    // Like generality threshold for SiNE, except used by the sine2age trick
  , _sineToAgeGeneralityThreshold("sine_to_age_generality_threshold",this,0,
      {.short_name = "s2agt",
       .description = "Like sine_generality_threshold but influences sine_to_age, sine_to_pred_levels, and sine_level_split_queue rather than sine_selection.",
       .tag = OptionTag::SATURATION})
  , _sineSelection("sine_selection",this,SineSelection::OFF,{"axioms","included","off"},
      {.short_name = "ss",
       .description = "If 'axioms', all formulas that are not annotated as 'axiom' (i.e. conjectures and hypotheses) are initially selected, and the SInE selection is performed on those annotated as 'axiom'. If 'included', all formulas that are directly in the problem file are initially selected, and the SInE selection is performed on formulas from included files. The 'included' value corresponds to the behaviour of the original SInE implementation.",
       .tag = OptionTag::PREPROCESSING})
  , _sineTolerance("sine_tolerance",this,1.0,
      {.short_name = "st",
       .description = "SInE tolerance parameter (sometimes referred to as 'benevolence')."
    " Has special value of -1.0 (which effectively codes +infinity), but otherwise must be greater or equal 1.0."
    " For each unit, only its least general symbol (let's call its generality g_min) and its symbols with generality up to g_min*tolerance trigger the unit to be included.",
       .tag = OptionTag::PREPROCESSING})
    // Like generality threshold for SiNE, except used by the sine2age trick
  , _sineToAgeTolerance("sine_to_age_tolerance",this,1.0,
      {.short_name = "s2at",
       .description = "Like sine_tolerance but influences sine_to_age, sine_to_pred_levels, and sine_level_split_queue rather than sine_selection."
    " Has special value of -1.0, but otherwise must be greater or equal 1.0.",
       .tag = OptionTag::SATURATION})
  , _sos("sos",this,Sos::OFF,{"all","off","on","theory"},
      {.short_name = "sos",
       .description = "Set of support strategy. All formulas annotated as axioms are put directly among active clauses, without performing any inferences between them."
    " If all, select all literals of set-of-support clauses, otherwise use the default literal selector. If theory then only apply to theory"
    " axioms introduced by vampire (all literals are selected).",
       .tag = OptionTag::PREPROCESSING})
  , _sosTheoryLimit("sos_theory_limit",this,0,
      {.short_name = "sstl",
       .description = "When sos=theory, limit the depth of descendants a theory axiom can have.",
       .tag = OptionTag::PREPROCESSING})
  , _splitting("avatar",this,true,
      {.short_name = "av",
       .description = "Use AVATAR splitting.",
       .tag = OptionTag::AVATAR})
  , _splitAtActivation("split_at_activation",this,false,
      {.short_name = "sac",
       .description = "Split a clause when it is activated, default is to split when it is processed",
       .tag = OptionTag::AVATAR})
  , _cleaveNonsplittables("cleave_nonsplittables",this,false,
      {.short_name = "cn",
       .description = "Tentatively propose single-literal component strengthenings. Sometimes useful for bringing about finite saturations.",
       .tag = OptionTag::AVATAR})
  , _splittingAddComplementary("avatar_add_complementary",this,
                                                                                SplittingAddComplementary::GROUND,{"ground","none"},
      {.short_name = "aac",
       .tag = OptionTag::AVATAR})
  , _splittingCongruenceClosure("avatar_congruence_closure",this, false,
      {.short_name = "acc",
       .description = "Use a congruence closure decision procedure on top of the AVATAR SAT solver. This ensures that models produced by AVATAR satisfy the theory of uninterpreted functions.",
       .tag = OptionTag::AVATAR})
  , _splittingAvatimer("avatar_turn_off_time_frac",this,1.0,
      {.short_name = "atotf",
       .description = "Stop splitting after the specified fraction of the overall time has passed (the default 1.0 means AVATAR runs until the end).\n"
        "(the remaining time AVATAR is still switching branches and communicating with the SAT solver,\n"
        "but not introducing new splits anymore. This fights the theoretical possibility of AVATAR's dynamic incompleteness.)",
       .tag = OptionTag::AVATAR})
  , _splittingNonsplittableComponents("avatar_nonsplittable_components",this,
                                                                                              SplittingNonsplittableComponents::KNOWN,
                                                                                              {"all","all_dependent","known","none"},
      {.short_name = "anc",
       .description = "Decide what to do with a nonsplittable component:\n"
    "  -known: SAT clauses will be learnt from non-splittable clauses that have corresponding components (if there is a component C with name SAT l, clause C | {l1,..ln} will give SAT clause ~l1 \\/ … \\/ ~ln \\/ l). When we add the sat clause, we discard the original FO clause C | {l1,..ln} and let the component selection update model, possibly adding the component clause C | {l}.\n"
    "  -all: like known, except when we see a non-splittable clause that doesn't have a name, we introduce the name for it.\n"
    "  -all_dependent: like all, but we don't introduce names for non-splittable clauses that don't depend on any components",
       .tag = OptionTag::AVATAR})
  , _splittingMinimizeModel("avatar_minimize_model",this,true,
      {.short_name = "amm",
       .description = "Minimize the SAT-solver model by replacing concrete values with don't-cares"
                                        " provided the sat clauses remain provably satisfied by the partial model.",
       .tag = OptionTag::AVATAR})
  , _splittingLiteralPolarityAdvice(
                                                "avatar_literal_polarity_advice",this,
                                                SplittingLiteralPolarityAdvice::NONE,
                                                {"false","true","none","random"},
      {.short_name = "alpa",
       .description = "Override SAT-solver's default polarity/phase setting for variables abstracting clause components.",
       .tag = OptionTag::AVATAR})
  , _splittingDeleteDeactivated("avatar_delete_deactivated",this,
                                                                        SplittingDeleteDeactivated::LARGE_ONLY,{"on","large","off"},
      {.short_name = "add",
       .tag = OptionTag::AVATAR})
  , _statistics("statistics",this,Statistics::BRIEF,{"brief","full","none"},
      {.short_name = "stat",
       .description = "The level of statistics to report at the end of the run.",
       .tag = OptionTag::OUTPUT})
  , _superpositionFromVariables("superposition_from_variables",this,true,
      {.short_name = "sfv",
       .description = "Perform superposition from variables.",
       .tag = OptionTag::INFERENCES})
  , _termOrdering("term_ordering",this, TermOrdering::AUTO_KBO,
                                                    {"auto_kbo","kbo","qkbo","lakbo","lpo","incomp"},
      {.short_name = "to",
       .description = "The term ordering used by Vampire to orient equations and order literals.\n"
      "possible values:\n"
      "- auto_kbo: boils down to kbo for non-theory problems and to qkbo, whenever alasca (on by default) kicks in\n"
      "- kbo: Knuth-Bendix Ordering\n"
      "- qkbo: QKBO ordering as described in the TACAS 2023 paper \"ALASCA: Reasoning in Quantified Linear Arithmetic\"\n"
      "- lpo: Lexicographical Path Ordering\n"
      "- lakbo: similar to QKBO but for mixed integer-real arithmetic. this option is experimental",
       .tag = OptionTag::SATURATION})
  , _symbolPrecedence("symbol_precedence",this,SymbolPrecedence::FREQUENCY,
                                                            {"arity","occurrence","reverse_arity","unary_first",
                                                            "const_max", "const_min",
                                                            "scramble","frequency","unary_frequency","const_frequency",
                                                            "reverse_frequency","reverse_occurrence"},
      {.short_name = "sp",
       .description = "Vampire uses term orderings which require a precedence relation between symbols.\n"
                                  "Arity orders symbols by their arity (and reverse_arity takes the reverse of this) and occurrence orders symbols by the order they appear in the problem, "
                                  "the first one seen becoming the smallest (reverse_occurrence takes the reverse of this, which notably puts the symbols introduced during "
                                  "preprocessing -- the Skolems and the formula names -- at the bottom rather than above every input symbol). "
                                  "Then we have a few precedence generating schemes adopted from E: frequency - sort by frequency making rare symbols large, reverse does the opposite, "
                                  "(For the weighted versions, each symbol occurrence counts as many times as is the length of the clause in which it occurs.) "
                                  "unary_first is like arity, except that unary symbols are maximal (and ties are broken by frequency), "
                                  "unary_frequency is like frequency, except that unary symbols are maximal, "
                                  "const_max makes constants the largest, then falls back to arity, "
                                  "const_min makes constants the smallest, then falls back to reverse_arity, "
                                  "const_frequency makes constants the smallest, then falls back to frequency.",
       .tag = OptionTag::SATURATION})
  , _introducedSymbolPrecedence("introduced_symbol_precedence",this,
                                                                                IntroducedSymbolPrecedence::TOP,
                                                                                {"top","bottom"},
      {.short_name = "isp",
       .description = "Decides where to place symbols introduced during proof search in the symbol precedence",
       .tag = OptionTag::SATURATION})
  , _evaluationMode("evaluation",this,
                                                        EvaluationMode::SIMPLE,
                                                        {"off","simple","force","cautious"},
      {.short_name = "ev",
       .description = "Chooses the algorithm used to simplify interpreted integer, rational, and real terms. \
                                 \
    - simple: will only evaluate expressions built from interpreted constants only.\
    - cautious: will evaluate abstract expressions to a weak polynomial normal form. This is more powerful but may fail in some rare cases where the resulting polynomial is not strictly smaller than the initial one wrt. the simplification ordering. In these cases a new clause with the normal form term will be added to the search space instead of replacing the original clause.  \
    - force: same as `cautious`, but ignoring the simplification ordering and replacing the hypothesis with the normal form clause in any case. \
    ",
       .tag = OptionTag::THEORIES,
       .experimental = true})
  , _kboWeightGenerationScheme("kbo_weight_scheme",this,KboWeightGenerationScheme::CONST,
                                          {"const","random","arity","inv_arity","arity_squared","inv_arity_squared",
                                          "precedence","inv_precedence","frequency","inv_frequency"},
      {.short_name = "kws",
       .description = "Weight generation schemes from KBO inspired by E. This gets overridden by the function_weights option if used.",
       .tag = OptionTag::SATURATION,
       .experimental = true})
  , _kboMaxZero("kbo_max_zero",this,false,
      {.short_name = "kmz",
       .description = "Modifies any kbo_weight_scheme by setting the maximal (by the precedence) function symbol to have weight 0.",
       .tag = OptionTag::SATURATION,
       .experimental = true})
  , _kboAdmissabilityCheck(
        "kbo_admissibility_check",this, KboAdmissibilityCheck::ERROR,
                                     {"error","warning" },
      {.description = "Choose to emit a warning instead of throwing an exception if the weight function and precedence ordering for kbo are not compatible.",
       .tag = OptionTag::SATURATION,
       .experimental = true})
  , _functionWeights("function_weights",this,"",
      {.short_name = "fw",
       .description = "Path to a file that defines weights for KBO for function symbols.\n"
      "\n"
      "Each line in the file is expected to contain a function name, followed by the functions arity, and a positive integer, that specifies symbols weight.\n"
      "\n"
      "Additionally there are special values that can be specified:\n"
      "- `$default    <number>` specifies the default symbol weight, that is used for all symbols not present in the file (if not specified 0 is used)\n"
      "- `$introduced <number>` specifies the weight used for symbols introduced during preprocessing or proof search\n"
      "- `$var        <number>` specifies the weight used for variables\n"
      "- `$int        <number>` specifies the weight used for integer constants\n"
      "- `$rat        <number>` specifies the weight used for rational constants\n"
      "- `$real       <number>` specifies the weight used for real constants\n"
      "\n"
      "\n"
      "===== example ============\n"
      "$add 2 2\n"
      "$mul 2 7\n"
      "f    1 2\n"
      "$default 2\n"
      "$var     2\n"
      "===== end of example =====\n"
      "\n"
      "If this option is empty all weights default to 1.\n",
       .experimental = true})
  , _typeConPrecedence("type_con_precedence",this,"",
      {.short_name = "tcp",
       .description = "A name of a file with an explicit user specified precedence on type constructor symbols.",
       .experimental = true})
  , _functionPrecedence("function_precedence",this,"",
      {.short_name = "fp",
       .description = "A name of a file with an explicit user specified precedence on function symbols.",
       .experimental = true})
  , _predicatePrecedence("predicate_precedence",this,"",
      {.short_name = "pp",
       .description = "A name of a file with an explicit user specified precedence on predicate symbols.",
       .experimental = true})
   // Used by spider mode
  , _testId("test_id",this,"unspecified_test",
      {.experimental = true})
  , _outputMode("output_mode",this,Output::SZS,{"smtcomp","spider","szs","vampire","ucore"},
      {.short_name = "om",
       .description = "Change how Vampire prints the final result. SZS uses TPTP's SZS ontology. smtcomp mode"
    " suppresses all output and just prints sat/unsat. vampire is the same as SZS just without the SZS."
    " Spider prints out some profile information and extra error reports. ucore uses the smt-lib ucore output.",
       .tag = OptionTag::OUTPUT})
  , _ignoreMissingInputsInUnsatCore("ignore_missing_inputs_in_unsat_core",this,false,
      {.description = "When running in unsat core output mode we will complain if there is"
    " an input formula that has no label. Set this on if you don't want this behaviour (which is default in smt-comp).",
       .tag = OptionTag::OUTPUT})
  , _thanks("thanks",this,"Tanya",
      {.experimental = true})
  , _theoryAxioms("theory_axioms",this,TheoryAxiomLevel::ON,{"on","off","some"},
      {.short_name = "tha",
       .description = "Include theory axioms for detected interpreted symbols",
       .tag = OptionTag::PREPROCESSING})
  , _theoryFlattening("theory_flattening",this,false,
      {.short_name = "thf",
       .description = "Flatten clauses to separate theory and non-theory parts in the input. This is often quickly undone in proof search.",
       .tag = OptionTag::PREPROCESSING})
  , _ignoreUnrecognizedLogic("ignore_unrecognized_logic",this,false,
      {.short_name = "iul",
       .description = "Try proof search anyways, if vampire would throw an \"unrecognized logic\" error otherwise.",
       .tag = OptionTag::INPUT})
  // stores deciseconds, but reads seconds from the user by default
  , _timeLimitInDeciseconds("time_limit",this,600,
      {.short_name = "t",
       .description = "Time limit in wall clock seconds, you can use d,s,m,h,D suffixes also i.e. 60s, 5m. Setting it to 0 effectively gives no time limit."})
  #if VTIME_PROFILING
  , _timeStatistics("time_statistics",this,false,
      {.short_name = "tstat",
       .description = "Show how much running time was spent in each part of Vampire",
       .tag = OptionTag::OUTPUT})
  , _timeStatisticsFocus("time_statistics_focus",this,"",
      {.short_name = "tstat_focus",
       .description = "focus on some special subtree of the time statistics",
       .tag = OptionTag::OUTPUT})
  #endif
  , _unitResultingResolution("unit_resulting_resolution",this,URResolution::OFF,{"ec_only","off","on","full"},
      {.short_name = "urr",
       .description = "Uses unit resulting resolution only to derive empty clauses (may be useful for splitting)."
    " 'ec_only' only derives empty clauses, 'on' does everything (but implements a heuristic to skip deriving more than one empty clause),"
    " 'full' ignores this heuristic and is thus complete also under AVATAR.",
       .tag = OptionTag::INFERENCES})
  , _unusedPredicateDefinitionRemoval("unused_predicate_definition_removal",this,true,
      {.short_name = "updr",
       .description = "Attempt to remove predicate definitions. A predicate definition is a formula of the form ![X1,..,Xn] : (p(X1,..,XN) <=> F) where p is not equality and does not occur in F and X1,..,XN are the free variables of F. If p has only positive (negative) occurrences then <=> in the definition can be replaced by => (<=). If p does not occur in the rest of the problem the definition can be removed.",
       .tag = OptionTag::PREPROCESSING})
  , _blockedClauseElimination("blocked_clause_elimination",this,false,
      {.short_name = "bce",
       .description = "Eliminate blocked clauses after clausification.",
       .tag = OptionTag::PREPROCESSING})
  , _predicateElimination("predicate_elimination",this,
                                                                     PredicateElimination::OFF,
                                                                     {"off","on","multi"},
      {.short_name = "pel",
       .description = "After clausification, eliminate predicates that occur at most once in every clause"
      " by replacing their clauses with all pairwise resolvents (cf. Khasidashvili and Korovin, SAT 2016)."
      " With multi, also eliminate a predicate P occurring more than once in a clause, provided P"
      " never occurs both positively and negatively in a single clause and the multi-occurrence"
      " clauses all sit on one polarity side. Instead of pairwise resolvents, the replacement clauses"
      " are then all the hyper-resolvents, each occurrence of a multi-occurrence clause being resolved"
      " against its own (variable-disjoint) copy of a single-occurrence clause of the opposite polarity."
      " On problems without equality and theories, resolvents are computed with an mgu;"
      " otherwise argument disequalities are introduced via (virtual) flattening,"
      " which may add equality to a problem previously without it.",
       .tag = OptionTag::PREPROCESSING})
  , _predicateEliminationTotalLimit("predicate_elimination_total_limit",this,2.0,
      {.short_name = "peltl",
       .description = "A predicate elimination step is only performed if the estimated number of clauses afterwards"
      " (current - |S_P| - |S_~P| + the number of resolvents, which is |S_P|*|S_~P| unless"
      " predicate_elimination is set to multi) does not exceed the number of clauses"
      " before predicate elimination started times this factor.",
       .tag = OptionTag::PREPROCESSING})
  , _predicateEliminationSubsumption("predicate_elimination_subsumption",this,true,
      {.short_name = "pels",
       .description = "Keep the clause set forward-inter-subsumed and subsumption-resolved during predicate elimination.",
       .tag = OptionTag::PREPROCESSING})
  , _distinctGroupExpansionLimit("distinct_group_expansion_limit",this,140,
      {.short_name = "dgel",
       .description = "If a distinct group (defined, e.g., via TPTP's $distinct)"
         " is not larger than this limit, it will be expanded during preprocessing into quadratically many disequalities."
         " (0 means `always expand`)",
       .tag = OptionTag::INPUT})
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
  , _nonGoalWeightCoefficient("nongoal_weight_coefficient",this,
      {.short_name = "nwc",
       .description = "coefficient that will multiply the weight of non-conjecture clauses (those marked as 'axiom' in TPTP)",
       .tag = OptionTag::SATURATION}) // default 10.0 is hard-wired to the constructor
  , _selection("selection",this,10,
      {.short_name = "s",
       .description = "Selection methods 2,3,4,10,11 are complete by virtue of extending Maximal i.e. they select the best among maximal. Methods 1002,1003,1004,1010,1011 relax this restriction and are therefore not complete.\n"
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
    "positive and vice versa (can only apply to non-equality literals).\n",
       .tag = OptionTag::SATURATION})
  , _inputFile("input_file",this,"",
      {.description = "Problem file to be solved (if not specified, standard input is used)",
       .tag = OptionTag::INPUT,
       .experimental = true})
  , _newCNF("newcnf",this,false,
      {.short_name = "newcnf",
       .description = "Use NewCNF algorithm to do naming, preprocessing and clausification.",
       .tag = OptionTag::PREPROCESSING})
  , _inlineLet("inline_let",this,true,
      {.short_name = "ile",
       .description = "Always inline let-expressions.",
       .tag = OptionTag::PREPROCESSING})
  , _manualClauseSelection("manual_cs",this,false,
      {.description = "Run Vampire interactively by manually picking the clauses to be selected",
       .tag = OptionTag::DEVELOPMENT})
  , _inequalityNormalization("normalize_inequalities",this,false,
      {.short_name = "norm_ineq",
       .description = "Enable normalizing of inequalities like s < t ==> 0 < t - s.",
       .tag = OptionTag::THEORIES})
  , _pushUnaryMinus(
       "push_unary_minus",this,
       false,
      {.short_name = "pum",
       .description = "Enable the immediate simplifications:\n"
          " -(t + s) ==> -t + -s\n"
          " -(-t) ==> t\n",
       .tag = OptionTag::THEORIES})
  , _gaussianVariableElimination("gaussian_variable_elimination",this, ArithmeticSimplificationMode::OFF, {"force", "cautious", "off"},
      {.short_name = "gve",
       .description = "Enable the immediate simplification \"Gaussian Variable Elimination\":\n"
          "\n"
          "s != t \\/ C[X] \n"
          "--------------  if s != t can be rewritten to X != r \n"
          "    C[r] \n"
          "\n"
          "Example:\n"
          "\n"
          "6 * X0 != 2 * X1 | p(X0, X1)\n"
          "-------------------------------\n"
          "  p(2 * X1 / 6, X1)\n"
          "\n"
          "\n"
          "For a more detailed description see the paper Making Theory Reasoning Simpler ( https://easychair.org/publications/preprint/K2hb ). \
          In some rare cases the conclusion may be not strictly simpler than the hypothesis. With `force` we ignore these cases, violating the ordering and just simplifying \
          anyways. With `cautious` we will generate a new clause instead of simplifying in these cases.",
       .tag = OptionTag::THEORIES})
  , _alasca("abstracting_linear_arithmetic_superposition_calculus",this,false,
      {.short_name = "alasca",
       .description = "Enables the Linear Arithmetic Superposition CAlculus, a calculus for linear real arithmetic with uninterpretd functions. It is described in the LPAR2023 paper \"ALASCA: Reasoning in Quantified Linear Arithmetic\"\n",
       .tag = OptionTag::INFERENCES})
  , _viras("virtual_integer_real_arithmetic_substitution",this,true,
      {.short_name = "viras",
       .description = "Enables the VIRAS quantifier elimination to be used in ALASCA. The VIRAS method is explained in the LPAR2024 paper \"VIRAS: Conflict-Driven Quantifier Elimination for Integer-Real Arithmetic\"\n",
       .tag = OptionTag::INFERENCES,
       .experimental = true})
  , _alascaDemodulation("alasca_demodulation",this,false,
      {.short_name = "alasca_demod",
       .description = "Enables the linear arithmetic demodulation rule\n",
       .tag = OptionTag::INFERENCES,
       .experimental = true})
  , _alascaStrongNormalization("alasca_strong_normalziation",this,false,
      {.short_name = "alasca_sn",
       .description = "enables stronger normalizations for inequalities: \n"
            "s >= 0 ==> s > 0 \\/  s == 0\n"
            "s != 0 ==> s > 0 \\/ -s  > 0\n"
            "\n",
       .tag = OptionTag::INFERENCES})
  , _alascaIntegerConversion("alasca_integer_conversion",this,false,
      {.short_name = "alascai",
       .description = "enables converting integer problems into LIRA problems where there is only the sort of reals by"
            "replacing integer variables with floor functions and transforming the signature appropriately"
            "\n",
       .tag = OptionTag::INFERENCES,
       .experimental = true})
  , _alascaAbstraction("alasca_abstraction",this,false,
      {.short_name = "alascaa",
       .description = "Enables the alasca abstraction rule. This is an experimental rule not yet finished."
            "\n",
       .tag = OptionTag::INFERENCES,
       .experimental = true})
  , _cancellation("cancellation",this, ArithmeticSimplificationMode::OFF, {"force", "cautious", "off"},
      {.short_name = "canc",
       .description = "Enables the rule cancellation around additions as described in the paper Making Theory Reasoning Simpler ( https://easychair.org/publications/preprint/K2hb ). \
                                In some rare cases the conclusion may be not strictly simpler than the hypothesis. With `force` we ignore these cases, violating the ordering and just simplifying \
                                anyways. With `cautious` we will generate a new clause instead of simplifying in these cases.",
       .tag = OptionTag::THEORIES})
  , _arithmeticSubtermGeneralizations("arithmetic_subterm_generalizations",this, ArithmeticSimplificationMode::OFF, {"force", "cautious", "off"},
      {.short_name = "asg",
       .description = "\
          Enables various generalization rules for arithmetic terms as described in the paper Making Theory Reasoning Simpler ( https://easychair.org/publications/preprint/K2hb ). \
          In some rare cases the conclusion may be not strictly simpler than the hypothesis. With `force` we ignore these cases, violating the ordering and just simplifying \
          anyways. With `cautious` we will generate a new clause instead of simplifying in these cases.",
       .tag = OptionTag::THEORIES})
  , _holPrinting("pretty_hol_printing",this,
                                     HPrinting::TPTP,
                                     {"raw", "db", "pretty", "tptp"},
      {.short_name = "php",
       .description = "Various methods of printing higher-order terms: \n"
        " -raw : prints the internal representation of terms \n"
        " -pretty : converts internal representation to something resembling textbook notation \n"
        " -tptp : matches tptp standards \n"
        " -db : same as tptp, except that De Bruijn indices printed instead of named variables",
       .tag = OptionTag::HIGHER_ORDER})
  , _choiceAxiom("choice_ax",this,false,
      {.short_name = "cha",
       .description = "Adds the cnf form of the Hilbert choice axiom",
       .tag = OptionTag::HIGHER_ORDER})
  , _injectivity("injectivity",this, false,
      {.short_name = "inj",
       .description = "Attempts to identify injective functions and postulates a left-inverse",
       .tag = OptionTag::HIGHER_ORDER})
  , _choiceReasoning("choice_reasoning",this,false,
      {.short_name = "chr",
       .description = "Reason about choice by adding relevant instances of the axiom",
       .tag = OptionTag::HIGHER_ORDER})
    // TODO we have two ways of enabling function extensionality abstraction atm:
    // this option, and `-uwa`.
    // We should sort this out before merging into master.
  , _functionExtensionality("func_ext",this,FunctionExtensionality::OFF,
                                                                          {"off", "axiom", "abstraction"},
      {.short_name = "fe",
       .description = "Deal with extensionality using abstraction, axiom or neither",
       .tag = OptionTag::HIGHER_ORDER})
  , _clausificationOnTheFly("cnf_on_the_fly",this, CNFOnTheFly::EAGER,
                                                             {"eager",
                                                                "lazy_gen",
                                                                "lazy_simp",
                                                                "lazy_not_gen",
                                                                "lazy_pi_sigma_gen",
                                                                "lazy_not_gen_be_off",
                                                                "lazy_not_be_gen",
                                                                "conj_eager",
                                                                "off"},
      {.short_name = "cnfonf",
       .description = "Various options linked to clausification on the fly",
       .tag = OptionTag::HIGHER_ORDER})
  , _piSet("prim_inst_set",this,PISet::PRAGMATIC,
                                                                        {"all",
                                                                         "all_but_not_eq",
                                                                         "not",
                                                                         "small_set",
                                                                         "pragmatic",
                                                                         "and",
                                                                         "or",
                                                                         "equals",
                                                                         "pi_sigma"},
      {.short_name = "piset",
       .description = "Controls the set of equations to use in primitive instantiation",
       .tag = OptionTag::HIGHER_ORDER})
  , _equalityToEquivalence("equality_to_equiv",this,false,
      {.short_name = "e2e",
       .description = "Equality between boolean terms changed to equivalence \n"
      "t1 : $o = t2 : $o is changed to t1 <=> t2"})
  , _complexBooleanReasoning("complex_bool_reasoning",this,true,
      {.short_name = "cbe",
       .description = "Switches on primitive instantiation and elimination of leibniz equality",
       .tag = OptionTag::HIGHER_ORDER})
  , _booleanEqTrick("bool_eq_trick",this,false,
      {.short_name = "bet",
       .description = "Replace an equality between boolean terms such as: "
    "t = s with a disequality t != vnot(s)"
    " The theory is that this can help with EqRes",
       .tag = OptionTag::HIGHER_ORDER})
  , _heuristicInstantiation("heur_inst",this,false,
      {.short_name = "hi",
       .description = "Heuristically instantiates universally quantified variables with abstractions of literals from negated conjecture",
       .tag = OptionTag::HIGHER_ORDER})
  , _higherOrderUnifDepth("hol_unif_depth",this,2,
      {.short_name = "hud",
       .description = "Set the maximum depth (in terms of projections and imitations) that higher-order unification can descend to."
      "Once limit is reached, remaining pairs are returned as constraints.",
       .tag = OptionTag::HIGHER_ORDER})
  , _casesSimp("cases_simp",this,false,
      {.short_name = "cs",
       .description = "FOOL Paramodulation with two conclusion as a simplification",
       .tag = OptionTag::HIGHER_ORDER})
  , _cases("cases",this,false,
      {.short_name = "c",
       .description = "Alternative to FOOL Paramodulation that replaces all Boolean subterms in one step",
       .tag = OptionTag::HIGHER_ORDER})
  , _newTautologyDel("new_taut_del",this, false,
      {.short_name = "ntd",
       .description = "Delete clauses with literals of the form false != true or t = true \\/ t = false",
       .tag = OptionTag::HIGHER_ORDER})
  , _positiveExt("pos_ext",this,false,
      {.short_name = "pe",
       .description = "Enables the following inference\n"
        "C \\/ t X = s X \n"
        "----------------\n"
        "  C \\/ t = s   \n"
        "where X doesn't occur in t,s or C",
       .tag = OptionTag::HIGHER_ORDER})
  , _iffXorRewriter("iff_xor_rewriter",this,true,
      {.short_name = "ixr",
       .description = "Rewrites p <=> q = $true to p <=> q and the like. It does this as an immediate simplification.",
       .tag = OptionTag::HIGHER_ORDER})
{
//**********************************************************************
//*********************** GLOBAL, for all modes  ***********************
//**********************************************************************

#if VAMPIRE_PERF_EXISTS

  // _simulatedInstructionLimit.onlyUsefulWith(Or(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)),_splittingAvatimer.is(notEqual(1.0f))));
#endif

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

    _sampleStrategy.reliesOn(_mode.is(equal(Mode::VAMPIRE)));

    _randomStrategySeed.reliesOn(_sampleStrategy.is(notEqual(std::string(""))));
    _proof.addHardConstraint(If(equal(Proof::SMTCHECK)).then(_proofExtra.is(equal(ProofExtra::FULL))));

#if VTIME_PROFILING
    _timeStatisticsFocus.onlyUsefulWith(_timeStatistics.is(equal(true)));
#endif // VTIME_PROFILING

//*********************** Input  ***********************

    _guessTheGoalLimit.onlyUsefulWith(_guessTheGoal.is(notEqual(GoalGuess::OFF)));

//*********************** Preprocessing  ***********************

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

    // Captures that if the value is not default then sineSelection must be on
    _sineDepth.onlyUsefulWith(_sineSelection.is(notEqual(SineSelection::OFF)));

    // Captures that if the value is not default then sineSelection must be on
    _sineGeneralityThreshold.onlyUsefulWith(_sineSelection.is(notEqual(SineSelection::OFF)));

    _sineTolerance.addConstraint(Or(equal(-1.0f),greaterThanEq(1.0f) ));
    // Captures that if the value is not 1.0 then sineSelection must be on
    _sineTolerance.onlyUsefulWith(_sineSelection.is(notEqual(SineSelection::OFF)));

    _naming.addProblemConstraint(hasFormulas());
    _naming.addHardConstraint(lessThan(32768));
    _naming.addHardConstraint(greaterThan(-1));
    _naming.addHardConstraint(notEqual(1));

    _newCNF.addProblemConstraint(hasFormulas());
    _newCNF.addProblemConstraint(onlyFirstOrder());

    _inlineLet.onlyUsefulWith(_newCNF.is(equal(true)));

//*********************** Output  ***********************

#if VZ3
    _problemExportSyntax.reliesOn(Or(_exportAvatarProblem.is(notEqual(std::string(""))), _exportThiProblem.is(notEqual(std::string("")))));

    _exportAvatarProblem.onlyUsefulWith(And(_splitting.is(equal(true)), _satSolver.is(equal(Options::SatSolver::Z3))));

    _exportThiProblem.onlyUsefulWith(_theoryInstAndSimp.is(notEqual(TheoryInstSimp::OFF)));

#endif

//************************************************************************
//*********************** VAMPIRE (includes CASC)  ***********************
//************************************************************************

//*********************** Saturation  ***********************

    // make the next hard - RSTC will make FMB crash (as RSTC correctly does not trigger hadIncompleteTransformation; still it probably does not make sense to use ep with fmb)
    _saturationAlgorithm.addHardConstraint(If(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)).then(_equalityProxy.is(notEqual(EqualityProxy::RSTC))));

    // TheoryAxioms::applyFOOL leaves out the boolean domain axiom when this is on, relying on
    // the rule to do that job instead. FMB has no such rule, so it would happily build a
    // boolean domain of three or more elements.
    _FOOLParamodulation.addHardConstraint(If(equal(true)).then(
      _saturationAlgorithm.is(notEqual(SaturationAlgorithm::FINITE_MODEL_BUILDING))));

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

    _fmbAdjustSorts.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbAdjustSorts.addHardConstraint(
      If(equal(FMBAdjustSorts::EXPAND)).then(_fmbEnumerationStrategy.is(notEqual(FMBEnumerationStrategy::CONTOUR))));

    _fmbDetectSortBounds.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbDetectSortBounds.addHardConstraint(If(equal(true)).then(_fmbAdjustSorts.is(notEqual(FMBAdjustSorts::PREDICATE))));
    _fmbDetectSortBounds.addHardConstraint(If(equal(true)).then(_fmbAdjustSorts.is(notEqual(FMBAdjustSorts::FUNCTION))));

    _fmbDetectSortBoundsTimeLimit.onlyUsefulWith(_fmbDetectSortBounds.is(equal(true)));

    _fmbSizeWeightRatio.onlyUsefulWith(_fmbEnumerationStrategy.is(equal(FMBEnumerationStrategy::CONTOUR)));
    _fmbSizeWeightRatio.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbEnumerationStrategy.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));

    // for an example where this helps try "-sa fmb -fmbas expand Problems/KRS/KRS185+1.p"
    _fmbKeepSbeamGenerators.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbKeepSbeamGenerators.onlyUsefulWith(_fmbEnumerationStrategy.is(equal(FMBEnumerationStrategy::SBMEAM)));

    _fmbUseSimplifyingSolver.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::FINITE_MODEL_BUILDING)));
    _fmbUseSimplifyingSolver.onlyUsefulWith(_satSolver.is(equal(SatSolver::MINISAT)));
    _selection.onlyUsefulWith2(ProperSaturationAlgorithm());

    _lookaheadDelay.onlyUsefulWith(_selection.isLookAheadSelection());

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

     // Under lrd=off:lpd=off, we don't have any LRS anymore (and are back to Otter, essentially), so the value of this option is questionable.
     // (Still, it's currently used in a few strategies in Schedules.)
    _lrsPreemptiveDeletes.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));

    _simulatedTimeLimit.onlyUsefulWith(Or(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)),_splittingAvatimer.is(notEqual(1.0f))));
    _lrsEstimateCorrectionCoef.addConstraint(greaterThan(0.0f));
    _lrsEstimateCorrectionCoef.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));

    _lrsSaveTraceFile.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));

    _lrsLoadTraceFile.onlyUsefulWith(_saturationAlgorithm.is(equal(SaturationAlgorithm::LRS)));

  //*********************** Inferences  ***********************

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

    _structInduction.onlyUsefulWith(Or(_induction.is(equal(Induction::STRUCTURAL)),_induction.is(equal(Induction::BOTH))));
    _structInduction.addHardConstraint(If(equal(StructuralInductionKind::RECURSION)).then(_newCNF.is(equal(true))));
    _structInduction.addHardConstraint(If(equal(StructuralInductionKind::RECURSION)).then(_equalityResolutionWithDeletion.is(equal(true))));
    _structInduction.addHardConstraint(If(equal(StructuralInductionKind::ALL)).then(_newCNF.is(equal(true))));
    _structInduction.addHardConstraint(If(equal(StructuralInductionKind::ALL)).then(_equalityResolutionWithDeletion.is(equal(true))));

    _intInduction.onlyUsefulWith(Or(_induction.is(equal(Induction::INTEGER)),_induction.is(equal(Induction::BOTH))));
    _inductionSkolemOnly.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));

    _inductionGoalClausesOnly.onlyUsefulWith(_induction.is(notEqual(Induction::NONE)));

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

//*********************** Higher-order  ***********************

    _choiceAxiom.addProblemConstraint(hasHigherOrder());

    _choiceReasoning.addProblemConstraint(hasHigherOrder());
    _choiceReasoning.onlyUsefulWith(_choiceAxiom.is(equal(false))); //no point having two together

    _injectivity.addProblemConstraint(hasHigherOrder());

    _functionExtensionality.addProblemConstraint(hasHigherOrder());

    _clausificationOnTheFly.addProblemConstraint(hasHigherOrder());

    _piSet.addProblemConstraint(hasHigherOrder());

    _complexBooleanReasoning.addProblemConstraint(hasHigherOrder());

    _heuristicInstantiation.onlyUsefulWith(ProperSaturationAlgorithm());
    _heuristicInstantiation.addProblemConstraint(hasHigherOrder());   
    _heuristicInstantiation.addHardConstraint(If(notEqual(false)).then(_clausificationOnTheFly.is(equal(CNFOnTheFly::CONJ_EAGER)))); 

    _higherOrderUnifDepth.addProblemConstraint(hasHigherOrder());    
    _higherOrderUnifDepth.addHardConstraint(lessThan(100u));

    _casesSimp.onlyUsefulWith(_cases.is(equal(false)));

    //TODO, sort out the mess with cases and FOOLP.
    //One should be removed. AYB
    _cases.onlyUsefulWith(_casesSimp.is(equal(false)));

    _positiveExt.addProblemConstraint(hasHigherOrder());   
    _positiveExt.onlyUsefulWith(_functionExtensionality.is(notEqual(FunctionExtensionality::AXIOM)));

    _iffXorRewriter.addProblemConstraint(hasHigherOrder());

//*********************** InstGen  ***********************
// TODO not really InstGen any more, just global subsumption

    _globalSubsumption.onlyUsefulWith(ProperSaturationAlgorithm());
    // _globalSubsumption.addProblemConstraint(mayHaveNonUnits()); - this is too strict, think of a better one

//*********************** AVATAR  ***********************

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

//*********************** SAT solver (used in various places)  ***********************
#if VZ3
    _satSolver.addHardConstraint(If(equal(SatSolver::Z3)).then(_saturationAlgorithm.is(notEqual(SaturationAlgorithm::FINITE_MODEL_BUILDING))));
#endif
    _satSolver.onlyUsefulWith(_splitting.is(equal(true)));

#if VZ3

    _satFallbackForSMT.addProblemConstraint(hasTheories()); // Z3 won't be incomplete for pure FOL
    _satFallbackForSMT.onlyUsefulWith(_satSolver.is(equal(SatSolver::Z3)));
#endif

    //*************************************************************
    //*********************** which mode or tag?  ************************
    //*************************************************************

    _increasedNumeralWeight.onlyUsefulWith(ProperSaturationAlgorithm());

    _literalComparisonMode.onlyUsefulWith(ProperSaturationAlgorithm());
    _literalComparisonMode.addProblemConstraint(mayHaveNonUnits());
    _literalComparisonMode.addProblemConstraint(notJustEquality());

    _nonGoalWeightCoefficient.onlyUsefulWith(ProperSaturationAlgorithm());

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
} // Options::Options()

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
  size_t len = strlen(name);
  if(!len)
    return similar_names;

  while(options.hasNext()){
    AbstractOptionValue* opt = options.next();
    auto opt_name = is_short ? opt->shortName : opt->longName;
    size_t dif = 2;
    if(!is_short) dif += len/4;
    if(opt_name && StringUtils::distance(name,opt_name) < dif)
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
