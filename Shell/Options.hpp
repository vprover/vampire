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
 * @file Options.hpp
 * Defines Vampire options.
 *
 * INSTRUCTIONS on Adding a new Option
 *
 * Firstly, the easiest thing to do is copy what's been done for an existing option.
 * Most options can be added to the FOR_EACH_VAMPIRE_OPTION table below.
 *
 * In Options.hpp
 * - Add a row to the FOR_EACH_VAMPIRE_OPTION table
 * - Add enum for choices if it's a ChoiceOptionValue
 * - Add getter for OptionValue
 *
 * In Options.cpp
 * - Add value constraints, they can be soft or hard (see NOTE on OptionValueConstraints below)
 * - Add problem constraints (see NOTE on OptionProblemConstraints)
 *
 * You can also add options manually if they don't fit in the FOR_EACH_VAMPIRE_OPTION metaphor.
 */

#ifndef __Options__
#define __Options__

#include <memory>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Int.hpp"
#include "Lib/Portability.hpp"

#ifndef VAMPIRE_CLAUSE_TRACING
#  if VDEBUG
#    define VAMPIRE_CLAUSE_TRACING 1
#  else
#    define VAMPIRE_CLAUSE_TRACING 0
#  endif
#endif // VAMPIRE_CLAUSE_TRACINGE

namespace Shell {

using namespace Lib;
using namespace Kernel;

class Property;

/**
 * Possible tags to group options by
 * Update _tagNames at the end of Options constructor if you add a tag
 * @author Giles
 */
enum class OptionTag : unsigned int {
    UNUSED,
    OTHER,
    DEVELOPMENT,
    OUTPUT,
    PORTFOLIO,
    FMB,
    SAT,
    AVATAR,
    INFERENCES,
    INDUCTION,
    THEORIES,
    LRS,
    SATURATION,
    PREPROCESSING,
    INPUT,
    HELP,
    HIGHER_ORDER,
    LAST_TAG // Used for counting the number of tags
};
// update _tagNames at the end of Options constructor if you add a tag

/**
 * NOTE on OptionProblemConstraint
 *
 * OptionProblemConstraints are used to capture properties of a problem that
 * should be present when an option is used. The idea being that a warning will
 * be emitted if an option is used for an inappropriate problem.
 *
 * TODO - this element of Options is still under development
 * TODO consider merging problem and value constraints?
 */
struct OptionProblemConstraint {
  virtual bool check(Property* p) = 0;
  virtual std::string msg() = 0;
  virtual ~OptionProblemConstraint() = default;
};

using OptionProblemConstraintUP = std::unique_ptr<OptionProblemConstraint>;

// break cycle: OptionValueConstraint has methods which take an OptionValue<T> &
// ...but also OptionValue keep some constraints around
template<typename T> struct OptionValue;

/**
* NOTE on OptionValueConstraints
*
* OptionValueConstraints are used to declare constraints on and between option values
* these are checked in checkGlobalOptionConstraints, which should be called after
* Options is updated
*
* As usual, see Options.cpp for examples.
*
* There are two kinds of ValueConstraints (see below for ProblemConstraints)
*
* - Unary constraints such as greaterThan, equals, ...
* - If-then constraints that capture dependencies
*
* In both cases an attempt has been made to make the declaration of constraints
* in Options.cpp as readable as possible. For example, an If-then constraint is
* written as follows
*
*  If(equals(0)).then(_otherOption.is(lessThan(5)))
*
* Note that the equals(0) will apply to the OptionValue that the constraint belongs to (!!)
*/

template<typename T>
struct OptionValueConstraint {
  virtual ~OptionValueConstraint() = default;

  virtual bool check(const OptionValue<T>& value) = 0;
  virtual std::string msg(const OptionValue<T>& value) = 0;

  // By default cannot force constraint
  virtual bool force(OptionValue<T>* value){ return false;}
  bool hard = false;
};

template<typename T>
using OptionValueConstraintUP = std::unique_ptr<OptionValueConstraint<T>>;

/**
 * An AbstractOptionValue includes all the information and functionality that does not
 * depend on the type of the stored option. This is inherited by the templated OptionValue.
 *
 * The main purpose of the AbstractOptionValue is to allow us to have a collection of pointers
 * to OptionValue objects
 *
 * @author Giles
 */
struct AbstractOptionValue {
    AbstractOptionValue(const char *l,const char *s)
        // treat empty short names as nullptr
        : longName(l), shortName(s && *s ? s : nullptr) {}

    // Never copy/move an OptionValue... the Constraint system would break
    AbstractOptionValue(const AbstractOptionValue&) = delete;
    AbstractOptionValue& operator=(const AbstractOptionValue&) = delete;
    AbstractOptionValue(AbstractOptionValue&&) = delete;
    AbstractOptionValue& operator=(AbstractOptionValue&&) = delete;

    virtual ~AbstractOptionValue() = default;

    // This is the main method, it sets the value of the option using an input string
    // Returns false if we cannot set (will cause a UserError in Options::set)
    virtual bool setValue(const std::string& value) = 0;

    bool set(const std::string& value, bool dont_touch_if_defaulting = false) {
      bool okay = setValue(value);
      if (okay && (!dont_touch_if_defaulting || !isDefault())) {
        is_set=true;
      }
      return okay;
    }

    // Checking constraints
    virtual bool checkConstraints() = 0;

    // Problem constraints place a restriction on problem properties and option values
    void addProblemConstraint(OptionProblemConstraintUP c){ _prob_constraints.push(std::move(c)); }
    bool checkProblemConstraints(Property* prop);

    // This allows us to get the actual value in string form
    virtual std::string getStringOfActual() const = 0;
    // Check if default value
    virtual bool isDefault() const = 0;

    // For use in showOptions and explainOption
    virtual void output(std::ostream &out, bool linewrap) const;

    const char *longName = nullptr;
    const char *shortName = nullptr;
    const char *description = nullptr;
    bool experimental = false;
    bool is_set = false;

    // Tagging: options can be filtered by mode and are organised by Tag in showOptions
    OptionTag tag = OptionTag::LAST_TAG;

private:
    Lib::Stack<OptionProblemConstraintUP> _prob_constraints;
};

/**
 * The templated OptionValue is used to store default and actual values for options
 *
 * There are also type-related helper functions
 *
 * @author Giles
 */
template<typename T>
struct OptionValue : public AbstractOptionValue {
    OptionValue(const char *l, const char *s,T def) : AbstractOptionValue(l,s),
    defaultValue(def), actualValue(def){}

    // We store the defaultValue separately so that we can check if the actualValue is non-default
    T defaultValue;
    T actualValue;

    bool isDefault() const override { return defaultValue==actualValue;}

    // Getting the string versions of values, useful for output
    virtual std::string getStringOfValue(T value) const { ASSERTION_VIOLATION; }
    std::string getStringOfActual() const override { return getStringOfValue(actualValue); }

    // Adding and checking constraints
    // By default constraints are soft and reaction to them is controlled by the bad_option option
    // But a constraint can be added as Hard, meaning that it always causes a UserError
    template<typename C>
    void addConstraint(C c);
    template<typename C>
    void addHardConstraint(C c);

    // A onlyUsefulWith constraint gives a constraint that must be true if this option's value is set
    // For example, split_at_activation is only useful with splitting being on
    template<typename C>
    void onlyUsefulWith(C c);

    // similar to onlyUsefulWith, except the trigger is a non-default value
    // (as opposed to the explicitly-set flag)
    // we use it for selection and awr which cannot be not set via the decode string
    // TODO why not? ott+11_5:1_.... seems alright to me
    template<typename C>
    void onlyUsefulWith2(C c);

    // similar to onlyUsefulWith2, except its a hard constraint,
    // so that the user is strongly aware of situations when changing the
    // respective option has no effect
    template<typename C>
    void reliesOn(C c);

    // This checks the constraints and may cause a UserError
    bool checkConstraints() override;

    // Produces a separate constraint object based on this option
    /// Useful for IfThen constraints and onlyUsefulWith i.e. _splitting.is(equal(true))
    template<typename C>
    auto is(C c);

    void output(std::ostream& out, bool linewrap) const override {
        AbstractOptionValue::output(out,linewrap);
        out << "\tdefault: " << getStringOfValue(defaultValue) << std::endl;
    }

private:
    Lib::Stack<OptionValueConstraintUP<T>> _constraints;
};

/**
 * Class that represents Vampire's options.
 * 11/11/2004 Shrigley Hall, completely reimplemented
 *
 * @since Sep 14 reimplemented by Giles
 */
class Options
{
public:
    Options();

    /* Options must not be moved or copied:
     * the constraints in each OptionValueConstraint point to other options! */
    Options(const Options& that) = delete;
    Options& operator=(const Options& that) = delete;
    Options(Options&& that) = delete;
    Options& operator=(Options&& that) = delete;

    // used to print help and options
    void output (std::ostream&) const;

    // Dealing with encoded options. Used by --decode option
    void readFromEncodedOptions (std::string testId);
    void readOptionsString (std::string testId,bool assign=true);
    std::string generateEncodedOptions() const;

    // compile away auto-values; called BEFORE preprocessing
    void resolveAwayAutoValues0();
    // compile away auto-values; called after preprocessing, when Problem's prop reflect precise state of affairs
    void resolveAwayAutoValues(const Problem&);

    // deal with completeness
    bool complete(const Problem&) const;

    // deal with constraints
    void setForcedOptionValues(); // not currently used effectively
    bool checkGlobalOptionConstraints(bool fail_early=false);
    bool checkProblemOptionConstraints(Property*, bool before_preprocessing, bool fail_early=false);

    /**
     * Sample a random strategy from a distribution described by the given file.
     *
     * The format of the sampler file should be easy to understand (Look for examples samplerFOL.txt, samplerFNT.txt, samplerSMT.txt under vampire root).
     * The file describes a sequence of sampling rules (one on each line, barring empty lines and comment lines starting with a #),
     * which are executed in order, and each rule (provided its preconditions are satisfied) triggers
     * sampling of a value for a particular option from a specified distribution.
     * The most common sampler is for the categorical distribution (~cat), which is specified by a list of values with corresponding integer frequencies.
     * Other samplers include ratios, uniform floats and integers, and a (shifted) geometric distribution for potentially unbounded integers.
     * A notable feature is the ability to sample also fake (non-existent) options, recognized by a $-sign prefixed, whose value can later be reference in the conditions.
     *
     * Example:
     *
     * # naming
     * > $nm ~cat Z:1,NZ:5
     * $nm=Z > nm ~cat 0:1
     * $nm=NZ > nm ~sgd 0.07,2
     *
     * First samples a fake option $nm with either a value Z (1 out of 6) or Nz (5 out of 6).
     * Then, if $nm is set to Z samples the (actual) naming option with value 0 (nm ~cat 0:1 is simply an assignment to the effect of nm := 0),
     * and if $nm is set to NZ, samples from a shifted geometric distribution with p=0.07 and a shift=2. (So 2 gets selected with a probability p,
     * 3 with a probability p(1-p), ... and 2+i with a probability p(1-p)^i).
     */
    void sampleStrategy(const std::string& samplerFileName, DHMap<std::string,std::string, FnvHash, LengthHash> fakes = DHMap<std::string,std::string, FnvHash, LengthHash>());

    /**
     * Return the problem name
     *
     * The problem name is computed from the input file name in
     * the @b setInputFile function. If the input file is not set,
     * the problem name is equal to "unknown".
     */
    std::string problemName = "unknown";

    void setInputFile(const std::string& newVal){ _inputFile.set(newVal); }

    // standard ways of setting options
    void set(const std::string& name, const std::string& value); // implicitly the long version used here
    void set(const char* name, const char* value, bool longOpt);

public:
  //==========================================================
  // The Enums for Option Values
  //==========================================================
  //
  // If you create a ChoiceOptionValue you will also need to create an enum

  enum class TheoryInstSimp : unsigned int {
    OFF,
    ALL,    // select all interpreted
    STRONG, // select strong only
    NEG_EQ, // select only positive equalities
    OVERLAP,
    FULL,   // <-+- deprecated. only exists to not break portfolio modes. behaves exactly like `ALL` now
    NEW,    // <-+
  };
  enum class UnificationWithAbstraction : unsigned int {
    AUTO,
    OFF,
    INTERP_ONLY,
    ONE_INTERP,
    CONSTANT,
    ALL,
    GROUND,
    FUNC_EXT,
    ALASCA_ONE_INTERP,
    ALASCA_CAN_ABSTRACT,
    ALASCA_MAIN,
    ALASCA_MAIN_FLOOR,
    HOL,
  };
  friend std::ostream& operator<<(std::ostream& out, UnificationWithAbstraction const& self)
  {
    switch (self) {
      case UnificationWithAbstraction::AUTO:              return out << "auto";
      case UnificationWithAbstraction::OFF:               return out << "off";
      case UnificationWithAbstraction::INTERP_ONLY:       return out << "interp_only";
      case UnificationWithAbstraction::ONE_INTERP:        return out << "one_interp";
      case UnificationWithAbstraction::CONSTANT:          return out << "constant";
      case UnificationWithAbstraction::ALL:               return out << "all";
      case UnificationWithAbstraction::GROUND:            return out << "ground";
      case UnificationWithAbstraction::FUNC_EXT:          return out << "func_ext";
      case UnificationWithAbstraction::ALASCA_ONE_INTERP:   return out << "alasca_one_interp";
      case UnificationWithAbstraction::ALASCA_CAN_ABSTRACT: return out << "alasca_can_abstract";
      case UnificationWithAbstraction::ALASCA_MAIN:         return out << "alasca_main";
      case UnificationWithAbstraction::ALASCA_MAIN_FLOOR:   return out << "alasca_floor";
      case UnificationWithAbstraction::HOL:               return out << "hol";
    }
    ASSERTION_VIOLATION
  }

  enum class Induction : unsigned int {
    NONE,
    STRUCTURAL,
    INTEGER,
    BOTH
  };
  enum class StructuralInductionKind : unsigned int {
    ONE,
    TWO,
    THREE,
    RECURSION,
    ALL
  };
  enum class IntInductionKind : unsigned int {
    ONE,
    TWO
  };
  enum class IntegerInductionInterval : unsigned int {
    INFINITE,
    FINITE,
    BOTH
  };
  enum class IntegerInductionLiteralStrictness: unsigned int {
    NONE,
    TOPLEVEL_NOT_IN_OTHER,
    ONLY_ONE_OCCURRENCE,
    NOT_IN_BOTH,
    ALWAYS
  };
  enum class IntegerInductionTermStrictness: unsigned int {
    NONE,
    INTERPRETED_CONSTANT,
    NO_SKOLEMS
  };

  enum class PredicateSineLevels : unsigned int {
    NO,   // no means 1) the reverse of "on", 2) use with caution, it is predicted to be the worse value
    OFF,
    ON
  };


  enum class InductionChoice : unsigned int {
    ALL,
    GOAL,                     // only apply induction to goal constants
                              // a goal constant is one appearing in an explicit goal, or if gtg is used
                              // a constant that is used to lift a clause to a goal (uniqueness or Skolem)
    GOAL_PLUS,                // above plus skolem terms introduced in induction inferences
  };

  enum class DemodulationRedundancyCheck : unsigned int {
    OFF,       // no check
    ORDERING,  // solely ordering-based check
    ENCOMPASS, // (1) positive unit equations (PUE) are smaller than non-PUE clauses,
               // (2) more general PUE are smaller than less general PUE, and
               // (3) equally general PUEs are ordered based on term ordering.
  };

  enum class TheoryAxiomLevel : unsigned int {
    ON,  // all of them
    OFF, // none of them
    CHEAP
  };

  enum class ProofExtra : unsigned int {
    OFF,
    FREE,
    FULL
  };
  enum class FMBWidgetOrders : unsigned int {
    FUNCTION_FIRST, // f(1) f(2) f(3) ... g(1) g(2) ...
    ARGUMENT_FIRST, // f(1) g(1) h(1) ... f(2) g(2) ...
    DIAGONAL,       // f(1) g(2) h(3) f(2) g(3) h(1) f(3) g(1) h(2)
  };
  enum class FMBSymbolOrders : unsigned int {
    OCCURRENCE,
    INPUT_USAGE,
    PREPROCESSED_USAGE
  };
  enum class FMBAdjustSorts : unsigned int {
    OFF,
    EXPAND,
    GROUP,
    PREDICATE,
    FUNCTION
  };
  enum class FMBEnumerationStrategy : unsigned int {
    SBMEAM,
#if VZ3
    SMT,
#endif
    CONTOUR
  };

  enum class BadOption : unsigned int {
    HARD,
    FORCED,
    OFF,
    SOFT
  };

  enum class IgnoreMissing : unsigned int {
    ON,
    OFF,
    WARN
  };

  /**
   * Possible values for function_definition_elimination.
   * @since 29/05/2004 Manchester
   */
  enum class FunctionDefinitionElimination : unsigned int {
    ALL = 0,
    NONE = 1,
    UNUSED = 2
  };

  /**
   * Possible values for predicate_elimination.
   */
  enum class PredicateElimination : unsigned int {
    OFF = 0,
    ON = 1,
    MULTI = 2
  };

  /**
   * Possible values for the input syntax
   * @since 26/08/2009 Redmond
   */
  enum class InputSyntax : unsigned int {
    SMTLIB2 = 0,
    /** syntax of the TPTP prover */
    TPTP = 1,
    AUTO = 2
    //HUMAN = 4,
    //MPS = 5,
    //NETLIB = 6
  };

  /**
   * Possible values for mode_name.
   * @since 06/05/2007 Manchester
   */
  enum class Mode : unsigned int {
    AXIOM_SELECTION,
    CASC,
    CLAUSIFY,
    CONSEQUENCE_ELIMINATION,
    MODEL_CHECK,
    /** this mode only outputs the input problem, without any preprocessing */
    OUTPUT,
    PORTFOLIO,
    PREPROCESS,
    PREPROCESS2,
    PROFILE,
    SMTCOMP,
    SPIDER,
    TCLAUSIFY,
    TPREPROCESS,
    VAMPIRE
  };

  enum class Intent : unsigned int {
    UNSAT, // preferentially look for refutations, proofs, arguments of unsatisfiability etc.
    SAT    // preferentially look for (finite) models, saturations, etc.
  };

  enum class Schedule : unsigned int {
    CASC,
    CASC_2024,
    CASC_2025,
    CASC_SAT,
    CASC_SAT_2024,
    CASC_SAT_2025,
    FILE,
    INDUCTION,
    INTEGER_INDUCTION,
    INTIND_OEIS,
    LTB_DEFAULT_2017,
    LTB_HH4_2017,
    LTB_HLL_2017,
    LTB_ISA_2017,
    LTB_MZR_2017,
    SMTCOMP,
    SMTCOMP_2018,
    SNAKE_TPTP_UNS,
    SNAKE_TPTP_SAT,
    STRUCT_INDUCTION,
    STRUCT_INDUCTION_TIP
  };

/* TODO: use an enum for Selection. The current issue is the way these values are manipulated as ints
 *
  enum class Selection : unsigned int {
    TOTAL,
    MAXIMAL,
    TWO,
    THREE,
    FOUR,
    TEN,
    LOOKAHEAD,
    BEST_TWO,
    BEST_THREE,
    BEST_FOUR,
    BEST_TEN,
    BEST_LOOKAHED
  }
*/

  /** Various options for the output of statistics in Vampire */
  enum class Statistics : unsigned int {
    /** changed by the option "--statistics brief" */
    BRIEF = 0,
    /** changed by the option "--statistics full */
    FULL = 1,
    /** changed by the option "--statistics off" */
    NONE = 2
  };

  /** how much we want vampire talking and in what language */
  enum class Output : unsigned int {
    SMTCOMP,
    SPIDER,
    SZS,
    VAMPIRE,
    UCORE
  };

  /** Possible values for sat_solver */
  enum class SatSolver : unsigned int {
     MINISAT = 0,
     CADICAL = 1
#if VZ3
     ,Z3 = 2
#endif
  };

  /** Possible values for saturation_algorithm */
  enum class SaturationAlgorithm : unsigned int {
     DISCOUNT,
     FINITE_MODEL_BUILDING,
     LRS,
     OTTER,
     Z3
   };

  /** Possible values for activity of some inference rules */
  enum class RuleActivity : unsigned int {
    INPUT_ONLY = 0,
    OFF = 1,
    ON = 2
  };

  enum class QuestionAnsweringMode : unsigned int {
    AUTO = 0,
    PLAIN = 1,
    SYNTHESIS = 2,
    OFF = 3
  };

  enum class InterpolantMode : unsigned int {
    NEW_HEUR,
#if VZ3
    NEW_OPT,
#endif
    OFF,
  };

  enum class LiteralComparisonMode : unsigned int {
    PREDICATE = 0,
    REVERSE = 1,
    STANDARD = 2
  };

  enum class Condensation : unsigned int {
    FAST = 0,
    OFF = 1,
    ON = 2
  };

  enum class Demodulation : unsigned int {
    ALL = 0,
    OFF = 1,
    PREORDERED = 2
  };

  enum class Subsumption : unsigned int {
    OFF = 0,
    ON = 1,
    UNIT_ONLY = 2
  };

  enum class URResolution : unsigned int {
    EC_ONLY = 0,
    OFF = 1,
    ON = 2,
    FULL = 3
  };

  enum class TermOrdering : unsigned int {
    AUTO_KBO = 0,
    KBO = 1,
    QKBO = 2,
    LAKBO = 3,
    LPO = 4,
    ALL_INCOMPARABLE = 5,
  };

  enum class SymbolPrecedence : unsigned int {
    ARITY = 0,
    OCCURRENCE = 1,
    REVERSE_ARITY = 2,
    UNARY_FIRST = 3,
    CONST_MAX = 4,
    CONST_MIN = 5,
    SCRAMBLE = 6,
    FREQUENCY = 7,
    UNARY_FREQ = 8,
    CONST_FREQ = 9,
    REVERSE_FREQUENCY = 10,
  };
  enum class SymbolPrecedenceBoost : unsigned int {
    NONE = 0,
    GOAL = 1,
    UNITS = 2,
    GOAL_THEN_UNITS = 3,
    NON_INTRO = 4,
    INTRO = 5,
  };
  enum class IntroducedSymbolPrecedence : unsigned int {
    TOP = 0,
    BOTTOM = 1
  };

  enum class SineSelection : unsigned int {
    AXIOMS = 0,
    INCLUDED = 1,
    OFF = 2
  };

  enum class Proof : unsigned int {
    OFF = 0,
    ON = 1,
    PROOFCHECK = 2,
    TPTP = 3,
    PROPERTY = 4,
    SMT2_PROOFCHECK = 5,
    SMTCHECK = 6
  };

  /** Values for --equality_proxy */
  enum class EqualityProxy : unsigned int {
    R = 0,
    RS = 1,
    RST = 2,
    RSTC = 3,
    OFF = 4,
  };

  /** Values for --extensionality_resolution */
  enum class ExtensionalityResolution : unsigned int {
    FILTER = 0,
    KNOWN = 1,
    TAGGED = 2,
    OFF = 3
  };

  enum class SplittingLiteralPolarityAdvice : unsigned int {
    FALSE,
    TRUE,
    NONE,
    RANDOM
  };

  enum class SplittingDeleteDeactivated : unsigned int {
    ON,
    LARGE_ONLY,
    OFF
  };

  enum class SplittingAddComplementary : unsigned int {
    GROUND = 0,
    NONE = 1
  };

  enum class SplittingNonsplittableComponents : unsigned int {
    ALL = 0,
    ALL_DEPENDENT = 1,
    KNOWN = 2,
    NONE = 3
  };

  enum class TweeGoalTransformation : unsigned int {
    OFF = 0,
    GROUND = 1,
    FULL = 2
  };

  enum class Sos : unsigned int{
    ALL = 0,
    OFF = 1,
    ON = 2,
    THEORY = 3
  };

  enum class TARules : unsigned int {
    OFF = 0,
    INJECTGEN = 1,
    INJECTSIMPL = 2,
    INJECTOPT = 2,
    FULL = 3
  };

  enum class TACyclicityCheck : unsigned int {
    OFF = 0,
    AXIOM = 1,
    RULE = 2,
    RULELIGHT = 3
  };

  enum class GoalGuess : unsigned int {
    OFF = 0,
    ALL = 1,
    EXISTS_TOP = 2,
    EXISTS_ALL = 3,
    EXISTS_SYM = 4,
    POSITION = 5
  };

  enum class EvaluationMode : unsigned int {
    OFF,
    SIMPLE,
    POLYNOMIAL_FORCE,
    POLYNOMIAL_CAUTIOUS,
  };

  enum class ArithmeticSimplificationMode : unsigned int {
    FORCE,
    CAUTIOUS,
    OFF,
  };

  enum class KboWeightGenerationScheme : unsigned int {
    CONST = 0,
    RANDOM = 1,
    ARITY = 2,
    INV_ARITY = 3,
    ARITY_SQUARED = 4,
    INV_ARITY_SQUARED = 5,
    PRECEDENCE = 6,
    INV_PRECEDENCE = 7,
    FREQUENCY = 8,
    INV_FREQUENCY = 9,
  };

  enum class KboAdmissibilityCheck : unsigned int {
    ERROR = 0,
    WARNING = 1,
  };

  enum class FunctionExtensionality : unsigned int {
    OFF = 0,
    AXIOM = 1,
    ABSTRACTION = 2
  };

  enum class CNFOnTheFly : unsigned int {
    EAGER = 0,
    LAZY_GEN = 1,
    LAZY_SIMP = 2,
    LAZY_SIMP_NOT_GEN = 3,
    LAZY_SIMP_PI_SIGMA_GEN = 4,
    LAZY_SIMP_NOT_GEN_BOOL_EQ_OFF = 5,
    LAZY_SIMP_NOT_GEN_BOOL_EQ_GEN = 6,
    CONJ_EAGER = 7,
    OFF = 8
  };

  enum class PISet : unsigned int {
    ALL = 0,
    ALL_EXCEPT_NOT_EQ = 1,
    NOT = 2,
    NOT_EQ_NOT_EQ = 3,
    PRAGMATIC = 4,
    AND = 5,
    OR = 6,
    EQUALS = 7,
    PI_SIGMA = 8
  };

  enum class ProblemExportSyntax : unsigned int {
    SMTLIB = 0,
    API_CALLS = 1,
  };

  enum class HPrinting : unsigned int {
    RAW = 0,
    DB_INDICES = 1,
    PRETTY = 2,
    TPTP = 3
  };

// ----------------------------------------------------------------------
// Helper macros used to conditionally include a row of the option table
// below when the corresponding preprocessor feature is compiled in.
// (A disabled VAMPIRE_IF_* discards its argument entirely, so the whole
// row -- and the comma/semicolon it produces at each use site -- simply
// vanishes; there is no need to also wrap the row in #if/#endif.)
#if VZ3
#  define VAMPIRE_IF_VZ3(...) __VA_ARGS__
#else
#  define VAMPIRE_IF_VZ3(...)
#endif
#if VAMPIRE_PERF_EXISTS
#  define VAMPIRE_IF_PERF(...) __VA_ARGS__
#else
#  define VAMPIRE_IF_PERF(...)
#endif
#if VAMPIRE_CLAUSE_TRACING
#  define VAMPIRE_IF_CLAUSE_TRACING(...) __VA_ARGS__
#else
#  define VAMPIRE_IF_CLAUSE_TRACING(...)
#endif
#if VTIME_PROFILING
#  define VAMPIRE_IF_TIME_PROFILING(...) __VA_ARGS__
#else
#  define VAMPIRE_IF_TIME_PROFILING(...)
#endif

// Turns a parenthesised token list back into a plain comma-separated one,
// e.g. `VAMPIRE_EXPAND_CHOICES ("a","b","c")` expands to `"a","b","c"`.
// Used to smuggle a choice list (which contains top-level commas) through
// the argument list of a single macro invocation below.
#define VAMPIRE_EXPAND_CHOICES(...) __VA_ARGS__

/**
 * X-macro table of Vampire's options.
*
 * A handful of options are not listed here, because they need idiosyncratic
 * construction or storage. These are declared, constructed and registered by hand.
 *
 * To add a new option: add a row below (BOOL/INT/UNSIGNED/FLOAT/LONG/STRING
 * for scalars, CHOICE for an enum-valued option -- which also needs an enum defined
 * above, as before), then follow the remaining INSTRUCTIONS at the top of this file
 * (value constraints, problem constraints, ...) at the option's use site.
 *
 * BOOL/INT/UNSIGNED/FLOAT/LONG/STRING(member, longName, shortName, defaultValue, description, tag, experimental)
 * CHOICE(enumType, member, longName, shortName, defaultValue, choices, description, tag, experimental)
 *   `choices` is a parenthesised list of string literals, e.g. ("a","b","c")
 */
#define FOR_EACH_VAMPIRE_OPTION(BOOL, INT, UNSIGNED, FLOAT, LONG, STRING, CHOICE) \
  BOOL(_encode, "encode", "", false, \
    "Output an encoding of the strategy to be used with the decode option", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_useTheorySplitQueues, "theory_split_queue", "thsq", false, \
    "Turn on clause selection using multiple queues containing different clauses (split by " \
    "amount of theory reasoning)", \
    OptionTag::SATURATION, false) \
  \
  STRING(_theorySplitQueueRatios, "theory_split_queue_ratios", "thsqr", "1,1", \
    "The ratios for picking clauses from the split-queues using weighted round robin. If " \
    "a queue is empty, the clause will be picked from the next non-empty queue to the right. " \
    "Note that this option implicitly also sets the number of queues.", \
    OptionTag::SATURATION, false) \
  \
  STRING(_theorySplitQueueCutoffs, "theory_split_queue_cutoffs", "thsqc", "0", \
    "The cutoff-values for the split-queues (the cutoff value for the last queue has to be " \
    "omitted, as it is always infinity). Any split-queue contains all clauses which are assigned " \
    "a feature-value less or equal to the cutoff-value of the queue. If no custom value for " \
    "this option is set, the implementation will use cutoffs 0,4*d,10*d,infinity (where d " \
    "denotes the theory split queue expected ratio denominator).", \
    OptionTag::SATURATION, false) \
  \
  INT(_theorySplitQueueExpectedRatioDenom, "theory_split_queue_expected_ratio_denom", "thsqd", 8, \
    "The denominator n such that we expect the final proof to have a ratio of theory-axioms " \
    "to all-axioms of 1/n.", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_theorySplitQueueLayeredArrangement, "theory_split_queue_layered_arrangement", "thsql", true, \
    "If turned on, use a layered arrangement to split clauses into queues. Otherwise use " \
    "a tammet-style-arrangement.", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_useAvatarSplitQueues, "avatar_split_queue", "avsq", false, \
    "Turn on experiments: clause selection with multiple queues containing different clauses " \
    "(split by amount of avatar-split-set-size)", \
    OptionTag::AVATAR, false) \
  \
  STRING(_avatarSplitQueueRatios, "avatar_split_queue_ratios", "avsqr", "1,1", \
    "The ratios for picking clauses from the split-queues using weighted round robin. If " \
    "a queue is empty, the clause will be picked from the next non-empty queue to the right. " \
    "Note that this option implicitly also sets the number of queues.", \
    OptionTag::AVATAR, false) \
  \
  STRING(_avatarSplitQueueCutoffs, "avatar_split_queue_cutoffs", "avsqc", "0", \
    "The cutoff-values for the avatar-split-queues (the cutoff value for the last queue is " \
    "omitted, since it has to be infinity).", \
    OptionTag::AVATAR, false) \
  \
  BOOL(_avatarSplitQueueLayeredArrangement, "avatar_split_queue_layered_arrangement", "avsql", false, \
    "If turned on, use a layered arrangement to split clauses into queues. Otherwise use " \
    "a tammet-style-arrangement.", \
    OptionTag::AVATAR, false) \
  \
  BOOL(_useSineLevelSplitQueues, "sine_level_split_queue", "slsq", false, \
    "Turn on experiments: clause selection with multiple queues containing different clauses " \
    "(split by sine-level of clause)", \
    OptionTag::SATURATION, false) \
  \
  STRING(_sineLevelSplitQueueRatios, "sine_level_split_queue_ratios", "slsqr", "1,1", \
    "The ratios for picking clauses from the sine-level-split-queues using weighted round " \
    "robin. If a queue is empty, the clause will be picked from the next non-empty queue " \
    "to the right. Note that this option implicitly also sets the number of queues.", \
    OptionTag::SATURATION, false) \
  \
  STRING(_sineLevelSplitQueueCutoffs, "sine_level_split_queue_cutoffs", "slsqc", "0", \
    "The cutoff-values for the sine-level-split-queues (the cutoff value for the last queue " \
    "is omitted, since it has to be infinity).", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_sineLevelSplitQueueLayeredArrangement, "sine_level_split_queue_layered_arrangement", "slsql", true, \
    "If turned on, use a layered arrangement to split clauses into queues. Otherwise use " \
    "a tammet-style-arrangement.", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_usePositiveLiteralSplitQueues, "positive_literal_split_queue", "plsq", false, \
    "Turn on experiments: clause selection with multiple queues containing different clauses " \
    "(split by number of positive literals in clause)", \
    OptionTag::SATURATION, false) \
  \
  STRING(_positiveLiteralSplitQueueRatios, "positive_literal_split_queue_ratios", "plsqr", "1,4", \
    "The ratios for picking clauses from the positive-literal-split-queues using weighted " \
    "round robin. If a queue is empty, the clause will be picked from the next non-empty " \
    "queue to the right. Note that this option implicitly also sets the number of queues.", \
    OptionTag::SATURATION, false) \
  \
  STRING(_positiveLiteralSplitQueueCutoffs, "positive_literal_split_queue_cutoffs", "plsqc", "0", \
    "The cutoff-values for the positive-literal-split-queues (the cutoff value for the last " \
    "queue is omitted, since it has to be infinity).", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_positiveLiteralSplitQueueLayeredArrangement, "positive_literal_split_queue_layered_arrangement", "plsql", false, \
    "If turned on, use a layered arrangement to split clauses into queues. Otherwise use " \
    "a tammet-style-arrangement.", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_hoSplitQueues, "ho_split_queue", "hsq", false, \
    "Turn on clause selection using multiple queues containing different clauses (split by " \
    "amount of higher-order featues)", \
    OptionTag::SATURATION, false) \
  \
  UNSIGNED(_hoSplitQueueLambdaWeight, "ho_split_queue_lambda_weight", "hsqlw", 1, \
    "How much should lambda occurrences count in the HO features", \
    OptionTag::SATURATION, false) \
  \
  UNSIGNED(_hoSplitQueueAppVarWeight, "ho_split_queue_appvar_weight", "hsqaw", 1, \
    "How much should app-var occurrences count in the HO features", \
    OptionTag::SATURATION, false) \
  \
  STRING(_hoSplitQueueRatios, "ho_split_queue_ratios", "hsqr", "1,1", \
    "The ratios for picking clauses from the split-queues using weighted round robin. If " \
    "a queue is empty, the clause will be picked from the next non-empty queue to the right. " \
    "Note that this option implicitly also sets the number of queues.", \
    OptionTag::AVATAR, false) \
  \
  STRING(_hoSplitQueueCutoffs, "ho_split_queue_cutoffs", "hsqc", "0", \
    "The cutoff-values for the split-queues (the cutoff value for the last queue has to be " \
    "omitted, as it is always infinity). Any split-queue contains all clauses which are assigned " \
    "a feature-value less or equal to the cutoff-value of the queue. If no custom value for " \
    "this option is set, the implementation will use cutoffs 0,4*d,10*d,infinity (where d " \
    "denotes the theory split queue expected ratio denominator).", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_hoSplitQueueLayeredArrangement, "ho_split_queue_layered_arrangement", "hsql", true, \
    "If turned on, use a layered arrangement to split clauses into queues. Otherwise use " \
    "a tammet-style-arrangement.", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_randomAWR, "random_awr", "rawr", false, \
    "Respecting age_weight_ratio, always choose the next clause selection queue probabilistically " \
    "(rather than deterministically).", \
    OptionTag::SATURATION, true) \
  \
  BOOL(_literalMaximalityAftercheck, "literal_maximality_aftercheck", "lma", true, \
    "Allows to disable a secondary (literal maximality) ordering check (in the superposition " \
    "calculus) after a substitution is applied." \
    " The check costs something but sometimes helps to skip some generating inferences", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_arityCheck, "arity_check", "", false, \
    "Enforce the condition that the same symbol name cannot be used with multiple arities." \
    "This also ensures a symbol is not used as a function and predicate.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_parseGoalAnnotations, "parse_goal_annotations", "", true, \
    "Enable parsing :goal annotations in smtlib problems." \
    "They can be used like this: (assert (! <formula> :goal <goal-name>))", \
    OptionTag::INPUT, false) \
  \
  BOOL(_randomTraversals, "random_traversals", "rtra", false, \
    nullptr, \
    OptionTag::SATURATION, true) \
  \
  CHOICE(BadOption, _badOption, "bad_option", "", BadOption::SOFT, \
    ("hard","forced","off","soft"), \
    "What should be done if a bad option value (wrt hard and soft constraints) is encountered:\n" \
    " - hard: will cause a user error\n" \
    " - soft: will only report the error (unless it is unsafe)\n" \
    " - forced: <under development> \n" \
    " - off: will ignore safe errors\n" \
    "Note that unsafe errors will always lead to a user error", \
    OptionTag::HELP, false) \
  \
  CHOICE(Demodulation, _backwardDemodulation, "backward_demodulation", "bd", Demodulation::OFF, \
    ("all","off","preordered"), \
    "Oriented rewriting of kept clauses by newly derived unit equalities\n" \
    "s = t     L[sθ] \\/ C\n" \
    "---------------------   where sθ > tθ (replaces RHS)\n" \
    " L[tθ] \\/ C\n", \
    OptionTag::INFERENCES, false) \
  \
  CHOICE(Subsumption, _backwardSubsumption, "backward_subsumption", "bs", Subsumption::OFF, \
    ("off","on","unit_only"), \
    "Perform subsumption deletion of kept clauses by newly derived clauses. Unit_only means " \
    "that the subsumption will be performed only by unit clauses", \
    OptionTag::INFERENCES, false) \
  \
  CHOICE(Subsumption, _backwardSubsumptionResolution, "backward_subsumption_resolution", "bsr", Subsumption::OFF, \
    ("off","on","unit_only"), \
    "Perform subsumption resolution on kept clauses using newly derived clauses. Unit_only " \
    "means that the subsumption resolution will be performed only by unit clauses", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_backwardSubsumptionDemodulation, "backward_subsumption_demodulation", "bsd", false, \
    "Perform backward subsumption demodulation.", \
    OptionTag::INFERENCES, false) \
  \
  UNSIGNED(_backwardSubsumptionDemodulationMaxMatches, "backward_subsumption_demodulation_max_matches", "bsdmm", 0, \
    "Maximum number of multi-literal matches to consider in backward subsumption demodulation. " \
    "0 means to try all matches (until first success).", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_binaryResolution, "binary_resolution", "br", true, \
    "Standard binary resolution i.e.\n" \
    "C \\/ t     D \\/ s\n" \
    "---------------------\n" \
    "(C \\/ D)θ\n" \
    "where θ = mgu(t,-s) and t selected", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_superposition, "superposition", "sup", true, \
    "Control superposition. Turning off this core inference leads to an incomplete calculus " \
    "on equational problems.", \
    OptionTag::INFERENCES, false) \
  \
  CHOICE(Condensation, _condensation, "condensation", "cond", Condensation::OFF, \
    ("fast","off","on"), \
    "Perform condensation. If 'fast' is specified, we only perform condensations that are " \
    "easy to check for.", \
    OptionTag::INFERENCES, false) \
  \
  CHOICE(DemodulationRedundancyCheck, _demodulationRedundancyCheck, "demodulation_redundancy_check", "drc", DemodulationRedundancyCheck::ENCOMPASS, \
    ("off","ordering","encompass"), \
    "The following cases of backward and forward demodulation do not preserve completeness:\n" \
    "s = t     s = t1 \\/ C \t s = t     s != t1 \\/ C\n" \
    "--------------------- \t ---------------------\n" \
    "t = t1 \\/ C \t\t t != t1 \\/ C\n" \
    "where t > t1 and s = t > C (RHS replaced)\n" \
    "With `encompass`, we treat demodulations (both forward and backward) as encompassment " \
    "demodulations (as defined by Duarte and Korovin in 2022's IJCAR paper).\n" \
    "With `ordering`, we check this condition and don't demodulate if we could violate completeness.\n" \
    "With `off`, we skip the checks, save time, but become incomplete.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_forwardDemodulationTermOrderingDiagrams, "forward_demodulation_term_ordering_diagrams", "fdtod", true, \
    "Use term ordering diagrams (TODs) to runtime specialize post-ordering checks in forward " \
    "demodulation.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_demodulationOnlyEquational, "demodulation_only_equational", "doe", false, \
    "Disables demodulation of non-equational literals. In combination with -ins > 0 simulates " \
    "the effect of Waldmeister's `Enlarging the Hypothesis` trick.", \
    OptionTag::INFERENCES, true) \
  \
  CHOICE(EqualityProxy, _equalityProxy, "equality_proxy", "ep", EqualityProxy::OFF, \
    ("R","RS","RST","RSTC","off"), \
    "Applies the equality proxy transformation to the problem. It works as follows:\n" \
    " - All literals s=t are replaced by E(s,t)\n" \
    " - All literals s!=t are replaced by ~E(s,t)\n" \
    " - If S the symmetry clause ~E(x,y) \\/ E(y,x) is added\n" \
    " - If T the transitivity clause ~E(x,y) \\/ ~E(y,z) \\/ E(x,z) is added\n" \
    " - If C the congruence clauses are added as follows:\n" \
    "    for predicates p that are not E or equality add\n" \
    "     ~E(x1,y1) \\/ ... \\/ ~E(xN,yN) \\/ ~p(x1,...,xN) \\/ p(y1,...,yN)\n" \
    "    for non-constant functions f add\n" \
    "     ~E(x1,y1) \\/ ... \\/ ~E(xN,yN) \\/ E(f(x1,...,xN),f(y1,...,yN))\n" \
    " R stands for reflexivity.\n" \
    " E is a single polymorphic predicate for a polymorphic problem and one predicate" \
    " per sort for a monomorphic one", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_equalityResolutionWithDeletion, "equality_resolution_with_deletion", "erd", true, \
    "Perform equality resolution with deletion.", \
    OptionTag::PREPROCESSING, false) \
  \
  CHOICE(ExtensionalityResolution, _extensionalityResolution, "extensionality_resolution", "er", ExtensionalityResolution::OFF, \
    ("filter","known","tagged","off"), \
    "Turns on the following inference rule:\n" \
    "  x=y \\/ C    s != t \\/ D\n" \
    "  -----------------------\n" \
    "  C{x → s, y → t} \\/ D\n" \
    "Where s!=t is selected in s!=t \\/D and x=y \\/ C is a recognised as an extensionality " \
    "clause - how clauses are recognised depends on the value of this option.\n" \
    "If filter we attempt to recognise all extensionality clauses i.e. those that have exactly " \
    "one X=Y, no inequality of the same sort as X-Y (and optionally no equality except X=Y, " \
    "see extensionality_allow_pos_eq).\n" \
    "If known we only recognise a known set of extensionality clauses. At the moment this " \
    "includes the standard and subset-based formulations of the set extensionality axiom, " \
    "as well as the array extensionality axiom.\n" \
    "If tagged we only use formulas tagged as extensionality clauses.", \
    OptionTag::INFERENCES, false) \
  \
  UNSIGNED(_extensionalityMaxLength, "extensionality_max_length", "erml", 0, \
    "Sets the maximum length (number of literals) an extensionality" \
    " clause can have when doing recognition for extensionality resolution. If zero there " \
    "is no maximum.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_extensionalityAllowPosEq, "extensionality_allow_pos_eq", "eape", true, \
    "If extensionality resolution equals filter, this dictates" \
    " whether we allow other positive equalities when recognising extensionality clauses", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_FOOLParamodulation, "fool_paramodulation", "foolp", false, \
    "Turns on the following inference rule:\n" \
    "        C[s]\n" \
    "--------------------,\n" \
    "C[true] \\/ s = false\n" \
    "where s is a boolean term that is not a variable, true or false, C[true] is " \
    "the C clause with s substituted by true. This rule is needed for efficient " \
    "treatment of boolean terms.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_termAlgebraInferences, "term_algebra_rules", "tar", true, \
    "Activates some rules that improve reasoning with term algebras (such as algebraic datatypes " \
    "in SMT-LIB):\n" \
    "If the problem does not contain any term algebra symbols, activating this options has " \
    "no effect\n" \
    "- distinctness rule:\n" \
    "f(...) = g(...) \\/ A\n" \
    "--------------------\n" \
    "          A         \n" \
    "where f and g are distinct term algebra constructors\n" \
    "- distinctness tautology deletion: clauses of the form f(...) ~= g(...) \\/ A are deleted\n" \
    "- injectivity rule:\n" \
    "f(s1 ... sn) = f(t1 ... tn) \\/ A\n" \
    "--------------------------------\n" \
    "         s1 = t1 \\/ A\n" \
    "               ...\n" \
    "         sn = tn \\/ A", \
    OptionTag::THEORIES, false) \
  \
  CHOICE(TACyclicityCheck, _termAlgebraCyclicityCheck, "term_algebra_acyclicity", "tac", TACyclicityCheck::OFF, \
    ("off","axiom","rule","light"), \
    "Activates the cyclicity rule for term algebras (such as algebraic datatypes in SMT-LIB):\n" \
    "- off : the cyclicity rule is not enforced (this is sound but incomplete)\n" \
    "- axiom : the cyclicity rule is axiomatized with a transitive predicate describing the " \
    "subterm relation over terms\n" \
    "- rule : the cyclicity rule is enforced by a specific hyper-resolution rule\n" \
    "- light : the cyclicity rule is enforced by rule generating disequality between a term " \
    "and its known subterms", \
    OptionTag::THEORIES, false) \
  \
  BOOL(_termAlgebraExhaustivenessAxiom, "term_algebra_exhaustiveness_axiom", "taea", true, \
    "Enable term algebra exhaustiveness axiom", \
    OptionTag::THEORIES, false) \
  \
  UNSIGNED(_fmbStartSize, "fmb_start_size", "fmbss", 1, \
    "Set the initial model size for finite model building", \
    OptionTag::FMB, false) \
  \
  FLOAT(_fmbSymmetryRatio, "fmb_symmetry_ratio", "fmbsr", 1.0, \
    "Usually we use at most n principal terms for symmetry avoidance where n is the current " \
    "model size. This option allows us to supply a multiplier for that n. See Symmetry Avoidance " \
    "in MACE-Style Finite Model Finding.", \
    OptionTag::FMB, false) \
  \
  CHOICE(FMBSymbolOrders, _fmbSymmetryOrderSymbols, "fmb_symmetry_symbol_order", "fmbsso", FMBSymbolOrders::OCCURRENCE, \
    ("occurrence","input_usage","preprocessed_usage"), \
    "The order of symbols considered for symmetry avoidance. See Symmetry Avoidance in MACE-Style " \
    "Finite Model Finding.", \
    OptionTag::FMB, false) \
  \
  CHOICE(FMBAdjustSorts, _fmbAdjustSorts, "fmb_adjust_sorts", "fmbas", FMBAdjustSorts::GROUP, \
    ("off","expand","group","predicate","function"), \
    "Detect monotonic sorts. If <expand> then expand monotonic subsorts into proper sorts. " \
    "If <group> then collapse monotonic sorts into a single sort. If <predicate> then introduce " \
    "sort predicates for non-monotonic sorts and collapse all sorts into one. If <function> " \
    "then introduce sort functions for non-monotonic sorts and collapse all sorts into one", \
    OptionTag::FMB, false) \
  \
  BOOL(_fmbDetectSortBounds, "fmb_detect_sort_bounds", "fmbdsb", false, \
    "Use a saturation loop to detect sort bounds introduced by (for example) injective functions", \
    OptionTag::FMB, false) \
  \
  UNSIGNED(_fmbSizeWeightRatio, "fmb_size_weight_ratio", "fmbswr", 1, \
    "Controls the priority the next sort size vector is given based on a ratio. 0 is size " \
    "only, 1 means 1:1, 2 means 1:2, etc.", \
    OptionTag::FMB, false) \
  \
  BOOL(_fmbKeepSbeamGenerators, "fmb_keep_sbeam_generators", "fmbksg", false, \
    "A modification of the sbeam enumeration strategy which (for a performance price) makes " \
    "it more enumeration-complete.", \
    OptionTag::FMB, false) \
  \
  BOOL(_fmbUseSimplifyingSolver, "fmb_use_simplifying_solver", "fmbuss", true, \
    "Allow the SAT solver to internally simplify the instance.", \
    OptionTag::FMB, false) \
  \
  STRING(_forbiddenOptions, "forbidden_options", "", "", \
    "If some of the specified options are set to a forbidden state, vampire will fail to " \
    "start, or in portfolio modes it will skip such strategies. The expected syntax is <opt1>=<val1>:<opt2>:<val2>:...:<optn>=<valN>", \
    OptionTag::INPUT, false) \
  \
  STRING(_forcedOptions, "forced_options", "", "", \
    "Options in the format <opt1>=<val1>:<opt2>=<val2>:...:<optn>=<valN> that override the " \
    "option values set by other means (also inside portfolio mode strategies)", \
    OptionTag::INPUT, false) \
  \
  CHOICE(Demodulation, _forwardDemodulation, "forward_demodulation", "fd", Demodulation::ALL, \
    ("all","off","preordered"), \
    "Oriented rewriting of newly derived clauses by kept unit equalities\n" \
    "s = t     L[sθ] \\/ C\n" \
    "---------------------  where sθ > tθ\n" \
    " L[tθ] \\/ C\n" \
    "If 'preordered' is set, only equalities s = t where s > t are used for rewriting.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_forwardGroundJoinability, "forward_ground_joinability", "fgj", false, \
    "Perform forward ground joinability.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_forwardLiteralRewriting, "forward_literal_rewriting", "flr", false, \
    "Perform forward literal rewriting.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_forwardSubsumption, "forward_subsumption", "fs", true, \
    "Perform forward subsumption deletion.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_forwardSubsumptionResolution, "forward_subsumption_resolution", "fsr", true, \
    "Perform forward subsumption resolution.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_forwardSubsumptionDemodulation, "forward_subsumption_demodulation", "fsd", false, \
    "Perform forward subsumption demodulation.", \
    OptionTag::INFERENCES, false) \
  \
  UNSIGNED(_forwardSubsumptionDemodulationMaxMatches, "forward_subsumption_demodulation_max_matches", "fsdmm", 0, \
    "Maximum number of multi-literal matches to consider in forward subsumption demodulation. " \
    "0 means to try all matches (until first success).", \
    OptionTag::INFERENCES, false) \
  \
  CHOICE(FunctionDefinitionElimination, _functionDefinitionElimination, "function_definition_elimination", "fde", FunctionDefinitionElimination::ALL, \
    ("all","none","unused"), \
    "Attempts to eliminate function definitions. A function definition is a unit clause of " \
    "the form f(x1,..,xn) = t where x1,..,xn are the pairwise distinct free variables of " \
    "t and f does not appear in t." \
    " If 'all', definitions are eliminated by replacing every occurrence of f(s1,..,sn) by " \
    "t{x1 -> s1, .., xn -> sn}. If 'unused' only unused definitions are removed.", \
    OptionTag::PREPROCESSING, false) \
  \
  UNSIGNED(_functionDefinitionIntroduction, "function_definition_introduction", "fdi", 0, \
    "If non-zero, introduces function definitions with generalisation for repeated compound " \
    "terms in the active set. " \
    "For example, if f(a, g(a)) and f(b, g(b)) occur frequently, we might define d(X) = f(X, " \
    "g(X)). " \
    "The parameter value 'n' is a threshold: terms that occur more than n times have a definition " \
    "created.", \
    OptionTag::INFERENCES, false) \
  \
  CHOICE(TweeGoalTransformation, _tweeGoalTransformation, "twee_goal_transformation", "tgt", TweeGoalTransformation::OFF, \
    ("off","ground","full"), \
    "Add definitions for `ground` subterms in the conjecture, inspired by Twee. " \
    "This adds a goal-directed flavour to equational reasoning. " \
    "`full` is a generalization, where also non-ground subterms are considered.", \
    OptionTag::PREPROCESSING, true) \
  \
  BOOL(_tweeSkipArrows, "twee_skip_arrows", "tsa", true, \
    "During twee_goal_transformation, when in HOL, don't introduce definitions for arrow-typed " \
    "subterms.", \
    OptionTag::PREPROCESSING, true) \
  \
  BOOL(_codeTreeSubsumption, "code_tree_subsumption", "cts", true, \
    "Use code tree implementation of forward subsumption and subsumption resolution.", \
    OptionTag::INFERENCES, true) \
  \
  BOOL(_generalSplitting, "general_splitting", "gsp", false, \
    "Splits clauses in order to reduce number of different variables in each clause. " \
    "A clause C[X] \\/ D[Y] with subclauses C and D over non-equal sets of variables X and " \
    "Y can be split into S(Z) \\/ C[X] and ~S(Z) \\/ D[Y] where Z is the intersection of " \
    "X and Y.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_globalSubsumption, "global_subsumption", "gs", false, \
    "Perform global subsumption. Use a set of groundings of generated clauses G to replace " \
    "C \\/ L by C if the grounding of C is implied by G. A SAT solver is used for ground " \
    "reasoning.", \
    OptionTag::INFERENCES, false) \
  \
  CHOICE(GoalGuess, _guessTheGoal, "guess_the_goal", "gtg", GoalGuess::OFF, \
    ("off","all","exists_top","exists_all","exists_sym","position"), \
    "Use heuristics to guess formulas that correspond to the goal. Doesn't " \
    "really make sense if there is already a goal but it will still do something. " \
    "This is really designed for use with SMTLIB problems that don't have goals", \
    OptionTag::INPUT, false) \
  \
  UNSIGNED(_guessTheGoalLimit, "guess_the_goal_limit", "gtgl", 1, \
    "The maximum number of input units a symbol appears for it to be considered in a goal", \
    OptionTag::INPUT, false) \
  \
  BOOL(_simultaneousSuperposition, "simultaneous_superposition", "sims", true, \
    "Rewrite the whole RHS clause during superposition, not just the target literal.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_innerRewriting, "inner_rewriting", "irw", false, \
    "C[t_1] | t1 != t2 ==> C[t_2] | t1 != t2 when t1>t2", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_equationalTautologyRemoval, "equational_tautology_removal", "etr", false, \
    "A reduction which uses congruence closure to remove logically valid clauses.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_subsumptionEqualityResolution, "subsumption_equality_resolution", "ser", false, \
    "Similar to subsumption resolution but uses the implicit x = x clause to resolve a literal.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_partialRedundancyCheck, "partial_redundancy_check", "prc", false, \
    "Skip generating inferences on clause instances on which we already performed a simplifying " \
    "inference.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_partialRedundancyOrderingConstraints, "partial_redundancy_ordering_constraints", "proc", false, \
    "Strengthen partial redundancy with ordering constraints.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_partialRedundancyAvatarConstraints, "partial_redundancy_avatar_constraints", "prac", false, \
    "Strengthen partial redundancy with AVATAR constraints.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_partialRedundancyLiteralConstraints, "partial_redundancy_literal_constraints", "prlc", false, \
    "Strengthen partial redundancy with literals from clauses.", \
    OptionTag::INFERENCES, false) \
  \
  CHOICE(IgnoreMissing, _ignoreMissing, "ignore_missing", "", IgnoreMissing::OFF, \
    ("on","off","warn"), \
    "Ignore any options that have been removed (useful in portfolio modes where this can " \
    "cause strategies to be skipped). If set to warn " \
    "this will print a warning when ignoring. This is set to warn in CASC mode.", \
    OptionTag::DEVELOPMENT, false) \
  \
  STRING(_include, "include", "", "", \
    "Path prefix for the 'include' TPTP directive", \
    OptionTag::INPUT, false) \
  \
  BOOL(_increasedNumeralWeight, "increased_numeral_weight", "inw", false, \
    "This option only applies if the problem has interpreted numbers. The weight of integer " \
    "constants depends on the logarithm of their absolute value (instead of being 1)", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_ignoreConjectureInPreprocessing, "ignore_conjecture_in_preprocessing", "icip", false, \
    "Make sure we do not delete the conjecture in preprocessing even if it can be deleted.", \
    OptionTag::PREPROCESSING, false) \
  \
  INT(_inequalitySplitting, "inequality_splitting", "ins", 0, \
    "When greater than zero, ins defines a weight threshold w such that any clause C \\/ " \
    "s!=t " \
    "where s (or conversely t) is ground and has weight greater or equal than w " \
    "is replaced by C \\/ p(s) with the additional unit clause ~p(t) being added " \
    "for fresh predicate p.", \
    OptionTag::PREPROCESSING, false) \
  \
  CHOICE(InputSyntax, _inputSyntax, "input_syntax", "", InputSyntax::AUTO, \
    ("smtlib2","tptp","auto"), \
    "Input syntax. Historic input syntaxes have been removed as they are not actively maintained. " \
    "Contact developers for help with these.", \
    OptionTag::INPUT, false) \
  \
  BOOL(_instantiation, "instantiation", "inst", false, \
    "Heuristically instantiate variables. Often wastes a lot of effort. Consider using thi " \
    "instead.", \
    OptionTag::THEORIES, false) \
  \
  CHOICE(Induction, _induction, "induction", "ind", Induction::NONE, \
    ("none","struct","int","both"), \
    "Apply structural and/or integer induction on datatypes and integers.", \
    OptionTag::INDUCTION, false) \
  \
  CHOICE(StructuralInductionKind, _structInduction, "structural_induction_kind", "sik", StructuralInductionKind::ONE, \
    ("one","two","three","recursion","all"), \
    "The kind of structural induction applied", \
    OptionTag::INDUCTION, false) \
  \
  CHOICE(IntInductionKind, _intInduction, "int_induction_kind", "iik", IntInductionKind::ONE, \
    ("one","two","all"), \
    "The kind of integer induction applied", \
    OptionTag::INDUCTION, false) \
  \
  CHOICE(InductionChoice, _inductionChoice, "induction_choice", "indc", InductionChoice::ALL, \
    ("all","goal","goal_plus"), \
    "Where to apply induction. Goal only applies to constants in goal, goal_plus" \
    " extends this with skolem constants introduced by induction. Consider using" \
    " guess_the_goal for problems in SMTLIB as they do not come with a conjecture", \
    OptionTag::INDUCTION, false) \
  \
  UNSIGNED(_maxInductionDepth, "induction_max_depth", "indmd", 0, \
    "Set maximum depth of induction where 0 means no max.", \
    OptionTag::INDUCTION, false) \
  \
  BOOL(_inductionNegOnly, "induction_neg_only", "indn", true, \
    "Only apply induction to negative literals", \
    OptionTag::INDUCTION, false) \
  \
  BOOL(_inductionUnitOnly, "induction_unit_only", "indu", true, \
    "Only apply induction to unit clauses", \
    OptionTag::INDUCTION, false) \
  \
  BOOL(_inductionGen, "induction_gen", "indgen", false, \
    "Apply induction with generalization (on both all & selected occurrences)", \
    OptionTag::INDUCTION, false) \
  \
  BOOL(_inductionStrengthenHypothesis, "induction_strengthen_hypothesis", "indstrhyp", false, \
    "Strengthen induction formulas with the remaining skolem constants" \
    " replaced with universally quantified variables in hypotheses", \
    OptionTag::INDUCTION, false) \
  \
  UNSIGNED(_maxInductionGenSubsetSize, "max_induction_gen_subset_size", "indgenss", 3, \
    "Set maximum number of occurrences of the induction term to be" \
    " generalized, where 0 means no max. (Regular induction will" \
    " be applied without this restriction.)", \
    OptionTag::INDUCTION, false) \
  \
  BOOL(_inductionOnComplexTerms, "induction_on_complex_terms", "indoct", false, \
    "Apply induction on complex (ground) terms vs. only on constants", \
    OptionTag::INDUCTION, false) \
  \
  BOOL(_inductionGroundOnly, "induction_ground_only", "indgo", true, \
    "Apply induction only on ground literals vs. literals with at most one free variable", \
    OptionTag::INDUCTION, false) \
  \
  BOOL(_functionDefinitionRewriting, "function_definition_rewriting", "fnrw", false, \
    "Use function definitions as rewrite rules with the intended orientation rather than " \
    "the term ordering one", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_integerInductionDefaultBound, "int_induction_default_bound", "intinddb", false, \
    "Always apply integer induction with bound 0", \
    OptionTag::INDUCTION, false) \
  \
  CHOICE(IntegerInductionInterval, _integerInductionInterval, "int_induction_interval", "intindint", IntegerInductionInterval::BOTH, \
    ("infinite","finite","both"), \
    "Whether integer induction is applied over infinite or finite intervals, or both", \
    OptionTag::INDUCTION, false) \
  \
  CHOICE(IntegerInductionLiteralStrictness, _integerInductionStrictnessEq, "int_induction_strictness_eq", "intindsteq", IntegerInductionLiteralStrictness::NONE, \
    ("none","toplevel_not_in_other","only_one_occurrence","not_in_both","always"), \
    "Exclude induction term t/literal l combinations from integer induction.\n" \
    "Induction is not applied to _equality_ literals l:\n" \
    "  - none: no exclusion\n" \
    "  - toplevel_not_in_other: t is a top-level argument of l,\n" \
    "    but it does not occur in the other argument of l\n" \
    "  - only_one_occurrence: t has only one occurrence in l\n" \
    "  - not_in_both: t does not occur in both arguments of l\n" \
    "  - always: induction on l is not allowed at all\n", \
    OptionTag::INDUCTION, false) \
  \
  CHOICE(IntegerInductionLiteralStrictness, _integerInductionStrictnessComp, "int_induction_strictness_comp", "intindstcomp", IntegerInductionLiteralStrictness::TOPLEVEL_NOT_IN_OTHER, \
    ("none","toplevel_not_in_other","only_one_occurrence","not_in_both","always"), \
    "Exclude induction term t/literal l combinations from integer induction.\n" \
    "Induction is not applied to _comparison_ literals l:\n" \
    "  - none: no exclusion\n" \
    "  - toplevel_not_in_other: t is a top-level argument of l,\n" \
    "    but it does not occur in the other argument of l\n" \
    "  - only_one_occurrence: t has only one occurrence in l\n" \
    "  - not_in_both: t does not occur in both arguments of l\n" \
    "  - always: induction on l is not allowed at all\n", \
    OptionTag::INDUCTION, false) \
  \
  CHOICE(IntegerInductionTermStrictness, _integerInductionStrictnessTerm, "int_induction_strictness_term", "intindstterm", IntegerInductionTermStrictness::INTERPRETED_CONSTANT, \
    ("none", "interpreted_constant", "no_skolems"), \
    "Exclude induction term t/literal l combinations from integer induction.\n" \
    "Induction is not applied to the induction term t:\n" \
    "  - none: no exclusion\n" \
    "  - interpreted_constant: t is an interpreted constant\n" \
    "  - no_skolems: t does not contain a skolem function", \
    OptionTag::INDUCTION, false) \
  \
  BOOL(_nonUnitInduction, "non_unit_induction", "nui", false, \
    "Induction on certain clauses or clause sets instead of just unit clauses", \
    OptionTag::INDUCTION, false) \
  \
  BOOL(_inductionOnActiveOccurrences, "induction_on_active_occurrences", "indao", false, \
    "Only use induction terms from active occurrences, generalize over active occurrences", \
    OptionTag::INDUCTION, false) \
  \
  CHOICE(LiteralComparisonMode, _literalComparisonMode, "literal_comparison_mode", "lcm", LiteralComparisonMode::STANDARD, \
    ("predicate","reverse","standard"), \
    "Vampire uses term orderings which use an ordering of predicates. Standard places equality " \
    "(and certain other special predicates) first and all others second. Predicate depends " \
    "on symbol precedence (see symbol_precedence). Reverse reverses the order.", \
    OptionTag::SATURATION, false) \
  \
  INT(_lookaheadDelay, "lookahaed_delay", "lsd", 0, \
    "Delay the use of lookahead selection by this many selections" \
    " the idea is that lookahead selection may behave erratically" \
    " at the start", \
    OptionTag::SATURATION, false) \
  \
  INT(_lrsFirstTimeCheck, "lrs_first_time_check", "lftc", 5, \
    "Percentage of time limit at which the LRS algorithm will for the first time estimate " \
    "the number of reachable clauses.", \
    OptionTag::LRS, false) \
  \
  BOOL(_lrsWeightLimitOnly, "lrs_weight_limit_only", "lwlo", false, \
    "If off, the lrs sets both age and weight limit according to clause reachability, otherwise " \
    "it sets the age limit to 0 and only the weight limit reflects reachable clauses", \
    OptionTag::LRS, false) \
  \
  BOOL(_lrsRetroactiveDeletes, "lrs_retroactive_deletes", "lrd", false, \
    "Not only deleted new clauses that exceed current estimated limits in passive," \
    " but also visit active and passive and delete clauses that exceed the new limit or would " \
    "only generate children exceeding the limit.", \
    OptionTag::LRS, false) \
  \
  BOOL(_lrsPreemptiveDeletes, "lrs_preemptive_deletes", "lpd", true, \
    "If false, LRS will not use limits to delete clauses entering passive." \
    " (Only the retroactive deletes might apply.)", \
    OptionTag::LRS, false) \
  \
  VAMPIRE_IF_PERF(UNSIGNED(_instructionLimit, "instruction_limit", "i", 0, \
    "Limit the number (in millions) of executed instructions (excluding the kernel ones).", \
    OptionTag::LAST_TAG, false)) \
  \
  VAMPIRE_IF_PERF(UNSIGNED(_simulatedInstructionLimit, "simulated_instruction_limit", "sil", 0, \
    "Instruction limit (in millions) of executed instructions for the purpose of reachability " \
    "estimations of the LRS saturation algorithm (if 0, the actual instruction limit is used)", \
    OptionTag::LRS, false)) \
  \
  VAMPIRE_IF_PERF(BOOL(_parsingDoesNotCount, "parsing_does_not_count", "", false, \
    "Extend the instruction limit by the amount of instructions it took to parse the input " \
    "problem.", \
    OptionTag::DEVELOPMENT, false)) \
  \
  BOOL(_interactive, "interactive", "", false, \
    "An experimental interactive mode (commands to use: load <file to parse>, read <line " \
    "to parse>, pop (to drop the last added set of formulas), run [options to supply], exit).", \
    OptionTag::LAST_TAG, true) \
  \
  CHOICE(Mode, _mode, "mode", "", Mode::VAMPIRE, \
    ("axiom_selection", "casc", "clausify", "consequence_elimination", "model_check", "output", "portfolio", "preprocess", "preprocess2", "profile", "smtcomp", "spider", "tclausify", "tpreprocess", "vampire"), \
    "Select the mode of operation. Choices are:\n" \
    "  -vampire: the standard mode of operation for first-order theorem proving\n" \
    "  -portfolio: a portfolio mode running a specified schedule (see schedule)\n" \
    "  -casc, casc_sat, smtcomp - like portfolio mode, with competition-specific presets " \
    "for other options, including output. " \
    "If you wish to use e.g. the CASC portfolio without the presets, use --mode portfolio " \
    "--schedule casc.\n" \
    "  -preprocess,axiom_selection,clausify: modes for producing output\n" \
    "      for other solvers.\n" \
    "  -tpreprocess,tclausify: output modes for theory input (clauses are quantified\n" \
    "      with sort information; tclausify outputs TPTP tcf).\n" \
    "  -output,profile: output information about the problem\n" \
    "Some modes are not currently maintained (get in touch if interested):\n" \
    "  -bpa: perform bound propagation\n" \
    "  -consequence_elimination: perform consequence elimination\n", \
    OptionTag::LAST_TAG, false) \
  \
  CHOICE(Intent, _intent, "intent", "intent", Intent::UNSAT, \
    ("unsat","sat"), \
    "Describes what the system should be striving to show." \
    " By default a prover tries to show `unsat` and find a refutation (a proof of the negated " \
    "conjecture)." \
    " Discovering a finite saturations while using a complete strategy and thus testifying " \
    "satisfiability is a nice bonus in that case." \
    " On the other hand, with the intent `sat` the main focus is on finding models." \
    " (Please use `--mode casc --intent sat` to achieve what was previously triggered via " \
    "`--mode CASC_SAT`).", \
    OptionTag::LAST_TAG, false) \
  \
  CHOICE(Schedule, _schedule, "schedule", "sched", Schedule::CASC, \
    ("casc", "casc_2024", "casc_2025", "casc_sat", "casc_sat_2024", "casc_sat_2025", "file", "induction", "integer_induction", "intind_oeis", "ltb_default_2017", "ltb_hh4_2017", "ltb_hll_2017", "ltb_isa_2017", "ltb_mzr_2017", "smtcomp", "smtcomp_2018", "snake_tptp_uns", "snake_tptp_sat", "struct_induction", "struct_induction_tip"), \
    "Schedule to be run by the portfolio mode. casc and smtcomp usually point to the most " \
    "recent schedule in that category. file loads the schedule from a file specified in --schedule_file. " \
    "Note that some old schedules may contain option values that are no longer supported " \
    "- see ignore_missing.", \
    OptionTag::PORTFOLIO, false) \
  \
  STRING(_scheduleFile, "schedule_file", "", "", \
    "Path to the input schedule file. Each line contains an encoded strategy. Disabled unless " \
    "`--schedule file` is set.", \
    OptionTag::PORTFOLIO, false) \
  \
  UNSIGNED(_multicore, "cores", "", 1, \
    "When running in portfolio modes (including casc or smtcomp modes) specify the number " \
    "of cores, set to 0 to use maximum", \
    OptionTag::PORTFOLIO, false) \
  \
  FLOAT(_slowness, "slowness", "", 1.0, \
    "The factor by which is multiplied the time limit of each configuration in casc/casc_sat/smtcomp/portfolio " \
    "mode", \
    OptionTag::PORTFOLIO, false) \
  \
  BOOL(_randomizeSeedForPortfolioWorkers, "randomize_seed_for_portfolio_workers", "", true, \
    "In portfolio mode, let each worker process start from its own independent random seed.", \
    OptionTag::PORTFOLIO, false) \
  \
  BOOL(_shuffleOnScheduleRepeats, "shuffle_on_schedule_repeats", "", true, \
    "In portfolio mode, when we run out of strategies in the selected schedule, we restart " \
    "from the beginning while doubling the limits," \
    " under this option, we also force si=on:rtra=on to increase the chance that the repeated " \
    "strategies `do something else`.", \
    OptionTag::PORTFOLIO, false) \
  \
  INT(_naming, "naming", "nm", 8, \
    "Introduce names for subformulas. Given a subformula F(x1,..,xk) of formula G a new predicate " \
    "symbol is introduced as a name for F(x1,..,xk) by adding the axiom n(x1,..,xk) <=> F(x1,..,xk) " \
    "and replacing F(x1,..,xk) with n(x1,..,xk) in G. The value indicates how many times " \
    "a subformula must be used before it is named.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_nonliteralsInClauseWeight, "nonliterals_in_clause_weight", "nicw", false, \
    "Non-literal parts of clauses (such as its split history) will also contribute to the " \
    "weight", \
    OptionTag::AVATAR, false) \
  \
  BOOL(_normalize, "normalize", "norm", false, \
    "Normalize the problem so that the ordering of clauses etc does not effect proof search.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_shuffleInput, "shuffle_input", "si", false, \
    "Randomly shuffle the input problem. (Runs after and thus destroys normalize.)", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_randomPolarities, "random_polarities", "rp", false, \
    "As part of preprocessing, randomly (though consistently) flip polarities of non-equality " \
    "predicates in the whole CNF.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_randomizedSimplifications, "randomized_simplifications", "rsi", false, \
    "Make selected saturation-loop simplifications (including AVATAR splitting) \"leaky\":" \
    " under a coin toss, some of their candidate operations are randomly skipped, as a source " \
    "of noise injection.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_randomizedPreprocessing, "randomized_preprocessing", "rpr", false, \
    "Make selected preprocessing steps \"leaky\": under a coin toss, some of their operations " \
    "are randomly skipped," \
    " producing a mixture of half-completed (but still sound) results as a source of noise " \
    "injection.", \
    OptionTag::PREPROCESSING, false) \
  \
  STRING(_printProofToFile, "print_proofs_to_file", "pptf", "", \
    "If Vampire finds a proof, it is printed to the here specified file instead of to stdout.\n" \
    "Currently, this option only works in portfolio mode.", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_printClausifierPremises, "print_clausifier_premises", "", false, \
    "Output how the clausified problem was derived.", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_replaceDomainElements, "replace_domain_elements", "", false, \
    "When printing a finite model, try hard to look for constants from the original formulation " \
    "to use instead of domain elements.", \
    OptionTag::OUTPUT, false) \
  \
  CHOICE(Proof, _proof, "proof", "p", Proof::ON, \
    ("off","on","proofcheck","tptp","property","smt2_proofcheck","smtcheck"), \
    "Specifies whether proof (or similar e.g. model/saturation) will be output and in which " \
    "format:\n" \
    "- off gives no proof output\n" \
    "- on gives native Vampire proof output\n" \
    "- proofcheck will output proof as a sequence of TPTP problems to allow for proof-checking " \
    "by external solvers\n" \
    "- tptp gives TPTP output\n" \
    "- property is a developmental option. It allows developers to output statistics about " \
    "the proof using a ProofPrinter " \
    "object (see Kernel/InferenceStore::ProofPropertyPrinter\n" \
    "- smtcheck produces a ground SMT script for proof checking\n", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_minimizeSatProofs, "minimize_sat_proofs", "msp", true, \
    "Perform premise minimization when a sat solver finds a clause set UNSAT\n" \
    "(such as with AVATAR proofs or with global subsumption).", \
    OptionTag::OUTPUT, false) \
  \
  CHOICE(ProofExtra, _proofExtra, "proof_extra", "", ProofExtra::OFF, \
    ("off","free","full"), \
    "Add extra detail to proofs:\n" \
    " " \
    "- free uses known information only\n" \
    "- full may perform expensive operations to achieve this so may" \
    " significantly impact on performance.\n" \
    " The option is still under development and the format of extra information (mainly from " \
    "full) may change between minor releases", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_traceback, "traceback", "", false, \
    "Try decoding backtrace into a sequence of human readable function names using addr2line/atos/etc.", \
    OptionTag::OUTPUT, false) \
  \
  STRING(_protectedPrefix, "protected_prefix", "", "", \
    "Symbols with this prefix are immune against elimination during preprocessing", \
    OptionTag::PREPROCESSING, true) \
  \
  CHOICE(QuestionAnsweringMode, _questionAnswering, "question_answering", "qa", QuestionAnsweringMode::AUTO, \
    ("auto","plain","synthesis","off"), \
    "Determines whether (and how) we attempt to answer questions:" \
    " plain - answer-literal-based, supports disjunctive answers; synthesis - designed for " \
    "synthesising programs from proofs.", \
    OptionTag::OTHER, false) \
  \
  BOOL(_questionAnsweringGroundOnly, "question_answering_ground_only", "qago", false, \
    "In qa plain mode: if set, only ground answers will be considered.", \
    OptionTag::OTHER, false) \
  \
  STRING(_questionAnsweringAvoidThese, "question_answering_avoid_these", "qaat", "", \
    "A |-separated list of answer literal atoms (e.g., `ans0(sK1)|ans0(f(c))`) that should " \
    "not be considered as answers to return." \
    " The atoms may contain variables. Matching against any of those disqualifies a potential " \
    "answer.", \
    OptionTag::OTHER, false) \
  \
  UNSIGNED(_randomSeed, "random_seed", "", 1 /* this should be the value of Random::_seed from Random.cpp */, \
    "Some parts of vampire use random numbers. This seed allows for reproducibility of results. " \
    "By default the seed is not changed." \
    " Use the non-default value 0 to have vampire query a random_device for always different " \
    "behaviour.", \
    OptionTag::INPUT, false) \
  \
  UNSIGNED(_randomStrategySeed, "random_strategy_seed", "", 0, \
    "Sets the seed for generating random strategies." \
    " This option is necessary because --random_seed <value> will be included as a fixed " \
    "value in the generated random strategy," \
    " hence won't have any effect on the random strategy generation. Set to non-0 for this " \
    "to have effect; the default 0 still calls a random_device.", \
    OptionTag::INPUT, true) \
  \
  STRING(_sampleStrategy, "sample_strategy", "", "", \
    "Specify a path to a filename (of homemade format) describing how to sample a random " \
    "strategy.", \
    OptionTag::DEVELOPMENT, true) \
  \
  INT(_activationLimit, "activation_limit", "al", 0, \
    "Terminate saturation after this many iterations of the main loop. 0 means no limit.", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_showAll, "show_everything", "", false, \
    "Turn (almost) all of the showX commands on", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showActive, "show_active", "", false, \
    "Print activated clauses.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showBlocked, "show_blocked", "", false, \
    "Show generating inferences blocked due to coloring of symbols", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showDefinitions, "show_definitions", "", false, \
    "Show definition introductions.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showNew, "show_new", "", false, \
    "Show new (generated) clauses", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_sineToAge, "sine_to_age", "s2a", false, \
    "Use SInE levels to postpone introducing clauses more distant from the conjecture to " \
    "proof search by artificially making them younger (age := sine_level).", \
    OptionTag::SATURATION, false) \
  \
  CHOICE(PredicateSineLevels, _sineToPredLevels, "sine_to_pred_levels", "s2pl", PredicateSineLevels::OFF, \
    ("no","off","on"), \
    "Assign levels to predicate symbols as they are used to trigger axioms during SInE computation. " \
    "Then use them as predicateLevels determining the ordering. 'on' means conjecture symbols " \
    "are larger, 'no' means the opposite. (equality keeps its standard lowest level).", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_showSplitting, "show_splitting", "", false, \
    "Show updates within AVATAR", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showNonconstantSkolemFunctionTrace, "show_nonconstant_skolem_function_trace", "", false, \
    "Show introduction of non-constant skolem functions.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showOptions, "show_options", "", false, \
    "List all available options", \
    OptionTag::HELP, false) \
  \
  BOOL(_showOptionsLineWrap, "show_options_line_wrap", "", true, \
    "Line wrap in show options. Mainly used when options are read by another tool that applies " \
    "its own line wrap.", \
    OptionTag::HELP, true) \
  \
  BOOL(_showExperimentalOptions, "show_experimental_options", "", false, \
    "Include experimental options in showOption", \
    OptionTag::HELP, true) \
  \
  BOOL(_showHelp, "help", "h", false, \
    "Display the help message", \
    OptionTag::HELP, false) \
  \
  BOOL(_printAllTheoryAxioms, "print_theory_axioms", "", false, \
    "Just print all theory axioms and terminate", \
    OptionTag::DEVELOPMENT, true) \
  \
  STRING(_explainOption, "explain_option", "explain", "", \
    "Use to explain a single option i.e. -explain explain", \
    OptionTag::HELP, false) \
  \
  BOOL(_showPassive, "show_passive", "", false, \
    "Show clauses added to the passive set.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showReductions, "show_reductions", "", false, \
    "Show reductions.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showPreprocessing, "show_preprocessing", "", false, \
    "Show preprocessing.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showSkolemisations, "show_skolemisations", "", false, \
    "Show Skolemisations.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showSymbolElimination, "show_symbol_elimination", "", false, \
    "Show symbol elimination.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showTheoryAxioms, "show_theory_axioms", "", false, \
    "Show the added theory axioms.", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_showFOOL, "show_fool", "", false, \
    "Reveal the internal representation of FOOL terms", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_showFMBsortInfo, "show_fmb_sort_info", "", false, \
    "Print information about sorts in FMB", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_showInduction, "show_induction", "", false, \
    "Print information about induction", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_showSimplOrdering, "show_ordering", "", false, \
    "Display the used simplification ordering's parameters.", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_showPropDict, "show_property_dict", "", false, \
    "Display a (python-formatted) dictionary summing up the main properties of the parsed " \
    "problem.", \
    OptionTag::OUTPUT, true) \
  \
  VAMPIRE_IF_CLAUSE_TRACING(INT(_traceBackward, "trace_bwd", "", 0, \
    "The id of a clause you want to see all predecessors (unites used to derive the clause).", \
    OptionTag::OUTPUT, false)) \
  \
  VAMPIRE_IF_CLAUSE_TRACING(INT(_traceForward, "trace_fwd", "", -1, \
    "The id of a clause you want to see all consequences of.", \
    OptionTag::OUTPUT, false)) \
  \
  VAMPIRE_IF_VZ3(BOOL(_showZ3, "show_z3", "", false, \
    "Print the clauses being added to Z3", \
    OptionTag::DEVELOPMENT, false)) \
  \
  VAMPIRE_IF_VZ3(CHOICE(ProblemExportSyntax, _problemExportSyntax, "export_syntax", "", ProblemExportSyntax::SMTLIB, \
    ("smtlib", "api_calls",), \
    "Set the syntax for exporting z3 problems.", \
    OptionTag::DEVELOPMENT, false)) \
  \
  VAMPIRE_IF_VZ3(STRING(_exportAvatarProblem, "export_avatar", "", "", \
    "Export the avatar problems to solve in smtlib syntax.", \
    OptionTag::DEVELOPMENT, false)) \
  \
  VAMPIRE_IF_VZ3(STRING(_exportThiProblem, "export_thi", "", "", \
    "Export the theory instantiation problems to solve in smtlib syntax.", \
    OptionTag::DEVELOPMENT, false)) \
  \
  VAMPIRE_IF_VZ3(BOOL(_satFallbackForSMT, "sat_fallback_for_smt", "sffsmt", false, \
    "If using z3 run a sat solver alongside to use if the smt" \
    " solver returns unknown at any point", \
    OptionTag::SAT, false)) \
  \
  VAMPIRE_IF_VZ3(CHOICE(TheoryInstSimp, _theoryInstAndSimp, "theory_instantiation", "thi", TheoryInstSimp::OFF, \
    ("off", "all", "strong", "neg_eq", "overlap", "full", "new"), \
    "\nEnables theory instantiation rule: \n" \
    "T[x_1, ..., x_n] \\/ C[x_1, ..., x_n]\n" \
    "-------------------------------------\n" \
    "           C[t_1, ..., t_n]          \n" \
    "where  \n" \
    " -  T[x_1, ..., x_n] is a pure theory clause  \n" \
    " - ~T[t_1, ...., t_n] is valid \n\n" \
    "The rule uses an smt solver (i.e. z3 atm) to find t_1...t_n that satisfy the requirement " \
    "for the rule.\n\n" \
    "The different option values define the behaviour of which theory literals to select.\n" \
    "- all    : hmmm.. what could that mean?!\n" \
    "- neg_eq : only negative equalities\n" \
    "- strong : interpreted predicates, but no positive equalities\n" \
    "- overlap: all literals that contain variables that are also contained in a strong literal\n" \
    "- new    : deprecated\n" \
    "- full   : deprecated" \
    "", \
    OptionTag::THEORIES, false)) \
  \
  VAMPIRE_IF_VZ3(BOOL(_thiGeneralise, "theory_instantiation_generalisation", "thigen", false, \
    "Enable retrieval of generalised instances in theory instantiation. This can help with " \
    "datatypes but requires thi to call the smt solver twice. \n\n" \
    " An example of such a generalisation is:\n" \
    " first(x) > 0 \\/ P[x]\n" \
    " ==================== \n" \
    "     P[(-1, y)]\n\n" \
    " instead of the more concrete instance\n" \
    " first(x) > 0 \\/ P[x]\n" \
    " ==================== \n" \
    "     P[(-1, 0)]", \
    OptionTag::THEORIES, true)) \
  \
  VAMPIRE_IF_VZ3(BOOL(_thiTautologyDeletion, "theory_instantiation_tautology_deletion", "thitd", false, \
    "Enable deletion of tautology theory subclauses detected via theory instantiation.", \
    OptionTag::THEORIES, true)) \
  \
  CHOICE(UnificationWithAbstraction, _unificationWithAbstraction, "unification_with_abstraction", "uwa", UnificationWithAbstraction::AUTO, \
    ("auto","off","interpreted_only","one_side_interpreted","one_side_constant","all","ground", "func_ext", "alasca_one_interp", "alasca_can_abstract", "alasca_main", "alasca_main_floor", "hol"), \
    "During unification, if two terms s and t fail to unify we will introduce a constraint " \
    "s!=t and carry on. For example, " \
    "resolving p(1) \\/ C with ~p(a+2) would produce C \\/ 1 !=a+2. This is controlled by " \
    "a check on the terms. The expected " \
    "use case is in theory reasoning. The possible values are:" \
    "- auto: boils down to off for non-theory problems, and to alasca_main whenever alasca " \
    "(on by default) kicks in (except under alasca_integer_conversion, when it becomes alasca_main_floor)\n" \
    "- off: do not introduce a constraint\n" \
    "- interpreted_only: only if s and t have interpreted top symbols\n" \
    "- one_side_interpreted: only if one of s or t have interpreted top symbols\n" \
    "- one_side_constant: only if one of s or t is an interpreted constant (e.g. a number)\n" \
    "- all: always apply\n" \
    "- ground: only if both s and t are ground\n" \
    "- alasca_one_interp, alasca_can_abstract, alasca_main: strategies used for the real-arithmetic " \
    "version of alasca. these are described in  the LPAR2023 paper  \"Refining Unification " \
    "with Abstraction\"" \
    "- alasca_main_floor: an extension of the alasca_main strategy to work with mixed integer-real " \
    "arithmetic. this option is experimental\n" \
    "- hol: introduce constraints for all higher-order parts whose unification is undecidable\n" \
    "See Unification with Abstraction and Theory Instantiation in Saturation-Based Reasoning " \
    "for further details.", \
    OptionTag::THEORIES, false) \
  \
  BOOL(_unificationWithAbstractionFixedPointIteration, "unification_with_abstraction_fixed_point_iteration", "uwa_fpi", false, \
    "The order in which arguments are being processed in unification with absraction can " \
    "yield different results. i.e. unnecessary unifiers. This can be resolved by applying " \
    "unification with absraction multiple times. This option enables this fixed point iteration. " \
    "For details have a look at the paper \"Refining Unification with Abstraction\" from " \
    "LPAR 2023.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_useACeval, "use_ac_eval", "uace", false, \
    "Evaluate associative and commutative operators e.g. + and *.", \
    OptionTag::THEORIES, false) \
  \
  FLOAT(_lrsEstimateCorrectionCoef, "lrs_estimate_correction_coef", "lecc", 1.0, \
    "Make lrs more (<1.0) or less (>1.0) aggressive by multiplying by this coef its estimate " \
    "of how many clauses are still reachable.", \
    OptionTag::LRS, false) \
  \
  STRING(_lrsSaveTraceFile, "lrs_save_trace_file", "lstf", "", \
    "When set, vampire will output a trace of decistions in the LRS estimate module, which " \
    "can be used to reproduce a lucky run.", \
    OptionTag::LRS, false) \
  \
  STRING(_lrsLoadTraceFile, "lrs_load_trace_file", "lltf", "", \
    "When set, vampire will load a previously saved trace of decistions of the LRS estimate " \
    "module, which be used instead of the module's logic to guide the estimates.", \
    OptionTag::LRS, false) \
  \
  UNSIGNED(_sineDepth, "sine_depth", "sd", 0, \
    "Limit number of iterations of the transitive closure algorithm that selects formulas " \
    "based on SInE's D-relation (see SInE description). 0 means no limit, 1 is a maximal " \
    "limit (least selected axioms), 2 allows two iterations, etc...", \
    OptionTag::PREPROCESSING, false) \
  \
  UNSIGNED(_sineGeneralityThreshold, "sine_generality_threshold", "sgt", 0, \
    "Generality of a symbol is the number of input formulas in which a symbol appears." \
    " If the generality of a symbol is smaller than the threshold, it is always included " \
    "into the D-relation with formulas in which it appears." \
    " Note that with the default value (0) this actually never happens." \
    " (And with 1, there would be no difference, because the 1 is used up on the occurrence " \
    "in the already included unit.)", \
    OptionTag::PREPROCESSING, false) \
  \
  UNSIGNED(_sineToAgeGeneralityThreshold, "sine_to_age_generality_threshold", "s2agt", 0, \
    "Like sine_generality_threshold but influences sine_to_age, sine_to_pred_levels, and " \
    "sine_level_split_queue rather than sine_selection.", \
    OptionTag::SATURATION, false) \
  \
  CHOICE(SineSelection, _sineSelection, "sine_selection", "ss", SineSelection::OFF, \
    ("axioms","included","off"), \
    "If 'axioms', all formulas that are not annotated as 'axiom' (i.e. conjectures and hypotheses) " \
    "are initially selected, and the SInE selection is performed on those annotated as 'axiom'. " \
    "If 'included', all formulas that are directly in the problem file are initially selected, " \
    "and the SInE selection is performed on formulas from included files. The 'included' " \
    "value corresponds to the behaviour of the original SInE implementation.", \
    OptionTag::PREPROCESSING, false) \
  \
  FLOAT(_sineTolerance, "sine_tolerance", "st", 1.0, \
    "SInE tolerance parameter (sometimes referred to as 'benevolence')." \
    " Has special value of -1.0 (which effectively codes +infinity), but otherwise must be " \
    "greater or equal 1.0." \
    " For each unit, only its least general symbol (let's call its generality g_min) and " \
    "its symbols with generality up to g_min*tolerance trigger the unit to be included.", \
    OptionTag::PREPROCESSING, false) \
  \
  FLOAT(_sineToAgeTolerance, "sine_to_age_tolerance", "s2at", 1.0, \
    "Like sine_tolerance but influences sine_to_age, sine_to_pred_levels, and sine_level_split_queue " \
    "rather than sine_selection." \
    " Has special value of -1.0, but otherwise must be greater or equal 1.0.", \
    OptionTag::SATURATION, false) \
  \
  CHOICE(Sos, _sos, "sos", "sos", Sos::OFF, \
    ("all","off","on","theory"), \
    "Set of support strategy. All formulas annotated as axioms are put directly among active " \
    "clauses, without performing any inferences between them." \
    " If all, select all literals of set-of-support clauses, otherwise use the default literal " \
    "selector. If theory then only apply to theory" \
    " axioms introduced by vampire (all literals are selected).", \
    OptionTag::PREPROCESSING, false) \
  \
  UNSIGNED(_sosTheoryLimit, "sos_theory_limit", "sstl", 0, \
    "When sos=theory, limit the depth of descendants a theory axiom can have.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_splitting, "avatar", "av", true, \
    "Use AVATAR splitting.", \
    OptionTag::AVATAR, false) \
  \
  BOOL(_splitAtActivation, "split_at_activation", "sac", false, \
    "Split a clause when it is activated, default is to split when it is processed", \
    OptionTag::AVATAR, false) \
  \
  BOOL(_cleaveNonsplittables, "cleave_nonsplittables", "cn", false, \
    "Tentatively propose single-literal component strengthenings. Sometimes useful for bringing " \
    "about finite saturations.", \
    OptionTag::AVATAR, false) \
  \
  CHOICE(SplittingAddComplementary, _splittingAddComplementary, "avatar_add_complementary", "aac", SplittingAddComplementary::GROUND, \
    ("ground","none"), \
    "", \
    OptionTag::AVATAR, false) \
  \
  BOOL(_splittingCongruenceClosure, "avatar_congruence_closure", "acc", false, \
    "Use a congruence closure decision procedure on top of the AVATAR SAT solver. This ensures " \
    "that models produced by AVATAR satisfy the theory of uninterpreted functions.", \
    OptionTag::AVATAR, false) \
  \
  FLOAT(_splittingAvatimer, "avatar_turn_off_time_frac", "atotf", 1.0, \
    "Stop splitting after the specified fraction of the overall time has passed (the default " \
    "1.0 means AVATAR runs until the end).\n" \
    "(the remaining time AVATAR is still switching branches and communicating with the SAT " \
    "solver,\n" \
    "but not introducing new splits anymore. This fights the theoretical possibility of AVATAR's " \
    "dynamic incompleteness.)", \
    OptionTag::AVATAR, false) \
  \
  CHOICE(SplittingNonsplittableComponents, _splittingNonsplittableComponents, "avatar_nonsplittable_components", "anc", SplittingNonsplittableComponents::KNOWN, \
    ("all","all_dependent","known","none"), \
    "Decide what to do with a nonsplittable component:\n" \
    "  -known: SAT clauses will be learnt from non-splittable clauses that have corresponding " \
    "components (if there is a component C with name SAT l, clause C | {l1,..ln} will give " \
    "SAT clause ~l1 \\/ … \\/ ~ln \\/ l). When we add the sat clause, we discard the original " \
    "FO clause C | {l1,..ln} and let the component selection update model, possibly adding " \
    "the component clause C | {l}.\n" \
    "  -all: like known, except when we see a non-splittable clause that doesn't have a name, " \
    "we introduce the name for it.\n" \
    "  -all_dependent: like all, but we don't introduce names for non-splittable clauses " \
    "that don't depend on any components", \
    OptionTag::AVATAR, false) \
  \
  BOOL(_splittingMinimizeModel, "avatar_minimize_model", "amm", true, \
    "Minimize the SAT-solver model by replacing concrete values with don't-cares" \
    " provided the sat clauses remain provably satisfied by the partial model.", \
    OptionTag::AVATAR, false) \
  \
  CHOICE(SplittingLiteralPolarityAdvice, _splittingLiteralPolarityAdvice, "avatar_literal_polarity_advice", "alpa", SplittingLiteralPolarityAdvice::NONE, \
    ("false","true","none","random"), \
    "Override SAT-solver's default polarity/phase setting for variables abstracting clause " \
    "components.", \
    OptionTag::AVATAR, false) \
  \
  CHOICE(SplittingDeleteDeactivated, _splittingDeleteDeactivated, "avatar_delete_deactivated", "add", SplittingDeleteDeactivated::LARGE_ONLY, \
    ("on","large","off"), \
    "", \
    OptionTag::AVATAR, false) \
  \
  CHOICE(Statistics, _statistics, "statistics", "stat", Statistics::BRIEF, \
    ("brief","full","none"), \
    "The level of statistics to report at the end of the run.", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_superpositionFromVariables, "superposition_from_variables", "sfv", true, \
    "Perform superposition from variables.", \
    OptionTag::INFERENCES, false) \
  \
  CHOICE(TermOrdering, _termOrdering, "term_ordering", "to", TermOrdering::AUTO_KBO, \
    ("auto_kbo","kbo","qkbo","lakbo","lpo","incomp"), \
    "The term ordering used by Vampire to orient equations and order literals.\n" \
    "possible values:\n" \
    "- auto_kbo: boils down to kbo for non-theory problems and to qkbo, whenever alasca (on " \
    "by default) kicks in\n" \
    "- kbo: Knuth-Bendix Ordering\n" \
    "- qkbo: QKBO ordering as described in the TACAS 2023 paper \"ALASCA: Reasoning in Quantified " \
    "Linear Arithmetic\"\n" \
    "- lpo: Lexicographical Path Ordering\n" \
    "- lakbo: similar to QKBO but for mixed integer-real arithmetic. this option is experimental", \
    OptionTag::SATURATION, false) \
  \
  CHOICE(SymbolPrecedence, _symbolPrecedence, "symbol_precedence", "sp", SymbolPrecedence::FREQUENCY, \
    ("arity","occurrence","reverse_arity","unary_first", "const_max", "const_min", "scramble","frequency","unary_frequency","const_frequency", "reverse_frequency"), \
    "Vampire uses term orderings which require a precedence relation between symbols.\n" \
    "Arity orders symbols by their arity (and reverse_arity takes the reverse of this) and " \
    "occurrence orders symbols by the order they appear in the problem. " \
    "Then we have a few precedence generating schemes adopted from E: frequency - sort by " \
    "frequency making rare symbols large, reverse does the opposite, " \
    "(For the weighted versions, each symbol occurrence counts as many times as is the length " \
    "of the clause in which it occurs.) " \
    "unary_first is like arity, except that unary symbols are maximal (and ties are broken " \
    "by frequency), " \
    "unary_frequency is like frequency, except that unary symbols are maximal, " \
    "const_max makes constants the largest, then falls back to arity, " \
    "const_min makes constants the smallest, then falls back to reverse_arity, " \
    "const_frequency makes constants the smallest, then falls back to frequency.", \
    OptionTag::SATURATION, false) \
  \
  CHOICE(SymbolPrecedenceBoost, _symbolPrecedenceBoost, "symbol_precedence_boost", "spb", SymbolPrecedenceBoost::NONE, \
    ("none","goal","units","goal_then_units", "non_intro","intro"), \
    "Boost the symbol precedence of symbols occurring in certain kinds of clauses in the " \
    "input.\n" \
    "Additionally, non_intro/intro suppress/boost the precedence of symbols introduced during " \
    "preprocessing (i.e., mainly, the naming predicates and the skolems).", \
    OptionTag::SATURATION, false) \
  \
  CHOICE(IntroducedSymbolPrecedence, _introducedSymbolPrecedence, "introduced_symbol_precedence", "isp", IntroducedSymbolPrecedence::TOP, \
    ("top","bottom"), \
    "Decides where to place symbols introduced during proof search in the symbol precedence", \
    OptionTag::SATURATION, false) \
  \
  CHOICE(EvaluationMode, _evaluationMode, "evaluation", "ev", EvaluationMode::SIMPLE, \
    ("off","simple","force","cautious"), \
    "Chooses the algorithm used to simplify interpreted integer, rational, and real terms. \
                                 \
    - simple: will only evaluate expressions built from interpreted constants only.\
    - cautious: will evaluate abstract expressions to a weak polynomial normal form. This is more powerful but may fail in some rare cases where the resulting polynomial is not strictly smaller than the initial one wrt. the simplification ordering. In these cases a new clause with the normal form term will be added to the search space instead of replacing the original clause.  \
    - force: same as `cautious`, but ignoring the simplification ordering and replacing the hypothesis with the normal form clause in any case. \
    ", \
    OptionTag::THEORIES, true) \
  \
  CHOICE(KboWeightGenerationScheme, _kboWeightGenerationScheme, "kbo_weight_scheme", "kws", KboWeightGenerationScheme::CONST, \
    ("const","random","arity","inv_arity","arity_squared","inv_arity_squared", "precedence","inv_precedence","frequency","inv_frequency"), \
    "Weight generation schemes from KBO inspired by E. This gets overridden by the function_weights " \
    "option if used.", \
    OptionTag::SATURATION, true) \
  \
  BOOL(_kboMaxZero, "kbo_max_zero", "kmz", false, \
    "Modifies any kbo_weight_scheme by setting the maximal (by the precedence) function symbol " \
    "to have weight 0.", \
    OptionTag::SATURATION, true) \
  \
  CHOICE(KboAdmissibilityCheck, _kboAdmissabilityCheck, "kbo_admissibility_check", "", KboAdmissibilityCheck::ERROR, \
    ("error","warning"), \
    "Choose to emit a warning instead of throwing an exception if the weight function and " \
    "precedence ordering for kbo are not compatible.", \
    OptionTag::SATURATION, true) \
  \
  STRING(_functionWeights, "function_weights", "fw", "", \
    "Path to a file that defines weights for KBO for function symbols.\n\n" \
    "Each line in the file is expected to contain a function name, followed by the functions " \
    "arity, and a positive integer, that specifies symbols weight.\n\n" \
    "Additionally there are special values that can be specified:\n" \
    "- `$default    <number>` specifies the default symbol weight, that is used for all symbols " \
    "not present in the file (if not specified 0 is used)\n" \
    "- `$introduced <number>` specifies the weight used for symbols introduced during preprocessing " \
    "or proof search\n" \
    "- `$var        <number>` specifies the weight used for variables\n" \
    "- `$int        <number>` specifies the weight used for integer constants\n" \
    "- `$rat        <number>` specifies the weight used for rational constants\n" \
    "- `$real       <number>` specifies the weight used for real constants\n\n\n" \
    "===== example ============\n" \
    "$add 2 2\n" \
    "$mul 2 7\n" \
    "f    1 2\n" \
    "$default 2\n" \
    "$var     2\n" \
    "===== end of example =====\n\n" \
    "If this option is empty all weights default to 1.\n", \
    OptionTag::LAST_TAG, true) \
  \
  STRING(_typeConPrecedence, "type_con_precedence", "tcp", "", \
    "A name of a file with an explicit user specified precedence on type constructor symbols.", \
    OptionTag::LAST_TAG, true) \
  \
  STRING(_functionPrecedence, "function_precedence", "fp", "", \
    "A name of a file with an explicit user specified precedence on function symbols.", \
    OptionTag::LAST_TAG, true) \
  \
  STRING(_predicatePrecedence, "predicate_precedence", "pp", "", \
    "A name of a file with an explicit user specified precedence on predicate symbols.", \
    OptionTag::LAST_TAG, true) \
  \
  STRING(_testId, "test_id", "", "unspecified_test", \
    "", \
    OptionTag::LAST_TAG, true) \
  \
  CHOICE(Output, _outputMode, "output_mode", "om", Output::SZS, \
    ("smtcomp","spider","szs","vampire","ucore"), \
    "Change how Vampire prints the final result. SZS uses TPTP's SZS ontology. smtcomp mode" \
    " suppresses all output and just prints sat/unsat. vampire is the same as SZS just without " \
    "the SZS." \
    " Spider prints out some profile information and extra error reports. ucore uses the " \
    "smt-lib ucore output.", \
    OptionTag::OUTPUT, false) \
  \
  BOOL(_ignoreMissingInputsInUnsatCore, "ignore_missing_inputs_in_unsat_core", "", false, \
    "When running in unsat core output mode we will complain if there is" \
    " an input formula that has no label. Set this on if you don't want this behaviour (which " \
    "is default in smt-comp).", \
    OptionTag::OUTPUT, false) \
  \
  STRING(_thanks, "thanks", "", "Tanya", \
    "", \
    OptionTag::LAST_TAG, true) \
  \
  CHOICE(TheoryAxiomLevel, _theoryAxioms, "theory_axioms", "tha", TheoryAxiomLevel::ON, \
    ("on","off","some"), \
    "Include theory axioms for detected interpreted symbols", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_theoryFlattening, "theory_flattening", "thf", false, \
    "Flatten clauses to separate theory and non-theory parts in the input. This is often " \
    "quickly undone in proof search.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_ignoreUnrecognizedLogic, "ignore_unrecognized_logic", "iul", false, \
    "Try proof search anyways, if vampire would throw an \"unrecognized logic\" error otherwise.", \
    OptionTag::INPUT, false) \
  \
  VAMPIRE_IF_TIME_PROFILING(BOOL(_timeStatistics, "time_statistics", "tstat", false, \
    "Show how much running time was spent in each part of Vampire", \
    OptionTag::OUTPUT, false)) \
  \
  VAMPIRE_IF_TIME_PROFILING(STRING(_timeStatisticsFocus, "time_statistics_focus", "tstat_focus", "", \
    "focus on some special subtree of the time statistics", \
    OptionTag::OUTPUT, false)) \
  \
  CHOICE(URResolution, _unitResultingResolution, "unit_resulting_resolution", "urr", URResolution::OFF, \
    ("ec_only","off","on","full"), \
    "Uses unit resulting resolution only to derive empty clauses (may be useful for splitting)." \
    " 'ec_only' only derives empty clauses, 'on' does everything (but implements a heuristic " \
    "to skip deriving more than one empty clause)," \
    " 'full' ignores this heuristic and is thus complete also under AVATAR.", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_unusedPredicateDefinitionRemoval, "unused_predicate_definition_removal", "updr", true, \
    "Attempt to remove predicate definitions. A predicate definition is a formula of the " \
    "form ![X1,..,Xn] : (p(X1,..,XN) <=> F) where p is not equality and does not occur in " \
    "F and X1,..,XN are the free variables of F. If p has only positive (negative) occurrences " \
    "then <=> in the definition can be replaced by => (<=). If p does not occur in the rest " \
    "of the problem the definition can be removed.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_blockedClauseElimination, "blocked_clause_elimination", "bce", false, \
    "Eliminate blocked clauses after clausification.", \
    OptionTag::PREPROCESSING, false) \
  \
  CHOICE(PredicateElimination, _predicateElimination, "predicate_elimination", "pel", PredicateElimination::OFF, \
    ("off","on","multi"), \
    "After clausification, eliminate predicates that occur at most once in every clause" \
    " by replacing their clauses with all pairwise resolvents (cf. Khasidashvili and Korovin, " \
    "SAT 2016)." \
    " With multi, also eliminate a predicate P occurring more than once in a clause, provided " \
    "P" \
    " never occurs both positively and negatively in a single clause and the multi-occurrence" \
    " clauses all sit on one polarity side. Instead of pairwise resolvents, the replacement " \
    "clauses" \
    " are then all the hyper-resolvents, each occurrence of a multi-occurrence clause being " \
    "resolved" \
    " against its own (variable-disjoint) copy of a single-occurrence clause of the opposite " \
    "polarity." \
    " On problems without equality and theories, resolvents are computed with an mgu;" \
    " otherwise argument disequalities are introduced via (virtual) flattening," \
    " which may add equality to a problem previously without it.", \
    OptionTag::PREPROCESSING, false) \
  \
  FLOAT(_predicateEliminationTotalLimit, "predicate_elimination_total_limit", "peltl", 2.0, \
    "A predicate elimination step is only performed if the estimated number of clauses afterwards" \
    " (current - |S_P| - |S_~P| + the number of resolvents, which is |S_P|*|S_~P| unless" \
    " predicate_elimination is set to multi) does not exceed the number of clauses" \
    " before predicate elimination started times this factor.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_predicateEliminationSubsumption, "predicate_elimination_subsumption", "pels", true, \
    "Keep the clause set forward-inter-subsumed and subsumption-resolved during predicate " \
    "elimination.", \
    OptionTag::PREPROCESSING, false) \
  \
  UNSIGNED(_distinctGroupExpansionLimit, "distinct_group_expansion_limit", "dgel", 140, \
    "If a distinct group (defined, e.g., via TPTP's $distinct)" \
    " is not larger than this limit, it will be expanded during preprocessing into quadratically " \
    "many disequalities." \
    " (0 means `always expand`)", \
    OptionTag::INPUT, false) \
  \
  BOOL(_restrictNWCtoGC, "restrict_nwc_to_goal_constants", "rnwc", false, \
    "restrict nongoal_weight_coefficient to those containing goal constants", \
    OptionTag::SATURATION, false) \
  \
  BOOL(_newCNF, "newcnf", "newcnf", false, \
    "Use NewCNF algorithm to do naming, preprocessing and clausification.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_inlineLet, "inline_let", "ile", true, \
    "Always inline let-expressions.", \
    OptionTag::PREPROCESSING, false) \
  \
  BOOL(_manualClauseSelection, "manual_cs", "", false, \
    "Run Vampire interactively by manually picking the clauses to be selected", \
    OptionTag::DEVELOPMENT, false) \
  \
  BOOL(_inequalityNormalization, "normalize_inequalities", "norm_ineq", false, \
    "Enable normalizing of inequalities like s < t ==> 0 < t - s.", \
    OptionTag::THEORIES, false) \
  \
  BOOL(_pushUnaryMinus, "push_unary_minus", "pum", false, \
    "Enable the immediate simplifications:\n" \
    " -(t + s) ==> -t + -s\n" \
    " -(-t) ==> t\n", \
    OptionTag::THEORIES, false) \
  \
  CHOICE(ArithmeticSimplificationMode, _gaussianVariableElimination, "gaussian_variable_elimination", "gve", ArithmeticSimplificationMode::OFF, \
    ("force", "cautious", "off"), \
    "Enable the immediate simplification \"Gaussian Variable Elimination\":\n" "\n" "s != t \\/ C[X] \n" "--------------  if s != t can be rewritten to X != r \n" "    C[r] \n" "\n" "Example:\n" "\n" "6 * X0 != 2 * X1 | p(X0, X1)\n" "-------------------------------\n" "  p(2 * X1 / 6, X1)\n" "\n" "\n" "For a more detailed description see the paper Making Theory Reasoning Simpler ( https://easychair.org/publications/preprint/K2hb ). \
          In some rare cases the conclusion may be not strictly simpler than the hypothesis. With `force` we ignore these cases, violating the ordering and just simplifying \
          anyways. With `cautious` we will generate a new clause instead of simplifying in these cases.", \
    OptionTag::THEORIES, false) \
  \
  BOOL(_alasca, "abstracting_linear_arithmetic_superposition_calculus", "alasca", false, \
    "Enables the Linear Arithmetic Superposition CAlculus, a calculus for linear real arithmetic " \
    "with uninterpretd functions. It is described in the LPAR2023 paper \"ALASCA: Reasoning " \
    "in Quantified Linear Arithmetic\"\n", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_viras, "virtual_integer_real_arithmetic_substitution", "viras", true, \
    "Enables the VIRAS quantifier elimination to be used in ALASCA. The VIRAS method is explained " \
    "in the LPAR2024 paper \"VIRAS: Conflict-Driven Quantifier Elimination for Integer-Real " \
    "Arithmetic\"\n", \
    OptionTag::INFERENCES, true) \
  \
  BOOL(_alascaDemodulation, "alasca_demodulation", "alasca_demod", false, \
    "Enables the linear arithmetic demodulation rule\n", \
    OptionTag::INFERENCES, true) \
  \
  BOOL(_alascaStrongNormalization, "alasca_strong_normalziation", "alasca_sn", false, \
    "enables stronger normalizations for inequalities: \n" \
    "s >= 0 ==> s > 0 \\/  s == 0\n" \
    "s != 0 ==> s > 0 \\/ -s  > 0\n\n", \
    OptionTag::INFERENCES, false) \
  \
  BOOL(_alascaIntegerConversion, "alasca_integer_conversion", "alascai", false, \
    "enables converting integer problems into LIRA problems where there is only the sort " \
    "of reals by" \
    "replacing integer variables with floor functions and transforming the signature appropriately\n", \
    OptionTag::INFERENCES, true) \
  \
  BOOL(_alascaAbstraction, "alasca_abstraction", "alascaa", false, \
    "Enables the alasca abstraction rule. This is an experimental rule not yet finished.\n", \
    OptionTag::INFERENCES, true) \
  \
  CHOICE(ArithmeticSimplificationMode, _cancellation, "cancellation", "canc", ArithmeticSimplificationMode::OFF, \
    ("force", "cautious", "off"), \
    "Enables the rule cancellation around additions as described in the paper Making Theory Reasoning Simpler ( https://easychair.org/publications/preprint/K2hb ). \
                                In some rare cases the conclusion may be not strictly simpler than the hypothesis. With `force` we ignore these cases, violating the ordering and just simplifying \
                                anyways. With `cautious` we will generate a new clause instead of simplifying in these cases.", \
    OptionTag::THEORIES, false) \
  \
  CHOICE(ArithmeticSimplificationMode, _arithmeticSubtermGeneralizations, "arithmetic_subterm_generalizations", "asg", ArithmeticSimplificationMode::OFF, \
    ("force", "cautious", "off"), \
    "\
          Enables various generalization rules for arithmetic terms as described in the paper Making Theory Reasoning Simpler ( https://easychair.org/publications/preprint/K2hb ). \
          In some rare cases the conclusion may be not strictly simpler than the hypothesis. With `force` we ignore these cases, violating the ordering and just simplifying \
          anyways. With `cautious` we will generate a new clause instead of simplifying in these cases.", \
    OptionTag::THEORIES, false) \
  \
  CHOICE(HPrinting, _holPrinting, "pretty_hol_printing", "php", HPrinting::TPTP, \
    ("raw", "db", "pretty", "tptp"), \
    "Various methods of printing higher-order terms: \n" \
    " -raw : prints the internal representation of terms \n" \
    " -pretty : converts internal representation to something resembling textbook notation \n" \
    " -tptp : matches tptp standards \n" \
    " -db : same as tptp, except that De Bruijn indices printed instead of named variables", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_choiceAxiom, "choice_ax", "cha", false, \
    "Adds the cnf form of the Hilbert choice axiom", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_injectivity, "injectivity", "inj", false, \
    "Attempts to identify injective functions and postulates a left-inverse", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_choiceReasoning, "choice_reasoning", "chr", false, \
    "Reason about choice by adding relevant instances of the axiom", \
    OptionTag::HIGHER_ORDER, false) \
  \
  CHOICE(FunctionExtensionality, _functionExtensionality, "func_ext", "fe", FunctionExtensionality::OFF, \
    ("off", "axiom", "abstraction"), \
    "Deal with extensionality using abstraction, axiom or neither", \
    OptionTag::HIGHER_ORDER, false) \
  \
  CHOICE(CNFOnTheFly, _clausificationOnTheFly, "cnf_on_the_fly", "cnfonf", CNFOnTheFly::EAGER, \
    ("eager", "lazy_gen", "lazy_simp", "lazy_not_gen", "lazy_pi_sigma_gen", "lazy_not_gen_be_off", "lazy_not_be_gen", "conj_eager", "off"), \
    "Various options linked to clausification on the fly", \
    OptionTag::HIGHER_ORDER, false) \
  \
  CHOICE(PISet, _piSet, "prim_inst_set", "piset", PISet::PRAGMATIC, \
    ("all", "all_but_not_eq", "not", "small_set", "pragmatic", "and", "or", "equals", "pi_sigma"), \
    "Controls the set of equations to use in primitive instantiation", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_equalityToEquivalence, "equality_to_equiv", "e2e", false, \
    "Equality between boolean terms changed to equivalence \n" \
    "t1 : $o = t2 : $o is changed to t1 <=> t2", \
    OptionTag::LAST_TAG, false) \
  \
  BOOL(_complexBooleanReasoning, "complex_bool_reasoning", "cbe", true, \
    "Switches on primitive instantiation and elimination of leibniz equality", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_booleanEqTrick, "bool_eq_trick", "bet", false, \
    "Replace an equality between boolean terms such as: " \
    "t = s with a disequality t != vnot(s)" \
    " The theory is that this can help with EqRes", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_heuristicInstantiation, "heur_inst", "hi", false, \
    "Heuristically instantiates universally quantified variables with abstractions of literals " \
    "from negated conjecture", \
    OptionTag::HIGHER_ORDER, false) \
  \
  UNSIGNED(_higherOrderUnifDepth, "hol_unif_depth", "hud", 2, \
    "Set the maximum depth (in terms of projections and imitations) that higher-order unification " \
    "can descend to." \
    "Once limit is reached, remaining pairs are returned as constraints.", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_casesSimp, "cases_simp", "cs", false, \
    "FOOL Paramodulation with two conclusion as a simplification", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_cases, "cases", "c", false, \
    "Alternative to FOOL Paramodulation that replaces all Boolean subterms in one step", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_newTautologyDel, "new_taut_del", "ntd", false, \
    "Delete clauses with literals of the form false != true or t = true \\/ t = false", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_positiveExt, "pos_ext", "pe", false, \
    "Enables the following inference\n" \
    "C \\/ t X = s X \n" \
    "----------------\n" \
    "  C \\/ t = s   \n" \
    "where X doesn't occur in t,s or C", \
    OptionTag::HIGHER_ORDER, false) \
  \
  BOOL(_iffXorRewriter, "iff_xor_rewriter", "ixr", true, \
    "Rewrites p <=> q = $true to p <=> q and the like. It does this as an immediate simplification.", \
    OptionTag::HIGHER_ORDER, false)

    //==========================================================
    // The Internals
    //==========================================================
    // Here I define the internal structures used to specify Options
    // Normally these are not modified, see below for getters and values
    //
    // The internals consist of
    // - OptionChoiceValues: to store the names of a option choice
    // - OptionValue: stores an options value and meta-data
    // - OptionValueConstraint: to give a constraint on an option
    // - OptionProblemConstraint: to give a constraint on an option wrt the problem
    //
    // The details are explained in comments below
private:
    // helper function of sampleStrategy
    void strategySamplingAssign(std::string optname, std::string value, DHMap<std::string,std::string, FnvHash, LengthHash>& fakes);
    std::string strategySamplingLookup(std::string optname, DHMap<std::string,std::string, FnvHash, LengthHash>& fakes);

    /**
     * These store the names of the choices for an option.
     * They can be declared using initializer lists i.e. {"on","off","half_on"}
     *
     * TODO: this uses a linear search, for alternative see NameArray
     *
     * @author Giles
     * @since 30/07/14
     */
    class OptionChoiceValues{
    public:
        OptionChoiceValues() = default;
        OptionChoiceValues(std::initializer_list<std::string_view> list) : _names(list)
        {
#if VDEBUG
          for (auto x : list)
            ASS(x.length() < 70) // or else cannot be printed on a line
#endif
        }

        int find(std::string_view value) const {
            for(unsigned i=0;i<_names.size();i++){
                if(value == _names[i]) return i;
            }
            return -1;
        }
        const int length() const { return _names.size(); }
        std::string_view operator[](unsigned i) const{ return _names[i];}

    private:
        Stack<std::string_view> _names;
    };

    /**
     * We now define particular OptionValues, see NOTE on OptionValues for high level usage
     */

    /**
     * A ChoiceOptionValue is templated by an enum, which must be defined above
     *
     * It is then necessary to provide names for the enum values.
     * We do not check that those names have the same length as the enum but this is very important.
     * The names must also be in the same order!
     *
     * @author Giles
     */
    template<typename T >
    struct ChoiceOptionValue : public OptionValue<T> {
        ChoiceOptionValue(){}
        ChoiceOptionValue(const char *l, const char *s,T def,OptionChoiceValues c) :
        OptionValue<T>(l,s,def), choices(c) {}

        bool setValue(const std::string& value) override{
            // makes reasonable assumption about ordering of every enum
            int index = choices.find(value.c_str());
            if(index<0) return false;
            this->actualValue = static_cast<T>(index);
            return true;
        }

        void output(std::ostream& out,bool linewrap) const override {
            AbstractOptionValue::output(out,linewrap);
            out << "\tdefault: " << choices[static_cast<unsigned>(this->defaultValue)];
            out << std::endl;
            std::string values_header = "values: ";
            out << "\t" << values_header;
            // Again we restrict line length to 70 characters
            int count=0;
            for(int i=0;i<choices.length();i++){
                if(i==0){
                    out << choices[i];
                }
                else{
                    out << ",";
                    auto next = choices[i];
                    if(linewrap && next.size()+count>60){ // next.size() will be <70, how big is a tab?
                        out << std::endl << "\t";
                        for(unsigned j=0;j<values_header.size();j++){out << " ";}
                        count = 0;
                    }
                    out << next;
                    count += next.size();
                }
            }
            out << std::endl;
        }

        std::string getStringOfValue(T value) const override {
            unsigned i = static_cast<unsigned>(value);
            return std::string(choices[i]);
        }

    private:
        OptionChoiceValues choices;
    };


    /**
     * For Booleans - we use on/off rather than true/false
     * @author Giles
     */
    struct BoolOptionValue : public OptionValue<bool> {
        BoolOptionValue(const char *l, const char *s, bool d) : OptionValue(l,s,d){}
        bool setValue(const std::string& value) override{
            if (! value.compare("on") || ! value.compare("true")) {
                actualValue=true;

            }
            else if (! value.compare("off") || ! value.compare("false")) {
                actualValue=false;
            }
            else return false;

            return true;
        }

        std::string getStringOfValue(bool value) const override { return (value ? "on" : "off"); }
    };

    struct IntOptionValue : public OptionValue<int> {
        IntOptionValue(const char *l,const char *s, int d) : OptionValue(l,s,d){}
        bool setValue(const std::string& value) override{
            return Int::stringToInt(value.c_str(),actualValue);
        }
        std::string getStringOfValue(int value) const override{ return Lib::Int::toString(value); }
    };

    struct UnsignedOptionValue : public OptionValue<unsigned> {
        UnsignedOptionValue(const char *l,const char *s, unsigned d) : OptionValue(l,s,d){}

        bool setValue(const std::string& value) override{
            return Int::stringToUnsignedInt(value.c_str(),actualValue);
        }
        std::string getStringOfValue(unsigned value) const override{ return Lib::Int::toString(value); }
    };

    struct StringOptionValue : public OptionValue<std::string> {
        StringOptionValue(const char *l,const char *s, std::string d) : OptionValue(l,s,d){}
        bool setValue(const std::string& value) override{
            actualValue = (value=="<empty>") ? "" : value;
            return true;
        }
        std::string getStringOfValue(std::string value) const override{
            if(value.empty()) return "<empty>";
            return value;
        }
    };

    struct LongOptionValue : public OptionValue<long> {
        LongOptionValue(const char *l,const char *s, long d) : OptionValue(l,s,d){}
        bool setValue(const std::string& value) override{
            return Int::stringToLong(value.c_str(),actualValue);
        }
        std::string getStringOfValue(long value) const override{ return Lib::Int::toString(value); }
    };

    struct FloatOptionValue : public OptionValue<float> {
        FloatOptionValue(const char *l,const char *s, float d) : OptionValue(l,s,d){}
        bool setValue(const std::string& value) override{
            return Int::stringToFloat(value.c_str(),actualValue);
        }
        std::string getStringOfValue(float value) const override{ return Lib::Int::toString(value); }
    };

struct RatioOptionValue : public OptionValue<std::pair<unsigned, unsigned>> {
RatioOptionValue(const char *l, const char *s, std::pair<unsigned, unsigned> def, char sp=':') :
OptionValue(l,s,def), sep(sp) {};

bool readRatio(const char* val,char separator);
bool setValue(const std::string& value) override {
    return readRatio(value.c_str(),sep);
}

char sep;

void output(std::ostream& out,bool linewrap) const override {
    AbstractOptionValue::output(out,linewrap);
    out << "\tdefault left: " << defaultValue.first << std::endl;
    out << "\tdefault right: " << defaultValue.second << std::endl;
}

std::string getStringOfActual() const override {
  return Lib::Int::toString(actualValue.first)+sep+Lib::Int::toString(actualValue.second);
}
};

// We now have a number of option-specific values
// These are necessary when the option needs to be read in a special way

/**
* Oddly gets set with a float value and then creates a ratio of value*100/100
* @author Giles
*/
struct NonGoalWeightOptionValue : public OptionValue<float>{
NonGoalWeightOptionValue(const char *l, const char *s) :
OptionValue(l,s,10.0), numerator(10), denominator(1) {};

bool setValue(const std::string& value) override;

// output does not output numerator and denominator as they
// are produced from defaultValue
int numerator;
int denominator;

std::string getStringOfValue(float value) const override{ return Lib::Int::toString(value); }
};

/**
* Selection is defined by a set of integers (TODO: make enum)
* For now we need to check the integer is a valid one
* @author Giles
*/
struct SelectionOptionValue : public OptionValue<int>{
SelectionOptionValue(const char *l,const char *s, int def):
OptionValue(l,s,def){};

bool setValue(const std::string& value) override;

void output(std::ostream& out,bool linewrap) const override {
    AbstractOptionValue::output(out,linewrap);
    out << "\tdefault: " << defaultValue << std::endl;;
}

std::string getStringOfValue(int value) const override{ return Lib::Int::toString(value); }

auto isLookAheadSelection();
};

/**
* This also updates problemName
* @author Giles
*/
struct InputFileOptionValue : public OptionValue<std::string>{
InputFileOptionValue(const char *l,const char *s, std::string def,Options* p):
OptionValue(l,s,def), parent(p){};

bool setValue(const std::string& value) override;

void output(std::ostream& out,bool linewrap) const override {
    AbstractOptionValue::output(out,linewrap);
    out << "\tdefault: " << defaultValue << std::endl;;
}
std::string getStringOfValue(std::string value) const override{ return value; }
private:
Options* parent;

};

/**
* We need to decode the encoded option string
* @author Giles
*/
struct DecodeOptionValue : public OptionValue<std::string>{
    DecodeOptionValue(const char *l,const char *s,Options* p)
        : OptionValue(l,s,""), parent(p){}

bool setValue(const std::string& value) override{
    parent->readFromEncodedOptions(value);
    return true;
}
std::string getStringOfValue(std::string value) const override{ return value; }
private:
Options* parent = nullptr;

};
/**
* Need to read the time limit. By default it assumes seconds (and stores deciseconds) but you can give
* a multiplier i.e. d,s,m,h,D for deciseconds,seconds,minutes,hours,Days
* @author Giles
*/
struct TimeLimitOptionValue : public OptionValue<int>{
TimeLimitOptionValue(const char *l, const char *s, float def) :
OptionValue(l,s,def) {};

bool setValue(const std::string& value) override;

void output(std::ostream& out,bool linewrap) const override {
    AbstractOptionValue::output(out,linewrap);
    out << "\tdefault: " << defaultValue << "d" << std::endl;
}
std::string getStringOfValue(int value) const override{ return Lib::Int::toString(value)+"d"; }
};

  //==========================================================
  // Getter functions
  // -currently disabled all unnecessary setter functions
  //==========================================================
  //
  // This is how options are accessed so if you add a new option you should add a getter
public:
  bool encodeStrategy() const{ return _encode.actualValue;}
  BadOption getBadOptionChoice() const { return _badOption.actualValue; }
  void setBadOptionChoice(BadOption newVal) { _badOption.actualValue = newVal; }
  std::string forcedOptions() const { return _forcedOptions.actualValue; }
  std::string forbiddenOptions() const { return _forbiddenOptions.actualValue; }
  std::string testId() const { return _testId.actualValue; }
  std::string protectedPrefix() const { return _protectedPrefix.actualValue; }
  Statistics statistics() const { return _statistics.actualValue; }
  void setStatistics(Statistics newVal) { _statistics.actualValue=newVal; }
  Proof proof() const { return _proof.actualValue; }
  bool minimizeSatProofs() const { return _minimizeSatProofs.actualValue; }
  ProofExtra proofExtra() const { return _proofExtra.actualValue; }
  bool traceback() const { return _traceback.actualValue; }
  std::string printProofToFile() const { return _printProofToFile.actualValue; }
  int naming() const { return _naming.actualValue; }

  bool fmbNonGroundDefs() const { return _fmbNonGroundDefs.actualValue; }
  unsigned fmbStartSize() const { return _fmbStartSize.actualValue;}
  float fmbSymmetryRatio() const { return _fmbSymmetryRatio.actualValue; }
  FMBWidgetOrders fmbSymmetryWidgetOrders() { return _fmbSymmetryWidgetOrders.actualValue;}
  FMBSymbolOrders fmbSymmetryOrderSymbols() const {return _fmbSymmetryOrderSymbols.actualValue; }
  FMBAdjustSorts fmbAdjustSorts() const {return _fmbAdjustSorts.actualValue; }
  bool fmbDetectSortBounds() const { return _fmbDetectSortBounds.actualValue; }
  unsigned fmbDetectSortBoundsTimeLimit() const { return _fmbDetectSortBoundsTimeLimit.actualValue; }
  unsigned fmbSizeWeightRatio() const { return _fmbSizeWeightRatio.actualValue; }
  FMBEnumerationStrategy fmbEnumerationStrategy() const { return _fmbEnumerationStrategy.actualValue; }
  bool keepSbeamGenerators() const { return _fmbKeepSbeamGenerators.actualValue; }
  bool fmbUseSimplifyingSolver() const { return _fmbUseSimplifyingSolver.actualValue; }

  Mode mode() const { return _mode.actualValue; }
  Intent intent() const { return _intent.actualValue; }
  Schedule schedule() const { return _schedule.actualValue; }
  std::string scheduleName() const { return _schedule.getStringOfValue(_schedule.actualValue); }
  void setSchedule(Schedule newVal) {  _schedule.actualValue = newVal; }
  std::string scheduleFile() const { return _scheduleFile.actualValue; }
  unsigned multicore() const { return _multicore.actualValue; }
  void setMulticore(unsigned newVal) { _multicore.actualValue = newVal; }
  float slowness() const {return _slowness.actualValue; }
  InputSyntax inputSyntax() const { return _inputSyntax.actualValue; }
  bool normalize() const { return _normalize.actualValue; }
  void setNormalize(bool normalize) { _normalize.actualValue = normalize; }
  GoalGuess guessTheGoal() const { return _guessTheGoal.actualValue; }
  unsigned gtgLimit() const { return _guessTheGoalLimit.actualValue; }

  std::string include() const { return _include.actualValue; }
  std::string inputFile() const { return _inputFile.actualValue; }
  void resetInputFile() { _inputFile.actualValue = ""; }
  int activationLimit() const { return _activationLimit.actualValue; }
  unsigned randomSeed() const { return _randomSeed.actualValue; }
  void setRandomSeed(unsigned seed) { _randomSeed.actualValue = seed; }
  const std::string& strategySamplerFilename() const { return _sampleStrategy.actualValue; }
  bool printClausifierPremises() const { return _printClausifierPremises.actualValue; }
  bool replaceDomainElements() const { return _replaceDomainElements.actualValue; }

  // IMPORTANT, if you add a showX command then include showAll
  bool showAll() const { return _showAll.actualValue; }
  bool showActive() const { return showAll() || _showActive.actualValue; }
  bool showBlocked() const { return showAll() || _showBlocked.actualValue; }
  bool showDefinitions() const { return showAll() || _showDefinitions.actualValue; }
  bool showNew() const { return showAll() || _showNew.actualValue; }
  bool sineToAge() const { return _sineToAge.actualValue; }
  PredicateSineLevels sineToPredLevels() const { return _sineToPredLevels.actualValue; }
  bool showSplitting() const { return showAll() || _showSplitting.actualValue; }
  bool showNewPropositional() const { return showAll() || _showNewPropositional.actualValue; }
  bool showPassive() const { return showAll() || _showPassive.actualValue; }
  bool showReductions() const { return showAll() || _showReductions.actualValue; }
  bool showPreprocessing() const { return showAll() || _showPreprocessing.actualValue; }
  bool showSkolemisations() const { return showAll() || _showSkolemisations.actualValue; }
  bool showSymbolElimination() const { return showAll() || _showSymbolElimination.actualValue; }
  bool showTheoryAxioms() const { return showAll() || _showTheoryAxioms.actualValue; }
  bool showFOOL() const { return showAll() || _showFOOL.actualValue; }
  bool showFMBsortInfo() const { return showAll() || _showFMBsortInfo.actualValue; }
  bool showInduction() const { return showAll() || _showInduction.actualValue; }
  bool showSimplOrdering() const { return showAll() || _showSimplOrdering.actualValue; }
  bool showPropDict() const { return _showPropDict.actualValue; }

#if VAMPIRE_CLAUSE_TRACING
  int traceBackward() { return _traceBackward.actualValue; }
  int traceForward() { return _traceForward.actualValue; }
#endif // VAMPIRE_CLAUSE_TRACING

#if VZ3
  bool showZ3() const { return showAll() || _showZ3.actualValue; }
  ProblemExportSyntax problemExportSyntax() const { return _problemExportSyntax.actualValue; }
  std::string const& exportAvatarProblem() const { return _exportAvatarProblem.actualValue; }
  std::string const& exportThiProblem() const { return _exportThiProblem.actualValue; }
#endif

  // end of show commands

  bool showNonconstantSkolemFunctionTrace() const { return _showNonconstantSkolemFunctionTrace.actualValue; }
  InterpolantMode showInterpolant() const { return _showInterpolant.actualValue; }
  bool showOptions() const { return _showOptions.actualValue; }
  bool lineWrapInShowOptions() const { return _showOptionsLineWrap.actualValue; }
  bool showExperimentalOptions() const { return _showExperimentalOptions.actualValue; }
  bool showHelp() const { return _showHelp.actualValue; }
  std::string explainOption() const { return _explainOption.actualValue; }

  bool printAllTheoryAxioms() const { return _printAllTheoryAxioms.actualValue; }

#if VZ3
  bool satFallbackForSMT() const { return _satFallbackForSMT.actualValue; }
  bool smtForGround() const { return _smtForGround.actualValue; }
  TheoryInstSimp theoryInstAndSimp() const { return _theoryInstAndSimp.actualValue; }
  bool thiGeneralise() const { return _thiGeneralise.actualValue; }
  bool thiTautologyDeletion() const { return _thiTautologyDeletion.actualValue; }
#endif
  UnificationWithAbstraction unificationWithAbstraction() const { return _unificationWithAbstraction.actualValue; }
  bool unificationWithAbstractionFixedPointIteration() const { return _unificationWithAbstractionFixedPointIteration.actualValue; }
  void setUWA(UnificationWithAbstraction value){ _unificationWithAbstraction.actualValue = value; }
  void setUWAFPI(bool fpi) { _unificationWithAbstractionFixedPointIteration.actualValue = fpi; }
  // TODO make alasca independent of normal evaluation
  bool useACeval() const { return _useACeval.actualValue; }

  bool unusedPredicateDefinitionRemoval() const { return _unusedPredicateDefinitionRemoval.actualValue; }
  bool blockedClauseElimination() const { return _blockedClauseElimination.actualValue; }
  PredicateElimination predicateElimination() const { return _predicateElimination.actualValue; }
  float predicateEliminationTotalLimit() const { return _predicateEliminationTotalLimit.actualValue; }
  bool predicateEliminationSubsumption() const { return _predicateEliminationSubsumption.actualValue; }
  bool predicateEliminationMultiOccurrence() const { return _predicateElimination.actualValue == PredicateElimination::MULTI; }
  unsigned distinctGroupExpansionLimit() const { return _distinctGroupExpansionLimit.actualValue; }
  void setUnusedPredicateDefinitionRemoval(bool newVal) { _unusedPredicateDefinitionRemoval.actualValue = newVal; }
  SatSolver satSolver() const { return _satSolver.actualValue; }
  SaturationAlgorithm saturationAlgorithm() const { return _saturationAlgorithm.actualValue; }
  int selection() const { return _selection.actualValue; }
  LiteralComparisonMode literalComparisonMode() const { return _literalComparisonMode.actualValue; }
  bool forwardSubsumptionResolution() const { return _forwardSubsumptionResolution.actualValue; }
  bool forwardSubsumptionDemodulation() const { return _forwardSubsumptionDemodulation.actualValue; }
  unsigned forwardSubsumptionDemodulationMaxMatches() const { return _forwardSubsumptionDemodulationMaxMatches.actualValue; }
  Demodulation forwardDemodulation() const { return _forwardDemodulation.actualValue; }
  bool forwardGroundJoinability() const { return _forwardGroundJoinability.actualValue; }
  bool binaryResolution() const { return _binaryResolution.actualValue; }
  bool superposition() const {return _superposition.actualValue; }
  URResolution unitResultingResolution() const { return _unitResultingResolution.actualValue; }
  bool simulatenousSuperposition() const { return _simultaneousSuperposition.actualValue; }
  bool innerRewriting() const { return _innerRewriting.actualValue; }
  bool equationalTautologyRemoval() const { return _equationalTautologyRemoval.actualValue; }
  bool subsumptionEqualityResolution() const { return _subsumptionEqualityResolution.actualValue; }
  bool partialRedundancyCheck() const { return _partialRedundancyCheck.actualValue; }
  bool partialRedundancyOrderingConstraints() const { return _partialRedundancyOrderingConstraints.actualValue; }
  bool partialRedundancyAvatarConstraints() const { return _partialRedundancyAvatarConstraints.actualValue; }
  bool partialRedundancyLiteralConstraints() const { return _partialRedundancyLiteralConstraints.actualValue; }
  bool arityCheck() const { return _arityCheck.actualValue; }
  bool parseGoalAnnotations() const { return _parseGoalAnnotations.actualValue; }
  Demodulation backwardDemodulation() const { return _backwardDemodulation.actualValue; }
  DemodulationRedundancyCheck demodulationRedundancyCheck() const { return _demodulationRedundancyCheck.actualValue; }
  bool forwardDemodulationTermOrderingDiagrams() const { return _forwardDemodulationTermOrderingDiagrams.actualValue; }
  bool demodulationOnlyEquational() const { return _demodulationOnlyEquational.actualValue; }

  Subsumption backwardSubsumption() const { return _backwardSubsumption.actualValue; }
  Subsumption backwardSubsumptionResolution() const { return _backwardSubsumptionResolution.actualValue; }
  bool backwardSubsumptionDemodulation() const { return _backwardSubsumptionDemodulation.actualValue; }
  unsigned backwardSubsumptionDemodulationMaxMatches() const { return _backwardSubsumptionDemodulationMaxMatches.actualValue; }
  bool forwardSubsumption() const { return _forwardSubsumption.actualValue; }
  bool forwardLiteralRewriting() const { return _forwardLiteralRewriting.actualValue; }
  int lrsFirstTimeCheck() const { return _lrsFirstTimeCheck.actualValue; }
  int lrsWeightLimitOnly() const { return _lrsWeightLimitOnly.actualValue; }
  int lrsRetroactiveDeletes() const { return _lrsRetroactiveDeletes.actualValue; }
  int lrsPreemptiveDeletes() const { return _lrsPreemptiveDeletes.actualValue; }
  int lookaheadDelay() const { return _lookaheadDelay.actualValue; }
  int simulatedTimeLimit() const { return _simulatedTimeLimit.actualValue; }
  void setSimulatedTimeLimit(int newVal) { _simulatedTimeLimit.actualValue = newVal; }
  float lrsEstimateCorrectionCoef() const { return _lrsEstimateCorrectionCoef.actualValue; }
  const std::string& lrsSaveTraceFile() const { return _lrsSaveTraceFile.actualValue; }
  const std::string& lrsLoadTraceFile() const { return _lrsLoadTraceFile.actualValue; }
  TermOrdering termOrdering() const { return _termOrdering.actualValue; }
  SymbolPrecedence symbolPrecedence() const { return _symbolPrecedence.actualValue; }
  SymbolPrecedenceBoost symbolPrecedenceBoost() const { return _symbolPrecedenceBoost.actualValue; }
  IntroducedSymbolPrecedence introducedSymbolPrecedence() const { return _introducedSymbolPrecedence.actualValue; }
  KboWeightGenerationScheme kboWeightGenerationScheme() const { return _kboWeightGenerationScheme.actualValue; }
  bool kboMaxZero() const { return _kboMaxZero.actualValue; }
  const KboAdmissibilityCheck kboAdmissabilityCheck() const { return _kboAdmissabilityCheck.actualValue; }
  const std::string& functionWeights() const { return _functionWeights.actualValue; }
  const std::string& predicateWeights() const { return _predicateWeights.actualValue; }
  const std::string& functionPrecedence() const { return _functionPrecedence.actualValue; }
  const std::string& typeConPrecedence() const { return _typeConPrecedence.actualValue; }
  const std::string& predicatePrecedence() const { return _predicatePrecedence.actualValue; }
  // Return time limit in deciseconds, or 0 if there is no time limit
  int timeLimitInDeciseconds() const { return _timeLimitInDeciseconds.actualValue; }
  size_t memoryLimit() const { return _memoryLimit.actualValue; }
#if VAMPIRE_PERF_EXISTS
  unsigned instructionLimit() const { return _instructionLimit.actualValue; }
  void setInstructionLimit(unsigned newVal) { _instructionLimit.actualValue = newVal; }
  unsigned simulatedInstructionLimit() const { return _simulatedInstructionLimit.actualValue; }
  bool parsingDoesNotCount() const { return _parsingDoesNotCount.actualValue; }
#endif
  bool interactive() const { return _interactive.actualValue; }
  void setInteractive(bool v) { _interactive.actualValue = v; }
  int inequalitySplitting() const { return _inequalitySplitting.actualValue; }
  unsigned ageRatio() const { return _ageWeightRatio.actualValue.first; }
  unsigned weightRatio() const { return _ageWeightRatio.actualValue.second; }
  bool useTheorySplitQueues() const { return _useTheorySplitQueues.actualValue; }
  std::vector<int> theorySplitQueueRatios() const;
  std::vector<float> theorySplitQueueCutoffs() const;
  int theorySplitQueueExpectedRatioDenom() const { return _theorySplitQueueExpectedRatioDenom.actualValue; }
  bool theorySplitQueueLayeredArrangement() const { return _theorySplitQueueLayeredArrangement.actualValue; }
  bool useAvatarSplitQueues() const { return _useAvatarSplitQueues.actualValue; }
  std::vector<int> avatarSplitQueueRatios() const;
  std::vector<float> avatarSplitQueueCutoffs() const;
  bool avatarSplitQueueLayeredArrangement() const { return _avatarSplitQueueLayeredArrangement.actualValue; }
  bool useSineLevelSplitQueues() const { return _useSineLevelSplitQueues.actualValue; }
  std::vector<int> sineLevelSplitQueueRatios() const;
  std::vector<float> sineLevelSplitQueueCutoffs() const;
  bool sineLevelSplitQueueLayeredArrangement() const { return _sineLevelSplitQueueLayeredArrangement.actualValue; }
  bool usePositiveLiteralSplitQueues() const { return _usePositiveLiteralSplitQueues.actualValue; }
  std::vector<int> positiveLiteralSplitQueueRatios() const;
  std::vector<float> positiveLiteralSplitQueueCutoffs() const;
  bool positiveLiteralSplitQueueLayeredArrangement() const { return _positiveLiteralSplitQueueLayeredArrangement.actualValue; }
  bool hoSplitQueues() const { return _hoSplitQueues.actualValue; }
  unsigned hoSplitQueueLambdaWeight() const { return _hoSplitQueueLambdaWeight.actualValue; }
  unsigned hoSplitQueueAppVarWeight() const { return _hoSplitQueueAppVarWeight.actualValue; }
  std::vector<int> hoSplitQueueRatios() const;
  std::vector<float> hoSplitQueueCutoffs() const;
  bool hoSplitQueueLayeredArrangement() const { return _hoSplitQueueLayeredArrangement.actualValue; }
  bool literalMaximalityAftercheck() const { return _literalMaximalityAftercheck.actualValue; }
  bool superpositionFromVariables() const { return _superpositionFromVariables.actualValue; }
  EqualityProxy equalityProxy() const { return _equalityProxy.actualValue; }
  bool equalityResolutionWithDeletion() const { return _equalityResolutionWithDeletion.actualValue; }
  ExtensionalityResolution extensionalityResolution() const { return _extensionalityResolution.actualValue; }
  bool FOOLParamodulation() const { return _FOOLParamodulation.actualValue; }
  bool termAlgebraInferences() const { return _termAlgebraInferences.actualValue; }
  bool termAlgebraExhaustivenessAxiom() const { return _termAlgebraExhaustivenessAxiom.actualValue; }
  TACyclicityCheck termAlgebraCyclicityCheck() const { return _termAlgebraCyclicityCheck.actualValue; }
  unsigned extensionalityMaxLength() const { return _extensionalityMaxLength.actualValue; }
  bool extensionalityAllowPosEq() const { return _extensionalityAllowPosEq.actualValue; }
  unsigned nongoalWeightCoefficientNumerator() const { return _nonGoalWeightCoefficient.numerator; }
  unsigned nongoalWeightCoefficientDenominator() const { return _nonGoalWeightCoefficient.denominator; }
  bool restrictNWCtoGC() const { return _restrictNWCtoGC.actualValue; }
  Sos sos() const { return _sos.actualValue; }
  unsigned sosTheoryLimit() const { return _sosTheoryLimit.actualValue; }

  bool shuffleInput() const { return _shuffleInput.actualValue; }
  bool randomPolarities() const { return _randomPolarities.actualValue; }
  bool randomizedSimplifications() const { return _randomizedSimplifications.actualValue; }
  bool randomizedPreprocessing() const { return _randomizedPreprocessing.actualValue; }
  bool randomAWR() const { return _randomAWR.actualValue; }
  bool randomTraversals() const { return _randomTraversals.actualValue; }
  bool randomizeSeedForPortfolioWorkers() const { return _randomizeSeedForPortfolioWorkers.actualValue; }
  void setRandomizeSeedForPortfolioWorkers(bool val) { _randomizeSeedForPortfolioWorkers.actualValue = val; }
  bool shuffleOnScheduleRepeats() const { return _shuffleOnScheduleRepeats.actualValue; }
  void enableShuffling() { _shuffleInput.actualValue = true; _randomTraversals.actualValue = true; }

  bool ignoreConjectureInPreprocessing() const {return _ignoreConjectureInPreprocessing.actualValue;}

  FunctionDefinitionElimination functionDefinitionElimination() const { return _functionDefinitionElimination.actualValue; }
  unsigned functionDefinitionIntroduction() const { return _functionDefinitionIntroduction.actualValue; }
  TweeGoalTransformation tweeGoalTransformation() const { return _tweeGoalTransformation.actualValue; }
  bool tweeSkipArrows() const { return _tweeSkipArrows.actualValue; }
  bool codeTreeSubsumption() const { return _codeTreeSubsumption.actualValue; }
  QuestionAnsweringMode questionAnswering() const { return _questionAnswering.actualValue; }
  bool questionAnsweringGroundOnly() const { return _questionAnsweringGroundOnly.actualValue; }
  std::string questionAnsweringAvoidThese() const { return _questionAnsweringAvoidThese.actualValue; }
  Output outputMode() const { return _outputMode.actualValue; }
  void setOutputMode(Output newVal) { _outputMode.actualValue = newVal; }
  bool ignoreMissingInputsInUnsatCore() {  return _ignoreMissingInputsInUnsatCore.actualValue; }
  std::string thanks() const { return _thanks.actualValue; }
  void setQuestionAnswering(QuestionAnsweringMode newVal) { _questionAnswering.actualValue = newVal; }
  bool globalSubsumption() const { return _globalSubsumption.actualValue; }

  /** true if calling set() on non-existing options does not result in a user error */
  IgnoreMissing ignoreMissing() const { return _ignoreMissing.actualValue; }
  void setIgnoreMissing(IgnoreMissing newVal) { _ignoreMissing.actualValue = newVal; }
  bool increasedNumeralWeight() const { return _increasedNumeralWeight.actualValue; }
  TheoryAxiomLevel theoryAxioms() const { return _theoryAxioms.actualValue; }
  Condensation condensation() const { return _condensation.actualValue; }
  bool generalSplitting() const { return _generalSplitting.actualValue; }
#if VTIME_PROFILING
  bool timeStatistics() const { return _timeStatistics.actualValue; }
  std::string const& timeStatisticsFocus() const { return _timeStatisticsFocus.actualValue; }
#endif // VTIME_PROFILING
  bool splitting() const { return _splitting.actualValue; }
  void setSplitting(bool value){ _splitting.actualValue=value; }
  bool nonliteralsInClauseWeight() const { return _nonliteralsInClauseWeight.actualValue; }
  unsigned sineDepth() const { return _sineDepth.actualValue; }
  unsigned sineGeneralityThreshold() const { return _sineGeneralityThreshold.actualValue; }
  unsigned sineToAgeGeneralityThreshold() const { return _sineToAgeGeneralityThreshold.actualValue; }
  SineSelection sineSelection() const { return _sineSelection.actualValue; }
  void setSineSelection(SineSelection val) { _sineSelection.actualValue=val; }
  float sineTolerance() const { return _sineTolerance.actualValue; }
  float sineToAgeTolerance() const { return _sineToAgeTolerance.actualValue; }

  bool instantiation() const { return _instantiation.actualValue; }
  bool theoryFlattening() const { return _theoryFlattening.actualValue; }
  bool ignoreUnrecognizedLogic() const { return _ignoreUnrecognizedLogic.actualValue; }

  Induction induction() const { return _induction.actualValue; }
  StructuralInductionKind structInduction() const { return _structInduction.actualValue; }
  IntInductionKind intInduction() const { return _intInduction.actualValue; }
  InductionChoice inductionChoice() const { return _inductionChoice.actualValue; }
  unsigned maxInductionDepth() const { return _maxInductionDepth.actualValue; }
  bool inductionNegOnly() const { return _inductionNegOnly.actualValue; }
  bool inductionUnitOnly() const { return _inductionUnitOnly.actualValue; }
  bool inductionGen() const { return _inductionGen.actualValue; }
  bool inductionStrengthenHypothesis() const { return _inductionStrengthenHypothesis.actualValue; }
  unsigned maxInductionGenSubsetSize() const { return _maxInductionGenSubsetSize.actualValue; }
  bool inductionOnComplexTerms() const {return _inductionOnComplexTerms.actualValue;}
  bool inductionGroundOnly() const {return _inductionGroundOnly.actualValue;}
  bool functionDefinitionRewriting() const { return _functionDefinitionRewriting.actualValue; }
  bool integerInductionDefaultBound() const { return _integerInductionDefaultBound.actualValue; }
  IntegerInductionInterval integerInductionInterval() const { return _integerInductionInterval.actualValue; }
  IntegerInductionLiteralStrictness integerInductionStrictnessEq() const {return _integerInductionStrictnessEq.actualValue; }
  IntegerInductionLiteralStrictness integerInductionStrictnessComp() const {return _integerInductionStrictnessComp.actualValue; }
  IntegerInductionTermStrictness integerInductionStrictnessTerm() const {return _integerInductionStrictnessTerm.actualValue; }
  bool nonUnitInduction() const { return _nonUnitInduction.actualValue; }
  bool inductionOnActiveOccurrences() const { return _inductionOnActiveOccurrences.actualValue; }

  void setTimeLimitInSeconds(int newVal) { _timeLimitInDeciseconds.actualValue = 10*newVal; }
  void setTimeLimitInDeciseconds(int newVal) { _timeLimitInDeciseconds.actualValue = newVal; }

  bool splitAtActivation() const{ return _splitAtActivation.actualValue; }
  bool cleaveNonsplittables() const{ return _cleaveNonsplittables.actualValue; }
  SplittingNonsplittableComponents splittingNonsplittableComponents() const { return _splittingNonsplittableComponents.actualValue; }
  SplittingAddComplementary splittingAddComplementary() const { return _splittingAddComplementary.actualValue; }
  bool splittingMinimizeModel() const { return _splittingMinimizeModel.actualValue; }
  SplittingLiteralPolarityAdvice splittingLiteralPolarityAdvice() const { return _splittingLiteralPolarityAdvice.actualValue; }
  SplittingDeleteDeactivated splittingDeleteDeactivated() const { return _splittingDeleteDeactivated.actualValue;}
  float splittingAvatimer() const { return _splittingAvatimer.actualValue; }
  bool splittingCongruenceClosure() const { return _splittingCongruenceClosure.actualValue; }

  void setProof(Proof p) { _proof.actualValue = p; }
  bool newCNF() const { return _newCNF.actualValue; }
  bool getIteInlineLet() const { return _inlineLet.actualValue; }

  bool useManualClauseSelection() const { return _manualClauseSelection.actualValue; }
  bool inequalityNormalization() const { return _inequalityNormalization.actualValue; }
  EvaluationMode evaluationMode() const { return _evaluationMode.actualValue; }
  ArithmeticSimplificationMode gaussianVariableElimination() const { return _gaussianVariableElimination.actualValue; }
  bool alasca() const { return _alasca.actualValue; }
  bool viras() const { return _viras.actualValue; }
  bool alascaDemodulation() const { return _alascaDemodulation.actualValue; }
  bool alascaStrongNormalization() const { return _alascaStrongNormalization.actualValue; }
  bool alascaIntegerConversion() const { return _alascaIntegerConversion.actualValue; }
  bool alascaAbstraction() const { return _alascaAbstraction.actualValue; }
  bool pushUnaryMinus() const { return _pushUnaryMinus.actualValue; }
  ArithmeticSimplificationMode cancellation() const { return _cancellation.actualValue; }
  ArithmeticSimplificationMode arithmeticSubtermGeneralizations() const { return _arithmeticSubtermGeneralizations.actualValue; }

  //Higher-order Options

  HPrinting holPrinting() const { return _holPrinting.actualValue; }
  void setHolPrinting(HPrinting setting) { _holPrinting.actualValue = setting; }

  bool choiceAxiom() const { return _choiceAxiom.actualValue; }
  bool injectivityReasoning() const { return _injectivity.actualValue; }
  bool choiceReasoning() const { return _choiceReasoning.actualValue; }
  FunctionExtensionality functionExtensionality() const { return _functionExtensionality.actualValue; }
  CNFOnTheFly cnfOnTheFly() const { return _clausificationOnTheFly.actualValue; }
  PISet piSet() const { return _piSet.actualValue; }
  bool equalityToEquivalence () const { return _equalityToEquivalence.actualValue; }
  bool complexBooleanReasoning () const { return _complexBooleanReasoning.actualValue; }
  bool booleanEqTrick() const { return _booleanEqTrick.actualValue; }
  bool heuristicInstantiation() const { return _heuristicInstantiation.actualValue; }
  unsigned higherOrderUnifDepth() const { return _higherOrderUnifDepth.actualValue; }
  bool casesSimp() const { return _casesSimp.actualValue; }
  bool cases() const { return _cases.actualValue; }
  bool newTautologyDel() const { return _newTautologyDel.actualValue; }
  bool positiveExtensionality() const { return _positiveExt.actualValue; }
  bool iffXorRewriter() const { return _iffXorRewriter.actualValue; }

private:

    /**
     * A LookupWrapper is used to wrap up two maps for long and short names and query them
     */
    struct LookupWrapper {
        LookupWrapper() = default;
        LookupWrapper(const LookupWrapper &) = delete;
        LookupWrapper &operator=(const LookupWrapper &) = delete;

        void insert(AbstractOptionValue &option_value){
            ASS(option_value.longName);
            bool new_long =  _longMap.insert(option_value.longName,&option_value);
            bool new_short = true;
            if(option_value.shortName){
                new_short = _shortMap.insert(option_value.shortName,&option_value);
            }
            if(!new_long || !new_short){ std::cout << "Bad " << option_value.longName << std::endl; }
            ASS(new_long && new_short);
        }
        AbstractOptionValue *findLong(const char *longName) const {
            AbstractOptionValue *value = nullptr;
            _longMap.find(longName, value);
            return value;
        }
        AbstractOptionValue* findShort(const char *shortName) const{
            AbstractOptionValue *value = nullptr;
            _shortMap.find(shortName, value);
            return value;
        }

        auto values() const {
            return _longMap.range();
        }

    private:
        DHMap<std::string,AbstractOptionValue*, FnvHash, LengthHash> _longMap;
        DHMap<std::string,AbstractOptionValue*, FnvHash, LengthHash> _shortMap;
    } _lookup;

    AbstractOptionValue *getOptionValueByName(const char *name) const;
    Stack<const char *> getSimilarOptionNames(const char *name, bool is_short) const;

    //==========================================================
    // Variables holding option values
    //==========================================================

 /**
  * NOTE on OptionValues
  *
  * An OptionValue stores the value for an Option as well as all the meta-data
  * See the definitions of different OptionValue objects above for details
  * but the main OptionValuse are
  *  - BoolOptionValue
  *  - IntOptionValue, UnsignedOptionValue, FloatOptionValue, LongOptionValue
  *  - StringOptionValue
  *  - ChoiceOptionValue
  *  - RatioOptionValue
  *
  * ChoiceOptionValue requires you to define an enum for the choice values
  *
  * For examples of how the different OptionValues are used see Options.cpp
  *
  * If an OptionValue needs custom assignment you will need to create a custom
  *  OptionValue. See DecodeOptionValue and SelectionOptionValue for examples.
  *
  */

  DecodeOptionValue _decode;

#define VAMPIRE_DECL_BOOL(member, ...) BoolOptionValue member;
#define VAMPIRE_DECL_INT(member, ...) IntOptionValue member;
#define VAMPIRE_DECL_UNSIGNED(member, ...) UnsignedOptionValue member;
#define VAMPIRE_DECL_FLOAT(member, ...) FloatOptionValue member;
#define VAMPIRE_DECL_LONG(member, ...) LongOptionValue member;
#define VAMPIRE_DECL_STRING(member, ...) StringOptionValue member;
#define VAMPIRE_DECL_CHOICE(enumType, member, ...) ChoiceOptionValue<enumType> member;
  FOR_EACH_VAMPIRE_OPTION(VAMPIRE_DECL_BOOL, VAMPIRE_DECL_INT, VAMPIRE_DECL_UNSIGNED, VAMPIRE_DECL_FLOAT, VAMPIRE_DECL_LONG, VAMPIRE_DECL_STRING, VAMPIRE_DECL_CHOICE)
#undef VAMPIRE_DECL_BOOL
#undef VAMPIRE_DECL_INT
#undef VAMPIRE_DECL_UNSIGNED
#undef VAMPIRE_DECL_FLOAT
#undef VAMPIRE_DECL_LONG
#undef VAMPIRE_DECL_STRING
#undef VAMPIRE_DECL_CHOICE


  RatioOptionValue _ageWeightRatio;

  BoolOptionValue _fmbNonGroundDefs;
  ChoiceOptionValue<FMBWidgetOrders> _fmbSymmetryWidgetOrders;
  TimeLimitOptionValue _fmbDetectSortBoundsTimeLimit;
  ChoiceOptionValue<FMBEnumerationStrategy> _fmbEnumerationStrategy;

  /** if true, then calling set() on non-existing options will not result in a user error */
  /** if this option is true, Vampire will add the numeral weight of a clause
   * to its weight. The weight is defined as the sum of binary sizes of all
   * integers occurring in this clause. This option has not been tested and
   * may be extensive, see Clause::getNumeralWeight()
   */

  UnsignedOptionValue _memoryLimit; // should be size_t, making an assumption

  ChoiceOptionValue<SatSolver> _satSolver;
  ChoiceOptionValue<SaturationAlgorithm> _saturationAlgorithm;
  ChoiceOptionValue<InterpolantMode> _showInterpolant;
  BoolOptionValue _showNewPropositional;
#if VAMPIRE_CLAUSE_TRACING
  // TODO make unsigned option value
#endif // VAMPIRE_CLAUSE_TRACING
#if VZ3
  BoolOptionValue _smtForGround;
#endif
  TimeLimitOptionValue _simulatedTimeLimit;

  StringOptionValue _predicateWeights;


  /** Time limit in deciseconds */
  TimeLimitOptionValue _timeLimitInDeciseconds;


  OptionChoiceValues _tagNames;

  NonGoalWeightOptionValue _nonGoalWeightCoefficient;

  SelectionOptionValue _selection;

  InputFileOptionValue _inputFile;


  // arithmeitc reasoning options


  //Higher-order options

}; // class Options

// Allow printing of enums
// TODO move this elsewhere
template<typename T,
         typename = typename std::enable_if<std::is_enum<T>::value>::type>
std::ostream& operator<< (std::ostream& str,const T& val)
{
  return str << static_cast<typename std::underlying_type<T>::type>(val);
}

}

#endif
