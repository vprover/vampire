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
 * Firstly, the easiest thing to do is copy what's been done for an existing option
 *
 * In Options.hpp
 * - Add an OptionValue object (see NOTE on OptionValues below) 
 * - Add enum for choices if ChoiceOptionValue
 * - Add getter for OptionValue
 * - Only if necessary (usually not), add setter for OptionValue
 *
 * In Options.cpp
 * - Initialise the OptionValue member, to do this you need to
 * -- Call the constructor with at least a long name, short name and default value
 * -- Provide a description
 * -- Insert the option into lookup (this is essential)
 * -- Tag the option, otherwise it will not appear nicely in showOptions
 * -- Add value constraints, they can be soft or hard (see NOTE on OptionValueConstraints below)
 * -- Add problem constraints (see NOTE on OptionProblemConstraints)
 *
 */

#ifndef __Options__
#define __Options__

#include <type_traits>
#include <cstring>
#include <memory>
#include <sys/stat.h>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/VString.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Int.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/STL.hpp"

#include "Property.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class Property;

/**
 * Let us define a similarity measure for strings, used to compare option names 
 * 
 * This is a Levenshtein (edit) distance and therefore gives the number
 * of edits needed to change s1 into s2
 *
 * TODO does not really belong here!
 *
 * @author Giles
 */
static size_t distance(const vstring &s1, const vstring &s2)
{
  const size_t m(s1.size());
  const size_t n(s2.size());

  if( m==0 ) return n;
  if( n==0 ) return m;

  DArray<size_t> costs = DArray<size_t>(n+1);

  for( size_t k=0; k<=n; k++ ) costs[k] = k;

  size_t i = 0;
  for ( vstring::const_iterator it1 = s1.begin(); it1 != s1.end(); ++it1, ++i )
  {
    costs[0] = i+1;
    size_t corner = i;

    size_t j = 0;
    for ( vstring::const_iterator it2 = s2.begin(); it2 != s2.end(); ++it2, ++j )
    {
      size_t upper = costs[j+1];
      if( *it1 == *it2 ){costs[j+1] = corner;}
      else{
        size_t t(upper<corner?upper:corner);
        costs[j+1] = (costs[j]<t?costs[j]:t)+1;
      }
      corner = upper;
    }
  }

  return costs[n];
}

/**
 * Class that represents Vampire's options.
 * 11/11/2004 Shrigley Hall, completely reimplemented
 *
 * @since Sep 14 reimplemented by Giles
 */
class Options
{
public:

    Options ();
    // It is important that we can safely copy Options for use in CASC mode
    void init();
    void copyValuesFrom(const Options& that);
    Options(const Options& that);
    Options& operator=(const Options& that);

    // used to print help and options
    void output (ostream&) const;

    // Dealing with encoded options. Used by --decode option
    void readFromEncodedOptions (vstring testId);
    void readOptionsString (vstring testId,bool assign=true);
    vstring generateEncodedOptions() const;

    // deal with completeness
    bool complete(const Problem&) const;
    bool completeForNNE() const;

    // deal with constraints
    void setForcedOptionValues(); // not currently used effectively
    bool checkGlobalOptionConstraints(bool fail_early=false);
    bool checkProblemOptionConstraints(Property*, bool before_preprocessing, bool fail_early=false);

    // Randomize strategy (will only work if randomStrategy=on)
    // should only be called after all other options are set
    //
    // The usage is overloaded. If prop=0 then this function will randomize
    // options that do not require a Property (no ProblemConstraints) 
    // (note it is possible to supress the requirement, see Options.cpp)
    // Otherwise all other options will be randomized.
    //
    // This dual usage is required as the property object is created during
    // the preprocessing stage. This means that in vampire.cpp we call this twice
    void randomizeStrategy(Property* prop);
    
    /**
     * Return the problem name
     *
     * The problem name is computed from the input file name in
     * the @b setInputFile function. If the input file is not set,
     * the problem name is equal to "unknown". The problem name can
     * be set to a specific value using setProblemName().
     */
    const vstring& problemName () const { return _problemName.actualValue; }
    void setProblemName(vstring str) { _problemName.actualValue = str; }
    
    void setInputFile(const vstring& newVal){ _inputFile.set(newVal); }
    vstring includeFileName (const vstring& relativeName);

    CLASS_NAME(Options);
    USE_ALLOCATOR(Options);
    
    // standard ways of creating options
    void set(const vstring& name, const vstring& value); // implicitly the long version used here
    void set(const char* name, const char* value, bool longOpt);
    
public:
  //==========================================================
  // The Enums for Option Values
  //==========================================================
  //
  // If you create a ChoiceOptionValue you will also need to create an enum
   
 
    /**
     * Possible tags to group options by
     * Update _tagNames at the end of Options constructor if you add a tag
     * @author Giles
     */
    enum class OptionTag: unsigned int {
        UNUSED,
        OTHER,
        DEVELOPMENT,
        OUTPUT,
        INST_GEN,
        FMB,
        SAT,
        AVATAR,
        INFERENCES,
        LRS,
        SATURATION,
        PREPROCESSING,
        INPUT,
        HELP,
        HIGHER_ORDER,
        LAST_TAG // Used for counting the number of tags
    };
    // update _tagNames at the end of Options constructor if you add a tag
    
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
    OFF,
    INTERP_ONLY,
    ONE_INTERP,
    CONSTANT,
    ALL,
    GROUND
  };

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
    ALL
  };
  enum class IntInductionKind : unsigned int {
    ONE,
    TWO,
    ALL
  };
  enum class IntegerInductionInterval : unsigned int {
    INFINITE,
    FINITE,
    BOTH
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
    OCCURENCE,
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

  enum class RandomStrategy : unsigned int {
    ON,
    OFF,
    SAT,
    NOCHECK
  };

  enum class BadOption : unsigned int {
    HARD,
    FORCED,
    OFF,
    SOFT
  };

  enum class LTBLearning : unsigned int {
    ON,
    OFF,
    BIASED
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
   *
   *
   */
  enum class Instantiation : unsigned int {
    OFF = 0,
    ON = 1
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
    CASC_HOL,
    CASC_SAT,
    CASC_LTB,
    CLAUSIFY,
    CONSEQUENCE_ELIMINATION,
    GROUNDING,
    MODEL_CHECK,
    /** this mode only outputs the input problem, without any preprocessing */
    OUTPUT,
    PORTFOLIO,
    PREPROCESS,
    PREPROCESS2,
    PROFILE,
    RANDOM_STRATEGY,
    SMTCOMP,
    SPIDER,
    TCLAUSIFY,
    TPREPROCESS,
    VAMPIRE
};

  enum class Schedule : unsigned int {
    CASC,
    CASC_2019,
    CASC_SAT,
    CASC_SAT_2019,
    CASC_HOL_2020,
    INDUCTION,
    INTEGER_INDUCTION,
    LTB_DEFAULT_2017,
    LTB_HH4_2017,
    LTB_HLL_2017,
    LTB_ISA_2017,
    LTB_MZR_2017,
    SMTCOMP,
    SMTCOMP_2018,
    STRUCT_INDUCTION
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
     MINISAT = 0
#if VZ3
     ,Z3 = 1
#endif
  };

  /** Possible values for saturation_algorithm */
  enum class SaturationAlgorithm : unsigned int {
     DISCOUNT = 0,
     FINITE_MODEL_BUILDING = 1,
     INST_GEN = 2,
     LRS = 3,
     OTTER = 4,
     Z3 = 5,
   };

  /** Possible values for activity of some inference rules */
  enum class RuleActivity : unsigned int {
    INPUT_ONLY = 0,
    OFF = 1,
    ON = 2
  };

  enum class QuestionAnsweringMode : unsigned int {
    ANSWER_LITERAL = 0,
    FROM_PROOF = 1,
    OFF = 2
  };

  enum class InterpolantMode : unsigned int {
    NEW_HEUR = 0,
    NEW_OPT = 1,
    OFF = 2,
    OLD = 3,
    OLD_OPT = 4
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
    ON = 2
  };

  enum class TermOrdering : unsigned int {
    KBO = 0,
    LPO = 1
  };

  enum class SymbolPrecedence : unsigned int {
    ARITY = 0,
    OCCURRENCE = 1,
    REVERSE_ARITY = 2,
    SCRAMBLE = 3,
    FREQUENCY = 4,
    REVERSE_FREQUENCY = 5,
    WEIGHTED_FREQUENCY = 6,
    REVERSE_WEIGHTED_FREQUENCY = 7
  };
  enum class SymbolPrecedenceBoost : unsigned int {
    NONE = 0,
    GOAL = 1,
    UNIT = 2,
    GOAL_UNIT = 3
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
    PROPERTY = 4
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
    NONE
  };

  enum class SplittingMinimizeModel : unsigned int {
    OFF = 0,
    SCO = 1,
    ALL = 2
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
  
  enum class SplittingCongruenceClosure : unsigned int {
    MODEL = 0,
    OFF = 1,
    ON = 2
  };

  enum class SplittingNonsplittableComponents : unsigned int {
    ALL = 0,
    ALL_DEPENDENT = 1,
    KNOWN = 2,
    NONE = 3
  };

  enum class CCUnsatCores : unsigned int {
    FIRST = 0,
    SMALL_ONES = 1,
    ALL = 2
  };

  enum class GlobalSubsumptionSatSolverPower : unsigned int {
    PROPAGATION_ONLY,
    FULL
  };

  enum class GlobalSubsumptionExplicitMinim : unsigned int {
    OFF,
    ON,
    RANDOMIZED
  };

  enum class GlobalSubsumptionAvatarAssumptions : unsigned int {
    OFF,
    FROM_CURRENT,
    FULL_MODEL
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
    SIMPLE,
    POLYNOMIAL_FORCE,
    POLYNOMIAL_CAUTIOUS,
  };

  enum class ArithmeticSimplificationMode : unsigned int {
    FORCE,
    CAUTIOUS,
    OFF,
  };

  enum class AgeWeightRatioShape {
    CONSTANT,
    DECAY,
    CONVERGE
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
    LAZY_SIMP_NOT_GEN_BOOL_EQ_OFF = 4,
    LAZY_SIMP_NOT_GEN_BOOL_EQ_GEN = 5,
    OFF = 6
  };

  enum class PISet : unsigned int {
    ALL = 0,
    ALL_EXCEPT_NOT_EQ = 1,
    FALSE_TRUE_NOT = 2,
    FALSE_TRUE_NOT_EQ_NOT_EQ = 3
  };

  enum class Narrow : unsigned int {
    ALL = 0,
    SK = 1,
    SKI = 2,
    OFF = 3
  };


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
      void check_names_are_short() {
        for (auto x : _names) {
          ASS(x.size() < 70) // or else cannot be printed on a line
        }
      }
    public:
        OptionChoiceValues() : _names() { };
        OptionChoiceValues(Stack<vstring> names) : _names(std::move(names))  
        {
          check_names_are_short();
        }

        OptionChoiceValues(std::initializer_list<vstring> list) : _names(list)
        {
          check_names_are_short();
        }
        
        int find(vstring value) const {
            for(unsigned i=0;i<_names.length();i++){
                if(value.compare(_names[i])==0) return i;
            }
            return -1;
        }
        const int length() const { return _names.length(); }
        const vstring operator[](int i) const{ return _names[i];}

    private:
        Stack<vstring> _names;
    };
    
    // Declare constraints here so they can be referred to, but define them below
    template<typename T>
    struct OptionValueConstraint;
    template<typename T>
    using OptionValueConstraintUP = std::unique_ptr<OptionValueConstraint<T>>;
    struct AbstractWrappedConstraint;
    typedef std::unique_ptr<AbstractWrappedConstraint> AbstractWrappedConstraintUP;
    struct OptionProblemConstraint;
    typedef std::unique_ptr<OptionProblemConstraint> OptionProblemConstraintUP;
    
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

        CLASS_NAME(AbstractOptionValue);
        USE_ALLOCATOR(AbstractOptionValue);

        AbstractOptionValue(){}
        AbstractOptionValue(vstring l,vstring s) :
        longName(l), shortName(s), experimental(false), is_set(false),_should_copy(true), _tag(OptionTag::LAST_TAG), supress_problemconstraints(false) {}

        // Never copy an OptionValue... the Constraint system would break
        AbstractOptionValue(const AbstractOptionValue&) = delete;
        AbstractOptionValue& operator=(const AbstractOptionValue&) = delete;

        // however move-assigment is needed for all the assigns in Options::init()
        AbstractOptionValue(AbstractOptionValue&&) = default;
        AbstractOptionValue& operator= (AbstractOptionValue && ) = default;

        virtual ~AbstractOptionValue() = default;

        // This is the main method, it sets the value of the option using an input string
        // Returns false if we cannot set (will cause a UserError in Options::set)
        virtual bool setValue(const vstring& value) = 0;

        bool set(const vstring& value){
          bool okay = setValue(value); 
          if(okay) is_set=true;
          return okay;
        }
        
        // Set to a random value
        virtual bool randomize(Property* P) = 0;

        // Experimental options are not included in help
        void setExperimental(){experimental=true;}
        
        // Meta-data
        vstring longName;
        vstring shortName;
        vstring description;
        bool experimental;
        bool is_set;
        
        // Checking constraits
        virtual bool checkConstraints() = 0;
        virtual bool checkProblemConstraints(Property* prop) = 0;
        
        // Tagging: options can be filtered by mode and are organised by Tag in showOptions
        void tag(OptionTag tag){ ASS(_tag==OptionTag::LAST_TAG);_tag=tag; }
        void tag(Options::Mode mode){ _modes.push(mode); }
        
        OptionTag getTag(){ return _tag;}
        bool inMode(Options::Mode mode){
            if(_modes.isEmpty()) return true;
            else return _modes.find(mode);
        }
        
        // This allows us to get the actual value in string form
        virtual vstring getStringOfActual() const = 0;
        // Check if default value
        virtual bool isDefault() const = 0;
        
        // For use in showOptions and explainOption
        //virtual void output(vstringstream& out) const {
        virtual void output(ostream& out,bool linewrap) const {
            CALL("Options::AbstractOptionValue::output");
            out << "--" << longName;
            if(!shortName.empty()){ out << " (-"<<shortName<<")"; }
            out << endl;
            
            if (experimental) {
              out << "\t[experimental]" << endl;
            }
            

            if(!description.empty()){
                // Break a the description into lines where there have been at least 70 characters
                // on the line at the next space
                out << "\t";
                int count=0;
                for(const char* p = description.c_str();*p;p++){
                    out << *p;
                    count++;
                    if(linewrap && count>70 && *p==' '){
                        out << endl << '\t';
                        count=0;
                    }
                    if(*p=='\n'){ count=0; out << '\t'; }
                }
                out << endl;
            }
            else{ out << "\tno description provided!" << endl; }
        }
        
        // Used to determine wheter the value of an option should be copied when
        // the Options object is copied.
        bool _should_copy;
        bool shouldCopy() const { return _should_copy; }
       
        typedef std::unique_ptr<DArray<vstring>> vstringDArrayUP;

        typedef pair<OptionProblemConstraintUP,vstringDArrayUP> RandEntry;

        void setRandomChoices(std::initializer_list<vstring> list){
          CALL("AbstractOptionValue::setRandomChoices(std::initializer_list<vstring> list)");
          rand_choices.push(RandEntry(OptionProblemConstraintUP(),toArray(list)));
        }
        void setRandomChoices(std::initializer_list<vstring> list,
                              std::initializer_list<vstring> list_sat){
          CALL("AbstractOptionValue::setRandomChoices(std::initializer_list<vstring> list, std::initializer_list<vstring> list_sat)");
          rand_choices.push(RandEntry(isRandOn(),toArray(list)));
          rand_choices.push(RandEntry(isRandSat(),toArray(list_sat)));
        }
        void setRandomChoices(OptionProblemConstraintUP c,
                              std::initializer_list<vstring> list){
          CALL("AbstractOptionValue::setRandomChoices(OptionProblemConstraintUP c, std::initializer_list<vstring> list)");
          rand_choices.push(RandEntry(std::move(c),toArray(list)));
        }
        void setNoPropertyRandomChoices(std::initializer_list<vstring> list){
          CALL("AbstractOptionValue::setNoPropertyRandomChoices(std::initializer_list<vstring> list)");
          rand_choices.push(RandEntry(OptionProblemConstraintUP(),toArray(list)));
          supress_problemconstraints=true;
        }

 
    private:
        // Tag state
        OptionTag _tag;
        Lib::Stack<Options::Mode> _modes;

        vstringDArrayUP toArray(std::initializer_list<vstring>& list){
          DArray<vstring>* array = new DArray<vstring>(list.size());
          unsigned index=0;
          for(typename std::initializer_list<vstring>::iterator it = list.begin();
           it!=list.end();++it){ (*array)[index++] =*it; }
          return vstringDArrayUP(array);
        }
    protected:
        // Note has LIFO semantics so use BottomFirstIterator
        Stack<RandEntry> rand_choices;
        bool supress_problemconstraints;
    };
    
    struct AbstractOptionValueCompatator{
      Comparison compare(AbstractOptionValue* o1, AbstractOptionValue* o2)
      {
        int value = strcmp(o1->longName.c_str(),o2->longName.c_str());
        return value < 0 ? LESS : (value==0 ? EQUAL : GREATER);
      }
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
        
        CLASS_NAME(OptionValue);
        USE_ALLOCATOR(OptionValue);
        
        // We need to include an empty constructor as all the OptionValue objects need to be initialized
        // with something when the Options object is created. They should then all be reconstructed
        // This is annoying but preferable to the alternative in my opinion
        OptionValue(){}
        OptionValue(vstring l, vstring s,T def) : AbstractOptionValue(l,s),
        defaultValue(def), actualValue(def){}
        
        // We store the defaultValue separately so that we can check if the actualValue is non-default
        T defaultValue;
        T actualValue;
        
        virtual bool isDefault() const { return defaultValue==actualValue;}

        // Getting the string versions of values, useful for output
        virtual vstring getStringOfValue(T value) const{ ASSERTION_VIOLATION;}
        virtual vstring getStringOfActual() const { return getStringOfValue(actualValue); }
        
        // Adding and checking constraints
        // By default constraints are soft and reaction to them is controlled by the bad_option option
        // But a constraint can be added as Hard, meaning that it always causes a UserError
        void addConstraint(OptionValueConstraintUP<T> c){ _constraints.push(std::move(c)); }
        void addHardConstraint(OptionValueConstraintUP<T> c){ c->setHard();addConstraint(std::move(c)); }

        // A reliesOn constraint gives a constraint that must be true if a non-default value is used
        // For example, split_at_activation relies on splitting being on
        // These are defined for OptionValueConstraints and WrappedConstraints - see below for explanation
        void reliesOn(AbstractWrappedConstraintUP c){
            _constraints.push(If(getNotDefault()).then(unwrap<T>(c)));
        }
        void reliesOn(OptionValueConstraintUP<T> c){
            _constraints.push(If(getNotDefault()).then(std::move(c)));
        }
        virtual OptionValueConstraintUP<T> getNotDefault(){ return isNotDefault<T>(); }
        void reliesOnHard(AbstractWrappedConstraintUP c){
            OptionValueConstraintUP<T> tc = If(getNotDefault()).then(unwrap<T>(c));
            tc->setHard();
            _constraints.push(std::move(tc));
        }
        void reliesOnHard(OptionValueConstraintUP<T> c){
            OptionValueConstraintUP<T> tc = If(getNotDefault()).then(c);
            tc->setHard();
            _constraints.push(std::move(tc));
        }
        // This checks the constraints and may cause a UserError
        bool checkConstraints();
        
        // Produces a separate constraint object based on this option
        /// Useful for IfThen constraints and reliesOn i.e. _splitting.is(equal(true))
        AbstractWrappedConstraintUP is(OptionValueConstraintUP<T> c);
        
        // Problem constraints place a restriction on problem properties and option values
        void addProblemConstraint(OptionProblemConstraintUP c){ _prob_constraints.push(std::move(c)); }
        bool hasProblemConstraints(){ 
          return !supress_problemconstraints && !_prob_constraints.isEmpty(); 
        }
        virtual bool checkProblemConstraints(Property* prop);
        
        virtual void output(ostream& out, bool linewrap) const {
            CALL("Options::OptionValue::output");
            AbstractOptionValue::output(out,linewrap);
            out << "\tdefault: " << getStringOfValue(defaultValue) << endl;
        }
       
        // This is where actual randomisation happens
        bool randomize(Property* p);
 
    private:
        Lib::Stack<OptionValueConstraintUP<T>> _constraints;
        Lib::Stack<OptionProblemConstraintUP> _prob_constraints;
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
        
        CLASS_NAME(ChoiceOptionValue);
        USE_ALLOCATOR(ChoiceOptionValue);
        
        ChoiceOptionValue(){}
        ChoiceOptionValue(vstring l, vstring s,T def,OptionChoiceValues c) :
        OptionValue<T>(l,s,def), choices(c) {}
        ChoiceOptionValue(vstring l, vstring s,T d) : ChoiceOptionValue(l,s,d, T::optionChoiceValues()) {}
        
        bool setValue(const vstring& value){
            // makes reasonable assumption about ordering of every enum
            int index = choices.find(value.c_str());
            if(index<0) return false;
            this->actualValue = static_cast<T>(index);
            return true;
        }
        
        virtual void output(ostream& out,bool linewrap) const {
            AbstractOptionValue::output(out,linewrap);
            out << "\tdefault: " << choices[static_cast<unsigned>(this->defaultValue)];
            out << endl;
            string values_header = "values: ";
            out << "\t" << values_header;
            // Again we restrict line length to 70 characters
            int count=0;
            for(int i=0;i<choices.length();i++){
                if(i==0){
                    out << choices[i];
                }
                else{
                    out << ",";
                    vstring next = choices[i];
                    if(linewrap && next.size()+count>60){ // next.size() will be <70, how big is a tab?
                        out << endl << "\t";
                        for(unsigned j=0;j<values_header.size();j++){out << " ";}
                        count = 0;
                    }
                    out << next;
                    count += next.size();
                }
            }
            out << endl;
        }
        
        vstring getStringOfValue(T value) const {
            unsigned i = static_cast<unsigned>(value);
            return choices[i];
        }
        
    private:
        OptionChoiceValues choices;
    };


    /**
     * For Booleans - we use on/off rather than true/false
     * @author Giles
     */
    struct BoolOptionValue : public OptionValue<bool> {
        BoolOptionValue(){}
        BoolOptionValue(vstring l,vstring s, bool d) : OptionValue(l,s,d){}
        bool setValue(const vstring& value){
            if (! value.compare("on") || ! value.compare("true")) {
                actualValue=true;
                
            }
            else if (! value.compare("off") || ! value.compare("false")) {
                actualValue=false;
            }
            else return false;
            
            return true;
        }
        
        vstring getStringOfValue(bool value) const { return (value ? "on" : "off"); }
    };

    struct IntOptionValue : public OptionValue<int> {
        IntOptionValue(){}
        IntOptionValue(vstring l,vstring s, int d) : OptionValue(l,s,d){}
        bool setValue(const vstring& value){
            return Int::stringToInt(value.c_str(),actualValue);
        }
        vstring getStringOfValue(int value) const{ return Lib::Int::toString(value); }
    };
    
    struct UnsignedOptionValue : public OptionValue<unsigned> {
        UnsignedOptionValue(){}
        UnsignedOptionValue(vstring l,vstring s, unsigned d) : OptionValue(l,s,d){}

        bool setValue(const vstring& value){
            return Int::stringToUnsignedInt(value.c_str(),actualValue);
        }
        vstring getStringOfValue(unsigned value) const{ return Lib::Int::toString(value); }
    };
    
    struct StringOptionValue : public OptionValue<vstring> {
        StringOptionValue(){}
        StringOptionValue(vstring l,vstring s, vstring d) : OptionValue(l,s,d){}
        bool setValue(const vstring& value){
            actualValue = (value=="<empty>") ? "" : value;
            return true;
        }
        vstring getStringOfValue(vstring value) const{
            if(value.empty()) return "<empty>";
            return value;
        }
    };
    
    struct LongOptionValue : public OptionValue<long> {
        LongOptionValue(){}
        LongOptionValue(vstring l,vstring s, long d) : OptionValue(l,s,d){}
        bool setValue(const vstring& value){
            return Int::stringToLong(value.c_str(),actualValue);
        }
        vstring getStringOfValue(long value) const{ return Lib::Int::toString(value); }
    };
    
struct FloatOptionValue : public OptionValue<float>{
FloatOptionValue(){}
FloatOptionValue(vstring l,vstring s, float d) : OptionValue(l,s,d){}
bool setValue(const vstring& value){
    return Int::stringToFloat(value.c_str(),actualValue);
}
vstring getStringOfValue(float value) const{ return Lib::Int::toString(value); }
};

/**
* Ratios have two actual values and two default values
* Therefore, we often need to tread them specially
* @author Giles
*/
struct RatioOptionValue : public OptionValue<int> {

CLASS_NAME(RatioOptionValue);
USE_ALLOCATOR(RatioOptionValue);

RatioOptionValue(){}
RatioOptionValue(vstring l, vstring s, int def, int other, char sp=':') :
OptionValue(l,s,def), sep(sp), defaultOtherValue(other), otherValue(other) {};

virtual OptionValueConstraintUP<int> getNotDefault() override { return isNotDefaultRatio(); }

void addConstraintIfNotDefault(AbstractWrappedConstraintUP c){
    addConstraint(If(isNotDefaultRatio()).then(unwrap<int>(c)));
}

bool readRatio(const char* val,char seperator);
bool setValue(const vstring& value) override {
    return readRatio(value.c_str(),sep);
}

char sep;
int defaultOtherValue;
int otherValue;

virtual void output(ostream& out,bool linewrap) const override {
    AbstractOptionValue::output(out,linewrap);
    out << "\tdefault left: " << defaultValue << endl;
    out << "\tdefault right: " << defaultOtherValue << endl;
}

virtual vstring getStringOfValue(int value) const override { ASSERTION_VIOLATION;}
virtual vstring getStringOfActual() const override {
    return Lib::Int::toString(actualValue)+sep+Lib::Int::toString(otherValue);
}

};

// We now have a number of option-specific values
// These are necessary when the option needs to be read in a special way

/**
* Oddly gets set with a float value and then creates a ratio of value*100/100
* @author Giles
*/
struct NonGoalWeightOptionValue : public OptionValue<float>{

CLASS_NAME(NonGoalWeightOptionValue);
USE_ALLOCATOR(NonGoalWeightOptionValue);

NonGoalWeightOptionValue(){}
NonGoalWeightOptionValue(vstring l, vstring s, float def) :
OptionValue(l,s,def), numerator(1), denominator(1) {};

bool setValue(const vstring& value);

// output does not output numerator and denominator as they
// are produced from defaultValue
int numerator;
int denominator;

virtual vstring getStringOfValue(float value) const{ return Lib::Int::toString(value); }
};

/**
* Selection is defined by a set of integers (TODO: make enum)
* For now we need to check the integer is a valid one
* @author Giles
*/
struct SelectionOptionValue : public OptionValue<int>{
SelectionOptionValue(){}
SelectionOptionValue(vstring l,vstring s, int def):
OptionValue(l,s,def){};

bool setValue(const vstring& value);

virtual void output(ostream& out,bool linewrap) const {
    AbstractOptionValue::output(out,linewrap);
    out << "\tdefault: " << defaultValue << endl;;
}

virtual vstring getStringOfValue(int value) const{ return Lib::Int::toString(value); }

AbstractWrappedConstraintUP isLookAheadSelection(){
  return AbstractWrappedConstraintUP(new WrappedConstraint<int>(*this,OptionValueConstraintUP<int>(new isLookAheadSelectionConstraint())));
}
};

/**
* This also updates problemName
* @author Giles
*/
struct InputFileOptionValue : public OptionValue<vstring>{
InputFileOptionValue(){}
InputFileOptionValue(vstring l,vstring s, vstring def,Options* p):
OptionValue(l,s,def), parent(p){};

bool setValue(const vstring& value);

virtual void output(ostream& out,bool linewrap) const {
    AbstractOptionValue::output(out,linewrap);
    out << "\tdefault: " << defaultValue << endl;;
}
virtual vstring getStringOfValue(vstring value) const{ return value; }
private:
Options* parent;

};
/**
* We need to decode the encoded option string
* @author Giles
*/
struct DecodeOptionValue : public OptionValue<vstring>{
DecodeOptionValue(){ AbstractOptionValue::_should_copy=false;}
DecodeOptionValue(vstring l,vstring s,Options* p):
OptionValue(l,s,""), parent(p){ AbstractOptionValue::_should_copy=false;}

bool setValue(const vstring& value){
    parent->readFromEncodedOptions(value);
    return true;
}
virtual vstring getStringOfValue(vstring value) const{ return value; }

private:
Options* parent;

};
/**
* Need to read the time limit. By default it assumes seconds (and stores deciseconds) but you can give
* a multiplier i.e. d,s,m,h,D for deciseconds,seconds,minutes,hours,Days
* @author Giles
*/
struct TimeLimitOptionValue : public OptionValue<int>{
TimeLimitOptionValue(){}
TimeLimitOptionValue(vstring l, vstring s, float def) :
OptionValue(l,s,def) {};

bool setValue(const vstring& value);

virtual void output(ostream& out,bool linewrap) const {
    CALL("Options::TimeLimitOptionValue::output");
    AbstractOptionValue::output(out,linewrap);
    out << "\tdefault: " << defaultValue << "d" << endl;
}
virtual vstring getStringOfValue(int value) const{ return Lib::Int::toString(value)+"d"; }
};

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
* Note that the equals(0) will apply to the OptionValue that the constraint belongs to
*
* WrappedConstraints are produced by OptionValue.is and are used to provide constraints
* on other OptionValues, as seen in the example above. Most functions work with both
* OptionValueConstraint and WrappedConstraint but in some cases one of these options
* may need to be added. In this case see examples from AndWrapper below.
*
* MS: While OptionValueConstraints are expressions which wait for a concrete value to be evaluated against:
* as in λ value. expression(value),
* WrappedConstraints have already been "closed" by providing a concrete value:
* as in (λ value. expression(value))[concrete_value]
* Finally, we can at anytime "unwrap" a WrappedConstraint by providing a "fake" lambda again on top, to turn it into a OptionValueConstraints again:
* as in λ value. expression_ignoring_value
*
* The tricky part (C++-technology-wise) here is that unwrapping needs to get a type for the value
* and this type is independent form the expression_ignoring_value for obvious reasons.
* So various overloads of things are needed until we get to the point, where the type is known and can be supplied.
* (e.g. there needs to be a separate hierarchy of Wrapped expressions along the one for OptionValueConstraint ones).
*/

template<typename T>
struct OptionValueConstraint{
CLASS_NAME(OptionValueConstraint);
USE_ALLOCATOR(OptionValueConstraint);
OptionValueConstraint() : _hard(false) {}

virtual ~OptionValueConstraint() {} // virtual methods present -> there should be virtual destructor

virtual bool check(const OptionValue<T>& value) = 0;
virtual vstring msg(const OptionValue<T>& value) = 0;

// By default cannot force constraint
virtual bool force(OptionValue<T>* value){ return false;}
// TODO - allow for hard constraints
bool isHard(){ return _hard; }
void setHard(){ _hard=true;}
bool _hard;
};

    // A Wrapped Constraint takes an OptionValue and a Constraint
    // It allows us to supply a constraint on another OptionValue in an If constraint for example
    struct AbstractWrappedConstraint {
      virtual bool check() = 0;
      virtual vstring msg() = 0;
      virtual ~AbstractWrappedConstraint() {};
    };

    template<typename T>
    struct WrappedConstraint : AbstractWrappedConstraint {
        CLASS_NAME(WrappedConstraint);
        USE_ALLOCATOR(WrappedConstraint);
        
        WrappedConstraint(const OptionValue<T>& v, OptionValueConstraintUP<T> c) : value(v), con(std::move(c)) {}
        
        bool check() override {
            return con->check(value);
        }
        vstring msg() override {
            return con->msg(value);
        }

        const OptionValue<T>& value;
        OptionValueConstraintUP<T> con;
    };
    
    struct WrappedConstraintOrWrapper : public AbstractWrappedConstraint {
        CLASS_NAME(WrappedConstraintOrWrapper);
        USE_ALLOCATOR(WrappedConstraintOrWrapper);
        WrappedConstraintOrWrapper(AbstractWrappedConstraintUP l, AbstractWrappedConstraintUP r) : left(std::move(l)),right(std::move(r)) {}
        bool check() override {
            return left->check() || right->check();
        }
        vstring msg() override { return left->msg() + " or " + right->msg(); }

        AbstractWrappedConstraintUP left;
        AbstractWrappedConstraintUP right;
    };

    struct WrappedConstraintAndWrapper : public AbstractWrappedConstraint {
        CLASS_NAME(WrappedConstraintAndWrapper);
        USE_ALLOCATOR(WrappedConstraintAndWrapper);
        WrappedConstraintAndWrapper(AbstractWrappedConstraintUP l, AbstractWrappedConstraintUP r) : left(std::move(l)),right(std::move(r)) {}
        bool check() override {
            return left->check() && right->check();
        }
        vstring msg() override { return left->msg() + " and " + right->msg(); }

        AbstractWrappedConstraintUP left;
        AbstractWrappedConstraintUP right;
    };

    template<typename T>
    struct OptionValueConstraintOrWrapper : public OptionValueConstraint<T>{
        CLASS_NAME(OptionValueConstraintOrWrapper);
        USE_ALLOCATOR(OptionValueConstraintOrWrapper);
        OptionValueConstraintOrWrapper(OptionValueConstraintUP<T> l, OptionValueConstraintUP<T> r) : left(std::move(l)),right(std::move(r)) {}
        bool check(const OptionValue<T>& value){
            return left->check(value) || right->check(value);
        }
        vstring msg(const OptionValue<T>& value){ return left->msg(value) + " or " + right->msg(value); }

        OptionValueConstraintUP<T> left;
        OptionValueConstraintUP<T> right;
    };

    template<typename T>
    struct OptionValueConstraintAndWrapper : public OptionValueConstraint<T>{
        CLASS_NAME(OptionValueConstraintAndWrapper);
        USE_ALLOCATOR(OptionValueConstraintAndWrapper);
        OptionValueConstraintAndWrapper(OptionValueConstraintUP<T> l, OptionValueConstraintUP<T> r) : left(std::move(l)),right(std::move(r)) {}
        bool check(const OptionValue<T>& value){
            return left->check(value) && right->check(value);
        }
        vstring msg(const OptionValue<T>& value){ return left->msg(value) + " and " + right->msg(value); }

        OptionValueConstraintUP<T> left;
        OptionValueConstraintUP<T> right;
    };

    template<typename T>
    struct UnWrappedConstraint : public OptionValueConstraint<T>{
        CLASS_NAME(UnWrappedConstraint);
        USE_ALLOCATOR(UnWrappedConstraint);
        
        UnWrappedConstraint(AbstractWrappedConstraintUP c) : con(std::move(c)) {}
        
        bool check(const OptionValue<T>&){ return con->check(); }
        vstring msg(const OptionValue<T>&){ return con->msg(); }
        
        AbstractWrappedConstraintUP con;
    };
    
    template <typename T>
    static OptionValueConstraintUP<T> maybe_unwrap(OptionValueConstraintUP<T> c) { return c; }

    template <typename T>
    static OptionValueConstraintUP<T> unwrap(AbstractWrappedConstraintUP& c) { return OptionValueConstraintUP<T>(new UnWrappedConstraint<T>(std::move(c))); }

    template <typename T>
    static OptionValueConstraintUP<T> maybe_unwrap(AbstractWrappedConstraintUP& c) { return unwrap<T>(c); }

    /*
     * To avoid too many cases a certain discipline is required from the user.
     * Namely, OptionValueConstraints need to precede WrappedConstraints in the arguments of Or and And
     **/

    // the base case (the unary Or)
    template <typename T>
    OptionValueConstraintUP<T> Or(OptionValueConstraintUP<T> a) { return a; }
    AbstractWrappedConstraintUP Or(AbstractWrappedConstraintUP a) { return a; }

    template<typename T, typename... Args>
    OptionValueConstraintUP<T> Or(OptionValueConstraintUP<T> a, Args... args)
    {
      OptionValueConstraintUP<T> r = maybe_unwrap<T>(Or(std::move(args)...));
      return OptionValueConstraintUP<T>(new OptionValueConstraintOrWrapper<T>(std::move(a),std::move(r)));
    }

    template<typename... Args>
    AbstractWrappedConstraintUP Or(AbstractWrappedConstraintUP a, Args... args)
    {
      AbstractWrappedConstraintUP r = Or(std::move(args)...);
      return AbstractWrappedConstraintUP(new WrappedConstraintOrWrapper(std::move(a),std::move(r)));
    }

    // the base case (the unary And)
    template <typename T>
    OptionValueConstraintUP<T> And(OptionValueConstraintUP<T> a) { return a; }
    AbstractWrappedConstraintUP And(AbstractWrappedConstraintUP a) { return a; }

    template<typename T, typename... Args>
    OptionValueConstraintUP<T> And(OptionValueConstraintUP<T> a, Args... args)
    {
      OptionValueConstraintUP<T> r = maybe_unwrap<T>(And(std::move(args)...));
      return OptionValueConstraintUP<T>(new OptionValueConstraintAndWrapper<T>(std::move(a),std::move(r)));
    }

    template<typename... Args>
    AbstractWrappedConstraintUP And(AbstractWrappedConstraintUP a, Args... args)
    {
      AbstractWrappedConstraintUP r = And(std::move(args)...);
      return AbstractWrappedConstraintUP(new WrappedConstraintAndWrapper(std::move(a),std::move(r)));
    }

    template<typename T>
    struct Equal : public OptionValueConstraint<T>{
        CLASS_NAME(Equal);
        USE_ALLOCATOR(Equal);
        Equal(T gv) : _goodvalue(gv) {}
        bool check(const OptionValue<T>& value){
            return value.actualValue == _goodvalue;
        }
        vstring msg(const OptionValue<T>& value){
            return value.longName+"("+value.getStringOfActual()+") is equal to " + value.getStringOfValue(_goodvalue);
        }
        T _goodvalue;
    };
    template<typename T>
    static OptionValueConstraintUP<T> equal(T bv){
        return OptionValueConstraintUP<T>(new Equal<T>(bv));
    }
    
    template<typename T>
    struct NotEqual : public OptionValueConstraint<T>{
        CLASS_NAME(NotEqual);
        USE_ALLOCATOR(NotEqual);
        NotEqual(T bv) : _badvalue(bv) {}
        bool check(const OptionValue<T>& value){
            return value.actualValue != _badvalue;
        }
        vstring msg(const OptionValue<T>& value){ return value.longName+"("+value.getStringOfActual()+") is not equal to " + value.getStringOfValue(_badvalue); }
        T _badvalue;
    };
    template<typename T>
    static OptionValueConstraintUP<T> notEqual(T bv){
        return OptionValueConstraintUP<T>(new NotEqual<T>(bv));
    }
    
    // Constraint that the value should be less than a given value
    // optionally we can allow it be equal to that value also
    template<typename T>
    struct LessThan : public OptionValueConstraint<T>{
        CLASS_NAME(LessThan);
        USE_ALLOCATOR(LessThan);
        LessThan(T gv,bool eq=false) : _goodvalue(gv), _orequal(eq) {}
        bool check(const OptionValue<T>& value){
            return (value.actualValue < _goodvalue || (_orequal && value.actualValue==_goodvalue));
        }
        vstring msg(const OptionValue<T>& value){
            if(_orequal) return value.longName+"("+value.getStringOfActual()+") is less than or equal to " + value.getStringOfValue(_goodvalue);
            return value.longName+"("+value.getStringOfActual()+") is less than "+ value.getStringOfValue(_goodvalue);
        }
        
        T _goodvalue;
        bool _orequal;
    };
    template<typename T>
    static OptionValueConstraintUP<T> lessThan(T bv){
        return OptionValueConstraintUP<T>(new LessThan<T>(bv,false));
    }
    template<typename T>
    static OptionValueConstraintUP<T> lessThanEq(T bv){
        return OptionValueConstraintUP<T>(new LessThan<T>(bv,true));
    }
    
    // Constraint that the value should be greater than a given value
    // optionally we can allow it be equal to that value also
    template<typename T>
    struct GreaterThan : public OptionValueConstraint<T>{
        CLASS_NAME(GreaterThan);
        USE_ALLOCATOR(GreaterThan);
        GreaterThan(T gv,bool eq=false) : _goodvalue(gv), _orequal(eq) {}
        bool check(const OptionValue<T>& value){
            return (value.actualValue > _goodvalue || (_orequal && value.actualValue==_goodvalue));
        }
        
        vstring msg(const OptionValue<T>& value){
            if(_orequal) return value.longName+"("+value.getStringOfActual()+") is greater than or equal to " + value.getStringOfValue(_goodvalue);
            return value.longName+"("+value.getStringOfActual()+") is greater than "+ value.getStringOfValue(_goodvalue);
        }
        
        T _goodvalue;
        bool _orequal;
    };
    template<typename T>
    static OptionValueConstraintUP<T> greaterThan(T bv){
        return OptionValueConstraintUP<T>(new GreaterThan<T>(bv,false));
    }
    template<typename T>
    static OptionValueConstraintUP<T> greaterThanEq(T bv){
        return OptionValueConstraintUP<T>(new GreaterThan<T>(bv,true));
    }
    
    // Constraint that the value should be smaller than a given value
    // optionally we can allow it be equal to that value also
    template<typename T>
    struct SmallerThan : public OptionValueConstraint<T>{
        CLASS_NAME(SmallerThan);
        USE_ALLOCATOR(SmallerThan);
        SmallerThan(T gv,bool eq=false) : _goodvalue(gv), _orequal(eq) {}
        bool check(const OptionValue<T>& value){
            return (value.actualValue < _goodvalue || (_orequal && value.actualValue==_goodvalue));
        }

        vstring msg(const OptionValue<T>& value){
            if(_orequal) return value.longName+"("+value.getStringOfActual()+") is smaller than or equal to " + value.getStringOfValue(_goodvalue);
            return value.longName+"("+value.getStringOfActual()+") is smaller than "+ value.getStringOfValue(_goodvalue);
        }

        T _goodvalue;
        bool _orequal;
    };
    template<typename T>
    static OptionValueConstraintUP<T> smallerThan(T bv){
        return OptionValueConstraintUP<T>(new SmallerThan<T>(bv,false));
    }
    template<typename T>
    static OptionValueConstraintUP<T> smallerThanEq(T bv){
        return OptionValueConstraintUP<T>(new SmallerThan<T>(bv,true));
    }

    /**
     * If constraints
     */
    
    template<typename T>
    struct IfConstraint;
    
    template<typename T>
    struct IfThenConstraint : public OptionValueConstraint<T>{
        CLASS_NAME(IfThenConstraint);
        USE_ALLOCATOR(IfThenConstraint);
        
        IfThenConstraint(OptionValueConstraintUP<T> ic, OptionValueConstraintUP<T> c) :
        if_con(std::move(ic)), then_con(std::move(c)) {}
        
        bool check(const OptionValue<T>& value){
            ASS(then_con);
            return !if_con->check(value) || then_con->check(value);
        }
        
        vstring msg(const OptionValue<T>& value){
            return "if "+if_con->msg(value)+" then "+ then_con->msg(value);
        }
        
        OptionValueConstraintUP<T> if_con;
        OptionValueConstraintUP<T> then_con;
    };
    
    template<typename T>
    struct IfConstraint {
        CLASS_NAME(IfConstraint);
        USE_ALLOCATOR(IfConstraint);
        IfConstraint(OptionValueConstraintUP<T> c) :if_con(std::move(c)) {}

        OptionValueConstraintUP<T> then(OptionValueConstraintUP<T> c){
          return OptionValueConstraintUP<T>(new IfThenConstraint<T>(std::move(if_con),std::move(c)));
        }
        OptionValueConstraintUP<T> then(AbstractWrappedConstraintUP c){
          return OptionValueConstraintUP<T>(new IfThenConstraint<T>(std::move(if_con),unwrap<T>(c)));
        }
        
        OptionValueConstraintUP<T> if_con;
    };
    
    template<typename T>
    static IfConstraint<T> If(OptionValueConstraintUP<T> c){
        return IfConstraint<T>(std::move(c));
    }
    template<typename T>
    static IfConstraint<T> If(AbstractWrappedConstraintUP c){
        return IfConstraint<T>(unwrap<T>(c));
    }

    /**
     * Default Value constraints
     */
    
    template<typename T>
    struct NotDefaultConstraint : public OptionValueConstraint<T> {
        NotDefaultConstraint() {}
        
        bool check(const OptionValue<T>& value){
            return value.defaultValue != value.actualValue;
        }
        vstring msg(const OptionValue<T>& value) { return value.longName+"("+value.getStringOfActual()+") is not default("+value.getStringOfValue(value.defaultValue)+")";}
    };
    struct NotDefaultRatioConstraint : public OptionValueConstraint<int> {
        NotDefaultRatioConstraint() {}
        
        bool check(const OptionValue<int>& value){
            const RatioOptionValue& rvalue = static_cast<const RatioOptionValue&>(value);
            return (rvalue.defaultValue != rvalue.actualValue ||
                    rvalue.defaultOtherValue != rvalue.otherValue);
        }
        vstring msg(const OptionValue<int>& value) { return value.longName+"("+value.getStringOfActual()+") is not default";}
        
    };
    
    // You will need to provide the type, optionally use addConstraintIfNotDefault
    template<typename T>
    static OptionValueConstraintUP<T> isNotDefault(){
        return OptionValueConstraintUP<T>(new NotDefaultConstraint<T>());
    }
    // You will need to provide the type, optionally use addConstraintIfNotDefault
    static OptionValueConstraintUP<int> isNotDefaultRatio(){
        return OptionValueConstraintUP<int>(new NotDefaultRatioConstraint());
    }

    struct isLookAheadSelectionConstraint : public OptionValueConstraint<int>{
        CLASS_NAME(isLookAheadSelectionConstraint);
        USE_ALLOCATOR(isLookAheadSelectionConstraint);
        isLookAheadSelectionConstraint() {}
        bool check(const OptionValue<int>& value){
            return value.actualValue == 11 || value.actualValue == 1011 || value.actualValue == -11 || value.actualValue == -1011;
        }
        vstring msg(const OptionValue<int>& value){
            return value.longName+"("+value.getStringOfActual()+") is not lookahead selection";
        }
    };
    
    
    /**
     * NOTE on OptionProblemConstraint
     *
     * OptionProblemConstraints are used to capture properties of a problem that
     * should be present when an option is used. The idea being that a warning will
     * be emitted if an option is used for an inappropriate problem.
     *
     * TODO - this element of Options is still under development
     */
    
    struct OptionProblemConstraint{
      CLASS_NAME(OptionProblemConstraint);
      USE_ALLOCATOR(OptionProblemConstraint);

      virtual bool check(Property* p) = 0;
      virtual vstring msg() = 0;
      virtual ~OptionProblemConstraint() {};
    };
    
    struct CategoryCondition : OptionProblemConstraint{
      CLASS_NAME(CategoryCondition);
      USE_ALLOCATOR(CategoryCondition);

      CategoryCondition(Property::Category c,bool h) : cat(c), has(h) {}
      bool check(Property*p){
          CALL("Options::CategoryCondition::check");
          ASS(p);
          return has ? p->category()==cat : p->category()!=cat;
      }
      vstring msg(){
        vstring m =" not useful for property ";
        if(has) m+="not";
        return m+" in category "+Property::categoryToString(cat);
      }
      Property::Category cat;
      bool has;
    };

    struct UsesEquality : OptionProblemConstraint{
      CLASS_NAME(UsesEquality);
      USE_ALLOCATOR(UsesEquality);

      bool check(Property*p){
        CALL("Options::UsesEquality::check");
        ASS(p)
        return (p->equalityAtoms() != 0);
      }
      vstring msg(){ return " only useful with equality"; }
    };

    struct HasHigherOrder : OptionProblemConstraint{
      CLASS_NAME(HasHigherOrder);
      USE_ALLOCATOR(HasHigherOrder);

      bool check(Property*p){
        CALL("Options::HasHigherOrder::check");
        ASS(p)
        return (p->higherOrder());
      }
      vstring msg(){ return " only useful with higher-order problems"; }
    };

    struct OnlyFirstOrder : OptionProblemConstraint{
      CLASS_NAME(OnlyFirstOrder);
      USE_ALLOCATOR(OnlyFirstOrder);

      bool check(Property*p){
        CALL("Options::OnlyFirstOrder::check");
        ASS(p)
        return (!p->higherOrder());
      }
      vstring msg(){ return " not compatible with higher-order problems"; }
    };

    struct HasNonUnits : OptionProblemConstraint{
      CLASS_NAME(HasNonUnits);
      USE_ALLOCATOR(HasNonUnits);

      bool check(Property*p){
        CALL("Options::HasNonUnits::check");
        return (p->clauses()-p->unitClauses())!=0;
      }
      vstring msg(){ return " only useful with non-unit clauses"; }
    };

    struct HasPredicates : OptionProblemConstraint{
      CLASS_NAME(HasPredicates);
      USE_ALLOCATOR(HasPredicates);

      bool check(Property*p){
        CALL("Options::HasPredicates::check");
        return (p->category()==Property::PEQ || p->category()==Property::UEQ);
      }
      vstring msg(){ return " only useful with predicates"; }
    };

    struct AtomConstraint : OptionProblemConstraint{
      CLASS_NAME(AtomConstraint);
      USE_ALLOCATOR(AtomConstraint);

      AtomConstraint(int a,bool g) : atoms(a),greater(g) {}
      int atoms;
      bool greater;
      bool check(Property*p){ 
        CALL("Options::AtomConstraint::check");
        return greater ? p->atoms()>atoms : p->atoms()<atoms;
      }
          
      vstring msg(){ 
        vstring m = " not with ";
        if(greater){ m+="more";}else{m+="less";}
        return m+" than "+Lib::Int::toString(atoms)+" atoms";
      }
    };

    struct HasTheories : OptionProblemConstraint {
      CLASS_NAME(HasTheories);
      USE_ALLOCATOR(HasTheories);

      bool check(Property*p);
      vstring msg(){ return " only useful with theories"; }
    };

    struct HasFormulas : OptionProblemConstraint {
      CLASS_NAME(HasFormulas);
      USE_ALLOCATOR(HasFormulas);

      bool check(Property*p) {
        CALL("Options::HasFormulas::check");
        return p->hasFormulas();
      }
      vstring msg(){ return " only useful with (non-cnf) formulas"; }
    };

    struct HasGoal : OptionProblemConstraint {
      CLASS_NAME(HasGoal);
      USE_ALLOCATOR(HasGoal);

      bool check(Property*p){
        CALL("Options::HasGoal::check");
        return p->hasGoal();
      }
      vstring msg(){ return " only useful with a goal: (conjecture) formulas or (negated_conjecture) clauses"; }
    };

    // Factory methods
    static OptionProblemConstraintUP notWithCat(Property::Category c){
      return OptionProblemConstraintUP(new CategoryCondition(c,false));
    }
    static OptionProblemConstraintUP hasCat(Property::Category c){
      return OptionProblemConstraintUP(new CategoryCondition(c,true));
    }
    static OptionProblemConstraintUP hasEquality(){ return OptionProblemConstraintUP(new UsesEquality); }
    static OptionProblemConstraintUP hasHigherOrder(){ return OptionProblemConstraintUP(new HasHigherOrder); }
    static OptionProblemConstraintUP onlyFirstOrder(){ return OptionProblemConstraintUP(new OnlyFirstOrder); }
    static OptionProblemConstraintUP hasNonUnits(){ return OptionProblemConstraintUP(new HasNonUnits); }
    static OptionProblemConstraintUP hasPredicates(){ return OptionProblemConstraintUP(new HasPredicates); }
    static OptionProblemConstraintUP atomsMoreThan(int a){
      return OptionProblemConstraintUP(new AtomConstraint(a,true));
    }
    static OptionProblemConstraintUP atomsLessThan(int a){
      return OptionProblemConstraintUP(new AtomConstraint(a,false));
    }
    static OptionProblemConstraintUP hasFormulas() { return OptionProblemConstraintUP(new HasFormulas); }
    static OptionProblemConstraintUP hasTheories() { return OptionProblemConstraintUP(new HasTheories); }
    static OptionProblemConstraintUP hasGoal() { return OptionProblemConstraintUP(new HasGoal); }

    //Cheating - we refer to env.options to ask about option values
    // There is an assumption that the option values used have been
    // set to their final values
    // These are used in randomisation where we guarantee a certain
    // set of options will not be randomized and some will be randomized first

    struct OptionHasValue : OptionProblemConstraint{
      CLASS_NAME(OptionHasValue);
      USE_ALLOCATOR(OptionHasValue);

      OptionHasValue(vstring ov,vstring v) : option_value(ov),value(v) {}
      bool check(Property*p);
      vstring msg(){ return option_value+" has value "+value; } 
      vstring option_value;
      vstring value; 
    };

    struct ManyOptionProblemConstraints : OptionProblemConstraint {
      CLASS_NAME(ManyOptionProblemConstraints);
      USE_ALLOCATOR(ManyOptionProblemConstraints);

      ManyOptionProblemConstraints(bool a) : is_and(a) {}

      bool check(Property*p){
        CALL("Options::ManyOptionProblemConstraints::check");
        bool res = is_and;
        Stack<OptionProblemConstraintUP>::Iterator it(cons);
        while(it.hasNext()){ 
          bool n=it.next()->check(p);res = is_and ? (res && n) : (res || n);}
        return res;
      } 

      vstring msg(){
        vstring res="";
        Stack<OptionProblemConstraintUP>::Iterator it(cons);
        if(it.hasNext()){ res=it.next()->msg();}
        while(it.hasNext()){ res+=",and\n"+it.next()->msg();}
        return res;
      }

      void add(OptionProblemConstraintUP& c){ cons.push(std::move(c));}
      Stack<OptionProblemConstraintUP> cons;
      bool is_and;
    };

    static OptionProblemConstraintUP And(OptionProblemConstraintUP left,
                                        OptionProblemConstraintUP right){
       ManyOptionProblemConstraints* c = new ManyOptionProblemConstraints(true);
       c->add(left);c->add(right);
       return OptionProblemConstraintUP(c);
    }
    static OptionProblemConstraintUP And(OptionProblemConstraintUP left,
                                        OptionProblemConstraintUP mid,
                                        OptionProblemConstraintUP right){
       ManyOptionProblemConstraints* c = new ManyOptionProblemConstraints(true);
       c->add(left);c->add(mid);c->add(right);
       return OptionProblemConstraintUP(c);
    }
    static OptionProblemConstraintUP Or(OptionProblemConstraintUP left,
                                        OptionProblemConstraintUP right){
       ManyOptionProblemConstraints* c = new ManyOptionProblemConstraints(false);
       c->add(left);c->add(right);
       return OptionProblemConstraintUP(c);
    }
    static OptionProblemConstraintUP Or(OptionProblemConstraintUP left,
                                        OptionProblemConstraintUP mid,
                                        OptionProblemConstraintUP right){
       ManyOptionProblemConstraints* c = new ManyOptionProblemConstraints(false);
       c->add(left);c->add(mid);c->add(right);
       return OptionProblemConstraintUP(c);
    }
    
    static OptionProblemConstraintUP isRandOn();
    static OptionProblemConstraintUP isRandSat();
    static OptionProblemConstraintUP saNotInstGen();

  //==========================================================
  // Getter functions
  // -currently disabled all unnecessary setter functions
  //==========================================================
  //
  // This is how options are accessed so if you add a new option you should add a getter
public:
  bool encodeStrategy() const{ return _encode.actualValue;}
  RandomStrategy randomStrategy() const {return _randomStrategy.actualValue; }
  void setRandomStrategy(RandomStrategy newVal){ _randomStrategy.actualValue=newVal;}
  BadOption getBadOptionChoice() const { return _badOption.actualValue; }
  void setBadOptionChoice(BadOption newVal) { _badOption.actualValue = newVal; }
  vstring forcedOptions() const { return _forcedOptions.actualValue; }
  vstring forbiddenOptions() const { return _forbiddenOptions.actualValue; }
  vstring testId() const { return _testId.actualValue; }
  vstring protectedPrefix() const { return _protectedPrefix.actualValue; }
  Statistics statistics() const { return _statistics.actualValue; }
  void setStatistics(Statistics newVal) { _statistics.actualValue=newVal; }
  Proof proof() const { return _proof.actualValue; }
  bool minimizeSatProofs() const { return _minimizeSatProofs.actualValue; }
  ProofExtra proofExtra() const { return _proofExtra.actualValue; }
  vstring printProofToFile() const { return _printProofToFile.actualValue; }
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

  bool flattenTopLevelConjunctions() const { return _flattenTopLevelConjunctions.actualValue; }
  LTBLearning ltbLearning() const { return _ltbLearning.actualValue; }
  vstring ltbDirectory() const { return _ltbDirectory.actualValue; }
  Mode mode() const { return _mode.actualValue; }
  Schedule schedule() const { return _schedule.actualValue; }
  vstring scheduleName() const { return _schedule.getStringOfValue(_schedule.actualValue); }
  void setSchedule(Schedule newVal) {  _schedule.actualValue = newVal; }
  unsigned multicore() const { return _multicore.actualValue; }
  void setMulticore(unsigned newVal) { _multicore.actualValue = newVal; }
  float slowness() const {return _slowness.actualValue; }
  InputSyntax inputSyntax() const { return _inputSyntax.actualValue; }
  void setInputSyntax(InputSyntax newVal) { _inputSyntax.actualValue = newVal; }
  bool normalize() const { return _normalize.actualValue; }
  void setNormalize(bool normalize) { _normalize.actualValue = normalize; }
  GoalGuess guessTheGoal() const { return _guessTheGoal.actualValue; }
  unsigned gtgLimit() const { return _guessTheGoalLimit.actualValue; }
  void setMaxXX(unsigned max) { _maximumXXNarrows.actualValue = max; }

  void setNaming(int n){ _naming.actualValue = n;} //TODO: ensure global constraints
  vstring include() const { return _include.actualValue; }
  void setInclude(vstring val) { _include.actualValue = val; }
  vstring inputFile() const { return _inputFile.actualValue; }
  int activationLimit() const { return _activationLimit.actualValue; }
  int randomSeed() const { return _randomSeed.actualValue; }
  int randomStrategySeed() const { return _randomStrategySeed.actualValue; }
  bool printClausifierPremises() const { return _printClausifierPremises.actualValue; }

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

#if VZ3
  bool showZ3() const { return showAll() || _showZ3.actualValue; }
  vstring const& exportAvatarProblem() const { return _exportAvatarProblem.actualValue; }
  vstring const& exportThiProblem() const { return _exportThiProblem.actualValue; }
#endif
  
  // end of show commands

  bool showNonconstantSkolemFunctionTrace() const { return _showNonconstantSkolemFunctionTrace.actualValue; }
  void setShowNonconstantSkolemFunctionTrace(bool newVal) { _showNonconstantSkolemFunctionTrace.actualValue = newVal; }
  InterpolantMode showInterpolant() const { return _showInterpolant.actualValue; }
  bool showOptions() const { return _showOptions.actualValue; }
  bool lineWrapInShowOptions() const { return _showOptionsLineWrap.actualValue; }
  bool showExperimentalOptions() const { return _showExperimentalOptions.actualValue; }
  bool showHelp() const { return _showHelp.actualValue; }
  vstring explainOption() const { return _explainOption.actualValue; }

  bool printAllTheoryAxioms() const { return _printAllTheoryAxioms.actualValue; }

#if VZ3
  bool satFallbackForSMT() const { return _satFallbackForSMT.actualValue; }
  bool smtForGround() const { return _smtForGround.actualValue; }
  TheoryInstSimp theoryInstAndSimp() const { return _theoryInstAndSimp.actualValue; }
  bool thiGeneralise() const { return _thiGeneralise.actualValue; }
  bool thiTautologyDeletion() const { return _thiTautologyDeletion.actualValue; }
#endif
  UnificationWithAbstraction unificationWithAbstraction() const { return _unificationWithAbstraction.actualValue; }
  void setUWA(UnificationWithAbstraction value){ _unificationWithAbstraction.actualValue = value; } 
  bool fixUWA() const { return _fixUWA.actualValue; }
  bool useACeval() const { return _useACeval.actualValue;}

  bool unusedPredicateDefinitionRemoval() const { return _unusedPredicateDefinitionRemoval.actualValue; }
  bool blockedClauseElimination() const { return _blockedClauseElimination.actualValue; }
  void setUnusedPredicateDefinitionRemoval(bool newVal) { _unusedPredicateDefinitionRemoval.actualValue = newVal; }
  // bool useDM() const { return _use_dm.actualValue; }
  SatSolver satSolver() const { return _satSolver.actualValue; }
  //void setSatSolver(SatSolver newVal) { _satSolver = newVal; }
  SaturationAlgorithm saturationAlgorithm() const { return _saturationAlgorithm.actualValue; }
  void setSaturationAlgorithm(SaturationAlgorithm newVal) { _saturationAlgorithm.actualValue = newVal; }
  int selection() const { return _selection.actualValue; }
  void setSelection(int v) { _selection.actualValue=v;}
  vstring latexOutput() const { return _latexOutput.actualValue; }
  bool latexUseDefault() const { return _latexUseDefaultSymbols.actualValue; }
  LiteralComparisonMode literalComparisonMode() const { return _literalComparisonMode.actualValue; }
  bool forwardSubsumptionResolution() const { return _forwardSubsumptionResolution.actualValue; }
  //void setForwardSubsumptionResolution(bool newVal) { _forwardSubsumptionResolution = newVal; }
  bool forwardSubsumptionDemodulation() const { return _forwardSubsumptionDemodulation.actualValue; }
  unsigned forwardSubsumptionDemodulationMaxMatches() const { return _forwardSubsumptionDemodulationMaxMatches.actualValue; }
  Demodulation forwardDemodulation() const { return _forwardDemodulation.actualValue; }
  bool binaryResolution() const { return _binaryResolution.actualValue; }
  URResolution unitResultingResolution() const { return _unitResultingResolution.actualValue; }
  bool hyperSuperposition() const { return _hyperSuperposition.actualValue; }
  bool simulatenousSuperposition() const { return _simultaneousSuperposition.actualValue; }
  bool innerRewriting() const { return _innerRewriting.actualValue; }
  bool equationalTautologyRemoval() const { return _equationalTautologyRemoval.actualValue; }
  bool arityCheck() const { return _arityCheck.actualValue; }
  //void setArityCheck(bool newVal) { _arityCheck=newVal; }
  Demodulation backwardDemodulation() const { return _backwardDemodulation.actualValue; }
  bool demodulationRedundancyCheck() const { return _demodulationRedundancyCheck.actualValue; }
  //void setBackwardDemodulation(Demodulation newVal) { _backwardDemodulation = newVal; }
  Subsumption backwardSubsumption() const { return _backwardSubsumption.actualValue; }
  //void setBackwardSubsumption(Subsumption newVal) { _backwardSubsumption = newVal; }
  Subsumption backwardSubsumptionResolution() const { return _backwardSubsumptionResolution.actualValue; }
  bool backwardSubsumptionDemodulation() const { return _backwardSubsumptionDemodulation.actualValue; }
  unsigned backwardSubsumptionDemodulationMaxMatches() const { return _backwardSubsumptionDemodulationMaxMatches.actualValue; }
  bool forwardSubsumption() const { return _forwardSubsumption.actualValue; }
  bool forwardLiteralRewriting() const { return _forwardLiteralRewriting.actualValue; }
  int lrsFirstTimeCheck() const { return _lrsFirstTimeCheck.actualValue; }
  int lrsWeightLimitOnly() const { return _lrsWeightLimitOnly.actualValue; }
  int lookaheadDelay() const { return _lookaheadDelay.actualValue; }
  int simulatedTimeLimit() const { return _simulatedTimeLimit.actualValue; }
  void setSimulatedTimeLimit(int newVal) { _simulatedTimeLimit.actualValue = newVal; }
  TermOrdering termOrdering() const { return _termOrdering.actualValue; }
  SymbolPrecedence symbolPrecedence() const { return _symbolPrecedence.actualValue; }
  SymbolPrecedenceBoost symbolPrecedenceBoost() const { return _symbolPrecedenceBoost.actualValue; }
  IntroducedSymbolPrecedence introducedSymbolPrecedence() const { return _introducedSymbolPrecedence.actualValue; }
  const KboAdmissibilityCheck kboAdmissabilityCheck() const { return _kboAdmissabilityCheck.actualValue; }
  const vstring& functionWeights() const { return _functionWeights.actualValue; }
  const vstring& predicateWeights() const { return _predicateWeights.actualValue; }
  const vstring& functionPrecedence() const { return _functionPrecedence.actualValue; }
  const vstring& predicatePrecedence() const { return _predicatePrecedence.actualValue; }
  // Return time limit in deciseconds, or 0 if there is no time limit
  int timeLimitInDeciseconds() const { return _timeLimitInDeciseconds.actualValue; }
  size_t memoryLimit() const { return _memoryLimit.actualValue; }
#ifdef __linux__
  size_t instructionLimit() const { return _instructionLimit.actualValue; }
#endif
  int inequalitySplitting() const { return _inequalitySplitting.actualValue; }
  int ageRatio() const { return _ageWeightRatio.actualValue; }
  void setAgeRatio(int v){ _ageWeightRatio.actualValue = v; }
  int weightRatio() const { return _ageWeightRatio.otherValue; }
  bool useTheorySplitQueues() const { return _useTheorySplitQueues.actualValue; }
  Lib::vvector<int> theorySplitQueueRatios() const;
  Lib::vvector<float> theorySplitQueueCutoffs() const;
  int theorySplitQueueExpectedRatioDenom() const { return _theorySplitQueueExpectedRatioDenom.actualValue; }
  bool theorySplitQueueLayeredArrangement() const { return _theorySplitQueueLayeredArrangement.actualValue; }
  bool useAvatarSplitQueues() const { return _useAvatarSplitQueues.actualValue; }
  Lib::vvector<int> avatarSplitQueueRatios() const;
  Lib::vvector<float> avatarSplitQueueCutoffs() const;
  bool avatarSplitQueueLayeredArrangement() const { return _avatarSplitQueueLayeredArrangement.actualValue; }
  bool useSineLevelSplitQueues() const { return _useSineLevelSplitQueues.actualValue; }
  Lib::vvector<int> sineLevelSplitQueueRatios() const;
  Lib::vvector<float> sineLevelSplitQueueCutoffs() const;
  bool sineLevelSplitQueueLayeredArrangement() const { return _sineLevelSplitQueueLayeredArrangement.actualValue; }
  bool usePositiveLiteralSplitQueues() const { return _usePositiveLiteralSplitQueues.actualValue; }
  Lib::vvector<int> positiveLiteralSplitQueueRatios() const;
  Lib::vvector<float> positiveLiteralSplitQueueCutoffs() const;
  bool positiveLiteralSplitQueueLayeredArrangement() const { return _positiveLiteralSplitQueueLayeredArrangement.actualValue; }
  void setWeightRatio(int v){ _ageWeightRatio.otherValue = v; }
	AgeWeightRatioShape ageWeightRatioShape() const { return _ageWeightRatioShape.actualValue; }
	int ageWeightRatioShapeFrequency() const { return _ageWeightRatioShapeFrequency.actualValue; }
  bool literalMaximalityAftercheck() const { return _literalMaximalityAftercheck.actualValue; }
  bool superpositionFromVariables() const { return _superpositionFromVariables.actualValue; }
  EqualityProxy equalityProxy() const { return _equalityProxy.actualValue; }
  bool useMonoEqualityProxy() const { return _useMonoEqualityProxy.actualValue; }
  bool equalityResolutionWithDeletion() const { return _equalityResolutionWithDeletion.actualValue; }
  ExtensionalityResolution extensionalityResolution() const { return _extensionalityResolution.actualValue; }
  bool FOOLParamodulation() const { return _FOOLParamodulation.actualValue; }
  bool termAlgebraInferences() const { return _termAlgebraInferences.actualValue; }
  TACyclicityCheck termAlgebraCyclicityCheck() const { return _termAlgebraCyclicityCheck.actualValue; }
  unsigned extensionalityMaxLength() const { return _extensionalityMaxLength.actualValue; }
  bool extensionalityAllowPosEq() const { return _extensionalityAllowPosEq.actualValue; }
  unsigned nongoalWeightCoefficientNumerator() const { return _nonGoalWeightCoefficient.numerator; }
  unsigned nongoalWeightCoefficientDenominator() const { return _nonGoalWeightCoefficient.denominator; }
  bool restrictNWCtoGC() const { return _restrictNWCtoGC.actualValue; }
  Sos sos() const { return _sos.actualValue; }
  unsigned sosTheoryLimit() const { return _sosTheoryLimit.actualValue; }
  //void setSos(Sos newVal) { _sos = newVal; }

  bool ignoreConjectureInPreprocessing() const {return _ignoreConjectureInPreprocessing.actualValue;}

  FunctionDefinitionElimination functionDefinitionElimination() const { return _functionDefinitionElimination.actualValue; }
  bool skolemReuse() const { return _skolemReuse.actualValue; }
  bool definitionReuse() const { return _definitionReuse.actualValue; }
  bool outputAxiomNames() const { return _outputAxiomNames.actualValue; }
  void setOutputAxiomNames(bool newVal) { _outputAxiomNames.actualValue = newVal; }
  QuestionAnsweringMode questionAnswering() const { return _questionAnswering.actualValue; }
  Output outputMode() const { return _outputMode.actualValue; }
  void setOutputMode(Output newVal) { _outputMode.actualValue = newVal; }
  bool ignoreMissingInputsInUnsatCore() {  return _ignoreMissingInputsInUnsatCore.actualValue; }
  vstring thanks() const { return _thanks.actualValue; }
  void setQuestionAnswering(QuestionAnsweringMode newVal) { _questionAnswering.actualValue = newVal; }
  bool globalSubsumption() const { return _globalSubsumption.actualValue; }
  GlobalSubsumptionSatSolverPower globalSubsumptionSatSolverPower() const { return _globalSubsumptionSatSolverPower.actualValue; }
  GlobalSubsumptionExplicitMinim globalSubsumptionExplicitMinim() const { return _globalSubsumptionExplicitMinim.actualValue; }
  GlobalSubsumptionAvatarAssumptions globalSubsumptionAvatarAssumptions() const { return _globalSubsumptionAvatarAssumptions.actualValue; }

  /** true if calling set() on non-existing options does not result in a user error */
  IgnoreMissing ignoreMissing() const { return _ignoreMissing.actualValue; }
  void setIgnoreMissing(IgnoreMissing newVal) { _ignoreMissing.actualValue = newVal; }
  bool increasedNumeralWeight() const { return _increasedNumeralWeight.actualValue; }
  TheoryAxiomLevel theoryAxioms() const { return _theoryAxioms.actualValue; }
  //void setTheoryAxioms(bool newValue) { _theoryAxioms = newValue; }
  Condensation condensation() const { return _condensation.actualValue; }
  bool generalSplitting() const { return _generalSplitting.actualValue; }
  bool timeStatistics() const { return _timeStatistics.actualValue; }
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

  bool colorUnblocking() const { return _colorUnblocking.actualValue; }

  Instantiation instantiation() const { return _instantiation.actualValue; }
  bool theoryFlattening() const { return _theoryFlattening.actualValue; }

  Induction induction() const { return _induction.actualValue; }
  StructuralInductionKind structInduction() const { return _structInduction.actualValue; }
  IntInductionKind intInduction() const { return _intInduction.actualValue; }
  InductionChoice inductionChoice() const { return _inductionChoice.actualValue; }
  unsigned maxInductionDepth() const { return _maxInductionDepth.actualValue; }
  bool inductionNegOnly() const { return _inductionNegOnly.actualValue; }
  bool inductionUnitOnly() const { return _inductionUnitOnly.actualValue; }
  bool inductionGen() const { return _inductionGen.actualValue; }
  unsigned maxInductionGenSubsetSize() const { return _maxInductionGenSubsetSize.actualValue; }
  bool inductionOnComplexTerms() const {return _inductionOnComplexTerms.actualValue;}
  bool integerInductionDefaultBound() const { return _integerInductionDefaultBound.actualValue; }
  IntegerInductionInterval integerInductionInterval() const { return _integerInductionInterval.actualValue; }

  float instGenBigRestartRatio() const { return _instGenBigRestartRatio.actualValue; }
  bool instGenPassiveReactivation() const { return _instGenPassiveReactivation.actualValue; }
  int instGenResolutionRatioInstGen() const { return _instGenResolutionInstGenRatio.actualValue; }
  int instGenResolutionRatioResolution() const { return _instGenResolutionInstGenRatio.otherValue; }
  int instGenRestartPeriod() const { return _instGenRestartPeriod.actualValue; }
  float instGenRestartPeriodQuotient() const { return _instGenRestartPeriodQuotient.actualValue; }
  int instGenSelection() const { return _instGenSelection.actualValue; }
  bool instGenWithResolution() const { return _instGenWithResolution.actualValue; }
  bool useHashingVariantIndex() const { return _useHashingVariantIndex.actualValue; }

  void setMemoryLimit(size_t newVal) { _memoryLimit.actualValue = newVal; }
  void setTimeLimitInSeconds(int newVal) { _timeLimitInDeciseconds.actualValue = 10*newVal; }
  void setTimeLimitInDeciseconds(int newVal) { _timeLimitInDeciseconds.actualValue = newVal; }

  bool splitAtActivation() const{ return _splitAtActivation.actualValue; }
  SplittingNonsplittableComponents splittingNonsplittableComponents() const { return _splittingNonsplittableComponents.actualValue; }
  SplittingAddComplementary splittingAddComplementary() const { return _splittingAddComplementary.actualValue; }
  SplittingMinimizeModel splittingMinimizeModel() const { return _splittingMinimizeModel.actualValue; }
  SplittingLiteralPolarityAdvice splittingLiteralPolarityAdvice() const { return _splittingLiteralPolarityAdvice.actualValue; }
  SplittingDeleteDeactivated splittingDeleteDeactivated() const { return _splittingDeleteDeactivated.actualValue;}
  bool splittingFastRestart() const { return _splittingFastRestart.actualValue; }
  bool splittingBufferedSolver() const { return _splittingBufferedSolver.actualValue; }
  int splittingFlushPeriod() const { return _splittingFlushPeriod.actualValue; }
  float splittingFlushQuotient() const { return _splittingFlushQuotient.actualValue; }
  float splittingAvatimer() const { return _splittingAvatimer.actualValue; }
  bool splittingEagerRemoval() const { return _splittingEagerRemoval.actualValue; }
  SplittingCongruenceClosure splittingCongruenceClosure() const { return _splittingCongruenceClosure.actualValue; }
  CCUnsatCores ccUnsatCores() const { return _ccUnsatCores.actualValue; }

  void setProof(Proof p) { _proof.actualValue = p; }
    
  bool newCNF() const { return _newCNF.actualValue; }
  bool getIteInlineLet() const { return _inlineLet.actualValue; }

  bool useManualClauseSelection() const { return _manualClauseSelection.actualValue; }
  bool inequalityNormalization() const { return _inequalityNormalization.actualValue; }
  EvaluationMode evaluationMode() const { return _highSchool.actualValue ? EvaluationMode::POLYNOMIAL_CAUTIOUS : _evaluationMode.actualValue; }
  ArithmeticSimplificationMode gaussianVariableElimination() const { return _highSchool.actualValue ? ArithmeticSimplificationMode::CAUTIOUS : _gaussianVariableElimination.actualValue; }
  bool pushUnaryMinus() const { return _pushUnaryMinus.actualValue || _highSchool.actualValue; }
  ArithmeticSimplificationMode cancellation() const { return _highSchool.actualValue ? ArithmeticSimplificationMode::CAUTIOUS : _cancellation.actualValue; }
  ArithmeticSimplificationMode arithmeticSubtermGeneralizations() const { return  _highSchool.actualValue ? ArithmeticSimplificationMode::CAUTIOUS : _arithmeticSubtermGeneralizations.actualValue; }

  //Higher-order Options

  bool addCombAxioms() const { return _addCombAxioms.actualValue; }
  bool addProxyAxioms() const { return _addProxyAxioms.actualValue; }
  bool combinatorySup() const { return _combinatorySuperposition.actualValue; }
  bool choiceAxiom() const { return _choiceAxiom.actualValue; }
  bool injectivityReasoning() const { return _injectivity.actualValue; }
  bool pragmatic() const { return _pragmatic.actualValue; }
  bool choiceReasoning() const { return _choiceReasoning.actualValue; }
  bool prioritiseClausesProducedByLongReduction() const { return _priortyToLongReducts.actualValue; }
  int maxXXNarrows() const { return _maximumXXNarrows.actualValue; }
  FunctionExtensionality functionExtensionality() const { return _functionExtensionality.actualValue; }
  CNFOnTheFly cnfOnTheFly() const { return _clausificationOnTheFly.actualValue; }
  PISet piSet() const { return _piSet.actualValue; }
  Narrow narrow() const { return _narrow.actualValue; }
  bool equalityToEquivalence () const { return _equalityToEquivalence.actualValue; }
  bool complexBooleanReasoning () const { return _complexBooleanReasoning.actualValue; }
  bool booleanEqTrick() const { return _booleanEqTrick.actualValue; }
  bool superposition() const {return _superposition.actualValue; }
  bool casesSimp() const { return _casesSimp.actualValue; }
  bool cases() const { return _cases.actualValue; }
  bool newTautologyDel() const { return _newTautologyDel.actualValue; }
  bool lambdaFreeHol() const { return _lambdaFreeHol.actualValue; }

private:
    
    /**
     * A LookupWrapper is used to wrap up two maps for long and short names and query them
     */
    struct LookupWrapper {
        
        LookupWrapper() {}
        
        private:
          LookupWrapper operator=(const LookupWrapper&){ NOT_IMPLEMENTED;}
        public:
        
        void insert(AbstractOptionValue* option_value){
            CALL("LookupWrapper::insert");
            ASS(!option_value->longName.empty());
            bool new_long =  _longMap.insert(option_value->longName,option_value);
            bool new_short = true;
            if(!option_value->shortName.empty()){
                new_short = _shortMap.insert(option_value->shortName,option_value);
            }
            if(!new_long || !new_short){ cout << "Bad " << option_value->longName << endl; }
            ASS(new_long && new_short);
        }
        AbstractOptionValue* findLong(vstring longName) const{
            CALL("LookupWrapper::findLong");
            if(!_longMap.find(longName)){ throw ValueNotFoundException(); }
            return _longMap.get(longName);
        }
        AbstractOptionValue* findShort(vstring shortName) const{
            CALL("LookupWrapper::findShort");
            if(!_shortMap.find(shortName)){ throw ValueNotFoundException(); }
            return _shortMap.get(shortName);
        }
        
        VirtualIterator<AbstractOptionValue*> values() const {
            return _longMap.range();
        }
        
    private:
        DHMap<vstring,AbstractOptionValue*> _longMap;
        DHMap<vstring,AbstractOptionValue*> _shortMap;
    };
    
    LookupWrapper _lookup;
    
    // The const is a lie - we can alter the resulting OptionValue
    AbstractOptionValue* getOptionValueByName(vstring name) const{
        try{
          return _lookup.findLong(name);
        }
        catch(ValueNotFoundException&){
          try{
            return _lookup.findShort(name);
          }
          catch(ValueNotFoundException&){
            return 0;
          }
        }
    }
  
    Stack<vstring> getSimilarOptionNames(vstring name, bool is_short) const{

      Stack<vstring> similar_names;

      VirtualIterator<AbstractOptionValue*> options = _lookup.values();
      while(options.hasNext()){
        AbstractOptionValue* opt = options.next();
        vstring opt_name = is_short ? opt->shortName : opt->longName;
        size_t dif = 2;
        if(!is_short) dif += name.size()/4;
        if(name.size()!=0 && distance(name,opt_name) < dif)
          similar_names.push(opt_name);
      }

      return similar_names;
    }
    
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

  ChoiceOptionValue<RandomStrategy> _randomStrategy;
  DecodeOptionValue _decode;
  BoolOptionValue _encode;

  RatioOptionValue _ageWeightRatio;
	ChoiceOptionValue<AgeWeightRatioShape> _ageWeightRatioShape;
	UnsignedOptionValue _ageWeightRatioShapeFrequency;
  BoolOptionValue _useTheorySplitQueues;
  StringOptionValue _theorySplitQueueRatios;
  StringOptionValue _theorySplitQueueCutoffs;
  IntOptionValue _theorySplitQueueExpectedRatioDenom;
  BoolOptionValue _theorySplitQueueLayeredArrangement;
  BoolOptionValue _useAvatarSplitQueues;
  StringOptionValue _avatarSplitQueueRatios;
  StringOptionValue _avatarSplitQueueCutoffs;
  BoolOptionValue _avatarSplitQueueLayeredArrangement;
  BoolOptionValue _useSineLevelSplitQueues;
  StringOptionValue _sineLevelSplitQueueRatios;
  StringOptionValue _sineLevelSplitQueueCutoffs;
  BoolOptionValue _sineLevelSplitQueueLayeredArrangement;
  BoolOptionValue _usePositiveLiteralSplitQueues;
  StringOptionValue _positiveLiteralSplitQueueRatios;
  StringOptionValue _positiveLiteralSplitQueueCutoffs;
  BoolOptionValue _positiveLiteralSplitQueueLayeredArrangement;
  BoolOptionValue _literalMaximalityAftercheck;
  BoolOptionValue _arityCheck;
  
  ChoiceOptionValue<BadOption> _badOption;
  ChoiceOptionValue<Demodulation> _backwardDemodulation;
  ChoiceOptionValue<Subsumption> _backwardSubsumption;
  ChoiceOptionValue<Subsumption> _backwardSubsumptionResolution;
  BoolOptionValue _backwardSubsumptionDemodulation;
  UnsignedOptionValue _backwardSubsumptionDemodulationMaxMatches;
  BoolOptionValue _binaryResolution;

  BoolOptionValue _colorUnblocking;
  ChoiceOptionValue<Condensation> _condensation;

  BoolOptionValue _demodulationRedundancyCheck;

  ChoiceOptionValue<EqualityProxy> _equalityProxy;
  BoolOptionValue _useMonoEqualityProxy;
  BoolOptionValue _equalityResolutionWithDeletion;
  BoolOptionValue _equivalentVariableRemoval;
  ChoiceOptionValue<ExtensionalityResolution> _extensionalityResolution;
  UnsignedOptionValue _extensionalityMaxLength;
  BoolOptionValue _extensionalityAllowPosEq;

  BoolOptionValue _FOOLParamodulation;

  BoolOptionValue _termAlgebraInferences;
  ChoiceOptionValue<TACyclicityCheck> _termAlgebraCyclicityCheck;

  BoolOptionValue _fmbNonGroundDefs;
  UnsignedOptionValue _fmbStartSize;
  FloatOptionValue _fmbSymmetryRatio;
  ChoiceOptionValue<FMBWidgetOrders> _fmbSymmetryWidgetOrders;
  ChoiceOptionValue<FMBSymbolOrders> _fmbSymmetryOrderSymbols;
  ChoiceOptionValue<FMBAdjustSorts> _fmbAdjustSorts;
  BoolOptionValue _fmbDetectSortBounds;
  UnsignedOptionValue _fmbDetectSortBoundsTimeLimit;
  UnsignedOptionValue _fmbSizeWeightRatio;
  ChoiceOptionValue<FMBEnumerationStrategy> _fmbEnumerationStrategy;

  BoolOptionValue _flattenTopLevelConjunctions;
  StringOptionValue _forbiddenOptions;
  BoolOptionValue _forceIncompleteness;
  StringOptionValue _forcedOptions;
  ChoiceOptionValue<Demodulation> _forwardDemodulation;
  BoolOptionValue _forwardLiteralRewriting;
  BoolOptionValue _forwardSubsumption;
  BoolOptionValue _forwardSubsumptionResolution;
  BoolOptionValue _forwardSubsumptionDemodulation;
  UnsignedOptionValue _forwardSubsumptionDemodulationMaxMatches;
  ChoiceOptionValue<FunctionDefinitionElimination> _functionDefinitionElimination;
  BoolOptionValue _skolemReuse;
  BoolOptionValue _definitionReuse;
  
  BoolOptionValue _generalSplitting;
  BoolOptionValue _globalSubsumption;
  ChoiceOptionValue<GlobalSubsumptionSatSolverPower> _globalSubsumptionSatSolverPower;
  ChoiceOptionValue<GlobalSubsumptionExplicitMinim> _globalSubsumptionExplicitMinim;
  ChoiceOptionValue<GlobalSubsumptionAvatarAssumptions> _globalSubsumptionAvatarAssumptions;
  ChoiceOptionValue<GoalGuess> _guessTheGoal;
  UnsignedOptionValue _guessTheGoalLimit;

  BoolOptionValue _hyperSuperposition;

  BoolOptionValue _simultaneousSuperposition;
  BoolOptionValue _innerRewriting;
  BoolOptionValue _equationalTautologyRemoval;

  /** if true, then calling set() on non-existing options will not result in a user error */
  ChoiceOptionValue<IgnoreMissing> _ignoreMissing;
  StringOptionValue _include;
  /** if this option is true, Vampire will add the numeral weight of a clause
   * to its weight. The weight is defined as the sum of binary sizes of all
   * integers occurring in this clause. This option has not been tested and
   * may be extensive, see Clause::getNumeralWeight()
   */
  BoolOptionValue _increasedNumeralWeight;

  BoolOptionValue _ignoreConjectureInPreprocessing;

  IntOptionValue _inequalitySplitting;
  ChoiceOptionValue<InputSyntax> _inputSyntax;
  ChoiceOptionValue<Instantiation> _instantiation;
  FloatOptionValue _instGenBigRestartRatio;
  BoolOptionValue _instGenPassiveReactivation;
  RatioOptionValue _instGenResolutionInstGenRatio;
  //IntOptionValue _instGenResolutionRatioResolution;
  IntOptionValue _instGenRestartPeriod;
  FloatOptionValue _instGenRestartPeriodQuotient;
  BoolOptionValue _instGenWithResolution;
  BoolOptionValue _useHashingVariantIndex;

  ChoiceOptionValue<Induction> _induction;
  ChoiceOptionValue<StructuralInductionKind> _structInduction;
  ChoiceOptionValue<IntInductionKind> _intInduction;
  ChoiceOptionValue<InductionChoice> _inductionChoice;
  UnsignedOptionValue _maxInductionDepth;
  BoolOptionValue _inductionNegOnly;
  BoolOptionValue _inductionUnitOnly;
  BoolOptionValue _inductionGen;
  UnsignedOptionValue _maxInductionGenSubsetSize;
  BoolOptionValue _inductionOnComplexTerms;
  BoolOptionValue _integerInductionDefaultBound;
  ChoiceOptionValue<IntegerInductionInterval> _integerInductionInterval;

  StringOptionValue _latexOutput;
  BoolOptionValue _latexUseDefaultSymbols;

  ChoiceOptionValue<LiteralComparisonMode> _literalComparisonMode;
  IntOptionValue _lookaheadDelay;
  IntOptionValue _lrsFirstTimeCheck;
  BoolOptionValue _lrsWeightLimitOnly;
  ChoiceOptionValue<LTBLearning> _ltbLearning;
  StringOptionValue _ltbDirectory;

#ifdef __linux__
  UnsignedOptionValue _instructionLimit; 
#endif

  UnsignedOptionValue _memoryLimit; // should be size_t, making an assumption
  ChoiceOptionValue<Mode> _mode;
  ChoiceOptionValue<Schedule> _schedule;
  UnsignedOptionValue _multicore;
  FloatOptionValue _slowness;

  IntOptionValue _naming;
  BoolOptionValue _nonliteralsInClauseWeight;
  BoolOptionValue _normalize;

  BoolOptionValue _outputAxiomNames;

  StringOptionValue _printProofToFile;
  BoolOptionValue _printClausifierPremises;
  StringOptionValue _problemName;
  ChoiceOptionValue<Proof> _proof;
  BoolOptionValue _minimizeSatProofs;
  ChoiceOptionValue<ProofExtra> _proofExtra;
  
  StringOptionValue _protectedPrefix;

  ChoiceOptionValue<QuestionAnsweringMode> _questionAnswering;

  IntOptionValue _randomSeed;
  IntOptionValue _randomStrategySeed;

  IntOptionValue _activationLimit;

  ChoiceOptionValue<SatSolver> _satSolver;
  ChoiceOptionValue<SaturationAlgorithm> _saturationAlgorithm;
  BoolOptionValue _showAll;
  BoolOptionValue _showActive;
  BoolOptionValue _showBlocked;
  BoolOptionValue _showDefinitions;
  ChoiceOptionValue<InterpolantMode> _showInterpolant;
  BoolOptionValue _showNew;
  BoolOptionValue _sineToAge;
  ChoiceOptionValue<PredicateSineLevels> _sineToPredLevels;
  BoolOptionValue _showSplitting;
  BoolOptionValue _showNewPropositional;
  BoolOptionValue _showNonconstantSkolemFunctionTrace;
  BoolOptionValue _showOptions;
  BoolOptionValue _showOptionsLineWrap;
  BoolOptionValue _showExperimentalOptions;
  BoolOptionValue _showHelp;
  BoolOptionValue _printAllTheoryAxioms;
  StringOptionValue _explainOption;
  BoolOptionValue _showPassive;
  BoolOptionValue _showReductions;
  BoolOptionValue _showPreprocessing;
  BoolOptionValue _showSkolemisations;
  BoolOptionValue _showSymbolElimination;
  BoolOptionValue _showTheoryAxioms;
  BoolOptionValue _showFOOL;
  BoolOptionValue _showFMBsortInfo;
  BoolOptionValue _showInduction;
  BoolOptionValue _showSimplOrdering;
#if VZ3
  BoolOptionValue _showZ3;
  StringOptionValue _exportAvatarProblem;
  StringOptionValue _exportThiProblem;
  BoolOptionValue _satFallbackForSMT;
  BoolOptionValue _smtForGround;
  ChoiceOptionValue<TheoryInstSimp> _theoryInstAndSimp;
  BoolOptionValue _thiGeneralise;
  BoolOptionValue _thiTautologyDeletion;
#endif
  ChoiceOptionValue<UnificationWithAbstraction> _unificationWithAbstraction; 
  BoolOptionValue _fixUWA;
  BoolOptionValue _useACeval;
  TimeLimitOptionValue _simulatedTimeLimit;
  UnsignedOptionValue _sineDepth;
  UnsignedOptionValue _sineGeneralityThreshold;
  UnsignedOptionValue _sineToAgeGeneralityThreshold;
  ChoiceOptionValue<SineSelection> _sineSelection;
  FloatOptionValue _sineTolerance;
  FloatOptionValue _sineToAgeTolerance;
  ChoiceOptionValue<Sos> _sos;
  UnsignedOptionValue _sosTheoryLimit;
  BoolOptionValue _splitting;
  BoolOptionValue _splitAtActivation;
  ChoiceOptionValue<SplittingAddComplementary> _splittingAddComplementary;
  ChoiceOptionValue<SplittingCongruenceClosure> _splittingCongruenceClosure;
  ChoiceOptionValue<CCUnsatCores> _ccUnsatCores;
  BoolOptionValue _splittingEagerRemoval;
  UnsignedOptionValue _splittingFlushPeriod;
  FloatOptionValue _splittingFlushQuotient;
  FloatOptionValue _splittingAvatimer;
  ChoiceOptionValue<SplittingNonsplittableComponents> _splittingNonsplittableComponents;
  ChoiceOptionValue<SplittingMinimizeModel> _splittingMinimizeModel;
  ChoiceOptionValue<SplittingLiteralPolarityAdvice> _splittingLiteralPolarityAdvice;
  ChoiceOptionValue<SplittingDeleteDeactivated> _splittingDeleteDeactivated;
  BoolOptionValue _splittingFastRestart;
  BoolOptionValue _splittingBufferedSolver;

  ChoiceOptionValue<Statistics> _statistics;
  BoolOptionValue _superpositionFromVariables;
  ChoiceOptionValue<TermOrdering> _termOrdering;
  ChoiceOptionValue<SymbolPrecedence> _symbolPrecedence;
  ChoiceOptionValue<SymbolPrecedenceBoost> _symbolPrecedenceBoost;
  ChoiceOptionValue<IntroducedSymbolPrecedence> _introducedSymbolPrecedence;
  ChoiceOptionValue<EvaluationMode> _evaluationMode;
  ChoiceOptionValue<KboAdmissibilityCheck> _kboAdmissabilityCheck;
  StringOptionValue _functionWeights;
  StringOptionValue _predicateWeights;
  StringOptionValue _functionPrecedence;
  StringOptionValue _predicatePrecedence;

  StringOptionValue _testId;
  ChoiceOptionValue<Output> _outputMode;
  BoolOptionValue _ignoreMissingInputsInUnsatCore;
  StringOptionValue _thanks;
  ChoiceOptionValue<TheoryAxiomLevel> _theoryAxioms;
  BoolOptionValue _theoryFlattening;

  /** Time limit in deciseconds */
  TimeLimitOptionValue _timeLimitInDeciseconds;
  BoolOptionValue _timeStatistics;

  ChoiceOptionValue<URResolution> _unitResultingResolution;
  BoolOptionValue _unusedPredicateDefinitionRemoval;
  BoolOptionValue _blockedClauseElimination;
  // BoolOptionValue _use_dm;

  OptionChoiceValues _tagNames;

  NonGoalWeightOptionValue _nonGoalWeightCoefficient;
  BoolOptionValue _restrictNWCtoGC;

  SelectionOptionValue _selection;
  SelectionOptionValue _instGenSelection;
    
  InputFileOptionValue _inputFile;

  BoolOptionValue _newCNF;
  BoolOptionValue _inlineLet;

  BoolOptionValue _manualClauseSelection;
  // arithmeitc reasoning options
  BoolOptionValue _inequalityNormalization;
  BoolOptionValue _pushUnaryMinus;
  BoolOptionValue _highSchool;
  ChoiceOptionValue<ArithmeticSimplificationMode> _gaussianVariableElimination;
  ChoiceOptionValue<ArithmeticSimplificationMode> _cancellation;
  ChoiceOptionValue<ArithmeticSimplificationMode> _arithmeticSubtermGeneralizations;

 
  //Higher-order options
  BoolOptionValue _addCombAxioms;
  BoolOptionValue _addProxyAxioms;
  BoolOptionValue _combinatorySuperposition;
  BoolOptionValue _choiceAxiom;
  BoolOptionValue _injectivity;
  BoolOptionValue _pragmatic;
  BoolOptionValue _choiceReasoning;
  BoolOptionValue _priortyToLongReducts;
  IntOptionValue  _maximumXXNarrows;
  ChoiceOptionValue<FunctionExtensionality> _functionExtensionality;
  ChoiceOptionValue<CNFOnTheFly> _clausificationOnTheFly;
  ChoiceOptionValue<PISet> _piSet;
  ChoiceOptionValue<Narrow> _narrow;
  BoolOptionValue _equalityToEquivalence;
  BoolOptionValue _complexBooleanReasoning;
  BoolOptionValue _booleanEqTrick;
  BoolOptionValue _superposition;
  BoolOptionValue _casesSimp;
  BoolOptionValue _cases;
  BoolOptionValue _newTautologyDel;
  BoolOptionValue _lambdaFreeHol;

}; // class Options

// Allow printing of enums
template<typename T,
         typename = typename std::enable_if<std::is_enum<T>::value>::type>
std::ostream& operator<< (std::ostream& str,const T& val)
{
  return str << static_cast<typename std::underlying_type<T>::type>(val);
}

}

#endif
