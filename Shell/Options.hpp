/**
 * @file Options.hpp
 * Defines Vampire options.
 */

#ifndef __Options__
#define __Options__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/XML.hpp"

using namespace Lib;

namespace Shell {

/**
 * Class that represents Vampire's options.
 * 11/11/2004 Shrigley Hall, completely reimplemented
 */
class Options
{
public:
  enum Tag {
    AGE_WEIGHT_RATIO,
    ARITY_CHECK,

    BACKWARD_DEMODULATION,
    BACKWARD_SUBSUMPTION,
    BACKWARD_SUBSUMPTION_RESOLUTION,
    BDD_MARKING_SUBSUMPTION,

    COLOR_UNBLOCKING,
    CONDENSATION,

    /** Decode test id */
    DECODE,
    DEMODULATION_REDUNDANCY_CHECK,

    EMPTY_CLAUSE_SUBSUMPTION,
    EPR_PRESERVING_NAMING,
    EQUALITY_PROXY,
    EQUALITY_RESOLUTION_WITH_DELETION,

    FORCED_OPTIONS,
    FORWARD_DEMODULATION,
    FORWARD_LITERAL_REWRITING,
    FORWARD_SUBSUMPTION,
    FORWARD_SUBSUMPTION_RESOLUTION,
    FUNCTION_DEFINITION_ELIMINATION,

    GENERAL_SPLITTING,

    INCLUDE,
    INCREASED_NUMERAL_WEIGHT,
    INEQUALITY_SPLITTING,
    INPUT_FILE,
    INPUT_SYNTAX,
    INTERPRETED_EVALUATION,
    INTERPRETED_SIMPLIFICATION,

    LATEX_OUTPUT,
    LITERAL_COMPARISON_MODE,
    LOG_FILE,
    LRS_FIRST_TIME_CHECK,
    LRS_WEIGHT_LIMIT_ONLY,

    MAX_ACTIVE,
    MAX_ANSWERS,
    MAX_INFERENCE_DEPTH,
    MAX_PASSIVE,
    MAX_WEIGHT,
    MEMORY_LIMIT,
    MODE,

    NAME_PREFIX,
    NAMING,
    NONGOAL_WEIGHT_COEFFICIENT,
    NONLITERALS_IN_CLAUSE_WEIGHT,
    NORMALIZE,

    OUTPUT_AXIOM_NAMES,

    PROBLEM_NAME,
    PROOF,
    PROOF_CHECKING,
    PROPOSITIONAL_TO_BDD,

    RANDOM_SEED,
    ROW_VARIABLE_MAX_LENGTH,

    SAT_SOLVER_FOR_EMPTY_CLAUSE,
    SAT_SOLVER_WITH_NAMING,
    SAT_SOLVER_WITH_SUBSUMPTION_RESOLUTION,
    /** saturation algorithm: lrs, otter, or discount */
    SATURATION_ALGORITHM,
    SELECTION,
    SHOW_ACTIVE,
    SHOW_BLOCKED,
    SHOW_DEFINITIONS,
    SHOW_INTERPOLANT,
    SHOW_NEW,
    SHOW_NEW_PROPOSITIONAL,
    SHOW_OPTIONS,
    SHOW_PASSIVE,
    SHOW_SKOLEMISATIONS,
    SHOW_SYMBOL_ELIMINATION,
    SIMULATED_TIME_LIMIT,
    SINE_DEPTH,
    SINE_GENERALITY_THRESHOLD,
    SINE_SELECTION,
    SINE_TOLERANCE,
    SOS,
    SPLIT_ADD_GROUND_NEGATION,
    SPLIT_AT_ACTIVATION,
    SPLIT_GOAL_ONLY,
    SPLIT_INPUT_ONLY,
    SPLIT_POSITIVE,
    SPLITTING,
    SPLITTING_WITH_BLOCKING,
    STATISTICS,
    SUPERPOSITION_FROM_VARIABLES,
    SYMBOL_PRECEDENCE,

    TEST_ID,
    THANKS,
    THEORY_AXIOMS,
    TIME_LIMIT,
    TIME_STATISTICS,

    UNUSED_PREDICATE_DEFINITION_REMOVAL,

    WEIGHT_INCREMENT,

    XML_OUTPUT,

    NUMBER_OF_OPTIONS // must be the last one!
  };

public:
  class StringInt;
  class StringIntMap;

  /**
   * Possible values for function_definition_elimination.
   * @since 29/05/2004 Manchester
   */
  enum FunctionDefinitionElimination {
    FDE_ALL = 0,
    FDE_NONE = 1,
    FDE_UNUSED = 2
  };

  /**
   * Possible values for the input syntax
   * @since 26/08/2009 Redmond
   */
  enum InputSyntax {
    /** syntax of the Simplify prover */
    IS_SIMPLIFY = 0,
    /** syntax of the TPTP prover */
    IS_TPTP = 1
  };

  /**
   * Possible values for mode_name.
   * @since 06/05/2007 Manchester
   */
  enum Mode {
    MODE_AXIOM_SELECTION,
    MODE_CASC,
    MODE_CASC_LTB,
    MODE_CASC_SIMPLE_LTB,
    MODE_CLAUSIFY,
    MODE_CONSEQUENCE_ELIMINATION,
    MODE_GROUNDING,
    MODE_INST_GEN,
    MODE_LTB_BUILD,
    MODE_LTB_SOLVE,
    MODE_PROFILE,
    MODE_PROGRAM_ANALYSIS,
    MODE_RULE,
    MODE_SPIDER,
    MODE_VAMPIRE
  };

  /** Various options for the output of statistics in Vampire */
  enum Statistics {
    /** changed by the option "--statistics brief" */
    STATISTICS_BRIEF = 0,
    /** changed by the option "--statistics full */
    STATISTICS_FULL = 1,
    /** changed by the option "--statistics off" */
    STATISTICS_NONE = 2
  };

  /** Possible values for saturation_algorithm */
  enum SaturationAlgorithm {
     DISCOUNT = 0,
     LRS = 1,
     OTTER = 2
   };

  /** Possible values for activity of some inference rules */
  enum RuleActivity {
    RA_INPUT_ONLY = 0,
    RA_OFF = 1,
    RA_ON = 2
  };

  /** Possible values for splitting */
  enum SplittingMode {
    SM_BACKTRACKING = 0,
    SM_NOBACKTRACKING = 1,
    SM_OFF = 2
  };

  enum LiteralComparisonMode {
    LCM_PREDICATE = 0,
    LCM_REVERSE = 1,
    LCM_STANDARD = 2
  };

  enum Condensation {
    CONDENSATION_FAST = 0,
    CONDENSATION_OFF = 1,
    CONDENSATION_ON = 2
  };

  enum Demodulation {
    DEMODULATION_ALL = 0,
    DEMODULATION_OFF = 1,
    DEMODULATION_PREORDERED = 2
  };

  enum Subsumption {
    SUBSUMPTION_OFF = 0,
    SUBSUMPTION_ON = 1,
    SUBSUMPTION_UNIT_ONLY = 2
  };

  enum SymbolPrecedence {
    BY_ARITY = 0,
    BY_OCCURRENCE = 1,
    BY_REVERSE_ARITY = 2
  };

  enum SineSelection {
    SS_AXIOMS = 0,
    SS_INCLUDED = 1,
    SS_OFF = 2
  };

  enum Proof {
    PROOF_OFF = 0,
    PROOF_ON = 1,
    PROOF_PROOFCHECK = 2,
    PROOF_TPTP = 3
  };

  /** Values for --equality_proxy */
  enum EqualityProxy {
    EP_R = 0,
    EP_RS = 1,
    EP_RST = 2,
    EP_RSTC = 3,
    /** --equality_proxy=off */
    EP_OFF = 4,
    /** --equality_proxy=on */
    EP_ON = 5
  };

public:
  Options ();
  void output (ostream&) const;
  void readFromTestId (string testId);
  void readOptionsString (string testId);
  string generateTestId() const;
  bool complete() const;
  void setForcedOptionValues();
  void checkGlobalOptionConstraints() const;

  void forceIncompleteness() { _forceIncompleteness=true; }

  string problemName () const;

  string forcedOptions() const { return _forcedOptions; }
  string testId() const { return _testId; }
  Statistics statistics() const { return _statistics; }
  Proof proof() const { return _proof; }
  bool proofChecking() const { return _proofChecking; }
  int naming() const { return _naming; }
  bool setNaming(int newVal);
  bool eprPreservingNaming() const { return _eprPreservingNaming; }
  void setEprPreservingNaming(bool newVal) { _eprPreservingNaming = newVal; }
  Mode mode() const { return _mode; }
  void setMode(Mode newVal) { _mode = newVal; }
  InputSyntax inputSyntax() { return _inputSyntax; }
  void setInputSyntax(InputSyntax newVal) { _inputSyntax = newVal; }
  bool normalize() const { return _normalize; }
  void setNormalize(bool normalize) { _normalize = normalize; }
  string include() const { return _include; }
  void setInclude(string val) { _include = val; }
  string includeFileName (const string& relativeName);
  string logFile() const { return _logFile; }
  string inputFile() const { return _inputFile; }
  int randomSeed() const { return _randomSeed; }
  int rowVariableMaxLength() const { return _rowVariableMaxLength; }
  void setRowVariableMaxLength(int newVal) { _rowVariableMaxLength = newVal; }
  bool showActive() const { return _showActive; }
  bool showBlocked() const { return _showBlocked; }
  bool showDefinitions() const { return _showDefinitions; }
  bool showInterpolant() const { return _showInterpolant; }
  bool showNew() const { return _showNew; }
  bool showNewPropositional() const { return _showNewPropositional; }
  bool showOptions() const { return _showOptions; }
  bool showPassive() const { return _showPassive; }
  bool showSkolemisations() const { return _showSkolemisations; }
  bool showSymbolElimination() const { return _showSymbolElimination; }
  bool unusedPredicateDefinitionRemoval() const { return _unusedPredicateDefinitionRemoval; }
  void setUnusedPredicateDefinitionRemoval(bool newVal) { _unusedPredicateDefinitionRemoval = newVal; }
  bool weightIncrement() const { return _weightIncrement; }
  SaturationAlgorithm saturationAlgorithm() const { return _saturationAlgorithm; }
  int selection() const { return _selection; }
  bool setSelection(int newValue);
  string latexOutput() const { return _latexOutput; }
  LiteralComparisonMode literalComparisonMode() const { return _literalComparisonMode; }
  bool forwardSubsumptionResolution() const { return _forwardSubsumptionResolution; }
  void setForwardSubsumptionResolution(bool newVal) { _forwardSubsumptionResolution = newVal; }
  Demodulation forwardDemodulation() const { return _forwardDemodulation; }
  bool arityCheck() const { return _arityCheck; }
  void setArityCheck(bool newVal) { _arityCheck=newVal; }
  Demodulation backwardDemodulation() const { return _backwardDemodulation; }
  bool demodulationRedundancyCheck() const { return _demodulationRedundancyCheck; }
  void setBackwardDemodulation(Demodulation newVal) { _backwardDemodulation = newVal; }
  Subsumption backwardSubsumption() const { return _backwardSubsumption; }
  void setBackwardSubsumption(Subsumption newVal) { _backwardSubsumption = newVal; }
  Subsumption backwardSubsumptionResolution() const { return _backwardSubsumptionResolution; }
  bool forwardSubsumption() const { return _forwardSubsumption; }
  bool forwardLiteralRewriting() const { return _forwardLiteralRewriting; }
  int lrsFirstTimeCheck() const { return _lrsFirstTimeCheck; }
  int lrsWeightLimitOnly() const { return _lrsWeightLimitOnly; }
  bool setLrsFirstTimeCheck(int newVal);
  int simulatedTimeLimit() const { return _simulatedTimeLimit; }
  void setSimulatedTimeLimit(int newVal) { _simulatedTimeLimit = newVal; }
  int maxInferenceDepth() const { return _maxInferenceDepth; }
  SymbolPrecedence symbolPrecedence() const { return _symbolPrecedence; }
  /**
   * Return time limit in deciseconds, or 0 if there is no time limit
   */
  int timeLimitInDeciseconds() const { return _timeLimitInDeciseconds; }
  static int readTimeLimit(const char* val);
  size_t memoryLimit() const { return _memoryLimit; }
  int inequalitySplitting() const { return _inequalitySplitting; }
  long maxActive() const { return _maxActive; }
  long maxAnswers() const { return _maxAnswers; }
  void setMaxAnswers(int newVal) { _maxAnswers = newVal; }
  long maxPassive() const { return _maxPassive; }
  int maxWeight() const { return _maxWeight; }
  int ageRatio() const { return _ageRatio; }
  int weightRatio() const { return _weightRatio; }
  bool superpositionFromVariables() const { return _superpositionFromVariables; }
  EqualityProxy equalityProxy() const { return _equalityProxy; }
  RuleActivity equalityResolutionWithDeletion() const { return _equalityResolutionWithDeletion; }
  float nongoalWeightCoefficient() const { return _nongoalWeightCoefficient; }
  bool setNongoalWeightCoefficient(float newVal);
  bool sos() const { return _sos; }
  void setSos(bool newVal) { _sos = newVal; }
  FunctionDefinitionElimination functionDefinitionElimination() const { return _functionDefinitionElimination; }
  bool outputAxiomNames() const { return _outputAxiomNames; }
  void setOutputAxiomNames(bool newVal) { _outputAxiomNames = newVal; }
  string xmlOutput() const { return _xmlOutput; }
  string thanks() const { return _thanks; }

  bool increasedNumeralWeight() const { return _increasedNumeralWeight; }
  bool interpretedEvaluation() const { return _interpretedEvaluation; }
  bool interpretedSimplification() const { return _interpretedSimplification; }
  void setInterpretedEvaluation(bool val) { _interpretedEvaluation = val; }
  bool theoryAxioms() const { return _theoryAxioms; }
  void setTheoryAxioms(bool val) { _theoryAxioms = val; }
  Condensation condensation() const { return _condensation; }
  RuleActivity generalSplitting() const { return _generalSplitting; }
  string namePrefix() const { return _namePrefix; }
  bool timeStatistics() const { return _timeStatistics; }
  bool satSolverForEmptyClause() const { return _satSolverForEmptyClause; }
  bool satSolverWithNaming() const { return _satSolverWithNaming; }
  bool satSolverWithSubsumptionResolution() const { return _satSolverWithSubsumptionResolution; }
  bool emptyClauseSubsumption() const { return _emptyClauseSubsumption; }
  bool propositionalToBDD() const { return _propositionalToBDD; }
  void setPropositionalToBDD(bool value) { _propositionalToBDD = value; }
  bool splitAddGroundNegation() const { return _splitAddGroundNegation; }
  bool splitAtActivation() const { return _splitAtActivation; }
  bool splitGoalOnly() const { return _splitGoalOnly; }
  bool splitInputOnly() const { return _splitInputOnly; }
  bool splitPositive() const { return _splitPositive; }
  SplittingMode splitting() const { return _splitting; }
  bool splittingWithBlocking() const { return _splittingWithBlocking; }
  bool bddMarkingSubsumption() const { return _bddMarkingSubsumption; }
  bool nonliteralsInClauseWeight() const { return _nonliteralsInClauseWeight; }
  unsigned sineDepth() const { return _sineDepth; }
  unsigned sineGeneralityThreshold() const { return _sineGeneralityThreshold; }
  SineSelection sineSelection() const { return _sineSelection; }
  void setSineSelection(SineSelection val) { _sineSelection=val; }
  float sineTolerance() const { return _sineTolerance; }

  bool colorUnblocking() const { return _colorUnblocking; }

  void setMemoryLimit(size_t newVal) { _memoryLimit = newVal; }
  void setInputFile(const string& newVal);
  void setTimeLimitInSeconds(int newVal) { _timeLimitInDeciseconds = 10*newVal; }
  void setTimeLimitInDeciseconds(int newVal) { _timeLimitInDeciseconds = newVal; }

//   // standard ways of creating options
  XMLElement toXML() const;
  bool outputSuppressed() const;
  void set(const string& name, const string& value);
  void set(const char* name, const char* value);
  void setShort(const char* name, const char* value);


  CLASS_NAME("Options");
  USE_ALLOCATOR(Options);

private:
  void set(const char* name, const char* value, int index);

private:
  class Constants;

  int _ageRatio;
  int _weightRatio;
  bool _arityCheck;

  Demodulation _backwardDemodulation;
  Subsumption _backwardSubsumption;
  Subsumption _backwardSubsumptionResolution;
  bool _bddMarkingSubsumption;

  bool _colorUnblocking;
  Condensation _condensation;

  bool _demodulationRedundancyCheck;

  bool _emptyClauseSubsumption;
  bool _eprPreservingNaming;
  EqualityProxy _equalityProxy;
  RuleActivity _equalityResolutionWithDeletion;

  string _forcedOptions;
  Demodulation _forwardDemodulation;
  bool _forwardLiteralRewriting;
  bool _forwardSubsumption;
  bool _forwardSubsumptionResolution;
  FunctionDefinitionElimination _functionDefinitionElimination;

  RuleActivity _generalSplitting;

  string _include;
  /** if this option is true, Vampire will add the numeral weight of a clause
   * to its weight. The weight is defined as the sum of binary sizes of all
   * integers occurring in this clause. This option has not been tested and
   * may be extensive, see Clause::getNumeralWeight()
   */
  bool _increasedNumeralWeight;
  int _inequalitySplitting;
  string _inputFile;
  InputSyntax _inputSyntax;
  bool _interpretedEvaluation;
  bool _interpretedSimplification;

  string _latexOutput;
  LiteralComparisonMode _literalComparisonMode;
  string _logFile;
  int _lrsFirstTimeCheck;
  int _lrsWeightLimitOnly;

  long _maxActive;
  int _maxAnswers;
  int _maxInferenceDepth;
  long _maxPassive;
  int _maxWeight;
  size_t _memoryLimit;
  Mode _mode;

  string _namePrefix;
  int _naming;
  float _nongoalWeightCoefficient;
  bool _nonliteralsInClauseWeight;
  bool _normalize;

  bool _outputAxiomNames;

  string _problemName;
  Proof _proof;
  bool _proofChecking;
  bool _propositionalToBDD;

  int _randomSeed;
  int _rowVariableMaxLength;

  bool _satSolverForEmptyClause;
  bool _satSolverWithNaming;
  bool _satSolverWithSubsumptionResolution;
  SaturationAlgorithm _saturationAlgorithm;
  int _selection;
  bool _showActive;
  bool _showBlocked;
  bool _showDefinitions;
  bool _showInterpolant;
  bool _showNew;
  bool _showNewPropositional;
  bool _showOptions;
  bool _showPassive;
  bool _showSkolemisations;
  bool _showSymbolElimination;
  int _simulatedTimeLimit;
  unsigned _sineDepth;
  unsigned _sineGeneralityThreshold;
  SineSelection _sineSelection;
  float _sineTolerance;
  bool _sos;
  bool _splitAddGroundNegation;
  bool _splitAtActivation;
  bool _splitGoalOnly;
  bool _splitInputOnly;
  bool _splitPositive;
  SplittingMode _splitting;
  bool _splittingWithBlocking;
  Statistics _statistics;
  bool _superpositionFromVariables;
  SymbolPrecedence _symbolPrecedence;

  string _testId;
  string _thanks;
  bool _theoryAxioms;
  /** Time limit in deciseconds */
  int _timeLimitInDeciseconds;
  bool _timeStatistics;

  bool _unusedPredicateDefinitionRemoval;

  bool _weightIncrement;

  string _xmlOutput;


  bool _forceIncompleteness;

  // various read-from-string-write options
  void readAgeWeightRatio(const char* val);
  static string boolToOnOff(bool);
  void outputValue(ostream& str,int optionTag) const;

  friend class Shell::LTB::Builder;

public:
  // the following two functions are used by Environment
  static bool onOffToBool(const char* onOff,const char* option);
}; // class Options

}

#endif

