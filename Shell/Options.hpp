/**
 * @file Options.hpp
 * Defines Vampire options.
 */

#ifndef __Options__
#define __Options__

#include "../Debug/Assertion.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/XML.hpp"

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

    BACKWARD_DEMODULATION,
    BACKWARD_SUBSUMPTION,

    CONDENSATION,

    /** Decode test id */
    DECODE,

    EMPTY_CLAUSE_SUBSUMPTION,
    EQUALITY_PROXY,
    EQUALITY_RESOLUTION_WITH_DELETION,

    FORWARD_DEMODULATION,
    FORWARD_SUBSUMPTION,
    FORWARD_SUBSUMPTION_RESOLUTION,
    FUNCTION_DEFINITION_ELIMINATION,

    GENERAL_SPLITTING,

    INCLUDE,
    INEQUALITY_SPLITTING,
    INPUT_SYNTAX,

    LATEX_OUTPUT,
    LITERAL_COMPARISON_MODE,
    LOG_FILE,
    LRS_FIRST_TIME_CHECK,

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
    NORMALIZE,

    ORPHAN_DELETION,
    OUTPUT_MESSAGES,

    PROBLEM_NAME,
    PROOF,
    PROOF_CHECKING,

    RANDOM_SEED,
    ROW_VARIABLE_MAX_LENGTH,

    SAT_SOLVER_FOR_EMPTY_CLAUSE,
    /** saturation algorithm: lrs, otter, or discount */
    SATURATION_ALGORITHM,
    SELECTION,
    SHOW_ACTIVE,
    SHOW_DEFINITIONS,
    SHOW_NEW,
    SHOW_NEW_PROPOSITIONAL,
    SHOW_OPTIONS,
    SHOW_PASSIVE,
    SIMULATED_TIME_LIMIT,
    SOS,
    SPLITTING,
    STATISTICS,
    SUPERPOSITION_FROM_VARIABLES,
    SYMBOL_PRECEDENCE,

    TEST_ID,
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
    MODE_CASC,
    MODE_GROUNDING,
    MODE_OUTPUT,
    MODE_PROFILE,
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

  /** Possible values for splitting */
  enum RuleActivity {
    RA_INPUT_ONLY = 0,
    RA_OFF = 1,
    RA_ON = 2
  };

  enum LiteralComparisonMode {
    LCM_REVERSE = 0,
    LCM_PREDICATE = 1,
//     LCM_REVERSE = 1,
    LCM_STANDARD = 2
  };

  enum Demodulation {
    DEMODULATION_ALL = 0,
    DEMODULATION_OFF = 1,
    DEMODULATION_PREORDERED = 2
  };

  enum SymbolPrecedence {
    BY_ARITY = 0,
    BY_OCCURRENCE = 1,
    BY_REVERSE_ARITY = 2
  };

  enum Proof {
    PROOF_OFF = 0,
    PROOF_ON = 1,
    PROOF_SUCCINCT = 2
  };

  /** Values for --equality_proxy */
  enum EqualityProxy {
    EP_R = 0,
    EP_RS = 1,
    EP_RST = 2,
    /** experimental */
    EP_EXP1 = 3,
    /** --equality_proxy=off */
    EP_OFF = 4,
    /** --equality_proxy=on */
    EP_ON = 5
  };

public:
  Options ();
  void output (ostream&) const;
  void readFromTestId (string testId);
  bool complete() const;

  string problemName () const;

  string testId() const { return _testId; }
  Statistics statistics() const { return _statistics; }
  Proof proof() const { return _proof; }
  bool proofChecking() const { return _proofChecking; }
  int naming() const { return _naming; }
  bool setNaming(int newVal);
  Mode mode() const { return _mode; }
  void setMode(Mode newVal) { _mode = newVal; }
  InputSyntax inputSyntax() { return _inputSyntax; }
  void setInputSyntax(InputSyntax newVal) { _inputSyntax = newVal; }
  bool normalize() const { return _normalize; }
  string include() const { return _include; }
  string includeFileName (const string& relativeName);
  string logFile() const { return _logFile; }
  string inputFile() const { return _inputFile; }
  int randomSeed() const { return _randomSeed; }
  int rowVariableMaxLength() const { return _rowVariableMaxLength; }
  void setRowVariableMaxLength(int newVal) { _rowVariableMaxLength = newVal; }
  bool outputMessages() const { return _outputMessages; }
  void setOutputMessages(bool newVal) { _outputMessages = newVal; }
  bool showActive() const { return _showActive; }
  bool showDefinitions() const { return _showDefinitions; }
  bool showNew() const { return _showNew; }
  bool showNewPropositional() const { return _showNewPropositional; }
  bool showOptions() const { return _showOptions; }
  bool showPassive() const { return _showPassive; }
  bool unusedPredicateDefinitionRemoval() const { return _unusedPredicateDefinitionRemoval; }
  void setUnusedPredicateDefinitionRemoval(bool newVal) { _unusedPredicateDefinitionRemoval = newVal; }
  bool weightIncrement() const { return _weightIncrement; }
  SaturationAlgorithm saturationAlgorithm() const { return _saturationAlgorithm; }
  RuleActivity splitting() const { return _splitting; }
  int selection() const { return _selection; }
  bool setSelection(int newValue);
  string latexOutput() const { return _latexOutput; }
  LiteralComparisonMode literalComparisonMode() const { return _literalComparisonMode; }
  bool forwardSubsumptionResolution() const { return _forwardSubsumptionResolution; }
  void setForwardSubsumptionResolution(bool newVal) { _forwardSubsumptionResolution = newVal; }
  Demodulation forwardDemodulation() const { return _forwardDemodulation; }
  Demodulation backwardDemodulation() const { return _backwardDemodulation; }
  void setBackwardDemodulation(Demodulation newVal) { _backwardDemodulation = newVal; }
  bool backwardSubsumption() const { return _backwardSubsumption; }
  void setBackwardSubsumption(bool newVal) { _backwardSubsumption = newVal; }
  bool forwardSubsumption() const { return _forwardSubsumption; }
  bool orphanDeletion() const { return _orphanDeletion; }
  int lrsFirstTimeCheck() const { return _lrsFirstTimeCheck; }
  bool setLrsFirstTimeCheck(int newVal);
  int simulatedTimeLimit() const { return _simulatedTimeLimit; }
  void setSimulatedTimeLimit(int newVal) { _simulatedTimeLimit = newVal; }
  int maxInferenceDepth() const { return _maxInferenceDepth; }
  SymbolPrecedence symbolPrecedence() const { return _symbolPrecedence; }
  int timeLimitInDeciseconds() const { return _timeLimitInDeciseconds; }
  static int readTimeLimit(const char* val);
  int memoryLimit() const { return _memoryLimit; }
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
  string xmlOutput() const { return _xmlOutput; }

  bool condensation() const { return _condensation; }
  RuleActivity generalSplitting() const { return _generalSplitting; }
  string namePrefix() const { return _namePrefix; }
  bool timeStatistics() const { return _timeStatistics; }
  bool satSolverForEmptyClause() const { return _satSolverForEmptyClause; }
  bool emptyClauseSubsumption() const { return _emptyClauseSubsumption; }

  void setMemoryLimit(int newVal) { _memoryLimit = newVal; }
  void setInputFile(const string& newVal) { _inputFile = newVal; }
  void setTimeLimitInSeconds(int newVal) { _timeLimitInDeciseconds = 10*newVal; }
  void setTimeLimitInDeciseconds(int newVal) { _timeLimitInDeciseconds = newVal; }

//   // standard ways of creating options
  XMLElement toXML() const;
  bool outputSuppressed() const;
  void set(const string& name, const string& value);
  void set(const char* name, const char* value);
  void setShort(const char* name, const char* value);


  void checkGlobalOptionConstraints() const;

  CLASS_NAME("Options");
  USE_ALLOCATOR(Options);

private:
  void set(const char* name, const char* value, int index);

private:
  class Constants;

  int _ageRatio;
  int _weightRatio;

  Demodulation _backwardDemodulation;
  bool _backwardSubsumption;

  bool _condensation;

  bool _emptyClauseSubsumption;
  EqualityProxy _equalityProxy;
  RuleActivity _equalityResolutionWithDeletion;

  Demodulation _forwardDemodulation;
  bool _forwardSubsumption;
  bool _forwardSubsumptionResolution;
  FunctionDefinitionElimination _functionDefinitionElimination;

  RuleActivity _generalSplitting;

  string _include;
  int _inequalitySplitting;
  string _inputFile;
  InputSyntax _inputSyntax;

  string _latexOutput;
  LiteralComparisonMode _literalComparisonMode;
  string _logFile;
  int _lrsFirstTimeCheck;

  long _maxActive;
  int _maxAnswers;
  int _maxInferenceDepth;
  long _maxPassive;
  int _maxWeight;
  int _memoryLimit;
  Mode _mode;

  string _namePrefix;
  int _naming;
  float _nongoalWeightCoefficient;
  bool _normalize;

  bool _orphanDeletion;
  bool _outputMessages;

  string _problemName;
  Proof _proof;
  bool _proofChecking;

  int _randomSeed;
  int _rowVariableMaxLength;

  bool _satSolverForEmptyClause;
  SaturationAlgorithm _saturationAlgorithm;
  int _selection;
  bool _showActive;
  bool _showDefinitions;
  bool _showNew;
  bool _showNewPropositional;
  bool _showOptions;
  bool _showPassive;
  int _simulatedTimeLimit;
  bool _sos;
  RuleActivity _splitting;
  Statistics _statistics;
  bool _superpositionFromVariables;
  SymbolPrecedence _symbolPrecedence;

  string _testId;
  /** Time limit in deciseconds */
  int _timeLimitInDeciseconds;
  bool _timeStatistics;

  bool _unusedPredicateDefinitionRemoval;

  bool _weightIncrement;

  string _xmlOutput;

  // various read-from-string-write options
  void readAgeWeightRatio(const char* val);
  static string boolToOnOff(bool);
  void outputValue(ostream& str,int optionTag) const;

public:
  // the following two functions are used by Environment
  static bool onOffToBool(const char* onOff,const char* option);
}; // class Options

}

#endif

