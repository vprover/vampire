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
    AGE_WEIGHT_RATIO = 0,

    BACKWARD_DEMODULATION = 1,
    BACKWARD_SUBSUMPTION = 2,

    /** Decode test id */
    DECODE = 3,

    EQUALITY_PROXY = 4,
    EQUALITY_RESOLUTION_WITH_DELETION = 5,

    FORWARD_DEMODULATION = 6,
    FORWARD_SUBSUMPTION = 7,
    FORWARD_SUBSUMPTION_RESOLUTION = 8,
    FUNCTION_DEFINITION_ELIMINATION = 9,

    INCLUDE = 10,
    INEQUALITY_SPLITTING = 11,

    LATEX_OUTPUT = 12,
    LITERAL_COMPARISON_MODE = 13,
    LOG_FILE = 14,
    LRS_FIRST_TIME_CHECK = 15,

    MAX_ACTIVE = 16,
    MAX_ANSWERS = 17,
    MAX_INFERENCE_DEPTH = 18,
    MAX_PASSIVE = 19,
    MAX_WEIGHT = 20,
    MEMORY_LIMIT = 21,
    MODE = 22,

    NAMING = 23,
    NONGOAL_WEIGHT_COEFFICIENT = 24,
    NORMALIZE = 25,

    ORPHAN_DELETION = 26,
    OUTPUT_MESSAGES = 27,

    PROBLEM_NAME = 28,
    PROOF = 29,
    PROOF_CHECKING = 30,

    RANDOM_SEED = 31,
    ROW_VARIABLE_MAX_LENGTH = 32,

    /** saturation algorithm: lrs, otter, or discount */
    SATURATION_ALGORITHM = 33,
    SELECTION = 34,
    SHOW_ACTIVE = 35,
    SHOW_NEW = 36,
    SHOW_OPTIONS = 37,
    SHOW_PASSIVE = 38,
    SIMULATED_TIME_LIMIT = 39,
    SOS = 40,
    SPLITTING = 41,
    STATISTICS = 42,
    SUPERPOSITION_FROM_VARIABLES = 43,
    SYMBOL_PRECEDENCE = 44,

    TEST_ID = 45,
    TIME_LIMIT = 46,

    UNUSED_PREDICATE_DEFINITION_REMOVAL = 47,

    WEIGHT_INCREMENT = 48,

    XML_OUTPUT = 49,

    NUMBER_OF_OPTIONS = 50 // must be the last one!
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
   * Possible values for mode_name.
   * @since 06/05/2007 Manchester
   */
  enum Mode {
    MODE_CASC = 0,
    MODE_OUTPUT = 1,
    MODE_PROFILE = 2,
    MODE_RULE = 3,
    MODE_SPIDER = 4,
    MODE_VAMPIRE = 5
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
  enum Splitting {
    SPLIT_INPUT_ONLY = 0,
    SPLIT_OFF = 1,
    SPLIT_ON = 2
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
    /** experimental */
    EP_EXP1 = 0,
    /** --equality_proxy=off */
    EP_OFF = 1,
    /** --equality_proxy=on */
    EP_ON = 2
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
  bool showNew() const { return _showNew; }
  bool showOptions() const { return _showOptions; }
  bool showPassive() const { return _showPassive; }
  bool unusedPredicateDefinitionRemoval() const { return _unusedPredicateDefinitionRemoval; }
  void setUnusedPredicateDefinitionRemoval(bool newVal) { _unusedPredicateDefinitionRemoval = newVal; }
  bool weightIncrement() const { return _weightIncrement; }
  SaturationAlgorithm saturationAlgorithm() const { return _saturationAlgorithm; }
  Splitting splitting() const { return _splitting; }
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
  bool equalityResolutionWithDeletion() const { return _equalityResolutionWithDeletion; }
  float nongoalWeightCoefficient() const { return _nongoalWeightCoefficient; }
  bool setNongoalWeightCoefficient(float newVal);
  bool sos() const { return _sos; }
  void setSos(bool newVal) { _sos = newVal; }
  FunctionDefinitionElimination functionDefinitionElimination() const { return _functionDefinitionElimination; }
  string xmlOutput() const { return _xmlOutput; }

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

  EqualityProxy _equalityProxy;
  bool _equalityResolutionWithDeletion;

  Demodulation _forwardDemodulation;
  bool _forwardSubsumption;
  bool _forwardSubsumptionResolution;
  FunctionDefinitionElimination _functionDefinitionElimination;

  string _include;
  int _inequalitySplitting;
  string _inputFile;

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

  SaturationAlgorithm _saturationAlgorithm;
  int _selection;
  bool _showActive;
  bool _showNew;
  bool _showOptions;
  bool _showPassive;
  int _simulatedTimeLimit;
  bool _sos;
  Splitting _splitting;
  Statistics _statistics;
  bool _superpositionFromVariables;
  SymbolPrecedence _symbolPrecedence;

  string _testId;
  /** Time limit in deciseconds */
  int _timeLimitInDeciseconds;

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

