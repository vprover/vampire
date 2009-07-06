/**
 * @file Options.cpp
 * Implements Vampire options.
 *
 * @since 06/06/2001 Manchester, completely rewritten
 */

// Visual does not know the round function
#include <cmath>
#include <sstream>
#include <cstring>

#include "../Debug/Tracer.hpp"
#include "../Debug/Assertion.hpp"

#include "../Lib/Int.hpp"
#include "../Lib/NameArray.hpp"
#include "../Lib/Random.hpp"
#include "../Lib/Exception.hpp"

#include "Options.hpp"

using namespace Lib;

namespace Shell {

/**
 * Class to hide various data used by class Options, mostly name arrays.
 * @since 21/04/2005 Manchester
 */
class Options::Constants {
public:
  static const char* _optionNames[];
  static const char* _shortNames[];
  static const char* _statisticsValues[];
  static const char* _demodulationValues[];
  static const char* _fdeValues[];
  static const char* _lcmValues[];
  static const char* _satAlgValues[];
  static const char* _equalityProxyValues[];
  static const char* _modeValues[];
  static const char* _splittingValues[];
  static const char* _symbolPrecedenceValues[];
  static const char* _tcValues[];
  static const char* _proofValues[];

  static int shortNameIndexes[];

  static NameArray optionNames;
  static NameArray shortNames;
  static NameArray statisticsValues;
  static NameArray demodulationValues;
  static NameArray fdeValues;
  static NameArray lcmValues;
  static NameArray satAlgValues;
  static NameArray equalityProxyValues;
  static NameArray modeValues;
  static NameArray splittingValues;
  static NameArray symbolPrecedenceValues;
  static NameArray tcValues;
  static NameArray proofValues;
}; // class Options::Constants


/** Names for all options */
const char* Options::Constants::_optionNames[] = {
  "age_weight_ratio",

  "backward_demodulation",
  "backward_subsumption",

  "condensation",

  "decode",

  "equality_proxy",
  "equality_resolution_with_deletion",

  "forward_demodulation",
  "forward_subsumption",
  "forward_subsumption_resolution",
  "function_definition_elimination",

  "include",
  "inequality_splitting",

  "latex_output",
  "literal_comparison_mode",
  "log_file",
  "lrs_first_time_check",

  "max_active",
  "max_answers",
  "max_inference_depth",
  "max_passive",
  "max_weight",
  "memory_limit",
  "mode",

  "naming",
  "nongoal_weight_coefficient",
  "normalize",

  "orphan_deletion",
  "output_messages",

  "problem_name",
  "proof",
  "proof_checking",

  "random_seed",
  "row_variable_max_length",

  "saturation_algorithm",
  "selection",
  "show_active",
  "show_new",
  "show_options",
  "show_passive",
  "simulated_time_limit",
  "sos",
  "splitting",
  "statistics",
  "superposition_from_variables",
  "symbol_precedence",

  "test_id",
  "time_limit",

  "unused_predicate_definition_removal",

  "weight_increment",

  "xml_output"};

/** Names for all options */
NameArray Options::Constants::optionNames(_optionNames,
					  sizeof(_optionNames)/sizeof(char*));

const char* Options::Constants::_shortNames[] = {
  "awr",
  "bd",
  "bs",
  "ep",
  "fde",
  "fsr",
  "l",
  "lcm",
  "m",
  "n",
  "nwc",
  "p",
  "pc",
  "s",
  "sa",
  "sos",
  "sp",
  "stl",
  "t",
  "wi"};

/** Short names for all options */
NameArray Options::Constants::shortNames(_shortNames,
					  sizeof(_shortNames)/sizeof(char*));

int Options::Constants::shortNameIndexes[] = {
  AGE_WEIGHT_RATIO,
  BACKWARD_DEMODULATION,
  BACKWARD_SUBSUMPTION,
  EQUALITY_PROXY,
  FUNCTION_DEFINITION_ELIMINATION,
  FORWARD_SUBSUMPTION_RESOLUTION,
  LOG_FILE,
  LITERAL_COMPARISON_MODE,
  MEMORY_LIMIT,
  NORMALIZE,
  NONGOAL_WEIGHT_COEFFICIENT,
  PROOF,
  PROOF_CHECKING,
  SELECTION,
  SATURATION_ALGORITHM,
  SOS,
  SPLITTING,
  SIMULATED_TIME_LIMIT,
  TIME_LIMIT,
  WEIGHT_INCREMENT};

const char* Options::Constants::_statisticsValues[] = {
  "brief",
  "full",
  "none"};
NameArray Options::Constants::statisticsValues(_statisticsValues,
					       sizeof(_statisticsValues)/sizeof(char*));

const char* Options::Constants::_demodulationValues[] = {
  "all",
  "off",
  "preordered"};
NameArray Options::Constants::demodulationValues(_demodulationValues,
						 sizeof(_demodulationValues)/sizeof(char*));

const char* Options::Constants::_fdeValues[] = {
  "all",
  "none",
  "unused"};
NameArray Options::Constants::fdeValues(_fdeValues,
					sizeof(_fdeValues)/sizeof(char*));

const char* Options::Constants::_lcmValues[] = {
  "kinky",
  "predicate",
//   "reverse",
  "standard"
};
NameArray Options::Constants::lcmValues(_lcmValues,
					sizeof(_lcmValues)/sizeof(char*));

const char* Options::Constants::_satAlgValues[] = {
  "discount",
  "lrs",
  "otter"};
NameArray Options::Constants::satAlgValues(_satAlgValues,
					   sizeof(_satAlgValues)/sizeof(char*));

const char* Options::Constants::_equalityProxyValues[] = {
  "exp1",
  "off",
  "on",
  "R",
  "RS",
  "RST"};
NameArray Options::Constants::equalityProxyValues(_equalityProxyValues,
						  sizeof(_equalityProxyValues)/sizeof(char*));

const char* Options::Constants::_splittingValues[] = {
  "input_only",
  "off",
  "on"};
NameArray Options::Constants::splittingValues(_splittingValues,
					      sizeof(_splittingValues)/sizeof(char*));

const char* Options::Constants::_symbolPrecedenceValues[] = {
  "arity",
  "occurrence",
  "reverse_arity"};
NameArray Options::Constants::symbolPrecedenceValues(_symbolPrecedenceValues,
						     sizeof(_symbolPrecedenceValues)/sizeof(char*));

const char* Options::Constants::_tcValues[] = {
  "full",
  "none",
  "only_nonvariables"};
NameArray Options::Constants::tcValues(_tcValues,
				       sizeof(_tcValues)/sizeof(char*));

const char* Options::Constants::_modeValues[] = {
  "casc",
  "output",
  "profile",
  "rule",
  "spider",
  "vampire"};
NameArray Options::Constants::modeValues(_modeValues,
					 sizeof(_modeValues)/sizeof(char*));

/** Possible values for --proof */
const char* Options::Constants::_proofValues[] = {
  "off",
  "on",
  "succinct"};
NameArray Options::Constants::proofValues(_proofValues,
					  sizeof(_proofValues)/sizeof(char*));

/**
 * Initialize options to the default values.
 *
 * @since 10/07/2003 Manchester, _normalize added
 */
Options::Options ()
  :
  _ageRatio(1),
  _weightRatio(1),

  _backwardDemodulation(DEMODULATION_ALL),
  _backwardSubsumption(true),

  _condensation(false),

  _equalityProxy(EP_OFF),
  _equalityResolutionWithDeletion(false),

  _forwardDemodulation(DEMODULATION_ALL),
  _forwardSubsumption(true),
  _forwardSubsumptionResolution(true),
  _functionDefinitionElimination(FDE_ALL),

  _include(""),
  _inequalitySplitting(3),
  _inputFile(""),

  _latexOutput("off"),
  _literalComparisonMode(LCM_STANDARD),
  _logFile("off"),
  _lrsFirstTimeCheck(5),

  _maxActive(0),
  _maxAnswers(1),
  _maxInferenceDepth(0),
  _maxPassive(0),
  _maxWeight(0),
  _memoryLimit(1000),
  _mode(MODE_VAMPIRE),

  _naming(8),

  _nongoalWeightCoefficient(1.0),
  _normalize(false),

  _orphanDeletion(false),
  _outputMessages(true),

  _problemName(""),
  _proof(PROOF_ON),
  _proofChecking(false),

  _randomSeed(Random::seed()),
  _rowVariableMaxLength(2),

  _saturationAlgorithm(LRS),
  _selection(10),
  _showActive(false),
  _showNew(false),
  _showOptions(false),
  _showPassive(false),
  _simulatedTimeLimit(0),
  _sos(false),
  _splitting(SPLIT_INPUT_ONLY),
  _statistics(STATISTICS_FULL),
  _superpositionFromVariables(true),
  _symbolPrecedence(BY_ARITY),

  _testId ("unspecified_test"),
  _timeLimitInDeciseconds(0),

  _unusedPredicateDefinitionRemoval(true),

  _weightIncrement(false),

  _xmlOutput("off")
{
  CALL("Options::Options");
} // Options::Options


/**
 * Set option by its name and value.
 * @since 13/11/2004 Manchester
 */
void Options::set (const char* name,const char* value)
{
  CALL ("Options::set/2");

  set(name,value,Constants::optionNames.find(name));
} // Options::set/2


/**
 * Set option by its name and value.
 * @since 06/04/2005 Torrevieja
 */
void Options::set (const string& name,const string& value)
{
  CALL ("Options::set/3");

  set(name.c_str(),value.c_str());
} // Options::set/3


/**
 * Set option by its name, value, and index in the list of options.
 * If index is -1, then name does not correspond to any existing option.
 *
 * @since 13/11/2004 Manchester
 */
void Options::set (const char* name,const char* value, int index)
{
  CALL("Options::set/3");

  int intValue;
  float floatValue;

  switch (index) {
  case AGE_WEIGHT_RATIO:
    readAgeWeightRatio(value);
    return;

  case BACKWARD_DEMODULATION:
    _backwardDemodulation = (Demodulation)Constants::demodulationValues.find(value);
    if (_backwardDemodulation == -1) {
      break;
    }
    return;
  case BACKWARD_SUBSUMPTION:
    _backwardSubsumption = onOffToBool(value,name);
    return;

  case CONDENSATION:
    _condensation = onOffToBool(value,name);
    return;

  case DECODE:
    readFromTestId(value);
    return;

  case EQUALITY_PROXY:
    _equalityProxy = (EqualityProxy)Constants::equalityProxyValues.find(value);
    if (_equalityProxy == -1) {
      break;
    }
    return;

  case EQUALITY_RESOLUTION_WITH_DELETION:
    _equalityResolutionWithDeletion = onOffToBool(value,name);
    return;

  case FORWARD_DEMODULATION:
    _forwardDemodulation =
      (Demodulation)Constants::demodulationValues.find(value);
    if (_forwardDemodulation == -1) {
      break;
    }
    return;
  case FORWARD_SUBSUMPTION:
    _forwardSubsumption = onOffToBool(value,name);
    return;
  case FORWARD_SUBSUMPTION_RESOLUTION:
    _forwardSubsumptionResolution = onOffToBool(value,name);
    return;
  case FUNCTION_DEFINITION_ELIMINATION:
    _functionDefinitionElimination =
      (FunctionDefinitionElimination)Constants::fdeValues.find(value);
    if (_functionDefinitionElimination == -1) {
      break;
    }
    return;

  case INCLUDE:
    _include = value;
    return;
  case INEQUALITY_SPLITTING:
    if (Int::stringToUnsignedInt(value,intValue)) {
      _inequalitySplitting = intValue;
      return;
    }
    break;

  case LATEX_OUTPUT:
    _latexOutput = value;
    return;
  case LITERAL_COMPARISON_MODE:
    _literalComparisonMode =
      (LiteralComparisonMode)Constants::lcmValues.find(value);
    if (_literalComparisonMode == -1) {
      break;
    }
    return;
  case LOG_FILE:
    _logFile = value;
    return;
  case LRS_FIRST_TIME_CHECK:
    if (Int::stringToInt(value,intValue) &&
	setLrsFirstTimeCheck(intValue)) {
      return;
    }
    break;

  case MAX_ACTIVE:
    if (Int::stringToUnsignedInt(value,intValue)) {
      _maxActive = intValue;
      return;
    }
    break;
  case MAX_ANSWERS:
    if (Int::stringToUnsignedInt(value,intValue)) {
      _maxAnswers = intValue;
      return;
    }
    break;
  case MAX_INFERENCE_DEPTH:
    if (Int::stringToUnsignedInt(value,intValue)) {
      _maxInferenceDepth = intValue;
      return;
    }
    break;
  case MAX_PASSIVE:
    if (Int::stringToUnsignedInt(value,intValue)) {
      _maxPassive = intValue;
      return;
    }
    break;
  case MAX_WEIGHT:
    if (Int::stringToUnsignedInt(value,intValue)) {
      _maxWeight = intValue;
      return;
    }
    break;
  case MEMORY_LIMIT:
    if (Int::stringToUnsignedInt(value,intValue)) {
      _memoryLimit = intValue;
      return;
    }
    break;
  case MODE:
    _mode = (Mode)Constants::modeValues.find(value);
    if (_mode == -1) {
      break;
    }
    return;

  case NAMING:
    if (Int::stringToUnsignedInt(value,intValue) &&
	setNaming(intValue)) {
      return;
    }
    break;
  case NONGOAL_WEIGHT_COEFFICIENT:
    if (Int::stringToFloat(value,floatValue) &&
	setNongoalWeightCoefficient(floatValue)) {
      return;
    }
    break;
  case NORMALIZE:
    _normalize = onOffToBool(value,name);
    return;

  case ORPHAN_DELETION:
    _orphanDeletion = onOffToBool(value,name);
    return;
  case OUTPUT_MESSAGES:
    _outputMessages = onOffToBool(value,name);
    return;

  case PROOF:
    _proof = (Proof)Constants::proofValues.find(value);
    if (_proof == -1) {
      break;
    }
    return;

  case PROOF_CHECKING:
    _proofChecking = onOffToBool(value,name);
    return;

  case RANDOM_SEED:
    if (Int::stringToUnsignedInt(value,intValue)) {
      _randomSeed = intValue;
      return;
    }
    break;
  case ROW_VARIABLE_MAX_LENGTH:
    if (Int::stringToUnsignedInt(value,intValue)) {
      _rowVariableMaxLength = intValue;
      return;
    }
    break;

  case SATURATION_ALGORITHM:
    _saturationAlgorithm = (SaturationAlgorithm)Constants::satAlgValues.find(value);
    if (_saturationAlgorithm == -1) {
      break;
    }
    return;
  case SELECTION:
    if (Int::stringToInt(value,intValue) &&
	setSelection(intValue) ) {
      return;
    }
    break;
  case SHOW_ACTIVE:
    _showActive = onOffToBool(value,name);
    return;
  case SHOW_NEW:
    _showNew = onOffToBool(value,name);
    return;
  case SHOW_OPTIONS:
    _showOptions = onOffToBool(value,name);
    return;
  case SHOW_PASSIVE:
    _showPassive = onOffToBool(value,name);
    return;
  case SIMULATED_TIME_LIMIT:
    _simulatedTimeLimit = readTimeLimit(value);
    return;
  case SOS:
    _sos = onOffToBool(value,name);
    return;
  case SPLITTING:
    _splitting = (Splitting)Constants::splittingValues.find(value);
    if (_splitting == -1) {
      break;
    }
    return;
  case STATISTICS:
    _statistics = (Statistics)Constants::statisticsValues.find(value);
    if (_statistics == -1) {
      break;
    }
    return;
  case SUPERPOSITION_FROM_VARIABLES:
    _superpositionFromVariables = onOffToBool(value,name);
    return;
  case SYMBOL_PRECEDENCE:
    _symbolPrecedence =
      (SymbolPrecedence)Constants::symbolPrecedenceValues.find(value);
    if (_symbolPrecedence == -1) {
      break;
    }
    return;

  case TEST_ID:
    _testId = value;
    return;

  case TIME_LIMIT:
    _timeLimitInDeciseconds = readTimeLimit(value);
    return;

  case UNUSED_PREDICATE_DEFINITION_REMOVAL:
    _unusedPredicateDefinitionRemoval = onOffToBool(value,name);
    return;

  case WEIGHT_INCREMENT:
    _weightIncrement = onOffToBool(value,name);
    return;

  case XML_OUTPUT:
    _xmlOutput = value;
    return;

  case -1: // not found
    USER_ERROR((string)name + " is not a valid option");

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }

  USER_ERROR((string)"wrong value (" + value + ") for " + name);
} // Options::set


/**
 * Set option by its short name and value. If such a short name does not
 * exist, try to use the long name instead.
 *
 * @since 21/11/2004 Manchester
 */
void Options::setShort (const char* name,const char* value)
{
  CALL ("Options::setShort");

  int found = Constants::shortNames.find(name);
  if (found == -1) {
    found = Constants::optionNames.find(name);
  }
  else {
    found = Constants::shortNameIndexes[found];
  }
  set(name,value,found);
} // Options::setShort


/**
 * Convert the string onOff to a boolean value. If onOff is not one
 * of "on" or "off", then raise a user error exception.
 * @since 15/11/2004 Manchester
 */
bool Options::onOffToBool (const char* onOff,const char* option)
{
  CALL("Options::onOffToBool");

  if (! strcmp(onOff,"on")) {
    return true;
  }
  if (! strcmp(onOff,"off")) {
    return false;
  }

  USER_ERROR((string)"wrong value for " + option + ": " + onOff);
} // Options::onOffToBool


/**
 * Convert a boolean value to the corresponding string "on"/"off"
 * value.
 * @since 15/11/2004 Manchester
 */
string Options::boolToOnOff (bool val)
{
  CALL("Options::boolToOnOff");

  static string on ("on");
  static string off ("off");

  return val ? on : off;
} // Options::boolToOnOff


/**
 * Set selection to a new value.
 * @since 15/11/2004 Manchester
 */
bool Options::setSelection(int sel)
{
  CALL("Options::setSelection");

  _selection = sel;
  return true;
//  switch (sel) {
//  case -11:
//  case -16:
//  case -1012:
//  case 8:
//  case 10:
//  case 11:
//  case 13:
//  case 16:
//  case 17:
//  case 1010:
//  case 1011:
//  case 1012:
//  case 1013:
//    _selection = sel;
//    return true;
//  default:
//    return false;
//  }
} // Options::setSelection


/**
 * Set nongoal weight coefficient to a new value.
 * @since 15/11/2004 Manchester.
 */
bool Options::setNongoalWeightCoefficient (float newVal)
{
  CALL("Options::setNongoalWeightCoefficient");

  if (newVal <= 0.0) {
    return false;
  }
  _nongoalWeightCoefficient = newVal;
  return true;
} // Options::setNongoalWeightCoefficient


/**
 * Set naming to a new value.
 * @since 13/07/2005 Haifa
 */
bool Options::setNaming (int newVal)
{
  CALL("Options::setNaming");

  if (newVal > 32767) {
    return false;
  }
  _naming = newVal;
  return true;
} // Options::setNaming


/**
 * Set LRS first time check.
 * @since 15/11/2004 Manchester.
 */
bool Options::setLrsFirstTimeCheck (int newVal)
{
  CALL("Options::setLrsFirstTimeCheck");

  if (newVal < 0 && newVal >= 100) {
    return false;
  }
  _lrsFirstTimeCheck = newVal;
  return true;
} // Options::setLrsFirstTimeCheck


/**
 * Return the include file name using its relative name.
 *
 * @param relativeName the relative name, must begin and end with "'"
 *        because of the TPTP syntax
 * @since 16/10/2003 Manchester, relativeName change to string from char*
 */
string Options::includeFileName (const string& relativeName)
{
  CALL("Options::includeFileName");

  if (relativeName[0] == '/') { // absolute name
    return relativeName;
  }

  // truncatedRelativeName is relative.
  // Use the conventions of Vampire:
  // (a) first search the value of "include"
  string dir = include ();
  if (dir == "") { // include undefined
    // (b) search the value of the environment variable TPTP_DIR
    char* env = getenv("TPTP_DIR");
    if (env) {
      dir = env;
    }
    else {
      dir = ".";
    }
  }
  // now dir is the directory to search
  return dir + "/" + relativeName;
} // Options::includeFileName


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
void Options::output (ostream& str) const
{
  CALL("Options::output");

  if (! showOptions()) {
    return;
  }

  str << "=========== Options ==========\n";

  for (int i = 0;i < Constants::optionNames.length;i++) {
    str << Constants::optionNames[i] << '=';
    outputValue(str,i);
    str << '\n';
  }

  str << "======= End of options =======\n";
} // Options::output (ostream& str) const


/**
 * Output the value of an option with a given tag to the output stream
 * str.
 *
 * @since 15/11/2004 Manchester
 */
void Options::outputValue (ostream& str,int optionTag) const
{
  CALL("Options::outputValue");

  switch (optionTag) {
  case AGE_WEIGHT_RATIO:
    str << _ageRatio << ':' << _weightRatio;
    return;

  case BACKWARD_DEMODULATION:
    str << Constants::demodulationValues[_backwardDemodulation];
    return;
  case BACKWARD_SUBSUMPTION:
    str << boolToOnOff(_backwardSubsumption);
    return;

  case CONDENSATION:
    str << boolToOnOff(_condensation);
    return;

  case DECODE: // no output for DECODE
    return;

  case EQUALITY_PROXY:
    str << Constants::equalityProxyValues[_equalityProxy];
    return;
  case EQUALITY_RESOLUTION_WITH_DELETION:
    str << boolToOnOff(_equalityResolutionWithDeletion);
    return;

  case FORWARD_DEMODULATION:
    str << Constants::demodulationValues[_forwardDemodulation];
    return;
  case FORWARD_SUBSUMPTION:
    str << boolToOnOff(_forwardSubsumption);
    return;
  case FORWARD_SUBSUMPTION_RESOLUTION:
    str << boolToOnOff(_forwardSubsumptionResolution);
    return;
  case FUNCTION_DEFINITION_ELIMINATION:
    str << Constants::fdeValues[_functionDefinitionElimination];
    return;

  case INCLUDE:
    str << _include;
    return;
  case INEQUALITY_SPLITTING:
    str << _inequalitySplitting;
    return;

  case LATEX_OUTPUT:
    str << _latexOutput;
    return;
  case LITERAL_COMPARISON_MODE:
    str << Constants::lcmValues[_literalComparisonMode];
    return;
  case LOG_FILE:
    str << _logFile;
    return;
  case LRS_FIRST_TIME_CHECK:
    str << _lrsFirstTimeCheck;
    return;

  case MAX_ACTIVE:
    str << _maxActive;
    return;
  case MAX_ANSWERS:
    str << _maxAnswers;
    return;
  case MAX_INFERENCE_DEPTH:
    str << _maxInferenceDepth;
    return;
  case MAX_PASSIVE:
    str << _maxPassive;
    return;
  case MAX_WEIGHT:
    str << _maxWeight;
    return;
  case MEMORY_LIMIT:
    str << _memoryLimit;
    return;
  case MODE:
    str << Constants::modeValues[_mode];
    return;

  case NAMING:
    str << _naming;
    return;
  case NONGOAL_WEIGHT_COEFFICIENT:
    str << _nongoalWeightCoefficient;
    return;
  case NORMALIZE:
    str << boolToOnOff(_normalize);
    return;

  case ORPHAN_DELETION:
    str << boolToOnOff(_orphanDeletion);
    return;
  case OUTPUT_MESSAGES:
    str << boolToOnOff(_outputMessages);
    return;

  case PROBLEM_NAME:
    str << _problemName;
    return;
  case PROOF:
    str << boolToOnOff(_proof);
    return;
  case PROOF_CHECKING:
    str << boolToOnOff(_proofChecking);
    return;

  case RANDOM_SEED:
    str << _randomSeed;
    return;
  case ROW_VARIABLE_MAX_LENGTH:
    str << _rowVariableMaxLength;
    return;

  case SATURATION_ALGORITHM:
    str << Constants::satAlgValues[_saturationAlgorithm];
    return;
  case SELECTION:
    str << _selection;
    return;
  case SHOW_ACTIVE:
    str << boolToOnOff(_showActive);
    return;
  case SHOW_NEW:
    str << boolToOnOff(_showNew);
    return;
  case SHOW_OPTIONS:
    str << boolToOnOff(_showOptions);
    return;
  case SHOW_PASSIVE:
    str << boolToOnOff(_showPassive);
    return;
  case SIMULATED_TIME_LIMIT:
    str << _simulatedTimeLimit/10;
    if (_simulatedTimeLimit % 10) {
      str << '.' << _simulatedTimeLimit % 10;
    }
    return;
  case SOS:
    str << boolToOnOff(_sos);
    return;
  case SPLITTING:
    str << Constants::splittingValues[_splitting];
    return;
  case STATISTICS:
    str << Constants::statisticsValues[_statistics];
    return;
  case SUPERPOSITION_FROM_VARIABLES:
    str << boolToOnOff(_superpositionFromVariables);
    return;
  case SYMBOL_PRECEDENCE:
    str << Constants::symbolPrecedenceValues[_symbolPrecedence];
    return;

  case TEST_ID:
    str << _testId;
    return;
  case TIME_LIMIT:
    str << _timeLimitInDeciseconds/10;
    if (_timeLimitInDeciseconds % 10) {
      str << '.' << _timeLimitInDeciseconds % 10;
    }
    return;

  case UNUSED_PREDICATE_DEFINITION_REMOVAL:
    str << boolToOnOff(_unusedPredicateDefinitionRemoval);
    return;

  case WEIGHT_INCREMENT:
    str << boolToOnOff(_weightIncrement);
    return;

  case XML_OUTPUT:
    str << _xmlOutput;
    return;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // Options::outputValue


/**
 * Return the problem name computed from the input file name. Returns
 * null pointer if the input file name is not specified or is wrong;
 *
 * @since 07/07/2003 Manchester, bug fixed (when the problem name contained
 *        more than one ".", the name was calculated wrongly
 * @since 06/12/2003 Manchester, changed to use and return string
 */
string Options::problemName () const
{
  CALL("Options::problemName");

  if (_problemName != "") {
    return _problemName;
  }

  string inputFileName = inputFile();
  if (inputFileName == "") {
    return "unknown";
  }

  int length = inputFileName.length() - 1;
  const char* name = inputFileName.c_str();

  int b = length - 1;
  while (b >= 0 && name[b] != '/') {
    b--;
  }
  b++;

  int e = length-1;
  while (e >= b && name[e] != '.') {
    e--;
  }
  if (e < b) {
    e = length-1;
  }

  return inputFileName.substr(b,e-b);
} // const char* Options::problemName () const


// /**
//  * Convert options to an XML element.
//  *
//  * @since 15/11/2004 Manchester
//  */
// XMLElement Options::toXML () const
// {
//   CALL("Options::toXML");

//   XMLElement options("options");
//   for (int i = 0;i < Constants::optionNames.length;i++) {
//     ostringstream str;
//     outputValue(str,i);
//     XMLElement option("option",true);
//     options.addChild(option);
//     option.addAttribute("name",Constants::optionNames[i]);
//     option.addAttribute("value",str.str());
//   }
//   return options;
// } // Options::toXML


/**
 * Read age-weight ratio from a string. The string can be an integer
 * or an expression "a:w", where a,w are integers.
 *
 * @since 25/05/2004 Manchester
 */
void Options::readAgeWeightRatio(const char* val)
{
  CALL("Options::readAgeWeightRatio");

  // search the string for ":"
  bool found = false;
  int colonIndex = 0;
  while (val[colonIndex]) {
    if (val[colonIndex] == ':') {
      found = true;
      break;
    }
    colonIndex++;
  }

  if (found) {
    if (strlen(val) > 127) {
      USER_ERROR((string)"wrong value for age-weight ratio: " + val);
    }
    char copy[128];
    strcpy(copy,val);
    copy[colonIndex] = 0;
    int age;
    if (! Int::stringToInt(copy,age)) {
      USER_ERROR((string)"wrong value for age-weight ratio: " + val);
    }
    _ageRatio = age;
    int weight;
    if (! Int::stringToInt(copy+colonIndex+1,weight)) {
      USER_ERROR((string)"wrong value for age-weight ratio: " + val);
    }
    _weightRatio = weight;
    return;
  }
  _ageRatio = 1;
  int weight;
  if (! Int::stringToInt(val,weight)) {
    USER_ERROR((string)"wrong value for age-weight ratio: " + val);
  }
  _weightRatio = weight;
} // Options::readAgeWeightRatio(const char* val)


/**
 * Read age-weight ratio from a string. The string can be an integer
 * or an expression "a:w", where a,w are integers.
 *
 * @since 25/05/2004 Manchester
 */
int Options::readTimeLimit(const char* val)
{
  CALL("Options::readTimeLimit");

  int length = strlen(val);
  if (length == 0 || length > 127) {
    USER_ERROR((string)"wrong value for time limit: " + val);
  }

  char copy[128];
  strcpy(copy,val);
  char* end = copy;
  // search for the end of the string for
  while (*end) {
    end++;
  }
  end--;
  float multiplier = 10.0;
  switch (*end) {
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
  case 'd': // days
    multiplier = 864000.0;
    *end = 0;
    break;
  default:
    break;
  }

  float number;
  if (! Int::stringToFloat(copy,number)) {
    USER_ERROR((string)"wrong value for time limit: " + val);
  }

#ifdef _MSC_VER
  // Visual C++ does not know the round function
  return (int)floor(number * multiplier);
#else
  return (int)round(number * multiplier);
#endif
} // Options::readTimeLimit(const char* val)


/**
 * Build options from a Spider test id.
 * @since 30/05/2004 Manchester
 * @since 21/06/2005 Manchester time limit in the test id must be
 *        in deciseconds
 * @throws UserErrorException if the test id is incorrect
 */
void Options::readFromTestId (string testId)
{
  CALL("Options::setLrsFirstTimeCheck");

  _normalize = true;
  _testId = testId;

  string ma(testId,0,3); // the first 3 characters
  if (ma == "dis") {
    _saturationAlgorithm = DISCOUNT;
  }
  else if (ma == "lrs") {
    _saturationAlgorithm = LRS;
  }
  else if (ma == "ott") {
    _saturationAlgorithm = OTTER;
  }
  else {
  error: USER_ERROR("bad test id " + testId);
  }

  // after last '_' we have time limit
  size_t index = testId.find_last_of('_');
  if (index == string::npos) { // not found
    goto error;
  }
  string timeString = testId.substr(index+1);
  _timeLimitInDeciseconds = readTimeLimit(timeString.c_str()) / 10;

  testId = testId.substr(3,index-2);
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
  int selection;
  string sel = testId.substr(0,index);
  Int::stringToInt(sel,selection);
  setSelection(selection);
  testId = testId.substr(index+1);

  if (testId == "") {
    goto error;
  }

  index = testId.find('_');
  string awr = testId.substr(0,index);
  readAgeWeightRatio(awr.c_str());
  testId = testId.substr(index+1);
  // repeatedly look for param=value
  while (testId != "") {
    size_t index1 = testId.find('=');
    if (index1 == string::npos) {
      goto error;
    }
    index = testId.find('_');
    if (index1 > index) {
      goto error;
    }

    string param = testId.substr(0,index1);
    string value = testId.substr(index1+1,index-index1-1);
    setShort(param.c_str(),value.c_str());
    testId = testId.substr(index+1);
  }
} // Options::readFromTestId


/**
 * The standard output is suppressed if either LaTeX or XML
 * output is directed to cout.
 * @since 05/07/2004 Cork
 */
bool Options::outputSuppressed () const
{
  CALL("Options::setLrsFirstTimeCheck");

  return _xmlOutput == "on" ||
         _latexOutput == "on";
} // Output::outputSuppressed

/**
 * True if the options are complete.
 * @since 28/07/2005 Manchester
 */
bool Options::complete () const
{
  CALL("Options::setLrsFirstTimeCheck");

  return ! _equalityResolutionWithDeletion &&
         (_literalComparisonMode != LCM_REVERSE) &&
         _selection < 20 &&
         _selection > -20 &&
         ! _sos &&
         _superpositionFromVariables;
} // Options::complete


}
