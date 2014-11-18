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


#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/VString.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Int.hpp"
#include "Lib/NameArray.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/XML.hpp"

#include "Property.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class Property;

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
    void init();
    void copyValuesFrom(Options& that);
    void copyValuesFrom(const Options& that);
    Options(Options& that);
    Options(const Options& that);
    Options& operator=(const Options& that);

    // used to print help and options
    void output (ostream&) const;

    // for use in testing 
    void readFromTestId (vstring testId);
    void readOptionsString (vstring testId);
    vstring generateTestId() const;

    // deal with completeness
    bool complete(const Problem&) const;
    bool completeForNNE() const;
    void forceIncompleteness() { _forceIncompleteness.actualValue=true; }

    // deal with options constraints
    void setForcedOptionValues();
    void checkGlobalOptionConstraints() const;
    void checkProblemOptionConstraints(const Problem&) const;
    
    /**
     * Return the problem name
     *
     * The problem name is computed from the input file name in
     * the @b setInputFile function. If the input file is not set,
     * the problem name is equal to "unknown". The problem name can
     * be set to a specific value using setProblemName().
     */
    vstring problemName () const { return _problemName.actualValue; }
    void setProblemName(vstring str) { _problemName.actualValue = str; }
    
    void setInputFile(const vstring& newVal){ _inputFile.set(newVal); }
    vstring includeFileName (const vstring& relativeName);

    CLASS_NAME(Options);
    USE_ALLOCATOR(Options);
    
    // standard ways of creating options
    void set(const vstring& name, const vstring& value);
    void set(const char* name, const char* value);
    void setShort(const char* name, const char* value);
    

    
public:
  //==========================================================
  // The Enums for Option Values
  //==========================================================
  
  enum class BadOption : unsigned int {
    HARD,
    FORCED,
    OFF,
    SOFT
  };

  //enums for the bound propagation purpose
  enum class BPAlmostHalfBoundingRemoval : unsigned int {
    BOUNDS_ONLY = 0,
    OFF = 1,
    ON = 2
  };

  enum class BPAssignmentSelector: unsigned int {
    ALTERNATIVE = 0,
    BMP = 1,
    LOWER = 2,
    MIDDLE = 3,
    RANDOM = 4,
    RATIONAL = 5,
    SMALLEST = 6,
    TIGHT = 7,
    TIGHTISH = 8,
    UPPER = 9
  };
  
  enum class BPConflictSelector: unsigned int {
    LEAST_RECENT = 0, 
    MOST_RECENT = 1, 
    SHORTEST_CONSTRAINT = 2
  };
  
  enum class BPVariableSelector: unsigned int {
    CONFLICTING = 0, 
    CONFLICTING_AND_COLLAPSING = 1, 
    FIRST = 2, 
    LOOK_AHEAD =3, 
    RANDOM = 4, 
    RECENTLY_CONFLICTING = 5,
    RECENTLY_COLLAPSING = 6,
    TIGHTEST_BOUND = 7

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
   * Possible values for the input syntax
   * @since 26/08/2009 Redmond
   */
  enum class InputSyntax : unsigned int {
    /** syntax of the Simplify prover */
    SIMPLIFY = 0,
    /** syntax of SMTLIB1.2 */
    SMTLIB = 1,
    SMTLIB2 = 2,
    /** syntax of the TPTP prover */
    TPTP = 3, 
    HUMAN = 4, 
    MPS = 5, 
    NETLIB = 6
  };

 /**
  * Possible tags to group options by 
  * Update _tagNames at the end of Options constructor if you add a tag
  * @author Giles
  */
  enum class OptionTag: unsigned int {
    OTHER,
    OUTPUT,
    TABULATION,
    INST_GEN,
    SAT,
    AVATAR,
    INFERENCES,
    SATURATION,
    PREPROCESSING,
    LAST_TAG // Used for counting the number of tags
  };
  // update _tagNames at the end of Options constructor if you add a tag

  /**
   * Possible values for mode_name.
   * @since 06/05/2007 Manchester
   */
  enum class Mode : unsigned int {
    AXIOM_SELECTION,
    BOUND_PROP,
    CASC,
    CASC_EPR,
    CASC_LTB,
    CASC_MZR,
    CASC_SAT,
    CLAUSIFY,
    CONSEQUENCE_ELIMINATION,
    GROUNDING,
    LTB_BUILD,
    LTB_SOLVE,
    /** this mode only outputs the input problem, without any preprocessing */
    OUTPUT,
    PREPROCESS,
    PROFILE,
    PROGRAM_ANALYSIS,   
    SAT, 
    SPIDER,
    VAMPIRE
};

/*
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

  /** Possible values for sat_solver */
  enum class SatSolver : unsigned int {
     BUFFERED_LINGELING = 0,
     BUFFERED_MINISAT = 1,
     BUFFERED_VAMPIRE = 2,
     LINGELING = 3,
     MINISAT = 4,
     VAMPIRE = 5
  };

  /** Possible values for saturation_algorithm */
  enum class SaturationAlgorithm : unsigned int {
     DISCOUNT = 0,
     INST_GEN = 1,
     LRS = 2,
     OTTER = 3,
     TABULATION = 4
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

  enum class InliningMode : unsigned int {
    AXIOMS_ONLY = 0,
    NON_GROWING = 1,
    OFF = 2,
    ON = 3
  };

  enum class InterpolantMode : unsigned int {
    MINIMIZED = 0,
    OFF = 1,
    ON = 2
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

  enum class SymbolPrecedence : unsigned int {
    ARITY = 0,
    OCCURRENCE = 1,
    REVERSE_ARITY = 2
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
    TPTP = 3
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
    OFF = 2
  };

  enum class SatRestartStrategy : unsigned int {
    FIXED = 0,
    GEOMETRIC = 1,
    LUBY = 2,
    MINISAT = 3,
  };

  enum class SatVarSelector : unsigned int {
    ACTIVE = 0,
    NICENESS = 1,
    RECENTLY_LEARNT = 2,
  };

  enum class Niceness: unsigned int {
    AVERAGE = 0,
    NONE=1,
    SUM = 2,
    TOP = 3,
  };

  enum class SatClauseDisposer : unsigned int {
    GROWING = 0,
    MINISAT = 1,
  };

  enum class SSplittingComponentSweeping : unsigned int {
    ALL = 0,
    ITERATED = 1,
    NONE = 2,
    ONLY_NEW = 3
  };

  enum class SSplittingAddComplementary : unsigned int {
    GROUND = 0,
    NONE = 1
  };

  enum class SSplittingNonsplittableComponents : unsigned int {
    ALL = 0,
    ALL_DEPENDENT = 1,
    KNOWN = 2,
    NONE = 3
  };

  enum class Sos : unsigned int{
    ALL = 0,
    OFF = 1,
    ON = 2
  };

  enum class PredicateEquivalenceDiscoveryMode : unsigned int{
    ALL_ATOMS = 0,
    ALL_FORMULAS = 1,
    DEFINITIONS = 2,
    OFF = 3,
    ON = 4
  };


  //==========================================================
  // Getter functions
  // -currently disabled all unecessary setter functions
  //==========================================================


  BadOption getBadOptionChoice() const { return _badOption.actualValue; }
  vstring forcedOptions() const { return _forcedOptions.actualValue; }
  vstring forbiddenOptions() const { return _forbiddenOptions.actualValue; }
  vstring testId() const { return _testId.actualValue; }
  vstring protectedPrefix() const { return _protectedPrefix.actualValue; }
  Statistics statistics() const { return _statistics.actualValue; }
  void setStatistics(Statistics newVal) { _statistics.actualValue=newVal; }
  Proof proof() const { return _proof.actualValue; }
  bool proofChecking() const { return _proofChecking.actualValue; }
  int naming() const { return _naming.actualValue; }
  bool flattenTopLevelConjunctions() const { return _flattenTopLevelConjunctions.actualValue; }
  bool eprPreservingNaming() const { return _eprPreservingNaming.actualValue; }
  //void setEprPreservingNaming(bool newVal) { _eprPreservingNaming = newVal; }
  bool eprPreservingSkolemization() const { return _eprPreservingSkolemization.actualValue; }
  //void setEprPreservingSkolemization(bool newVal) { _eprPreservingSkolemization = newVal; }
  bool eprRestoringInlining() const { return _eprRestoringInlining.actualValue; }
  //void setEprRestoringInlining(bool newVal) { _eprRestoringInlining = newVal; }
  InliningMode predicateDefinitionInlining() const { return _predicateDefinitionInlining.actualValue; }
  //void setPredicateDefinitionInlining(InliningMode newVal) { _predicateDefinitionInlining.actualValue = newVal; }
  bool predicateDefinitionMerging() const { return _predicateDefinitionMerging.actualValue; }
  //void setPredicateDefinitionMerging(bool newValue) { _predicateDefinitionMerging = newValue; }
  PredicateEquivalenceDiscoveryMode predicateEquivalenceDiscovery() const { return _predicateEquivalenceDiscovery.actualValue; }
  void setPredicateEquivalenceDiscovery(PredicateEquivalenceDiscoveryMode newValue) { _predicateEquivalenceDiscovery.actualValue = newValue; }
  bool predicateEquivalenceDiscoveryAddImplications() const { return _predicateEquivalenceDiscoveryAddImplications.actualValue; }
  bool predicateEquivalenceDiscoveryRandomSimulation() const { return _predicateEquivalenceDiscoveryRandomSimulation.actualValue; }
  int predicateEquivalenceDiscoverySatConflictLimit() const { return _predicateEquivalenceDiscoverySatConflictLimit.actualValue; }
  bool predicateIndexIntroduction() const { return _predicateIndexIntroduction.actualValue; }
  //void setPredicateIndexIntroduction(bool newValue) { _predicateIndexIntroduction = newValue; }
  bool aigBddSweeping() const { return _aigBddSweeping.actualValue; }
  bool aigConditionalRewriting() const { return _aigConditionalRewriting.actualValue; }
  bool aigDefinitionIntroduction() const { return _aigDefinitionIntroduction.actualValue; }
  unsigned aigDefinitionIntroductionThreshold() const { return _aigDefinitionIntroductionThreshold.actualValue; }
  bool aigFormulaSharing() const { return _aigFormulaSharing.actualValue; }
  bool aigInliner() const { return _aigInliner.actualValue; }
  Mode mode() const { return _mode.actualValue; }
  InputSyntax inputSyntax() const { return _inputSyntax.actualValue; }
  //void setInputSyntax(InputSyntax newVal) { _inputSyntax = newVal; }
  bool normalize() const { return _normalize.actualValue; }
  void setNormalize(bool normalize) { _normalize.actualValue = normalize; }
  void setNaming(int n){ _naming.actualValue = n;} //TODO: ensure global constraints
  vstring include() const { return _include.actualValue; }
  void setInclude(vstring val) { _include.actualValue = val; }
  vstring logFile() const { return _logFile.actualValue; }
  vstring inputFile() const { return _inputFile.actualValue; }
  int randomSeed() const { return _randomSeed.actualValue; }
  int rowVariableMaxLength() const { return _rowVariableMaxLength.actualValue; }
  //void setRowVariableMaxLength(int newVal) { _rowVariableMaxLength = newVal; }
  bool printClausifierPremises() const { return _printClausifierPremises.actualValue; }
  bool showActive() const { return _showActive.actualValue; }
  bool showBlocked() const { return _showBlocked.actualValue; }
  bool showDefinitions() const { return _showDefinitions.actualValue; }
  InterpolantMode showInterpolant() const { return _showInterpolant.actualValue; }
  bool showNew() const { return _showNew.actualValue; }
  bool showNewPropositional() const { return _showNewPropositional.actualValue; }
  bool showNonconstantSkolemFunctionTrace() const { return _showNonconstantSkolemFunctionTrace.actualValue; }
  void setShowNonconstantSkolemFunctionTrace(bool newVal) { _showNonconstantSkolemFunctionTrace.actualValue = newVal; }
  bool showOptions() const { return _showOptions.actualValue; }
  bool showExperimentalOptions() const { return _showExperimentalOptions.actualValue; }
  bool showHelp() const { return _showHelp.actualValue; }
  vstring explainOption() const { return _explainOption.actualValue; }
  bool showPassive() const { return _showPassive.actualValue; }
  bool showPreprocessing() const { return _showPreprocessing.actualValue; }
  bool showSkolemisations() const { return _showSkolemisations.actualValue; }
  bool showSymbolElimination() const { return _showSymbolElimination.actualValue; }
  bool showTheoryAxioms() const { return _showTheoryAxioms.actualValue; }
  bool unusedPredicateDefinitionRemoval() const { return _unusedPredicateDefinitionRemoval.actualValue; }
  void setUnusedPredicateDefinitionRemoval(bool newVal) { _unusedPredicateDefinitionRemoval.actualValue = newVal; }
  bool weightIncrement() const { return _weightIncrement.actualValue; }
  bool useDM() const { return _use_dm.actualValue; }
  SatSolver satSolver() const { return _satSolver.actualValue; }
  //void setSatSolver(SatSolver newVal) { _satSolver = newVal; }
  bool satLingelingSimilarModels() const { return _satLingelingSimilarModels.actualValue; }
  bool satLingelingIncremental() const { return _satLingelingIncremental.actualValue; }
  SaturationAlgorithm saturationAlgorithm() const { return _saturationAlgorithm.actualValue; }
  void setSaturationAlgorithm(SaturationAlgorithm newVal) { _saturationAlgorithm.actualValue = newVal; }
  int selection() const { return _selection.actualValue; }
  vstring latexOutput() const { return _latexOutput.actualValue; }
  bool latexUseDefault() const { return _latexUseDefaultSymbols.actualValue; }
  LiteralComparisonMode literalComparisonMode() const { return _literalComparisonMode.actualValue; }
  bool forwardSubsumptionResolution() const { return _forwardSubsumptionResolution.actualValue; }
  //void setForwardSubsumptionResolution(bool newVal) { _forwardSubsumptionResolution = newVal; }
  Demodulation forwardDemodulation() const { return _forwardDemodulation.actualValue; }
  bool binaryResolution() const { return _binaryResolution.actualValue; }
  bool bfnt() const { return _bfnt.actualValue; }
  void setBfnt(bool newVal) { _bfnt.actualValue = newVal; }
  URResolution unitResultingResolution() const { return _unitResultingResolution.actualValue; }
  bool hyperSuperposition() const { return _hyperSuperposition.actualValue; }
  bool arityCheck() const { return _arityCheck.actualValue; }
  //void setArityCheck(bool newVal) { _arityCheck=newVal; }
  Demodulation backwardDemodulation() const { return _backwardDemodulation.actualValue; }
  bool demodulationRedundancyCheck() const { return _demodulationRedundancyCheck.actualValue; }
  //void setBackwardDemodulation(Demodulation newVal) { _backwardDemodulation = newVal; }
  Subsumption backwardSubsumption() const { return _backwardSubsumption.actualValue; }
  //void setBackwardSubsumption(Subsumption newVal) { _backwardSubsumption = newVal; }
  Subsumption backwardSubsumptionResolution() const { return _backwardSubsumptionResolution.actualValue; }
  bool forwardSubsumption() const { return _forwardSubsumption.actualValue; }
  bool forwardLiteralRewriting() const { return _forwardLiteralRewriting.actualValue; }
  vstring lingvaAdditionalInvariants() const {return _lingvaAdditionalInvariants.actualValue; }
  int lrsFirstTimeCheck() const { return _lrsFirstTimeCheck.actualValue; }
  int lrsWeightLimitOnly() const { return _lrsWeightLimitOnly.actualValue; }
  int simulatedTimeLimit() const { return _simulatedTimeLimit.actualValue; }
  void setSimulatedTimeLimit(int newVal) { _simulatedTimeLimit.actualValue = newVal; }
  int maxInferenceDepth() const { return _maxInferenceDepth.actualValue; }
  SymbolPrecedence symbolPrecedence() const { return _symbolPrecedence.actualValue; }
  /**
   * Return time limit in deciseconds, or 0 if there is no time limit
   */
  int timeLimitInDeciseconds() const { return _timeLimitInDeciseconds.actualValue; }
  size_t memoryLimit() const { return _memoryLimit.actualValue; }
  int inequalitySplitting() const { return _inequalitySplitting.actualValue; }
  long maxActive() const { return _maxActive.actualValue; }
  long maxAnswers() const { return _maxAnswers.actualValue; }
  //void setMaxAnswers(int newVal) { _maxAnswers = newVal; }
  long maxPassive() const { return _maxPassive.actualValue; }
  int maxWeight() const { return _maxWeight.actualValue; }
  int ageRatio() const { return _ageWeightRatio.actualValue; }
  int weightRatio() const { return _ageWeightRatio.otherValue; }
  bool superpositionFromVariables() const { return _superpositionFromVariables.actualValue; }
  bool equalityPropagation() const { return _equalityPropagation.actualValue; }
  //void setEqualityPropagation(bool newVal) { _equalityPropagation = newVal; }
  EqualityProxy equalityProxy() const { return _equalityProxy.actualValue; }
  RuleActivity equalityResolutionWithDeletion() const { return _equalityResolutionWithDeletion.actualValue; }
  ExtensionalityResolution extensionalityResolution() const { return _extensionalityResolution.actualValue; }
  unsigned extensionalityMaxLength() const { return _extensionalityMaxLength.actualValue; }
  bool extensionalityAllowPosEq() const { return _extensionalityAllowPosEq.actualValue; }
  
  float nongoalWeightCoefficient() const { return _nonGoalWeightCoefficient.actualValue; }

  Sos sos() const { return _sos.actualValue; }
  //void setSos(Sos newVal) { _sos = newVal; }
  FunctionDefinitionElimination functionDefinitionElimination() const { return _functionDefinitionElimination.actualValue; }
  bool outputAxiomNames() const { return _outputAxiomNames.actualValue; }
  void setOutputAxiomNames(bool newVal) { _outputAxiomNames.actualValue = newVal; }
  QuestionAnsweringMode questionAnswering() const { return _questionAnswering.actualValue; }
  vstring xmlOutput() const { return _xmlOutput.actualValue; }
  vstring thanks() const { return _thanks.actualValue; }
  void setQuestionAnswering(QuestionAnsweringMode newVal) { _questionAnswering.actualValue = newVal; }

  bool globalSubsumption() const { return _globalSubsumption.actualValue; }
  /** true if calling set() on non-existing options does not result in a user error */
  bool ignoreMissing() const { return _ignoreMissing.actualValue; }
  /** set the "ignore missing options" value to true or false */
  //void setIgnoreMissing(bool newVal) { _ignoreMissing = newVal; }
  bool increasedNumeralWeight() const { return _increasedNumeralWeight.actualValue; }
  bool theoryAxioms() const { return _theoryAxioms.actualValue; }
  //void setTheoryAxioms(bool newValue) { _theoryAxioms = newValue; }
  bool interpretedSimplification() const { return _interpretedSimplification.actualValue; }
  //void setInterpretedSimplification(bool val) { _interpretedSimplification = val; }
  Condensation condensation() const { return _condensation.actualValue; }
  RuleActivity generalSplitting() const { return _generalSplitting.actualValue; }
  vstring namePrefix() const { return _namePrefix.actualValue; }
  bool timeStatistics() const { return _timeStatistics.actualValue; }
  bool splitting() const { return _splitting.actualValue; }
  bool nonliteralsInClauseWeight() const { return _nonliteralsInClauseWeight.actualValue; }
  unsigned sineDepth() const { return _sineDepth.actualValue; }
  unsigned sineGeneralityThreshold() const { return _sineGeneralityThreshold.actualValue; }
  SineSelection sineSelection() const { return _sineSelection.actualValue; }
  void setSineSelection(SineSelection val) { _sineSelection.actualValue=val; }
  float sineTolerance() const { return _sineTolerance.actualValue; }
  bool smtlibConsiderIntsReal() const { return _smtlibConsiderIntsReal.actualValue; }
  //void setSmtlibConsiderIntsReal( bool newVal ) { _smtlibConsiderIntsReal = newVal; }
  bool smtlibFletAsDefinition() const { return _smtlibFletAsDefinition.actualValue; }
  bool smtlibIntroduceAIGNames() const { return _smtlibIntroduceAIGNames.actualValue; }

  bool colorUnblocking() const { return _colorUnblocking.actualValue; }
  bool distinctProcessor() const { return _distinctProcessor.actualValue; }
  bool hornRevealing() const { return _hornRevealing.actualValue; }
  bool trivialPredicateRemoval() const { return _trivialPredicateRemoval.actualValue; }

  bool tabulationBwRuleSubsumptionResolutionByLemmas() const { return _tabulationBwRuleSubsumptionResolutionByLemmas.actualValue; }
  bool tabulationFwRuleSubsumptionResolutionByLemmas() const { return _tabulationFwRuleSubsumptionResolutionByLemmas.actualValue; }
  int tabulationGoalAgeRatio() const { return _tabulationGoalAgeWeightRatio.actualValue; }
  int tabulationGoalWeightRatio() const { return _tabulationGoalAgeWeightRatio.otherValue; }
  int tabulationGoalRatio() const { return _tabulationGoalLemmaRatio.actualValue; }
  int tabulationLemmaRatio() const { return _tabulationGoalLemmaRatio.otherValue; }
  bool tabulationInstantiateProducingRules() const { return _tabulationInstantiateProducingRules.actualValue; }
  int tabulationLemmaAgeRatio() const { return _tabulationLemmaAgeWeightRatio.actualValue; }
  int tabulationLemmaWeightRatio() const { return _tabulationLemmaAgeWeightRatio.otherValue; }

  float instGenBigRestartRatio() const { return _instGenBigRestartRatio.actualValue; }
  bool instGenInprocessing() const { return _instGenInprocessing.actualValue; }
  bool instGenPassiveReactivation() const { return _instGenPassiveReactivation.actualValue; }
  int instGenResolutionRatioInstGen() const { return _instGenResolutionInstGenRatio.actualValue; }
  int instGenResolutionRatioResolution() const { return _instGenResolutionInstGenRatio.otherValue; }
  int instGenRestartPeriod() const { return _instGenRestartPeriod.actualValue; }
  float instGenRestartPeriodQuotient() const { return _instGenRestartPeriodQuotient.actualValue; }
  int instGenSelection() const { return _instGenSelection.actualValue; }
  bool instGenWithResolution() const { return _instGenWithResolution.actualValue; }

  float satClauseActivityDecay() const { return _satClauseActivityDecay.actualValue; }
  SatClauseDisposer satClauseDisposer() const { return _satClauseDisposer.actualValue; }
  bool satLearntMinimization() const { return _satLearntMinimization.actualValue; }
  bool satLearntSubsumptionResolution() const { return _satLearntSubsumptionResolution.actualValue; }
  int satRestartFixedCount() const { return _satRestartFixedCount.actualValue; }
  float satRestartGeometricIncrease() const { return _satRestartGeometricIncrease.actualValue; }
  int satRestartGeometricInit() const { return _satRestartGeometricInit.actualValue; }
  int satRestartLubyFactor() const { return _satRestartLubyFactor.actualValue; }
  float satRestartMinisatIncrease() const { return _satRestartMinisatIncrease.actualValue; }
  int satRestartMinisatInit() const { return _satRestartMinisatInit.actualValue; }
  SatRestartStrategy satRestartStrategy() const { return _satRestartStrategy.actualValue; }
  float satVarActivityDecay() const { return _satVarActivityDecay.actualValue; }
  SatVarSelector satVarSelector() const { return _satVarSelector.actualValue; }

  Niceness nicenessOption() const { return _nicenessOption.actualValue; }

  void setMemoryLimit(size_t newVal) { _memoryLimit.actualValue = newVal; }
  
  void setTimeLimitInSeconds(int newVal) { _timeLimitInDeciseconds.actualValue = 10*newVal; }
  void setTimeLimitInDeciseconds(int newVal) { _timeLimitInDeciseconds.actualValue = newVal; }
  int getTimeLimit(){return _timeLimitInDeciseconds.actualValue;}
  int getWhileNumber(){return _whileNumber.actualValue;}
  int getFunctionNumber(){return _functionNumber.actualValue;}

  int nonGoalWeightCoeffitientNumerator() const { return _nonGoalWeightCoefficient.numerator; }
  int nonGoalWeightCoeffitientDenominator() const { return _nonGoalWeightCoefficient.denominator; }

  SSplittingNonsplittableComponents ssplittingNonsplittableComponents() const { return _ssplittingNonsplittableComponents.actualValue; }
  SSplittingComponentSweeping ssplittingComponentSweeping() const { return _ssplittingComponentSweeping.actualValue; }
  SSplittingAddComplementary ssplittingAddComplementary() const { return _ssplittingAddComplementary.actualValue; }
  int ssplittingFlushPeriod() const { return _ssplittingFlushPeriod.actualValue; }
  float ssplittingFlushQuotient() const { return _ssplittingFlushQuotient.actualValue; }
  bool ssplittingEagerRemoval() const { return _ssplittingEagerRemoval.actualValue; }
  bool ssplittingCongruenceClosure() const { return _ssplittingCongruenceClosure.actualValue; }

  void setProof(Proof p) { _proof.actualValue = p; }
  bool bpEquivalentVariableRemoval() const { return _equivalentVariableRemoval.actualValue; }
  unsigned bpMaximalPropagatedEqualityLength() const { return _maximalPropagatedEqualityLength.actualValue; }
  BPAlmostHalfBoundingRemoval bpAlmostHalfBoundingRemoval() const {return _bpAlmostHalfBoundingRemoval.actualValue;}
  bool bpFmElimination () const {return _bpFmElimination.actualValue;}
  unsigned bpAllowedFMBalance() const { return _bpAllowedFMBalance.actualValue; }
  BPAssignmentSelector bpAssignmentSelector() const {return _bpAssignmentSelector.actualValue; }
  bool bpCollapsingPropagation() const {return _bpCollapsingPropagation.actualValue; }
  unsigned bpUpdatesByOneConstraint() const {return _updatesByOneConstraint.actualValue; }
  bool bpConservativeAssignmentSelection() const {return _bpConservativeAssignmentSelection.actualValue; }
  BPConflictSelector bpConflictSelector() const {return _bpConflictSelector.actualValue; }
  bool backjumpTargetIsDecisionPoint() const { return _backjumpTargetIsDecisionPoint.actualValue; }
  bool bpPropagateAfterConflict() const {return _bpPropagateAfterConflict.actualValue; }
  BPVariableSelector bpVariableSelector() const {return _bpVariableSelector.actualValue; }
  bool bpSelectUnusedVariablesFirst() const {return _selectUnusedVariablesFirst.actualValue; }
  bool bpStartWithPrecise() const { return _bpStartWithPrecise.actualValue; }
  bool bpStartWithRational() const { return _bpStartWithRational.actualValue;}
  

    
private:
    //==========================================================
    // Variables holding option values
    //==========================================================

    /**
     * TODO: this uses a linear search, for alternative see NameArray 
     *
     * @author Giles
     * @since 30/07/14
     */
    struct OptionValues{
        
        OptionValues(){ };
        OptionValues(std::initializer_list<vstring> list){
          for(std::initializer_list<vstring>::iterator it = list.begin();
              it!=list.end();++it){
              names.push(*it);
              ASS((*it).size()<70); // or else cannot be printed on a line
          }
        }

        int find(vstring value) const {
          for(unsigned i=0;i<names.length();i++){
             if(value.compare(names[i])==0) return i;
          }
          return -1;
        }
        const int length() const { return names.length(); }
        const vstring operator[](int i) const{ return names[i];}

    private:
      Stack<vstring> names;
    };

    // Declare constraints here so they can be refered to, but define them below
    template<typename T>
    struct OptionValueConstraint;
    template<typename T>
    struct WrappedConstraint;
    struct OptionProblemConstraint;
    
   /**
    * OptionValues store information about options, including their value
    */
    struct AbstractOptionValue{

        CLASS_NAME(AbstractOptionValue);
        USE_ALLOCATOR(AbstractOptionValue);

        AbstractOptionValue(){}
        AbstractOptionValue(vstring l,vstring s) :
          longName(l), shortName(s), experimental(false), _should_copy(true), _tag(OptionTag::LAST_TAG) {}

        // Never copy an OptionValue... the Constraint system would break
        AbstractOptionValue(const AbstractOptionValue& that){ ASSERTION_VIOLATION; }
        public:

        virtual bool set(const vstring& value) = 0;
        void setExperimental(){experimental=true;}

        vstring longName;
        vstring shortName;
        vstring description;
        bool experimental;

        virtual bool checkConstraints() = 0;
        virtual bool checkProblemConstraints(Property& prop) = 0;

       void tag(OptionTag tag){ ASS(_tag==OptionTag::LAST_TAG);_tag=tag; }
       void tag(Mode mode){ _modes.push(mode); }
       
       OptionTag getTag(){ return _tag;}
       bool inMode(Mode mode){
         if(_modes.isEmpty()) return true;
         else return _modes.find(mode);
       }

       virtual vstring getStringOfActual() const = 0; 
       virtual void output(vstringstream& out) const {
         out << "--" << longName;
         if(!shortName.empty()){ out << " (-"<<shortName<<")"; }
         out << endl; 

         if(!description.empty()){
           // Break a the description into lines where there have been at least 70 characters
           // on the line at the next space
           out << "\t";
           int count=0;
           for(const char* p = description.c_str();*p;p++){
             out << *p; 
             count++;
             if(count>70 && *p==' '){
               out << endl << '\t';
               count=0;
             }
             if(*p=='\n'){ count=0; out << '\t'; }
           }
           out << endl;
         }
         else{ out << "\tno description provided!" << endl; }
       }

      bool _should_copy;
      bool shouldCopy() const { return _should_copy; }


    private:
      OptionTag _tag;
      Lib::Stack<Mode> _modes;

    };
    
    template<typename T>
    struct OptionValue : public AbstractOptionValue {

        CLASS_NAME(OptionValue);
        USE_ALLOCATOR(OptionValue);

        OptionValue(){}
        OptionValue(vstring l, vstring s,T def) : AbstractOptionValue(l,s), 
          defaultValue(def), actualValue(def) {}

        T defaultValue;
        T actualValue;

      virtual vstring getStringOfValue(T value) const{ ASSERTION_VIOLATION;} 
      virtual vstring getStringOfActual() const { return getStringOfValue(actualValue); }

      // Adding and checking constraints
      void addConstraint(OptionValueConstraint<T>* c){ _constraints.push(c); }
      template<typename S>
      void addConstraintIfNotDefault(WrappedConstraint<S>* c){
        _constraints.push(If(isNotDefault<T>()).then(c));
      }
      void addConstraintIfNotDefault(OptionValueConstraint<T>* c){
        _constraints.push(If(isNotDefault<T>()).then(c));
      }
      bool checkConstraints();

      WrappedConstraint<T>* is(OptionValueConstraint<T>* c);

      void addProblemConstraint(OptionProblemConstraint* c){ _prob_constraints.push(c); }
      virtual bool checkProblemConstraints(Property& prop);

      virtual void output(vstringstream& out) const {
        AbstractOptionValue::output(out);
        out << "\tdefault: " << getStringOfValue(defaultValue) << endl;
      }      

      private:
        //TODO add destructor to delete constraints
        Lib::Stack<OptionValueConstraint<T>*> _constraints;
        Lib::Stack<OptionProblemConstraint*> _prob_constraints;

    };


    template<typename T>
    struct ChoiceOptionValue : public OptionValue<T> {

      CLASS_NAME(ChoiceOptionValue);
      USE_ALLOCATOR(ChoiceOptionValue);

      ChoiceOptionValue(){}
      ChoiceOptionValue(vstring l, vstring s,T def,OptionValues c) :
          OptionValue<T>(l,s,def), choices(c) {} 

      bool set(const vstring& value){
        // makes reasonable assumption about ordering of every enum
        int index = choices.find(value.c_str());
        if(index<0) return false;
        this->actualValue = static_cast<T>(index);
        return true;
      }

      virtual void output(vstringstream& out) const {
        AbstractOptionValue::output(out);
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
            if(next.size()+count>60){ // next.size() will be <70, how big is a tab?
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
      OptionValues choices;
    };

    struct BoolOptionValue : public OptionValue<bool> {
      BoolOptionValue(){}
      BoolOptionValue(vstring l,vstring s, bool d) : OptionValue(l,s,d){} 
      bool set(const vstring& value){
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
      bool set(const vstring& value){
        return Int::stringToInt(value.c_str(),actualValue);
      }
      vstring getStringOfValue(int value) const{ return Lib::Int::toString(value); }
    };

    struct UnsignedOptionValue : public OptionValue<unsigned> {
      UnsignedOptionValue(){}
      UnsignedOptionValue(vstring l,vstring s, unsigned d) : OptionValue(l,s,d){} 
      bool set(const vstring& value){
        return Int::stringToUnsignedInt(value.c_str(),actualValue);
      }
      vstring getStringOfValue(unsigned value) const{ return Lib::Int::toString(value); }
    }; 

    struct StringOptionValue : public OptionValue<vstring> {
      StringOptionValue(){}
      StringOptionValue(vstring l,vstring s, vstring d) : OptionValue(l,s,d){} 
      // Is reference safe here?
      bool set(const vstring& value){ 
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
      bool set(const vstring& value){
        return Int::stringToLong(value.c_str(),actualValue);
      }
      vstring getStringOfValue(long value) const{ return Lib::Int::toString(value); }
    };

    struct FloatOptionValue : public OptionValue<float>{
      FloatOptionValue(){}
      FloatOptionValue(vstring l,vstring s, float d) : OptionValue(l,s,d){} 
      bool set(const vstring& value){
        return Int::stringToFloat(value.c_str(),actualValue);
      }
      vstring getStringOfValue(float value) const{ return Lib::Int::toString(value); }
    };
 
    struct RatioOptionValue : public OptionValue<int> {

        CLASS_NAME(RatioOptionValue);
        USE_ALLOCATOR(RatioOptionValue);

        RatioOptionValue(){}
        RatioOptionValue(vstring l, vstring s, int def, int other, char sp=':') :
          OptionValue(l,s,def), sep(sp), defaultOtherValue(other), otherValue(other) {};

      template<typename S>
      void addConstraintIfNotDefault(WrappedConstraint<S>* c){
        addConstraint(If(isNotDefaultRatio()).then(c));
      }

        bool readRatio(const char* val,char seperator);
        bool set(const vstring& value){
          return readRatio(value.c_str(),sep);
        }

        char sep;
        int defaultOtherValue;
        int otherValue;

        virtual void output(vstringstream& out) const {
          AbstractOptionValue::output(out);
          out << "\tdefault left: " << defaultValue << endl;
          out << "\tdefault right: " << defaultOtherValue << endl;
        }

        virtual vstring getStringOfValue(int value) const{ ASSERTION_VIOLATION;}
        virtual vstring getStringOfActual() const{ 
          return Lib::Int::toString(actualValue)+sep+Lib::Int::toString(otherValue); 
        }

    };
    
    struct NonGoalWeightOptionValue : public OptionValue<float>{

        CLASS_NAME(NonGoalWeightOptionValue);
        USE_ALLOCATOR(NonGoalWeightOptionValue);

        NonGoalWeightOptionValue(){}
        NonGoalWeightOptionValue(vstring l, vstring s, float def) :
        OptionValue(l,s,def), numerator(1), denominator(1) {};
        
        bool set(const vstring& value);
        
        // output does not output numerator and denominator as they
        // are produced from defaultValue
        int numerator;
        int denominator;

        virtual vstring getStringOfValue(float value) const{ return Lib::Int::toString(value); }
    };
    
    // Feels like it should be an enum
    struct SelectionOptionValue : public OptionValue<int>{
        SelectionOptionValue(){}
        SelectionOptionValue(vstring l,vstring s, int def):
        OptionValue(l,s,def){};
        
        bool set(const vstring& value);
        
        virtual void output(vstringstream& out) const {
            AbstractOptionValue::output(out);
            out << "\tdefault: " << defaultValue << endl;;
        }

        virtual vstring getStringOfValue(int value) const{ return Lib::Int::toString(value); }
    };
    
    struct InputFileOptionValue : public OptionValue<vstring>{
        InputFileOptionValue(){}
        InputFileOptionValue(vstring l,vstring s, vstring def,Options* p):
        OptionValue(l,s,def), parent(p){};
        
        bool set(const vstring& value);
        
        virtual void output(vstringstream& out) const {
            AbstractOptionValue::output(out);
            out << "\tdefault: " << defaultValue << endl;;
        }
        virtual vstring getStringOfValue(vstring value) const{ return value; }
    private:
      Options* parent;
 
    };
   
    struct DecodeOptionValue : public OptionValue<vstring>{
        DecodeOptionValue(){ AbstractOptionValue::_should_copy=false;}
        DecodeOptionValue(vstring l,vstring s,Options* p):
          OptionValue(l,s,""), parent(p){ AbstractOptionValue::_should_copy=false;}

        bool set(const vstring& value){
          parent->readFromTestId(value);
          return true;
        }
        virtual vstring getStringOfValue(vstring value) const{ return value; }

      private:
        Options* parent;

    };

    struct TimeLimitOptionValue : public OptionValue<int>{
        TimeLimitOptionValue(){}
        TimeLimitOptionValue(vstring l, vstring s, float def) :
        OptionValue(l,s,def) {};
        
        bool set(const vstring& value);
        
        virtual void output(vstringstream& out) const {
            AbstractOptionValue::output(out);
            out << "\tdefault: " << defaultValue << endl;;
        }
        virtual vstring getStringOfValue(int value) const{ return Lib::Int::toString(value); }
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
    * may need to be added. In this case see examples from AddWrapper below. 
    *
    */
    template<typename T>
    struct WrappedConstraint;

    template<typename T>
    struct OptionValueConstraint{
        CLASS_NAME(OptionValueConstraint);
        USE_ALLOCATOR(OptionValueConstraint);
        virtual bool check(OptionValue<T>& value) = 0; 
        virtual bool check(){ ASSERTION_VIOLATION; }
        virtual vstring msg(OptionValue<T>& value) = 0;
        virtual vstring msg() { ASSERTION_VIOLATION; }

        // By default cannot force constraint
        virtual bool force(OptionValue<T>& value){ return false;}
        // TODO - allow for hard constraints
        virtual bool isHard(){ return false; }

        OptionValueConstraint<T>* And(OptionValueConstraint<T>* another);
        OptionValueConstraint<T>* Or(OptionValueConstraint<T>* another);

        template<typename S>
        OptionValueConstraint<T>* And(WrappedConstraint<S>* another);
        template<typename S>
        OptionValueConstraint<T>* Or(WrappedConstraint<S>* another);
        
    };


    // A Wrapped Constraint takes an OptionValue and a Constraint
    // It allows us to supply a constraint on another OptionValue in an If constraint for example
    template<typename T>
    struct WrappedConstraint{ 
        CLASS_NAME(WrappedConstraint);
        USE_ALLOCATOR(WrappedConstraint);

        WrappedConstraint(OptionValue<T>* v, OptionValueConstraint<T>* c) : value(v), con(c) {}

        bool check(){
            return con->check(*value);
        }
        vstring msg(){
            return con->msg(*value);
        }

        template<typename S, typename R>
        OptionValueConstraint<S>* And(WrappedConstraint<R>* another);

        OptionValue<T>* value;
        OptionValueConstraint<T>* con;
    };

    template<typename T, typename S>
    struct UnWrappedConstraint : public OptionValueConstraint<T>{
      CLASS_NAME(UnWrappedConstraint);
      USE_ALLOCATOR(UnWrappedConstraint);

      UnWrappedConstraint(WrappedConstraint<S>* c) : con(c) {}

      bool check(OptionValue<T>&){ return con->check(); }
      vstring msg(OptionValue<T>&){ return con->msg(); }
      
      WrappedConstraint<S>* con;
    };

    template<typename T>
    struct OrWrapper : public OptionValueConstraint<T>{
       CLASS_NAME(OrWrapper);
       USE_ALLOCATOR(OrWrapper);
       OrWrapper(OptionValueConstraint<T>* l, OptionValueConstraint<T>* r) : left(l),right(r) {}
       bool check(OptionValue<T>& value){
         return left->check(value) || right->check(value);
       }
       vstring msg(OptionValue<T>& value){ return left->msg(value) + " or " + right->msg(value); }

       OptionValueConstraint<T>* left;
       OptionValueConstraint<T>* right;
    };

    template<typename T>
    struct AndWrapper : public OptionValueConstraint<T>{
       CLASS_NAME(AndWrapper);
       USE_ALLOCATOR(AndWrapper);
       AndWrapper(OptionValueConstraint<T>* l, OptionValueConstraint<T>* r) : left(l),right(r) {}
       bool check(OptionValue<T>& value){
          return left->check(value) && right->check(value);
       }
       vstring msg(OptionValue<T>& value){ return left->msg(value) + " and " + right->msg(value); }

       OptionValueConstraint<T>* left;
       OptionValueConstraint<T>* right;
    };

    // Add a constraint to a boolean option that only holds when the option is on
    struct OnAnd : public OptionValueConstraint<bool>{
        CLASS_NAME(OnAnd);
        USE_ALLOCATOR(OnAnd);
       OnAnd(OptionValueConstraint<bool>* other) : _other(other) {}
       bool check(OptionValue<bool>& value){
          if(value.actualValue) return _other->check(value);
          return true;
       }
       vstring msg(OptionValue<bool>& value){ return value.longName+"("+value.getStringOfActual()+") is on and "+_other->msg(value); }
       OptionValueConstraint<bool>* _other;
    };

    template<typename T>
    struct RequiresCompleteForNonHorn : public OptionValueConstraint<T>{
       CLASS_NAME(RequiresCompleteForNonHorn);
       USE_ALLOCATOR(RequiresCompleteForNonHorn);
       RequiresCompleteForNonHorn(){}
       bool check(OptionValue<T>& value);
       vstring msg(OptionValue<T>& value){ return value.longName+"("+value.getStringOfActual()+") is complete for non-horn"; }
    }; 

    template<typename T>
    struct Equal : public OptionValueConstraint<T>{
       CLASS_NAME(Equal);
       USE_ALLOCATOR(Equal);
       Equal(T gv) : _goodvalue(gv) {}
       bool check(OptionValue<T>& value){
         return value.actualValue == _goodvalue;
       }
       vstring msg(OptionValue<T>& value){ 
         return value.longName+"("+value.getStringOfActual()+") is equal to " + value.getStringOfValue(_goodvalue); 
       }
       T _goodvalue;
    };
    template<typename T>
    static OptionValueConstraint<T>* equal(T bv){
        return new Equal<T>(bv);
    }

    template<typename T>
    struct NotEqual : public OptionValueConstraint<T>{
       CLASS_NAME(NotEqual);
       USE_ALLOCATOR(NotEqual);
       NotEqual(T bv) : _badvalue(bv) {}
       bool check(OptionValue<T>& value){
         return value.actualValue != _badvalue;
       }
       vstring msg(OptionValue<T>& value){ return value.longName+"("+value.getStringOfActual()+") is not equal to " + value.getStringOfValue(_badvalue); }
       T _badvalue;
    };
    template<typename T>
    static OptionValueConstraint<T>* notEqual(T bv){
        return new NotEqual<T>(bv);
    }

    // Constraint that the value should be less than a given value
    // optionally we can allow it be equal to that value also
    template<typename T>
    struct LessThan : public OptionValueConstraint<T>{
       CLASS_NAME(LessThan);
       USE_ALLOCATOR(LessThan);
       LessThan(T gv,bool eq=false) : _goodvalue(gv), _orequal(eq) {}
       bool check(OptionValue<T>& value){
         return (value.actualValue < _goodvalue || (_orequal && value.actualValue==_goodvalue));
       }
       vstring msg(OptionValue<T>& value){
         if(_orequal) return value.longName+"("+value.getStringOfActual()+") is less than or equal to " + value.getStringOfValue(_goodvalue);
         return value.longName+"("+value.getStringOfActual()+") is less than "+ value.getStringOfValue(_goodvalue);
       }

       T _goodvalue;
       bool _orequal;
    };
    template<typename T>
    static OptionValueConstraint<T>* lessThan(T bv){
        return new LessThan<T>(bv,false);
    }
    template<typename T>
    static OptionValueConstraint<T>* lessThanEq(T bv){
        return new LessThan<T>(bv,true);
    }

    // Constraint that the value should be greater than a given value
    // optionally we can allow it be equal to that value also
    template<typename T>
    struct GreaterThan : public OptionValueConstraint<T>{
       CLASS_NAME(GreaterThan);
       USE_ALLOCATOR(GreaterThan);
       GreaterThan(T gv,bool eq=false) : _goodvalue(gv), _orequal(eq) {}
       bool check(OptionValue<T>& value){
         return (value.actualValue > _goodvalue || (_orequal && value.actualValue==_goodvalue));
       }

       vstring msg(OptionValue<T>& value){
         if(_orequal) return value.longName+"("+value.getStringOfActual()+") is greater than or equal to " + value.getStringOfValue(_goodvalue);
         return value.longName+"("+value.getStringOfActual()+") is greater than "+ value.getStringOfValue(_goodvalue);
       }

       T _goodvalue;
       bool _orequal;
    };
    template<typename T>
    static OptionValueConstraint<T>* greaterThan(T bv){
        return new GreaterThan<T>(bv,false);
    }
    template<typename T>
    static OptionValueConstraint<T>* greaterThanEq(T bv){
        return new GreaterThan<T>(bv,true);
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

       IfThenConstraint(OptionValueConstraint<T>* ic, OptionValueConstraint<T>* c) :
         if_con(ic), then_con(c) {} 

       bool check(OptionValue<T>& value){
           ASS(then_con);
           return !if_con->check(value) || then_con->check(value); 
       }

       vstring msg(OptionValue<T>& value){
         return "if "+if_con->msg(value)+" then "+ then_con->msg(value);
       }

       OptionValueConstraint<T>* if_con;
       OptionValueConstraint<T>* then_con;
    };

    template<typename T>
    struct IfConstraint {
       CLASS_NAME(IfConstraint);
       USE_ALLOCATOR(IfConstraint);
       IfConstraint(OptionValueConstraint<T>* c) :if_con(c) {}

       OptionValueConstraint<T>* then(OptionValueConstraint<T>* c){
         return new IfThenConstraint<T>(if_con,c);  
       }
       template<typename S>
       OptionValueConstraint<T>* then(WrappedConstraint<S>* c){
         return new IfThenConstraint<T>(if_con,new UnWrappedConstraint<T,S>(c));  
       }

       OptionValueConstraint<T>* if_con;
    };

    template<typename T>
    static IfConstraint<T> If(OptionValueConstraint<T>* c){
        return IfConstraint<T>(c);
    }
  /**
   * Default Value constraints
   */

    template<typename T>
    struct NotDefaultConstraint : public OptionValueConstraint<T> { 
        NotDefaultConstraint() {}

        bool check(OptionValue<T>& value){
          return value.defaultValue != value.actualValue;
        }
        vstring msg(OptionValue<T>& value) { return value.longName+"("+value.getStringOfActual()+") is not default("+value.getStringOfValue(value.defaultValue)+")";}
    };
    struct NotDefaultRatioConstraint : public OptionValueConstraint<int> {
        NotDefaultRatioConstraint() {}
      
        bool check(OptionValue<int>& value){
            RatioOptionValue& rvalue = static_cast<RatioOptionValue&>(value);
            return (rvalue.defaultValue != rvalue.actualValue || 
               rvalue.defaultOtherValue != rvalue.otherValue);
        }
        vstring msg(OptionValue<int>& value) { return value.longName+"("+value.getStringOfActual()+") is not default";}

    };

    // You will need to provide the type, optionally use addConstraintIfNotDefault
    template<typename T>
    static OptionValueConstraint<T>* isNotDefault(){
        return new NotDefaultConstraint<T>();
    }
    // You will need to provide the type, optionally use addConstraintIfNotDefault
    static OptionValueConstraint<int>* isNotDefaultRatio(){
        return new NotDefaultRatioConstraint();
    }


   /**
    * NOTE on OptionProblemConstraint
    * 
    * OptionProblemConstraints are used to capture properties of a problem that
    * should be present when an option is used. The idea being that a warning will
    * be emited if an option is used for an inappropriate problem.
    *
    * TODO - this element of Options is still under development
    */

    struct OptionProblemConstraint{
       virtual bool check(Property& p) = 0;
       virtual vstring msg() = 0;
    };

    struct HasCategory : OptionProblemConstraint{
       HasCategory(Property::Category c) : cat(c) {}
       bool check(Property&p){
          return p.category()==cat;
       }
       vstring msg(){ return " not useful for property in category "+cat; }
       Property::Category cat;
    };

   /**
    *
    */
    struct LookupWrapper {
        
        LookupWrapper() {}

        // When copying a lookup wrapper do not copy any of its contents
        // The copy constructor for Options recreates the LookupWrapper
        LookupWrapper operator=(const LookupWrapper&){ return LookupWrapper(); } 

        void insert(AbstractOptionValue* option_value){
            CALL("LookupWrapper::insert");
            ASS(!option_value->longName.empty());
            bool new_long =  _longMap.insert(option_value->longName,option_value);
            bool new_short = true;
            if(!option_value->shortName.empty()){ 
              new_short = _shortMap.insert(option_value->shortName,option_value);
            }
            //if(!new_long || !new_short){ cout << "Bad " << option_value->longName << endl; }
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
    return _lookup.findLong(name);
  }
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

  RatioOptionValue _ageWeightRatio;
  BoolOptionValue _aigBddSweeping;
  BoolOptionValue _aigConditionalRewriting;
  BoolOptionValue _aigDefinitionIntroduction;
  UnsignedOptionValue _aigDefinitionIntroductionThreshold;
  BoolOptionValue _aigFormulaSharing;
  BoolOptionValue _aigInliner;
  BoolOptionValue _arityCheck;
  
  BoolOptionValue _backjumpTargetIsDecisionPoint;
  ChoiceOptionValue<BadOption> _badOption;
  ChoiceOptionValue<Demodulation> _backwardDemodulation;
  ChoiceOptionValue<Subsumption> _backwardSubsumption;
  ChoiceOptionValue<Subsumption> _backwardSubsumptionResolution;
  BoolOptionValue _bfnt;
  BoolOptionValue _binaryResolution;
  BoolOptionValue _bpCollapsingPropagation;
  UnsignedOptionValue _bpAllowedFMBalance;
  ChoiceOptionValue<BPAlmostHalfBoundingRemoval> _bpAlmostHalfBoundingRemoval;
  ChoiceOptionValue<BPAssignmentSelector> _bpAssignmentSelector;
  ChoiceOptionValue<BPConflictSelector> _bpConflictSelector;
  BoolOptionValue _bpConservativeAssignmentSelection;
  BoolOptionValue _bpFmElimination;
  BoolOptionValue _bpPropagateAfterConflict;
  BoolOptionValue _bpStartWithPrecise;
  BoolOptionValue _bpStartWithRational;
  ChoiceOptionValue<BPVariableSelector> _bpVariableSelector;

  BoolOptionValue _colorUnblocking;
  ChoiceOptionValue<Condensation> _condensation;

  BoolOptionValue _demodulationRedundancyCheck;
  BoolOptionValue _distinctProcessor;

  BoolOptionValue _eprPreservingNaming;
  BoolOptionValue _eprPreservingSkolemization;
  BoolOptionValue _eprRestoringInlining;
  BoolOptionValue _equalityPropagation;
  ChoiceOptionValue<EqualityProxy> _equalityProxy;
  ChoiceOptionValue<RuleActivity> _equalityResolutionWithDeletion;
  BoolOptionValue _equivalentVariableRemoval;
  ChoiceOptionValue<ExtensionalityResolution> _extensionalityResolution;
  UnsignedOptionValue _extensionalityMaxLength;
  BoolOptionValue _extensionalityAllowPosEq;
  
  BoolOptionValue _flattenTopLevelConjunctions;
  StringOptionValue _forbiddenOptions;
  BoolOptionValue _forceIncompleteness;
  StringOptionValue _forcedOptions;
  ChoiceOptionValue<Demodulation> _forwardDemodulation;
  BoolOptionValue _forwardLiteralRewriting;
  BoolOptionValue _forwardSubsumption;
  BoolOptionValue _forwardSubsumptionResolution;
  ChoiceOptionValue<FunctionDefinitionElimination> _functionDefinitionElimination;
  IntOptionValue _functionNumber;
  
  ChoiceOptionValue<RuleActivity> _generalSplitting;
  BoolOptionValue _globalSubsumption;

  BoolOptionValue _hornRevealing;
  BoolOptionValue _hyperSuperposition;

  /** if true, then calling set() on non-existing options will not result in a user error */
  BoolOptionValue _ignoreMissing;
  StringOptionValue _include;
  /** if this option is true, Vampire will add the numeral weight of a clause
   * to its weight. The weight is defined as the sum of binary sizes of all
   * integers occurring in this clause. This option has not been tested and
   * may be extensive, see Clause::getNumeralWeight()
   */
  BoolOptionValue _increasedNumeralWeight;
  IntOptionValue _inequalitySplitting;
  ChoiceOptionValue<InputSyntax> _inputSyntax;
  FloatOptionValue _instGenBigRestartRatio;
  BoolOptionValue _instGenInprocessing;
  BoolOptionValue _instGenPassiveReactivation;
  RatioOptionValue _instGenResolutionInstGenRatio;
  //IntOptionValue _instGenResolutionRatioResolution;
  IntOptionValue _instGenRestartPeriod;
  FloatOptionValue _instGenRestartPeriodQuotient;
  BoolOptionValue _instGenWithResolution;
  BoolOptionValue _interpretedSimplification;

  StringOptionValue _latexOutput;
  BoolOptionValue _latexUseDefaultSymbols;
  StringOptionValue _lingvaAdditionalInvariants;

  ChoiceOptionValue<LiteralComparisonMode> _literalComparisonMode;
  StringOptionValue _logFile;
  IntOptionValue _lrsFirstTimeCheck;
  BoolOptionValue _lrsWeightLimitOnly;

  LongOptionValue _maxActive;
  IntOptionValue _maxAnswers;
  IntOptionValue _maxInferenceDepth;
  LongOptionValue _maxPassive;
  IntOptionValue _maxWeight;
  UnsignedOptionValue _maximalPropagatedEqualityLength;
  UnsignedOptionValue _memoryLimit; // should be size_t, making an assumption
  ChoiceOptionValue<Mode> _mode;

  StringOptionValue _namePrefix;
  IntOptionValue _naming;
  ChoiceOptionValue<Niceness> _nicenessOption;
  BoolOptionValue _nonliteralsInClauseWeight;
  BoolOptionValue _normalize;

  BoolOptionValue _outputAxiomNames;

  ChoiceOptionValue<InliningMode> _predicateDefinitionInlining;
  BoolOptionValue _predicateDefinitionMerging;
  ChoiceOptionValue<PredicateEquivalenceDiscoveryMode> _predicateEquivalenceDiscovery;
  BoolOptionValue _predicateEquivalenceDiscoveryAddImplications;
  BoolOptionValue _predicateEquivalenceDiscoveryRandomSimulation;
  IntOptionValue _predicateEquivalenceDiscoverySatConflictLimit;
  BoolOptionValue _predicateIndexIntroduction;
  BoolOptionValue _printClausifierPremises;
  StringOptionValue _problemName;
  ChoiceOptionValue<Proof> _proof;
  BoolOptionValue _proofChecking;
  
  StringOptionValue _protectedPrefix;

  ChoiceOptionValue<QuestionAnsweringMode> _questionAnswering;

  IntOptionValue _randomSeed;
  IntOptionValue _rowVariableMaxLength;

  FloatOptionValue _satClauseActivityDecay;
  ChoiceOptionValue<SatClauseDisposer> _satClauseDisposer;
  BoolOptionValue _satLearntMinimization;
  BoolOptionValue _satLearntSubsumptionResolution;
  IntOptionValue _satRestartFixedCount;
  FloatOptionValue _satRestartGeometricIncrease;
  IntOptionValue _satRestartGeometricInit;
  IntOptionValue _satRestartLubyFactor;
  FloatOptionValue _satRestartMinisatIncrease;
  IntOptionValue _satRestartMinisatInit;
  ChoiceOptionValue<SatRestartStrategy> _satRestartStrategy;
  FloatOptionValue _satVarActivityDecay;
  ChoiceOptionValue<SatVarSelector> _satVarSelector;
  ChoiceOptionValue<SatSolver> _satSolver;
  BoolOptionValue _satLingelingSimilarModels;
  BoolOptionValue _satLingelingIncremental;
  ChoiceOptionValue<SaturationAlgorithm> _saturationAlgorithm;
  BoolOptionValue _selectUnusedVariablesFirst;
  BoolOptionValue _showActive;
  BoolOptionValue _showBlocked;
  BoolOptionValue _showDefinitions;
  ChoiceOptionValue<InterpolantMode> _showInterpolant;
  BoolOptionValue _showNew;
  BoolOptionValue _showNewPropositional;
  BoolOptionValue _showNonconstantSkolemFunctionTrace;
  BoolOptionValue _showOptions;
  BoolOptionValue _showExperimentalOptions;
  BoolOptionValue _showHelp;
  StringOptionValue _explainOption;
  BoolOptionValue _showPassive;
  BoolOptionValue _showPreprocessing;
  BoolOptionValue _showSkolemisations;
  BoolOptionValue _showSymbolElimination;
  BoolOptionValue _showTheoryAxioms;
  TimeLimitOptionValue _simulatedTimeLimit;
  UnsignedOptionValue _sineDepth;
  UnsignedOptionValue _sineGeneralityThreshold;
  ChoiceOptionValue<SineSelection> _sineSelection;
  FloatOptionValue _sineTolerance;
  BoolOptionValue _smtlibConsiderIntsReal;
  BoolOptionValue _smtlibFletAsDefinition;
  BoolOptionValue _smtlibIntroduceAIGNames;
  ChoiceOptionValue<Sos> _sos;
  BoolOptionValue _splitting;
  ChoiceOptionValue<SSplittingAddComplementary> _ssplittingAddComplementary;
  ChoiceOptionValue<SSplittingComponentSweeping> _ssplittingComponentSweeping;
  BoolOptionValue _ssplittingCongruenceClosure;
  BoolOptionValue _ssplittingEagerRemoval;
  UnsignedOptionValue _ssplittingFlushPeriod;
  FloatOptionValue _ssplittingFlushQuotient;
  ChoiceOptionValue<SSplittingNonsplittableComponents> _ssplittingNonsplittableComponents;
  ChoiceOptionValue<Statistics> _statistics;
  BoolOptionValue _superpositionFromVariables;
  ChoiceOptionValue<SymbolPrecedence> _symbolPrecedence;

  BoolOptionValue _tabulationBwRuleSubsumptionResolutionByLemmas;
  BoolOptionValue _tabulationFwRuleSubsumptionResolutionByLemmas;
  RatioOptionValue _tabulationGoalAgeWeightRatio;
  //IntOptionValue _tabulationGoalWeightRatio;
  RatioOptionValue _tabulationGoalLemmaRatio;
  //IntOptionValue _tabulationLemmaRatio;
  BoolOptionValue _tabulationInstantiateProducingRules;
  RatioOptionValue _tabulationLemmaAgeWeightRatio;
  //IntOptionValue _tabulationLemmaWeightRatio;
  StringOptionValue _testId;
  StringOptionValue _thanks;
  BoolOptionValue _theoryAxioms;
  /** Time limit in deciseconds */
  TimeLimitOptionValue _timeLimitInDeciseconds;
  BoolOptionValue _timeStatistics;
  BoolOptionValue _trivialPredicateRemoval;

  ChoiceOptionValue<URResolution> _unitResultingResolution;
  BoolOptionValue _unusedPredicateDefinitionRemoval;
  UnsignedOptionValue _updatesByOneConstraint;
  BoolOptionValue _use_dm;
  BoolOptionValue _weightIncrement;
  IntOptionValue _whileNumber;

  StringOptionValue _xmlOutput;

  OptionValues _tagNames;

  NonGoalWeightOptionValue _nonGoalWeightCoefficient;

  SelectionOptionValue _selection;
  SelectionOptionValue _instGenSelection;
    


  InputFileOptionValue _inputFile;

    
}; // class Options

}

#endif

