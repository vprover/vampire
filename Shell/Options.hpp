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
    void output (ostream&) const;
    void readFromTestId (vstring testId);
    void readOptionsString (vstring testId);
    vstring generateTestId() const;
    bool complete(const Problem&) const;
    bool completeForNNE() const;
    void setForcedOptionValues();
    void setInputFile(const vstring& newVal);
    void checkGlobalOptionConstraints() const;
    
    void forceIncompleteness() { _forceIncompleteness=true; }
    
    static int readTimeLimit(const char* val);
    /**
     * Return the problem name
     *
     * The problem name is computed from the input file name in
     * the @b setInputFile function. If the input file is not set,
     * the problem name is equal to "unknown". The problem name can
     * be set to a specific value using setProblemName().
     */
    vstring problemName () const { return _problemName; }
    void setProblemName(vstring str) { _problemName = str; }
    
    CLASS_NAME(Options);
    USE_ALLOCATOR(Options);
    
    /** first is option name, second option value */
    typedef pair<vstring, vstring> OptionSpec;
    typedef Stack<OptionSpec> OptionSpecStack;
    static void readOptionsString(vstring testId, OptionSpecStack& assignments);
    
    // the following two functions are used by Environment
    bool onOffToBool(const char* onOff,const char* option);
    
    // standard ways of creating options
    XMLElement toXML() const;
    bool outputSuppressed() const;
    void set(const vstring& name, const vstring& value);
    void set(const char* name, const char* value);
    void setShort(const char* name, const char* value);
    
private:
    void set(const char* name, const char* value, int index);
    
    // various read-from-string-write options
    static void readAgeWeightRatio(const char* val, int& ageRatio, int& weightRatio, char separator=':');
    static vstring boolToOnOff(bool);
    void outputValue(ostream& str,int optionTag) const;
    friend class Shell::LTB::Builder;

    
public:
  //==========================================================
  // The Enums for Option Values
  //==========================================================
  
  //enums for the bound propagation purpose
  enum BPAlmostHalfBoundingRemoval {
    AHR_BOUNDS_ONLY = 0,
    AHR_OFF = 1,
    AHR_ON = 2
  };

  enum BPAssignmentSelector{
    ASG_ALTERNATIVE = 0,
    ASG_BMP = 1,
    ASG_LOWER = 2,
    ASG_MIDDLE = 3,
    ASG_RANDOM = 4,
    ASG_RATIONAL = 5,
    ASG_SMALLEST = 6,
    ASG_TIGHT = 7,
    ASG_TIGHTISH = 8,
    ASG_UPPER = 9
  };
  
  enum BPConflictSelector{
    CS_LEAST_RECENT = 0, 
    CS_MOST_RECENT = 1, 
    CS_SHORTEST_CONSTRAINT = 2
  };
  
  enum BPVariableSelector{
    VS_CONFLICTING = 0, 
    VS_CONFLICTING_AND_COLLAPSING = 1, 
    VS_FIRST = 2, 
    VS_LOOK_AHEAD =3, 
    VS_RANDOM = 4, 
    VS_RECENTLY_CONFLICTING = 5,
    VS_RECENTLY_COLLAPSING = 6,
    VS_TIGHTEST_BOUND = 7

  };
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
    /** syntax of SMTLIB1.2 */
    IS_SMTLIB = 1,
    IS_SMTLIB2 = 2,
    /** syntax of the TPTP prover */
    IS_TPTP = 3, 
    IS_HUMAN = 4, 
    IS_MPS = 5, 
    IS_NETLIB = 6
  };

 /**
  * Possible values for show_option (used in OptionNameArray)
  * @author Giles
  */
  enum OptionTag{
    BP_TAG,
    OFF_TAG,
    GLOBAL_TAG,
    VAMPIRE_TAG
  };

  /**
   * Possible values for mode_name.
   * @since 06/05/2007 Manchester
   */
  enum Mode {
    MODE_AXIOM_SELECTION,
    MODE_BOUND_PROP,
    MODE_CASC,
    MODE_CASC_EPR,
    MODE_CASC_LTB,
    MODE_CASC_MZR,
    MODE_CASC_SAT,
    MODE_CLAUSIFY,
    MODE_CONSEQUENCE_ELIMINATION,
    MODE_GROUNDING,
    MODE_LTB_BUILD,
    MODE_LTB_SOLVE,
    /** this mode only outputs the input problem, without any preprocessing */
    MODE_OUTPUT,
    MODE_PREPROCESS,
    MODE_PROFILE,
    MODE_PROGRAM_ANALYSIS,   
    MODE_SAT, 
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

  /** Possible values for sat_solver */
  enum SatSolver {
     BUFFERED_LINGELING = 0,
     BUFFERED_MINISAT = 1,
     BUFFERED_VAMPIRE = 2,
     LINGELING = 3,
     MINISAT = 4,
     VAMPIRE = 5
  };

  /** Possible values for saturation_algorithm */
  enum SaturationAlgorithm {
     DISCOUNT = 0,
     INST_GEN = 1,
     LRS = 2,
     OTTER = 3,
     TABULATION = 4
   };

  /** Possible values for activity of some inference rules */
  enum RuleActivity {
    RA_INPUT_ONLY = 0,
    RA_OFF = 1,
    RA_ON = 2
  };

  enum QuestionAnsweringMode {
    QA_ANSWER_LITERAL = 0,
    QA_FROM_PROOF = 1,
    QA_OFF = 2
  };

  enum InliningMode {
    INL_AXIOMS_ONLY = 0,
    INL_NON_GROWING = 1,
    INL_OFF = 2,
    INL_ON = 3
  };

  enum InterpolantMode {
    INTERP_MINIMIZED = 0,
    INTERP_OFF = 1,
    INTERP_ON = 2
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

  enum URResolution {
    URR_EC_ONLY = 0,
    URR_OFF = 1,
    URR_ON = 2
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
    EP_OFF = 4,
  };

  /** Values for --extensionality_resolution */
  enum ExtensionalityResolution {
    ER_FILTER = 0,
    ER_KNOWN = 1,
    ER_OFF = 2
  };

  enum SatRestartStrategy {
    SRS_FIXED = 0,
    SRS_GEOMETRIC = 1,
    SRS_LUBY = 2,
    SRS_MINISAT = 3,
  };

  enum SatVarSelector {
    SVS_ACTIVE = 0,
    SVS_NICENESS = 1,
    SVS_RECENTLY_LEARNT = 2,
  };

  enum NicenessOption{
    NICENESS_AVERAGE = 0,
    NICENESS_NONE=1,
    NICENESS_SUM = 2,
    NICENESS_TOP = 3,
  };

  enum SatClauseDisposer {
    SCD_GROWING = 0,
    SCD_MINISAT = 1,
  };

  enum SSplittingComponentSweeping {
    SSCS_ALL = 0,
    SSCS_ITERATED = 1,
    SSCS_NONE = 2,
    SSCS_ONLY_NEW = 3
  };

  enum SSplittingAddComplementary {
    SSAC_GROUND = 0,
    SSAC_NONE = 1
  };

  enum SSplittingNonsplittableComponents {
    SSNS_ALL = 0,
    SSNS_ALL_DEPENDENT = 1,
    SSNS_KNOWN = 2,
    SSNS_NONE = 3
  };

  enum Sos {
    SOS_ALL = 0,
    SOS_OFF = 1,
    SOS_ON = 2
  };

  enum PredicateEquivalenceDiscoveryMode {
    PED_ALL_ATOMS = 0,
    PED_ALL_FORMULAS = 1,
    PED_DEFINITIONS = 2,
    PED_OFF = 3,
    PED_ON = 4
  };


  //==========================================================
  // Getter functions
  // -currently disabled all setter functions
  //==========================================================

  vstring forcedOptions() const { return _forcedOptions.value; }
  vstring forbiddenOptions() const { return _forbiddenOptions.value; }
  vstring testId() const { return _testId.value; }
  vstring protectedPrefix() const { return _protectedPrefix.value; }
  Statistics statistics() const { return _statistics.value; }
  //void setStatistics(Statistics newVal) { _statistics=newVal; }
  Proof proof() const { return _proof.value; }
  bool proofChecking() const { return _proofChecking.value; }
  int naming() const { return _naming.value; }
  bool setNaming(int newVal);
  bool flattenTopLevelConjunctions() const { return _flattenTopLevelConjunctions.value; }
  bool eprPreservingNaming() const { return _eprPreservingNaming.value; }
  //void setEprPreservingNaming(bool newVal) { _eprPreservingNaming = newVal; }
  bool eprPreservingSkolemization() const { return _eprPreservingSkolemization.value; }
  //void setEprPreservingSkolemization(bool newVal) { _eprPreservingSkolemization = newVal; }
  bool eprRestoringInlining() const { return _eprRestoringInlining.value; }
  //void setEprRestoringInlining(bool newVal) { _eprRestoringInlining = newVal; }
  InliningMode predicateDefinitionInlining() const { return _predicateDefinitionInlining.value; }
  //void setPredicateDefinitionInlining(InliningMode newVal) { _predicateDefinitionInlining = newVal; }
  bool predicateDefinitionMerging() const { return _predicateDefinitionMerging.value; }
  //void setPredicateDefinitionMerging(bool newValue) { _predicateDefinitionMerging = newValue; }
  PredicateEquivalenceDiscoveryMode predicateEquivalenceDiscovery() const { return _predicateEquivalenceDiscovery.value; }
  //void setPredicateEquivalenceDiscovery(PredicateEquivalenceDiscoveryMode newValue) { _predicateEquivalenceDiscovery = newValue; }
  bool predicateEquivalenceDiscoveryAddImplications() const { return _predicateEquivalenceDiscoveryAddImplications.value; }
  bool predicateEquivalenceDiscoveryRandomSimulation() const { return _predicateEquivalenceDiscoveryRandomSimulation.value; }
  int predicateEquivalenceDiscoverySatConflictLimit() const { return _predicateEquivalenceDiscoverySatConflictLimit.value; }
  bool predicateIndexIntroduction() const { return _predicateIndexIntroduction.value; }
  //void setPredicateIndexIntroduction(bool newValue) { _predicateIndexIntroduction = newValue; }
  bool aigBddSweeping() const { return _aigBddSweeping.value; }
  bool aigConditionalRewriting() const { return _aigConditionalRewriting.value; }
  bool aigDefinitionIntroduction() const { return _aigDefinitionIntroduction.value; }
  unsigned aigDefinitionIntroductionThreshold() const { return _aigDefinitionIntroductionThreshold.value; }
  bool aigFormulaSharing() const { return _aigFormulaSharing.value; }
  bool aigInliner() const { return _aigInliner.value; }
  Mode mode() const { return _mode.value; }
  //void setMode(Mode newVal);
  InputSyntax inputSyntax() const { return _inputSyntax.value; }
  //void setInputSyntax(InputSyntax newVal) { _inputSyntax = newVal; }
  bool normalize() const { return _normalize.value; }
  //void setNormalize(bool normalize) { _normalize = normalize; }
  vstring include() const { return _include.value; }
  //void setInclude(vstring val) { _include = val; }
  vstring includeFileName (const vstring& relativeName);
  vstring logFile() const { return _logFile.value; }
  vstring inputFile() const { return _inputFile.value; }
  int randomSeed() const { return _randomSeed.value; }
  int rowVariableMaxLength() const { return _rowVariableMaxLength.value; }
  //void setRowVariableMaxLength(int newVal) { _rowVariableMaxLength = newVal; }
  bool printClausifierPremises() const { return _printClausifierPremises.value; }
  bool showActive() const { return _showActive.value; }
  bool showBlocked() const { return _showBlocked.value; }
  bool showDefinitions() const { return _showDefinitions.value; }
  InterpolantMode showInterpolant() const { return _showInterpolant.value; }
  bool showNew() const { return _showNew.value; }
  bool showNewPropositional() const { return _showNewPropositional.value; }
  bool showNonconstantSkolemFunctionTrace() const { return _showNonconstantSkolemFunctionTrace.value; }
  //void setShowNonconstantSkolemFunctionTrace(bool newVal) { _showNonconstantSkolemFunctionTrace = newVal; }
  OptionTag showOptions() const { return _showOptions.value; }
  bool showExperimentalOptions() const { return _showExperimentalOptions.value; }
  bool showHelp() const { return _showHelp.value; }
  bool showPassive() const { return _showPassive.value; }
  bool showPreprocessing() const { return _showPreprocessing.value; }
  bool showSkolemisations() const { return _showSkolemisations.value; }
  bool showSymbolElimination() const { return _showSymbolElimination.value; }
  bool showTheoryAxioms() const { return _showTheoryAxioms.value; }
  bool unusedPredicateDefinitionRemoval() const { return _unusedPredicateDefinitionRemoval.value; }
  //void setUnusedPredicateDefinitionRemoval(bool newVal) { _unusedPredicateDefinitionRemoval = newVal; }
  bool weightIncrement() const { return _weightIncrement.value; }
  bool useDM() const { return _use_dm.value; }
  SatSolver satSolver() const { return _satSolver.value; }
  //void setSatSolver(SatSolver newVal) { _satSolver = newVal; }
  SaturationAlgorithm saturationAlgorithm() const { return _saturationAlgorithm.value; }
  //void setSaturationAlgorithm(SaturationAlgorithm newVal) { _saturationAlgorithm = newVal; }
  int selection() const { return _selection.value; }
  bool setSelection(int newValue);
  bool setInstGenSelection(int newValue);
  vstring latexOutput() const { return _latexOutput.value; }
  LiteralComparisonMode literalComparisonMode() const { return _literalComparisonMode.value; }
  bool forwardSubsumptionResolution() const { return _forwardSubsumptionResolution.value; }
  void setForwardSubsumptionResolution(bool newVal) { _forwardSubsumptionResolution = newVal; }
  Demodulation forwardDemodulation() const { return _forwardDemodulation.value; }
  bool binaryResolution() const { return _binaryResolution.value; }
  bool bfnt() const { return _bfnt.value; }
  //void setBfnt(bool newVal) { _bfnt = newVal; }
  URResolution unitResultingResolution() const { return _unitResultingResolution.value; }
  bool hyperSuperposition() const { return _hyperSuperposition.value; }
  bool arityCheck() const { return _arityCheck.value; }
  //void setArityCheck(bool newVal) { _arityCheck=newVal; }
  Demodulation backwardDemodulation() const { return _backwardDemodulation.value; }
  bool demodulationRedundancyCheck() const { return _demodulationRedundancyCheck.value; }
  //void setBackwardDemodulation(Demodulation newVal) { _backwardDemodulation = newVal; }
  Subsumption backwardSubsumption() const { return _backwardSubsumption.value; }
  //void setBackwardSubsumption(Subsumption newVal) { _backwardSubsumption = newVal; }
  Subsumption backwardSubsumptionResolution() const { return _backwardSubsumptionResolution.value; }
  bool forwardSubsumption() const { return _forwardSubsumption.value; }
  bool forwardLiteralRewriting() const { return _forwardLiteralRewriting.value; }
  vstring lingvaAdditionalInvariants() const {return _lingvaAdditionalInvariants.value; }
  int lrsFirstTimeCheck() const { return _lrsFirstTimeCheck.value; }
  int lrsWeightLimitOnly() const { return _lrsWeightLimitOnly.value; }
>>>>>>> Changing the way we do options
  bool setLrsFirstTimeCheck(int newVal);
  int simulatedTimeLimit() const { return _simulatedTimeLimit.value; }
  //void setSimulatedTimeLimit(int newVal) { _simulatedTimeLimit = newVal; }
  int maxInferenceDepth() const { return _maxInferenceDepth.value; }
  SymbolPrecedence symbolPrecedence() const { return _symbolPrecedence.value; }
  /**
   * Return time limit in deciseconds, or 0 if there is no time limit
   */
  int timeLimitInDeciseconds() const { return _timeLimitInDeciseconds.value; }
  size_t memoryLimit() const { return _memoryLimit.value; }
  int inequalitySplitting() const { return _inequalitySplitting.value; }
  long maxActive() const { return _maxActive.value; }
  long maxAnswers() const { return _maxAnswers.value; }
  //void setMaxAnswers(int newVal) { _maxAnswers = newVal; }
  long maxPassive() const { return _maxPassive.value; }
  int maxWeight() const { return _maxWeight.value; }
  int ageRatio() const { return _ageRatio.value; }
  int weightRatio() const { return _weightRatio.value; }
  bool superpositionFromVariables() const { return _superpositionFromVariables.value; }
  bool equalityPropagation() const { return _equalityPropagation.value; }
  //void setEqualityPropagation(bool newVal) { _equalityPropagation = newVal; }
  EqualityProxy equalityProxy() const { return _equalityProxy.value; }
  RuleActivity equalityResolutionWithDeletion() const { return _equalityResolutionWithDeletion.value; }
  ExtensionalityResolution extensionalityResolution() const { return _extensionalityResolution.value; }
  unsigned extensionalityMaxLength() const { return _extensionalityMaxLength.value; }
  bool extensionalityAllowPosEq() const { return _extensionalityAllowPosEq.value; }
  
  float nongoalWeightCoefficient() const { return _nongoalWeightCoefficient.value; }
  bool setNongoalWeightCoefficient(float newVal);
  Sos sos() const { return _sos; }
  //void setSos(Sos newVal) { _sos = newVal; }
  FunctionDefinitionElimination functionDefinitionElimination() const { return _functionDefinitionElimination.value; }
  bool outputAxiomNames() const { return _outputAxiomNames.value; }
  //void setOutputAxiomNames(bool newVal) { _outputAxiomNames = newVal; }
  QuestionAnsweringMode questionAnswering() const { return _questionAnswering.value; }
  //void setQuestionAnswering(QuestionAnsweringMode newVal) { _questionAnswering = newVal; }
  vstring xmlOutput() const { return _xmlOutput.value; }
  vstring thanks() const { return _thanks.value; }

  bool globalSubsumption() const { return _globalSubsumption.value; }
  /** true if calling set() on non-existing options does not result in a user error */
  bool ignoreMissing() const { return _ignoreMissing.value; }
  /** set the "ignore missing options" value to true or false */
  //void setIgnoreMissing(bool newVal) { _ignoreMissing = newVal; }
  bool increasedNumeralWeight() const { return _increasedNumeralWeight.value; }
  bool theoryAxioms() const { return _theoryAxioms.value; }
  //void setTheoryAxioms(bool newValue) { _theoryAxioms = newValue; }
  bool interpretedSimplification() const { return _interpretedSimplification.value; }
  //void setInterpretedSimplification(bool val) { _interpretedSimplification = val; }
  Condensation condensation() const { return _condensation.value; }
  RuleActivity generalSplitting() const { return _generalSplitting.value; }
  vstring namePrefix() const { return _namePrefix.value; }
  bool timeStatistics() const { return _timeStatistics.value; }
  bool splitAtActivation() const { return _splitAtActivation.value; }
  bool splitting() const { return _splitting.value; }
  bool nonliteralsInClauseWeight() const { return _nonliteralsInClauseWeight.value; }
  unsigned sineDepth() const { return _sineDepth.value; }
  unsigned sineGeneralityThreshold() const { return _sineGeneralityThreshold.value; }
  SineSelection sineSelection() const { return _sineSelection.value; }
  //void setSineSelection(SineSelection val) { _sineSelection=val; }
  float sineTolerance() const { return _sineTolerance.value; }
  bool smtlibConsiderIntsReal() const { return _smtlibConsiderIntsReal.value; }
  //void setSmtlibConsiderIntsReal( bool newVal ) { _smtlibConsiderIntsReal = newVal; }
  bool smtlibFletAsDefinition() const { return _smtlibFletAsDefinition.value; }
  bool smtlibIntroduceAIGNames() const { return _smtlibIntroduceAIGNames.value; }

  bool colorUnblocking() const { return _colorUnblocking.value; }
  bool distinctProcessor() const { return _distinctProcessor.value; }
  bool hornRevealing() const { return _hornRevealing.value; }
  bool trivialPredicateRemoval() const { return _trivialPredicateRemoval.value; }

  bool tabulationBwRuleSubsumptionResolutionByLemmas() const { return _tabulationBwRuleSubsumptionResolutionByLemmas.value; }
  bool tabulationFwRuleSubsumptionResolutionByLemmas() const { return _tabulationFwRuleSubsumptionResolutionByLemmas.value; }
  int tabulationGoalAgeRatio() const { return _tabulationGoalAgeRatio.value; }
  int tabulationGoalWeightRatio() const { return _tabulationGoalWeightRatio.value; }
  int tabulationGoalRatio() const { return _tabulationGoalRatio.value; }
  int tabulationLemmaRatio() const { return _tabulationLemmaRatio.value; }
  bool tabulationInstantiateProducingRules() const { return _tabulationInstantiateProducingRules.value; }
  int tabulationLemmaAgeRatio() const { return _tabulationLemmaAgeRatio.value; }
  int tabulationLemmaWeightRatio() const { return _tabulationLemmaWeightRatio.value; }

  float instGenBigRestartRatio() const { return _instGenBigRestartRatio.value; }
  bool instGenInprocessing() const { return _instGenInprocessing.value; }
  bool instGenPassiveReactivation() const { return _instGenPassiveReactivation.value; }
  int instGenResolutionRatioInstGen() const { return _instGenResolutionRatioInstGen.value; }
  int instGenResolutionRatioResolution() const { return _instGenResolutionRatioResolution.value; }
  int instGenRestartPeriod() const { return _instGenRestartPeriod.value; }
  float instGenRestartPeriodQuotient() const { return _instGenRestartPeriodQuotient.value; }
  int instGenSelection() const { return _instGenSelection.value; }
  bool instGenWithResolution() const { return _instGenWithResolution.value; }

  float satClauseActivityDecay() const { return _satClauseActivityDecay.value; }
  SatClauseDisposer satClauseDisposer() const { return _satClauseDisposer.value; }
  bool satLearntMinimization() const { return _satLearntMinimization.value; }
  bool satLearntSubsumptionResolution() const { return _satLearntSubsumptionResolution.value; }
  int satRestartFixedCount() const { return _satRestartFixedCount.value; }
  float satRestartGeometricIncrease() const { return _satRestartGeometricIncrease.value; }
  int satRestartGeometricInit() const { return _satRestartGeometricInit.value; }
  int satRestartLubyFactor() const { return _satRestartLubyFactor.value; }
  float satRestartMinisatIncrease() const { return _satRestartMinisatIncrease.value; }
  int satRestartMinisatInit() const { return _satRestartMinisatInit.value; }
  SatRestartStrategy satRestartStrategy() const { return _satRestartStrategy.value; }
  float satVarActivityDecay() const { return _satVarActivityDecay.value; }
  SatVarSelector satVarSelector() const { return _satVarSelector.value; }

  NicenessOption nicenessOption() const { return _nicenessOption.value; }

  //void setMemoryLimit(size_t newVal) { _memoryLimit = newVal; }
  
  void setTimeLimitInSeconds(int newVal) { _timeLimitInDeciseconds.value = 10*newVal; }
  void setTimeLimitInDeciseconds(int newVal) { _timeLimitInDeciseconds.value = newVal; }
  int getTimeLimit(){return _timeLimitInDeciseconds.value;}
  int getWhileNumber(){return _whileNumber.value;}
  int getFunctionNumber(){return _functionNumber.value;}

  int nonGoalWeightCoeffitientNumerator() const { return _nonGoalWeightCoeffitientNumerator.value; }
  int nonGoalWeightCoeffitientDenominator() const { return _nonGoalWeightCoeffitientDenominator.value; }

  SSplittingNonsplittableComponents ssplittingNonsplittableComponents() const { return _ssplittingNonsplittableComponents.value; }
  SSplittingComponentSweeping ssplittingComponentSweeping() const { return _ssplittingComponentSweeping.value; }
  SSplittingAddComplementary ssplittingAddComplementary() const { return _ssplittingAddComplementary.value; }
  int ssplittingFlushPeriod() const { return _ssplittingFlushPeriod; }
  float ssplittingFlushQuotient() const { return _ssplittingFlushQuotient.value; }
  bool ssplittingEagerRemoval() const { return _ssplittingEagerRemoval.value; }
  bool ssplittingCongruenceClosure() const { return _ssplittingCongruenceClosure.value; }

  //void setProof(Proof p) { _proof = p; }
  bool bpEquivalentVariableRemoval() const { return _equivalentVariableRemoval.value; }
  unsigned bpMaximalPropagatedEqualityLength() const { return _maximalPropagatedEqualityLength.value; }
  BPAlmostHalfBoundingRemoval bpAlmostHalfBoundingRemoval() const {return _bpAlmostHalfBoundingRemoval.value;}
  bool bpFmElimination () const {return _bpFmElimination.value;}
  unsigned bpAllowedFMBalance() const { return _bpAllowedFMBalance.value; }
  BPAssignmentSelector bpAssignmentSelector() const {return _bpAssignmentSelector.value; }
  bool bpCollapsingPropagation() const {return _bpCollapsingPropagation.value; }
  unsigned bpUpdatesByOneConstraint() const {return _updatesByOneConstraint.value; }
  bool bpConservativeAssignmentSelection() const {return _bpConservativeAssignmentSelection.value; }
  BPConflictSelector bpConflictSelector() const {return _bpConflictSelector.value; }
  bool backjumpTargetIsDecisionPoint() const { return _backjumpTargetIsDecisionPoint.value; }
  bool bpPropagateAfterConflict() const {return _bpPropagateAfterConflict.value; }
  BPVariableSelector bpVariableSelector() const {return _bpVariableSelector.value; }
  bool bpSelectUnusedVariablesFirst() const {return _selectUnusedVariablesFirst.value; }
  bool bpStartWithPrecise() const { return _bpStartWithPrecise.value; }
  bool bpStartWithRational() const { return _bpStartWithRational.value;}
  


    //==========================================================
    // Variables holding option values
    //==========================================================
private:
  
    template<typename T>
    class OptionValue {
    public:
        OptionValue() {}
        OptionValue(vstring l, vstring s) : longName(l), shortName(s) {}
        vstring longName;
        vstring shortName;
        vstring description;
        bool experimental;
        T defaultValue;
        T actualValue;
        
        void setOptionValues(OptionValues choices){}
        
    };
    typedef OptionValue<bool> BoolOptionValue;
    typedef OptionValue<int> IntOptionValue;
    typedef OptionValue<unsigned> UnsignedOptionValue;
    typedef OptionValue<vstring> StringOptionValue;
    typedef OptionValue<long> LongOptionValue;
    typedef OptionValue<float> FloatOptionValue;
    
  StringOptionValue _decode;

  StringOptionValue _ageRatio;
  BoolOptionValue _aigBddSweeping;
  BoolOptionValue _aigConditionalRewriting;
  BoolOptionValue _aigDefinitionIntroduction;
  UnsignedOptionValue _aigDefinitionIntroductionThreshold;
  BoolOptionValue _aigFormulaSharing;
  BoolOptionValue _aigInliner;
  BoolOptionValue _arityCheck;
  
  BoolOptionValue _backjumpTargetIsDecisionPoint;
  OptionValue<Demodulation> _backwardDemodulation;
  OptionValue<Subsumption> _backwardSubsumption;
  OptionValue<Subsumption> _backwardSubsumptionResolution;
  BoolOptionValue _bfnt;
  BoolOptionValue _binaryResolution;
  BoolOptionValue _bpCollapsingPropagation;
  UnsignedOptionValue _bpAllowedFMBalance;
  OptionValue<BPAlmostHalfBoundingRemoval> _bpAlmostHalfBoundingRemoval;
  OptionValue<BPAssignmentSelector> _bpAssignmentSelector;
  OptionValue<BPConflictSelector> _bpConflictSelector;
  BoolOptionValue _bpConservativeAssignmentSelection;
  BoolOptionValue _bpFmElimination;
  BoolOptionValue _bpPropagateAfterConflict;
  BoolOptionValue _bpStartWithPrecise;
  BoolOptionValue _bpStartWithRational;
  OptionValue<BPVariableSelector> _bpVariableSelector;

  BoolOptionValue _colorUnblocking;
  OptionValue<Condensation> _condensation;

  BoolOptionValue _demodulationRedundancyCheck;
  BoolOptionValue _distinctProcessor;

  BoolOptionValue _eprPreservingNaming;
  BoolOptionValue _eprPreservingSkolemization;
  BoolOptionValue _eprRestoringInlining;
  BoolOptionValue _equalityPropagation;
  OptionValue<EqualityProxy> _equalityProxy;
  OptionValue<RuleActivity> _equalityResolutionWithDeletion;
  BoolOptionValue _equivalentVariableRemoval;
  OptionValue<ExtensionalityResolution> _extensionalityResolution;
  UnsignedOptionValue _extensionalityMaxLength;
  BoolOptionValue _extensionalityAllowPosEq;
  
  BoolOptionValue _flattenTopLevelConjunctions;
  StringOptionValue _forbiddenOptions;
  BoolOptionValue _forceIncompleteness;
  StringOptionValue _forcedOptions;
  OptionValue<Demodulation> _forwardDemodulation;
  BoolOptionValue _forwardLiteralRewriting;
  BoolOptionValue _forwardSubsumption;
  BoolOptionValue _forwardSubsumptionResolution;
  OptionValue<FunctionDefinitionElimination> _functionDefinitionElimination;
  IntOptionValue _functionNumber;
  
  OptionValue<RuleActivity> _generalSplitting;
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
  StringOptionValue _inputFile;
  OptionValue<InputSyntax> _inputSyntax;
  FloatOptionValue _instGenBigRestartRatio;
  BoolOptionValue _instGenInprocessing;
  BoolOptionValue _instGenPassiveReactivation;
  IntOptionValue _instGenResolutionRatioInstGen;
  IntOptionValue _instGenResolutionRatioResolution;
  IntOptionValue _instGenRestartPeriod;
  FloatOptionValue _instGenRestartPeriodQuotient;
  IntOptionValue _instGenSelection;
  BoolOptionValue _instGenWithResolution;
  BoolOptionValue _interpretedSimplification;

  StringOptionValue _latexOutput;
  StringOptionValue _lingvaAdditionalInvariants;

  OptionValue<LiteralComparisonMode> _literalComparisonMode;
  StringOptionValue _logFile;
  IntOptionValue _lrsFirstTimeCheck;
  BoolOptionValue _lrsWeightLimitOnly;

  LongOptionValue _maxActive;
  IntOptionValue _maxAnswers;
  IntOptionValue _maxInferenceDepth;
  LongOptionValue _maxPassive;
  IntOptionValue _maxWeight;
  UnsignedOptionValue _maximalPropagatedEqualityLength;
  OptionValue<size_t> _memoryLimit;
  OptionValue<Mode> _mode;

  StringOptionValue _namePrefix;
  IntOptionValue _naming;
  OptionValue<NicenessOption> _nicenessOption;
  FloatOptionValue _nongoalWeightCoefficient;
  IntOptionValue _nonGoalWeightCoeffitientDenominator;
  IntOptionValue _nonGoalWeightCoeffitientNumerator;
  BoolOptionValue _nonliteralsInClauseWeight;
  BoolOptionValue _normalize;

  BoolOptionValue _outputAxiomNames;

  OptionValue<InliningMode> _predicateDefinitionInlining;
  BoolOptionValue _predicateDefinitionMerging;
  OptionValue<PredicateEquivalenceDiscoveryMode> _predicateEquivalenceDiscovery;
  BoolOptionValue _predicateEquivalenceDiscoveryAddImplications;
  BoolOptionValue _predicateEquivalenceDiscoveryRandomSimulation;
  IntOptionValue _predicateEquivalenceDiscoverySatConflictLimit;
  BoolOptionValue _predicateIndexIntroduction;
  BoolOptionValue _printClausifierPremises;
  StrintOptionValue _problemName;
  OptionValue<Proof> _proof;
  BoolOptionValue _proofChecking;
  
  StringOptionValue _protectedPrefix;

  OptionValue<QuestionAnsweringMode> _questionAnswering;

  IntOptionValue _randomSeed;
  IntOptionValue _rowVariableMaxLength;

  FloatOptionValue _satClauseActivityDecay;
  OptionValue<SatClauseDisposer> _satClauseDisposer;
  BoolOptionValue _satLearntMinimization;
  BoolOptionValue _satLearntSubsumptionResolution;
  IntOptionValue _satRestartFixedCount;
  FloatOptionValue _satRestartGeometricIncrease;
  IntOptionValue _satRestartGeometricInit;
  IntOptionValue _satRestartLubyFactor;
  FloatOptionValue _satRestartMinisatIncrease;
  IntOptionValue _satRestartMinisatInit;
  OptionValue<SatRestartStrategy> _satRestartStrategy;
  FloatOptionValue _satVarActivityDecay;
  OptionValue<SatVarSelector> _satVarSelector;
  OptionValue<SatSolver> _satSolver;
  OptionValue<SaturationAlgorithm> _saturationAlgorithm;
  IntOptionValue _selection;
  BoolOptionValue _selectUnusedVariablesFirst;
  BoolOptionValue _showActive;
  BoolOptionValue _showBlocked;
  BoolOptionValue _showDefinitions;
  OptionValue<InterpolantMode> _showInterpolant;
  BoolOptionValue _showNew;
  BoolOptionValue _showNewPropositional;
  BoolOptionValue _showNonconstantSkolemFunctionTrace;
  OptionValue<OptionTag> _showOptions;
  BoolOptionValue _showExperimentalOptions;
  BoolOptionValue _showHelp;
  BoolOptionValue _showPassive;
  BoolOptionValue _showPreprocessing;
  BoolOptionValue _showSkolemisations;
  BoolOptionValue _showSymbolElimination;
  BoolOptionValue _showTheoryAxioms;
  IntOptionValue _simulatedTimeLimit;
  UnsignedOptionValue _sineDepth;
  UnsignedOptionValue _sineGeneralityThreshold;
  OptionValue<SineSelection> _sineSelection;
  FloatOptionValue _sineTolerance;
  BoolOptionValue _smtlibConsiderIntsReal;
  BoolOptionValue _smtlibFletAsDefinition;
  BoolOptionValue _smtlibIntroduceAIGNames;
  OptionValue<Sos> _sos;
  BoolOptionValue _splitting;
  OptionValue<SSplittingAddComplementary> _ssplittingAddComplementary;
  OptionValue<SSplittingComponentSweeping> _ssplittingComponentSweeping;
  BoolOptionValue _ssplittingCongruenceClosure;
  BoolOptionValue _ssplittingEagerRemoval;
  UnsignedOptionValue _ssplittingFlushPeriod;
  FloatOptionValue _ssplittingFlushQuotient;
  OptionValue<SSplittingNonsplittableComponents> _ssplittingNonsplittableComponents;
  OptionValue<Statistics> _statistics;
  BoolOptionValue _superpositionFromVariables;
  OptionValue<SymbolPrecedence> _symbolPrecedence;

  BoolOptionValue _tabulationBwRuleSubsumptionResolutionByLemmas;
  BoolOptionValue _tabulationFwRuleSubsumptionResolutionByLemmas;
  IntOptionValue _tabulationGoalAgeRatio;
  IntOptionValue _tabulationGoalWeightRatio;
  IntOptionValue _tabulationGoalRatio;
  IntOptionValue _tabulationLemmaRatio;
  BoolOptionValue _tabulationInstantiateProducingRules;
  IntOptionValue _tabulationLemmaAgeRatio;
  IntOptionValue _tabulationLemmaWeightRatio;
  StringOptionValue _testId;
  StringOptionValue _thanks;
  BoolOptionValue _theoryAxioms;
  /** Time limit in deciseconds */
  IntOptionValue _timeLimitInDeciseconds;
  BoolOptionValue _timeStatistics;
  BoolOptionValue _trivialPredicateRemoval;

  OptionValue<URResolution> _unitResultingResolution;
  BoolOptionValue _unusedPredicateDefinitionRemoval;
  UnsignedOptionValue _updatesByOneConstraint;
  BoolOptionValue _use_dm;
  BoolOptionValue _weightIncrement;
  IntOptionValue _weightRatio;
  IntOptionValue _whileNumber;

  StringOptionValue _xmlOutput;
>>>>>>> Changing the way we do options

}; // class Options

}

#endif

