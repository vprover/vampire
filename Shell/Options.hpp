/**
 * @file Options.hpp
 * Defines Vampire options.
 */

#ifndef __Options__
#define __Options__

#include <cstring> 

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/VirtualIterator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/NameArray.hpp"
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
    
    void forceIncompleteness() { _forceIncompleteness.actualValue=true; }
    
    static int readTimeLimit(const char* val);
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
    
    CLASS_NAME(Options);
    USE_ALLOCATOR(Options);
    
    /** first is option name, second option value */
    typedef pair<vstring, vstring> OptionSpec;
    typedef Stack<OptionSpec> OptionSpecStack;
    static void readOptionsString(vstring testId, OptionSpecStack& assignments);
    
    bool onOffToBool(const char* onOff,const char* option);
    
    // standard ways of creating options
    XMLElement toXML() const;
    bool outputSuppressed() const;
    void set(const vstring& name, const vstring& value);
    void set(const char* name, const char* value);
    void setShort(const char* name, const char* value);
    
private:
    void set(const char* name, const char* value, int index);
    
    static string boolToOnOff(bool);
    void outputValue(ostream& str,int optionTag) const;
    friend class Shell::LTB::Builder;

    
public:
  //==========================================================
  // The Enums for Option Values
  //==========================================================
  
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
  * Possible values for show_option
  * @author Giles
  */
  enum class OptionTag: unsigned int {
    BP,
    OFF,
    GLOBAL,
    VAMPIRE
  };

  /**
   * Possible values for mode_name.
   * @since 06/05/2007 Manchester
   */
  enum class Mode : unsigned int {
    AXIOM_SELECTION,
    SOLVER,
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
  // -currently disabled all setter functions
  //==========================================================

  vstring forcedOptions() const { return _forcedOptions.actualValue; }
  vstring forbiddenOptions() const { return _forbiddenOptions.actualValue; }
  vstring testId() const { return _testId.actualValue; }
  vstring protectedPrefix() const { return _protectedPrefix.actualValue; }
  Statistics statistics() const { return _statistics.actualValue; }
  void setStatistics(Statistics newVal) { _statistics.actualValue=newVal; }
  Proof proof() const { return _proof.actualValue; }
  bool proofChecking() const { return _proofChecking.actualValue; }
  int naming() const { return _naming.actualValue; }
  bool setNaming(int newVal);
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
  //void setMode(Mode newVal); // warning - code put into setForcedOptions
  InputSyntax inputSyntax() const { return _inputSyntax.actualValue; }
  //void setInputSyntax(InputSyntax newVal) { _inputSyntax = newVal; }
  bool normalize() const { return _normalize.actualValue; }
  void setNormalize(bool normalize) { _normalize.actualValue = normalize; }
  vstring include() const { return _include.actualValue; }
  //void setInclude(string val) { _include = val; }
  vstring includeFileName (const string& relativeName);
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
  //void setShowNonconstantSkolemFunctionTrace(bool newVal) { _showNonconstantSkolemFunctionTrace = newVal; }
  OptionTag showOptions() const { return _showOptions.actualValue; }
  bool showExperimentalOptions() const { return _showExperimentalOptions.actualValue; }
  bool showHelp() const { return _showHelp.actualValue; }
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
  SaturationAlgorithm saturationAlgorithm() const { return _saturationAlgorithm.actualValue; }
  void setSaturationAlgorithm(SaturationAlgorithm newVal) { _saturationAlgorithm.actualValue = newVal; }
  int selection() const { return _selection.actualValue; }
  bool setSelection(int newValue);
  bool setInstGenSelection(int newValue);
  vstring latexOutput() const { return _latexOutput.actualValue; }
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
  bool setLrsFirstTimeCheck(int newVal);
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
  //void setOutputAxiomNames(bool newVal) { _outputAxiomNames = newVal; }
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

  //void setMemoryLimit(size_t newVal) { _memoryLimit = newVal; }
  
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
     * Allows us to give a variable number of option values
     * This is a bit of a hack, and a nicer solution would be to have a variable argument
     * constructor. But this is simpler, in some senses.
     *
     * Note: It may be necessary to add a new constructor
     *
     * @author Giles
     * @since 30/07/14
     */
    struct OptionValues{
        
        OptionValues(){ };
        OptionValues(std::initializer_list<string> list){
          _len = list.size();
          _array = new const char*[_len];
          unsigned i = 0;
          for(std::initializer_list<string>::iterator it = list.begin();
              it!=list.end();++it){
            _array[i++]=(*it).c_str();
          }
          na = new NameArray(_array,_len);
        }

        int find(const char* value) const {
          ASS(na);
          return na->find(value);
        }

    private:
        const char**  _array;
        int _len;
        NameArray* na;
    };
    
    struct AbstractOptionValue{

        AbstractOptionValue(){}
        AbstractOptionValue(string l,string s) :
          longName(l), shortName(s), experimental(false) {}

        virtual void check() = 0;
        virtual bool set(const string& value) = 0;

        string longName;
        string shortName;
        string description;
        bool experimental;
    };
    
// Dangerous as we do not necessarily instantiate... default constructor is called giving
// default values to contents, then we assign. Want mechanism to ensure everything is set.
// However, don't want to have to create in init list of Options
    template<typename T>
    struct OptionValue : public AbstractOptionValue {
        OptionValue(){}
        OptionValue(vstring l, vstring s,T def) : AbstractOptionValue(l,s), 
          defaultValue(def), actualValue(def) {}


        T defaultValue;
        T actualValue;

        virtual bool set(const vstring& value) = 0;
        
#if VDEBUG
        void check(){ if(longName.empty()){ ASSERTION_VIOLATION;} }
#endif        

    };

    template<typename T>
    struct ChoiceOptionValue : public OptionValue<T> {
      ChoiceOptionValue(){}
      ChoiceOptionValue(vstring l, vstring s,T def,OptionValues c) :
          OptionValue<T>(l,s,def), choices(c) {} 

      bool set(const vstring& value){
        // makes reasonable assumption about ordering of every enum
        int index = choices.find(value.c_str());
        // obviously unsafe cast... what if choices is larger than T
        this->actualValue = static_cast<T>(index);
        return true;
      }

      OptionValues choices;
    };

    struct BoolOptionValue : public OptionValue<bool> {
      BoolOptionValue(){}
      BoolOptionValue(vstring l,vstring s, bool d) : OptionValue(l,s,d){} 
      bool set(const vstring& value){
        const char* cvalue = value.c_str();
        if (! strcmp(cvalue,"on") || ! strcmp(cvalue,"true")) {
          actualValue=true;
           
        }
        else if (! strcmp(cvalue,"off") || ! strcmp(cvalue,"false")) {
          actualValue=false;
        }
        else return false;
          
        return true;
      }
    };

    struct IntOptionValue : public OptionValue<int> {
      IntOptionValue(){}
      IntOptionValue(vstring l,vstring s, int d) : OptionValue(l,s,d){} 
      bool set(const vstring& value){
        return Int::stringToInt(value.c_str(),actualValue);
      }
    };

    struct UnsignedOptionValue : public OptionValue<unsigned> {
      UnsignedOptionValue(){}
      UnsignedOptionValue(vstring l,vstring s, unsigned d) : OptionValue(l,s,d){} 
      bool set(const vstring& value){
        return Int::stringToUnsignedInt(value.c_str(),actualValue);
      }
    }; 

    struct StringOptionValue : public OptionValue<vstring> {
      StringOptionValue(){}
      StringOptionValue(vstring l,vstring s, vstring d) : OptionValue(l,s,d){} 
      bool set(const vstring& value){ actualValue = value; return true; }
    }; 

    struct LongOptionValue : public OptionValue<long> {
      LongOptionValue(){}
      LongOptionValue(vstring l,vstring s, long d) : OptionValue(l,s,d){} 
      bool set(const vstring& value){
        return Int::stringToLong(value.c_str(),actualValue);
      }
    };

    struct FloatOptionValue : public OptionValue<float>{
      FloatOptionValue(){}
      FloatOptionValue(vstring l,vstring s, float d) : OptionValue(l,s,d){} 
      bool set(const vstring& value){
        return Int::stringToFloat(value.c_str(),actualValue);
      }
    };
 
    struct RatioOptionValue : public OptionValue<int> {
        RatioOptionValue(){}
        RatioOptionValue(vstring l, vstring s, int def, int other) :
          OptionValue(l,s,def), defaultOtherValue(other), otherValue(other) {};

        void readRatio(const char* val, char seperator=':');
        bool set(const vstring& value){
          if(sep) readRatio(value.c_str(),sep);
          else readRatio(value.c_str());
            return true; // TODO readRatio should return bool
        }

        char sep = 0;
        int defaultOtherValue;
        int otherValue;
    };
   
    struct LookupWrapper {
        
        LookupWrapper() : _copied(false) {}

        LookupWrapper operator=(const LookupWrapper&){
          _copied=true; 
          return *this;
        } 

        void insert(AbstractOptionValue* option_value){
            ASS(!_copied);
            _longMap.insert(option_value->longName,option_value);
            _shortMap.insert(option_value->shortName,option_value);
        }
        AbstractOptionValue* findLong(vstring longName){
            ASS(!_copied);
            return _longMap.get(longName);
        }
        AbstractOptionValue* findShort(vstring shortName){
            ASS(!_copied);
            return _shortMap.get(shortName);
        }

#if VDEBUG
        void check(){
          DHMap<vstring,AbstractOptionValue*>::Iterator it(_longMap);
          while(it.hasNext()){ it.next()->check(); } 
        }
#endif

        VirtualIterator<AbstractOptionValue*> values() { 
         //TODO implement values() in DHMap
         return _longMap.values();
        } 

        private:
        bool _copied;
        DHMap<vstring,AbstractOptionValue*> _longMap;
        DHMap<vstring,AbstractOptionValue*> _shortMap;
    };
    
    LookupWrapper _lookup;
    
  StringOptionValue _decode;

  RatioOptionValue _ageWeightRatio;
  BoolOptionValue _aigBddSweeping;
  BoolOptionValue _aigConditionalRewriting;
  BoolOptionValue _aigDefinitionIntroduction;
  UnsignedOptionValue _aigDefinitionIntroductionThreshold;
  BoolOptionValue _aigFormulaSharing;
  BoolOptionValue _aigInliner;
  BoolOptionValue _arityCheck;
  
  BoolOptionValue _backjumpTargetIsDecisionPoint;
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
  StringOptionValue _inputFile;
  ChoiceOptionValue<InputSyntax> _inputSyntax;
  FloatOptionValue _instGenBigRestartRatio;
  BoolOptionValue _instGenInprocessing;
  BoolOptionValue _instGenPassiveReactivation;
  RatioOptionValue _instGenResolutionInstGenRatio;
  //IntOptionValue _instGenResolutionRatioResolution;
  IntOptionValue _instGenRestartPeriod;
  FloatOptionValue _instGenRestartPeriodQuotient;
  IntOptionValue _instGenSelection;
  BoolOptionValue _instGenWithResolution;
  BoolOptionValue _interpretedSimplification;

  StringOptionValue _latexOutput;
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
  ChoiceOptionValue<SaturationAlgorithm> _saturationAlgorithm;
  IntOptionValue _selection;
  BoolOptionValue _selectUnusedVariablesFirst;
  BoolOptionValue _showActive;
  BoolOptionValue _showBlocked;
  BoolOptionValue _showDefinitions;
  ChoiceOptionValue<InterpolantMode> _showInterpolant;
  BoolOptionValue _showNew;
  BoolOptionValue _showNewPropositional;
  BoolOptionValue _showNonconstantSkolemFunctionTrace;
  ChoiceOptionValue<OptionTag> _showOptions;
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
  IntOptionValue _timeLimitInDeciseconds;
  BoolOptionValue _timeStatistics;
  BoolOptionValue _trivialPredicateRemoval;

  ChoiceOptionValue<URResolution> _unitResultingResolution;
  BoolOptionValue _unusedPredicateDefinitionRemoval;
  UnsignedOptionValue _updatesByOneConstraint;
  BoolOptionValue _use_dm;
  BoolOptionValue _weightIncrement;
  IntOptionValue _whileNumber;

  StringOptionValue _xmlOutput;
>>>>>>> Changing the way we do options

  // Taken from what was previously setNongoalWeightCoefficient
  struct NonGoalWeightOptionValue : public OptionValue<float>{
        NonGoalWeightOptionValue(){}
        NonGoalWeightOptionValue(vstring l, vstring s, float def) :
        OptionValue(l,s,def), numerator(1), denominator(1) {};
        

        bool set(const vstring& value){
            
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
      
        int numerator;
        int denominator;
    };
    
  NonGoalWeightOptionValue _nonGoalWeightCoefficient;
    
    
}; // class Options

}

#endif

