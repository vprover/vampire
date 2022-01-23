################################################################
# general configuration
################################################################
cmake_minimum_required (VERSION 3.12.0)
project(Vampire)

# require the compiler to use C++14
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# compile command database
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# variables for binary name, set later
set(VAMPIRE_BINARY vampire)
set(VAMPIRE_BINARY_BUILD)
set(VAMPIRE_BINARY_STATIC)
set(VAMPIRE_BINARY_Z3)
set(VAMPIRE_BINARY_HASH)
set(VAMPIRE_BINARY_BRANCH)
set(VAMPIRE_BINARY_REV_COUNT)

# set build type if not set
if(NOT CMAKE_BUILD_TYPE)
  message(STATUS "Setting build type to 'Release' as none was specified.")
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Choose the type of build." FORCE)
endif()

# statically link libraries
option(BUILD_SHARED_LIBS "Build an executable dynamically linking to libraries instead of a statically-linked one (static not working on Mac)" ON)
if (NOT BUILD_SHARED_LIBS)
  set(CMAKE_FIND_LIBRARY_SUFFIXES .a)
  set(CMAKE_EXE_LINKER_FLAGS -static)
  set(VAMPIRE_BINARY_STATIC _static)
endif()

# We compile tests only in debug mode, since in release mode assertions are NOPs anyways.
if(CMAKE_BUILD_TYPE STREQUAL Debug)
  SET(COMPILE_TESTS ON)
else()
  SET(COMPILE_TESTS OFF)
endif()

option(IPO "If supported, build with link-time optimisation." OFF)
option(DEBUG_IPO "Print information about why IPO isn't supported" OFF)
# check whether IPO is available
include(CheckIPOSupported)
check_ipo_supported(RESULT IPO_SUPPORTED OUTPUT IPO_ERROR)
if (IPO_SUPPORTED)
  message(STATUS "IPO supported")
else()
  message(STATUS "IPO not supported")
  if(DEBUG_IPO)
    message(STATUS "${IPO_ERROR}")
  else()
    message(STATUS "(if you need IPO, set DEBUG_IPO=ON to investigate)")
  endif()
endif()

################################################################
# define all vampire sources,
# generate the main target and 
# link it against the libraries
# NOTE: we add the header files here such that they are considered
#       to be a part of the project and therefore are displayed
#       displayed by the IDEs (we wouldn't need to add them because
#       of dependendy tracking, this is figured out automatically
#       by the compiler)
# TODO: there are unused files (I guess both headers and source 
#       files). I included only the source files which are also 
#       included in the makefile, but then added all headers 
#       which don't have a corresponding source file (since I don't
#       know which of them are really used, that information is
#       of course not contained in the makefile)
################################################################

set(VAMPIRE_MINISAT_SOURCES
    Minisat/core/Solver.cc
    Minisat/simp/SimpSolver.cc
    Minisat/utils/Options.cc
    Minisat/utils/System.cc
    SAT/MinisatInterfacing.cpp
    SAT/MinisatInterfacingNewSimp.cpp
    Minisat/core/Dimacs.h
    Minisat/core/Solver.h
    Minisat/core/SolverTypes.h
    Minisat/mtl/Alg.h
    Minisat/mtl/Alloc.h
    Minisat/mtl/Heap.h
    Minisat/mtl/IntMap.h
    Minisat/mtl/IntTypes.h
    Minisat/mtl/Map.h
    Minisat/mtl/Queue.h
    Minisat/mtl/Rnd.h
    Minisat/mtl/Sort.h
    Minisat/mtl/Vec.h
    Minisat/mtl/XAlloc.h
    Minisat/simp/SimpSolver.h
    Minisat/utils/Options.h
    Minisat/utils/ParseUtils.h
    Minisat/utils/System.h
    )
source_group(minisat_source_files FILES ${VAMPIRE_MINISAT_SOURCES})

set(VAMPIRE_DEBUG_SOURCES
    Debug/Assertion.cpp
    Debug/RuntimeStatistics.cpp
    Debug/Tracer.cpp    
    Debug/Assertion.hpp
    Debug/RuntimeStatistics.hpp
    Debug/Tracer.hpp
    )
source_group(debug_source_files FILES ${VAMPIRE_DEBUG_SOURCES})

set(VAMPIRE_LIB_SOURCES
    Lib/Allocator.cpp
    Lib/DHMap.cpp
    Lib/Environment.cpp
    Lib/Event.cpp
    Lib/Exception.cpp
    Lib/Hash.cpp
    Lib/Int.cpp
    Lib/IntNameTable.cpp
    Lib/IntUnionFind.cpp
    Lib/MemoryLeak.cpp
    Lib/MultiCounter.cpp
    Lib/NameArray.cpp
    Lib/Random.cpp
    Lib/StringUtils.cpp
    Lib/System.cpp
    Lib/TimeCounter.cpp
    Lib/Timer.cpp

    Lib/Allocator.hpp
    Lib/Array.hpp
    Lib/ArrayMap.hpp
    Lib/Backtrackable.hpp
    Lib/BacktrackIterators.hpp
    Lib/BinaryHeap.hpp
    Lib/BitUtils.hpp
    Lib/BucketSorter.hpp
    Lib/Cache.hpp
    Lib/Comparison.hpp
    Lib/Counter.hpp
    Lib/DArray.hpp
    Lib/Deque.hpp
    Lib/DHMap.hpp
    Lib/DHMultiset.hpp
    Lib/DHSet.hpp
    Lib/DynamicHeap.hpp
    Lib/Environment.hpp
    Lib/Event.hpp
    Lib/Exception.hpp
    Lib/fdstream.hpp
    Lib/FreshnessGuard.hpp
    Lib/Hash.hpp
    Lib/ImplicationSetClosure.hpp
    Lib/Int.hpp
    Lib/IntNameTable.hpp
    Lib/IntUnionFind.hpp
    Lib/InverseLookup.hpp
    Lib/LastCopyWatcher.hpp
    Lib/List.hpp
    Lib/Map.hpp
    Lib/MapToLIFO.hpp
    Lib/MaybeBool.hpp
    Lib/MemoryLeak.hpp
    Lib/Metaarrays.hpp
    Lib/Metaiterators.hpp
    Lib/MultiColumnMap.hpp
    Lib/MultiCounter.hpp
    Lib/NameArray.hpp
    Lib/Numbering.hpp
    Lib/PairUtils.hpp
    Lib/Portability.hpp
    Lib/Random.hpp
    Lib/RatioKeeper.hpp
    Lib/RCPtr.hpp
    Lib/Recycler.hpp
    Lib/ReferenceCounter.hpp
    Lib/Reflection.hpp
    Lib/SafeRecursion.hpp
    Lib/SCCAnalyzer.hpp
    Lib/ScopedLet.hpp
    Lib/ScopedPtr.hpp
    Lib/Set.hpp
    Lib/SharedSet.hpp
    Lib/SkipList.hpp
    Lib/SmartPtr.hpp
    Lib/Sort.hpp
    Lib/Stack.hpp
    Lib/STLAllocator.hpp
    Lib/StringUtils.hpp
    Lib/System.hpp
    Lib/TimeCounter.hpp
    Lib/Timer.hpp
    Lib/TriangularArray.hpp
    Lib/Vector.hpp
    Lib/VirtualIterator.hpp
    Lib/VString.hpp
    Lib/STL.hpp
    )
source_group(lib_source_files FILES ${VAMPIRE_LIB_SOURCES})

set(VAMPIRE_LIB_SYS_SOURCES
    Lib/Sys/Multiprocessing.cpp
    Lib/Sys/Semaphore.cpp
    Lib/Sys/SyncPipe.cpp
    Lib/Sys/Multiprocessing.hpp
    Lib/Sys/Semaphore.hpp
    Lib/Sys/SyncPipe.hpp
    )
source_group(lib_sys_source_files FILES ${VAMPIRE_LIB_SYS_SOURCES})

set(VAMPIRE_KERNEL_SOURCES
    Kernel/Clause.cpp
    Kernel/ClauseQueue.cpp
    Kernel/ColorHelper.cpp
    Kernel/ELiteralSelector.cpp
    Kernel/EqHelper.cpp
    Kernel/FlatTerm.cpp
    Kernel/Formula.cpp
    Kernel/FormulaTransformer.cpp
    Kernel/FormulaUnit.cpp
    Kernel/FormulaVarIterator.cpp
    Kernel/Grounder.cpp
    Kernel/Inference.cpp
    Kernel/InferenceStore.cpp
    Kernel/InterpretedLiteralEvaluator.cpp
    Kernel/Rebalancing.cpp
    Kernel/KBO.cpp
    Kernel/KBOForEPR.cpp
    Kernel/LiteralSelector.cpp
    Kernel/LookaheadLiteralSelector.cpp
    Kernel/MainLoop.cpp
    Kernel/Matcher.cpp
    Kernel/MaximalLiteralSelector.cpp
    Kernel/MLMatcher.cpp
    Kernel/MLMatcherSD.cpp
    Kernel/MLVariant.cpp
    Kernel/Ordering.cpp
    Kernel/Ordering_Equality.cpp
    Kernel/Problem.cpp
    Kernel/Renaming.cpp
    Kernel/RobSubstitution.cpp
    Kernel/MismatchHandler.cpp
    Kernel/Signature.cpp
    Kernel/SortHelper.cpp
    Kernel/OperatorType.cpp
    Kernel/SpassLiteralSelector.cpp
    Kernel/SubformulaIterator.cpp
    Kernel/Substitution.cpp
    Kernel/Term.cpp
    Kernel/TermIterators.cpp
    Kernel/TermTransformer.cpp
    Kernel/Theory.cpp
    Kernel/Signature.cpp
    Kernel/Unit.cpp
    Kernel/BottomUpEvaluation.hpp
    Kernel/BottomUpEvaluation/TermList.hpp
    Kernel/BottomUpEvaluation/TypedTermList.hpp
    Kernel/BottomUpEvaluation/PolyNf.hpp
    Kernel/BestLiteralSelector.hpp
    Kernel/Clause.hpp
    Kernel/ClauseQueue.hpp
    Kernel/ColorHelper.hpp
    Kernel/Connective.hpp
    Kernel/Curryfier.hpp
    Kernel/ELiteralSelector.hpp
    Kernel/EqHelper.hpp
    Kernel/FlatTerm.hpp
    Kernel/Formula.hpp
    Kernel/FormulaTransformer.hpp
    Kernel/FormulaUnit.hpp
    Kernel/FormulaVarIterator.hpp
    Kernel/Grounder.hpp
    Kernel/Inference.hpp
    Kernel/InferenceStore.hpp
    Kernel/InterpretedLiteralEvaluator.hpp
    Kernel/Rebalancing.cpp
    Kernel/KBO.hpp
    Kernel/KBOForEPR.hpp
    Kernel/LiteralComparators.hpp
    Kernel/LiteralSelector.hpp
    Kernel/LookaheadLiteralSelector.hpp
    Kernel/MainLoop.hpp
    Kernel/Matcher.hpp
    Kernel/MaximalLiteralSelector.hpp
    Kernel/MLMatcher.hpp
    Kernel/MLVariant.hpp
    Kernel/Ordering.hpp
    Kernel/Problem.hpp
    Kernel/RCClauseStack.hpp
    Kernel/Renaming.hpp
    Kernel/RobSubstitution.hpp
    Kernel/MismatchHandler.hpp
    Kernel/Signature.hpp
    Kernel/SortHelper.hpp
    Kernel/OperatorType.hpp
    Kernel/SpassLiteralSelector.hpp
    Kernel/SubformulaIterator.hpp
    Kernel/SubstHelper.hpp
    Kernel/Substitution.hpp
    Kernel/Term.hpp
    Kernel/TermIterators.hpp
    Kernel/TermTransformer.hpp
    Kernel/Theory.hpp
    Kernel/Signature.hpp
    Kernel/Unit.hpp
    Kernel/LPO.cpp
    Kernel/LPO.hpp
    Kernel/Polynomial.hpp
    Kernel/Polynomial.cpp
    Kernel/PolynomialNormalizer.hpp
    Kernel/PolynomialNormalizer.cpp
    Kernel/ApplicativeHelper.hpp
    Kernel/ApplicativeHelper.cpp
    Kernel/SKIKBO.hpp
    Kernel/SKIKBO.cpp
    Indexing/TypeSubstitutionTree.cpp
    Indexing/TypeSubstitutionTree.hpp
    Inferences/CNFOnTheFly.cpp
    Inferences/CNFOnTheFly.hpp
    Inferences/CombinatorDemodISE.cpp
    Inferences/CombinatorDemodISE.hpp
    Inferences/CombinatorNormalisationISE.hpp
    Inferences/CombinatorNormalisationISE.cpp
    Inferences/ArgCong.hpp
    Inferences/ArgCong.cpp
    Inferences/NegativeExt.cpp
    Inferences/NegativeExt.hpp
    Inferences/Narrow.hpp
    Inferences/Narrow.cpp
    Inferences/SubVarSup.hpp
    Inferences/SubVarSup.cpp
    Inferences/BoolEqToDiseq.hpp
    Inferences/BoolEqToDiseq.cpp
    Inferences/PrimitiveInstantiation.cpp
    Inferences/PrimitiveInstantiation.hpp
    Inferences/ElimLeibniz.cpp
    Inferences/ElimLeibniz.hpp
    Inferences/Choice.cpp
    Inferences/Choice.hpp
    Inferences/Injectivity.hpp
    Inferences/Injectivity.cpp
    Inferences/BoolSimp.hpp
    Inferences/BoolSimp.cpp
    Inferences/CasesSimp.cpp
    Inferences/CasesSimp.hpp
    Inferences/Cases.cpp
    Inferences/Cases.hpp
    Shell/LambdaElimination.cpp
    Shell/LambdaElimination.hpp
    )
source_group(kernel_source_files FILES ${VAMPIRE_KERNEL_SOURCES})

set(VAMPIRE_INDEXING_SOURCES
    Indexing/AcyclicityIndex.cpp
    Indexing/ClauseCodeTree.cpp
    Indexing/ClauseVariantIndex.cpp
    Indexing/CodeTree.cpp
    Indexing/CodeTreeInterfaces.cpp
    Indexing/GroundingIndex.cpp
    Indexing/Index.cpp
    Indexing/IndexManager.cpp
    Indexing/LiteralIndex.cpp
    Indexing/LiteralMiniIndex.cpp
    Indexing/LiteralSubstitutionTree.cpp
    Indexing/ResultSubstitution.cpp
    Indexing/SubstitutionTree.cpp
    Indexing/SubstitutionTree_FastGen.cpp
    Indexing/SubstitutionTree_FastInst.cpp
    Indexing/SubstitutionTree_Nodes.cpp
    Indexing/TermCodeTree.cpp
    Indexing/TermIndex.cpp
    Indexing/TermSharing.cpp
    Indexing/TermSubstitutionTree.cpp
    Indexing/AcyclicityIndex.hpp
    Indexing/ClauseCodeTree.hpp
    Indexing/ClauseVariantIndex.hpp
    Indexing/CodeTree.hpp
    Indexing/CodeTreeInterfaces.hpp
    Indexing/GroundingIndex.hpp
    Indexing/Index.hpp
    Indexing/IndexManager.hpp
    Indexing/LiteralIndex.hpp
    Indexing/LiteralIndexingStructure.hpp
    Indexing/LiteralMiniIndex.hpp
    Indexing/LiteralSubstitutionTree.hpp
    Indexing/ResultSubstitution.hpp
    Indexing/SubstitutionTree.hpp
    Indexing/TermCodeTree.hpp
    Indexing/TermIndex.hpp
    Indexing/TermIndexingStructure.hpp
    Indexing/TermSharing.hpp
    Indexing/TermSubstitutionTree.hpp
    )
source_group(indexing_source_files FILES ${VAMPIRE_INDEXING_SOURCES})

set(VAMPIRE_INFERENCE_SOURCES
    Inferences/BackwardDemodulation.cpp
    Inferences/BackwardSubsumptionDemodulation.cpp
    Inferences/BackwardSubsumptionResolution.cpp
    Inferences/BinaryResolution.cpp
    Inferences/Condensation.cpp
    Inferences/DistinctEqualitySimplifier.cpp
    Inferences/EqualityFactoring.cpp
    Inferences/EqualityResolution.cpp
    Inferences/ExtensionalityResolution.cpp
    Inferences/Factoring.cpp
    Inferences/FastCondensation.cpp
    Inferences/FOOLParamodulation.cpp
    Inferences/ForwardDemodulation.cpp
    Inferences/ForwardLiteralRewriting.cpp
    Inferences/ForwardSubsumptionAndResolution.cpp
    Inferences/ForwardSubsumptionDemodulation.cpp
    Inferences/GlobalSubsumption.cpp
    Inferences/HyperSuperposition.cpp
    Inferences/InnerRewriting.cpp
    Inferences/EquationalTautologyRemoval.cpp
    Inferences/Induction.cpp
    Inferences/InductionHelper.cpp
    Inferences/InferenceEngine.cpp
    Inferences/Instantiation.cpp
    Inferences/InterpretedEvaluation.cpp
    Inferences/PushUnaryMinus.cpp
    Inferences/Cancellation.cpp
    Inferences/ArithmeticSubtermGeneralization.cpp
    Kernel/NumTraits.cpp
    Inferences/GaussianVariableElimination.cpp
    Kernel/Rebalancing.cpp
    Kernel/Rebalancing/Inverters.cpp
    Inferences/SLQueryBackwardSubsumption.cpp
    Inferences/Superposition.cpp
    Inferences/TautologyDeletionISE.cpp
    Inferences/TermAlgebraReasoning.cpp
    Inferences/URResolution.cpp
    Inferences/BackwardDemodulation.hpp
    Inferences/BackwardSubsumptionResolution.hpp
    Inferences/BinaryResolution.hpp
    Inferences/Condensation.hpp
    Inferences/DistinctEqualitySimplifier.hpp
    Inferences/EqualityFactoring.hpp
    Inferences/EqualityResolution.hpp
    Inferences/ExtensionalityResolution.hpp
    Inferences/Factoring.hpp
    Inferences/FastCondensation.hpp
    Inferences/FOOLParamodulation.hpp
    Inferences/ForwardDemodulation.hpp
    Inferences/ForwardLiteralRewriting.hpp
    Inferences/ForwardSubsumptionAndResolution.hpp
    Inferences/GlobalSubsumption.hpp
    Inferences/HyperSuperposition.hpp
    Inferences/InnerRewriting.hpp
    Inferences/EquationalTautologyRemoval.hpp
    Inferences/InductionHelper.hpp
    Inferences/InferenceEngine.hpp
    Inferences/Instantiation.hpp
    Inferences/InterpretedEvaluation.hpp
    Inferences/PushUnaryMinus.hpp
    Inferences/Cancellation.hpp
    Inferences/ArithmeticSubtermGeneralization.hpp
    Kernel/NumTraits.cpp
    Inferences/GaussianVariableElimination.hpp
    Kernel/Rebalancing.hpp
    Kernel/Rebalancing/Inverters.hpp
    Inferences/SLQueryBackwardSubsumption.hpp
    Inferences/SubsumptionDemodulationHelper.cpp
    Inferences/Superposition.hpp
    Inferences/TautologyDeletionISE.hpp
    Inferences/TermAlgebraReasoning.hpp
    Inferences/URResolution.hpp
    Inferences/TheoryInstAndSimp.hpp
    Inferences/TheoryInstAndSimp.cpp  # this is theory instantiation
    Inferences/ArithmeticSubtermGeneralization.hpp
    Inferences/ArithmeticSubtermGeneralization.cpp
    Inferences/PolynomialEvaluation.hpp
    Inferences/PolynomialEvaluation.cpp
    Inferences/Cancellation.hpp
    Inferences/Cancellation.cpp
#    Inferences/TheoryRuleAttempt.hpp
#    Inferences/TheoryRuleAttempt.cpp
    )
source_group(inference_source_files FILES ${VAMPIRE_INFERENCE_SOURCES})

set(VAMPIRE_INSTANCEGENERATION_SOURCES
    InstGen/IGAlgorithm.cpp
    InstGen/ModelPrinter.cpp
    InstGen/IGAlgorithm.hpp
    InstGen/ModelPrinter.hpp
    )
source_group(instancegeneration_source_files FILES ${VAMPIRE_INSTANCEGENERATION_SOURCES})

set(VAMPIRE_SAT_SOURCES
    SAT/BufferedSolver.cpp
    SAT/DIMACS.cpp
    SAT/FallbackSolverWrapper.cpp
    SAT/MinimizingSolver.cpp
    SAT/SAT2FO.cpp
    SAT/SATClause.cpp
    SAT/SATInference.cpp
    SAT/SATLiteral.cpp
    SAT/Z3Interfacing.cpp

    SAT/BufferedSolver.hpp
    SAT/DIMACS.hpp
    SAT/FallbackSolverWrapper.hpp
    SAT/MinimizingSolver.hpp
    SAT/SAT2FO.hpp
    SAT/SATClause.hpp
    SAT/SATInference.hpp
    SAT/SATLiteral.hpp
    SAT/SATSolver.hpp
    SAT/Z3Interfacing.hpp
    )
source_group(sat_source_files FILES ${VAMPIRE_SAT_SOURCES})

set(VAMPIRE_DECISION_PROCEDURES_SOURCES
    DP/ShortConflictMetaDP.cpp
    DP/SimpleCongruenceClosure.cpp
    DP/DecisionProcedure.hpp
    DP/ShortConflictMetaDP.hpp
    DP/SimpleCongruenceClosure.hpp
    )
source_group(decision_procedures_source_files FILES ${VAMPIRE_DECISION_PROCEDURES_SOURCES})

set(VAMPIRE_SATURATION_SOURCES
    Saturation/AWPassiveClauseContainer.cpp
    Saturation/ManCSPassiveClauseContainer.cpp
    Saturation/ClauseContainer.cpp
    Saturation/ConsequenceFinder.cpp
    Saturation/Discount.cpp
    Saturation/ExtensionalityClauseContainer.cpp
    Saturation/LabelFinder.cpp
    Saturation/LRS.cpp
    Saturation/Otter.cpp
    Saturation/ProvingHelper.cpp
    Saturation/SaturationAlgorithm.cpp
    Saturation/Splitter.cpp
    Saturation/SymElOutput.cpp
    Saturation/PredicateSplitPassiveClauseContainer.cpp
    Saturation/AWPassiveClauseContainer.hpp
    Saturation/ClauseContainer.hpp
    Saturation/ConsequenceFinder.hpp
    Saturation/Discount.hpp
    Saturation/ExtensionalityClauseContainer.hpp
    Saturation/LabelFinder.hpp
    Saturation/LRS.hpp
    Saturation/Otter.hpp
    Saturation/ProvingHelper.hpp
    Saturation/SaturationAlgorithm.hpp
    Saturation/Splitter.hpp
    Saturation/SymElOutput.hpp
    Saturation/PredicateSplitPassiveClauseContainer.hpp
    )
source_group(saturation_source_files FILES ${VAMPIRE_SATURATION_SOURCES})

set(VAMPIRE_SHELL_SOURCES
    Shell/AnswerExtractor.cpp
    #Shell/AxiomGenerator.cpp
    Shell/CommandLine.cpp
    Shell/CNF.cpp
    Shell/NewCNF.cpp
    Shell/NameReuse.cpp
    Shell/DistinctProcessor.cpp
    Shell/DistinctGroupExpansion.cpp
    Shell/EqResWithDeletion.cpp
    Shell/EqualityProxy.cpp
    Shell/EqualityProxyMono.cpp    
    Shell/Flattening.cpp
    Shell/FunctionDefinition.cpp
    Shell/GeneralSplitting.cpp
    Shell/GoalGuessing.cpp
    Shell/Grounding.cpp
    Shell/InequalitySplitting.cpp
    Shell/InterpolantMinimizer.cpp
    Shell/InterpolantMinimizerNew.cpp
    Shell/Interpolants.cpp
    Shell/InterpolantsNew.cpp    
    Shell/InterpretedNormalizer.cpp
    Shell/LaTeX.cpp
    Shell/Lexer.cpp
    Shell/LispLexer.cpp
    Shell/LispParser.cpp
    Shell/Naming.cpp
    Shell/NNF.cpp
    Shell/Normalisation.cpp
    Shell/Options.cpp
    Shell/PredicateDefinition.cpp
    Shell/Preprocess.cpp
    Shell/Property.cpp
    Shell/Rectify.cpp
    Shell/Skolem.cpp
    Shell/SimplifyFalseTrue.cpp
    Shell/SineUtils.cpp
    Shell/SMTFormula.cpp
    #Shell/SMTPrinter.cpp
    Shell/FOOLElimination.cpp
    Shell/Statistics.cpp
    Shell/SymbolDefinitionInlining.cpp
    Shell/SymbolOccurrenceReplacement.cpp
    Shell/SymCounter.cpp
    Shell/TermAlgebra.cpp
    Shell/TheoryAxioms.cpp
    Shell/TheoryFinder.cpp
    Shell/TheoryFlattening.cpp
    Shell/BlockedClauseElimination.cpp
    Shell/Token.cpp
    Shell/TPTPPrinter.cpp
    #Shell/TrivialPredicateRemover.cpp
    Shell/UIHelper.cpp
    Shell/VarManager.cpp
    #Shell/EqualityVariableRemover.cpp
    Shell/Lexer.cpp
    #Shell/PARSER_TKV.cpp
    Shell/Preprocess.cpp
    #Shell/SMTLEX.cpp
    #Shell/SMTPAR.cpp
    Shell/AnswerExtractor.hpp
    #Shell/AxiomGenerator.hpp
    Shell/CommandLine.hpp
    Shell/CNF.hpp
    Shell/NewCNF.hpp
    Shell/NameReuse.hpp
    Shell/DistinctProcessor.hpp
    Shell/DistinctGroupExpansion.hpp
    Shell/EqResWithDeletion.hpp
    Shell/EqualityProxy.hpp
    Shell/EqualityProxyMono.hpp
    Shell/Flattening.hpp
    Shell/FunctionDefinition.hpp
    Shell/GeneralSplitting.hpp
    Shell/Grounding.hpp
    Shell/InequalitySplitting.hpp
    Shell/InterpolantMinimizer.hpp
    Shell/InterpolantMinimizerNew.hpp    
    Shell/Interpolants.hpp
    Shell/InterpolantsNew.hpp
    Shell/InterpretedNormalizer.hpp
    Shell/LaTeX.hpp
    Shell/Lexer.hpp
    Shell/LispLexer.hpp
    Shell/LispParser.hpp
    Shell/Naming.hpp
    Shell/NNF.hpp
    Shell/Normalisation.hpp
    Shell/Options.hpp
    Shell/PredicateDefinition.hpp
    Shell/Preprocess.hpp
    Shell/Property.hpp
    Shell/Rectify.hpp
    Shell/Skolem.hpp
    Shell/SimplifyFalseTrue.hpp
    Shell/SineUtils.hpp
    Shell/SMTFormula.hpp
    Shell/SMTLIBLogic.hpp
    #Shell/SMTPrinter.hpp
    Shell/FOOLElimination.hpp
    Shell/Statistics.hpp
    Shell/SymbolDefinitionInlining.hpp
    Shell/SymbolOccurrenceReplacement.hpp
    Shell/SymCounter.hpp
    Shell/TermAlgebra.hpp
    Shell/TheoryAxioms.hpp
    Shell/TheoryFinder.hpp
    Shell/TheoryFlattening.hpp
    Shell/BlockedClauseElimination.hpp
    Shell/Token.hpp
    Shell/TPTPPrinter.hpp
    Shell/UnificationWithAbstractionConfig.hpp
    Shell/UnificationWithAbstractionConfig.cpp
    #Shell/TrivialPredicateRemover.hpp
    Shell/UIHelper.hpp
    Shell/VarManager.hpp
    Shell/Lexer.hpp
    #Shell/PARSER_TKV.hpp
    Shell/Preprocess.hpp
    #Shell/SMTLEX.hpp
    #Shell/SMTPAR.hpp
    Shell/SubexpressionIterator.cpp
    Shell/SubexpressionIterator.hpp
    # Shell/version.cpp
    )
source_group(shell_source_files FILES ${VAMPIRE_SHELL_SOURCES})

set(VAMPIRE_PARSE_SOURCES
    Parse/SMTLIB2.cpp
    Parse/TPTP.cpp
    Parse/SMTLIB2.hpp
    Parse/TPTP.hpp
    )
source_group(parse_source_files FILES ${VAMPIRE_PARSE_SOURCES})

set(
    VAMPIRE_FINITEMODELBUILDING_SOURCES
    FMB/ClauseFlattening.cpp
    FMB/FiniteModel.cpp
    FMB/FiniteModelBuilder.cpp
    FMB/FiniteModelMultiSorted.cpp
    FMB/FunctionRelationshipInference.cpp
    FMB/Monotonicity.cpp
    FMB/SortInference.cpp
    FMB/ClauseFlattening.hpp
    FMB/DefinitionIntroduction.hpp
    FMB/FiniteModel.hpp
    FMB/FiniteModelBuilder.hpp
    FMB/FiniteModelMultiSorted.hpp    
    FMB/FunctionRelationshipInference.hpp
    FMB/ModelCheck.hpp
    FMB/Monotonicity.hpp
    FMB/SortInference.hpp
    )
source_group(finitemodelbuilding_source_files FILES ${VAMPIRE_FINITEMODELBUILDING_SOURCES})

set(VAMPIRE_SMTCOMP_SOURCES
    SAT/Z3MainLoop.cpp
    SAT/Z3MainLoop.hpp
    )
source_group(smt_comp_source_files FILES ${VAMPIRE_SMTCOMP_SOURCES})

set(VAMPIRE_CASC_SOURCES
    CASC/PortfolioMode.cpp
    CASC/Schedules.cpp
    CASC/ScheduleExecutor.cpp
    CASC/CLTBMode.cpp
    CASC/CLTBModeLearning.cpp
    CASC/PortfolioMode.hpp
    CASC/Schedules.hpp
    CASC/ScheduleExecutor.hpp
    CASC/CLTBMode.hpp
    CASC/CLTBModeLearning.hpp
    )
source_group(casc_source_files FILES ${VAMPIRE_CASC_SOURCES})

set(VAMPIRE_TESTING_SOURCES
    Test/UnitTesting.cpp
    Test/UnitTesting.hpp
    Test/SyntaxSugar.hpp
    Test/SyntaxSugar.cpp
    Test/TestUtils.hpp
    Test/TestUtils.cpp
    )
source_group(testing_files FILES ${VAMPIRE_TESTING_SOURCES})

set(UNIT_TESTS
    UnitTests/tDHMap.cpp
    UnitTests/tQuotientE.cpp
    UnitTests/tImplicationSetClosure.cpp
    UnitTests/tUnificationWithAbstraction.cpp
    UnitTests/tGaussianElimination.cpp
    UnitTests/tArithmeticSubtermGeneralization.cpp
    UnitTests/tInterpretedFunctions.cpp
    UnitTests/tRebalance.cpp
    UnitTests/tDisagreement.cpp
    UnitTests/tDynamicHeap.cpp
    UnitTests/tInduction.cpp
    UnitTests/tIntegerConstantType.cpp
    UnitTests/tSATSolver.cpp
    UnitTests/tArithCompare.cpp
    UnitTests/tSyntaxSugar.cpp
    UnitTests/tSkipList.cpp
    UnitTests/tfork.cpp
    UnitTests/tBinaryHeap.cpp
    UnitTests/tSafeRecursion.cpp
    UnitTests/tKBO.cpp
    UnitTests/tLPO.cpp
    UnitTests/tRatioKeeper.cpp
    UnitTests/tTwoVampires.cpp
    UnitTests/tOptionConstraints.cpp
    UnitTests/tSCCAnalyzer.cpp
    UnitTests/tDHMultiset.cpp
    UnitTests/tList.cpp
    UnitTests/tBottomUpEvaluation.cpp
    UnitTests/tCoproduct.cpp
    UnitTests/tEqualityResolution.cpp
    UnitTests/tIterator.cpp
    UnitTests/tOption.cpp
    UnitTests/tStack.cpp
    )
source_group(unit_tests FILES ${UNIT_TESTS})

set(UNIT_TESTS_Z3
    UnitTests/tTheoryInstAndSimp.cpp
    UnitTests/tZ3Interfacing.cpp
    )
source_group(unit_tests_z3 FILES ${UNIT_TESTS_Z3})



# also include forwards.hpp?
set(VAMPIRE_SOURCES 
    ${VAMPIRE_DEBUG_SOURCES}
    ${VAMPIRE_LIB_SOURCES}
    ${VAMPIRE_LIB_SYS_SOURCES}
    ${VAMPIRE_KERNEL_SOURCES}
    ${VAMPIRE_INDEXING_SOURCES}
    ${VAMPIRE_INFERENCE_SOURCES}
    ${VAMPIRE_INSTANCEGENERATION_SOURCES}
    ${VAMPIRE_SAT_SOURCES}
    ${VAMPIRE_DECISION_PROCEDURES_SOURCES}
    ${VAMPIRE_SATURATION_SOURCES}
    ${VAMPIRE_SHELL_SOURCES}
    ${VAMPIRE_PARSE_SOURCES}
    ${VAMPIRE_FINITEMODELBUILDING_SOURCES}
    ${VAMPIRE_SMTCOMP_SOURCES}
    ${VAMPIRE_MINISAT_SOURCES}
    ${VAMPIRE_CASC_SOURCES}
    Forwards.hpp
    "${CMAKE_CURRENT_BINARY_DIR}/version.cpp"
    )

################################################################
# compiler flag configuration
################################################################
# possible flags that might be useful in future
# "-ftrapv"
# "-pedantic"
# "-Wextra"
# "-Wconversion"
# "$<$<CONFIG:DEBUG>:-fsanitize=undefined>"
# "$<$<CONFIG:DEBUG>:-fsanitize=integer>"
# "$<$<CONFIG:DEBUG>:-fsanitize=address>"
# "$<$<CONFIG:DEBUG>:-O0>"
# "$<$<CONFIG:RELEASE>:-O3>"

# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# set preprocessor defines
add_compile_definitions(CHECK_LEAKS=0)
if(CMAKE_BUILD_TYPE STREQUAL Debug)
  add_compile_definitions(VDEBUG=1 UNIX_USE_SIGALRM=1)
elseif(CMAKE_BUILD_TYPE STREQUAL Release)
  add_compile_definitions(VDEBUG=0)
endif()

if (CYGWIN)
 add_compile_definitions(_BSD_SOURCE)
endif()
                    
# configure warning flags
if(CMAKE_CXX_COMPILER_ID STREQUAL GNU OR CMAKE_CXX_COMPILER_ID MATCHES Clang$)
  add_compile_options(-Wall)
endif()

################################################################
# z3 stuff
################################################################

# find Z3 automatically!
# normally this is just in /z3/build/, but this can be overridden
find_package(
  Z3
  CONFIG
    NO_CMAKE_PATH
    NO_CMAKE_ENVIRONMENT_PATH
    NO_SYSTEM_ENVIRONMENT_PATH
    NO_CMAKE_PACKAGE_REGISTRY
    NO_CMAKE_SYSTEM_PATH
    NO_CMAKE_SYSTEM_PACKAGE_REGISTRY
    PATHS
      ${CMAKE_SOURCE_DIR}/z3/build/
)
if (NOT Z3_FOUND)
  message(STATUS "No Z3 found -- Compiling without SMT support.")
  add_compile_definitions(VZ3=0)
else ()
  message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
  include_directories(${Z3_CXX_INCLUDE_DIRS})
  if(NOT BUILD_SHARED_LIBS AND Z3_FOUND AND CMAKE_CXX_COMPILER_ID STREQUAL GNU)
    # https://stackoverflow.com/questions/58848694/gcc-whole-archive-recipe-for-static-linking-to-pthread-stopped-working-in-rec
    message(STATUS "Adding workaround for gcc static linking against pthread")
    link_libraries(${Z3_LIBRARIES} -pthread -Wl,--whole-archive -lrt -lpthread -Wl,--no-whole-archive)
  else()
    link_libraries(${Z3_LIBRARIES})
  endif()

  # Z3 needs threads now
  if (APPLE)
    set(CMAKE_THREAD_LIBS_INIT "-lpthread")
    set(CMAKE_HAVE_THREADS_LIBRARY 1)
    set(CMAKE_USE_WIN32_THREADS_INIT 0)
    set(CMAKE_USE_PTHREADS_INIT 1)
    set(THREADS_PREFER_PTHREAD_FLAG ON)
  else ()
    set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
    set(THREADS_PREFER_PTHREAD_FLAG TRUE)
    find_package(Threads REQUIRED)
    link_libraries(Threads::Threads)
  endif ()

  add_library(Z3 SHARED IMPORTED)
  set_property(TARGET Z3 PROPERTY IMPORTED_LOCATION ${Z3_LIBRARY})
  add_compile_definitions(VZ3=1)
  set(VAMPIRE_BINARY_Z3 _z3)
  set(UNIT_TESTS ${UNIT_TESTS} ${UNIT_TESTS_Z3})
endif()

################################################################
# build objects
################################################################
add_library(obj OBJECT ${VAMPIRE_SOURCES})
if (COMPILE_TESTS) 
  add_library(test_obj OBJECT ${VAMPIRE_TESTING_SOURCES})
endif()

################################################################
# UNIT TESTING 
################################################################

set(UNIT_TEST_OBJ   )
set(UNIT_TEST_CASES )
if (COMPILE_TESTS) 
  include(CTest)
  foreach(test_file ${UNIT_TESTS})
    get_filename_component(test_name ${test_file} NAME_WE)
    string(REGEX REPLACE "^t" "" test_name ${test_name})

    # compiling the test case object 
    add_library(${test_name}_obj OBJECT ${test_file})
    target_compile_definitions(${test_name}_obj PUBLIC 
      UNIT_ID_STR=\"${test_name}\"
      UNIT_ID=${test_name}
      )
    set(UNIT_TEST_OBJ   ${UNIT_TEST_OBJ}   $<TARGET_OBJECTS:${test_name}_obj>)
    set(UNIT_TEST_CASES ${UNIT_TEST_CASES} ${test_name})
  endforeach()

  # build test executable
  add_executable(
    vtest
    ${UNIT_TEST_OBJ}
    $<TARGET_OBJECTS:obj>
    $<TARGET_OBJECTS:test_obj>
    )

  # add indivitual units as test cases
  foreach(case ${UNIT_TEST_CASES})
    add_test(${case} ${CMAKE_BINARY_DIR}/vtest run ${case})
    set_tests_properties(${case}
          PROPERTIES
          TIMEOUT 20)
  endforeach()

endif() # COMPILE_TESTS

#################################################################
# automated generation of Vampire revision information from git #
#################################################################
set(VAMPIRE_VERSION_NUMBER 4.6.1)

execute_process(
    COMMAND git rev-parse --is-inside-work-tree
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_IS_REPOSITORY
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

if (GIT_IS_REPOSITORY STREQUAL true)

  execute_process(
    COMMAND git log -1 --format=%h\ on\ %ci
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_COMMIT_DESCRIPTION
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  execute_process(
    COMMAND git rev-parse --abbrev-ref HEAD
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_BRANCH
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  execute_process(
    COMMAND git rev-list HEAD --count
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_REV_COUNT
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  execute_process(
    COMMAND git log -1 --format=%h
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_COMMIT_HASH
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  set(VAMPIRE_BINARY_HASH "_${GIT_COMMIT_HASH}")
  set(VAMPIRE_BINARY_BRANCH "_${GIT_BRANCH}")
  set(VAMPIRE_BINARY_REV_COUNT "_${GIT_REV_COUNT}")
endif()

################################################################
# binary name
################################################################
if(CMAKE_BUILD_TYPE STREQUAL Debug)
  set(VAMPIRE_BINARY_BUILD _dbg)
elseif(CMAKE_BUILD_TYPE STREQUAL Release)
  set(VAMPIRE_BINARY_BUILD _rel)
else()
  set(VAMPIRE_BINARY_BUILD "_${CMAKE_BUILD_TYPE}")
endif()
set(VAMPIRE_BINARY "vampire${VAMPIRE_BINARY_Z3}${VAMPIRE_BINARY_BUILD}${VAMPIRE_BINARY_STATIC}${VAMPIRE_BINARY_BRANCH}${VAMPIRE_BINARY_REV_COUNT}")
message(STATUS "Setting binary name to '${VAMPIRE_BINARY}'")

################################################################
# epilogue
################################################################
add_executable(vampire vampire.cpp $<TARGET_OBJECTS:obj>)
set_target_properties(vampire PROPERTIES
  OUTPUT_NAME ${VAMPIRE_BINARY}
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
  )
configure_file(version.cpp.in version.cpp)

if(CMAKE_BUILD_TYPE STREQUAL Release AND IPO)
  message(STATUS "compiling Vampire with IPO: this might take a while")
  set_property(TARGET obj PROPERTY INTERPROCEDURAL_OPTIMIZATION true)
  set_property(TARGET vampire PROPERTY INTERPROCEDURAL_OPTIMIZATION true)
endif()
