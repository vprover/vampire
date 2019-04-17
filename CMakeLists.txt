cmake_minimum_required (VERSION 3.12.1)

project(Vampire)

# require the compiler to use C++11
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

#static
if (NOT BUILD_SHARED_LIBS)
  SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
  # SET(BUILD_SHARED_LIBS OFF)
  SET(CMAKE_EXE_LINKER_FLAGS "-static")
endif()

#debug flags

set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DVDEBUG=1 -DUNIX_USE_SIGALRM=1 -DGNUMP=0 ")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -DVDEBUG=0")


# support sourcetrail
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_compile_options(
#    "-Wno-exceptions"  # there's just too many warnings if this is enabled # this option doesn't seem to exist in all compilers
    # "-ftrapv"
    # "-pedantic"
    # "-Wall"
    # "-Wextra"
    # "-Wconversion"
    # "$<$<CONFIG:DEBUG>:-fsanitize=undefined>"
    # "$<$<CONFIG:DEBUG>:-fsanitize=integer>"
    # "$<$<CONFIG:DEBUG>:-fsanitize=address>"
    # "$<$<CONFIG:DEBUG>:-O0>"
    # "$<$<CONFIG:RELEASE>:-O3>"
)

# add directoy, where we store all custom files for finding libraries which are not build using cmake (i.e. currently z3 only), to the search path of cmake
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/")

# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# Set the output folder where the binary will be created (i.e. build/dir)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)




################################################################
# minisat stuff
################################################################
#TODO: refactor minisat into independent imported target


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
#    Lib/Graph.cpp
    Lib/Hash.cpp
    Lib/Int.cpp
    Lib/IntNameTable.cpp
    Lib/IntUnionFind.cpp
    Lib/MemoryLeak.cpp
    Lib/MultiCounter.cpp
    Lib/NameArray.cpp
#    Lib/OptionsReader.cpp
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
    Lib/Enumerator.hpp
    Lib/Environment.hpp
    Lib/Event.hpp
    Lib/Exception.hpp
    Lib/fdstream.hpp
    Lib/FreshnessGuard.hpp
#    Lib/Graph.hpp
    Lib/Hash.hpp
    Lib/ImplicationSetClosure.hpp
    Lib/InPlaceStack.hpp
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
#    Lib/OptionsReader.hpp
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
    Kernel/KBO.cpp
    Kernel/KBOForEPR.cpp
    Kernel/LiteralSelector.cpp
    Kernel/LookaheadLiteralSelector.cpp
    Kernel/MainLoop.cpp
#    Kernel/MatchTag.cpp
    Kernel/Matcher.cpp
    Kernel/MaximalLiteralSelector.cpp
    Kernel/MLMatcher.cpp
    Kernel/MLVariant.cpp
    Kernel/Ordering.cpp
    Kernel/Ordering_Equality.cpp
    Kernel/Problem.cpp
    Kernel/Renaming.cpp
    Kernel/RobSubstitution.cpp
    Kernel/Signature.cpp
    Kernel/SortHelper.cpp
    Kernel/Sorts.cpp
    Kernel/SpassLiteralSelector.cpp
    Kernel/SubformulaIterator.cpp
    Kernel/Substitution.cpp
    Kernel/Term.cpp
    Kernel/TermIterators.cpp
    Kernel/TermTransformer.cpp
    Kernel/Theory.cpp
#    Kernel/Assignment.cpp
#    Kernel/Constraint.cpp
#    Kernel/Number.cpp
#    Kernel/Rational.cpp
#    Kernel/V2CIndex.cpp
    Kernel/Signature.cpp
    Kernel/Unit.cpp
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
    Kernel/KBO.hpp
    Kernel/KBOForEPR.hpp
    Kernel/LiteralComparators.hpp
    Kernel/LiteralSelector.hpp
    Kernel/LookaheadLiteralSelector.hpp
    Kernel/MainLoop.hpp
#    Kernel/MatchTag.hpp
    Kernel/Matcher.hpp
    Kernel/MaximalLiteralSelector.hpp
    Kernel/MLMatcher.hpp
    Kernel/MLVariant.hpp
    Kernel/Ordering.hpp
    Kernel/Problem.hpp
    Kernel/RCClauseStack.hpp
    Kernel/Renaming.hpp
    Kernel/RobSubstitution.hpp
    Kernel/Signature.hpp
    Kernel/SortHelper.hpp
    Kernel/Sorts.hpp
    Kernel/SpassLiteralSelector.hpp
    Kernel/SubformulaIterator.hpp
    Kernel/SubstHelper.hpp
    Kernel/Substitution.hpp
    Kernel/Term.hpp
    Kernel/TermIterators.hpp
    Kernel/TermTransformer.hpp
    Kernel/Theory.hpp
#    Kernel/Assignment.hpp
#    Kernel/Constraint.hpp
#    Kernel/Number.hpp
#    Kernel/Rational.hpp
#    Kernel/V2CIndex.hpp
    Kernel/Signature.hpp
    Kernel/Unit.hpp
    Kernel/LPO.cpp
    Kernel/LPO.hpp
    )
source_group(kernel_source_files FILES ${VAMPIRE_KERNEL_SOURCES})

set(VAMPIRE_INDEXING_SOURCES
    Indexing/AcyclicityIndex.cpp
    Indexing/ClauseCodeTree.cpp
    Indexing/ClauseVariantIndex.cpp
    Indexing/CodeTree.cpp
    Indexing/CodeTreeInterfaces.cpp
#    Indexing/FormulaIndex.cpp
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
    Indexing/FormulaIndex.hpp
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
    Inferences/BackwardSubsumptionResolution.cpp
    Inferences/BinaryResolution.cpp
    Inferences/Condensation.cpp
#    Inferences/CTFwSubsAndRes.cpp
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
    Inferences/GlobalSubsumption.cpp
    Inferences/HyperSuperposition.cpp
    Inferences/InnerRewriting.cpp
    Inferences/EquationalTautologyRemoval.cpp
    Inferences/Induction.cpp
    Inferences/InferenceEngine.cpp
    Inferences/Instantiation.cpp
    Inferences/InterpretedEvaluation.cpp
    Inferences/SLQueryBackwardSubsumption.cpp
    Inferences/Superposition.cpp
    Inferences/TautologyDeletionISE.cpp
    Inferences/TermAlgebraReasoning.cpp
    Inferences/URResolution.cpp
    Inferences/BackwardDemodulation.hpp
    Inferences/BackwardSubsumptionResolution.hpp
    Inferences/BinaryResolution.hpp
    Inferences/Condensation.hpp
#    Inferences/CTFwSubsAndRes.hpp
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
    Inferences/InferenceEngine.hpp
    Inferences/Instantiation.hpp
    Inferences/InterpretedEvaluation.hpp
    Inferences/SLQueryBackwardSubsumption.hpp
    Inferences/Superposition.hpp
    Inferences/TautologyDeletionISE.hpp
    Inferences/TermAlgebraReasoning.hpp
    Inferences/URResolution.hpp
    Inferences/TheoryInstAndSimp.hpp
    Inferences/TheoryInstAndSimp.cpp  # this is theory instantiation
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
    SAT/ClauseDisposer.cpp
    SAT/DIMACS.cpp
    SAT/FallbackSolverWrapper.cpp
    SAT/lglib.c
    SAT/lglopts.c
    SAT/MinimizingSolver.cpp
    SAT/Preprocess.cpp
    SAT/RestartStrategy.cpp
    SAT/SAT2FO.cpp
    SAT/SATClause.cpp
    SAT/SATInference.cpp
    SAT/SATLiteral.cpp
    SAT/TWLSolver.cpp
    SAT/VariableSelector.cpp
    SAT/Z3Interfacing.cpp

    SAT/BufferedSolver.hpp
    SAT/ClauseDisposer.hpp
    SAT/DIMACS.hpp
    SAT/FallbackSolverWrapper.hpp
    SAT/MinimizingSolver.hpp
    SAT/Preprocess.hpp
    SAT/RestartStrategy.hpp
    SAT/SAT2FO.hpp
    SAT/SATClause.hpp
    SAT/SATInference.hpp
    SAT/SATLiteral.hpp
    SAT/SATSolver.hpp
    SAT/TWLSolver.hpp
    SAT/VariableSelector.hpp
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
    Saturation/ClauseContainer.cpp
    Saturation/ConsequenceFinder.cpp
    Saturation/Discount.cpp
    Saturation/ExtensionalityClauseContainer.cpp
    Saturation/LabelFinder.cpp
    Saturation/Limits.cpp
    Saturation/LRS.cpp
    Saturation/Otter.cpp
    Saturation/ProvingHelper.cpp
    Saturation/SaturationAlgorithm.cpp
    Saturation/Splitter.cpp
    Saturation/SymElOutput.cpp
    Saturation/AWPassiveClauseContainer.hpp
    Saturation/ClauseContainer.hpp
    Saturation/ConsequenceFinder.hpp
    Saturation/Discount.hpp
    Saturation/ExtensionalityClauseContainer.hpp
    Saturation/LabelFinder.hpp
    Saturation/Limits.hpp
    Saturation/LRS.hpp
    Saturation/Otter.hpp
    Saturation/ProvingHelper.hpp
    Saturation/SaturationAlgorithm.hpp
    Saturation/Splitter.hpp
    Saturation/SymElOutput.hpp
    )
source_group(saturation_source_files FILES ${VAMPIRE_SATURATION_SOURCES})

set(VAMPIRE_SHELL_SOURCES
    Shell/AnswerExtractor.cpp
    #Shell/AxiomGenerator.cpp
    Shell/BFNT.cpp
    Shell/BFNTMainLoop.cpp
    Shell/CommandLine.cpp
    Shell/CNF.cpp
    Shell/NewCNF.cpp
    #Shell/CParser.cpp
    Shell/DistinctProcessor.cpp
    Shell/DistinctGroupExpansion.cpp
    Shell/EqResWithDeletion.cpp
    #Shell/EqualityAxiomatizer.cpp
    Shell/EqualityProxy.cpp
    Shell/Flattening.cpp
    Shell/FunctionDefinition.cpp
    Shell/GeneralSplitting.cpp
    Shell/GoalGuessing.cpp
    #Shell/GlobalOptions.cpp
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
    #Shell/PDUtils.cpp
    Shell/PredicateDefinition.cpp
    Shell/Preprocess.cpp
    Shell/Property.cpp
    Shell/Rectify.cpp
    #Shell/Refutation.cpp
    Shell/Skolem.cpp
    Shell/SimplifyFalseTrue.cpp
    Shell/SimplifyProver.cpp
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
    Shell/TrivialPredicateRemover.cpp
    Shell/UIHelper.cpp
    Shell/VarManager.cpp
    #Shell/ConstantRemover.cpp
    #Shell/ConstraintReaderBack.cpp
    #Shell/EqualityVariableRemover.cpp
    #Shell/EquivalentVariableRemover.cpp
    #Shell/HalfBoundingRemover.cpp
    Shell/Lexer.cpp
    #Shell/PARSER_TKV.cpp
    Shell/Preprocess.cpp
    #Shell/SMTLEX.cpp
    #Shell/SMTPAR.cpp
    #Shell/SubsumptionRemover.cpp
    Shell/AnswerExtractor.hpp
    #Shell/AxiomGenerator.hpp
    Shell/BFNT.hpp
    Shell/BFNTMainLoop.hpp
    Shell/CommandLine.hpp
    Shell/CNF.hpp
    Shell/NewCNF.hpp
    #Shell/CParser.hpp
    Shell/DistinctProcessor.hpp
    Shell/DistinctGroupExpansion.hpp
    Shell/EqResWithDeletion.hpp
    #Shell/EqualityAxiomatizer.hpp
    Shell/EqualityProxy.hpp
    Shell/Flattening.hpp
    Shell/FunctionDefinition.hpp
    Shell/GeneralSplitting.hpp
    #Shell/GlobalOptions.hpp
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
    #Shell/PDUtils.hpp
    Shell/PredicateDefinition.hpp
    Shell/Preprocess.hpp
    Shell/Property.hpp
    Shell/Rectify.hpp
    #Shell/Refutation.hpp
    Shell/Skolem.hpp
    Shell/SimplifyFalseTrue.hpp
    Shell/SimplifyProver.hpp
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
    Shell/TrivialPredicateRemover.hpp
    Shell/UIHelper.hpp
    Shell/VarManager.hpp
    #Shell/ConstantRemover.hpp
    #Shell/ConstraintReaderBack.hpp
    #Shell/EqualityVariableRemover.hpp
    #Shell/EquivalentVariableRemover.hpp
    #Shell/HalfBoundingRemover.hpp
    Shell/Lexer.hpp
    #Shell/PARSER_TKV.hpp
    Shell/Preprocess.hpp
    #Shell/SMTLEX.hpp
    #Shell/SMTPAR.hpp
    #Shell/SubsumptionRemover.hpp
    Shell/SubexpressionIterator.cpp
    Shell/SubexpressionIterator.hpp
    # Shell/version.cpp
    )
source_group(shell_source_files FILES ${VAMPIRE_SHELL_SOURCES})

set(VAMPIRE_PARSE_SOURCES
    Parse/SMTLIB2.cpp
    Parse/TPTP.cpp
    Parse/SMTLIB.hpp
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
    # Test/CheckedSatSolver.cpp
    # Test/CheckedSatSolver.hpp
    Global.cpp
    vampire.cpp
    "${CMAKE_CURRENT_BINARY_DIR}/version.cpp"
    )

# TODO: we want at least vampire_dbg, vampire_rel, vampire_z3_dbg, vampire_z3_rel
#message(STATUS "a test message")

add_executable(vampire ${VAMPIRE_SOURCES})
target_compile_definitions(vampire PRIVATE  CHECK_LEAKS=0)

################################################################
# z3 stuff
################################################################
# TODO: one could also add automatic installation of z3 and minisat (cf. github-seahorn solution)
find_package(Z3 CONFIG NO_DEFAULT_PATH)
if (NOT Z3_FOUND)
  message(WARNING "No Z3 found -- Compiling without SMT support.")
  target_compile_definitions(vampire PRIVATE VZ3=0)
else ()
  message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
  message(STATUS "Z3_DIR: ${Z3_DIR}")
  target_include_directories(vampire PRIVATE ${Z3_CXX_INCLUDE_DIRS})
  target_link_libraries(vampire PRIVATE ${Z3_LIBRARIES})
  add_library(Z3 SHARED IMPORTED)
  set_property(TARGET Z3 PROPERTY IMPORTED_LOCATION ${Z3_LIBRARY})
  target_compile_definitions(vampire PRIVATE VZ3=1)
endif()





#################################################################
# automated generation of Vampire revision information from git #
#################################################################
set(VAMPIRE_VERSION_NUMBER "4.3.0")

execute_process(
    COMMAND git log -1 --format=%h\ on\ %ci
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_COMMIT_DESCRIPTION
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

configure_file(version.cpp.in version.cpp)
