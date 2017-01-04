cmake_minimum_required (VERSION 3.6.3)

project (Vampire)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# include path where we store all custom files for finding libraries which are not build using cmake (i.e. currently z3 only)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/")




# Set the output folder where your program will be created
set(CMAKE_BINARY_DIR ${CMAKE_SOURCE_DIR}/bin)
set(EXECUTABLE_OUTPUT_PATH ${CMAKE_BINARY_DIR})
set(LIBRARY_OUTPUT_PATH ${CMAKE_BINARY_DIR})

# The following folder will be included
include_directories("${PROJECT_SOURCE_DIR}")


################################################################
# z3 stuff
################################################################
# TODO: one could also add automatic installation of z3 and minisat (cf. github-seahorn solution)
find_package(Z3 REQUIRED)
add_library(Z3 INTERFACE IMPORTED)


################################################################
# minisat stuff
################################################################
#TODO: refactor minisat into independent imported target


################################################################
# define all vampire sources, 
# generate the main target and 
# link it against the libraries
################################################################
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

set(VAMPIRE_MINISAT_SOURCES
    Minisat/core/Solver.cc
    Minisat/simp/SimpSolver.cc
	Minisat/utils/Options.cc
	Minisat/utils/System.cc
	SAT/MinisatInterfacing.cpp
	SAT/MinisatInterfacingNewSimp.cpp
	)
source_group(minisat_source_files FILES ${VAMPIRE_MINISAT_SOURCES})

set(VAMPIRE_DEBUG_SOURCES
	Debug/Assertion.cpp
	Debug/RuntimeStatistics.cpp
	Debug/Tracer.cpp
	)
source_group(debug_source_files FILES ${VAMPIRE_DEBUG_SOURCES})

set(VAMPIRE_LIB_SOURCES
	Lib/Allocator.cpp
    Lib/DHMap.cpp
    Lib/Environment.cpp
	Lib/Event.cpp
	Lib/Exception.cpp
    Lib/Graph.cpp
    Lib/Hash.cpp
    Lib/Int.cpp
    Lib/IntNameTable.cpp
    Lib/IntUnionFind.cpp
    Lib/MemoryLeak.cpp
    Lib/MultiCounter.cpp
    Lib/NameArray.cpp
    Lib/OptionsReader.cpp
    Lib/Random.cpp
    Lib/StringUtils.cpp
    Lib/System.cpp
    Lib/TimeCounter.cpp
    Lib/Timer.cpp
	)
source_group(lib_source_files FILES ${VAMPIRE_LIB_SOURCES})

set(VAMPIRE_LIB_SYS_SOURCES
	Lib/Sys/Multiprocessing.cpp
    Lib/Sys/Semaphore.cpp
    Lib/Sys/SyncPipe.cpp
	)
source_group(lib_sys_source_files FILES ${VAMPIRE_LIB_SYS_SOURCES})

set(VAMPIRE_KERNEL_SOURCES
	Kernel/Clause.cpp
    Kernel/ClauseQueue.cpp
    Kernel/ColorHelper.cpp
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
    Kernel/MatchTag.cpp
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
    Kernel/SubformulaIterator.cpp
    Kernel/Substitution.cpp
    Kernel/Term.cpp
    Kernel/TermIterators.cpp
    Kernel/TermTransformer.cpp
    Kernel/Theory.cpp
    Kernel/Assignment.cpp
    Kernel/Constraint.cpp
    Kernel/Number.cpp
    Kernel/Rational.cpp
    Kernel/V2CIndex.cpp
    Kernel/Signature.cpp
    Kernel/Unit.cpp
    Kernel/Unit.hpp
	)
source_group(kernel_source_files FILES ${VAMPIRE_KERNEL_SOURCES})

set(VAMPIRE_INDEXING_SOURCES
	Indexing/AcyclicityIndex.cpp
	Indexing/ClauseCodeTree.cpp
    Indexing/ClauseVariantIndex.cpp
    Indexing/CodeTree.cpp
    Indexing/CodeTreeInterfaces.cpp
    Indexing/FormulaIndex.cpp
    Indexing/GroundingIndex.cpp
    Indexing/Index.cpp
    Indexing/IndexManager.cpp
    Indexing/LiteralIndex.cpp
    Indexing/LiteralMiniIndex.cpp
    Indexing/LiteralSubstitutionTree.cpp
    Indexing/LiteralSubstitutionTreeWithoutTop.cpp
    Indexing/ResultSubstitution.cpp
    Indexing/SubstitutionTree.cpp
    Indexing/SubstitutionTree_FastGen.cpp
    Indexing/SubstitutionTree_FastInst.cpp
    Indexing/SubstitutionTree_Nodes.cpp
    Indexing/TermCodeTree.cpp
    Indexing/TermIndex.cpp
    Indexing/TermSharing.cpp
    Indexing/TermSubstitutionTree.cpp
	)
source_group(indexing_source_files FILES ${VAMPIRE_INDEXING_SOURCES})

set(VAMPIRE_INFERENCE_SOURCES
	Inferences/BackwardDemodulation.cpp
    Inferences/BackwardSubsumptionResolution.cpp
    Inferences/BinaryResolution.cpp
    Inferences/Condensation.cpp
    Inferences/CTFwSubsAndRes.cpp
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
    Inferences/InferenceEngine.cpp
    Inferences/Instantiation.cpp
    Inferences/InterpretedEvaluation.cpp
    Inferences/RefutationSeekerFSE.cpp
    Inferences/SLQueryBackwardSubsumption.cpp
    Inferences/SLQueryForwardSubsumption.cpp
    Inferences/Superposition.cpp
    Inferences/TautologyDeletionISE.cpp
    Inferences/TermAlgebraReasoning.cpp
    Inferences/URResolution.cpp
	)
source_group(inference_source_files FILES ${VAMPIRE_INFERENCE_SOURCES})

set(VAMPIRE_INSTANCEGENERATION_SOURCES
	InstGen/IGAlgorithm.cpp
    InstGen/ModelPrinter.cpp
	)
source_group(instancegeneration_source_files FILES ${VAMPIRE_INSTANCEGENERATION_SOURCES})

set(VAMPIRE_SAT_SOURCES
	SAT/ClauseDisposer.cpp
    SAT/DIMACS.cpp
    SAT/MinimizingSolver.cpp
    SAT/Preprocess.cpp
    SAT/RestartStrategy.cpp
    SAT/SAT2FO.cpp
    SAT/SATClause.cpp
    SAT/SATInference.cpp
    SAT/SATLiteral.cpp
    SAT/TWLSolver.cpp
    SAT/VariableSelector.cpp
    SAT/LingelingInterfacing.cpp
	SAT/Z3Interfacing.cpp
    SAT/lglib.c
    SAT/lglopts.c
	SAT/BufferedSolver.cpp
	SAT/FallbackSolverWrapper.cpp
	)
source_group(sat_source_files FILES ${VAMPIRE_SAT_SOURCES})

set(VAMPIRE_DECISION_PROCEDURES_SOURCES
	DP/ShortConflictMetaDP.cpp
    DP/SimpleCongruenceClosure.cpp
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
	)
source_group(saturation_source_files FILES ${VAMPIRE_SATURATION_SOURCES})

set(VAMPIRE_SHELL_SOURCES
	Shell/AnswerExtractor.cpp
    Shell/AxiomGenerator.cpp
    Shell/BFNT.cpp
    Shell/BFNTMainLoop.cpp
    Shell/CommandLine.cpp
    Shell/CNF.cpp
    Shell/NewCNF.cpp
    Shell/CParser.cpp
    Shell/DistinctProcessor.cpp
    Shell/DistinctGroupExpansion.cpp
    Shell/EqResWithDeletion.cpp
    Shell/EqualityAxiomatizer.cpp
    Shell/EqualityProxy.cpp
    Shell/Flattening.cpp
    Shell/FunctionDefinition.cpp
    Shell/GeneralSplitting.cpp
    Shell/GlobalOptions.cpp
    Shell/Grounding.cpp
    Shell/InequalitySplitting.cpp
    Shell/InterpolantMinimizer.cpp
    Shell/Interpolants.cpp
    Shell/InterpretedNormalizer.cpp
    Shell/LaTeX.cpp
    Shell/Lexer.cpp
    Shell/LispLexer.cpp
    Shell/LispParser.cpp
    Shell/Naming.cpp
    Shell/NNF.cpp
    Shell/Normalisation.cpp
    Shell/Options.cpp
    Shell/PDUtils.cpp
    Shell/PredicateDefinition.cpp
    Shell/Preprocess.cpp
    Shell/Property.cpp
    Shell/Rectify.cpp
    Shell/Refutation.cpp
    Shell/Skolem.cpp
    Shell/SimplifyFalseTrue.cpp
    Shell/SimplifyProver.cpp
    Shell/SineUtils.cpp
    Shell/SMTFormula.cpp
    Shell/SMTPrinter.cpp
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
    Shell/ConstantRemover.cpp
    Shell/ConstraintReaderBack.cpp
    Shell/EqualityVariableRemover.cpp
    Shell/EquivalentVariableRemover.cpp
    Shell/HalfBoundingRemover.cpp
    Shell/Lexer.cpp
    Shell/PARSER_TKV.cpp
    Shell/Preprocess.cpp
    Shell/SMTLEX.cpp
    Shell/SMTPAR.cpp
    Shell/SubsumptionRemover.cpp
	)
source_group(shell_source_files FILES ${VAMPIRE_SHELL_SOURCES})

set(VAMPIRE_PARSE_SOURCES
	Parse/SMTLIB.cpp
    Parse/SMTLIB2.cpp
    Parse/TPTP.cpp
    )
source_group(parse_source_files FILES ${VAMPIRE_PARSE_SOURCES})

set(VAMPIRE_TABULATION_SOURCES
	Tabulation/Producer.cpp
    Tabulation/TabulationAlgorithm.cpp
    Tabulation/TabulationContainers.cpp
    )
source_group(tabulation_source_files FILES ${VAMPIRE_TABULATION_SOURCES})

set(VAMPIRE_PROGRAM_SOURCES
	Program/Type.cpp
    Program/LoopAnalyzer.cpp
    Program/Analyze.cpp
    Program/Path.cpp
    Program/Expression.cpp
    Program/Statement.cpp
    Program/Variable.cpp
    Program/InvariantHelper.cpp
    )
source_group(program_source_files FILES ${VAMPIRE_PROGRAM_SOURCES})

set(
    VAMPIRE_FINITEMODELBUILDING_SOURCES
	FMB/ClauseFlattening.cpp
    FMB/SortInference.cpp
	FMB/Monotonicity.cpp
	FMB/FunctionRelationshipInference.cpp
	FMB/FiniteModel.cpp
	FMB/FiniteModelMultiSorted.cpp
    FMB/FiniteModelBuilder.cpp
	)
source_group(finitemodelbuilding_source_files FILES ${VAMPIRE_FINITEMODELBUILDING_SOURCES})

set(VAMPIRE_CASC_SOURCES
	CASC/CASCMode.cpp
    CASC/CASCMultiMode.cpp
    CASC/CLTBMode.cpp
    CASC/CLTBModeLearning.cpp
    CASC/CMZRMode.cpp
    CASC/ForkingCM.cpp
    CASC/SpawningCM.cpp
    )
source_group(casc_source_files FILES ${VAMPIRE_CASC_SOURCES})

set(VAMPIRE_SMTCOMP_SOURCES
	SMTCOMP/SMTCOMPMode.cpp
    SAT/Z3MainLoop.cpp
    )
source_group(smt_comp_source_files FILES ${VAMPIRE_SMTCOMP_SOURCES})


# do we also need Test/CheckedSatSolver.o (as in the makefile)?
# do we also need Global.o and vampire.o (as in the makefile)?
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
	${VAMPIRE_TABULATION_SOURCES}
	${VAMPIRE_PROGRAM_SOURCES}
	${VAMPIRE_FINITEMODELBUILDING_SOURCES}
	${VAMPIRE_CASC_SOURCES}
	${VAMPIRE_SMTCOMP_SOURCES}
    ${VAMPIRE_MINISAT_SOURCES}
    version.cpp
    global.cpp
    vampire.cpp
	)
    #version.cpp # the automatically generated version file

# TODO: we want at least vampire_dbg, vampire_rel, vampire_z3_dbg, vampire_z3_rel
message(STATUS "a test message")

add_executable(vampire ${VAMPIRE_SOURCES})
target_link_libraries(vampire Z3)

################################################################
# automated generation of Vampire revision information from git
################################################################





