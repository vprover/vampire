#/*
# * This file is part of the source code of the software program
# * Vampire. It is protected by applicable
# * copyright laws.
# *
# * This source code is distributed under the licence found here
# * https://vprover.github.io/license.html
# * and in the source directory
# */



###############################################################
# File:    makefile 
# Author:  Andrei Voronkov
# Created: 07/04/2006
# Purpose: makefile for Vampire
################################################################

# The following flags are available for compilation:
#   VDEBUG           - the debug mode
#   VTEST            - testing procedures will also be compiled
#   CHECK_LEAKS      - test for memory leaks (debugging mode only)
#   UNIX_USE_SIGALRM - the SIGALRM timer will be used even in debug mode
#   VZ3              - compile with Z3

DBG_FLAGS = -g -DVDEBUG=1 -DCHECK_LEAKS=0 -DUNIX_USE_SIGALRM=1 # debugging for spider 
# DELETEMEin2017: the bug with gcc-6.2 and problems in ClauseQueue could be also fixed by adding -fno-tree-ch
REL_FLAGS = -O6 -DVDEBUG=0 # no debugging
GCOV_FLAGS = -O0 --coverage #-pedantic

MINISAT_DBG_FLAGS = -D DEBUG
MINISAT_REL_FLAGS = -D NDEBUG
MINISAT_FLAGS = $(MINISAT_DBG_FLAGS)

#XFLAGS = -g -DVDEBUG=1 -DVTEST=1 -DCHECK_LEAKS=1 # full debugging + testing
#XFLAGS = $(DBG_FLAGS)
# XFLAGS = -Wfatal-errors -g -DVDEBUG=1 -DCHECK_LEAKS=0 -DUSE_SYSTEM_ALLOCATION=1 # standard debugging only
# careful, AddressSanitizer for clang does not show line numbers by default: https://stackoverflow.com/questions/24566416/how-do-i-get-line-numbers-in-the-debug-output-with-clangs-fsanitize-address
XFLAGS = -Wfatal-errors -g -DVDEBUG=1 -DCHECK_LEAKS=0 -DUSE_SYSTEM_ALLOCATION=1 -fsanitize=address -fno-omit-frame-pointer  # standard debugging only
# TODO: try the sanitizer of undefined behaviour from time to time:
# XFLAGS = -Wfatal-errors -g -DVDEBUG=1 -DCHECK_LEAKS=0 -DUSE_SYSTEM_ALLOCATION=1 -fsanitize=undefined
#XFLAGS = -g -DVDEBUG=1 -DCHECK_LEAKS=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 # memory leaks
#XFLAGS = $(REL_FLAGS)

# TODO: consider trying -flto (see https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html)

#XFLAGS = -O6 -DVDEBUG=0 -march=native -mtune=native # no debugging 
#XFLAGS = -O6 -DVDEBUG=0 -msse3 # no debugging 
#XFLAGS = -O6 -DVDEBUG=0 -msse3 -g # no debugging 
#XFLAGS = -O6 -DVDEBUG=0 -march=core2 -msse4.1 -mtune=core2 # no debugging 
#XFLAGS = -O6 -DVDEBUG=0 -march=core2 -msse4.1 -mtune=core2 -g # no debugging 
#XFLAGS = -O6 -DUSE_SYSTEM_ALLOCATION=1 -DVDEBUG=0 -march=core2 -msse4.1 -mtune=core2 -g # no debugging 

#XFLAGS = -pg -g -O6 -DVDEBUG=0 # profiling with max optimization
#XFLAGS = -pg -g -O6 -DVDEBUG=0 -fno-inline # profiling with no inlining
#XFLAGS = -pg -g -DVDEBUG=0 # profiling
#XFLAGS = -pg -g -DVDEBUG=1 -DCHECK_LEAKS=0 # profiling & debugging
#XFLAGS = -fprofile-arcs -pg -O6 -DVDEBUG=0 # coverage & profiling optimized
#XFLAGS = -O0 -DVDEBUG=0 -g # no debugging, no optimization
#XFLAGS = -O6 -DVDEBUG=1 -DCHECK_LEAKS=0 -g # debugging and optimized

#XFLAGS = -O6 -DVDEBUG=0 -g # Cachegrind
#XFLAGS = -O6 -DVDEBUG=0 -DUNIX_USE_SIGALRM=0 -g # Cachegrind
#XFLAGS = -O2 -DVDEBUG=0 -fno-inline-functions -fno-inline-functions-called-once -fno-default-inline -fno-inline-small-functions -fno-early-inlining -g # Callgrind
#XFLAGS = -O6 -DVDEBUG=0 -fno-inline-functions -fno-inline-functions-called-once -fno-default-inline -fno-early-inlining -g # Callgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUNIX_USE_SIGALRM=0 -fno-inline-functions -fno-inline-functions-called-once -fno-default-inline -fno-early-inlining -g # Callgrind
#XFLAGS = -O2 -DVDEBUG=0 -fno-inline-functions -fno-inline-functions-called-once -fno-default-inline -fno-early-inlining -g # Callgrind
#XFLAGS = -O6 -DVDEBUG=0 -DUNIX_USE_SIGALRM=0 -fno-inline -g # Callgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -fno-inline -fno-default-inline -g # Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -fno-inline -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -g #Valgrind
#XFLAGS = -O6 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=1 -DCHECK_LEAKS=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -fno-inline -fno-default-inline -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DEFENCE=1 -fno-inline -g -lefence #Electric Fence
#XFLAGS = -O6 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DEFENCE=1 -g -lefence #Electric Fence
#XFLAGS = -O6 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -g

INCLUDES= -I.
Z3FLAG= -DVZ3=0
Z3LIB=
ifeq (,$(shell echo $(MAKECMDGOALS) | sed 's/.*z3.*//g')) 
INCLUDES= -I. -Iz3/src/api -Iz3/src/api/c++ 
ifeq (,$(shell echo $(MAKECMDGOALS) | sed 's/.*static.*//g'))
Z3LIB= -Lz3/build -lz3 -lgomp -pthread  -Wl,--whole-archive -lrt -lpthread -Wl,--no-whole-archive -ldl
else
Z3LIB= -Lz3/build -lz3
endif

Z3FLAG= -DVZ3=1
endif

ifneq (,$(filter vtest%,$(MAKECMDGOALS)))
XFLAGS = $(DBG_FLAGS) $(Z3FLAG)
endif
ifneq (,$(filter %_dbg,$(MAKECMDGOALS)))
XFLAGS = $(DBG_FLAGS) $(Z3FLAG)
endif
ifneq (,$(filter %_rel,$(MAKECMDGOALS)))
XFLAGS = $(REL_FLAGS) $(Z3FLAG)
MINISAT_FLAGS = $(MINISAT_REL_FLAGS)
endif

ifneq (,$(filter %_dbg_gcov,$(MAKECMDGOALS)))
XFLAGS = $(DBG_FLAGS) $(GCOV_FLAGS) $(Z3FLAG)
endif
ifneq (,$(filter %_rel_gcov,$(MAKECMDGOALS)))
XFLAGS = $(REL_FLAGS) $(GCOV_FLAGS) $(Z3FLAG)
MINISAT_FLAGS = $(MINISAT_REL_FLAGS)
endif

OS = $(shell uname)
ifeq ($(OS),Darwin)
STATIC = -static-libgcc -static-libstdc++ 
else
STATIC = -static
endif

ifneq (,$(filter %_dbg_static,$(MAKECMDGOALS)))
XFLAGS = $(STATIC) $(DBG_FLAGS) $(Z3FLAG)
endif
ifneq (,$(filter %_rel_static,$(MAKECMDGOALS)))
XFLAGS = $(STATIC) $(REL_FLAGS) $(Z3FLAG)
MINISAT_FLAGS = $(MINISAT_REL_FLAGS)
endif


################################################################
# Specific build options for some targets
#

ifneq (,$(filter libvapi,$(MAKECMDGOALS)))
XFLAGS = $(REL_FLAGS) -DVAPI_LIBRARY=1 -fPIC
endif
ifneq (,$(filter libvapi_dbg,$(MAKECMDGOALS)))
XFLAGS = $(DBG_FLAGS) -DVAPI_LIBRARY=1 -fPIC 
endif

################################################################

CXX = g++
CXXFLAGS = $(XFLAGS) -Wall -std=c++14  $(INCLUDES) # -Wno-unknown-warning-option for clang

CC = gcc 
CCFLAGS = -Wall -O3 -DNDBLSCR -DNLGLOG -DNDEBUG -DNCHKSOL -DNLGLPICOSAT 
################################################################
MINISAT_OBJ = Minisat/core/Solver.o\
  Minisat/simp/SimpSolver.o\
  Minisat/utils/Options.o\
  Minisat/utils/System.o\
  SAT/MinisatInterfacing.o\
  SAT/MinisatInterfacingNewSimp.o

API_OBJ = Api/FormulaBuilder.o\
	  Api/Helper.o\
	  Api/ResourceLimits.o\
	  Api/Tracing.o
#	  Api/Problem.o\	  

VD_OBJ = Debug/Assertion.o\
         Debug/RuntimeStatistics.o\
         Debug/Tracer.o

VL_OBJ= Lib/Allocator.o\
        Lib/DHMap.o\
        Lib/Environment.o\
        Lib/Event.o\
        Lib/Exception.o\
        Lib/Hash.o\
        Lib/Int.o\
        Lib/IntNameTable.o\
        Lib/IntUnionFind.o\
        Lib/MemoryLeak.o\
        Lib/MultiCounter.o\
        Lib/NameArray.o\
        Lib/Random.o\
        Lib/StringUtils.o\
        Lib/System.o\
        Lib/TimeCounter.o\
        Lib/Timer.o

VLS_OBJ= Lib/Sys/Multiprocessing.o\
         Lib/Sys/Semaphore.o\
         Lib/Sys/SyncPipe.o

VK_OBJ= Kernel/Clause.o\
        Kernel/ClauseQueue.o\
        Kernel/ColorHelper.o\
        Kernel/EqHelper.o\
        Kernel/FlatTerm.o\
        Kernel/Formula.o\
        Kernel/FormulaTransformer.o\
        Kernel/FormulaUnit.o\
        Kernel/FormulaVarIterator.o\
        Kernel/Grounder.o\
        Kernel/Inference.o\
        Kernel/InferenceStore.o\
        Kernel/KBO.o\
        Kernel/SKIKBO.o\
        Kernel/KBOForEPR.o\
        Kernel/LiteralSelector.o\
        Kernel/LookaheadLiteralSelector.o\
	Kernel/LPO.o\
        Kernel/MainLoop.o\
        Kernel/Matcher.o\
        Kernel/MaximalLiteralSelector.o\
        Kernel/SpassLiteralSelector.o\
        Kernel/ELiteralSelector.o\
        Kernel/MLMatcher.o\
        Kernel/MLMatcherSD.o\
        Kernel/MLVariant.o\
        Kernel/Ordering.o\
        Kernel/Ordering_Equality.o\
        Kernel/Problem.o\
        Kernel/Renaming.o\
        Kernel/RobSubstitution.o\
        Kernel/MismatchHandler.o\
        Kernel/Signature.o\
        Kernel/SortHelper.o\
        Kernel/ApplicativeHelper.o\
        Kernel/OperatorType.o\
        Kernel/SubformulaIterator.o\
        Kernel/Substitution.o\
        Kernel/Term.o\
	Kernel/PolynomialNormalizer.o\
	Kernel/Polynomial.o\
        Kernel/TermIterators.o\
        Kernel/TermTransformer.o\
        Kernel/Theory.o\
        Kernel/Signature.o\
        Kernel/Unit.o\
        Kernel/InterpretedLiteralEvaluator.o\
        Kernel/Rebalancing.o\
        Kernel/Rebalancing/Inverters.o\
        Kernel/NumTraits.o

VI_OBJ = Indexing/AcyclicityIndex.o\
         Indexing/ClauseCodeTree.o\
         Indexing/ClauseVariantIndex.o\
         Indexing/CodeTree.o\
         Indexing/CodeTreeInterfaces.o\
         Indexing/GroundingIndex.o\
         Indexing/Index.o\
         Indexing/IndexManager.o\
         Indexing/LiteralIndex.o\
         Indexing/LiteralMiniIndex.o\
         Indexing/LiteralSubstitutionTree.o\
         Indexing/ResultSubstitution.o\
         Indexing/SubstitutionTree.o\
         Indexing/SubstitutionTree_FastGen.o\
         Indexing/SubstitutionTree_FastInst.o\
         Indexing/SubstitutionTree_Nodes.o\
         Indexing/TermCodeTree.o\
         Indexing/TermIndex.o\
         Indexing/TermSharing.o\
         Indexing/TermSubstitutionTree.o\
         Indexing/TypeSubstitutionTree.o

VIG_OBJ = InstGen/IGAlgorithm.o\
          InstGen/ModelPrinter.o

VINF_OBJ=Inferences/BackwardDemodulation.o\
         Inferences/BackwardSubsumptionResolution.o\
         Inferences/BackwardSubsumptionDemodulation.o\
         Inferences/BinaryResolution.o\
         Inferences/Condensation.o\
         Inferences/DistinctEqualitySimplifier.o\
         Inferences/EqualityFactoring.o\
         Inferences/EqualityResolution.o\
         Inferences/ExtensionalityResolution.o\
         Inferences/ArgCong.o\
         Inferences/NegativeExt.o\
         Inferences/Narrow.o\
         Inferences/SubVarSup.o\
         Inferences/Factoring.o\
         Inferences/FastCondensation.o\
         Inferences/FOOLParamodulation.o\
         Inferences/Injectivity.o\
         Inferences/ForwardDemodulation.o\
         Inferences/CombinatorDemodISE.o\
         Inferences/CombinatorNormalisationISE.o\
         Inferences/ForwardLiteralRewriting.o\
         Inferences/ForwardSubsumptionAndResolution.o\
         Inferences/SubsumptionDemodulationHelper.o\
         Inferences/ForwardSubsumptionDemodulation.o\
         Inferences/GlobalSubsumption.o\
         Inferences/HyperSuperposition.o\
         Inferences/InnerRewriting.o\
         Inferences/EquationalTautologyRemoval.o\
         Inferences/InferenceEngine.o\
	 Inferences/Instantiation.o\
         Inferences/InterpretedEvaluation.o\
         Inferences/PushUnaryMinus.o\
         Inferences/Cancellation.o\
         Inferences/PolynomialEvaluation.o\
         Inferences/ArithmeticSubtermGeneralization.o\
         Inferences/SLQueryBackwardSubsumption.o\
         Inferences/Superposition.o\
         Inferences/TautologyDeletionISE.o\
         Inferences/TermAlgebraReasoning.o\
         Inferences/Induction.o\
         Inferences/InductionHelper.o\
         Inferences/URResolution.o\
         Inferences/CNFOnTheFly.o\
         Inferences/CasesSimp.o\
         Inferences/Cases.o\
         Inferences/BoolSimp.o\
         Inferences/PrimitiveInstantiation.o\
         Inferences/Choice.o\
         Inferences/ElimLeibniz.o\
         Inferences/BoolEqToDiseq.o\
         Inferences/GaussianVariableElimination.o\
         Inferences/InterpretedEvaluation.o\
         Inferences/TheoryInstAndSimp.o
#         Inferences/RenamingOnTheFly.o\

VSAT_OBJ=SAT/DIMACS.o\
         SAT/MinimizingSolver.o\
         SAT/SAT2FO.o\
         SAT/SATClause.o\
         SAT/SATInference.o\
         SAT/SATLiteral.o\
	 SAT/Z3Interfacing.o\
	 SAT/Z3MainLoop.o\
	 SAT/BufferedSolver.o\
	 SAT/FallbackSolverWrapper.o

VST_OBJ= Saturation/AWPassiveClauseContainer.o\
         Saturation/PredicateSplitPassiveClauseContainer.o\
         Saturation/ClauseContainer.o\
         Saturation/ConsequenceFinder.o\
         Saturation/Discount.o\
         Saturation/ExtensionalityClauseContainer.o\
	 Saturation/LabelFinder.o\
         Saturation/LRS.o\
         Saturation/Otter.o\
         Saturation/ProvingHelper.o\
         Saturation/SaturationAlgorithm.o\
         Saturation/Splitter.o\
         Saturation/SymElOutput.o\
         Saturation/ManCSPassiveClauseContainer.o\

VS_OBJ = Shell/AnswerExtractor.o\
         Shell/CommandLine.o\
         Shell/CNF.o\
         Shell/NewCNF.o\
         Shell/NameReuse.o\
         Shell/DistinctProcessor.o\
         Shell/DistinctGroupExpansion.o\
         Shell/EqResWithDeletion.o\
         Shell/EqualityProxy.o\
         Shell/EqualityProxyMono.o\
         Shell/Flattening.o\
         Shell/FunctionDefinition.o\
         Shell/GeneralSplitting.o\
         Shell/GoalGuessing.o\
         Shell/Grounding.o\
         Shell/InequalitySplitting.o\
         Shell/InterpolantMinimizer.o\
         Shell/InterpolantMinimizerNew.o\
         Shell/Interpolants.o\
         Shell/InterpolantsNew.o\
         Shell/InterpretedNormalizer.o\
         Shell/LambdaElimination.o\
         Shell/LaTeX.o\
         Shell/LispLexer.o\
         Shell/LispParser.o\
         Shell/Naming.o\
         Shell/NNF.o\
         Shell/Normalisation.o\
         Shell/Options.o\
         Shell/PredicateDefinition.o\
         Shell/Preprocess.o\
         Shell/Property.o\
         Shell/Rectify.o\
         Shell/Skolem.o\
         Shell/SimplifyFalseTrue.o\
         Shell/SineUtils.o\
         Shell/SMTFormula.o\
         Shell/FOOLElimination.o\
         Shell/Statistics.o\
         Shell/SubexpressionIterator.o\
         Shell/SymbolDefinitionInlining.o\
         Shell/SymbolOccurrenceReplacement.o\
         Shell/SymCounter.o\
         Shell/TermAlgebra.o\
         Shell/TheoryAxioms.o\
         Shell/TheoryFinder.o\
         Shell/TheoryFlattening.o\
         Shell/BlockedClauseElimination.o\
         Shell/Token.o\
         Shell/TPTPPrinter.o\
         Shell/UIHelper.o\
         Shell/VarManager.o\
         Shell/Lexer.o\
         Shell/Preprocess.o\
         Shell/UnificationWithAbstractionConfig.o\
         version.o

PARSE_OBJ = Parse/SMTLIB2.o\
            Parse/TPTP.o\



DP_OBJ = DP/ShortConflictMetaDP.o\
         DP/SimpleCongruenceClosure.o

CASC_OBJ = CASC/PortfolioMode.o\
           CASC/Schedules.o\
	   CASC/ScheduleExecutor.o\
           CASC/CLTBMode.o\
           CASC/CLTBModeLearning.o

VFMB_OBJ = FMB/ClauseFlattening.o\
           FMB/SortInference.o\
	   FMB/Monotonicity.o\
	   FMB/FunctionRelationshipInference.o\
	   FMB/FiniteModel.o\
	   FMB/FiniteModelMultiSorted.o\
           FMB/FiniteModelBuilder.o

# testing procedures
VT_OBJ = Test/UnitTesting.o

VUT_OBJ = $(patsubst %.cpp,%.o,$(wildcard UnitTests/*.cpp))

LIB_DEP = Indexing/TermSharing.o\
	  Inferences/DistinctEqualitySimplifier.o\
	  Inferences/InferenceEngine.o\
	  Kernel/Clause.o\
	  Kernel/Formula.o\
	  Kernel/FormulaUnit.o\
	  Kernel/FormulaVarIterator.o\
	  Kernel/InterpretedLiteralEvaluator.o\
	  Kernel/PolynomialNormalizer.o\
	  Kernel/Rebalancing.o\
	  Kernel/Rebalancing/Inverters.o\
	  Kernel/NumTraits.o\
	  Kernel/Inference.o\
	  Kernel/InferenceStore.o\
	  Kernel/Problem.o\
	  Kernel/SortHelper.o\
      Kernel/ApplicativeHelper.o\
      Kernel/OperatorType.o\
	  Kernel/Signature.o\
	  Kernel/SubformulaIterator.o\
	  Kernel/Substitution.o\
	  Kernel/Term.o\
	  Kernel/TermIterators.o\
	  Kernel/TermTransformer.o\
    Kernel/Theory.o\
	  Kernel/Unit.o\
	  Parse/TPTP.o\
	  Saturation/ClauseContainer.o\
	  Shell/FunctionDefinition.o\
	  Shell/Options.o\
	  Shell/Property.o\
	  Shell/Statistics.o\
          Shell/UnificationWithAbstractionConfig.o\
	  version.o
	  # ClausifierDependencyFix.o\
	  version.o\
    Kernel/InterpretedLiteralEvaluator.o\
    Kernel/Rebalancing.o\
    Kernel/Rebalancing/Inverters.o\
    Kernel/NumTraits.o

OTHER_CL_DEP = Indexing/LiteralSubstitutionTree.o\
	       Indexing/ResultSubstitution.o\
	       Indexing/SubstitutionTree_FastGen.o\
	       Indexing/SubstitutionTree_FastInst.o\
	       Indexing/SubstitutionTree_Nodes.o\
	       Indexing/SubstitutionTree.o\
	       Inferences/InferenceEngine.o\
	       Inferences/TautologyDeletionISE.o\
	       Kernel/EqHelper.o\
	       Kernel/FormulaTransformer.o\
	       Kernel/Grounder.o\
	       Kernel/InferenceStore.o\
	       Kernel/Matcher.o\
	       Kernel/KBO.o\
         Kernel/SKIKBO.o\
	       Kernel/KBOForEPR.o\
	       Kernel/Ordering.o\
	       Kernel/Ordering_Equality.o\
	       Kernel/Problem.o\
	       Kernel/Renaming.o\
	       Kernel/RobSubstitution.o\
	       SAT/SATClause.o\
	       SAT/SATInference.o\
	       SAT/SATLiteral.o\

VAMP_DIRS := Api Debug DP Lib Lib/Sys Kernel FMB Indexing Inferences InstGen Shell CASC SAT Saturation Test UnitTests VUtils Parse Minisat Minisat/core Minisat/mtl Minisat/simp Minisat/utils Kernel/Rebalancing

VAMP_BASIC := $(MINISAT_OBJ) $(VD_OBJ) $(VL_OBJ) $(VLS_OBJ) $(VK_OBJ) $(BP_VD_OBJ) $(BP_VL_OBJ) $(BP_VLS_OBJ) $(BP_VSOL_OBJ) $(BP_VT_OBJ) $(BP_MPS_OBJ) $(ALG_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VIG_OBJ) $(VSAT_OBJ) $(DP_OBJ) $(VST_OBJ) $(VS_OBJ) $(PARSE_OBJ) $(VFMB_OBJ)
VSAT_BASIC := $(VD_OBJ) $(VL_OBJ) $(VLS_OBJ) $(VSAT_OBJ) $(LIB_DEP)

VAMPIRE_DEP := $(VAMP_BASIC) $(CASC_OBJ) $(TKV_BASIC) vampire.o
VSAT_DEP = $(VSAT_BASIC)
VTEST_DEP = $(VAMP_BASIC) $(VT_OBJ) $(VUT_OBJ) $(DP_OBJ) vtest.o
LIBVAPI_DEP = $(VD_OBJ) $(API_OBJ)
VAPI_DEP =  $(LIBVAPI_DEP) test_vapi.o

all: #default make disabled
	@echo "The make(1)-based build is no longer supported: use the CMake build instead."
	@echo "If you know what you're doing and want to use it, read the Makefile."

#the $(CONF_ID) directory is considered intermediate and make would otherwise try to delete it
#(this forbids deletion of intermediate files)
.SECONDARY:

################################################################
# automated generation of Vampire revision information

VERSION_NUMBER = 4.6.1

# We extract the revision number from svn every time the svn meta-data are modified
# (that's why there is the dependency on .svn/entries) 

#.svn/entries:

#version.cpp: .svn/entries Makefile
#	echo "//Automatically generated file, see Makefile for details" > $@
#	svn info | (grep Revision || echo "Revision: unknown") | sed 's|Revision: \(.*\)|const char* VERSION_STRING = "Vampire $(VERSION_NUMBER) (revision \1)";|' >> $@

# Since we switched to Git we extract the commit hash.
# The dependency on .git/HEAD tracks switching between branches,
# the dependency on .git/index tracks new commits.

.git/HEAD:
.git/index:

version.cpp: .git/HEAD .git/index Makefile
	@echo "//Automatically generated file, see Makefile for details" > $@
	@echo "const char* VERSION_STRING = \"Vampire $(VERSION_NUMBER) (commit $(shell git log -1 --format=%h\ on\ %ci || echo unknown))\";" >> $@

################################################################
# separate directory for object files implementation

# different directory for each configuration, so there is no need for "make clean"
SED_CMD='s/.*[(].*/detached/' # if branch name contains an opening bracket, replace it with detached (in order to avoid a crash during linking). This covers at least the case '(HEAD' occuring if one is in detached state, and '(no' occuring if one currently performs a rebase.
BRANCH=$(shell git branch | grep "\*" | cut -d ' ' -f 2 | sed -e $(SED_CMD)  )
COM_CNT=$(shell git rev-list HEAD --count)
CONF_ID := obj/$(shell echo -n "$(BRANCH) $(XFLAGS)"|sum|cut -d ' ' -f1)X

obj:
	-mkdir obj
obj/%X: | obj
	-mkdir $@
	-cd $@ ; mkdir $(VAMP_DIRS); cd .. 

#cancel the implicit rule
%.o : %.cpp

$(CONF_ID)/%.o : %.cpp | $(CONF_ID)
	mkdir -p `dirname $@`
	$(CXX) $(CXXFLAGS) -c -o $@ $*.cpp -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -MMD -MF $(CONF_ID)/$*.d

%.o : %.c 
$(CONF_ID)/%.o : %.c | $(CONF_ID)
	$(CC) $(CCFLAGS) -c -o $@ $*.c -MMD -MF $(CONF_ID)/$*.d

%.o : %.cc
$(CONF_ID)/%.o : %.cc | $(CONF_ID)
	$(CXX) $(CXXFLAGS) -c -o $@ $*.cc $(MINISAT_FLAGS) -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -MMD -MF $(CONF_ID)/$*.d

################################################################
# targets for executables

VAMPIRE_OBJ := $(addprefix $(CONF_ID)/, $(VAMPIRE_DEP))
VTEST_OBJ := $(addprefix $(CONF_ID)/, $(VTEST_DEP))
VUTIL_OBJ := $(addprefix $(CONF_ID)/, $(VUTIL_DEP))
VSAT_OBJ := $(addprefix $(CONF_ID)/, $(VSAT_DEP))
VAPI_OBJ := $(addprefix $(CONF_ID)/, $(VAPI_DEP))
LIBVAPI_OBJ := $(addprefix $(CONF_ID)/, $(LIBVAPI_DEP))
TKV_OBJ := $(addprefix $(CONF_ID)/, $(TKV_DEP))

define COMPILE_CMD
$(CXX) $(CXXFLAGS) $(filter -l%, $+) $(filter %.o, $^) -o $@_$(BRANCH)_$(COM_CNT) $(Z3LIB)
@#$(CXX) -static $(CXXFLAGS) $(Z3LIB) $(filter %.o, $^) -o $@
@#strip $@
endef

define COMPILE_CMD_SIMPLE
$(CXX) $(CXXFLAGS) $(filter -l%, $+) $(filter %.o, $^) -o $@
endef

define COMPILE_CMD_TKV
$(CXX) $(CXXFLAGS) $(filter -l%, $+) $(filter %.o, $^) -o $@
@#$(CXX) -static $(CXXFLAGS) $(filter %.o, $^) -o $@
@#strip $@
endef

################################################################
# definitions of targets

.LIBPATTERNS =

-lmemcached:

EXEC_DEF_PREREQ = Makefile

vampire_dbg vampire_rel vampire_dbg_static vampire_dbg_gcov vampire_rel_static vampire_rel_gcov vampire_z3_dbg vampire_z3_rel vampire_z3_dbg_static vampire_z3_dbg_gcov vampire_z3_rel_static vampire_z3_rel_gcov: $(VAMPIRE_OBJ) $(EXEC_DEF_PREREQ)
	$(COMPILE_CMD)

vampire: $(VAMPIRE_OBJ) $(EXEC_DEF_PREREQ)
	$(COMPILE_CMD_SIMPLE)

vtest vtest_z3: $(VTEST_OBJ) $(EXEC_DEF_PREREQ)
	$(COMPILE_CMD)

vapi vapi_dbg vapi_rel: $(VAPI_OBJ) $(EXEC_DEF_PREREQ)
	$(COMPILE_CMD)

libvapi libvapi_dbg: $(LIBVAPI_OBJ) $(EXEC_DEF_PREREQ)
	$(CXX) $(CXXFLAGS) -shared -Wl,-soname,libvapi.so -o libvapi.so $(filter %.o, $^) -lc

test_libvapi: $(CONF_ID)/test_libvapi.o $(EXEC_DEF_PREREQ)
	$(CXX) $(CXXFLAGS) $(filter %.o, $^) -o $@ -lvapi -L. -Wl,-R,\$$ORIGIN

compile_commands:
	mkdir compile_commands

compile_commands/%.o: compile_commands
	mkdir -p $(dir $@)
	echo $(CXX) $(CXXFLAGS) -c $*.cpp -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -MMD -MF $(CONF_ID)/$*.d > $@

compile_commands.json: $(foreach x, $(VAMPIRE_DEP), compile_commands/$x)
	echo '[' > $@
	for f in $(VAMPIRE_DEP);\
	do\
	  echo '  {';\
	  echo '    "directory": "$(PWD)",';\
	  echo '    "command"  : "'$$(cat compile_commands/$$f)'",';\
	  echo '    "file"     : "'$$f'"';\
	  echo '  },';\
	done | sed '$$d' >> $@
	echo '  }'>> $@
	echo ']' >> $@

api_src:
	rm -rf $@
	mkdir $@
	mkdir $(patsubst %, $@/%, $(VAMP_DIRS))
	tar cf - $(sort $(patsubst %.o,%.cpp, $(VAPI_DEP) test_libvapi.o)) | (cd $@ ; tar xvf -) 2>/dev/null
	cp Makefile Makefile_depend test_vapi.cpp $@
	tar cf - $(sort $(shell $(CXX) -I. -MM -DVDEBUG=1 -DVTEST=1 -DCHECK_LEAKS=1 $(sort $(patsubst %.o,%.cpp, $(VAPI_DEP))) |tr '\n' ' '|tr -d ':\\'|sed -E 's/(^| )[^ ]+\.(o|cpp)//g' )) | (cd $@ ; tar xvf -) 2>/dev/null
	rm -f $@.tgz
	tar -czf $@.tgz $@

clean:
	rm -rf obj version.cpp

doc:
	rm -fr doc/html
	doxygen config.doc

.PHONY: doc clean api_src

###########################
# include header dependencies

include $(shell find obj -name *.d)
