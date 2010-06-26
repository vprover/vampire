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
#	

DBG_FLAGS = -g -DVDEBUG=1 -DCHECK_LEAKS=0 -DUNIX_USE_SIGALRM=1 # debugging for spider 
REL_FLAGS = -O6 -DVDEBUG=0 # no debugging 

#XFLAGS = -g -DVDEBUG=1 -DVTEST=1 -DCHECK_LEAKS=1 # full debugging + testing
#XFLAGS = $(DBG_FLAGS)
XFLAGS = -g -DVDEBUG=1 -DCHECK_LEAKS=0 # standard debugging only
#XFLAGS = $(REL_FLAGS)

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
#XFLAGS = -O6 -DVDEBUG=0 -DUNIX_USE_SIGALRM=0 -fno-inline -g # Callgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -fno-inline -fno-default-inline -g # Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -fno-inline -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -g #Valgrind
#XFLAGS = -O6 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=1 -DCHECK_LEAKS=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -fno-inline -fno-default-inline -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DEFENCE=1 -fno-inline -g -lefence #Electric Fence
#XFLAGS = -O6 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DEFENCE=1 -g -lefence #Electric Fence
#XFLAGS = -O6 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -g

ifneq (,$(filter %_dbg,$(MAKECMDGOALS)))
XFLAGS = $(DBG_FLAGS)
endif
ifneq (,$(filter %_rel,$(MAKECMDGOALS)))
XFLAGS = $(REL_FLAGS)
endif

CXX = g++
CXXFLAGS = $(XFLAGS) -Wall -I.

################################################################

VD_OBJ = Debug/Assertion.o\
         Debug/Log.o\
         Debug/RuntimeStatistics.o\
         Debug/Tracer.o

VL_OBJ= Lib/Allocator.o\
        Lib/DHMap.o\
        Lib/Environment.o\
        Lib/Event.o\
        Lib/Exception.o\
        Lib/Graph.o\
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

VK_OBJ= Kernel/BDD.o\
        Kernel/BDDClausifier.o\
        Kernel/BDDConjunction.o\
        Kernel/Clause.o\
        Kernel/ClauseQueue.o\
        Kernel/EqHelper.o\
        Kernel/FlatTerm.o\
        Kernel/Formula.o\
        Kernel/FormulaUnit.o\
        Kernel/FormulaVarIterator.o\
        Kernel/Inference.o\
        Kernel/InferenceStore.o\
        Kernel/KBO.o\
        Kernel/KBOForEPR.o\
        Kernel/LiteralSelector.o\
        Kernel/LookaheadLiteralSelector.o\
        Kernel/MatchTag.o\
        Kernel/Matcher.o\
        Kernel/MaximalLiteralSelector.o\
        Kernel/MLMatcher.o\
        Kernel/MLVariant.o\
        Kernel/Ordering.o\
        Kernel/Ordering_Equality.o\
        Kernel/Renaming.o\
        Kernel/RobSubstitution.o\
        Kernel/Signature.o\
        Kernel/SubformulaIterator.o\
        Kernel/Substitution.o\
        Kernel/Term.o\
        Kernel/TermIterators.o\
        Kernel/Theory.o\
        Kernel/Unit.o\
#        Kernel/EGSubstitution.o

ALG_OBJ = Kernel/Algebra/ArithmeticKB.o\
          Kernel/Algebra/Constraint.o\
          Kernel/Algebra/Polynomial.o

VI_OBJ = Indexing/ArithmeticIndex.o\
         Indexing/ClauseCodeTree.o\
         Indexing/ClauseSharing.o\
         Indexing/ClauseVariantIndex.o\
         Indexing/CodeTree.o\
         Indexing/CodeTreeInterfaces.o\
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
         Indexing/TermSubstitutionTree.o

VINF_OBJ=Inferences/BackwardDemodulation.o\
         Inferences/BackwardSubsumptionResolution.o\
         Inferences/BDDMarkingSubsumption.o\
         Inferences/BinaryResolution.o\
         Inferences/Condensation.o\
         Inferences/CTFwSubsAndRes.o\
         Inferences/EqualityFactoring.o\
         Inferences/EqualityResolution.o\
         Inferences/Factoring.o\
         Inferences/FastCondensation.o\
         Inferences/ForwardDemodulation.o\
         Inferences/ForwardLiteralRewriting.o\
         Inferences/ForwardSubsumptionAndResolution.o\
         Inferences/InferenceEngine.o\
         Inferences/InterpretedEvaluation.o\
         Inferences/InterpretedSimplifier.o\
         Inferences/PropositionalToBDDISE.o\
         Inferences/RefutationSeekerFSE.o\
         Inferences/SLQueryBackwardSubsumption.o\
         Inferences/SLQueryForwardSubsumption.o\
         Inferences/Superposition.o\
         Inferences/TautologyDeletionISE.o

VSAT_OBJ=SAT/DIMACS.o\
         SAT/Preprocess.o\
         SAT/SATClause.o\
         SAT/SATLiteral.o\
         SAT/TWLSolver.o\
#         SAT/SATClauseSharing.o\
#         SAT/SingleWatchSAT.o

VST_OBJ= Saturation/AWPassiveClauseContainer.o\
         Saturation/BSplitter.o\
         Saturation/ClauseContainer.o\
         Saturation/ConsequenceFinder.o\
         Saturation/Discount.o\
         Saturation/Limits.o\
         Saturation/LRS.o\
         Saturation/Otter.o\
         Saturation/SaturationAlgorithm_Construction.o\
         Saturation/SaturationAlgorithm.o\
         Saturation/SaturationResult.o\
         Saturation/Splitter.o\
         Saturation/SWBSplitter.o\
         Saturation/SWBSplitterWithBDDs.o\
         Saturation/SWBSplitterWithoutBDDs.o\
         Saturation/SymElOutput.o

VS_OBJ = Shell/AxiomGenerator.o\
         Shell/CommandLine.o\
         Shell/CNF.o\
         Shell/EqResWithDeletion.o\
         Shell/EqualityProxy.o\
         Shell/Flattening.o\
         Shell/FunctionDefinition.o\
         Shell/GeneralSplitting.o\
         Shell/Grounding.o\
         Shell/InequalitySplitting.o\
         Shell/Interpolants.o\
         Shell/LaTeX.o\
         Shell/Lexer.o\
         Shell/LispLexer.o\
         Shell/LispParser.o\
         Shell/Naming.o\
         Shell/NNF.o\
         Shell/Normalisation.o\
         Shell/Options.o\
         Shell/Parser.o\
         Shell/PredicateDefinition.o\
         Shell/Preprocess.o\
         Shell/Property.o\
         Shell/Rectify.o\
         Shell/Refutation.o\
         Shell/Skolem.o\
         Shell/SimplifyFalseTrue.o\
         Shell/SimplifyProver.o\
         Shell/SineUtils.o\
         Shell/SMTLexer.o\
         Shell/SMTParser.o\
         Shell/Statistics.o\
         Shell/SymCounter.o\
         Shell/TheoryAxioms.o\
         Shell/TheoryFinder.o\
         Shell/Token.o\
         Shell/TPTPLexer.o\
         Shell/TPTP.o\
         Shell/TPTPParser.o\
         Shell/UIHelper.o

VRULE_OBJ = Rule/Index.o\
            Rule/CASC.o\
            Rule/Prolog.o\
            Rule/ProofAttempt.o

LTB_OBJ = Shell/LTB/Builder.o\
          Shell/LTB/Selector.o\
          Shell/LTB/Storage.o

CASC_OBJ = Shell/CASC/CASCMode.o\
           Shell/CASC/CLTBMode.o\
           Shell/CASC/ForkingCM.o\
           Shell/CASC/SpawningCM.o

# testing procedures
VT_OBJ = Test/CheckedFwSimplifier.o\
         Test/CompitOutput.o\
         Test/Compit2Output.o\
         Test/Output.o\
         Test/UnitTesting.o

VUT_OBJ = UnitTests/tBinaryHeap.o\
		  UnitTests/tDHMap.o\
		  UnitTests/tDHMultiset.o\
		  UnitTests/tfork.o\
		  UnitTests/tSkipList.o\
		  UnitTests/tTwoVampires.o

LIB_DEP = Indexing/TermSharing.o\
		  Kernel/BDD.o\
		  Kernel/BDDClausifier.o\
		  Kernel/Clause.o\
		  Kernel/Formula.o\
		  Kernel/FormulaUnit.o\
		  Kernel/FormulaVarIterator.o\
		  Kernel/Inference.o\
		  Kernel/KBO.o\
		  Kernel/Ordering.o\
		  Kernel/Ordering_Equality.o\
		  Kernel/Signature.o\
		  Kernel/SubformulaIterator.o\
		  Kernel/Substitution.o\
		  Kernel/Term.o\
		  Kernel/TermIterators.o\
		  Kernel/Theory.o\
		  Kernel/Unit.o\
		  Saturation/ClauseContainer.o\
		  Shell/EqualityProxy.o\
		  Shell/Options.o\
		  Shell/Statistics.o
			  

VAMP_BASIC := $(VD_OBJ) $(VL_OBJ) $(VLS_OBJ) $(VK_OBJ) $(ALG_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VSAT_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ)  
VSAT_BASIC := $(VD_OBJ) $(VL_OBJ) $(VLS_OBJ) $(VSAT_OBJ) $(VT_OBJ) $(LIB_DEP)
#VGROUND_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VSAT_OBJ) $(VS_OBJ) $(VT_OBJ)  

VAMPIRE_DEP := $(VAMP_BASIC) $(CASC_OBJ) Global.o vampire.o
VCOMPIT_DEP = $(VAMP_BASIC) Global.o vcompit.o
VLTB_DEP = $(VAMP_BASIC) $(LTB_OBJ) Global.o vltb.o
VSAT_DEP = $(VSAT_BASIC) Global.o vsat.o
VTEST_DEP = $(VAMP_BASIC) $(VUT_OBJ) Global.o vtest.o
#UCOMPIT_OBJ = $(VCOMPIT_BASIC) Global.o compit2.o compit2_impl.o
#VGROUND_OBJ = $(VGROUND_BASIC) Global.o vground.o
#SAT_OBJ = $(VD_OBJ) $(SAT) sat.o
#TEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ) Global.o test_SubstitutionTree.o
#RTEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ) Global.o test_retrieval.o
#DHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_DHMap.o
#DHMSTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_DHMultiset.o
#BHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_BinaryHeap.o
#SLTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_SkipList.o
#ALLOCTEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VT_OBJ) $(VSAT_OBJ) $(VS_OBJ) Global.o test_alloc.o
#ALUCARD_OBJ = $(ALUC_BASIC) Global.o alucard.o

all:#default make disabled

#the $(CONF_ID) directory is considered intermediate and make would otherwise try to delete it
#(this forbids deletion of intermediate files)
.SECONDARY:

################################################################
# separate directory for object files implementation

# different directory for each configuration, so there is no need for "make clean"
CONF_ID := obj/$(shell echo -n "$(XFLAGS)"|sum|cut -d' ' -f1)X

obj:
	-mkdir obj
obj/%X: | obj
	-mkdir $@
	-cd $@ ; mkdir Debug Lib Lib/Sys Kernel Kernel/Algebra Indexing Inferences Shell Shell/CASC Shell/LTB Rule SAT Saturation Test UnitTests; cd .. 

#cancel the implicit rule
%.o : %.cpp

$(CONF_ID)/%.o : %.cpp | $(CONF_ID)
	$(CXX) $(CXXFLAGS) -c -o $@ $*.cpp

################################################################
# targets for executables

VAMPIRE_OBJ := $(addprefix $(CONF_ID)/, $(VAMPIRE_DEP))
VCOMPIT_OBJ := $(addprefix $(CONF_ID)/, $(VCOMPIT_DEP))
VLTB_OBJ := $(addprefix $(CONF_ID)/, $(VLTB_DEP))
VTEST_OBJ := $(addprefix $(CONF_ID)/, $(VTEST_DEP))
VSAT_OBJ := $(addprefix $(CONF_ID)/, $(VSAT_DEP))

define COMPILE_CMD
$(CXX) $(CXXFLAGS) $(filter -l%, $+) $(filter %.o, $^) -o $@
@#$(CXX) -static $(CXXFLAGS) $(filter %.o, $^) -o $@
@#strip $@
endef

.LIBPATTERNS =

-lmemcached:

EXEC_DEF_PREREQ = Makefile

vampire vampire_rel vampire_dbg: $(VAMPIRE_OBJ) $(EXEC_DEF_PREREQ)
	$(COMPILE_CMD)

vcompit: $(VCOMPIT_OBJ) $(EXEC_DEF_PREREQ)
	$(COMPILE_CMD)

vltb vltb_rel vltb_dbg: -lmemcached $(VLTB_OBJ) $(EXEC_DEF_PREREQ)
	$(COMPILE_CMD)

vtest vtest_rel vtest_dbg: $(VTEST_OBJ) $(EXEC_DEF_PREREQ)
	$(COMPILE_CMD)

vsat vsat_rel vsat_dbg: $(VSAT_OBJ) $(EXEC_DEF_PREREQ)
	$(COMPILE_CMD)

#vground: $(VGROUND_OBJ) $(EXEC_DEF_PREREQ)
##	$(CXX) -static $(CXXFLAGS) $^ -o vground
#	$(CXX) $(CXXFLAGS) $^ -o $@
#
#ucompit: $(UCOMPIT_OBJ) $(EXEC_DEF_PREREQ)
#	$(CXX) $(CXXFLAGS) $^ -o $@
#
#sat: $(SAT_OBJ) $(EXEC_DEF_PREREQ)
#	$(CXX) $(CXXFLAGS) $^ -o $@
##	strip sat
#
#test: $(TEST_OBJ) $(EXEC_DEF_PREREQ)
#	$(CXX) $(CXXFLAGS) $^ -o $@
#
#rtest: $(RTEST_OBJ) $(EXEC_DEF_PREREQ)
#	$(CXX) $(CXXFLAGS) $^ -o $@
#
#test_alloc: $(ALLOCTEST_OBJ) $(EXEC_DEF_PREREQ)
#	$(CXX) $(CXXFLAGS) $^ -o $@
#
#
#test_DHMap: $(DHTEST_OBJ) $(EXEC_DEF_PREREQ)
#	$(CXX) $(CXXFLAGS) $^ -o $@
#
#test_DHMultiset: $(DHMSTEST_OBJ) $(EXEC_DEF_PREREQ)
#	$(CXX) $(CXXFLAGS) $^ -o $@
#
#test_BinaryHeap: $(BHTEST_OBJ) $(EXEC_DEF_PREREQ)
#	$(CXX) $(CXXFLAGS) $^ -o $@
#
#test_SkipList: $(SLTEST_OBJ) $(EXEC_DEF_PREREQ)
#	$(CXX) $(CXXFLAGS) $^ -o $@

clean:
	cd Debug ; rm -f *.o *~ *.bak ; cd ..
	cd Lib ; rm -f *.o *~ *.bak ; cd ..
	cd Kernel ; rm -f *.o *~ *.bak ; cd ..
	cd Indexing ; rm -f *.o *~ *.bak ; cd ..
	cd Inferences ; rm -f *.o *~ *.bak ; cd ..
	cd Shell ; rm -f *.o *~ *.bak ; cd ..
	cd Rule ; rm -f *.o *~ *.bak ; cd ..
	cd SAT ; rm -f *.o *~ *.bak ; cd ..
	cd Saturation ; rm -f *.o *~ *.bak ; cd ..
	cd Test ; rm -f *.o *~ *.bak ; cd ..
	rm -f *.o *~ *.bak
	rm -rf obj

depend:
	makedepend -p'$$(CONF_ID)/' -fMakefile_depend -Y -DVDEBUG=1 -DVTEST=1 -DCHECK_LEAKS=1 Debug/*.cpp Lib/*.cpp Lib/Sys/*.cpp Shell/*.cpp Shell/LTB/*.cpp  Shell/CASC/*.cpp Kernel/*.cpp Kernel/Algebra/*.cpp Indexing/*.cpp Inferences/*.cpp Rule/*.cpp SAT/*.cpp Saturation/*.cpp Test/*.cpp UnitTests/*.cpp *.cpp

doc:
	rm -fr doc/html
	doxygen config.doc

.PHONY: doc depend clean


###########################
# include header dependencies
	
include Makefile_depend
