###############################################################
# File:    makefile 
# Author:  Andrei Voronkov
# Created: 07/04/2006
# Purpose: makefile for Vampire
################################################################

# The following flags are available for compilation:
#   VDEBUG      - the debug mode
#   VTEST       - testing procedures will also be compiled
#   CHECK_LEAKS - test for memory leaks (debugging mode only)
#	

#XFLAGS = -g -DVDEBUG=1 -DVTEST=1 -DCHECK_LEAKS=1 # full debugging + testing
#XFLAGS = -g -DVDEBUG=0 -DCHECK_LEAKS=0 # debug mode without VDEBUG macro 
#XFLAGS = -g -O6 -DVDEBUG=0 # no debugging, but debugging info present
#XFLAGS = -pg -g -O6 -DVDEBUG=0 # profiling with max optimization
#XFLAGS = -pg -g -O6 -DVDEBUG=0 -fno-inline # profiling with no inlining
#XFLAGS = -fprofile-arcs -pg -g -DVDEBUG=0 # coverage & profiling
#XFLAGS = -pg -g -DVDEBUG=0 # profiling
#XFLAGS = -pg -DVDEBUG=0 # profiling without debug info
#XFLAGS = -g -DVDEBUG=1 -DCHECK_LEAKS=0 # standard debugging only
XFLAGS = -O6 -DVDEBUG=0 # no debugging

#XFLAGS = -O6 -DVDEBUG=0 -mtune=athlon64 -march=athlon64 # no debugging, cpu optimization
#XFLAGS = -pg -g -DVDEBUG=1 -DCHECK_LEAKS=0 # profiling & debugging
#XFLAGS = -fprofile-arcs -pg -O6 -DVDEBUG=0 # coverage & profiling optimized
#XFLAGS = -DVDEBUG=0 # no debugging, no optimization
#XFLAGS = -O6 -DVDEBUG=1 -DCHECK_LEAKS=0 -g # debugging and optimized
#XFLAGS = -O6 -DVDEBUG=0 -g # Cachegrind
#XFLAGS = -O2 -DVDEBUG=0 -fno-inline-functions -fno-inline-functions-called-once -fno-default-inline -fno-inline-small-functions -fno-early-inlining -g # Callgrind
#XFLAGS = -O6 -DVDEBUG=0 -fno-inline-functions -fno-inline-functions-called-once -fno-default-inline -fno-early-inlining -g # Callgrind
#XFLAGS = -O0 -DVDEBUG=0 -fno-inline-functions -fno-inline-functions-called-once -fno-default-inline -fno-early-inlining -g # Callgrind
#XFLAGS = -O6 -DVDEBUG=0 -fno-inline -g # Callgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -fno-inline -fno-default-inline -g # Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -fno-inline -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -g #Valgrind
#XFLAGS = -O6 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=1 -DCHECK_LEAKS=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -fno-inline -fno-default-inline -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DEFENCE=1 -fno-inline -g -lefence #Electric Fence
#XFLAGS = -O6 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DEFENCE=1 -g -lefence #Electric Fence
#XFLAGS = -O6 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -g

CXX = g++
CXXFLAGS = $(XFLAGS) -Wall

# Valgrind
#VCXX = /usr/bin/g++-4.2
#VCXXFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -fno-inline -g -Wall

################################################################

VD_OBJ = Debug/Assertion.o\
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
        Lib/System.o\
        Lib/TimeCounter.o\
        Lib/Timer.o

VK_OBJ= Kernel/BDD.o\
        Kernel/Clause.o\
        Kernel/ClauseQueue.o\
        Kernel/EGSubstitution.o\
        Kernel/EqHelper.o\
        Kernel/Formula.o\
        Kernel/FormulaUnit.o\
        Kernel/FormulaVarIterator.o\
        Kernel/Inference.o\
        Kernel/InferenceStore.o\
        Kernel/KBO.o\
        Kernel/LiteralSelector.o\
        Kernel/MatchTag.o\
        Kernel/MaximalLiteralSelector.o\
        Kernel/MLMatcher.o\
        Kernel/MLVariant.o\
        Kernel/Ordering.o\
        Kernel/Renaming.o\
        Kernel/RobSubstitution.o\
        Kernel/Signature.o\
        Kernel/SubformulaIterator.o\
        Kernel/Substitution.o\
        Kernel/Term.o\
        Kernel/TermFunIterator.o\
        Kernel/TermVarIterator.o\
        Kernel/Unit.o

VI_OBJ = Indexing/ClauseVariantIndex.o\
         Indexing/Index.o\
         Indexing/IndexManager.o\
         Indexing/LiteralIndex.o\
         Indexing/LiteralMiniIndex.o\
         Indexing/LiteralSubstitutionTree.o\
         Indexing/ResultSubstitution.o\
         Indexing/SubstitutionTree.o\
         Indexing/SubstitutionTree_Nodes.o\
         Indexing/TermIndex.o\
         Indexing/TermSharing.o\
         Indexing/TermSubstitutionTree.o

VINF_OBJ=Inferences/BackwardDemodulation.o\
         Inferences/BinaryResolution.o\
         Inferences/Condensation.o\
         Inferences/EqualityFactoring.o\
         Inferences/EqualityResolution.o\
         Inferences/Factoring.o\
         Inferences/ForwardDemodulation.o\
         Inferences/ForwardLiteralRewriting.o\
         Inferences/ForwardSubsumptionAndResolution.o\
         Inferences/InferenceEngine.o\
         Inferences/InterpretedEvaluation.o\
         Inferences/PropositionalToBDDISE.o\
         Inferences/RefutationSeekerFSE.o\
         Inferences/SLQueryBackwardSubsumption.o\
         Inferences/SLQueryForwardSubsumption.o\
         Inferences/Superposition.o\
         Inferences/TautologyDeletionISE.o

VSAT_OBJ=SAT/ClauseSharing.o\
         SAT/DIMACS.o\
         SAT/Preprocess.o\
         SAT/SATClause.o\
         SAT/SATLiteral.o\
         SAT/SingleWatchSAT.o\
         SAT/TWLSolver.o

VST_OBJ= Saturation/AWPassiveClauseContainer.o\
	 Saturation/BSplitter.o\
         Saturation/ClauseContainer.o\
         Saturation/Discount.o\
         Saturation/Limits.o\
         Saturation/LRS.o\
         Saturation/Otter.o\
         Saturation/SaturationAlgorithm_Construction.o\
         Saturation/SaturationAlgorithm.o\
         Saturation/SaturationResult.o\
         Saturation/Splitter.o

VS_OBJ = Shell/CommandLine.o\
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
         Shell/TheoryFinder.o\
         Shell/Token.o\
         Shell/TPTPLexer.o\
         Shell/TPTP.o\
         Shell/TPTPParser.o


VRULE_OBJ = Rule/Index.o\
            Rule/CASC.o\
            Rule/Prolog.o\
            Rule/ProofAttempt.o

# testing procedures
VT_OBJ = Test/Output.o\
         Test/CompitOutput.o\
         Test/Compit2Output.o


VAMP_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VSAT_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ)  
VCOMPIT_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VT_OBJ)  
VGROUND_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VSAT_OBJ) $(VS_OBJ) $(VT_OBJ)  

VAMPIRE_OBJ = $(VAMP_BASIC) Global.o vampire.o
VCOMPIT_OBJ = $(VCOMPIT_BASIC) Global.o vcompit.o
UCOMPIT_OBJ = $(VCOMPIT_BASIC) Global.o compit2.o compit2_impl.o
VGROUND_OBJ = $(VGROUND_BASIC) Global.o vground.o
SAT_OBJ = $(VD_OBJ) $(SAT) sat.o
TEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ) Global.o test_SubstitutionTree.o
RTEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ) Global.o test_retrieval.o
DHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_DHMap.o
DHMSTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_DHMultiset.o
BHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_BinaryHeap.o
SLTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_SkipList.o
ALLOCTEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VT_OBJ) $(VSAT_OBJ) $(VS_OBJ) Global.o test_alloc.o
ALUCARD_OBJ = $(ALUC_BASIC) Global.o alucard.o

################################################################

all:#default make disabled

vampire: $(VAMPIRE_OBJ)
#	$(CXX) $(CXXFLAGS) $(VAMPIRE_OBJ) -o vampire
	$(CXX) -static $(CXXFLAGS) $(VAMPIRE_OBJ) -o vampire
#	strip vampire

vground: $(VGROUND_OBJ)
#	$(CXX) -static $(CXXFLAGS) $(VGROUND_OBJ) -o vground
	$(CXX) $(CXXFLAGS) $(VGROUND_OBJ) -o vground

vcompit: $(VCOMPIT_OBJ)
	$(CXX) $(CXXFLAGS) $(VCOMPIT_OBJ) -o vcompit

ucompit: $(UCOMPIT_OBJ)
	$(CXX) $(CXXFLAGS) $(UCOMPIT_OBJ) -o ucompit

# Vampipre for valgrind
vv: $(VAMPIRE_OBJ)
	$(VCXX) $(VCXXFLAGS) $(VAMPIRE_OBJ) -o vv

sat: $(SAT_OBJ)
	$(CXX) $(CXXFLAGS) $(SAT_OBJ) -o sat
#	strip sat

test: $(TEST_OBJ)
	$(CXX) $(CXXFLAGS) $(TEST_OBJ) -o test

rtest: $(RTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(RTEST_OBJ) -o rtest

test_alloc: $(ALLOCTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(ALLOCTEST_OBJ) -o test_alloc


test_DHMap: $(DHTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(DHTEST_OBJ) -o test_DHMap

test_DHMultiset: $(DHMSTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(DHMSTEST_OBJ) -o test_DHMultiset

test_BinaryHeap: $(BHTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(BHTEST_OBJ) -o test_BinaryHeap

test_SkipList: $(SLTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(SLTEST_OBJ) -o test_SkipList

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

depend:
	makedepend -Y -DVDEBUG=1 -DVTEST=1 -DCHECK_LEAKS=1 Debug/*.cpp Lib/*.cpp Shell/*.cpp Kernel/*.cpp Indexing/*.cpp Inferences/*.cpp Rule/*.cpp SAT/*.cpp Saturation/*.cpp Test/*.cpp *.cpp

.PHONY: doc
doc:
	rm -fr doc/html
	doxygen config.doc

# DO NOT DELETE

Debug/Assertion.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/System.hpp
Debug/Assertion.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Debug/Assertion.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Debug/Assertion.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Timer.hpp
Debug/Assertion.o: Shell/Options.hpp Lib/XML.hpp
Debug/Tracer.o: Debug/Tracer.hpp
Lib/Allocator.o: Lib/DHMap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Lib/Allocator.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Lib/Allocator.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Forwards.hpp Config.hpp
Lib/Allocator.o: Lib/Reflection.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Lib/Allocator.o: Lib/InverseLookup.hpp Lib/Metaiterators.hpp Lib/List.hpp
Lib/Allocator.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Lib/Allocator.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Lib/Allocator.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Lib/Allocator.o: Lib/List.hpp Shell/Statistics.hpp Shell/Options.hpp
Lib/Allocator.o: Lib/XML.hpp Lib/Environment.hpp Lib/Timer.hpp
Lib/Allocator.o: Lib/MemoryLeak.hpp Kernel/Unit.hpp Lib/Random.hpp
Lib/DHMap.o: Lib/DHMap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Lib/DHMap.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Lib/DHMap.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Forwards.hpp Config.hpp
Lib/DHMap.o: Lib/Reflection.hpp
Lib/Environment.o: Debug/Tracer.hpp Lib/Timer.hpp Debug/Assertion.hpp
Lib/Environment.o: Shell/Options.hpp Lib/Allocator.hpp Lib/XML.hpp
Lib/Environment.o: Shell/Statistics.hpp Lib/Environment.hpp Forwards.hpp
Lib/Environment.o: Config.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Lib/Event.o: Lib/Event.hpp Lib/List.hpp Forwards.hpp Config.hpp
Lib/Event.o: Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Lib/Event.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Lib/Event.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/SmartPtr.hpp
Lib/Exception.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Lib/Exception.o: Debug/Assertion.hpp Lib/Exception.hpp
Lib/Exception.o: Lib/LastCopyWatcher.hpp
Lib/Graph.o: Lib/Graph.hpp Lib/DArray.hpp Forwards.hpp Config.hpp
Lib/Graph.o: Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Lib/Graph.o: Lib/Comparison.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Lib/Graph.o: Lib/Random.hpp Lib/Reflection.hpp Lib/VirtualIterator.hpp
Lib/Graph.o: Lib/DHMultiset.hpp Lib/Hash.hpp Lib/DHMap.hpp
Lib/Graph.o: Lib/Portability.hpp Lib/Numbering.hpp Lib/Stack.hpp
Lib/Graph.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Lib/Hash.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Hash.hpp
Lib/Hash.o: Lib/Portability.hpp
Lib/Int.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Lib/Int.o: Debug/Assertion.hpp Debug/Tracer.hpp
Lib/IntNameTable.o: Lib/IntNameTable.hpp Lib/Array.hpp Debug/Assertion.hpp
Lib/IntNameTable.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Map.hpp
Lib/IntNameTable.o: Lib/Allocator.hpp Lib/Hash.hpp Lib/Exception.hpp
Lib/IntNameTable.o: Lib/LastCopyWatcher.hpp
Lib/IntUnionFind.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Lib/IntUnionFind.o: Lib/IntUnionFind.hpp Lib/Reflection.hpp Lib/Stack.hpp
Lib/IntUnionFind.o: Forwards.hpp Config.hpp Lib/BacktrackData.hpp
Lib/IntUnionFind.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Lib/IntUnionFind.o: Lib/LastCopyWatcher.hpp Lib/Int.hpp Lib/Comparison.hpp
Lib/IntUnionFind.o: Lib/Portability.hpp
Lib/IntegerSet.o: Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Lib/IntegerSet.o: Lib/IntegerSet.hpp
Lib/MemoryLeak.o: Lib/Hash.hpp Lib/Stack.hpp Forwards.hpp Config.hpp
Lib/MemoryLeak.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Lib/MemoryLeak.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
Lib/MemoryLeak.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Lib/MemoryLeak.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Lib/MemoryLeak.o: Lib/Portability.hpp Lib/MemoryLeak.hpp Lib/Set.hpp
Lib/MemoryLeak.o: Kernel/Unit.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Lib/MemoryLeak.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp
Lib/MemoryLeak.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
Lib/MemoryLeak.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Inference.hpp
Lib/MemoryLeak.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Lib/MemoryLeak.o: Kernel/FormulaUnit.hpp
Lib/MultiCounter.o: Debug/Tracer.hpp Lib/MultiCounter.hpp Debug/Assertion.hpp
Lib/MultiCounter.o: Lib/XML.hpp Lib/Int.hpp Lib/Comparison.hpp
Lib/MultiCounter.o: Lib/Portability.hpp Lib/Allocator.hpp Lib/Exception.hpp
Lib/MultiCounter.o: Lib/LastCopyWatcher.hpp
Lib/NameArray.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Lib/NameArray.o: Debug/Assertion.hpp Lib/NameArray.hpp Debug/Tracer.hpp
Lib/Random.o: Lib/Random.hpp
Lib/System.o: Lib/Portability.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Lib/System.o: Lib/Environment.hpp Forwards.hpp Config.hpp Lib/Exception.hpp
Lib/System.o: Lib/LastCopyWatcher.hpp Lib/Timer.hpp Shell/Options.hpp
Lib/System.o: Lib/Allocator.hpp Lib/XML.hpp Shell/Statistics.hpp
Lib/System.o: Lib/System.hpp
Lib/TimeCounter.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Environment.hpp
Lib/TimeCounter.o: Forwards.hpp Config.hpp Lib/Exception.hpp
Lib/TimeCounter.o: Lib/LastCopyWatcher.hpp Lib/Timer.hpp Shell/Options.hpp
Lib/TimeCounter.o: Lib/Allocator.hpp Lib/XML.hpp Lib/TimeCounter.hpp
Lib/Timer.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Int.hpp
Lib/Timer.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Timer.hpp
Shell/CNF.o: Debug/Tracer.hpp Kernel/Clause.hpp Forwards.hpp Config.hpp
Shell/CNF.o: Lib/Allocator.hpp Debug/Assertion.hpp Lib/InverseLookup.hpp
Shell/CNF.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Allocator.hpp Lib/Exception.hpp
Shell/CNF.o: Lib/LastCopyWatcher.hpp Lib/VirtualIterator.hpp
Shell/CNF.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/CNF.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
Shell/CNF.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/CNF.o: Lib/Portability.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/CNF.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/CNF.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/FormulaUnit.hpp
Shell/CNF.o: Shell/CNF.hpp
Shell/CommandLine.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
Shell/CommandLine.o: Lib/LastCopyWatcher.hpp Shell/CommandLine.hpp
Shell/CommandLine.o: Shell/Options.hpp Lib/Allocator.hpp Lib/XML.hpp
Shell/EqResWithDeletion.o: Kernel/Clause.hpp Forwards.hpp Config.hpp
Shell/EqResWithDeletion.o: Lib/Allocator.hpp Debug/Assertion.hpp
Shell/EqResWithDeletion.o: Debug/Tracer.hpp Lib/InverseLookup.hpp
Shell/EqResWithDeletion.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Allocator.hpp
Shell/EqResWithDeletion.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/EqResWithDeletion.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Shell/EqResWithDeletion.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Shell/EqResWithDeletion.o: Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/EqResWithDeletion.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/EqResWithDeletion.o: Lib/Comparison.hpp Lib/Portability.hpp
Shell/EqResWithDeletion.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Inference.hpp
Shell/EqResWithDeletion.o: Kernel/Unit.hpp Kernel/SubstHelper.hpp
Shell/EqResWithDeletion.o: Lib/DArray.hpp Lib/Random.hpp Kernel/Term.hpp
Shell/EqResWithDeletion.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/EqResWithDeletion.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Shell/EqResWithDeletion.o: Kernel/Term.hpp Shell/EqResWithDeletion.hpp
Shell/EqResWithDeletion.o: Lib/DHMap.hpp
Shell/EqualityProxy.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Shell/EqualityProxy.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/EqualityProxy.o: Debug/Assertion.hpp Lib/List.hpp Kernel/Clause.hpp
Shell/EqualityProxy.o: Lib/Allocator.hpp Debug/Tracer.hpp
Shell/EqualityProxy.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Shell/EqualityProxy.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Shell/EqualityProxy.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/EqualityProxy.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/EqualityProxy.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/EqualityProxy.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Shell/EqualityProxy.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/EqualityProxy.o: Kernel/Ordering.hpp Lib/SmartPtr.hpp
Shell/EqualityProxy.o: Kernel/Signature.hpp Lib/Map.hpp Kernel/Term.hpp
Shell/EqualityProxy.o: Indexing/TermSharing.hpp Lib/Set.hpp
Shell/EqualityProxy.o: Shell/EqualityProxy.hpp Shell/Options.hpp Lib/XML.hpp
Shell/Flattening.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Flattening.o: Lib/Allocator.hpp Debug/Assertion.hpp
Shell/Flattening.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Forwards.hpp
Shell/Flattening.o: Config.hpp Lib/List.hpp Shell/Flattening.hpp
Shell/Flattening.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/FunctionDefinition.o: Debug/Tracer.hpp Lib/Allocator.hpp
Shell/FunctionDefinition.o: Debug/Assertion.hpp Lib/BitUtils.hpp
Shell/FunctionDefinition.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Shell/FunctionDefinition.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/FunctionDefinition.o: Lib/Int.hpp Lib/Comparison.hpp
Shell/FunctionDefinition.o: Lib/Portability.hpp Kernel/Clause.hpp
Shell/FunctionDefinition.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Shell/FunctionDefinition.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Shell/FunctionDefinition.o: Lib/Reflection.hpp Lib/Metaiterators.hpp
Shell/FunctionDefinition.o: Lib/List.hpp Lib/Set.hpp Lib/TimeCounter.hpp
Shell/FunctionDefinition.o: Lib/Reflection.hpp Lib/Stack.hpp
Shell/FunctionDefinition.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Unit.hpp
Shell/FunctionDefinition.o: Lib/List.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/FunctionDefinition.o: Kernel/Connective.hpp Kernel/Inference.hpp
Shell/FunctionDefinition.o: Kernel/Unit.hpp Kernel/FormulaUnit.hpp
Shell/FunctionDefinition.o: Kernel/SubstHelper.hpp Lib/DArray.hpp
Shell/FunctionDefinition.o: Lib/Random.hpp Kernel/Term.hpp
Shell/FunctionDefinition.o: Lib/Portability.hpp Lib/Comparison.hpp
Shell/FunctionDefinition.o: Kernel/MatchTag.hpp Kernel/Term.hpp
Shell/FunctionDefinition.o: Kernel/TermVarIterator.hpp
Shell/FunctionDefinition.o: Lib/VirtualIterator.hpp
Shell/FunctionDefinition.o: Kernel/TermFunIterator.hpp Shell/Statistics.hpp
Shell/FunctionDefinition.o: Shell/FunctionDefinition.hpp Lib/DHMap.hpp
Shell/FunctionDefinition.o: Lib/MultiCounter.hpp Lib/XML.hpp
Shell/GeneralSplitting.o: Shell/GeneralSplitting.hpp Forwards.hpp Config.hpp
Shell/GeneralSplitting.o: Lib/Environment.hpp Lib/Exception.hpp
Shell/GeneralSplitting.o: Lib/LastCopyWatcher.hpp Debug/Assertion.hpp
Shell/GeneralSplitting.o: Lib/Graph.hpp Lib/DArray.hpp Lib/Allocator.hpp
Shell/GeneralSplitting.o: Debug/Tracer.hpp Lib/Comparison.hpp Lib/Random.hpp
Shell/GeneralSplitting.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Shell/GeneralSplitting.o: Lib/DHMultiset.hpp Lib/Hash.hpp Lib/DHMap.hpp
Shell/GeneralSplitting.o: Lib/Portability.hpp Lib/Numbering.hpp Lib/Stack.hpp
Shell/GeneralSplitting.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/GeneralSplitting.o: Kernel/Clause.hpp Lib/Allocator.hpp
Shell/GeneralSplitting.o: Lib/InverseLookup.hpp Lib/Metaiterators.hpp
Shell/GeneralSplitting.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/GeneralSplitting.o: Lib/Stack.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/GeneralSplitting.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/GeneralSplitting.o: Kernel/Signature.hpp Lib/Map.hpp Kernel/Term.hpp
Shell/Grounding.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Shell/Grounding.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/Grounding.o: Debug/Assertion.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Shell/Grounding.o: Debug/Tracer.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
Shell/Grounding.o: Lib/DHMap.hpp Lib/Allocator.hpp Lib/VirtualIterator.hpp
Shell/Grounding.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/Grounding.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/Grounding.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/Grounding.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Shell/Grounding.o: Lib/List.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Grounding.o: Kernel/Signature.hpp Lib/Map.hpp Kernel/SubstHelper.hpp
Shell/Grounding.o: Lib/DArray.hpp Lib/Random.hpp Kernel/Term.hpp
Shell/Grounding.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/Grounding.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Term.hpp
Shell/Grounding.o: Shell/Grounding.hpp Lib/DHMap.hpp Lib/VirtualIterator.hpp
Shell/InequalitySplitting.o: Lib/DArray.hpp Forwards.hpp Config.hpp
Shell/InequalitySplitting.o: Debug/Assertion.hpp Lib/Allocator.hpp
Shell/InequalitySplitting.o: Debug/Tracer.hpp Lib/Comparison.hpp
Shell/InequalitySplitting.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/InequalitySplitting.o: Lib/Random.hpp Lib/Reflection.hpp
Shell/InequalitySplitting.o: Lib/VirtualIterator.hpp Lib/Environment.hpp
Shell/InequalitySplitting.o: Kernel/Clause.hpp Lib/Allocator.hpp
Shell/InequalitySplitting.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Shell/InequalitySplitting.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Shell/InequalitySplitting.o: Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/InequalitySplitting.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/InequalitySplitting.o: Lib/Portability.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/InequalitySplitting.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/InequalitySplitting.o: Kernel/Signature.hpp Lib/Map.hpp Kernel/Term.hpp
Shell/InequalitySplitting.o: Indexing/TermSharing.hpp Lib/Set.hpp
Shell/InequalitySplitting.o: Shell/Options.hpp Lib/XML.hpp
Shell/InequalitySplitting.o: Shell/Statistics.hpp
Shell/InequalitySplitting.o: Shell/InequalitySplitting.hpp
Shell/Interpolants.o: Lib/Stack.hpp Forwards.hpp Config.hpp
Shell/Interpolants.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/Interpolants.o: Lib/BacktrackData.hpp Lib/List.hpp
Shell/Interpolants.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Interpolants.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
Shell/Interpolants.o: Lib/Comparison.hpp Lib/Portability.hpp
Shell/Interpolants.o: Kernel/Clause.hpp Lib/Allocator.hpp
Shell/Interpolants.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Shell/Interpolants.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/TimeCounter.hpp
Shell/Interpolants.o: Lib/Reflection.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/Interpolants.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/Interpolants.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Interpolants.o: Kernel/InferenceStore.hpp Lib/DHMap.hpp
Shell/Interpolants.o: Lib/DHMultiset.hpp Kernel/BDD.hpp Lib/Array.hpp
Shell/Interpolants.o: Lib/Hash.hpp Lib/Int.hpp Lib/Set.hpp Lib/SkipList.hpp
Shell/Interpolants.o: Lib/Random.hpp Kernel/Signature.hpp Lib/Map.hpp
Shell/Interpolants.o: SAT/TWLSolver.hpp Lib/DArray.hpp Lib/Exception.hpp
Shell/Interpolants.o: Kernel/SubstHelper.hpp Kernel/Term.hpp
Shell/Interpolants.o: Lib/Portability.hpp Lib/Comparison.hpp
Shell/Interpolants.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Term.hpp
Shell/Interpolants.o: Shell/SimplifyFalseTrue.hpp Shell/Interpolants.hpp
Shell/LaTeX.o: Shell/Options.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/LaTeX.o: Debug/Tracer.hpp Lib/XML.hpp Shell/LaTeX.hpp Forwards.hpp
Shell/LaTeX.o: Config.hpp Lib/DHMap.hpp Lib/Stack.hpp Lib/Allocator.hpp
Shell/LaTeX.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
Shell/LaTeX.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Reflection.hpp
Shell/LaTeX.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/LaTeX.o: Kernel/Connective.hpp Kernel/InferenceStore.hpp
Shell/LaTeX.o: Lib/DHMultiset.hpp Lib/Hash.hpp Lib/DHMap.hpp Kernel/BDD.hpp
Shell/LaTeX.o: Lib/Array.hpp Lib/Hash.hpp Lib/Int.hpp Lib/List.hpp
Shell/LaTeX.o: Lib/Set.hpp Lib/SkipList.hpp Lib/Random.hpp
Shell/LaTeX.o: Kernel/Signature.hpp Lib/Map.hpp SAT/TWLSolver.hpp
Shell/LaTeX.o: Lib/DArray.hpp Lib/Exception.hpp Kernel/Inference.hpp
Shell/LaTeX.o: Kernel/Unit.hpp Lib/Environment.hpp Kernel/Clause.hpp
Shell/LaTeX.o: Lib/InverseLookup.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Shell/LaTeX.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Shell/LaTeX.o: Kernel/Formula.hpp Kernel/Connective.hpp
Shell/LaTeX.o: Kernel/FormulaUnit.hpp Kernel/Term.hpp
Shell/Lexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Int.hpp
Shell/Lexer.o: Lib/Comparison.hpp Lib/Portability.hpp Shell/Lexer.hpp
Shell/Lexer.o: Lib/Array.hpp Lib/Allocator.hpp Lib/Exception.hpp
Shell/Lexer.o: Lib/LastCopyWatcher.hpp Shell/Token.hpp
Shell/LispLexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
Shell/LispLexer.o: Lib/LastCopyWatcher.hpp Shell/LispLexer.hpp
Shell/LispLexer.o: Shell/Lexer.hpp Lib/Array.hpp Lib/Allocator.hpp
Shell/LispLexer.o: Shell/Token.hpp
Shell/LispParser.o: Lib/List.hpp Shell/LispLexer.hpp Shell/Lexer.hpp
Shell/LispParser.o: Lib/Array.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/LispParser.o: Debug/Tracer.hpp Lib/Exception.hpp
Shell/LispParser.o: Lib/LastCopyWatcher.hpp Shell/Token.hpp
Shell/LispParser.o: Shell/LispParser.hpp Forwards.hpp Config.hpp
Shell/LispParser.o: Shell/Parser.hpp Lib/IntNameTable.hpp Lib/Array.hpp
Shell/LispParser.o: Lib/Map.hpp Lib/Allocator.hpp Lib/Hash.hpp
Shell/LispParser.o: Lib/Exception.hpp Lib/XML.hpp Kernel/Unit.hpp
Shell/NNF.o: Lib/Environment.hpp Forwards.hpp Config.hpp Lib/Exception.hpp
Shell/NNF.o: Lib/LastCopyWatcher.hpp Debug/Assertion.hpp Kernel/Inference.hpp
Shell/NNF.o: Kernel/Unit.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/NNF.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/NNF.o: Kernel/Term.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/NNF.o: Shell/NNF.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/NNF.o: Kernel/Connective.hpp
Shell/Naming.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Naming.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/Naming.o: Lib/Environment.hpp Forwards.hpp Config.hpp Lib/Exception.hpp
Shell/Naming.o: Lib/LastCopyWatcher.hpp Kernel/FormulaUnit.hpp
Shell/Naming.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Inference.hpp
Shell/Naming.o: Kernel/Unit.hpp Kernel/Signature.hpp Lib/Stack.hpp
Shell/Naming.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Shell/Naming.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp Lib/Int.hpp
Shell/Naming.o: Lib/Map.hpp Lib/Hash.hpp Kernel/Term.hpp Shell/Statistics.hpp
Shell/Naming.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Naming.hpp
Shell/Naming.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/Normalisation.o: Lib/Sort.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Normalisation.o: Lib/Allocator.hpp Lib/DArray.hpp Forwards.hpp
Shell/Normalisation.o: Config.hpp Lib/Comparison.hpp Lib/Exception.hpp
Shell/Normalisation.o: Lib/LastCopyWatcher.hpp Lib/Random.hpp
Shell/Normalisation.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Shell/Normalisation.o: Lib/Environment.hpp Kernel/Clause.hpp
Shell/Normalisation.o: Lib/Allocator.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
Shell/Normalisation.o: Lib/DHMap.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/Normalisation.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/Normalisation.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/Normalisation.o: Lib/Portability.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/Normalisation.o: Kernel/FormulaUnit.hpp Kernel/Inference.hpp
Shell/Normalisation.o: Kernel/Unit.hpp Kernel/Term.hpp Kernel/Signature.hpp
Shell/Normalisation.o: Lib/Map.hpp Kernel/SubformulaIterator.hpp
Shell/Normalisation.o: Lib/VirtualIterator.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/Normalisation.o: Kernel/Connective.hpp Shell/Normalisation.hpp
Shell/Normalisation.o: Lib/Comparison.hpp Shell/SymCounter.hpp
Shell/Options.o: Forwards.hpp Config.hpp Debug/Tracer.hpp Debug/Assertion.hpp
Shell/Options.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/Options.o: Lib/NameArray.hpp Lib/Random.hpp Lib/Exception.hpp
Shell/Options.o: Lib/LastCopyWatcher.hpp Shell/Options.hpp Lib/Allocator.hpp
Shell/Options.o: Lib/XML.hpp
Shell/Parser.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Int.hpp
Shell/Parser.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/IntNameTable.hpp
Shell/Parser.o: Lib/Array.hpp Lib/Allocator.hpp Lib/Map.hpp Lib/Allocator.hpp
Shell/Parser.o: Lib/Hash.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/Parser.o: Shell/Lexer.hpp Lib/Array.hpp Lib/Exception.hpp
Shell/Parser.o: Shell/Token.hpp Shell/Parser.hpp Lib/XML.hpp Kernel/Unit.hpp
Shell/PredicateDefinition.o: Lib/Allocator.hpp Debug/Assertion.hpp
Shell/PredicateDefinition.o: Debug/Tracer.hpp Lib/Environment.hpp
Shell/PredicateDefinition.o: Forwards.hpp Config.hpp Lib/Exception.hpp
Shell/PredicateDefinition.o: Lib/LastCopyWatcher.hpp Lib/Stack.hpp
Shell/PredicateDefinition.o: Lib/Allocator.hpp Lib/BacktrackData.hpp
Shell/PredicateDefinition.o: Lib/List.hpp Lib/VirtualIterator.hpp
Shell/PredicateDefinition.o: Lib/Reflection.hpp Lib/Int.hpp
Shell/PredicateDefinition.o: Lib/Comparison.hpp Lib/Portability.hpp
Shell/PredicateDefinition.o: Lib/Set.hpp Lib/MultiCounter.hpp Lib/XML.hpp
Shell/PredicateDefinition.o: Kernel/Clause.hpp Lib/InverseLookup.hpp
Shell/PredicateDefinition.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp
Shell/PredicateDefinition.o: Lib/Set.hpp Lib/TimeCounter.hpp
Shell/PredicateDefinition.o: Lib/Reflection.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/PredicateDefinition.o: Kernel/Formula.hpp Lib/XML.hpp
Shell/PredicateDefinition.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/PredicateDefinition.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/PredicateDefinition.o: Kernel/Signature.hpp Lib/Map.hpp
Shell/PredicateDefinition.o: Kernel/SubformulaIterator.hpp
Shell/PredicateDefinition.o: Lib/VirtualIterator.hpp Kernel/Formula.hpp
Shell/PredicateDefinition.o: Kernel/Term.hpp Shell/Statistics.hpp
Shell/PredicateDefinition.o: Shell/PredicateDefinition.hpp Lib/DArray.hpp
Shell/PredicateDefinition.o: Lib/Random.hpp Lib/DHMap.hpp
Shell/PredicateDefinition.o: Shell/SymCounter.hpp
Shell/Preprocess.o: Debug/Tracer.hpp Kernel/Unit.hpp Kernel/Clause.hpp
Shell/Preprocess.o: Forwards.hpp Config.hpp Lib/Allocator.hpp
Shell/Preprocess.o: Debug/Assertion.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
Shell/Preprocess.o: Lib/DHMap.hpp Lib/Allocator.hpp Lib/Exception.hpp
Shell/Preprocess.o: Lib/LastCopyWatcher.hpp Lib/VirtualIterator.hpp
Shell/Preprocess.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/Preprocess.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/Preprocess.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/Preprocess.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Shell/Preprocess.o: Lib/List.hpp Shell/CNF.hpp Shell/EqResWithDeletion.hpp
Shell/Preprocess.o: Lib/DHMap.hpp Kernel/Term.hpp Shell/EqualityProxy.hpp
Shell/Preprocess.o: Shell/Options.hpp Lib/XML.hpp Shell/Flattening.hpp
Shell/Preprocess.o: Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Preprocess.o: Shell/FunctionDefinition.hpp Lib/MultiCounter.hpp
Shell/Preprocess.o: Lib/XML.hpp Shell/GeneralSplitting.hpp
Shell/Preprocess.o: Shell/InequalitySplitting.hpp Shell/Naming.hpp
Shell/Preprocess.o: Shell/Normalisation.hpp Lib/Comparison.hpp
Shell/Preprocess.o: Shell/SymCounter.hpp Shell/NNF.hpp
Shell/Preprocess.o: Shell/PredicateDefinition.hpp Lib/DArray.hpp
Shell/Preprocess.o: Lib/Random.hpp Kernel/FormulaUnit.hpp
Shell/Preprocess.o: Shell/Preprocess.hpp Shell/Property.hpp Shell/Rectify.hpp
Shell/Preprocess.o: Lib/Array.hpp Shell/Skolem.hpp Kernel/Substitution.hpp
Shell/Preprocess.o: Lib/Random.hpp Lib/Environment.hpp Kernel/Term.hpp
Shell/Preprocess.o: Lib/Portability.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Shell/Preprocess.o: Shell/SimplifyFalseTrue.hpp Shell/SineUtils.hpp
Shell/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Profile.o: Lib/Portability.hpp Debug/Assertion.hpp Lib/Sort.hpp
Shell/Profile.o: Lib/Allocator.hpp Lib/DArray.hpp Forwards.hpp Config.hpp
Shell/Profile.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Random.hpp
Shell/Profile.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Shell/Profile.o: Lib/Environment.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Shell/Profile.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Shell/Profile.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Shell/Profile.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
Shell/Profile.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Unit.hpp
Shell/Profile.o: Lib/List.hpp Kernel/Signature.hpp Lib/Map.hpp
Shell/Profile.o: Kernel/Term.hpp Shell/Profile.hpp Kernel/Unit.hpp
Shell/Profile.o: Lib/Array.hpp
Shell/Property.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Property.o: Lib/Portability.hpp Debug/Assertion.hpp Kernel/Clause.hpp
Shell/Property.o: Forwards.hpp Config.hpp Lib/Allocator.hpp
Shell/Property.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Shell/Property.o: Lib/Allocator.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/Property.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Shell/Property.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Shell/Property.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
Shell/Property.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Unit.hpp
Shell/Property.o: Lib/List.hpp Kernel/FormulaUnit.hpp
Shell/Property.o: Kernel/SubformulaIterator.hpp Lib/VirtualIterator.hpp
Shell/Property.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/Property.o: Kernel/Term.hpp Shell/FunctionDefinition.hpp Lib/DHMap.hpp
Shell/Property.o: Lib/MultiCounter.hpp Lib/XML.hpp Kernel/Unit.hpp
Shell/Property.o: Shell/Property.hpp
Shell/Rectify.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Shell/Rectify.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/Rectify.o: Debug/Assertion.hpp Kernel/Formula.hpp Lib/List.hpp
Shell/Rectify.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/Rectify.o: Lib/Allocator.hpp Debug/Tracer.hpp Kernel/Unit.hpp
Shell/Rectify.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/Term.hpp
Shell/Rectify.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Rectify.hpp
Shell/Rectify.o: Lib/Array.hpp
Shell/Refutation.o: Debug/Tracer.hpp Lib/Hash.hpp Lib/Set.hpp Lib/Stack.hpp
Shell/Refutation.o: Forwards.hpp Config.hpp Debug/Assertion.hpp
Shell/Refutation.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Shell/Refutation.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Refutation.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
Shell/Refutation.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Clause.hpp
Shell/Refutation.o: Lib/Allocator.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
Shell/Refutation.o: Lib/DHMap.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Shell/Refutation.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Shell/Refutation.o: Lib/List.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Refutation.o: Shell/Refutation.hpp
Shell/SMTLexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
Shell/SMTLexer.o: Lib/LastCopyWatcher.hpp Shell/SMTLexer.hpp Shell/Lexer.hpp
Shell/SMTLexer.o: Lib/Array.hpp Lib/Allocator.hpp Shell/Token.hpp
Shell/SMTParser.o: Shell/SMTLexer.hpp Shell/Lexer.hpp Lib/Array.hpp
Shell/SMTParser.o: Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/SMTParser.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Shell/Token.hpp
Shell/SMTParser.o: Shell/SMTParser.hpp Shell/Parser.hpp Lib/IntNameTable.hpp
Shell/SMTParser.o: Lib/Array.hpp Lib/Map.hpp Lib/Allocator.hpp Lib/Hash.hpp
Shell/SMTParser.o: Lib/Exception.hpp Lib/XML.hpp Kernel/Unit.hpp
Shell/SimplifyFalseTrue.o: Debug/Tracer.hpp Lib/DArray.hpp Forwards.hpp
Shell/SimplifyFalseTrue.o: Config.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/SimplifyFalseTrue.o: Lib/Comparison.hpp Lib/Exception.hpp
Shell/SimplifyFalseTrue.o: Lib/LastCopyWatcher.hpp Lib/Random.hpp
Shell/SimplifyFalseTrue.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Shell/SimplifyFalseTrue.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/SimplifyFalseTrue.o: Lib/Allocator.hpp Kernel/FormulaUnit.hpp
Shell/SimplifyFalseTrue.o: Kernel/Unit.hpp Lib/List.hpp
Shell/SimplifyFalseTrue.o: Shell/SimplifyFalseTrue.hpp Kernel/Formula.hpp
Shell/SimplifyFalseTrue.o: Lib/XML.hpp Kernel/Connective.hpp
Shell/SimplifyProver.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/SimplifyProver.o: Debug/Assertion.hpp Lib/DArray.hpp Forwards.hpp
Shell/SimplifyProver.o: Config.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/SimplifyProver.o: Lib/Comparison.hpp Lib/Exception.hpp Lib/Random.hpp
Shell/SimplifyProver.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Shell/SimplifyProver.o: Lib/Environment.hpp Lib/Int.hpp Lib/Portability.hpp
Shell/SimplifyProver.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp
Shell/SimplifyProver.o: Kernel/Connective.hpp Kernel/Term.hpp
Shell/SimplifyProver.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/SimplifyProver.o: Lib/Allocator.hpp Kernel/Signature.hpp Lib/Stack.hpp
Shell/SimplifyProver.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/SimplifyProver.o: Lib/Map.hpp Lib/Hash.hpp Kernel/FormulaUnit.hpp
Shell/SimplifyProver.o: Kernel/Unit.hpp Kernel/FormulaVarIterator.hpp
Shell/SimplifyProver.o: Lib/MultiCounter.hpp Lib/XML.hpp
Shell/SimplifyProver.o: Kernel/TermVarIterator.hpp Lib/VirtualIterator.hpp
Shell/SimplifyProver.o: Shell/SimplifyProver.hpp Lib/Set.hpp
Shell/SimplifyProver.o: Shell/LispParser.hpp Shell/Parser.hpp
Shell/SimplifyProver.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp
Shell/SimplifyProver.o: Shell/Token.hpp Shell/Statistics.hpp
Shell/SineUtils.o: Lib/DHMultiset.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/SineUtils.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Shell/SineUtils.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/VirtualIterator.hpp
Shell/SineUtils.o: Forwards.hpp Config.hpp Lib/Reflection.hpp
Shell/SineUtils.o: Lib/Portability.hpp Lib/Environment.hpp Lib/List.hpp
Shell/SineUtils.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Shell/SineUtils.o: Lib/TimeCounter.hpp Lib/Set.hpp Lib/VirtualIterator.hpp
Shell/SineUtils.o: Kernel/Clause.hpp Lib/Allocator.hpp Lib/InverseLookup.hpp
Shell/SineUtils.o: Lib/Reflection.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Shell/SineUtils.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Unit.hpp
Shell/SineUtils.o: Kernel/FormulaUnit.hpp Kernel/Signature.hpp Lib/Map.hpp
Shell/SineUtils.o: Kernel/SubformulaIterator.hpp Kernel/Formula.hpp
Shell/SineUtils.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/Term.hpp
Shell/SineUtils.o: Kernel/TermFunIterator.hpp Shell/Options.hpp
Shell/SineUtils.o: Shell/SineUtils.hpp Lib/DArray.hpp Lib/Random.hpp
Shell/Skolem.o: Kernel/Signature.hpp Forwards.hpp Config.hpp
Shell/Skolem.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Skolem.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Shell/Skolem.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Skolem.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
Shell/Skolem.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Map.hpp
Shell/Skolem.o: Lib/Hash.hpp Kernel/Term.hpp Kernel/Inference.hpp
Shell/Skolem.o: Kernel/Unit.hpp Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/Skolem.o: Lib/List.hpp Kernel/SubformulaIterator.hpp
Shell/Skolem.o: Lib/VirtualIterator.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/Skolem.o: Kernel/Connective.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/Skolem.o: Shell/Options.hpp Shell/Rectify.hpp Lib/Array.hpp
Shell/Skolem.o: Kernel/Formula.hpp Shell/Skolem.hpp Kernel/Substitution.hpp
Shell/Skolem.o: Lib/Random.hpp Lib/Environment.hpp Kernel/Term.hpp
Shell/Skolem.o: Lib/Portability.hpp Lib/Comparison.hpp Lib/Metaiterators.hpp
Shell/Skolem.o: Lib/Set.hpp Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Shell/Skolem.o: Lib/BitUtils.hpp
Shell/Statistics.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Statistics.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Shell/Statistics.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Timer.hpp
Shell/Statistics.o: Shell/Options.hpp Lib/XML.hpp Shell/Statistics.hpp
Shell/SymCounter.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/SymCounter.o: Kernel/Term.hpp Kernel/Clause.hpp Forwards.hpp Config.hpp
Shell/SymCounter.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Shell/SymCounter.o: Lib/Allocator.hpp Lib/Exception.hpp
Shell/SymCounter.o: Lib/LastCopyWatcher.hpp Lib/VirtualIterator.hpp
Shell/SymCounter.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/SymCounter.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/SymCounter.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/SymCounter.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Shell/SymCounter.o: Lib/List.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/SymCounter.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/SymCounter.o: Kernel/Signature.hpp Lib/Map.hpp Kernel/Unit.hpp
Shell/SymCounter.o: Shell/SymCounter.hpp
Shell/TPTP.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/TPTP.o: Debug/Assertion.hpp Kernel/Term.hpp Kernel/Inference.hpp
Shell/TPTP.o: Kernel/Unit.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/TPTP.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp
Shell/TPTP.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/TPTP.o: Forwards.hpp Config.hpp Kernel/Clause.hpp Lib/InverseLookup.hpp
Shell/TPTP.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Allocator.hpp Lib/Exception.hpp
Shell/TPTP.o: Lib/LastCopyWatcher.hpp Lib/VirtualIterator.hpp
Shell/TPTP.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/TPTP.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/TPTP.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp Shell/TPTP.hpp
Shell/TPTPLexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
Shell/TPTPLexer.o: Lib/LastCopyWatcher.hpp Shell/TPTPLexer.hpp
Shell/TPTPLexer.o: Shell/Lexer.hpp Lib/Array.hpp Lib/Allocator.hpp
Shell/TPTPLexer.o: Shell/Token.hpp
Shell/TPTPParser.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/TPTPParser.o: Lib/Portability.hpp Debug/Assertion.hpp Lib/Stack.hpp
Shell/TPTPParser.o: Forwards.hpp Config.hpp Debug/Tracer.hpp
Shell/TPTPParser.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Shell/TPTPParser.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/TPTPParser.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
Shell/TPTPParser.o: Lib/Environment.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/TPTPParser.o: Lib/Allocator.hpp Kernel/Signature.hpp Lib/Map.hpp
Shell/TPTPParser.o: Lib/Hash.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/TPTPParser.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/TPTPParser.o: Kernel/Unit.hpp Kernel/Term.hpp Kernel/Clause.hpp
Shell/TPTPParser.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp
Shell/TPTPParser.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/TPTPParser.o: Shell/Statistics.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/TPTPParser.o: Shell/Options.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
Shell/TPTPParser.o: Lib/Array.hpp Lib/Exception.hpp Shell/Token.hpp
Shell/TPTPParser.o: Shell/TPTPParser.hpp Shell/Parser.hpp
Shell/TPTPParser.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp
Shell/TheoryFinder.o: Debug/Tracer.hpp Kernel/Clause.hpp Forwards.hpp
Shell/TheoryFinder.o: Config.hpp Lib/Allocator.hpp Debug/Assertion.hpp
Shell/TheoryFinder.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Shell/TheoryFinder.o: Lib/Allocator.hpp Lib/Exception.hpp
Shell/TheoryFinder.o: Lib/LastCopyWatcher.hpp Lib/VirtualIterator.hpp
Shell/TheoryFinder.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/TheoryFinder.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Shell/TheoryFinder.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/TheoryFinder.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Shell/TheoryFinder.o: Lib/List.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/TheoryFinder.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/TheoryFinder.o: Kernel/Term.hpp Shell/Property.hpp Kernel/Unit.hpp
Shell/TheoryFinder.o: Shell/TheoryFinder.hpp
Shell/Token.o: Debug/Assertion.hpp Shell/Token.hpp
Kernel/BDD.o: Lib/Cache.hpp Forwards.hpp Config.hpp Debug/Assertion.hpp
Kernel/BDD.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Environment.hpp
Kernel/BDD.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Exception.hpp
Kernel/BDD.o: Lib/DHMap.hpp Lib/DHSet.hpp Lib/DHMap.hpp Lib/Hash.hpp
Kernel/BDD.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp Lib/Int.hpp
Kernel/BDD.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/List.hpp
Kernel/BDD.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/BDD.o: Lib/Timer.hpp Lib/TimeCounter.hpp Kernel/Formula.hpp
Kernel/BDD.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/Signature.hpp
Kernel/BDD.o: Lib/Allocator.hpp Lib/Map.hpp Kernel/Term.hpp
Kernel/BDD.o: Lib/Portability.hpp Lib/Comparison.hpp Lib/Metaiterators.hpp
Kernel/BDD.o: Lib/Set.hpp Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Kernel/BDD.o: Lib/BitUtils.hpp SAT/ClauseSharing.hpp Lib/Set.hpp
Kernel/BDD.o: Lib/VirtualIterator.hpp SAT/SATClause.hpp Lib/InverseLookup.hpp
Kernel/BDD.o: Lib/Reflection.hpp SAT/SATLiteral.hpp SAT/Preprocess.hpp
Kernel/BDD.o: SAT/SATClause.hpp SAT/SATLiteral.hpp SAT/SingleWatchSAT.hpp
Kernel/BDD.o: Lib/DArray.hpp Lib/Random.hpp Lib/BinaryHeap.hpp
Kernel/BDD.o: Lib/Metaiterators.hpp Lib/BucketSorter.hpp Lib/Stack.hpp
Kernel/BDD.o: Shell/Options.hpp Kernel/BDD.hpp Lib/Array.hpp Lib/Hash.hpp
Kernel/BDD.o: Lib/SkipList.hpp Kernel/Signature.hpp SAT/TWLSolver.hpp
Kernel/Clause.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/Clause.o: Lib/DArray.hpp Forwards.hpp Config.hpp Lib/Allocator.hpp
Kernel/Clause.o: Lib/Comparison.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/Clause.o: Lib/Random.hpp Lib/Reflection.hpp Lib/VirtualIterator.hpp
Kernel/Clause.o: Lib/Environment.hpp Lib/Int.hpp Lib/Portability.hpp
Kernel/Clause.o: Lib/SharedSet.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/Clause.o: Lib/Hash.hpp Lib/Sort.hpp Lib/DArray.hpp Lib/Stack.hpp
Kernel/Clause.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp Lib/Stack.hpp
Kernel/Clause.o: SAT/SATClause.hpp Shell/Options.hpp Lib/XML.hpp
Kernel/Clause.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/Clause.hpp
Kernel/Clause.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp
Kernel/Clause.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Kernel/Clause.o: Lib/List.hpp Kernel/Term.hpp Lib/Portability.hpp
Kernel/Clause.o: Lib/Comparison.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/Clause.o: Kernel/BDD.hpp Lib/Array.hpp Lib/DHMap.hpp Lib/Hash.hpp
Kernel/Clause.o: Lib/Set.hpp Lib/SkipList.hpp Kernel/Signature.hpp
Kernel/Clause.o: Lib/Map.hpp SAT/TWLSolver.hpp Lib/Exception.hpp
Kernel/Clause.o: Kernel/Signature.hpp
Kernel/ClauseQueue.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Assertion.hpp
Kernel/ClauseQueue.o: Lib/Random.hpp Lib/Environment.hpp Forwards.hpp
Kernel/ClauseQueue.o: Config.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/ClauseQueue.o: Kernel/Clause.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
Kernel/ClauseQueue.o: Lib/DHMap.hpp Lib/Allocator.hpp Lib/VirtualIterator.hpp
Kernel/ClauseQueue.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Kernel/ClauseQueue.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Kernel/ClauseQueue.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Kernel/ClauseQueue.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Kernel/ClauseQueue.o: Lib/List.hpp Kernel/ClauseQueue.hpp
Kernel/EGSubstitution.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Kernel/EGSubstitution.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/EGSubstitution.o: Debug/Assertion.hpp Lib/Hash.hpp Lib/DArray.hpp
Kernel/EGSubstitution.o: Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/EGSubstitution.o: Lib/Comparison.hpp Lib/Random.hpp Lib/Reflection.hpp
Kernel/EGSubstitution.o: Lib/VirtualIterator.hpp Lib/List.hpp Lib/Random.hpp
Kernel/EGSubstitution.o: Lib/DHMultiset.hpp Lib/Hash.hpp Lib/DHMap.hpp
Kernel/EGSubstitution.o: Lib/Portability.hpp Lib/DHMap.hpp Lib/SkipList.hpp
Kernel/EGSubstitution.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/EGSubstitution.o: Lib/Int.hpp Kernel/Term.hpp Lib/Allocator.hpp
Kernel/EGSubstitution.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/EGSubstitution.o: Lib/Stack.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/EGSubstitution.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Kernel/EGSubstitution.o: Lib/BitUtils.hpp Kernel/Clause.hpp
Kernel/EGSubstitution.o: Lib/InverseLookup.hpp Lib/Reflection.hpp
Kernel/EGSubstitution.o: Kernel/Unit.hpp Kernel/Renaming.hpp
Kernel/EGSubstitution.o: Lib/VirtualIterator.hpp Indexing/TermSharing.hpp
Kernel/EGSubstitution.o: Lib/Set.hpp Kernel/Term.hpp
Kernel/EGSubstitution.o: Kernel/EGSubstitution.hpp Lib/BacktrackData.hpp
Kernel/EGSubstitution.o: Kernel/RobSubstitution.hpp Test/Output.hpp
Kernel/EqHelper.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Kernel/EqHelper.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/EqHelper.o: Debug/Assertion.hpp Shell/Options.hpp Lib/Allocator.hpp
Kernel/EqHelper.o: Debug/Tracer.hpp Lib/XML.hpp Kernel/EqHelper.hpp
Kernel/EqHelper.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp Lib/List.hpp
Kernel/EqHelper.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Kernel/EqHelper.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/EqHelper.o: Lib/TimeCounter.hpp Lib/PairUtils.hpp
Kernel/EqHelper.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp Kernel/Term.hpp
Kernel/EqHelper.o: Lib/Portability.hpp Lib/Comparison.hpp Lib/Stack.hpp
Kernel/EqHelper.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/EqHelper.o: Lib/Portability.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/Formula.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/Formula.o: Debug/Assertion.hpp Lib/MultiCounter.hpp Lib/XML.hpp
Kernel/Formula.o: Kernel/BDD.hpp Forwards.hpp Config.hpp Lib/Allocator.hpp
Kernel/Formula.o: Lib/Array.hpp Lib/DHMap.hpp Lib/Hash.hpp Lib/Int.hpp
Kernel/Formula.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/List.hpp
Kernel/Formula.o: Lib/Set.hpp Lib/SkipList.hpp Lib/Allocator.hpp
Kernel/Formula.o: Lib/Random.hpp Lib/BacktrackData.hpp Lib/List.hpp
Kernel/Formula.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Formula.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Stack.hpp
Kernel/Formula.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Kernel/Formula.o: SAT/TWLSolver.hpp Lib/DArray.hpp Kernel/Clause.hpp
Kernel/Formula.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp
Kernel/Formula.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Kernel/Formula.o: Kernel/Unit.hpp Kernel/Term.hpp Lib/Portability.hpp
Kernel/Formula.o: Lib/XML.hpp Lib/Comparison.hpp Kernel/MatchTag.hpp
Kernel/Formula.o: Lib/BitUtils.hpp Kernel/Formula.hpp Kernel/Connective.hpp
Kernel/Formula.o: Kernel/SubformulaIterator.hpp Lib/VirtualIterator.hpp
Kernel/Formula.o: Kernel/FormulaVarIterator.hpp Kernel/Term.hpp
Kernel/Formula.o: Kernel/Formula.hpp
Kernel/FormulaUnit.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/FormulaUnit.o: Debug/Assertion.hpp Kernel/Formula.hpp Lib/List.hpp
Kernel/FormulaUnit.o: Lib/XML.hpp Kernel/Connective.hpp
Kernel/FormulaUnit.o: Kernel/FormulaUnit.hpp Lib/Allocator.hpp
Kernel/FormulaUnit.o: Debug/Tracer.hpp Kernel/Unit.hpp Forwards.hpp
Kernel/FormulaUnit.o: Config.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/FormulaUnit.o: Kernel/SubformulaIterator.hpp Lib/VirtualIterator.hpp
Kernel/FormulaUnit.o: Kernel/Term.hpp Lib/Portability.hpp Lib/Comparison.hpp
Kernel/FormulaUnit.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/FormulaUnit.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/FormulaUnit.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
Kernel/FormulaUnit.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/FormulaUnit.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Kernel/FormulaUnit.o: Lib/BitUtils.hpp
Kernel/FormulaVarIterator.o: Debug/Tracer.hpp Kernel/FormulaVarIterator.hpp
Kernel/FormulaVarIterator.o: Lib/MultiCounter.hpp Debug/Assertion.hpp
Kernel/FormulaVarIterator.o: Lib/XML.hpp Lib/Stack.hpp Forwards.hpp
Kernel/FormulaVarIterator.o: Config.hpp Lib/Allocator.hpp
Kernel/FormulaVarIterator.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/FormulaVarIterator.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/FormulaVarIterator.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp
Kernel/FormulaVarIterator.o: Lib/Int.hpp Lib/Comparison.hpp
Kernel/FormulaVarIterator.o: Lib/Portability.hpp Kernel/Term.hpp
Kernel/FormulaVarIterator.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp
Kernel/FormulaVarIterator.o: Kernel/Connective.hpp Kernel/Formula.hpp
Kernel/FormulaVarIterator.o: Kernel/Term.hpp Lib/Allocator.hpp
Kernel/FormulaVarIterator.o: Lib/Portability.hpp Lib/Comparison.hpp
Kernel/FormulaVarIterator.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/FormulaVarIterator.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Kernel/FormulaVarIterator.o: Lib/BitUtils.hpp
Kernel/Inference.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Inference.o: Lib/Allocator.hpp Debug/Assertion.hpp
Kernel/InferenceStore.o: Lib/Allocator.hpp Debug/Assertion.hpp
Kernel/InferenceStore.o: Debug/Tracer.hpp Lib/Environment.hpp Forwards.hpp
Kernel/InferenceStore.o: Config.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/InferenceStore.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/InferenceStore.o: Lib/SharedSet.hpp Lib/Allocator.hpp
Kernel/InferenceStore.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/InferenceStore.o: Lib/Reflection.hpp Lib/Sort.hpp Lib/DArray.hpp
Kernel/InferenceStore.o: Lib/Random.hpp Lib/VirtualIterator.hpp Lib/Stack.hpp
Kernel/InferenceStore.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/InferenceStore.o: Lib/Stack.hpp Kernel/BDD.hpp Lib/Array.hpp
Kernel/InferenceStore.o: Lib/DHMap.hpp Lib/Hash.hpp Lib/List.hpp Lib/Set.hpp
Kernel/InferenceStore.o: Lib/SkipList.hpp Kernel/Signature.hpp Lib/Map.hpp
Kernel/InferenceStore.o: SAT/TWLSolver.hpp Lib/DArray.hpp Lib/Exception.hpp
Kernel/InferenceStore.o: Kernel/Clause.hpp Lib/InverseLookup.hpp
Kernel/InferenceStore.o: Lib/DHMap.hpp Lib/Metaiterators.hpp
Kernel/InferenceStore.o: Lib/TimeCounter.hpp Lib/Reflection.hpp
Kernel/InferenceStore.o: Kernel/Unit.hpp Kernel/Formula.hpp Lib/XML.hpp
Kernel/InferenceStore.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Kernel/InferenceStore.o: Kernel/FormulaVarIterator.hpp Lib/MultiCounter.hpp
Kernel/InferenceStore.o: Lib/XML.hpp Kernel/Term.hpp Kernel/Inference.hpp
Kernel/InferenceStore.o: Kernel/Unit.hpp Shell/LaTeX.hpp
Kernel/InferenceStore.o: Kernel/Connective.hpp Kernel/InferenceStore.hpp
Kernel/InferenceStore.o: Lib/DHMultiset.hpp Shell/Options.hpp
Kernel/InferenceStore.o: Kernel/InferenceStore.hpp
Kernel/KBO.o: Debug/Tracer.hpp Lib/Environment.hpp Forwards.hpp Config.hpp
Kernel/KBO.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Debug/Assertion.hpp
Kernel/KBO.o: Lib/Comparison.hpp Lib/DArray.hpp Lib/Allocator.hpp
Kernel/KBO.o: Lib/Comparison.hpp Lib/Random.hpp Lib/Reflection.hpp
Kernel/KBO.o: Lib/VirtualIterator.hpp Lib/DHMap.hpp Lib/Int.hpp
Kernel/KBO.o: Lib/Portability.hpp Lib/Metaiterators.hpp Lib/List.hpp
Kernel/KBO.o: Lib/Set.hpp Lib/Hash.hpp Lib/TimeCounter.hpp
Kernel/KBO.o: Shell/EqualityProxy.hpp Kernel/Term.hpp Shell/Options.hpp
Kernel/KBO.o: Lib/Allocator.hpp Lib/XML.hpp Shell/Options.hpp Kernel/Term.hpp
Kernel/KBO.o: Lib/Portability.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Kernel/KBO.o: Lib/Int.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/KBO.hpp
Kernel/KBO.o: Kernel/Ordering.hpp Lib/SmartPtr.hpp Kernel/Signature.hpp
Kernel/KBO.o: Lib/Map.hpp
Kernel/LiteralSelector.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/LiteralSelector.o: Debug/Assertion.hpp Kernel/Term.hpp Forwards.hpp
Kernel/LiteralSelector.o: Config.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/LiteralSelector.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/LiteralSelector.o: Lib/Stack.hpp Lib/Allocator.hpp
Kernel/LiteralSelector.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/LiteralSelector.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/LiteralSelector.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/LiteralSelector.o: Lib/Portability.hpp Lib/Metaiterators.hpp
Kernel/LiteralSelector.o: Lib/Set.hpp Lib/Hash.hpp Lib/TimeCounter.hpp
Kernel/LiteralSelector.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/LiteralSelector.o: Kernel/Clause.hpp Lib/InverseLookup.hpp
Kernel/LiteralSelector.o: Lib/DHMap.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Kernel/LiteralSelector.o: Lib/List.hpp Kernel/LiteralSelector.hpp
Kernel/LiteralSelector.o: Kernel/MaximalLiteralSelector.hpp Lib/SmartPtr.hpp
Kernel/LiteralSelector.o: Kernel/Ordering.hpp Kernel/BestLiteralSelector.hpp
Kernel/LiteralSelector.o: Lib/DArray.hpp Lib/Random.hpp Lib/Set.hpp
Kernel/LiteralSelector.o: Kernel/LiteralComparators.hpp Lib/Int.hpp
Kernel/LiteralSelector.o: Kernel/Renaming.hpp Lib/DHMap.hpp
Kernel/LiteralSelector.o: Lib/VirtualIterator.hpp
Kernel/MLMatcher.o: Lib/BacktrackData.hpp Lib/BacktrackIterators.hpp
Kernel/MLMatcher.o: Lib/DArray.hpp Forwards.hpp Config.hpp
Kernel/MLMatcher.o: Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/MLMatcher.o: Lib/Comparison.hpp Lib/Exception.hpp
Kernel/MLMatcher.o: Lib/LastCopyWatcher.hpp Lib/Random.hpp Lib/Reflection.hpp
Kernel/MLMatcher.o: Lib/VirtualIterator.hpp Lib/Stack.hpp
Kernel/MLMatcher.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/MLMatcher.o: Lib/Portability.hpp Lib/Metaiterators.hpp
Kernel/MLMatcher.o: Lib/BinaryHeap.hpp Lib/DArray.hpp Lib/DHMap.hpp
Kernel/MLMatcher.o: Lib/Environment.hpp Lib/Hash.hpp Lib/Int.hpp
Kernel/MLMatcher.o: Lib/Metaarrays.hpp Lib/PairUtils.hpp Lib/Metaarrays.hpp
Kernel/MLMatcher.o: Lib/Stack.hpp Lib/TriangularArray.hpp Lib/BitUtils.hpp
Kernel/MLMatcher.o: Kernel/Clause.hpp Lib/Allocator.hpp Lib/InverseLookup.hpp
Kernel/MLMatcher.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp
Kernel/MLMatcher.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Kernel/MLMatcher.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Term.hpp
Kernel/MLMatcher.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/MLMatcher.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Matcher.hpp
Kernel/MLMatcher.o: Lib/VirtualIterator.hpp Kernel/Term.hpp
Kernel/MLMatcher.o: Kernel/MLMatcher.hpp Test/Output.hpp
Kernel/MLVariant.o: Lib/BacktrackData.hpp Lib/BacktrackIterators.hpp
Kernel/MLVariant.o: Lib/DArray.hpp Forwards.hpp Config.hpp
Kernel/MLVariant.o: Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/MLVariant.o: Lib/Comparison.hpp Lib/Exception.hpp
Kernel/MLVariant.o: Lib/LastCopyWatcher.hpp Lib/Random.hpp Lib/Reflection.hpp
Kernel/MLVariant.o: Lib/VirtualIterator.hpp Lib/Stack.hpp
Kernel/MLVariant.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/MLVariant.o: Lib/Portability.hpp Lib/Metaiterators.hpp
Kernel/MLVariant.o: Lib/BinaryHeap.hpp Lib/DArray.hpp Lib/DHMap.hpp
Kernel/MLVariant.o: Lib/Environment.hpp Lib/Hash.hpp Lib/Int.hpp
Kernel/MLVariant.o: Lib/Metaarrays.hpp Lib/PairUtils.hpp Lib/Metaarrays.hpp
Kernel/MLVariant.o: Lib/Stack.hpp Lib/TriangularArray.hpp Lib/BitUtils.hpp
Kernel/MLVariant.o: Kernel/Clause.hpp Lib/Allocator.hpp Lib/InverseLookup.hpp
Kernel/MLVariant.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp
Kernel/MLVariant.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Kernel/MLVariant.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Term.hpp
Kernel/MLVariant.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/MLVariant.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Matcher.hpp
Kernel/MLVariant.o: Lib/VirtualIterator.hpp Kernel/Term.hpp
Kernel/MLVariant.o: Kernel/MLVariant.hpp Test/Output.hpp
Kernel/MatchTag.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/MatchTag.o: Debug/Assertion.hpp Kernel/Term.hpp Forwards.hpp
Kernel/MatchTag.o: Config.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/MatchTag.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/MatchTag.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/MatchTag.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/MatchTag.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
Kernel/MatchTag.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/MatchTag.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/MaximalLiteralSelector.o: Lib/List.hpp Kernel/Term.hpp Forwards.hpp
Kernel/MaximalLiteralSelector.o: Config.hpp Debug/Assertion.hpp
Kernel/MaximalLiteralSelector.o: Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/MaximalLiteralSelector.o: Lib/Portability.hpp Lib/XML.hpp
Kernel/MaximalLiteralSelector.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/MaximalLiteralSelector.o: Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/MaximalLiteralSelector.o: Lib/List.hpp Lib/VirtualIterator.hpp
Kernel/MaximalLiteralSelector.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/MaximalLiteralSelector.o: Lib/Reflection.hpp Lib/Int.hpp
Kernel/MaximalLiteralSelector.o: Lib/Comparison.hpp Lib/Portability.hpp
Kernel/MaximalLiteralSelector.o: Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/MaximalLiteralSelector.o: Lib/Hash.hpp Lib/TimeCounter.hpp
Kernel/MaximalLiteralSelector.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/MaximalLiteralSelector.o: Kernel/Clause.hpp Lib/InverseLookup.hpp
Kernel/MaximalLiteralSelector.o: Lib/DHMap.hpp Lib/Reflection.hpp
Kernel/MaximalLiteralSelector.o: Kernel/Unit.hpp
Kernel/MaximalLiteralSelector.o: Kernel/MaximalLiteralSelector.hpp
Kernel/MaximalLiteralSelector.o: Lib/SmartPtr.hpp Kernel/Ordering.hpp
Kernel/MaximalLiteralSelector.o: Kernel/LiteralSelector.hpp
Kernel/Ordering.o: Forwards.hpp Config.hpp Lib/List.hpp Lib/SmartPtr.hpp
Kernel/Ordering.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Environment.hpp
Kernel/Ordering.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/Ordering.o: Lib/Exception.hpp Shell/Options.hpp Lib/Allocator.hpp
Kernel/Ordering.o: Lib/XML.hpp Kernel/Ordering.hpp Kernel/KBO.hpp
Kernel/Ordering.o: Lib/DArray.hpp Lib/Allocator.hpp Lib/Comparison.hpp
Kernel/Ordering.o: Lib/Random.hpp Lib/Reflection.hpp Lib/VirtualIterator.hpp
Kernel/Renaming.o: Lib/DArray.hpp Forwards.hpp Config.hpp Debug/Assertion.hpp
Kernel/Renaming.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Comparison.hpp
Kernel/Renaming.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Random.hpp
Kernel/Renaming.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Kernel/Renaming.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
Kernel/Renaming.o: Kernel/SubstHelper.hpp Kernel/Term.hpp Lib/Allocator.hpp
Kernel/Renaming.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Renaming.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp
Kernel/Renaming.o: Lib/Int.hpp Lib/Portability.hpp Lib/Metaiterators.hpp
Kernel/Renaming.o: Lib/Set.hpp Lib/Hash.hpp Lib/TimeCounter.hpp
Kernel/Renaming.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Renaming.hpp
Kernel/Renaming.o: Lib/DHMap.hpp Lib/VirtualIterator.hpp Lib/Int.hpp
Kernel/RobSubstitution.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Kernel/RobSubstitution.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/RobSubstitution.o: Debug/Assertion.hpp Lib/Hash.hpp Lib/DArray.hpp
Kernel/RobSubstitution.o: Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/RobSubstitution.o: Lib/Comparison.hpp Lib/Random.hpp
Kernel/RobSubstitution.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Kernel/RobSubstitution.o: Lib/List.hpp Lib/Random.hpp Lib/DHSet.hpp
Kernel/RobSubstitution.o: Lib/DHMap.hpp Lib/Hash.hpp Lib/DHMap.hpp
Kernel/RobSubstitution.o: Lib/SkipList.hpp Lib/BacktrackData.hpp Lib/List.hpp
Kernel/RobSubstitution.o: Lib/Int.hpp Lib/Portability.hpp Lib/Int.hpp
Kernel/RobSubstitution.o: Kernel/Term.hpp Lib/Allocator.hpp
Kernel/RobSubstitution.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/RobSubstitution.o: Lib/Stack.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/RobSubstitution.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Kernel/RobSubstitution.o: Lib/BitUtils.hpp Kernel/Clause.hpp
Kernel/RobSubstitution.o: Lib/InverseLookup.hpp Lib/Reflection.hpp
Kernel/RobSubstitution.o: Kernel/Unit.hpp Kernel/Renaming.hpp
Kernel/RobSubstitution.o: Lib/VirtualIterator.hpp Indexing/TermSharing.hpp
Kernel/RobSubstitution.o: Lib/Set.hpp Kernel/Term.hpp
Kernel/RobSubstitution.o: Kernel/RobSubstitution.hpp Lib/BacktrackData.hpp
Kernel/RobSubstitution.o: Test/Output.hpp
Kernel/Signature.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Kernel/Signature.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Kernel/Signature.o: Debug/Assertion.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Signature.o: Lib/Portability.hpp Shell/Options.hpp Lib/Allocator.hpp
Kernel/Signature.o: Debug/Tracer.hpp Lib/XML.hpp Kernel/Signature.hpp
Kernel/Signature.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/Signature.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Reflection.hpp
Kernel/Signature.o: Lib/Int.hpp Lib/Map.hpp Lib/Hash.hpp
Kernel/SubformulaIterator.o: Debug/Tracer.hpp Kernel/SubformulaIterator.hpp
Kernel/SubformulaIterator.o: Lib/VirtualIterator.hpp Kernel/Formula.hpp
Kernel/SubformulaIterator.o: Lib/List.hpp Lib/XML.hpp Kernel/Connective.hpp
Kernel/Substitution.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/Substitution.o: Debug/Assertion.hpp Kernel/Term.hpp Forwards.hpp
Kernel/Substitution.o: Config.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/Substitution.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Substitution.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/Substitution.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Substitution.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
Kernel/Substitution.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/Substitution.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Kernel/Substitution.o: Lib/BitUtils.hpp Kernel/Substitution.hpp
Kernel/Substitution.o: Lib/Random.hpp Lib/Environment.hpp
Kernel/Term.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Assertion.hpp
Kernel/Term.o: Lib/Environment.hpp Forwards.hpp Config.hpp Lib/Exception.hpp
Kernel/Term.o: Lib/LastCopyWatcher.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/Term.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
Kernel/Term.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Term.o: Lib/Portability.hpp Lib/Set.hpp Lib/Int.hpp
Kernel/Term.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Kernel/Term.o: Kernel/Substitution.hpp Lib/Random.hpp Kernel/Term.hpp
Kernel/Term.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Term.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/TimeCounter.hpp
Kernel/Term.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Ordering.hpp
Kernel/Term.o: Lib/SmartPtr.hpp Indexing/TermSharing.hpp Kernel/Term.hpp
Kernel/TermFunIterator.o: Debug/Tracer.hpp Kernel/Term.hpp Forwards.hpp
Kernel/TermFunIterator.o: Config.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/TermFunIterator.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/TermFunIterator.o: Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermFunIterator.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/TermFunIterator.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/TermFunIterator.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp
Kernel/TermFunIterator.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/TermFunIterator.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/TermFunIterator.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Kernel/TermFunIterator.o: Lib/BitUtils.hpp Kernel/TermFunIterator.hpp
Kernel/TermFunIterator.o: Lib/VirtualIterator.hpp
Kernel/TermVarIterator.o: Debug/Tracer.hpp Kernel/Term.hpp Forwards.hpp
Kernel/TermVarIterator.o: Config.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/TermVarIterator.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/TermVarIterator.o: Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermVarIterator.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/TermVarIterator.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/TermVarIterator.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp
Kernel/TermVarIterator.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/TermVarIterator.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/TermVarIterator.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Kernel/TermVarIterator.o: Lib/BitUtils.hpp Kernel/TermVarIterator.hpp
Kernel/TermVarIterator.o: Lib/VirtualIterator.hpp
Kernel/Unit.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Unit.o: Lib/Portability.hpp Debug/Assertion.hpp Kernel/BDD.hpp
Kernel/Unit.o: Forwards.hpp Config.hpp Lib/Allocator.hpp Lib/Array.hpp
Kernel/Unit.o: Lib/DHMap.hpp Lib/Hash.hpp Lib/List.hpp Lib/Set.hpp
Kernel/Unit.o: Lib/SkipList.hpp Lib/Allocator.hpp Lib/Random.hpp
Kernel/Unit.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
Kernel/Unit.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Reflection.hpp
Kernel/Unit.o: Lib/Int.hpp Lib/Stack.hpp Kernel/Signature.hpp Lib/Map.hpp
Kernel/Unit.o: Lib/Hash.hpp SAT/TWLSolver.hpp Lib/DArray.hpp
Kernel/Unit.o: Lib/Exception.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Unit.o: Kernel/Clause.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Kernel/Unit.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/TimeCounter.hpp
Kernel/Unit.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/Formula.hpp
Kernel/Unit.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Indexing/ClauseVariantIndex.o: Lib/List.hpp Lib/Metaiterators.hpp
Indexing/ClauseVariantIndex.o: Forwards.hpp Config.hpp Lib/List.hpp
Indexing/ClauseVariantIndex.o: Debug/Assertion.hpp Lib/Allocator.hpp
Indexing/ClauseVariantIndex.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Indexing/ClauseVariantIndex.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Indexing/ClauseVariantIndex.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Indexing/ClauseVariantIndex.o: Lib/TimeCounter.hpp Lib/SmartPtr.hpp
Indexing/ClauseVariantIndex.o: Lib/TimeCounter.hpp Kernel/Clause.hpp
Indexing/ClauseVariantIndex.o: Lib/Allocator.hpp Lib/InverseLookup.hpp
Indexing/ClauseVariantIndex.o: Lib/DHMap.hpp Lib/Reflection.hpp Lib/Stack.hpp
Indexing/ClauseVariantIndex.o: Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/ClauseVariantIndex.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/ClauseVariantIndex.o: Kernel/Unit.hpp Kernel/LiteralComparators.hpp
Indexing/ClauseVariantIndex.o: Lib/Comparison.hpp Lib/Int.hpp
Indexing/ClauseVariantIndex.o: Kernel/LiteralSelector.hpp Kernel/Term.hpp
Indexing/ClauseVariantIndex.o: Lib/Portability.hpp Lib/XML.hpp
Indexing/ClauseVariantIndex.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/ClauseVariantIndex.o: Kernel/Renaming.hpp Lib/DHMap.hpp
Indexing/ClauseVariantIndex.o: Lib/VirtualIterator.hpp Kernel/MLVariant.hpp
Indexing/ClauseVariantIndex.o: Kernel/Term.hpp Indexing/LiteralMiniIndex.hpp
Indexing/ClauseVariantIndex.o: Lib/DArray.hpp Lib/Random.hpp
Indexing/ClauseVariantIndex.o: Kernel/Matcher.hpp Lib/BacktrackData.hpp
Indexing/ClauseVariantIndex.o: Lib/Hash.hpp
Indexing/ClauseVariantIndex.o: Indexing/LiteralSubstitutionTree.hpp
Indexing/ClauseVariantIndex.o: Indexing/LiteralIndexingStructure.hpp
Indexing/ClauseVariantIndex.o: Indexing/Index.hpp Lib/Event.hpp
Indexing/ClauseVariantIndex.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/ClauseVariantIndex.o: Saturation/ClauseContainer.hpp
Indexing/ClauseVariantIndex.o: Saturation/Limits.hpp
Indexing/ClauseVariantIndex.o: Indexing/ResultSubstitution.hpp
Indexing/ClauseVariantIndex.o: Indexing/SubstitutionTree.hpp Lib/SkipList.hpp
Indexing/ClauseVariantIndex.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/ClauseVariantIndex.o: Lib/ArrayMap.hpp Lib/DArray.hpp Lib/Array.hpp
Indexing/ClauseVariantIndex.o: Kernel/EGSubstitution.hpp
Indexing/ClauseVariantIndex.o: Kernel/RobSubstitution.hpp
Indexing/ClauseVariantIndex.o: Kernel/RobSubstitution.hpp Kernel/Renaming.hpp
Indexing/ClauseVariantIndex.o: Test/Output.hpp
Indexing/ClauseVariantIndex.o: Indexing/ClauseVariantIndex.hpp
Indexing/Index.o: Indexing/Index.hpp Forwards.hpp Config.hpp Lib/Event.hpp
Indexing/Index.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Indexing/Index.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/Index.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/SmartPtr.hpp
Indexing/Index.o: Lib/Exception.hpp Lib/VirtualIterator.hpp
Indexing/Index.o: Saturation/ClauseContainer.hpp Lib/Stack.hpp
Indexing/Index.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/Index.o: Lib/Portability.hpp Saturation/Limits.hpp Kernel/Clause.hpp
Indexing/Index.o: Lib/Allocator.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
Indexing/Index.o: Lib/DHMap.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Indexing/Index.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Indexing/Index.o: Lib/List.hpp Indexing/ResultSubstitution.hpp
Indexing/Index.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Indexing/IndexManager.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Indexing/IndexManager.o: Debug/Assertion.hpp
Indexing/IndexManager.o: Saturation/SaturationAlgorithm.hpp Forwards.hpp
Indexing/IndexManager.o: Config.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Indexing/IndexManager.o: Debug/Tracer.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
Indexing/IndexManager.o: Lib/DHMap.hpp Lib/Allocator.hpp Lib/Exception.hpp
Indexing/IndexManager.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Indexing/IndexManager.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Indexing/IndexManager.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
Indexing/IndexManager.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/IndexManager.o: Lib/Portability.hpp Kernel/Unit.hpp Lib/List.hpp
Indexing/IndexManager.o: Kernel/RCClauseStack.hpp Lib/DHMap.hpp Lib/Event.hpp
Indexing/IndexManager.o: Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Indexing/IndexManager.o: Indexing/Index.hpp Lib/VirtualIterator.hpp
Indexing/IndexManager.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
Indexing/IndexManager.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Indexing/IndexManager.o: Kernel/Term.hpp Inferences/InferenceEngine.hpp
Indexing/IndexManager.o: Inferences/PropositionalToBDDISE.hpp
Indexing/IndexManager.o: Inferences/InferenceEngine.hpp
Indexing/IndexManager.o: Saturation/SaturationResult.hpp Shell/Statistics.hpp
Indexing/IndexManager.o: Lib/Environment.hpp Saturation/BSplitter.hpp
Indexing/IndexManager.o: Lib/Array.hpp Saturation/Splitter.hpp
Indexing/IndexManager.o: Indexing/ClauseVariantIndex.hpp
Indexing/IndexManager.o: Indexing/LiteralIndex.hpp
Indexing/IndexManager.o: Indexing/LiteralSubstitutionTree.hpp
Indexing/IndexManager.o: Indexing/LiteralIndexingStructure.hpp
Indexing/IndexManager.o: Indexing/SubstitutionTree.hpp Lib/Comparison.hpp
Indexing/IndexManager.o: Lib/Int.hpp Lib/SkipList.hpp Lib/Random.hpp
Indexing/IndexManager.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/IndexManager.o: Lib/BacktrackData.hpp Lib/ArrayMap.hpp
Indexing/IndexManager.o: Lib/DArray.hpp Kernel/EGSubstitution.hpp
Indexing/IndexManager.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/IndexManager.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/IndexManager.o: Kernel/RobSubstitution.hpp
Indexing/IndexManager.o: Kernel/RobSubstitution.hpp Kernel/Renaming.hpp
Indexing/IndexManager.o: Test/Output.hpp Indexing/TermIndex.hpp
Indexing/IndexManager.o: Indexing/TermSubstitutionTree.hpp
Indexing/IndexManager.o: Indexing/TermIndexingStructure.hpp
Indexing/IndexManager.o: Indexing/IndexManager.hpp
Indexing/LiteralIndex.o: Kernel/Clause.hpp Forwards.hpp Config.hpp
Indexing/LiteralIndex.o: Lib/Allocator.hpp Debug/Assertion.hpp
Indexing/LiteralIndex.o: Debug/Tracer.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
Indexing/LiteralIndex.o: Lib/DHMap.hpp Lib/Allocator.hpp Lib/Exception.hpp
Indexing/LiteralIndex.o: Lib/LastCopyWatcher.hpp Lib/VirtualIterator.hpp
Indexing/LiteralIndex.o: Lib/Reflection.hpp Lib/Metaiterators.hpp
Indexing/LiteralIndex.o: Lib/List.hpp Lib/Set.hpp Lib/TimeCounter.hpp
Indexing/LiteralIndex.o: Lib/Reflection.hpp Lib/Stack.hpp
Indexing/LiteralIndex.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/LiteralIndex.o: Lib/Portability.hpp Kernel/Unit.hpp Lib/List.hpp
Indexing/LiteralIndex.o: Kernel/LiteralComparators.hpp Lib/Comparison.hpp
Indexing/LiteralIndex.o: Lib/Int.hpp Kernel/LiteralSelector.hpp
Indexing/LiteralIndex.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/LiteralIndex.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/LiteralIndex.o: Kernel/Renaming.hpp Lib/DHMap.hpp
Indexing/LiteralIndex.o: Lib/VirtualIterator.hpp Kernel/Matcher.hpp
Indexing/LiteralIndex.o: Lib/BacktrackData.hpp Lib/Hash.hpp Kernel/Term.hpp
Indexing/LiteralIndex.o: Kernel/MLVariant.hpp Kernel/Ordering.hpp
Indexing/LiteralIndex.o: Lib/SmartPtr.hpp
Indexing/LiteralIndex.o: Indexing/LiteralIndexingStructure.hpp
Indexing/LiteralIndex.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/LiteralIndex.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
Indexing/LiteralIndex.o: Saturation/Limits.hpp
Indexing/LiteralIndex.o: Indexing/ResultSubstitution.hpp
Indexing/LiteralIndex.o: Indexing/LiteralSubstitutionTree.hpp
Indexing/LiteralIndex.o: Indexing/SubstitutionTree.hpp Lib/SkipList.hpp
Indexing/LiteralIndex.o: Lib/Random.hpp Lib/BinaryHeap.hpp
Indexing/LiteralIndex.o: Lib/Metaiterators.hpp Lib/ArrayMap.hpp
Indexing/LiteralIndex.o: Lib/DArray.hpp Lib/Array.hpp
Indexing/LiteralIndex.o: Kernel/EGSubstitution.hpp Kernel/RobSubstitution.hpp
Indexing/LiteralIndex.o: Kernel/RobSubstitution.hpp Kernel/Renaming.hpp
Indexing/LiteralIndex.o: Test/Output.hpp Indexing/LiteralIndex.hpp
Indexing/LiteralMiniIndex.o: Lib/Allocator.hpp Debug/Assertion.hpp
Indexing/LiteralMiniIndex.o: Debug/Tracer.hpp Indexing/LiteralMiniIndex.hpp
Indexing/LiteralMiniIndex.o: Forwards.hpp Config.hpp Lib/DArray.hpp
Indexing/LiteralMiniIndex.o: Lib/Allocator.hpp Lib/Comparison.hpp
Indexing/LiteralMiniIndex.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Indexing/LiteralMiniIndex.o: Lib/Random.hpp Lib/Reflection.hpp
Indexing/LiteralMiniIndex.o: Lib/VirtualIterator.hpp Kernel/Clause.hpp
Indexing/LiteralMiniIndex.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Indexing/LiteralMiniIndex.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Indexing/LiteralMiniIndex.o: Lib/TimeCounter.hpp Lib/Reflection.hpp
Indexing/LiteralMiniIndex.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/LiteralMiniIndex.o: Lib/Portability.hpp Kernel/Unit.hpp Lib/List.hpp
Indexing/LiteralMiniIndex.o: Kernel/Matcher.hpp Lib/BacktrackData.hpp
Indexing/LiteralMiniIndex.o: Lib/DHMap.hpp Lib/Hash.hpp
Indexing/LiteralMiniIndex.o: Lib/VirtualIterator.hpp Kernel/Term.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Environment.hpp Forwards.hpp
Indexing/LiteralSubstitutionTree.o: Config.hpp Lib/Exception.hpp
Indexing/LiteralSubstitutionTree.o: Lib/LastCopyWatcher.hpp
Indexing/LiteralSubstitutionTree.o: Debug/Assertion.hpp Lib/Metaiterators.hpp
Indexing/LiteralSubstitutionTree.o: Lib/List.hpp Lib/Allocator.hpp
Indexing/LiteralSubstitutionTree.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Reflection.hpp Lib/Set.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Hash.hpp Lib/TimeCounter.hpp
Indexing/LiteralSubstitutionTree.o: Lib/TimeCounter.hpp Kernel/Signature.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Allocator.hpp Lib/Stack.hpp
Indexing/LiteralSubstitutionTree.o: Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Map.hpp Kernel/Term.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/LiteralSubstitutionTree.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/LiteralIndexingStructure.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/Index.hpp Lib/Event.hpp
Indexing/LiteralSubstitutionTree.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/LiteralSubstitutionTree.o: Lib/VirtualIterator.hpp
Indexing/LiteralSubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/LiteralSubstitutionTree.o: Saturation/Limits.hpp Kernel/Clause.hpp
Indexing/LiteralSubstitutionTree.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Reflection.hpp Kernel/Unit.hpp
Indexing/LiteralSubstitutionTree.o: Lib/List.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/ResultSubstitution.hpp
Indexing/LiteralSubstitutionTree.o: Lib/SmartPtr.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/SubstitutionTree.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Comparison.hpp Lib/Int.hpp
Indexing/LiteralSubstitutionTree.o: Lib/SkipList.hpp Lib/Random.hpp
Indexing/LiteralSubstitutionTree.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/LiteralSubstitutionTree.o: Lib/BacktrackData.hpp Lib/ArrayMap.hpp
Indexing/LiteralSubstitutionTree.o: Lib/DArray.hpp Lib/Array.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/EGSubstitution.hpp Lib/DHMap.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/Term.hpp Lib/Portability.hpp
Indexing/LiteralSubstitutionTree.o: Lib/XML.hpp Kernel/MatchTag.hpp
Indexing/LiteralSubstitutionTree.o: Lib/BitUtils.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/RobSubstitution.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/RobSubstitution.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/Renaming.hpp Test/Output.hpp
Indexing/ResultSubstitution.o: Kernel/RobSubstitution.hpp
Indexing/ResultSubstitution.o: Kernel/EGSubstitution.hpp Forwards.hpp
Indexing/ResultSubstitution.o: Config.hpp Lib/DHMap.hpp Lib/Stack.hpp
Indexing/ResultSubstitution.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/ResultSubstitution.o: Lib/Allocator.hpp Lib/BacktrackData.hpp
Indexing/ResultSubstitution.o: Lib/List.hpp Lib/VirtualIterator.hpp
Indexing/ResultSubstitution.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Indexing/ResultSubstitution.o: Lib/Reflection.hpp Lib/Int.hpp
Indexing/ResultSubstitution.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/ResultSubstitution.o: Lib/BacktrackData.hpp Kernel/Term.hpp
Indexing/ResultSubstitution.o: Lib/Allocator.hpp Lib/Portability.hpp
Indexing/ResultSubstitution.o: Lib/XML.hpp Lib/Comparison.hpp
Indexing/ResultSubstitution.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Indexing/ResultSubstitution.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp
Indexing/ResultSubstitution.o: Lib/BitUtils.hpp Kernel/RobSubstitution.hpp
Indexing/ResultSubstitution.o: Indexing/ResultSubstitution.hpp
Indexing/ResultSubstitution.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Indexing/SubstitutionTree.o: Kernel/Matcher.hpp Forwards.hpp Config.hpp
Indexing/SubstitutionTree.o: Lib/BacktrackData.hpp Lib/DHMap.hpp Lib/Hash.hpp
Indexing/SubstitutionTree.o: Lib/Stack.hpp Debug/Assertion.hpp
Indexing/SubstitutionTree.o: Debug/Tracer.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree.o: Lib/BacktrackData.hpp Lib/List.hpp
Indexing/SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/SubstitutionTree.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp
Indexing/SubstitutionTree.o: Lib/Int.hpp Lib/Comparison.hpp
Indexing/SubstitutionTree.o: Lib/Portability.hpp Lib/VirtualIterator.hpp
Indexing/SubstitutionTree.o: Kernel/Term.hpp Kernel/Renaming.hpp
Indexing/SubstitutionTree.o: Kernel/SubstHelper.hpp Lib/DArray.hpp
Indexing/SubstitutionTree.o: Lib/Random.hpp Kernel/Term.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree.o: Lib/Portability.hpp Lib/XML.hpp
Indexing/SubstitutionTree.o: Lib/Comparison.hpp Lib/Metaiterators.hpp
Indexing/SubstitutionTree.o: Lib/Set.hpp Lib/Hash.hpp Lib/TimeCounter.hpp
Indexing/SubstitutionTree.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/SubstitutionTree.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/SubstitutionTree.o: Lib/Environment.hpp Lib/Recycler.hpp
Indexing/SubstitutionTree.o: Lib/Stack.hpp Lib/DArray.hpp Lib/DHMultiset.hpp
Indexing/SubstitutionTree.o: Lib/DHMap.hpp Indexing/TermSharing.hpp
Indexing/SubstitutionTree.o: Lib/Set.hpp Kernel/Signature.hpp Lib/Map.hpp
Indexing/SubstitutionTree.o: Lib/Int.hpp Test/Output.hpp
Indexing/SubstitutionTree.o: Indexing/SubstitutionTree.hpp Lib/List.hpp
Indexing/SubstitutionTree.o: Lib/SkipList.hpp Lib/ArrayMap.hpp Lib/Array.hpp
Indexing/SubstitutionTree.o: Kernel/EGSubstitution.hpp
Indexing/SubstitutionTree.o: Kernel/RobSubstitution.hpp
Indexing/SubstitutionTree.o: Kernel/RobSubstitution.hpp Kernel/Clause.hpp
Indexing/SubstitutionTree.o: Lib/InverseLookup.hpp Lib/Reflection.hpp
Indexing/SubstitutionTree.o: Kernel/Unit.hpp Indexing/Index.hpp Lib/Event.hpp
Indexing/SubstitutionTree.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/SubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/SubstitutionTree.o: Saturation/Limits.hpp
Indexing/SubstitutionTree.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/DHMultiset.hpp Debug/Assertion.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Hash.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/VirtualIterator.hpp Forwards.hpp
Indexing/SubstitutionTree_Nodes.o: Config.hpp Lib/Reflection.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Portability.hpp Lib/Exception.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/List.hpp Lib/Metaiterators.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/List.hpp Lib/Set.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/TimeCounter.hpp Lib/SkipList.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Comparison.hpp Lib/Random.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/VirtualIterator.hpp Indexing/Index.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/SubstitutionTree_Nodes.o: Saturation/ClauseContainer.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Stack.hpp Saturation/Limits.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/Clause.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/InverseLookup.hpp Lib/Reflection.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/Unit.hpp
Indexing/SubstitutionTree_Nodes.o: Indexing/ResultSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Indexing/SubstitutionTree_Nodes.o: Indexing/SubstitutionTree.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Comparison.hpp Lib/Int.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BacktrackData.hpp Lib/ArrayMap.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/DArray.hpp Lib/Array.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/EGSubstitution.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/Term.hpp Lib/Portability.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/XML.hpp Kernel/MatchTag.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BitUtils.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/RobSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/RobSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/Renaming.hpp Test/Output.hpp
Indexing/TermIndex.o: Kernel/Clause.hpp Forwards.hpp Config.hpp
Indexing/TermIndex.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/TermIndex.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Indexing/TermIndex.o: Lib/Allocator.hpp Lib/Exception.hpp
Indexing/TermIndex.o: Lib/LastCopyWatcher.hpp Lib/VirtualIterator.hpp
Indexing/TermIndex.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Indexing/TermIndex.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Indexing/TermIndex.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/TermIndex.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Indexing/TermIndex.o: Lib/List.hpp Kernel/Term.hpp Kernel/Ordering.hpp
Indexing/TermIndex.o: Lib/SmartPtr.hpp Kernel/EqHelper.hpp
Indexing/TermIndex.o: Lib/VirtualIterator.hpp Lib/PairUtils.hpp
Indexing/TermIndex.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Indexing/TermIndex.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/TermIndex.o: Lib/Comparison.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/TermIndex.o: Indexing/TermIndexingStructure.hpp Indexing/Index.hpp
Indexing/TermIndex.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/TermIndex.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
Indexing/TermIndex.o: Indexing/ResultSubstitution.hpp Indexing/TermIndex.hpp
Indexing/TermSharing.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Indexing/TermSharing.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Indexing/TermSharing.o: Debug/Assertion.hpp Kernel/Signature.hpp
Indexing/TermSharing.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Stack.hpp
Indexing/TermSharing.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Indexing/TermSharing.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Indexing/TermSharing.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Indexing/TermSharing.o: Lib/Map.hpp Lib/Hash.hpp Kernel/Term.hpp
Indexing/TermSharing.o: Indexing/TermSharing.hpp Lib/Set.hpp
Indexing/TermSubstitutionTree.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Indexing/TermSubstitutionTree.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Indexing/TermSubstitutionTree.o: Debug/Assertion.hpp Lib/Metaiterators.hpp
Indexing/TermSubstitutionTree.o: Lib/List.hpp Lib/Allocator.hpp
Indexing/TermSubstitutionTree.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Indexing/TermSubstitutionTree.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Indexing/TermSubstitutionTree.o: Lib/TimeCounter.hpp Lib/Random.hpp
Indexing/TermSubstitutionTree.o: Lib/SmartPtr.hpp Lib/TimeCounter.hpp
Indexing/TermSubstitutionTree.o: Kernel/Signature.hpp Lib/Allocator.hpp
Indexing/TermSubstitutionTree.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Indexing/TermSubstitutionTree.o: Lib/Int.hpp Lib/Comparison.hpp
Indexing/TermSubstitutionTree.o: Lib/Portability.hpp Lib/Map.hpp
Indexing/TermSubstitutionTree.o: Kernel/Term.hpp Kernel/Curryfier.hpp
Indexing/TermSubstitutionTree.o: Lib/DHMap.hpp Lib/DArray.hpp Lib/Random.hpp
Indexing/TermSubstitutionTree.o: Lib/ArrayMap.hpp Lib/DArray.hpp
Indexing/TermSubstitutionTree.o: Indexing/TermSharing.hpp Lib/Set.hpp
Indexing/TermSubstitutionTree.o: Kernel/Term.hpp Lib/Portability.hpp
Indexing/TermSubstitutionTree.o: Lib/XML.hpp Lib/Comparison.hpp
Indexing/TermSubstitutionTree.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/TermSubstitutionTree.o: Kernel/Signature.hpp
Indexing/TermSubstitutionTree.o: Indexing/TermSubstitutionTree.hpp
Indexing/TermSubstitutionTree.o: Kernel/Renaming.hpp Lib/SkipList.hpp
Indexing/TermSubstitutionTree.o: Indexing/Index.hpp Lib/Event.hpp
Indexing/TermSubstitutionTree.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/TermSubstitutionTree.o: Lib/VirtualIterator.hpp
Indexing/TermSubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/TermSubstitutionTree.o: Saturation/Limits.hpp Kernel/Clause.hpp
Indexing/TermSubstitutionTree.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Indexing/TermSubstitutionTree.o: Lib/Reflection.hpp Kernel/Unit.hpp
Indexing/TermSubstitutionTree.o: Lib/List.hpp Indexing/ResultSubstitution.hpp
Indexing/TermSubstitutionTree.o: Indexing/TermIndexingStructure.hpp
Indexing/TermSubstitutionTree.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/TermSubstitutionTree.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/TermSubstitutionTree.o: Lib/BacktrackData.hpp Lib/Array.hpp
Indexing/TermSubstitutionTree.o: Kernel/EGSubstitution.hpp
Indexing/TermSubstitutionTree.o: Kernel/RobSubstitution.hpp
Indexing/TermSubstitutionTree.o: Kernel/RobSubstitution.hpp Test/Output.hpp
Inferences/BackwardDemodulation.o: Lib/DHMultiset.hpp Debug/Assertion.hpp
Inferences/BackwardDemodulation.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/BackwardDemodulation.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Inferences/BackwardDemodulation.o: Lib/Hash.hpp Lib/DHMap.hpp
Inferences/BackwardDemodulation.o: Lib/VirtualIterator.hpp Forwards.hpp
Inferences/BackwardDemodulation.o: Config.hpp Lib/Reflection.hpp
Inferences/BackwardDemodulation.o: Lib/Portability.hpp Lib/Environment.hpp
Inferences/BackwardDemodulation.o: Lib/Int.hpp Lib/Comparison.hpp
Inferences/BackwardDemodulation.o: Lib/List.hpp Lib/Metaiterators.hpp
Inferences/BackwardDemodulation.o: Lib/List.hpp Lib/Set.hpp
Inferences/BackwardDemodulation.o: Lib/TimeCounter.hpp Lib/TimeCounter.hpp
Inferences/BackwardDemodulation.o: Lib/VirtualIterator.hpp Kernel/Term.hpp
Inferences/BackwardDemodulation.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/BackwardDemodulation.o: Lib/InverseLookup.hpp Lib/Reflection.hpp
Inferences/BackwardDemodulation.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Inferences/BackwardDemodulation.o: Lib/Int.hpp Kernel/Unit.hpp
Inferences/BackwardDemodulation.o: Kernel/EqHelper.hpp Lib/PairUtils.hpp
Inferences/BackwardDemodulation.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/BackwardDemodulation.o: Kernel/Term.hpp Lib/Portability.hpp
Inferences/BackwardDemodulation.o: Lib/XML.hpp Lib/Comparison.hpp
Inferences/BackwardDemodulation.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/BackwardDemodulation.o: Kernel/Renaming.hpp Kernel/Ordering.hpp
Inferences/BackwardDemodulation.o: Lib/SmartPtr.hpp Kernel/Inference.hpp
Inferences/BackwardDemodulation.o: Kernel/Unit.hpp Indexing/Index.hpp
Inferences/BackwardDemodulation.o: Lib/Event.hpp Lib/SmartPtr.hpp
Inferences/BackwardDemodulation.o: Lib/Exception.hpp
Inferences/BackwardDemodulation.o: Saturation/ClauseContainer.hpp
Inferences/BackwardDemodulation.o: Saturation/Limits.hpp
Inferences/BackwardDemodulation.o: Indexing/ResultSubstitution.hpp
Inferences/BackwardDemodulation.o: Indexing/TermIndex.hpp Indexing/Index.hpp
Inferences/BackwardDemodulation.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Inferences/BackwardDemodulation.o: Saturation/SaturationAlgorithm.hpp
Inferences/BackwardDemodulation.o: Kernel/RCClauseStack.hpp
Inferences/BackwardDemodulation.o: Inferences/InferenceEngine.hpp
Inferences/BackwardDemodulation.o: Inferences/PropositionalToBDDISE.hpp
Inferences/BackwardDemodulation.o: Inferences/InferenceEngine.hpp
Inferences/BackwardDemodulation.o: Saturation/SaturationResult.hpp
Inferences/BackwardDemodulation.o: Shell/Statistics.hpp
Inferences/BackwardDemodulation.o: Saturation/BSplitter.hpp Lib/Array.hpp
Inferences/BackwardDemodulation.o: Saturation/Splitter.hpp
Inferences/BackwardDemodulation.o: Indexing/ClauseVariantIndex.hpp
Inferences/BackwardDemodulation.o: Inferences/BackwardDemodulation.hpp
Inferences/BinaryResolution.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Inferences/BinaryResolution.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Inferences/BinaryResolution.o: Debug/Assertion.hpp Lib/Int.hpp
Inferences/BinaryResolution.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/BinaryResolution.o: Lib/Metaiterators.hpp Lib/List.hpp
Inferences/BinaryResolution.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/BinaryResolution.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Inferences/BinaryResolution.o: Lib/Set.hpp Lib/Hash.hpp Lib/TimeCounter.hpp
Inferences/BinaryResolution.o: Lib/PairUtils.hpp Lib/Metaiterators.hpp
Inferences/BinaryResolution.o: Lib/Metaarrays.hpp Lib/VirtualIterator.hpp
Inferences/BinaryResolution.o: Shell/Statistics.hpp Kernel/Clause.hpp
Inferences/BinaryResolution.o: Lib/Allocator.hpp Lib/InverseLookup.hpp
Inferences/BinaryResolution.o: Lib/DHMap.hpp Lib/Reflection.hpp Lib/Stack.hpp
Inferences/BinaryResolution.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/BinaryResolution.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Unit.hpp
Inferences/BinaryResolution.o: Kernel/Inference.hpp Indexing/Index.hpp
Inferences/BinaryResolution.o: Lib/Event.hpp Lib/SmartPtr.hpp
Inferences/BinaryResolution.o: Lib/Exception.hpp
Inferences/BinaryResolution.o: Saturation/ClauseContainer.hpp
Inferences/BinaryResolution.o: Saturation/Limits.hpp
Inferences/BinaryResolution.o: Indexing/ResultSubstitution.hpp
Inferences/BinaryResolution.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Inferences/BinaryResolution.o: Indexing/LiteralIndex.hpp Lib/DHMap.hpp
Inferences/BinaryResolution.o: Indexing/Index.hpp Indexing/IndexManager.hpp
Inferences/BinaryResolution.o: Saturation/SaturationAlgorithm.hpp
Inferences/BinaryResolution.o: Kernel/RCClauseStack.hpp
Inferences/BinaryResolution.o: Inferences/InferenceEngine.hpp
Inferences/BinaryResolution.o: Inferences/PropositionalToBDDISE.hpp
Inferences/BinaryResolution.o: Inferences/InferenceEngine.hpp
Inferences/BinaryResolution.o: Saturation/SaturationResult.hpp
Inferences/BinaryResolution.o: Saturation/BSplitter.hpp Lib/Array.hpp
Inferences/BinaryResolution.o: Saturation/Splitter.hpp
Inferences/BinaryResolution.o: Indexing/ClauseVariantIndex.hpp
Inferences/BinaryResolution.o: Inferences/BinaryResolution.hpp
Inferences/Condensation.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp
Inferences/Condensation.o: Forwards.hpp Config.hpp Lib/List.hpp
Inferences/Condensation.o: Debug/Assertion.hpp Lib/Allocator.hpp
Inferences/Condensation.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Inferences/Condensation.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Inferences/Condensation.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Inferences/Condensation.o: Lib/TimeCounter.hpp Lib/Int.hpp Lib/Comparison.hpp
Inferences/Condensation.o: Lib/Portability.hpp Lib/DArray.hpp Lib/Random.hpp
Inferences/Condensation.o: Kernel/Term.hpp Kernel/Clause.hpp
Inferences/Condensation.o: Lib/Allocator.hpp Lib/InverseLookup.hpp
Inferences/Condensation.o: Lib/DHMap.hpp Lib/Reflection.hpp Lib/Stack.hpp
Inferences/Condensation.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Unit.hpp
Inferences/Condensation.o: Lib/List.hpp Kernel/MLMatcher.hpp
Inferences/Condensation.o: Kernel/Ordering.hpp Lib/SmartPtr.hpp
Inferences/Condensation.o: Kernel/Inference.hpp Kernel/Unit.hpp
Inferences/Condensation.o: Kernel/Renaming.hpp Kernel/Matcher.hpp
Inferences/Condensation.o: Lib/BacktrackData.hpp Lib/DHMap.hpp Lib/Hash.hpp
Inferences/Condensation.o: Kernel/RobSubstitution.hpp
Inferences/Condensation.o: Indexing/LiteralMiniIndex.hpp
Inferences/Condensation.o: Saturation/SaturationAlgorithm.hpp
Inferences/Condensation.o: Kernel/RCClauseStack.hpp Lib/Event.hpp
Inferences/Condensation.o: Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Inferences/Condensation.o: Indexing/Index.hpp Lib/Exception.hpp
Inferences/Condensation.o: Saturation/ClauseContainer.hpp
Inferences/Condensation.o: Saturation/Limits.hpp
Inferences/Condensation.o: Indexing/ResultSubstitution.hpp
Inferences/Condensation.o: Inferences/InferenceEngine.hpp
Inferences/Condensation.o: Inferences/PropositionalToBDDISE.hpp
Inferences/Condensation.o: Inferences/InferenceEngine.hpp
Inferences/Condensation.o: Saturation/SaturationResult.hpp
Inferences/Condensation.o: Shell/Statistics.hpp Lib/Environment.hpp
Inferences/Condensation.o: Saturation/BSplitter.hpp Lib/Array.hpp
Inferences/Condensation.o: Saturation/Splitter.hpp
Inferences/Condensation.o: Indexing/ClauseVariantIndex.hpp
Inferences/Condensation.o: Inferences/Condensation.hpp Indexing/TermIndex.hpp
Inferences/EqualityFactoring.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp
Inferences/EqualityFactoring.o: Forwards.hpp Config.hpp Lib/List.hpp
Inferences/EqualityFactoring.o: Debug/Assertion.hpp Lib/Allocator.hpp
Inferences/EqualityFactoring.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Inferences/EqualityFactoring.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Inferences/EqualityFactoring.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Inferences/EqualityFactoring.o: Lib/TimeCounter.hpp Lib/PairUtils.hpp
Inferences/EqualityFactoring.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/EqualityFactoring.o: Lib/Environment.hpp Shell/Statistics.hpp
Inferences/EqualityFactoring.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/EqualityFactoring.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/EqualityFactoring.o: Lib/Reflection.hpp Lib/Stack.hpp
Inferences/EqualityFactoring.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/EqualityFactoring.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/EqualityFactoring.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Unit.hpp
Inferences/EqualityFactoring.o: Kernel/Inference.hpp
Inferences/EqualityFactoring.o: Kernel/RobSubstitution.hpp
Inferences/EqualityFactoring.o: Kernel/EqHelper.hpp Kernel/Term.hpp
Inferences/EqualityFactoring.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/EqualityFactoring.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Inferences/EqualityFactoring.o: Lib/BitUtils.hpp Kernel/Ordering.hpp
Inferences/EqualityFactoring.o: Lib/SmartPtr.hpp
Inferences/EqualityFactoring.o: Inferences/EqualityFactoring.hpp
Inferences/EqualityFactoring.o: Inferences/InferenceEngine.hpp
Inferences/EqualityResolution.o: Lib/VirtualIterator.hpp
Inferences/EqualityResolution.o: Lib/Metaiterators.hpp Forwards.hpp
Inferences/EqualityResolution.o: Config.hpp Lib/List.hpp Debug/Assertion.hpp
Inferences/EqualityResolution.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/EqualityResolution.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/EqualityResolution.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp
Inferences/EqualityResolution.o: Lib/Set.hpp Lib/Hash.hpp Lib/TimeCounter.hpp
Inferences/EqualityResolution.o: Lib/PairUtils.hpp Lib/Metaiterators.hpp
Inferences/EqualityResolution.o: Lib/Metaarrays.hpp Lib/Environment.hpp
Inferences/EqualityResolution.o: Shell/Statistics.hpp Kernel/Clause.hpp
Inferences/EqualityResolution.o: Lib/Allocator.hpp Lib/InverseLookup.hpp
Inferences/EqualityResolution.o: Lib/DHMap.hpp Lib/Reflection.hpp
Inferences/EqualityResolution.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Inferences/EqualityResolution.o: Lib/Int.hpp Lib/Comparison.hpp
Inferences/EqualityResolution.o: Lib/Portability.hpp Kernel/Unit.hpp
Inferences/EqualityResolution.o: Lib/List.hpp Kernel/Unit.hpp
Inferences/EqualityResolution.o: Kernel/Inference.hpp
Inferences/EqualityResolution.o: Kernel/RobSubstitution.hpp
Inferences/EqualityResolution.o: Kernel/EqHelper.hpp Kernel/Term.hpp
Inferences/EqualityResolution.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/EqualityResolution.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Inferences/EqualityResolution.o: Lib/BitUtils.hpp Kernel/Ordering.hpp
Inferences/EqualityResolution.o: Lib/SmartPtr.hpp
Inferences/EqualityResolution.o: Inferences/EqualityResolution.hpp
Inferences/EqualityResolution.o: Inferences/InferenceEngine.hpp
Inferences/Factoring.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Inferences/Factoring.o: Debug/Assertion.hpp Lib/VirtualIterator.hpp
Inferences/Factoring.o: Lib/Metaiterators.hpp Forwards.hpp Config.hpp
Inferences/Factoring.o: Lib/List.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/Factoring.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/Factoring.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp
Inferences/Factoring.o: Lib/Set.hpp Lib/Hash.hpp Lib/TimeCounter.hpp
Inferences/Factoring.o: Lib/Comparison.hpp Lib/PairUtils.hpp
Inferences/Factoring.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/Factoring.o: Lib/Environment.hpp Shell/Statistics.hpp
Inferences/Factoring.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/Factoring.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/Factoring.o: Lib/Reflection.hpp Lib/Stack.hpp
Inferences/Factoring.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Unit.hpp
Inferences/Factoring.o: Lib/List.hpp Kernel/Unit.hpp Kernel/Inference.hpp
Inferences/Factoring.o: Kernel/LiteralSelector.hpp Kernel/Term.hpp
Inferences/Factoring.o: Lib/Portability.hpp Lib/XML.hpp Kernel/MatchTag.hpp
Inferences/Factoring.o: Lib/BitUtils.hpp Kernel/RobSubstitution.hpp
Inferences/Factoring.o: Inferences/Factoring.hpp
Inferences/Factoring.o: Inferences/InferenceEngine.hpp
Inferences/ForwardDemodulation.o: Lib/Int.hpp Lib/Comparison.hpp
Inferences/ForwardDemodulation.o: Lib/Portability.hpp Debug/Assertion.hpp
Inferences/ForwardDemodulation.o: Lib/Metaiterators.hpp Forwards.hpp
Inferences/ForwardDemodulation.o: Config.hpp Lib/List.hpp Lib/Allocator.hpp
Inferences/ForwardDemodulation.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Inferences/ForwardDemodulation.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Inferences/ForwardDemodulation.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Inferences/ForwardDemodulation.o: Lib/TimeCounter.hpp Lib/TimeCounter.hpp
Inferences/ForwardDemodulation.o: Lib/VirtualIterator.hpp Kernel/Term.hpp
Inferences/ForwardDemodulation.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/ForwardDemodulation.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/ForwardDemodulation.o: Lib/Reflection.hpp Lib/Stack.hpp
Inferences/ForwardDemodulation.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/ForwardDemodulation.o: Kernel/Unit.hpp Lib/List.hpp
Inferences/ForwardDemodulation.o: Kernel/EqHelper.hpp Lib/PairUtils.hpp
Inferences/ForwardDemodulation.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/ForwardDemodulation.o: Kernel/Term.hpp Lib/Portability.hpp
Inferences/ForwardDemodulation.o: Lib/XML.hpp Lib/Comparison.hpp
Inferences/ForwardDemodulation.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/ForwardDemodulation.o: Kernel/Ordering.hpp Lib/SmartPtr.hpp
Inferences/ForwardDemodulation.o: Kernel/Inference.hpp Kernel/Unit.hpp
Inferences/ForwardDemodulation.o: Kernel/Renaming.hpp Indexing/Index.hpp
Inferences/ForwardDemodulation.o: Lib/Event.hpp Lib/SmartPtr.hpp
Inferences/ForwardDemodulation.o: Lib/Exception.hpp
Inferences/ForwardDemodulation.o: Saturation/ClauseContainer.hpp
Inferences/ForwardDemodulation.o: Saturation/Limits.hpp
Inferences/ForwardDemodulation.o: Indexing/ResultSubstitution.hpp
Inferences/ForwardDemodulation.o: Indexing/TermIndex.hpp Indexing/Index.hpp
Inferences/ForwardDemodulation.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Inferences/ForwardDemodulation.o: Saturation/SaturationAlgorithm.hpp
Inferences/ForwardDemodulation.o: Kernel/RCClauseStack.hpp
Inferences/ForwardDemodulation.o: Inferences/InferenceEngine.hpp
Inferences/ForwardDemodulation.o: Inferences/PropositionalToBDDISE.hpp
Inferences/ForwardDemodulation.o: Inferences/InferenceEngine.hpp
Inferences/ForwardDemodulation.o: Saturation/SaturationResult.hpp
Inferences/ForwardDemodulation.o: Shell/Statistics.hpp Lib/Environment.hpp
Inferences/ForwardDemodulation.o: Saturation/BSplitter.hpp Lib/Array.hpp
Inferences/ForwardDemodulation.o: Saturation/Splitter.hpp
Inferences/ForwardDemodulation.o: Indexing/ClauseVariantIndex.hpp
Inferences/ForwardDemodulation.o: Lib/Timer.hpp
Inferences/ForwardDemodulation.o: Inferences/ForwardDemodulation.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Int.hpp Lib/Comparison.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Portability.hpp Debug/Assertion.hpp
Inferences/ForwardLiteralRewriting.o: Kernel/Inference.hpp Kernel/Unit.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/ForwardLiteralRewriting.o: Kernel/Ordering.hpp Forwards.hpp
Inferences/ForwardLiteralRewriting.o: Config.hpp Lib/SmartPtr.hpp
Inferences/ForwardLiteralRewriting.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Inferences/ForwardLiteralRewriting.o: Indexing/Index.hpp Lib/Event.hpp
Inferences/ForwardLiteralRewriting.o: Lib/List.hpp Lib/Allocator.hpp
Inferences/ForwardLiteralRewriting.o: Lib/VirtualIterator.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Exception.hpp
Inferences/ForwardLiteralRewriting.o: Lib/LastCopyWatcher.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Reflection.hpp Lib/SmartPtr.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Exception.hpp
Inferences/ForwardLiteralRewriting.o: Lib/VirtualIterator.hpp
Inferences/ForwardLiteralRewriting.o: Saturation/ClauseContainer.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Int.hpp Saturation/Limits.hpp
Inferences/ForwardLiteralRewriting.o: Kernel/Clause.hpp Lib/InverseLookup.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Hash.hpp Lib/DHMap.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Metaiterators.hpp Lib/Set.hpp
Inferences/ForwardLiteralRewriting.o: Lib/TimeCounter.hpp Lib/Reflection.hpp
Inferences/ForwardLiteralRewriting.o: Kernel/Unit.hpp Lib/List.hpp
Inferences/ForwardLiteralRewriting.o: Indexing/ResultSubstitution.hpp
Inferences/ForwardLiteralRewriting.o: Kernel/Term.hpp
Inferences/ForwardLiteralRewriting.o: Saturation/SaturationAlgorithm.hpp
Inferences/ForwardLiteralRewriting.o: Kernel/RCClauseStack.hpp
Inferences/ForwardLiteralRewriting.o: Inferences/InferenceEngine.hpp
Inferences/ForwardLiteralRewriting.o: Inferences/PropositionalToBDDISE.hpp
Inferences/ForwardLiteralRewriting.o: Inferences/InferenceEngine.hpp
Inferences/ForwardLiteralRewriting.o: Saturation/SaturationResult.hpp
Inferences/ForwardLiteralRewriting.o: Shell/Statistics.hpp
Inferences/ForwardLiteralRewriting.o: Lib/Environment.hpp
Inferences/ForwardLiteralRewriting.o: Saturation/BSplitter.hpp Lib/Array.hpp
Inferences/ForwardLiteralRewriting.o: Saturation/Splitter.hpp
Inferences/ForwardLiteralRewriting.o: Indexing/ClauseVariantIndex.hpp
Inferences/ForwardLiteralRewriting.o: Inferences/ForwardLiteralRewriting.hpp
Inferences/ForwardLiteralRewriting.o: Indexing/LiteralIndex.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/VirtualIterator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/DArray.hpp Forwards.hpp
Inferences/ForwardSubsumptionAndResolution.o: Config.hpp Debug/Assertion.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Allocator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Debug/Tracer.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Comparison.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Exception.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/LastCopyWatcher.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Random.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Reflection.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/VirtualIterator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/List.hpp Lib/Comparison.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Metaiterators.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/List.hpp Lib/Set.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Hash.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/TimeCounter.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/TimeCounter.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Term.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Clause.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Allocator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/InverseLookup.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/DHMap.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Reflection.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Stack.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/BacktrackData.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Int.hpp Lib/Portability.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Unit.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Inference.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Unit.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Matcher.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/BacktrackData.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/DHMap.hpp Lib/Hash.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/MLMatcher.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/Index.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Event.hpp Lib/SmartPtr.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Exception.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/ClauseContainer.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/Limits.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/ResultSubstitution.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/SmartPtr.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/LiteralIndex.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/Index.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/LiteralMiniIndex.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/IndexManager.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/SaturationAlgorithm.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/RCClauseStack.hpp
Inferences/ForwardSubsumptionAndResolution.o: Inferences/InferenceEngine.hpp
Inferences/ForwardSubsumptionAndResolution.o: Inferences/PropositionalToBDDISE.hpp
Inferences/ForwardSubsumptionAndResolution.o: Inferences/InferenceEngine.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/SaturationResult.hpp
Inferences/ForwardSubsumptionAndResolution.o: Shell/Statistics.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Environment.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/BSplitter.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Array.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/Splitter.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/ClauseVariantIndex.hpp
Inferences/ForwardSubsumptionAndResolution.o: Inferences/ForwardSubsumptionAndResolution.hpp
Inferences/InferenceEngine.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Inferences/InferenceEngine.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Inferences/InferenceEngine.o: Debug/Assertion.hpp Lib/Random.hpp
Inferences/InferenceEngine.o: Lib/DArray.hpp Lib/Allocator.hpp
Inferences/InferenceEngine.o: Debug/Tracer.hpp Lib/Comparison.hpp
Inferences/InferenceEngine.o: Lib/Random.hpp Lib/Reflection.hpp
Inferences/InferenceEngine.o: Lib/VirtualIterator.hpp Lib/List.hpp
Inferences/InferenceEngine.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Inferences/InferenceEngine.o: Lib/Hash.hpp Lib/TimeCounter.hpp
Inferences/InferenceEngine.o: Kernel/Term.hpp Kernel/Clause.hpp
Inferences/InferenceEngine.o: Lib/Allocator.hpp Lib/InverseLookup.hpp
Inferences/InferenceEngine.o: Lib/DHMap.hpp Lib/Reflection.hpp Lib/Stack.hpp
Inferences/InferenceEngine.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/InferenceEngine.o: Lib/Portability.hpp Kernel/Unit.hpp
Inferences/InferenceEngine.o: Kernel/Inference.hpp Kernel/Unit.hpp
Inferences/InferenceEngine.o: Shell/Statistics.hpp
Inferences/InferenceEngine.o: Inferences/InferenceEngine.hpp
Inferences/InterpretedEvaluation.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Inferences/InterpretedEvaluation.o: Debug/Assertion.hpp Lib/DArray.hpp
Inferences/InterpretedEvaluation.o: Forwards.hpp Config.hpp Lib/Allocator.hpp
Inferences/InterpretedEvaluation.o: Debug/Tracer.hpp Lib/Comparison.hpp
Inferences/InterpretedEvaluation.o: Lib/Exception.hpp Lib/Random.hpp
Inferences/InterpretedEvaluation.o: Lib/Reflection.hpp
Inferences/InterpretedEvaluation.o: Lib/VirtualIterator.hpp Lib/Stack.hpp
Inferences/InterpretedEvaluation.o: Lib/BacktrackData.hpp Lib/List.hpp
Inferences/InterpretedEvaluation.o: Lib/Int.hpp Lib/Portability.hpp
Inferences/InterpretedEvaluation.o: Lib/Environment.hpp Lib/Metaiterators.hpp
Inferences/InterpretedEvaluation.o: Lib/Set.hpp Lib/Hash.hpp
Inferences/InterpretedEvaluation.o: Lib/TimeCounter.hpp Lib/Int.hpp
Inferences/InterpretedEvaluation.o: Kernel/Signature.hpp Lib/Allocator.hpp
Inferences/InterpretedEvaluation.o: Lib/Map.hpp Kernel/Term.hpp
Inferences/InterpretedEvaluation.o: Kernel/Clause.hpp Lib/InverseLookup.hpp
Inferences/InterpretedEvaluation.o: Lib/DHMap.hpp Lib/Reflection.hpp
Inferences/InterpretedEvaluation.o: Kernel/Unit.hpp Lib/List.hpp
Inferences/InterpretedEvaluation.o: Kernel/Inference.hpp Kernel/Unit.hpp
Inferences/InterpretedEvaluation.o: Indexing/TermSharing.hpp Lib/Set.hpp
Inferences/InterpretedEvaluation.o: Shell/Statistics.hpp
Inferences/InterpretedEvaluation.o: Inferences/InterpretedEvaluation.hpp
Inferences/InterpretedEvaluation.o: Inferences/InferenceEngine.hpp
Inferences/PropositionalToBDDISE.o: Lib/Environment.hpp Forwards.hpp
Inferences/PropositionalToBDDISE.o: Config.hpp Lib/Exception.hpp
Inferences/PropositionalToBDDISE.o: Lib/LastCopyWatcher.hpp
Inferences/PropositionalToBDDISE.o: Debug/Assertion.hpp Lib/Stack.hpp
Inferences/PropositionalToBDDISE.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/PropositionalToBDDISE.o: Lib/BacktrackData.hpp Lib/List.hpp
Inferences/PropositionalToBDDISE.o: Lib/VirtualIterator.hpp
Inferences/PropositionalToBDDISE.o: Lib/Reflection.hpp Lib/Int.hpp
Inferences/PropositionalToBDDISE.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/PropositionalToBDDISE.o: Kernel/BDD.hpp Lib/Allocator.hpp
Inferences/PropositionalToBDDISE.o: Lib/Array.hpp Lib/DHMap.hpp Lib/Hash.hpp
Inferences/PropositionalToBDDISE.o: Lib/Int.hpp Lib/List.hpp Lib/Set.hpp
Inferences/PropositionalToBDDISE.o: Lib/SkipList.hpp Lib/Random.hpp
Inferences/PropositionalToBDDISE.o: Kernel/Signature.hpp Lib/Map.hpp
Inferences/PropositionalToBDDISE.o: Lib/Hash.hpp SAT/TWLSolver.hpp
Inferences/PropositionalToBDDISE.o: Lib/DArray.hpp Lib/Exception.hpp
Inferences/PropositionalToBDDISE.o: Kernel/Clause.hpp Lib/InverseLookup.hpp
Inferences/PropositionalToBDDISE.o: Lib/DHMap.hpp Lib/Metaiterators.hpp
Inferences/PropositionalToBDDISE.o: Lib/Set.hpp Lib/TimeCounter.hpp
Inferences/PropositionalToBDDISE.o: Lib/Reflection.hpp Kernel/Unit.hpp
Inferences/PropositionalToBDDISE.o: Kernel/InferenceStore.hpp
Inferences/PropositionalToBDDISE.o: Lib/DHMultiset.hpp Kernel/Inference.hpp
Inferences/PropositionalToBDDISE.o: Kernel/Unit.hpp Kernel/Term.hpp
Inferences/PropositionalToBDDISE.o: Shell/Statistics.hpp Shell/Options.hpp
Inferences/PropositionalToBDDISE.o: Lib/XML.hpp
Inferences/PropositionalToBDDISE.o: Inferences/PropositionalToBDDISE.hpp
Inferences/PropositionalToBDDISE.o: Inferences/InferenceEngine.hpp
Inferences/RefutationSeekerFSE.o: Lib/VirtualIterator.hpp
Inferences/RefutationSeekerFSE.o: Lib/Metaiterators.hpp Forwards.hpp
Inferences/RefutationSeekerFSE.o: Config.hpp Lib/List.hpp Debug/Assertion.hpp
Inferences/RefutationSeekerFSE.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/RefutationSeekerFSE.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/RefutationSeekerFSE.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp
Inferences/RefutationSeekerFSE.o: Lib/Set.hpp Lib/Hash.hpp
Inferences/RefutationSeekerFSE.o: Lib/TimeCounter.hpp Lib/Int.hpp
Inferences/RefutationSeekerFSE.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/RefutationSeekerFSE.o: Kernel/Unit.hpp Kernel/Inference.hpp
Inferences/RefutationSeekerFSE.o: Lib/Allocator.hpp Kernel/Clause.hpp
Inferences/RefutationSeekerFSE.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/RefutationSeekerFSE.o: Lib/Reflection.hpp Lib/Stack.hpp
Inferences/RefutationSeekerFSE.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/RefutationSeekerFSE.o: Kernel/Unit.hpp Lib/List.hpp
Inferences/RefutationSeekerFSE.o: Indexing/Index.hpp Lib/Event.hpp
Inferences/RefutationSeekerFSE.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/RefutationSeekerFSE.o: Saturation/ClauseContainer.hpp
Inferences/RefutationSeekerFSE.o: Saturation/Limits.hpp
Inferences/RefutationSeekerFSE.o: Indexing/ResultSubstitution.hpp
Inferences/RefutationSeekerFSE.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Inferences/RefutationSeekerFSE.o: Indexing/LiteralIndex.hpp Lib/DHMap.hpp
Inferences/RefutationSeekerFSE.o: Indexing/Index.hpp
Inferences/RefutationSeekerFSE.o: Indexing/IndexManager.hpp
Inferences/RefutationSeekerFSE.o: Saturation/SaturationAlgorithm.hpp
Inferences/RefutationSeekerFSE.o: Kernel/RCClauseStack.hpp
Inferences/RefutationSeekerFSE.o: Inferences/InferenceEngine.hpp
Inferences/RefutationSeekerFSE.o: Inferences/PropositionalToBDDISE.hpp
Inferences/RefutationSeekerFSE.o: Inferences/InferenceEngine.hpp
Inferences/RefutationSeekerFSE.o: Saturation/SaturationResult.hpp
Inferences/RefutationSeekerFSE.o: Shell/Statistics.hpp Lib/Environment.hpp
Inferences/RefutationSeekerFSE.o: Saturation/BSplitter.hpp Lib/Array.hpp
Inferences/RefutationSeekerFSE.o: Saturation/Splitter.hpp
Inferences/RefutationSeekerFSE.o: Indexing/ClauseVariantIndex.hpp
Inferences/RefutationSeekerFSE.o: Inferences/RefutationSeekerFSE.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Comparison.hpp Lib/DArray.hpp
Inferences/SLQueryBackwardSubsumption.o: Forwards.hpp Config.hpp
Inferences/SLQueryBackwardSubsumption.o: Debug/Assertion.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Comparison.hpp Lib/Exception.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/LastCopyWatcher.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Random.hpp Lib/Reflection.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/VirtualIterator.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Environment.hpp Lib/List.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Metaiterators.hpp Lib/List.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Set.hpp Lib/Hash.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/TimeCounter.hpp Lib/Set.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/TimeCounter.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/VirtualIterator.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Reflection.hpp Lib/Stack.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Portability.hpp Kernel/Unit.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/Matcher.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/BacktrackData.hpp Lib/DHMap.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Hash.hpp Kernel/Term.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/MLMatcher.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/Index.hpp Lib/Event.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/ClauseContainer.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/Limits.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/ResultSubstitution.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/SmartPtr.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/LiteralIndex.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/Index.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/IndexManager.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/SaturationAlgorithm.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/RCClauseStack.hpp
Inferences/SLQueryBackwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryBackwardSubsumption.o: Inferences/PropositionalToBDDISE.hpp
Inferences/SLQueryBackwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/SaturationResult.hpp
Inferences/SLQueryBackwardSubsumption.o: Shell/Statistics.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/BSplitter.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Array.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/Splitter.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/ClauseVariantIndex.hpp
Inferences/SLQueryBackwardSubsumption.o: Inferences/SLQueryBackwardSubsumption.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/VirtualIterator.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/BacktrackData.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/SkipList.hpp Debug/Assertion.hpp
Inferences/SLQueryForwardSubsumption.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Comparison.hpp Lib/Random.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/BacktrackData.hpp Lib/List.hpp
Inferences/SLQueryForwardSubsumption.o: Forwards.hpp Config.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/VirtualIterator.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Exception.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/LastCopyWatcher.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Reflection.hpp Lib/Int.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Portability.hpp Lib/DArray.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/List.hpp Lib/DHMap.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/DHMultiset.hpp Lib/Hash.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/DHMap.hpp Lib/Comparison.hpp
Inferences/SLQueryForwardSubsumption.o: Kernel/Term.hpp Kernel/Clause.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Allocator.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/InverseLookup.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Metaiterators.hpp Lib/Set.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/TimeCounter.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Reflection.hpp Lib/Stack.hpp
Inferences/SLQueryForwardSubsumption.o: Kernel/Unit.hpp Kernel/MLMatcher.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/Index.hpp Lib/Event.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/ClauseContainer.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/Limits.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/ResultSubstitution.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/SmartPtr.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/LiteralIndex.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/Index.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/IndexManager.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/SaturationAlgorithm.hpp
Inferences/SLQueryForwardSubsumption.o: Kernel/RCClauseStack.hpp
Inferences/SLQueryForwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryForwardSubsumption.o: Inferences/PropositionalToBDDISE.hpp
Inferences/SLQueryForwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/SaturationResult.hpp
Inferences/SLQueryForwardSubsumption.o: Shell/Statistics.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Environment.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/BSplitter.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Array.hpp Saturation/Splitter.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/ClauseVariantIndex.hpp
Inferences/SLQueryForwardSubsumption.o: Inferences/SLQueryForwardSubsumption.hpp
Inferences/Superposition.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Inferences/Superposition.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Inferences/Superposition.o: Debug/Assertion.hpp Lib/Int.hpp
Inferences/Superposition.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/Superposition.o: Lib/Metaiterators.hpp Lib/List.hpp
Inferences/Superposition.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/Superposition.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Inferences/Superposition.o: Lib/Set.hpp Lib/Hash.hpp Lib/TimeCounter.hpp
Inferences/Superposition.o: Lib/PairUtils.hpp Lib/Metaiterators.hpp
Inferences/Superposition.o: Lib/Metaarrays.hpp Lib/VirtualIterator.hpp
Inferences/Superposition.o: Shell/Options.hpp Lib/Allocator.hpp Lib/XML.hpp
Inferences/Superposition.o: Shell/Statistics.hpp Kernel/Term.hpp
Inferences/Superposition.o: Kernel/Clause.hpp Lib/InverseLookup.hpp
Inferences/Superposition.o: Lib/DHMap.hpp Lib/Reflection.hpp Lib/Stack.hpp
Inferences/Superposition.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Unit.hpp
Inferences/Superposition.o: Lib/List.hpp Kernel/Unit.hpp Kernel/Inference.hpp
Inferences/Superposition.o: Kernel/Ordering.hpp Lib/SmartPtr.hpp
Inferences/Superposition.o: Kernel/EqHelper.hpp Kernel/Term.hpp
Inferences/Superposition.o: Lib/Portability.hpp Lib/Comparison.hpp
Inferences/Superposition.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/Superposition.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Inferences/Superposition.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
Inferences/Superposition.o: Saturation/Limits.hpp
Inferences/Superposition.o: Indexing/ResultSubstitution.hpp
Inferences/Superposition.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Inferences/Superposition.o: Indexing/Index.hpp Indexing/TermSharing.hpp
Inferences/Superposition.o: Lib/Set.hpp Saturation/SaturationAlgorithm.hpp
Inferences/Superposition.o: Kernel/RCClauseStack.hpp
Inferences/Superposition.o: Inferences/InferenceEngine.hpp
Inferences/Superposition.o: Inferences/PropositionalToBDDISE.hpp
Inferences/Superposition.o: Inferences/InferenceEngine.hpp
Inferences/Superposition.o: Saturation/SaturationResult.hpp
Inferences/Superposition.o: Saturation/BSplitter.hpp Lib/Array.hpp
Inferences/Superposition.o: Saturation/Splitter.hpp
Inferences/Superposition.o: Indexing/ClauseVariantIndex.hpp
Inferences/Superposition.o: Inferences/Superposition.hpp
Inferences/Superposition.o: Indexing/TermIndex.hpp
Inferences/TautologyDeletionISE.o: Lib/Random.hpp Lib/Environment.hpp
Inferences/TautologyDeletionISE.o: Forwards.hpp Config.hpp Lib/Exception.hpp
Inferences/TautologyDeletionISE.o: Lib/LastCopyWatcher.hpp
Inferences/TautologyDeletionISE.o: Debug/Assertion.hpp Lib/DArray.hpp
Inferences/TautologyDeletionISE.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/TautologyDeletionISE.o: Lib/Comparison.hpp Lib/Random.hpp
Inferences/TautologyDeletionISE.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Inferences/TautologyDeletionISE.o: Kernel/Term.hpp Kernel/Clause.hpp
Inferences/TautologyDeletionISE.o: Lib/Allocator.hpp Lib/InverseLookup.hpp
Inferences/TautologyDeletionISE.o: Lib/Hash.hpp Lib/DHMap.hpp
Inferences/TautologyDeletionISE.o: Lib/Metaiterators.hpp Lib/List.hpp
Inferences/TautologyDeletionISE.o: Lib/Set.hpp Lib/TimeCounter.hpp
Inferences/TautologyDeletionISE.o: Lib/Reflection.hpp Lib/Stack.hpp
Inferences/TautologyDeletionISE.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/TautologyDeletionISE.o: Lib/Portability.hpp Kernel/Unit.hpp
Inferences/TautologyDeletionISE.o: Lib/List.hpp Kernel/EqHelper.hpp
Inferences/TautologyDeletionISE.o: Lib/VirtualIterator.hpp Lib/PairUtils.hpp
Inferences/TautologyDeletionISE.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/TautologyDeletionISE.o: Kernel/Term.hpp Lib/Portability.hpp
Inferences/TautologyDeletionISE.o: Lib/XML.hpp Lib/Comparison.hpp
Inferences/TautologyDeletionISE.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/TautologyDeletionISE.o: Shell/Statistics.hpp
Inferences/TautologyDeletionISE.o: Inferences/TautologyDeletionISE.hpp
Inferences/TautologyDeletionISE.o: Inferences/InferenceEngine.hpp
Rule/CASC.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Rule/CASC.o: Lib/Portability.hpp Debug/Assertion.hpp Lib/Sort.hpp
Rule/CASC.o: Lib/Allocator.hpp Lib/DArray.hpp Forwards.hpp Config.hpp
Rule/CASC.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Random.hpp
Rule/CASC.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp Lib/Environment.hpp
Rule/CASC.o: Kernel/Clause.hpp Lib/Allocator.hpp Lib/InverseLookup.hpp
Rule/CASC.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp Lib/List.hpp
Rule/CASC.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
Rule/CASC.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Unit.hpp Lib/List.hpp
Rule/CASC.o: Kernel/Signature.hpp Lib/Map.hpp Kernel/Term.hpp Rule/Rule.hpp
Rule/CASC.o: Rule/CASC.hpp Kernel/Unit.hpp Lib/Array.hpp
Rule/Index.o: Lib/Stack.hpp Forwards.hpp Config.hpp Debug/Assertion.hpp
Rule/Index.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Rule/Index.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Rule/Index.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
Rule/Index.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Clause.hpp
Rule/Index.o: Lib/Allocator.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
Rule/Index.o: Lib/DHMap.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Rule/Index.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Rule/Index.o: Lib/List.hpp Kernel/Signature.hpp Lib/Map.hpp Kernel/Term.hpp
Rule/Index.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Rule/Index.o: Lib/Exception.hpp Lib/VirtualIterator.hpp
Rule/Index.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
Rule/Index.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Rule/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Rule/Profile.o: Lib/Portability.hpp Debug/Assertion.hpp Lib/Sort.hpp
Rule/Profile.o: Lib/Allocator.hpp Lib/DArray.hpp Forwards.hpp Config.hpp
Rule/Profile.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Random.hpp
Rule/Profile.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Rule/Profile.o: Lib/Environment.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Rule/Profile.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Rule/Profile.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Rule/Profile.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
Rule/Profile.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Unit.hpp
Rule/Profile.o: Lib/List.hpp Kernel/Signature.hpp Lib/Map.hpp Kernel/Term.hpp
Rule/Profile.o: Shell/Profile.hpp Kernel/Unit.hpp Lib/Array.hpp
Rule/Prolog.o: Kernel/Term.hpp Kernel/Clause.hpp Forwards.hpp Config.hpp
Rule/Prolog.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Rule/Prolog.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Rule/Prolog.o: Lib/Allocator.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Rule/Prolog.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Rule/Prolog.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Rule/Prolog.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
Rule/Prolog.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Rule/Prolog.o: Lib/Portability.hpp Kernel/Unit.hpp Lib/List.hpp
Rule/Prolog.o: Rule/Prolog.hpp Lib/Map.hpp Rule/Index.hpp Kernel/Unit.hpp
Rule/Prolog.o: Rule/Rule.hpp
Rule/ProofAttempt.o: Debug/Tracer.hpp Lib/Environment.hpp Forwards.hpp
Rule/ProofAttempt.o: Config.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Rule/ProofAttempt.o: Debug/Assertion.hpp Shell/Statistics.hpp
Rule/ProofAttempt.o: Rule/ProofAttempt.hpp Kernel/Unit.hpp
SAT/ClauseSharing.o: Lib/Hash.hpp SAT/ClauseSharing.hpp Debug/Assertion.hpp
SAT/ClauseSharing.o: Lib/Set.hpp Lib/VirtualIterator.hpp SAT/SATClause.hpp
SAT/ClauseSharing.o: Forwards.hpp Config.hpp Lib/Allocator.hpp
SAT/ClauseSharing.o: Debug/Tracer.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
SAT/ClauseSharing.o: Lib/DHMap.hpp Lib/Allocator.hpp Lib/Exception.hpp
SAT/ClauseSharing.o: Lib/LastCopyWatcher.hpp Lib/VirtualIterator.hpp
SAT/ClauseSharing.o: Lib/Reflection.hpp Lib/List.hpp Lib/Metaiterators.hpp
SAT/ClauseSharing.o: Lib/List.hpp Lib/Set.hpp Lib/TimeCounter.hpp
SAT/ClauseSharing.o: Lib/Reflection.hpp SAT/SATLiteral.hpp
SAT/DIMACS.o: Lib/BinaryHeap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
SAT/DIMACS.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
SAT/DIMACS.o: Lib/Comparison.hpp Lib/BacktrackData.hpp Lib/List.hpp
SAT/DIMACS.o: Forwards.hpp Config.hpp Lib/VirtualIterator.hpp
SAT/DIMACS.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Portability.hpp
SAT/DIMACS.o: Lib/Metaiterators.hpp Lib/DHMap.hpp Lib/Int.hpp Lib/List.hpp
SAT/DIMACS.o: Lib/MapToLIFO.hpp Lib/DHMap.hpp Lib/Hash.hpp Lib/Stack.hpp
SAT/DIMACS.o: Lib/VirtualIterator.hpp Kernel/Clause.hpp Lib/Allocator.hpp
SAT/DIMACS.o: Lib/InverseLookup.hpp Lib/Metaiterators.hpp Lib/Set.hpp
SAT/DIMACS.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Kernel/Unit.hpp
SAT/DIMACS.o: Kernel/Term.hpp SAT/DIMACS.hpp SAT/SATClause.hpp
SAT/DIMACS.o: SAT/SATLiteral.hpp
SAT/Preprocess.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp Forwards.hpp
SAT/Preprocess.o: Config.hpp Lib/List.hpp Debug/Assertion.hpp
SAT/Preprocess.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/VirtualIterator.hpp
SAT/Preprocess.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
SAT/Preprocess.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
SAT/Preprocess.o: Lib/TimeCounter.hpp Lib/DArray.hpp Lib/Comparison.hpp
SAT/Preprocess.o: Lib/Random.hpp Lib/DHMap.hpp Lib/DHMultiset.hpp
SAT/Preprocess.o: Lib/DHMap.hpp Lib/Portability.hpp Lib/Random.hpp
SAT/Preprocess.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Reflection.hpp
SAT/Preprocess.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
SAT/Preprocess.o: SAT/SATClause.hpp Lib/Allocator.hpp Lib/InverseLookup.hpp
SAT/Preprocess.o: Lib/List.hpp SAT/SATLiteral.hpp Shell/Preprocess.hpp
SAT/Preprocess.o: Kernel/Unit.hpp
SAT/SATClause.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
SAT/SATClause.o: Lib/DHMap.hpp Lib/Int.hpp Lib/Comparison.hpp
SAT/SATClause.o: Lib/Portability.hpp Kernel/Clause.hpp Forwards.hpp
SAT/SATClause.o: Config.hpp Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
SAT/SATClause.o: Lib/Allocator.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
SAT/SATClause.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
SAT/SATClause.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
SAT/SATClause.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
SAT/SATClause.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Unit.hpp
SAT/SATClause.o: Lib/List.hpp Kernel/Term.hpp SAT/SATClause.hpp
SAT/SATClause.o: Lib/VirtualIterator.hpp SAT/SATLiteral.hpp
SAT/SATLiteral.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
SAT/SATLiteral.o: Debug/Assertion.hpp SAT/SATLiteral.hpp
SAT/SingleWatchSAT.o: Lib/Allocator.hpp Debug/Assertion.hpp Debug/Tracer.hpp
SAT/SingleWatchSAT.o: Lib/Random.hpp Lib/VirtualIterator.hpp
SAT/SingleWatchSAT.o: Lib/Portability.hpp Lib/Environment.hpp Forwards.hpp
SAT/SingleWatchSAT.o: Config.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
SAT/SingleWatchSAT.o: Lib/Timer.hpp Lib/Sort.hpp Lib/Allocator.hpp
SAT/SingleWatchSAT.o: Lib/DArray.hpp Lib/Comparison.hpp Lib/Random.hpp
SAT/SingleWatchSAT.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
SAT/SingleWatchSAT.o: SAT/SATClause.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
SAT/SingleWatchSAT.o: Lib/DHMap.hpp Lib/List.hpp Lib/Metaiterators.hpp
SAT/SingleWatchSAT.o: Lib/List.hpp Lib/Set.hpp Lib/TimeCounter.hpp
SAT/SingleWatchSAT.o: Lib/Reflection.hpp SAT/SATLiteral.hpp
SAT/SingleWatchSAT.o: SAT/ClauseSharing.hpp Lib/Set.hpp
SAT/SingleWatchSAT.o: SAT/SingleWatchSAT.hpp Lib/DArray.hpp Lib/Stack.hpp
SAT/SingleWatchSAT.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Portability.hpp
SAT/SingleWatchSAT.o: Lib/Int.hpp Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
SAT/SingleWatchSAT.o: Lib/Comparison.hpp Lib/BucketSorter.hpp Lib/Stack.hpp
SAT/TWLSolver.o: Debug/Assertion.hpp Lib/Array.hpp Lib/Allocator.hpp
SAT/TWLSolver.o: Debug/Tracer.hpp Lib/Environment.hpp Forwards.hpp Config.hpp
SAT/TWLSolver.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp SAT/SATLiteral.hpp
SAT/TWLSolver.o: SAT/SATClause.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
SAT/TWLSolver.o: Lib/DHMap.hpp Lib/Allocator.hpp Lib/VirtualIterator.hpp
SAT/TWLSolver.o: Lib/Reflection.hpp Lib/List.hpp Lib/Metaiterators.hpp
SAT/TWLSolver.o: Lib/List.hpp Lib/Set.hpp Lib/TimeCounter.hpp
SAT/TWLSolver.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp SAT/TWLSolver.hpp
SAT/TWLSolver.o: Lib/DArray.hpp Lib/Comparison.hpp Lib/Random.hpp
SAT/TWLSolver.o: Lib/Exception.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
SAT/TWLSolver.o: Lib/Int.hpp Lib/Portability.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Environment.hpp Forwards.hpp
Saturation/AWPassiveClauseContainer.o: Config.hpp Lib/Exception.hpp
Saturation/AWPassiveClauseContainer.o: Lib/LastCopyWatcher.hpp
Saturation/AWPassiveClauseContainer.o: Debug/Assertion.hpp Lib/Int.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Comparison.hpp Lib/Portability.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Timer.hpp Kernel/Term.hpp
Saturation/AWPassiveClauseContainer.o: Kernel/Clause.hpp Lib/Allocator.hpp
Saturation/AWPassiveClauseContainer.o: Debug/Tracer.hpp Lib/InverseLookup.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Hash.hpp Lib/DHMap.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Allocator.hpp
Saturation/AWPassiveClauseContainer.o: Lib/VirtualIterator.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Reflection.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Metaiterators.hpp Lib/List.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Set.hpp Lib/TimeCounter.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Reflection.hpp Lib/Stack.hpp
Saturation/AWPassiveClauseContainer.o: Lib/BacktrackData.hpp Lib/Int.hpp
Saturation/AWPassiveClauseContainer.o: Kernel/Unit.hpp Lib/List.hpp
Saturation/AWPassiveClauseContainer.o: Shell/Statistics.hpp Shell/Options.hpp
Saturation/AWPassiveClauseContainer.o: Lib/XML.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/SaturationAlgorithm.hpp
Saturation/AWPassiveClauseContainer.o: Kernel/RCClauseStack.hpp Lib/DHMap.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Event.hpp Lib/SmartPtr.hpp
Saturation/AWPassiveClauseContainer.o: Indexing/IndexManager.hpp
Saturation/AWPassiveClauseContainer.o: Indexing/Index.hpp Lib/Exception.hpp
Saturation/AWPassiveClauseContainer.o: Lib/VirtualIterator.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/ClauseContainer.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/Limits.hpp
Saturation/AWPassiveClauseContainer.o: Indexing/ResultSubstitution.hpp
Saturation/AWPassiveClauseContainer.o: Lib/SmartPtr.hpp
Saturation/AWPassiveClauseContainer.o: Inferences/InferenceEngine.hpp
Saturation/AWPassiveClauseContainer.o: Inferences/PropositionalToBDDISE.hpp
Saturation/AWPassiveClauseContainer.o: Inferences/InferenceEngine.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/SaturationResult.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/BSplitter.hpp Lib/Array.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/Splitter.hpp
Saturation/AWPassiveClauseContainer.o: Indexing/ClauseVariantIndex.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/AWPassiveClauseContainer.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Comparison.hpp
Saturation/AWPassiveClauseContainer.o: Kernel/ClauseQueue.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/ClauseContainer.hpp
Saturation/BSplitter.o: Lib/DHSet.hpp Forwards.hpp Config.hpp Lib/DHMap.hpp
Saturation/BSplitter.o: Debug/Assertion.hpp Lib/Allocator.hpp
Saturation/BSplitter.o: Debug/Tracer.hpp Lib/Exception.hpp
Saturation/BSplitter.o: Lib/LastCopyWatcher.hpp Lib/Hash.hpp
Saturation/BSplitter.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Saturation/BSplitter.o: Lib/Environment.hpp Lib/IntUnionFind.hpp
Saturation/BSplitter.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp
Saturation/BSplitter.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Saturation/BSplitter.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/TimeCounter.hpp
Saturation/BSplitter.o: Lib/SharedSet.hpp Lib/Metaiterators.hpp Lib/Sort.hpp
Saturation/BSplitter.o: Lib/DArray.hpp Lib/Random.hpp Kernel/BDD.hpp
Saturation/BSplitter.o: Lib/Allocator.hpp Lib/Array.hpp Lib/DHMap.hpp
Saturation/BSplitter.o: Lib/Hash.hpp Lib/Int.hpp Lib/List.hpp Lib/Set.hpp
Saturation/BSplitter.o: Lib/SkipList.hpp Lib/Stack.hpp Kernel/Signature.hpp
Saturation/BSplitter.o: Lib/Map.hpp SAT/TWLSolver.hpp Lib/DArray.hpp
Saturation/BSplitter.o: Lib/Exception.hpp Kernel/Clause.hpp
Saturation/BSplitter.o: Lib/InverseLookup.hpp Lib/Reflection.hpp
Saturation/BSplitter.o: Kernel/Unit.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Saturation/BSplitter.o: Shell/Statistics.hpp Shell/Options.hpp Lib/XML.hpp
Saturation/BSplitter.o: Saturation/BSplitter.hpp Kernel/RCClauseStack.hpp
Saturation/BSplitter.o: Saturation/SaturationAlgorithm.hpp Lib/Event.hpp
Saturation/BSplitter.o: Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Saturation/BSplitter.o: Indexing/Index.hpp Lib/VirtualIterator.hpp
Saturation/BSplitter.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
Saturation/BSplitter.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Saturation/BSplitter.o: Kernel/Term.hpp Inferences/InferenceEngine.hpp
Saturation/BSplitter.o: Inferences/PropositionalToBDDISE.hpp
Saturation/BSplitter.o: Inferences/InferenceEngine.hpp
Saturation/BSplitter.o: Saturation/SaturationResult.hpp
Saturation/BSplitter.o: Saturation/Splitter.hpp
Saturation/BSplitter.o: Indexing/ClauseVariantIndex.hpp
Saturation/ClauseContainer.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Saturation/ClauseContainer.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Saturation/ClauseContainer.o: Debug/Assertion.hpp Lib/Set.hpp Lib/Stack.hpp
Saturation/ClauseContainer.o: Debug/Tracer.hpp Lib/Allocator.hpp
Saturation/ClauseContainer.o: Lib/BacktrackData.hpp Lib/List.hpp
Saturation/ClauseContainer.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Saturation/ClauseContainer.o: Lib/Int.hpp Lib/Comparison.hpp
Saturation/ClauseContainer.o: Lib/Portability.hpp Kernel/Clause.hpp
Saturation/ClauseContainer.o: Lib/Allocator.hpp Lib/InverseLookup.hpp
Saturation/ClauseContainer.o: Lib/Hash.hpp Lib/DHMap.hpp
Saturation/ClauseContainer.o: Lib/Metaiterators.hpp Lib/Set.hpp
Saturation/ClauseContainer.o: Lib/TimeCounter.hpp Lib/Reflection.hpp
Saturation/ClauseContainer.o: Kernel/Unit.hpp Lib/List.hpp
Saturation/ClauseContainer.o: Shell/Statistics.hpp
Saturation/ClauseContainer.o: Indexing/LiteralIndexingStructure.hpp
Saturation/ClauseContainer.o: Indexing/Index.hpp Lib/Event.hpp
Saturation/ClauseContainer.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Saturation/ClauseContainer.o: Lib/VirtualIterator.hpp
Saturation/ClauseContainer.o: Saturation/ClauseContainer.hpp
Saturation/ClauseContainer.o: Saturation/Limits.hpp
Saturation/ClauseContainer.o: Indexing/ResultSubstitution.hpp
Saturation/ClauseContainer.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Saturation/ClauseContainer.o: Saturation/SaturationAlgorithm.hpp
Saturation/ClauseContainer.o: Kernel/RCClauseStack.hpp Lib/DHMap.hpp
Saturation/ClauseContainer.o: Indexing/IndexManager.hpp
Saturation/ClauseContainer.o: Inferences/InferenceEngine.hpp
Saturation/ClauseContainer.o: Inferences/PropositionalToBDDISE.hpp
Saturation/ClauseContainer.o: Inferences/InferenceEngine.hpp
Saturation/ClauseContainer.o: Saturation/SaturationResult.hpp
Saturation/ClauseContainer.o: Saturation/BSplitter.hpp Lib/Array.hpp
Saturation/ClauseContainer.o: Saturation/Splitter.hpp
Saturation/ClauseContainer.o: Indexing/ClauseVariantIndex.hpp
Saturation/ClauseContainer.o: Saturation/ClauseContainer.hpp
Saturation/Discount.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Saturation/Discount.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Saturation/Discount.o: Debug/Assertion.hpp Lib/VirtualIterator.hpp
Saturation/Discount.o: Kernel/Clause.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Saturation/Discount.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Saturation/Discount.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Saturation/Discount.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Saturation/Discount.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Saturation/Discount.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Saturation/Discount.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Saturation/Discount.o: Lib/List.hpp Kernel/LiteralSelector.hpp
Saturation/Discount.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Saturation/Discount.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Saturation/Discount.o: Lib/BitUtils.hpp Shell/Options.hpp
Saturation/Discount.o: Shell/Statistics.hpp Saturation/Discount.hpp
Saturation/Discount.o: Saturation/SaturationAlgorithm.hpp
Saturation/Discount.o: Kernel/RCClauseStack.hpp Lib/DHMap.hpp Lib/Event.hpp
Saturation/Discount.o: Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Saturation/Discount.o: Indexing/Index.hpp Lib/Exception.hpp
Saturation/Discount.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
Saturation/Discount.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Saturation/Discount.o: Kernel/Term.hpp Inferences/InferenceEngine.hpp
Saturation/Discount.o: Inferences/PropositionalToBDDISE.hpp
Saturation/Discount.o: Inferences/InferenceEngine.hpp
Saturation/Discount.o: Saturation/SaturationResult.hpp
Saturation/Discount.o: Saturation/BSplitter.hpp Lib/Array.hpp
Saturation/Discount.o: Saturation/Splitter.hpp
Saturation/Discount.o: Indexing/ClauseVariantIndex.hpp
Saturation/LRS.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Saturation/LRS.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Saturation/LRS.o: Debug/Assertion.hpp Lib/Timer.hpp Lib/VirtualIterator.hpp
Saturation/LRS.o: Kernel/Clause.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Saturation/LRS.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Saturation/LRS.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Saturation/LRS.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Saturation/LRS.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Saturation/LRS.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Saturation/LRS.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Saturation/LRS.o: Lib/List.hpp Kernel/LiteralSelector.hpp Kernel/Term.hpp
Saturation/LRS.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Saturation/LRS.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Shell/Statistics.hpp
Saturation/LRS.o: Shell/Options.hpp Saturation/LRS.hpp Lib/Event.hpp
Saturation/LRS.o: Lib/SmartPtr.hpp Saturation/SaturationAlgorithm.hpp
Saturation/LRS.o: Kernel/RCClauseStack.hpp Lib/DHMap.hpp
Saturation/LRS.o: Indexing/IndexManager.hpp Indexing/Index.hpp
Saturation/LRS.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
Saturation/LRS.o: Saturation/Limits.hpp Indexing/ResultSubstitution.hpp
Saturation/LRS.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Saturation/LRS.o: Inferences/InferenceEngine.hpp
Saturation/LRS.o: Inferences/PropositionalToBDDISE.hpp
Saturation/LRS.o: Inferences/InferenceEngine.hpp
Saturation/LRS.o: Saturation/SaturationResult.hpp Saturation/BSplitter.hpp
Saturation/LRS.o: Lib/Array.hpp Saturation/Splitter.hpp
Saturation/LRS.o: Indexing/ClauseVariantIndex.hpp
Saturation/Limits.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Saturation/Limits.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Saturation/Limits.o: Debug/Assertion.hpp Shell/Options.hpp Lib/Allocator.hpp
Saturation/Limits.o: Debug/Tracer.hpp Lib/XML.hpp Saturation/Limits.hpp
Saturation/Limits.o: Lib/Event.hpp Lib/List.hpp Lib/Allocator.hpp
Saturation/Limits.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Saturation/Limits.o: Lib/SmartPtr.hpp Kernel/Clause.hpp Lib/InverseLookup.hpp
Saturation/Limits.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp
Saturation/Limits.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Saturation/Limits.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Saturation/Limits.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Saturation/Limits.o: Lib/List.hpp
Saturation/Otter.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Saturation/Otter.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Saturation/Otter.o: Debug/Assertion.hpp Lib/VirtualIterator.hpp
Saturation/Otter.o: Kernel/Clause.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Saturation/Otter.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Saturation/Otter.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Saturation/Otter.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Saturation/Otter.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
Saturation/Otter.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Saturation/Otter.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Unit.hpp
Saturation/Otter.o: Lib/List.hpp Kernel/LiteralSelector.hpp Kernel/Term.hpp
Saturation/Otter.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Saturation/Otter.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Shell/Options.hpp
Saturation/Otter.o: Shell/Statistics.hpp Saturation/Otter.hpp
Saturation/Otter.o: Saturation/SaturationAlgorithm.hpp
Saturation/Otter.o: Kernel/RCClauseStack.hpp Lib/DHMap.hpp Lib/Event.hpp
Saturation/Otter.o: Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Saturation/Otter.o: Indexing/Index.hpp Lib/Exception.hpp
Saturation/Otter.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
Saturation/Otter.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Saturation/Otter.o: Kernel/Term.hpp Inferences/InferenceEngine.hpp
Saturation/Otter.o: Inferences/PropositionalToBDDISE.hpp
Saturation/Otter.o: Inferences/InferenceEngine.hpp
Saturation/Otter.o: Saturation/SaturationResult.hpp Saturation/BSplitter.hpp
Saturation/Otter.o: Lib/Array.hpp Saturation/Splitter.hpp
Saturation/Otter.o: Indexing/ClauseVariantIndex.hpp
Saturation/SaturationAlgorithm.o: Lib/DHSet.hpp Forwards.hpp Config.hpp
Saturation/SaturationAlgorithm.o: Lib/DHMap.hpp Debug/Assertion.hpp
Saturation/SaturationAlgorithm.o: Lib/Allocator.hpp Debug/Tracer.hpp
Saturation/SaturationAlgorithm.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Saturation/SaturationAlgorithm.o: Lib/Hash.hpp Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm.o: Lib/Reflection.hpp Lib/Environment.hpp
Saturation/SaturationAlgorithm.o: Lib/Metaiterators.hpp Lib/List.hpp
Saturation/SaturationAlgorithm.o: Lib/Set.hpp Lib/TimeCounter.hpp
Saturation/SaturationAlgorithm.o: Lib/SharedSet.hpp Lib/Metaiterators.hpp
Saturation/SaturationAlgorithm.o: Lib/Sort.hpp Lib/DArray.hpp
Saturation/SaturationAlgorithm.o: Lib/Comparison.hpp Lib/Random.hpp
Saturation/SaturationAlgorithm.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Saturation/SaturationAlgorithm.o: Lib/Int.hpp Lib/Portability.hpp
Saturation/SaturationAlgorithm.o: Lib/Stack.hpp Lib/Timer.hpp
Saturation/SaturationAlgorithm.o: Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm.o: Indexing/LiteralIndexingStructure.hpp
Saturation/SaturationAlgorithm.o: Indexing/Index.hpp Lib/Event.hpp
Saturation/SaturationAlgorithm.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Saturation/SaturationAlgorithm.o: Saturation/ClauseContainer.hpp
Saturation/SaturationAlgorithm.o: Saturation/Limits.hpp Kernel/Clause.hpp
Saturation/SaturationAlgorithm.o: Lib/Allocator.hpp Lib/InverseLookup.hpp
Saturation/SaturationAlgorithm.o: Lib/Reflection.hpp Kernel/Unit.hpp
Saturation/SaturationAlgorithm.o: Lib/List.hpp
Saturation/SaturationAlgorithm.o: Indexing/ResultSubstitution.hpp
Saturation/SaturationAlgorithm.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Saturation/SaturationAlgorithm.o: Kernel/BDD.hpp Lib/Array.hpp Lib/DHMap.hpp
Saturation/SaturationAlgorithm.o: Lib/Hash.hpp Lib/Int.hpp Lib/Set.hpp
Saturation/SaturationAlgorithm.o: Lib/SkipList.hpp Kernel/Signature.hpp
Saturation/SaturationAlgorithm.o: Lib/Map.hpp SAT/TWLSolver.hpp
Saturation/SaturationAlgorithm.o: Lib/DArray.hpp Kernel/Inference.hpp
Saturation/SaturationAlgorithm.o: Kernel/Unit.hpp Kernel/InferenceStore.hpp
Saturation/SaturationAlgorithm.o: Lib/DHMultiset.hpp
Saturation/SaturationAlgorithm.o: Kernel/LiteralSelector.hpp Kernel/Term.hpp
Saturation/SaturationAlgorithm.o: Lib/Portability.hpp Lib/XML.hpp
Saturation/SaturationAlgorithm.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Saturation/SaturationAlgorithm.o: Lib/BitUtils.hpp Kernel/MLVariant.hpp
Saturation/SaturationAlgorithm.o: Kernel/FormulaUnit.hpp
Saturation/SaturationAlgorithm.o: Kernel/SubformulaIterator.hpp
Saturation/SaturationAlgorithm.o: Kernel/Formula.hpp Kernel/Connective.hpp
Saturation/SaturationAlgorithm.o: Shell/Options.hpp Shell/Statistics.hpp
Saturation/SaturationAlgorithm.o: Saturation/SaturationAlgorithm.hpp
Saturation/SaturationAlgorithm.o: Kernel/RCClauseStack.hpp
Saturation/SaturationAlgorithm.o: Indexing/IndexManager.hpp
Saturation/SaturationAlgorithm.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm.o: Inferences/PropositionalToBDDISE.hpp
Saturation/SaturationAlgorithm.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm.o: Saturation/SaturationResult.hpp
Saturation/SaturationAlgorithm.o: Saturation/BSplitter.hpp
Saturation/SaturationAlgorithm.o: Saturation/Splitter.hpp
Saturation/SaturationAlgorithm.o: Indexing/ClauseVariantIndex.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Exception.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/LastCopyWatcher.hpp
Saturation/SaturationAlgorithm_Construction.o: Debug/Assertion.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/KBO.hpp Forwards.hpp
Saturation/SaturationAlgorithm_Construction.o: Config.hpp Lib/DArray.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Allocator.hpp
Saturation/SaturationAlgorithm_Construction.o: Debug/Tracer.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Comparison.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Exception.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Random.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Reflection.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Ordering.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/SmartPtr.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/LiteralSelector.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Term.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Allocator.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Portability.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/XML.hpp Lib/Comparison.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Stack.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/BacktrackData.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/List.hpp Lib/Int.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Portability.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Metaiterators.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Set.hpp Lib/Hash.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/TimeCounter.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/MatchTag.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/BitUtils.hpp
Saturation/SaturationAlgorithm_Construction.o: Shell/Options.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/List.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/BackwardDemodulation.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/TermIndex.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/Index.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Event.hpp Lib/SmartPtr.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/ClauseContainer.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Limits.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Clause.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/InverseLookup.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/DHMap.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Reflection.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Unit.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/ResultSubstitution.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Term.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/BinaryResolution.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/Condensation.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/EqualityFactoring.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/EqualityResolution.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/InterpretedEvaluation.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/Factoring.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/ForwardDemodulation.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/ForwardLiteralRewriting.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/LiteralIndex.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/DHMap.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/ForwardSubsumptionAndResolution.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/RefutationSeekerFSE.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/SLQueryForwardSubsumption.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/SLQueryBackwardSubsumption.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/Superposition.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/TautologyDeletionISE.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/AWPassiveClauseContainer.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/ClauseQueue.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/ClauseContainer.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/SaturationAlgorithm.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/RCClauseStack.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/IndexManager.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/PropositionalToBDDISE.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/SaturationResult.hpp
Saturation/SaturationAlgorithm_Construction.o: Shell/Statistics.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Environment.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/BSplitter.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Array.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Splitter.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/ClauseVariantIndex.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Discount.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/LRS.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Otter.hpp
Saturation/SaturationResult.o: Kernel/Clause.hpp Forwards.hpp Config.hpp
Saturation/SaturationResult.o: Lib/Allocator.hpp Debug/Assertion.hpp
Saturation/SaturationResult.o: Debug/Tracer.hpp Lib/InverseLookup.hpp
Saturation/SaturationResult.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Allocator.hpp
Saturation/SaturationResult.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Saturation/SaturationResult.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Saturation/SaturationResult.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Saturation/SaturationResult.o: Lib/TimeCounter.hpp Lib/Reflection.hpp
Saturation/SaturationResult.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Saturation/SaturationResult.o: Lib/Int.hpp Lib/Comparison.hpp
Saturation/SaturationResult.o: Lib/Portability.hpp Kernel/Unit.hpp
Saturation/SaturationResult.o: Lib/List.hpp Saturation/SaturationResult.hpp
Saturation/SaturationResult.o: Shell/Statistics.hpp Lib/Environment.hpp
Saturation/Splitter.o: Lib/DHMap.hpp Lib/Environment.hpp Forwards.hpp
Saturation/Splitter.o: Config.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Saturation/Splitter.o: Debug/Assertion.hpp Lib/IntUnionFind.hpp
Saturation/Splitter.o: Lib/Reflection.hpp Lib/Stack.hpp Debug/Tracer.hpp
Saturation/Splitter.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Saturation/Splitter.o: Lib/VirtualIterator.hpp Lib/Int.hpp Lib/Comparison.hpp
Saturation/Splitter.o: Lib/Portability.hpp Kernel/BDD.hpp Lib/Allocator.hpp
Saturation/Splitter.o: Lib/Array.hpp Lib/Hash.hpp Lib/Int.hpp Lib/List.hpp
Saturation/Splitter.o: Lib/Set.hpp Lib/SkipList.hpp Lib/Random.hpp
Saturation/Splitter.o: Lib/Stack.hpp Kernel/Signature.hpp Lib/Map.hpp
Saturation/Splitter.o: Lib/Hash.hpp SAT/TWLSolver.hpp Lib/DArray.hpp
Saturation/Splitter.o: Lib/Exception.hpp Kernel/Clause.hpp
Saturation/Splitter.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Saturation/Splitter.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/TimeCounter.hpp
Saturation/Splitter.o: Lib/Reflection.hpp Kernel/Unit.hpp
Saturation/Splitter.o: Kernel/Inference.hpp Kernel/Unit.hpp
Saturation/Splitter.o: Kernel/InferenceStore.hpp Lib/DHMultiset.hpp
Saturation/Splitter.o: Kernel/Term.hpp Shell/Options.hpp Lib/XML.hpp
Saturation/Splitter.o: Shell/Statistics.hpp Indexing/TermSharing.hpp
Saturation/Splitter.o: Inferences/PropositionalToBDDISE.hpp
Saturation/Splitter.o: Inferences/InferenceEngine.hpp Saturation/Splitter.hpp
Saturation/Splitter.o: Indexing/ClauseVariantIndex.hpp
Test/Compit2Output.o: Test/Compit2Output.hpp Config.hpp
Test/CompitOutput.o: Test/CompitOutput.hpp Config.hpp
Test/Output.o: Debug/Assertion.hpp Kernel/Term.hpp Kernel/Clause.hpp
Test/Output.o: Forwards.hpp Config.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Test/Output.o: Lib/InverseLookup.hpp Lib/Hash.hpp Lib/DHMap.hpp
Test/Output.o: Lib/Allocator.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Test/Output.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Test/Output.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Test/Output.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Lib/Stack.hpp
Test/Output.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Test/Output.o: Lib/Portability.hpp Kernel/Unit.hpp Lib/List.hpp Lib/Int.hpp
Test/Output.o: Test/Output.hpp Lib/Environment.hpp Kernel/Signature.hpp
Test/Output.o: Lib/Map.hpp
Global.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/System.hpp
Global.o: Lib/Enumerator.hpp Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp
Global.o: Kernel/Connective.hpp Kernel/Unit.hpp Forwards.hpp Config.hpp
Global.o: Lib/Environment.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
Global.o: Debug/Assertion.hpp
compit2.o: compit2.hpp Kernel/Term.hpp Forwards.hpp Config.hpp
compit2.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
compit2.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
compit2.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
compit2.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
compit2.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
compit2.o: Lib/Portability.hpp Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
compit2.o: Lib/TimeCounter.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
compit2.o: Lib/Timer.hpp
compit2_impl.o: compit2.hpp Kernel/Term.hpp Forwards.hpp Config.hpp
compit2_impl.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
compit2_impl.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
compit2_impl.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
compit2_impl.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
compit2_impl.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
compit2_impl.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Metaiterators.hpp
compit2_impl.o: Lib/Set.hpp Lib/Hash.hpp Lib/TimeCounter.hpp
compit2_impl.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Lib/Allocator.hpp
compit2_impl.o: Lib/Random.hpp Lib/Set.hpp Lib/Stack.hpp Lib/Int.hpp
compit2_impl.o: Lib/Timer.hpp Lib/Exception.hpp Lib/Environment.hpp
compit2_impl.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp
compit2_impl.o: Kernel/Signature.hpp Lib/Map.hpp Kernel/Curryfier.hpp
compit2_impl.o: Lib/Environment.hpp Lib/DHMap.hpp Lib/DArray.hpp
compit2_impl.o: Lib/Random.hpp Lib/ArrayMap.hpp Lib/DArray.hpp
compit2_impl.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
compit2_impl.o: Kernel/Term.hpp Kernel/Signature.hpp Indexing/TermSharing.hpp
compit2_impl.o: Indexing/TermSubstitutionTree.hpp Kernel/Renaming.hpp
compit2_impl.o: Lib/SkipList.hpp Indexing/Index.hpp Lib/Event.hpp
compit2_impl.o: Lib/SmartPtr.hpp Lib/Exception.hpp Lib/VirtualIterator.hpp
compit2_impl.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
compit2_impl.o: Kernel/Clause.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
compit2_impl.o: Lib/Reflection.hpp Kernel/Unit.hpp Lib/List.hpp
compit2_impl.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
compit2_impl.o: Indexing/TermIndexingStructure.hpp
compit2_impl.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp Lib/BinaryHeap.hpp
compit2_impl.o: Lib/Metaiterators.hpp Lib/BacktrackData.hpp Lib/Array.hpp
compit2_impl.o: Kernel/EGSubstitution.hpp Kernel/RobSubstitution.hpp
compit2_impl.o: Kernel/RobSubstitution.hpp Test/Output.hpp Shell/Options.hpp
compit2_impl.o: Shell/CommandLine.hpp Shell/Property.hpp Kernel/Unit.hpp
compit2_impl.o: Shell/Preprocess.hpp Shell/Statistics.hpp
test_BinaryHeap.o: Lib/BinaryHeap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
test_BinaryHeap.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
test_BinaryHeap.o: Lib/Comparison.hpp Lib/BacktrackData.hpp Lib/List.hpp
test_BinaryHeap.o: Forwards.hpp Config.hpp Lib/VirtualIterator.hpp
test_BinaryHeap.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Portability.hpp
test_BinaryHeap.o: Lib/Metaiterators.hpp Lib/Int.hpp
test_DHMap.o: Lib/DHMap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
test_DHMap.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
test_DHMap.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Forwards.hpp Config.hpp
test_DHMap.o: Lib/Reflection.hpp
test_DHMultiset.o: Lib/DHMultiset.hpp Debug/Assertion.hpp Lib/Allocator.hpp
test_DHMultiset.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
test_DHMultiset.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/VirtualIterator.hpp
test_DHMultiset.o: Forwards.hpp Config.hpp Lib/Reflection.hpp
test_DHMultiset.o: Lib/Portability.hpp
test_SkipList.o: Lib/SkipList.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_SkipList.o: Lib/Allocator.hpp Lib/Comparison.hpp Lib/Random.hpp
test_SkipList.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp Config.hpp
test_SkipList.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
test_SkipList.o: Lib/LastCopyWatcher.hpp Lib/Reflection.hpp Lib/Int.hpp
test_SkipList.o: Lib/Portability.hpp Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
test_SkipList.o: Lib/DHMultiset.hpp Lib/Hash.hpp Lib/DHMap.hpp Lib/Int.hpp
test_SkipList.o: Lib/DArray.hpp Lib/Timer.hpp Lib/Random.hpp
test_SubstitutionTree.o: Debug/Tracer.hpp Lib/Array.hpp Debug/Assertion.hpp
test_SubstitutionTree.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Random.hpp
test_SubstitutionTree.o: Lib/Set.hpp Lib/Int.hpp Lib/Timer.hpp
test_SubstitutionTree.o: Lib/Exception.hpp Lib/Environment.hpp Forwards.hpp
test_SubstitutionTree.o: Config.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
test_SubstitutionTree.o: Lib/Vector.hpp Lib/Allocator.hpp
test_SubstitutionTree.o: Kernel/Signature.hpp Lib/Stack.hpp
test_SubstitutionTree.o: Lib/BacktrackData.hpp Lib/List.hpp
test_SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
test_SubstitutionTree.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
test_SubstitutionTree.o: Lib/Map.hpp Lib/Hash.hpp Kernel/Clause.hpp
test_SubstitutionTree.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
test_SubstitutionTree.o: Lib/Metaiterators.hpp Lib/Set.hpp
test_SubstitutionTree.o: Lib/TimeCounter.hpp Lib/Reflection.hpp
test_SubstitutionTree.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp
test_SubstitutionTree.o: Lib/XML.hpp Kernel/Connective.hpp
test_SubstitutionTree.o: Kernel/FormulaUnit.hpp Indexing/TermSharing.hpp
test_SubstitutionTree.o: Indexing/SubstitutionTree.hpp
test_SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Comparison.hpp
test_SubstitutionTree.o: Lib/Int.hpp Lib/SkipList.hpp Lib/Random.hpp
test_SubstitutionTree.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
test_SubstitutionTree.o: Lib/BacktrackData.hpp Lib/ArrayMap.hpp
test_SubstitutionTree.o: Lib/DArray.hpp Lib/Array.hpp
test_SubstitutionTree.o: Kernel/EGSubstitution.hpp Lib/DHMap.hpp
test_SubstitutionTree.o: Kernel/Term.hpp Lib/Portability.hpp
test_SubstitutionTree.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
test_SubstitutionTree.o: Kernel/RobSubstitution.hpp
test_SubstitutionTree.o: Kernel/RobSubstitution.hpp Kernel/Renaming.hpp
test_SubstitutionTree.o: Kernel/Clause.hpp Indexing/Index.hpp Lib/Event.hpp
test_SubstitutionTree.o: Lib/SmartPtr.hpp Lib/Exception.hpp
test_SubstitutionTree.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
test_SubstitutionTree.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
test_SubstitutionTree.o: Kernel/Term.hpp Test/Output.hpp Shell/Options.hpp
test_SubstitutionTree.o: Shell/CommandLine.hpp Shell/TPTPLexer.hpp
test_SubstitutionTree.o: Shell/Lexer.hpp Shell/Token.hpp Shell/TPTP.hpp
test_SubstitutionTree.o: Shell/TPTPParser.hpp Kernel/Unit.hpp
test_SubstitutionTree.o: Shell/Parser.hpp Lib/IntNameTable.hpp Lib/Array.hpp
test_SubstitutionTree.o: Lib/Map.hpp Shell/Property.hpp Shell/Preprocess.hpp
test_SubstitutionTree.o: Shell/Statistics.hpp Shell/Refutation.hpp
test_SubstitutionTree.o: Shell/TheoryFinder.hpp Rule/CASC.hpp Rule/Prolog.hpp
test_SubstitutionTree.o: Rule/Index.hpp Rule/Rule.hpp Rule/Index.hpp
test_SubstitutionTree.o: Rule/ProofAttempt.hpp Test/Output.hpp
test_SubstitutionTree.o: Lib/MemoryLeak.hpp
test_alloc.o: Forwards.hpp Config.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_alloc.o: Lib/System.hpp Lib/Allocator.hpp Lib/Environment.hpp
test_alloc.o: Forwards.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
test_alloc.o: Debug/Assertion.hpp Lib/Random.hpp Lib/Stack.hpp Lib/Timer.hpp
test_alloc.o: Lib/VirtualIterator.hpp SAT/ClauseSharing.hpp Lib/Set.hpp
test_alloc.o: Lib/VirtualIterator.hpp SAT/SATClause.hpp Lib/Allocator.hpp
test_alloc.o: Debug/Tracer.hpp Lib/InverseLookup.hpp Lib/Hash.hpp
test_alloc.o: Lib/DHMap.hpp Lib/Allocator.hpp Lib/VirtualIterator.hpp
test_alloc.o: Lib/Reflection.hpp Lib/List.hpp Lib/Metaiterators.hpp
test_alloc.o: Lib/List.hpp Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp
test_alloc.o: SAT/SATLiteral.hpp SAT/DIMACS.hpp SAT/Preprocess.hpp
test_alloc.o: SAT/SingleWatchSAT.hpp Lib/DArray.hpp Lib/Comparison.hpp
test_alloc.o: Lib/Random.hpp Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
test_alloc.o: Lib/Portability.hpp Lib/Int.hpp Lib/BinaryHeap.hpp
test_alloc.o: Lib/Metaiterators.hpp Lib/Comparison.hpp Lib/BucketSorter.hpp
test_alloc.o: Lib/Stack.hpp SAT/TWLSolver.hpp Lib/Array.hpp Lib/Exception.hpp
test_alloc.o: Indexing/TermSharing.hpp Shell/CommandLine.hpp
test_alloc.o: Shell/Options.hpp Lib/XML.hpp Shell/Statistics.hpp
test_retrieval.o: Debug/Tracer.hpp Lib/Array.hpp Debug/Assertion.hpp
test_retrieval.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Random.hpp
test_retrieval.o: Lib/Set.hpp Lib/Int.hpp Lib/Timer.hpp Lib/Exception.hpp
test_retrieval.o: Lib/Environment.hpp Forwards.hpp Config.hpp
test_retrieval.o: Lib/Exception.hpp Lib/LastCopyWatcher.hpp Lib/Vector.hpp
test_retrieval.o: Lib/Allocator.hpp Kernel/Signature.hpp Lib/Stack.hpp
test_retrieval.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
test_retrieval.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
test_retrieval.o: Lib/Portability.hpp Lib/Map.hpp Lib/Hash.hpp
test_retrieval.o: Kernel/Clause.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
test_retrieval.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/TimeCounter.hpp
test_retrieval.o: Lib/Reflection.hpp Kernel/Unit.hpp Lib/List.hpp
test_retrieval.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
test_retrieval.o: Kernel/FormulaUnit.hpp Indexing/TermSharing.hpp
test_retrieval.o: Indexing/SubstitutionTree.hpp Lib/VirtualIterator.hpp
test_retrieval.o: Lib/Comparison.hpp Lib/Int.hpp Lib/SkipList.hpp
test_retrieval.o: Lib/Random.hpp Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
test_retrieval.o: Lib/BacktrackData.hpp Lib/ArrayMap.hpp Lib/DArray.hpp
test_retrieval.o: Lib/Array.hpp Kernel/EGSubstitution.hpp Lib/DHMap.hpp
test_retrieval.o: Kernel/Term.hpp Lib/Portability.hpp Kernel/MatchTag.hpp
test_retrieval.o: Lib/BitUtils.hpp Kernel/RobSubstitution.hpp
test_retrieval.o: Kernel/RobSubstitution.hpp Kernel/Renaming.hpp
test_retrieval.o: Kernel/Clause.hpp Indexing/Index.hpp Lib/Event.hpp
test_retrieval.o: Lib/SmartPtr.hpp Lib/Exception.hpp
test_retrieval.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
test_retrieval.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
test_retrieval.o: Kernel/Term.hpp Test/Output.hpp Shell/Options.hpp
test_retrieval.o: Shell/CommandLine.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
test_retrieval.o: Shell/Token.hpp Shell/TPTP.hpp Shell/TPTPParser.hpp
test_retrieval.o: Kernel/Unit.hpp Shell/Parser.hpp Lib/IntNameTable.hpp
test_retrieval.o: Lib/Array.hpp Lib/Map.hpp Shell/Property.hpp
test_retrieval.o: Shell/Preprocess.hpp Shell/Statistics.hpp
test_retrieval.o: Shell/Refutation.hpp Shell/TheoryFinder.hpp Rule/CASC.hpp
test_retrieval.o: Rule/Prolog.hpp Rule/Index.hpp Rule/Rule.hpp Rule/Index.hpp
test_retrieval.o: Rule/ProofAttempt.hpp Test/Output.hpp Lib/MemoryLeak.hpp
ucompit.o: Forwards.hpp Config.hpp Debug/Tracer.hpp Lib/Allocator.hpp
ucompit.o: Lib/Random.hpp Lib/Set.hpp Lib/Int.hpp Lib/Timer.hpp
ucompit.o: Debug/Assertion.hpp Lib/Exception.hpp Lib/Environment.hpp
ucompit.o: Forwards.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
ucompit.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp Kernel/Signature.hpp
ucompit.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Stack.hpp Lib/Allocator.hpp
ucompit.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
ucompit.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
ucompit.o: Lib/Portability.hpp Lib/Map.hpp Lib/Hash.hpp Kernel/Term.hpp
ucompit.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
ucompit.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/TimeCounter.hpp
ucompit.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Curryfier.hpp
ucompit.o: Lib/Environment.hpp Lib/DHMap.hpp Lib/DArray.hpp Lib/Random.hpp
ucompit.o: Lib/ArrayMap.hpp Lib/DArray.hpp Indexing/TermSharing.hpp
ucompit.o: Lib/Set.hpp Kernel/Term.hpp Kernel/Term.hpp Kernel/Signature.hpp
ucompit.o: Indexing/TermSharing.hpp Indexing/TermSubstitutionTree.hpp
ucompit.o: Kernel/Renaming.hpp Lib/SkipList.hpp Indexing/Index.hpp
ucompit.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
ucompit.o: Lib/VirtualIterator.hpp Saturation/ClauseContainer.hpp
ucompit.o: Saturation/Limits.hpp Kernel/Clause.hpp Lib/InverseLookup.hpp
ucompit.o: Lib/DHMap.hpp Lib/Reflection.hpp Kernel/Unit.hpp Lib/List.hpp
ucompit.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
ucompit.o: Indexing/TermIndexingStructure.hpp Indexing/SubstitutionTree.hpp
ucompit.o: Lib/Int.hpp Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
ucompit.o: Lib/BacktrackData.hpp Lib/Array.hpp Kernel/EGSubstitution.hpp
ucompit.o: Kernel/RobSubstitution.hpp Kernel/RobSubstitution.hpp
ucompit.o: Test/Output.hpp Shell/Options.hpp Shell/CommandLine.hpp
ucompit.o: Shell/Property.hpp Kernel/Unit.hpp Shell/Preprocess.hpp
ucompit.o: Shell/Statistics.hpp
vampire.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/Environment.hpp
vampire.o: Forwards.hpp Config.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
vampire.o: Debug/Assertion.hpp Lib/Int.hpp Lib/Random.hpp Lib/Set.hpp
vampire.o: Lib/TimeCounter.hpp Lib/Timer.hpp Lib/List.hpp Lib/Allocator.hpp
vampire.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp Lib/Reflection.hpp
vampire.o: Lib/Vector.hpp Lib/System.hpp Lib/Metaiterators.hpp
vampire.o: Kernel/Signature.hpp Lib/Allocator.hpp Lib/Stack.hpp
vampire.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
vampire.o: Lib/Portability.hpp Lib/Map.hpp Lib/Hash.hpp Kernel/Clause.hpp
vampire.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Lib/Metaiterators.hpp
vampire.o: Lib/Set.hpp Lib/TimeCounter.hpp Lib/Reflection.hpp Kernel/Unit.hpp
vampire.o: Lib/List.hpp Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
vampire.o: Kernel/FormulaUnit.hpp Kernel/InferenceStore.hpp Lib/DHMap.hpp
vampire.o: Lib/DHMultiset.hpp Kernel/BDD.hpp Lib/Array.hpp Lib/Hash.hpp
vampire.o: Lib/Int.hpp Lib/Set.hpp Lib/SkipList.hpp Lib/Random.hpp
vampire.o: Kernel/Signature.hpp SAT/TWLSolver.hpp Lib/DArray.hpp
vampire.o: Lib/Exception.hpp Kernel/Inference.hpp Kernel/Unit.hpp
vampire.o: Indexing/TermSharing.hpp Indexing/SubstitutionTree.hpp
vampire.o: Lib/VirtualIterator.hpp Lib/Comparison.hpp Lib/BinaryHeap.hpp
vampire.o: Lib/Metaiterators.hpp Lib/BacktrackData.hpp Lib/ArrayMap.hpp
vampire.o: Lib/DArray.hpp Kernel/EGSubstitution.hpp Kernel/Term.hpp
vampire.o: Lib/Portability.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
vampire.o: Kernel/RobSubstitution.hpp Kernel/RobSubstitution.hpp
vampire.o: Kernel/Renaming.hpp Kernel/Clause.hpp Indexing/Index.hpp
vampire.o: Lib/Event.hpp Lib/SmartPtr.hpp Saturation/ClauseContainer.hpp
vampire.o: Saturation/Limits.hpp Indexing/ResultSubstitution.hpp
vampire.o: Lib/SmartPtr.hpp Kernel/Term.hpp Test/Output.hpp
vampire.o: Indexing/LiteralMiniIndex.hpp Kernel/Matcher.hpp
vampire.o: Shell/CommandLine.hpp Shell/Grounding.hpp Shell/Interpolants.hpp
vampire.o: Shell/LaTeX.hpp Kernel/Connective.hpp Kernel/InferenceStore.hpp
vampire.o: Shell/LispLexer.hpp Shell/Lexer.hpp Shell/Token.hpp
vampire.o: Shell/LispParser.hpp Shell/Parser.hpp Lib/IntNameTable.hpp
vampire.o: Lib/Array.hpp Lib/Map.hpp Shell/Options.hpp Shell/Property.hpp
vampire.o: Shell/Preprocess.hpp Shell/Refutation.hpp Shell/TheoryFinder.hpp
vampire.o: Shell/SimplifyProver.hpp Shell/LispParser.hpp Shell/Statistics.hpp
vampire.o: Shell/TPTPLexer.hpp Shell/TPTP.hpp Shell/TPTPParser.hpp
vampire.o: Saturation/SaturationAlgorithm.hpp Kernel/RCClauseStack.hpp
vampire.o: Indexing/IndexManager.hpp Inferences/InferenceEngine.hpp
vampire.o: Inferences/PropositionalToBDDISE.hpp
vampire.o: Inferences/InferenceEngine.hpp Saturation/SaturationResult.hpp
vampire.o: Shell/Statistics.hpp Lib/Environment.hpp Saturation/BSplitter.hpp
vampire.o: Saturation/Splitter.hpp Indexing/ClauseVariantIndex.hpp
vampire.o: SAT/DIMACS.hpp SAT/SATClause.hpp SAT/SATLiteral.hpp
vampire.o: SAT/SATClause.hpp Lib/Stack.hpp Kernel/Term.hpp Lib/MemoryLeak.hpp
vcompit.o: Forwards.hpp Config.hpp Debug/Tracer.hpp Lib/Allocator.hpp
vcompit.o: Lib/Random.hpp Lib/Set.hpp Lib/Int.hpp Lib/Timer.hpp
vcompit.o: Debug/Assertion.hpp Lib/Exception.hpp Lib/Environment.hpp
vcompit.o: Forwards.hpp Lib/Exception.hpp Lib/LastCopyWatcher.hpp
vcompit.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp Kernel/Signature.hpp
vcompit.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Stack.hpp Lib/Allocator.hpp
vcompit.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
vcompit.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
vcompit.o: Lib/Portability.hpp Lib/Map.hpp Lib/Hash.hpp Kernel/Term.hpp
vcompit.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
vcompit.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/TimeCounter.hpp
vcompit.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Curryfier.hpp
vcompit.o: Lib/Environment.hpp Lib/DHMap.hpp Lib/DArray.hpp Lib/Random.hpp
vcompit.o: Lib/ArrayMap.hpp Lib/DArray.hpp Indexing/TermSharing.hpp
vcompit.o: Lib/Set.hpp Kernel/Term.hpp Kernel/Term.hpp Kernel/Signature.hpp
vcompit.o: Indexing/TermSharing.hpp Indexing/TermSubstitutionTree.hpp
vcompit.o: Kernel/Renaming.hpp Lib/SkipList.hpp Indexing/Index.hpp
vcompit.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
vcompit.o: Lib/VirtualIterator.hpp Saturation/ClauseContainer.hpp
vcompit.o: Saturation/Limits.hpp Kernel/Clause.hpp Lib/InverseLookup.hpp
vcompit.o: Lib/DHMap.hpp Lib/Reflection.hpp Kernel/Unit.hpp Lib/List.hpp
vcompit.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
vcompit.o: Indexing/TermIndexingStructure.hpp Indexing/SubstitutionTree.hpp
vcompit.o: Lib/Int.hpp Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
vcompit.o: Lib/BacktrackData.hpp Lib/Array.hpp Kernel/EGSubstitution.hpp
vcompit.o: Kernel/RobSubstitution.hpp Kernel/RobSubstitution.hpp
vcompit.o: Test/Output.hpp Shell/Options.hpp Shell/CommandLine.hpp
vcompit.o: Shell/Property.hpp Kernel/Unit.hpp Shell/Preprocess.hpp
vcompit.o: Shell/Statistics.hpp
vground.o: Debug/Tracer.hpp Lib/Random.hpp Lib/Set.hpp Lib/Int.hpp
vground.o: Lib/Timer.hpp Debug/Assertion.hpp Lib/Exception.hpp
vground.o: Lib/Environment.hpp Forwards.hpp Config.hpp Lib/Exception.hpp
vground.o: Lib/LastCopyWatcher.hpp Lib/List.hpp Lib/Allocator.hpp
vground.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp Lib/Reflection.hpp
vground.o: Lib/Vector.hpp Lib/System.hpp Lib/Metaiterators.hpp
vground.o: Lib/MapToLIFO.hpp Lib/DHMap.hpp Lib/Hash.hpp Lib/List.hpp
vground.o: Lib/Metaiterators.hpp Kernel/Signature.hpp Lib/Allocator.hpp
vground.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
vground.o: Lib/Portability.hpp Lib/Map.hpp Kernel/Clause.hpp
vground.o: Lib/InverseLookup.hpp Lib/Metaiterators.hpp Lib/Set.hpp
vground.o: Lib/TimeCounter.hpp Lib/Reflection.hpp Kernel/Unit.hpp
vground.o: Lib/List.hpp Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
vground.o: Kernel/FormulaUnit.hpp Kernel/InferenceStore.hpp Lib/DHMap.hpp
vground.o: Lib/DHMultiset.hpp Kernel/BDD.hpp Lib/Array.hpp Lib/Hash.hpp
vground.o: Lib/Int.hpp Lib/Set.hpp Lib/SkipList.hpp Lib/Random.hpp
vground.o: Kernel/Signature.hpp SAT/TWLSolver.hpp Lib/DArray.hpp
vground.o: Lib/Exception.hpp Kernel/Inference.hpp Kernel/Unit.hpp
vground.o: Indexing/TermSharing.hpp Indexing/SubstitutionTree.hpp
vground.o: Lib/VirtualIterator.hpp Lib/Comparison.hpp Lib/BinaryHeap.hpp
vground.o: Lib/BacktrackData.hpp Lib/ArrayMap.hpp Lib/DArray.hpp
vground.o: Kernel/EGSubstitution.hpp Kernel/Term.hpp Lib/Portability.hpp
vground.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/RobSubstitution.hpp
vground.o: Kernel/RobSubstitution.hpp Kernel/Renaming.hpp Kernel/Clause.hpp
vground.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
vground.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
vground.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp Kernel/Term.hpp
vground.o: Test/Output.hpp Indexing/LiteralMiniIndex.hpp Kernel/Matcher.hpp
vground.o: Shell/CommandLine.hpp Shell/GeneralSplitting.hpp
vground.o: Shell/Grounding.hpp Shell/Options.hpp Shell/Property.hpp
vground.o: Shell/Preprocess.hpp Shell/Refutation.hpp Shell/Statistics.hpp
vground.o: Shell/TPTPLexer.hpp Shell/Lexer.hpp Shell/Token.hpp Shell/TPTP.hpp
vground.o: Shell/TPTPParser.hpp Shell/Parser.hpp Lib/IntNameTable.hpp
vground.o: Lib/Array.hpp Lib/Map.hpp Saturation/SaturationAlgorithm.hpp
vground.o: Kernel/RCClauseStack.hpp Indexing/IndexManager.hpp
vground.o: Inferences/InferenceEngine.hpp
vground.o: Inferences/PropositionalToBDDISE.hpp
vground.o: Inferences/InferenceEngine.hpp Saturation/SaturationResult.hpp
vground.o: Shell/Statistics.hpp Lib/Environment.hpp Saturation/BSplitter.hpp
vground.o: Saturation/Splitter.hpp Indexing/ClauseVariantIndex.hpp
vground.o: SAT/DIMACS.hpp SAT/SATClause.hpp SAT/SATLiteral.hpp
vground.o: SAT/SATClause.hpp Lib/MemoryLeak.hpp
