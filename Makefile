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
XFLAGS = -g -DVDEBUG=1 -DCHECK_LEAKS=0 # standard debugging only
#XFLAGS = -O6 -DVDEBUG=0 # no debugging

#XFLAGS = -O6 -DVDEBUG=0 -mtune=athlon64 -march=athlon64 # no debugging, cpu optimization
#XFLAGS = -pg -g -DVDEBUG=1 -DCHECK_LEAKS=0 # profiling & debugging
#XFLAGS = -fprofile-arcs -pg -O6 -DVDEBUG=0 # coverage & profiling optimized
#XFLAGS = -DVDEBUG=0 # no debugging, no optimization
#XFLAGS = -O6 -DVDEBUG=1 -DCHECK_LEAKS=0 -g # debugging and optimized
#XFLAGS = -O6 -DVDEBUG=0 -g # Cachegrind
#XFLAGS = -O2 -DVDEBUG=0 -fno-inline-functions -fno-inline-functions-called-once -fno-default-inline -fno-inline-small-functions -fno-early-inlining -g # Callgrind
#XFLAGS = -O2 -DVDEBUG=0 -fno-inline-functions -fno-inline-functions-called-once -fno-default-inline -fno-early-inlining -g # Callgrind
#XFLAGS = -O6 -DVDEBUG=0 -fno-inline -g # Callgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -fno-inline -fno-default-inline -g # Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -fno-inline -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=1 -DCHECK_LEAKS=0 -DUSE_SYSTEM_ALLOCATION=1 -DVALGRIND=1 -fno-inline -fno-default-inline -g #Valgrind
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -DEFENCE=1-fno-inline -g -lefence #Electric Fence

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
        Lib/Hash.o\
        Lib/Int.o\
        Lib/IntNameTable.o\
        Lib/IntUnionFind.o\
        Lib/MemoryLeak.o\
        Lib/MultiCounter.o\
        Lib/NameArray.o\
        Lib/Random.o\
        Lib/System.o

VK_OBJ= Kernel/BDD.o\
        Kernel/Clause.o\
        Kernel/ClauseQueue.o\
        Kernel/DoubleSubstitution.o\
        Kernel/EGSubstitution.o\
        Kernel/EqHelper.o\
        Kernel/Formula.o\
        Kernel/FormulaUnit.o\
        Kernel/FormulaVarIterator.o\
        Kernel/Inference.o\
        Kernel/KBO.o\
        Kernel/LiteralSelector.o\
        Kernel/MatchTag.o\
        Kernel/MaximalLiteralSelector.o\
        Kernel/MLMatcher.o\
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
         Inferences/ForwardSubsumptionAndResolution.o\
         Inferences/InferenceEngine.o\
         Inferences/InterpretedEvaluation.o\
         Inferences/RefutationSeekerFSE.o\
         Inferences/SLQueryBackwardSubsumption.o\
         Inferences/SLQueryForwardSubsumption.o\
         Inferences/SplittingFSE.o\
         Inferences/Superposition.o\
         Inferences/TautologyDeletionFSE.o

VST_OBJ= Saturation/AWPassiveClauseContainer.o\
         Saturation/ClauseContainer.o\
         Saturation/Discount.o\
         Saturation/LRS.o\
         Saturation/Otter.o\
         Saturation/SaturationAlgorithm_Construction.o\
         Saturation/SaturationAlgorithm.o\
         Saturation/SaturationResult.o

VS_OBJ = Shell/CommandLine.o\
         Shell/CNF.o\
         Shell/Flattening.o\
         Shell/FunctionDefinition.o\
         Shell/Lexer.o\
         Shell/Naming.o\
         Shell/NNF.o\
         Shell/Normalisation.o\
         Shell/Options.o\
         Shell/Parser.o\
         Shell/Preprocess.o\
         Shell/Property.o\
         Shell/Rectify.o\
         Shell/Refutation.o\
         Shell/Skolem.o\
         Shell/SimplifyFalseTrue.o\
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


VAMP_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ)  
ALUC_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ)  
VCOMPIT_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VT_OBJ)  

VAMPIRE_OBJ = $(VAMP_BASIC) Global.o vampire.o
VCOMPIT_OBJ = $(VCOMPIT_BASIC) Global.o vcompit.o
UCOMPIT_OBJ = $(VCOMPIT_BASIC) Global.o compit2.o compit2_impl.o
SAT_OBJ = $(VD_OBJ) $(SAT) sat.o
TEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ) Global.o test_SubstitutionTree.o
RTEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ) Global.o test_retrieval.o
DHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_DHMap.o
DHMSTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_DHMultiset.o
BHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_BinaryHeap.o
SLTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_SkipList.o
ALLOCTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_alloc.o
ALUCARD_OBJ = $(ALUC_BASIC) Global.o alucard.o

################################################################

all:#default make disabled

vampire: $(VAMPIRE_OBJ)
	$(CXX) $(CXXFLAGS) $(VAMPIRE_OBJ) -o vampire
#	strip vampire

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

alucard:  $(ALUCARD_OBJ)
	$(CXX) $(CXXFLAGS) $(ALUCARD_OBJ) -o alucard

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

Debug/Assertion.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Debug/Assertion.o: Debug/Tracer.hpp
Debug/Tracer.o: Debug/Tracer.hpp
Lib/Allocator.o: Lib/DHMap.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Lib/Allocator.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
Lib/Allocator.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Forwards.hpp Config.hpp
Lib/Allocator.o: Lib/Reflection.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Lib/Allocator.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Lib/Allocator.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Kernel/Unit.hpp
Lib/Allocator.o: Lib/List.hpp Shell/Statistics.hpp Lib/Environment.hpp
Lib/Allocator.o: Lib/MemoryLeak.hpp Kernel/Unit.hpp Lib/Random.hpp
Lib/DHMap.o: Lib/DHMap.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Lib/DHMap.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
Lib/DHMap.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Forwards.hpp Config.hpp
Lib/DHMap.o: Lib/Reflection.hpp
Lib/Environment.o: Debug/Tracer.hpp Lib/Timer.hpp Debug/Assertion.hpp
Lib/Environment.o: Debug/Tracer.hpp Lib/Environment.hpp Forwards.hpp
Lib/Environment.o: Config.hpp Shell/Options.hpp Lib/Allocator.hpp Lib/XML.hpp
Lib/Environment.o: Shell/Statistics.hpp
Lib/Event.o: Lib/Event.hpp Lib/List.hpp Forwards.hpp Config.hpp
Lib/Event.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Lib/Event.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Lib/Event.o: Lib/Reflection.hpp Lib/SmartPtr.hpp
Lib/Exception.o: Lib/Exception.hpp
Lib/Hash.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Lib/Hash.o: Lib/Hash.hpp Lib/Portability.hpp
Lib/Int.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Lib/Int.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Lib/IntNameTable.o: Lib/IntNameTable.hpp Lib/Array.hpp Debug/Assertion.hpp
Lib/IntNameTable.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Lib/IntNameTable.o: Lib/Map.hpp Lib/Allocator.hpp Lib/Hash.hpp
Lib/IntNameTable.o: Lib/Exception.hpp
Lib/IntUnionFind.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/IntUnionFind.hpp
Lib/IntUnionFind.o: Lib/Reflection.hpp Lib/Stack.hpp Debug/Assertion.hpp
Lib/IntUnionFind.o: Debug/Tracer.hpp Lib/BacktrackData.hpp Lib/List.hpp
Lib/IntUnionFind.o: Forwards.hpp Config.hpp Lib/VirtualIterator.hpp
Lib/IntUnionFind.o: Lib/Exception.hpp Lib/Int.hpp Lib/Comparison.hpp
Lib/IntUnionFind.o: Lib/Portability.hpp
Lib/IntegerSet.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/IntegerSet.hpp
Lib/MemoryLeak.o: Lib/Hash.hpp Lib/Stack.hpp Debug/Assertion.hpp
Lib/MemoryLeak.o: Debug/Tracer.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Lib/MemoryLeak.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp Config.hpp
Lib/MemoryLeak.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Lib/MemoryLeak.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Lib/MemoryLeak.o: Lib/Portability.hpp Lib/MemoryLeak.hpp Lib/Set.hpp
Lib/MemoryLeak.o: Kernel/Unit.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Lib/MemoryLeak.o: Lib/Metaiterators.hpp Lib/Reflection.hpp
Lib/MemoryLeak.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp
Lib/MemoryLeak.o: Lib/List.hpp Kernel/Inference.hpp Kernel/Formula.hpp
Lib/MemoryLeak.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Lib/MultiCounter.o: Debug/Tracer.hpp Lib/MultiCounter.hpp Debug/Assertion.hpp
Lib/MultiCounter.o: Debug/Tracer.hpp Lib/XML.hpp Lib/Int.hpp
Lib/MultiCounter.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Allocator.hpp
Lib/MultiCounter.o: Lib/Exception.hpp
Lib/NameArray.o: Lib/NameArray.hpp Debug/Tracer.hpp
Lib/Random.o: Lib/Random.hpp
Lib/System.o: Debug/Tracer.hpp Lib/System.hpp
Shell/CNF.o: Debug/Tracer.hpp Kernel/Clause.hpp Forwards.hpp Config.hpp
Shell/CNF.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/CNF.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/CNF.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/Reflection.hpp
Shell/CNF.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Shell/CNF.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/CNF.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/CNF.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/FormulaUnit.hpp
Shell/CNF.o: Shell/CNF.hpp Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/CNF.o: Lib/Comparison.hpp Lib/Portability.hpp
Shell/CommandLine.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Shell/CommandLine.o: Lib/Exception.hpp Shell/CommandLine.hpp
Shell/CommandLine.o: Shell/Options.hpp Lib/Allocator.hpp Lib/XML.hpp
Shell/Flattening.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Flattening.o: Lib/Allocator.hpp Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/Flattening.o: Lib/List.hpp Shell/Flattening.hpp Kernel/Formula.hpp
Shell/Flattening.o: Lib/XML.hpp Kernel/Connective.hpp
Shell/FunctionDefinition.o: Debug/Tracer.hpp Lib/Allocator.hpp
Shell/FunctionDefinition.o: Kernel/Clause.hpp Forwards.hpp Config.hpp
Shell/FunctionDefinition.o: Lib/Metaiterators.hpp Lib/List.hpp
Shell/FunctionDefinition.o: Debug/Assertion.hpp Debug/Tracer.hpp
Shell/FunctionDefinition.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Shell/FunctionDefinition.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp
Shell/FunctionDefinition.o: Lib/Hash.hpp Lib/Reflection.hpp
Shell/FunctionDefinition.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Shell/FunctionDefinition.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp
Shell/FunctionDefinition.o: Lib/XML.hpp Kernel/Connective.hpp
Shell/FunctionDefinition.o: Kernel/FormulaUnit.hpp Kernel/Term.hpp
Shell/FunctionDefinition.o: Lib/Portability.hpp Lib/Comparison.hpp
Shell/FunctionDefinition.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/FunctionDefinition.o: Lib/Comparison.hpp Lib/Portability.hpp
Shell/FunctionDefinition.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Shell/FunctionDefinition.o: Kernel/TermVarIterator.hpp
Shell/FunctionDefinition.o: Kernel/TermFunIterator.hpp
Shell/FunctionDefinition.o: Shell/FunctionDefinition.hpp Lib/MultiCounter.hpp
Shell/FunctionDefinition.o: Lib/XML.hpp Kernel/Unit.hpp
Shell/Lexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Shell/Lexer.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/Lexer.o: Shell/Lexer.hpp Lib/Array.hpp Lib/Allocator.hpp
Shell/Lexer.o: Lib/Exception.hpp Shell/Token.hpp
Shell/NNF.o: Lib/Environment.hpp Forwards.hpp Config.hpp Kernel/Inference.hpp
Shell/NNF.o: Kernel/Unit.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/NNF.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/NNF.o: Kernel/Term.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/NNF.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/NNF.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Shell/NNF.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/Reflection.hpp
Shell/NNF.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/NNF.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Shell/NNF.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Indexing/TermSharing.hpp
Shell/NNF.o: Lib/Set.hpp Shell/NNF.hpp Kernel/Formula.hpp
Shell/NNF.o: Kernel/Connective.hpp
Shell/Naming.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Shell/Naming.o: Lib/Comparison.hpp Lib/Portability.hpp Debug/Assertion.hpp
Shell/Naming.o: Debug/Tracer.hpp Lib/Environment.hpp Forwards.hpp Config.hpp
Shell/Naming.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/Naming.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/Signature.hpp
Shell/Naming.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Shell/Naming.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Naming.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Map.hpp Lib/Hash.hpp
Shell/Naming.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Shell/Naming.o: Lib/Comparison.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Shell/Naming.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Shell/Statistics.hpp
Shell/Naming.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Naming.hpp
Shell/Naming.o: Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Normalisation.o: Lib/Sort.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Normalisation.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/DArray.hpp
Shell/Normalisation.o: Forwards.hpp Config.hpp Lib/Comparison.hpp
Shell/Normalisation.o: Lib/Random.hpp Lib/Reflection.hpp
Shell/Normalisation.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Normalisation.o: Lib/Environment.hpp Kernel/Clause.hpp
Shell/Normalisation.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/Normalisation.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Shell/Normalisation.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp
Shell/Normalisation.o: Lib/List.hpp Kernel/FormulaUnit.hpp
Shell/Normalisation.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/Term.hpp
Shell/Normalisation.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/Normalisation.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/Normalisation.o: Lib/Portability.hpp Kernel/MatchTag.hpp
Shell/Normalisation.o: Lib/BitUtils.hpp Kernel/Signature.hpp Lib/Map.hpp
Shell/Normalisation.o: Kernel/SubformulaIterator.hpp Kernel/Formula.hpp
Shell/Normalisation.o: Kernel/Connective.hpp Shell/Normalisation.hpp
Shell/Normalisation.o: Shell/SymCounter.hpp
Shell/Options.o: Debug/Tracer.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Options.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/Options.o: Lib/NameArray.hpp Lib/Random.hpp Lib/Exception.hpp
Shell/Options.o: Shell/Options.hpp Lib/Allocator.hpp Lib/XML.hpp
Shell/Parser.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Shell/Parser.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/Parser.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Allocator.hpp
Shell/Parser.o: Lib/Map.hpp Lib/Allocator.hpp Lib/Hash.hpp Lib/Exception.hpp
Shell/Parser.o: Shell/Lexer.hpp Lib/Array.hpp Lib/Exception.hpp
Shell/Parser.o: Shell/Token.hpp Shell/Parser.hpp Lib/XML.hpp Kernel/Unit.hpp
Shell/Preprocess.o: Debug/Tracer.hpp Kernel/Unit.hpp Kernel/Clause.hpp
Shell/Preprocess.o: Forwards.hpp Config.hpp Lib/Allocator.hpp
Shell/Preprocess.o: Lib/Metaiterators.hpp Lib/List.hpp Debug/Assertion.hpp
Shell/Preprocess.o: Debug/Tracer.hpp Lib/Allocator.hpp
Shell/Preprocess.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Preprocess.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Shell/Preprocess.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Shell/Preprocess.o: Kernel/Unit.hpp Lib/List.hpp Shell/CNF.hpp Lib/Stack.hpp
Shell/Preprocess.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Preprocess.o: Lib/Portability.hpp Shell/Flattening.hpp
Shell/Preprocess.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/Preprocess.o: Shell/Naming.hpp Shell/Normalisation.hpp
Shell/Preprocess.o: Lib/Comparison.hpp Shell/SymCounter.hpp Shell/NNF.hpp
Shell/Preprocess.o: Shell/Options.hpp Shell/Preprocess.hpp Shell/Property.hpp
Shell/Preprocess.o: Shell/Rectify.hpp Lib/Array.hpp Shell/Skolem.hpp
Shell/Preprocess.o: Kernel/Substitution.hpp Lib/Random.hpp
Shell/Preprocess.o: Lib/Environment.hpp Kernel/Term.hpp Lib/Portability.hpp
Shell/Preprocess.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Shell/Preprocess.o: Shell/SimplifyFalseTrue.hpp
Shell/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Profile.o: Lib/Portability.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Profile.o: Lib/Sort.hpp Lib/Allocator.hpp Lib/DArray.hpp Forwards.hpp
Shell/Profile.o: Config.hpp Lib/Random.hpp Lib/Reflection.hpp
Shell/Profile.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Profile.o: Lib/Environment.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Shell/Profile.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp Lib/Hash.hpp
Shell/Profile.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Shell/Profile.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Signature.hpp
Shell/Profile.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp Lib/Map.hpp
Shell/Profile.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Shell/Profile.o: Lib/Comparison.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Shell/Profile.o: Shell/Profile.hpp Kernel/Unit.hpp Lib/Array.hpp
Shell/Property.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Property.o: Lib/Portability.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Property.o: Kernel/Clause.hpp Forwards.hpp Config.hpp Lib/Allocator.hpp
Shell/Property.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Allocator.hpp
Shell/Property.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Property.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Shell/Property.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Shell/Property.o: Kernel/Unit.hpp Lib/List.hpp Kernel/FormulaUnit.hpp
Shell/Property.o: Kernel/SubformulaIterator.hpp Kernel/Formula.hpp
Shell/Property.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/Term.hpp
Shell/Property.o: Lib/Portability.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/Property.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/MatchTag.hpp
Shell/Property.o: Lib/BitUtils.hpp Shell/FunctionDefinition.hpp
Shell/Property.o: Lib/MultiCounter.hpp Lib/XML.hpp Kernel/Unit.hpp
Shell/Property.o: Shell/Property.hpp
Shell/Rectify.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Shell/Rectify.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp
Shell/Rectify.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/Rectify.o: Lib/Allocator.hpp Debug/Tracer.hpp Kernel/Unit.hpp
Shell/Rectify.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/Term.hpp
Shell/Rectify.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Portability.hpp
Shell/Rectify.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Shell/Rectify.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
Shell/Rectify.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Shell/Rectify.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Metaiterators.hpp
Shell/Rectify.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp
Shell/Rectify.o: Lib/BitUtils.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/Rectify.o: Shell/Rectify.hpp Lib/Array.hpp
Shell/Refutation.o: Debug/Tracer.hpp Lib/Hash.hpp Lib/Set.hpp Lib/Stack.hpp
Shell/Refutation.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/Refutation.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp
Shell/Refutation.o: Config.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Refutation.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Refutation.o: Lib/Portability.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Shell/Refutation.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Shell/Refutation.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Shell/Refutation.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Inference.hpp
Shell/Refutation.o: Kernel/Unit.hpp Shell/Refutation.hpp
Shell/SMTLexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Shell/SMTLexer.o: Lib/Exception.hpp Shell/SMTLexer.hpp Shell/Lexer.hpp
Shell/SMTLexer.o: Lib/Array.hpp Lib/Allocator.hpp Shell/Token.hpp
Shell/SMTParser.o: Shell/SMTLexer.hpp Shell/Lexer.hpp Lib/Array.hpp
Shell/SMTParser.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/SMTParser.o: Debug/Tracer.hpp Lib/Exception.hpp Shell/Token.hpp
Shell/SMTParser.o: Shell/SMTParser.hpp Shell/Parser.hpp Lib/IntNameTable.hpp
Shell/SMTParser.o: Lib/Array.hpp Lib/Map.hpp Lib/Allocator.hpp Lib/Hash.hpp
Shell/SMTParser.o: Lib/Exception.hpp Lib/XML.hpp Kernel/Unit.hpp
Shell/SimplifyFalseTrue.o: Debug/Tracer.hpp Lib/DArray.hpp Forwards.hpp
Shell/SimplifyFalseTrue.o: Config.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/SimplifyFalseTrue.o: Lib/Allocator.hpp Lib/Comparison.hpp
Shell/SimplifyFalseTrue.o: Lib/Random.hpp Lib/Reflection.hpp
Shell/SimplifyFalseTrue.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/SimplifyFalseTrue.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/SimplifyFalseTrue.o: Lib/Allocator.hpp Kernel/FormulaUnit.hpp
Shell/SimplifyFalseTrue.o: Kernel/Unit.hpp Lib/List.hpp
Shell/SimplifyFalseTrue.o: Shell/SimplifyFalseTrue.hpp Kernel/Formula.hpp
Shell/SimplifyFalseTrue.o: Lib/XML.hpp Kernel/Connective.hpp
Shell/Skolem.o: Kernel/Signature.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/Skolem.o: Lib/Stack.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Skolem.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Shell/Skolem.o: Forwards.hpp Config.hpp Lib/VirtualIterator.hpp
Shell/Skolem.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Shell/Skolem.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Map.hpp
Shell/Skolem.o: Lib/Hash.hpp Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Shell/Skolem.o: Lib/Comparison.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Shell/Skolem.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Inference.hpp
Shell/Skolem.o: Kernel/Unit.hpp Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/Skolem.o: Lib/List.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/Skolem.o: Shell/Rectify.hpp Lib/Array.hpp Kernel/Formula.hpp
Shell/Skolem.o: Kernel/Connective.hpp Shell/Skolem.hpp
Shell/Skolem.o: Kernel/Substitution.hpp Lib/Random.hpp Lib/Environment.hpp
Shell/Skolem.o: Kernel/Term.hpp
Shell/Statistics.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Shell/Statistics.o: Shell/Statistics.hpp
Shell/SymCounter.o: Lib/Allocator.hpp Debug/Tracer.hpp Kernel/Term.hpp
Shell/SymCounter.o: Forwards.hpp Config.hpp Debug/Assertion.hpp
Shell/SymCounter.o: Debug/Tracer.hpp Lib/Portability.hpp Lib/XML.hpp
Shell/SymCounter.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Shell/SymCounter.o: Lib/BacktrackData.hpp Lib/List.hpp
Shell/SymCounter.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/SymCounter.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/SymCounter.o: Lib/Portability.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Shell/SymCounter.o: Lib/Hash.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Shell/SymCounter.o: Kernel/Clause.hpp Lib/Reflection.hpp
Shell/SymCounter.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp
Shell/SymCounter.o: Lib/List.hpp Kernel/Formula.hpp Kernel/Connective.hpp
Shell/SymCounter.o: Kernel/FormulaUnit.hpp Kernel/Signature.hpp Lib/Map.hpp
Shell/SymCounter.o: Kernel/Unit.hpp Shell/SymCounter.hpp
Shell/TPTP.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/TPTP.o: Debug/Assertion.hpp Debug/Tracer.hpp Kernel/Term.hpp
Shell/TPTP.o: Forwards.hpp Config.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/TPTP.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/TPTP.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Shell/TPTP.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/TPTP.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Metaiterators.hpp
Shell/TPTP.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Shell/TPTP.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/Formula.hpp
Shell/TPTP.o: Lib/List.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/TPTP.o: Kernel/Unit.hpp Kernel/Clause.hpp Lib/Reflection.hpp
Shell/TPTP.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Shell/TPTP.hpp
Shell/TPTPLexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Shell/TPTPLexer.o: Lib/Exception.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
Shell/TPTPLexer.o: Lib/Array.hpp Lib/Allocator.hpp Shell/Token.hpp
Shell/TPTPParser.o: Lib/List.hpp Lib/Stack.hpp Debug/Assertion.hpp
Shell/TPTPParser.o: Debug/Tracer.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/TPTPParser.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp
Shell/TPTPParser.o: Config.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/TPTPParser.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/TPTPParser.o: Lib/Portability.hpp Lib/Environment.hpp
Shell/TPTPParser.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/Allocator.hpp
Shell/TPTPParser.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Shell/TPTPParser.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/TPTPParser.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Kernel/Term.hpp
Shell/TPTPParser.o: Lib/Portability.hpp Lib/Comparison.hpp
Shell/TPTPParser.o: Lib/Metaiterators.hpp Lib/Set.hpp Kernel/MatchTag.hpp
Shell/TPTPParser.o: Lib/BitUtils.hpp Kernel/Clause.hpp Lib/Reflection.hpp
Shell/TPTPParser.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Shell/Statistics.hpp
Shell/TPTPParser.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Options.hpp
Shell/TPTPParser.o: Shell/TPTPLexer.hpp Shell/Lexer.hpp Lib/Array.hpp
Shell/TPTPParser.o: Lib/Exception.hpp Shell/Token.hpp Shell/TPTPParser.hpp
Shell/TPTPParser.o: Shell/Parser.hpp Lib/IntNameTable.hpp Lib/Array.hpp
Shell/TPTPParser.o: Lib/Map.hpp
Shell/TheoryFinder.o: Debug/Tracer.hpp Kernel/Clause.hpp Forwards.hpp
Shell/TheoryFinder.o: Config.hpp Lib/Allocator.hpp Lib/Metaiterators.hpp
Shell/TheoryFinder.o: Lib/List.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/TheoryFinder.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Shell/TheoryFinder.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp
Shell/TheoryFinder.o: Lib/Hash.hpp Lib/Reflection.hpp Lib/InverseLookup.hpp
Shell/TheoryFinder.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/TheoryFinder.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/TheoryFinder.o: Kernel/FormulaUnit.hpp Kernel/Term.hpp
Shell/TheoryFinder.o: Lib/Portability.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/TheoryFinder.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/TheoryFinder.o: Lib/Portability.hpp Kernel/MatchTag.hpp
Shell/TheoryFinder.o: Lib/BitUtils.hpp Shell/Property.hpp Kernel/Unit.hpp
Shell/TheoryFinder.o: Shell/TheoryFinder.hpp
Shell/Token.o: Debug/Assertion.hpp Debug/Tracer.hpp Shell/Token.hpp
Kernel/BDD.o: Lib/Stack.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/BDD.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/BDD.o: Lib/List.hpp Forwards.hpp Config.hpp Lib/VirtualIterator.hpp
Kernel/BDD.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Kernel/BDD.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/BDD.hpp
Kernel/BDD.o: Lib/Allocator.hpp Lib/Hash.hpp Lib/Set.hpp
Kernel/Clause.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Kernel/Clause.o: Lib/Comparison.hpp Lib/Portability.hpp Debug/Assertion.hpp
Kernel/Clause.o: Debug/Tracer.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/Clause.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp Config.hpp
Kernel/Clause.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/Reflection.hpp
Kernel/Clause.o: Lib/Int.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Clause.o: Kernel/Clause.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/Clause.o: Lib/Hash.hpp Lib/Reflection.hpp Lib/InverseLookup.hpp
Kernel/Clause.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp Kernel/Term.hpp
Kernel/Clause.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Clause.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/ClauseQueue.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Random.hpp
Kernel/ClauseQueue.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Kernel/ClauseQueue.o: Kernel/Clause.hpp Lib/Metaiterators.hpp Lib/List.hpp
Kernel/ClauseQueue.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/ClauseQueue.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/ClauseQueue.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/ClauseQueue.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Kernel/ClauseQueue.o: Kernel/Unit.hpp Lib/List.hpp Kernel/ClauseQueue.hpp
Kernel/DoubleSubstitution.o: Lib/Int.hpp Lib/Comparison.hpp
Kernel/DoubleSubstitution.o: Lib/Portability.hpp Debug/Assertion.hpp
Kernel/DoubleSubstitution.o: Debug/Tracer.hpp Lib/DArray.hpp Forwards.hpp
Kernel/DoubleSubstitution.o: Config.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/DoubleSubstitution.o: Lib/Random.hpp Lib/Reflection.hpp
Kernel/DoubleSubstitution.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/DoubleSubstitution.o: Kernel/Term.hpp Lib/Allocator.hpp
Kernel/DoubleSubstitution.o: Lib/Portability.hpp Lib/XML.hpp
Kernel/DoubleSubstitution.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/DoubleSubstitution.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/DoubleSubstitution.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/DoubleSubstitution.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/DoubleSubstitution.o: Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp
Kernel/EGSubstitution.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Kernel/EGSubstitution.o: Lib/Hash.hpp Lib/DArray.hpp Debug/Assertion.hpp
Kernel/EGSubstitution.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/EGSubstitution.o: Lib/Comparison.hpp Lib/Random.hpp Lib/Reflection.hpp
Kernel/EGSubstitution.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/EGSubstitution.o: Lib/List.hpp Lib/Random.hpp Lib/DHMultiset.hpp
Kernel/EGSubstitution.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/DHMap.hpp
Kernel/EGSubstitution.o: Lib/SkipList.hpp Lib/BacktrackData.hpp Lib/List.hpp
Kernel/EGSubstitution.o: Lib/Int.hpp Lib/Portability.hpp Lib/Int.hpp
Kernel/EGSubstitution.o: Kernel/Term.hpp Lib/Allocator.hpp
Kernel/EGSubstitution.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/EGSubstitution.o: Lib/Stack.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/EGSubstitution.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/EGSubstitution.o: Kernel/Clause.hpp Lib/Reflection.hpp
Kernel/EGSubstitution.o: Lib/InverseLookup.hpp Kernel/Unit.hpp
Kernel/EGSubstitution.o: Kernel/Renaming.hpp Lib/VirtualIterator.hpp
Kernel/EGSubstitution.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
Kernel/EGSubstitution.o: Kernel/EGSubstitution.hpp Lib/BacktrackData.hpp
Kernel/EGSubstitution.o: Kernel/RobSubstitution.hpp Test/Output.hpp
Kernel/EqHelper.o: Kernel/EqHelper.hpp Forwards.hpp Config.hpp
Kernel/EqHelper.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp Lib/List.hpp
Kernel/EqHelper.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/EqHelper.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/EqHelper.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/EqHelper.o: Lib/PairUtils.hpp Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Kernel/EqHelper.o: Kernel/Term.hpp Lib/Allocator.hpp Lib/Portability.hpp
Kernel/EqHelper.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Kernel/EqHelper.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/EqHelper.o: Lib/Portability.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/Formula.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/MultiCounter.hpp
Kernel/Formula.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/XML.hpp
Kernel/Formula.o: Kernel/Term.hpp Forwards.hpp Config.hpp Lib/Allocator.hpp
Kernel/Formula.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Formula.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/Formula.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Formula.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Formula.o: Lib/Portability.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/Formula.o: Lib/Hash.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/Formula.o: Kernel/Formula.hpp Lib/List.hpp Kernel/Connective.hpp
Kernel/Formula.o: Kernel/SubformulaIterator.hpp Kernel/FormulaVarIterator.hpp
Kernel/FormulaUnit.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/FormulaUnit.o: Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/FormulaUnit.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/Allocator.hpp
Kernel/FormulaUnit.o: Debug/Tracer.hpp Kernel/Formula.hpp Lib/List.hpp
Kernel/FormulaUnit.o: Lib/XML.hpp Kernel/Connective.hpp
Kernel/FormulaUnit.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Kernel/FormulaVarIterator.o: Debug/Tracer.hpp Kernel/FormulaVarIterator.hpp
Kernel/FormulaVarIterator.o: Lib/MultiCounter.hpp Debug/Assertion.hpp
Kernel/FormulaVarIterator.o: Debug/Tracer.hpp Lib/XML.hpp Kernel/Formula.hpp
Kernel/FormulaVarIterator.o: Lib/List.hpp Lib/XML.hpp Kernel/Connective.hpp
Kernel/FormulaVarIterator.o: Kernel/Term.hpp Forwards.hpp Config.hpp
Kernel/FormulaVarIterator.o: Lib/Allocator.hpp Lib/Portability.hpp
Kernel/FormulaVarIterator.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/FormulaVarIterator.o: Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/FormulaVarIterator.o: Lib/List.hpp Lib/VirtualIterator.hpp
Kernel/FormulaVarIterator.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Kernel/FormulaVarIterator.o: Lib/Comparison.hpp Lib/Portability.hpp
Kernel/FormulaVarIterator.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/FormulaVarIterator.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/Inference.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Inference.o: Lib/Allocator.hpp
Kernel/KBO.o: Debug/Tracer.hpp Lib/Environment.hpp Forwards.hpp Config.hpp
Kernel/KBO.o: Lib/Comparison.hpp Lib/DArray.hpp Debug/Assertion.hpp
Kernel/KBO.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Comparison.hpp
Kernel/KBO.o: Lib/Random.hpp Lib/Reflection.hpp Lib/VirtualIterator.hpp
Kernel/KBO.o: Lib/Exception.hpp Lib/DHMap.hpp Lib/Hash.hpp Lib/Int.hpp
Kernel/KBO.o: Lib/Portability.hpp Lib/Metaiterators.hpp Lib/List.hpp
Kernel/KBO.o: Lib/Set.hpp Kernel/Term.hpp Lib/Allocator.hpp
Kernel/KBO.o: Lib/Portability.hpp Lib/XML.hpp Lib/Stack.hpp
Kernel/KBO.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/MatchTag.hpp
Kernel/KBO.o: Lib/BitUtils.hpp Kernel/KBO.hpp Kernel/Ordering.hpp
Kernel/KBO.o: Kernel/Signature.hpp Lib/Map.hpp
Kernel/LiteralSelector.o: Lib/Exception.hpp Kernel/Term.hpp Forwards.hpp
Kernel/LiteralSelector.o: Config.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/LiteralSelector.o: Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/LiteralSelector.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/LiteralSelector.o: Lib/Stack.hpp Lib/Allocator.hpp
Kernel/LiteralSelector.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/LiteralSelector.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/LiteralSelector.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/LiteralSelector.o: Lib/Portability.hpp Lib/Metaiterators.hpp
Kernel/LiteralSelector.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp
Kernel/LiteralSelector.o: Lib/BitUtils.hpp Kernel/Clause.hpp
Kernel/LiteralSelector.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Kernel/LiteralSelector.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Kernel/LiteralSelector.o: Kernel/LiteralSelector.hpp Lib/MultiColumnMap.hpp
Kernel/LiteralSelector.o: Lib/BitUtils.hpp Kernel/MaximalLiteralSelector.hpp
Kernel/LiteralSelector.o: Lib/SmartPtr.hpp Kernel/Ordering.hpp
Kernel/LiteralSelector.o: Kernel/BestLiteralSelector.hpp Lib/DArray.hpp
Kernel/LiteralSelector.o: Lib/Random.hpp Lib/Set.hpp
Kernel/LiteralSelector.o: Kernel/LiteralComparators.hpp Lib/Int.hpp
Kernel/MLMatcher.o: Lib/BacktrackData.hpp Lib/BacktrackIterators.hpp
Kernel/MLMatcher.o: Lib/DArray.hpp Forwards.hpp Config.hpp
Kernel/MLMatcher.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/MLMatcher.o: Debug/Tracer.hpp Lib/Comparison.hpp Lib/Random.hpp
Kernel/MLMatcher.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Kernel/MLMatcher.o: Lib/Exception.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Kernel/MLMatcher.o: Lib/List.hpp Lib/Int.hpp Lib/Portability.hpp
Kernel/MLMatcher.o: Lib/Metaiterators.hpp Lib/BinaryHeap.hpp Lib/DArray.hpp
Kernel/MLMatcher.o: Lib/DHMap.hpp Lib/Hash.hpp Lib/Hash.hpp Lib/Int.hpp
Kernel/MLMatcher.o: Lib/Metaarrays.hpp Lib/PairUtils.hpp Lib/Metaarrays.hpp
Kernel/MLMatcher.o: Lib/Stack.hpp Lib/TriangularArray.hpp Kernel/Clause.hpp
Kernel/MLMatcher.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/MLMatcher.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Kernel/MLMatcher.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Term.hpp
Kernel/MLMatcher.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/MLMatcher.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/Matcher.hpp
Kernel/MLMatcher.o: Lib/VirtualIterator.hpp Kernel/Term.hpp
Kernel/MLMatcher.o: Kernel/MLMatcher.hpp Test/Output.hpp
Kernel/MatchTag.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/MatchTag.o: Debug/Assertion.hpp Debug/Tracer.hpp Kernel/Term.hpp
Kernel/MatchTag.o: Forwards.hpp Config.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/MatchTag.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/MatchTag.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/MatchTag.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/MatchTag.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Metaiterators.hpp
Kernel/MatchTag.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp
Kernel/MatchTag.o: Lib/BitUtils.hpp
Kernel/MaximalLiteralSelector.o: Lib/List.hpp Kernel/Term.hpp Forwards.hpp
Kernel/MaximalLiteralSelector.o: Config.hpp Debug/Assertion.hpp
Kernel/MaximalLiteralSelector.o: Debug/Tracer.hpp Debug/Tracer.hpp
Kernel/MaximalLiteralSelector.o: Lib/Allocator.hpp Lib/Portability.hpp
Kernel/MaximalLiteralSelector.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Kernel/MaximalLiteralSelector.o: Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/MaximalLiteralSelector.o: Lib/List.hpp Lib/VirtualIterator.hpp
Kernel/MaximalLiteralSelector.o: Lib/Exception.hpp Lib/Reflection.hpp
Kernel/MaximalLiteralSelector.o: Lib/Int.hpp Lib/Comparison.hpp
Kernel/MaximalLiteralSelector.o: Lib/Portability.hpp Lib/Metaiterators.hpp
Kernel/MaximalLiteralSelector.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp
Kernel/MaximalLiteralSelector.o: Lib/BitUtils.hpp Kernel/Clause.hpp
Kernel/MaximalLiteralSelector.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Kernel/MaximalLiteralSelector.o: Lib/DHMap.hpp Kernel/Unit.hpp
Kernel/MaximalLiteralSelector.o: Kernel/MaximalLiteralSelector.hpp
Kernel/MaximalLiteralSelector.o: Lib/SmartPtr.hpp Kernel/Ordering.hpp
Kernel/MaximalLiteralSelector.o: Kernel/LiteralSelector.hpp
Kernel/MaximalLiteralSelector.o: Lib/MultiColumnMap.hpp Lib/BitUtils.hpp
Kernel/Ordering.o: Forwards.hpp Config.hpp Lib/List.hpp Lib/SmartPtr.hpp
Kernel/Ordering.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Kernel/Ordering.o: Lib/Environment.hpp Lib/Exception.hpp Shell/Options.hpp
Kernel/Ordering.o: Lib/Allocator.hpp Lib/XML.hpp Kernel/Ordering.hpp
Kernel/Ordering.o: Kernel/KBO.hpp Lib/DArray.hpp Lib/Allocator.hpp
Kernel/Ordering.o: Lib/Comparison.hpp Lib/Random.hpp Lib/Reflection.hpp
Kernel/Ordering.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Renaming.o: Lib/DArray.hpp Forwards.hpp Config.hpp Debug/Assertion.hpp
Kernel/Renaming.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/Renaming.o: Lib/Comparison.hpp Lib/Random.hpp Lib/Reflection.hpp
Kernel/Renaming.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Renaming.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
Kernel/Renaming.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/Renaming.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Kernel/Renaming.o: Lib/List.hpp Lib/Int.hpp Lib/Portability.hpp
Kernel/Renaming.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/Renaming.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/Renaming.o: Kernel/SubstHelper.hpp Kernel/Term.hpp Kernel/Renaming.hpp
Kernel/Renaming.o: Lib/DHMap.hpp Lib/VirtualIterator.hpp Lib/Int.hpp
Kernel/RobSubstitution.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Kernel/RobSubstitution.o: Lib/Hash.hpp Lib/DArray.hpp Debug/Assertion.hpp
Kernel/RobSubstitution.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/RobSubstitution.o: Lib/Comparison.hpp Lib/Random.hpp
Kernel/RobSubstitution.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Kernel/RobSubstitution.o: Lib/Exception.hpp Lib/List.hpp Lib/Random.hpp
Kernel/RobSubstitution.o: Lib/DHMultiset.hpp Lib/Hash.hpp Lib/DHMap.hpp
Kernel/RobSubstitution.o: Lib/DHMap.hpp Lib/SkipList.hpp
Kernel/RobSubstitution.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/RobSubstitution.o: Lib/Portability.hpp Lib/Int.hpp Kernel/Term.hpp
Kernel/RobSubstitution.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/RobSubstitution.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/RobSubstitution.o: Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/RobSubstitution.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Kernel/RobSubstitution.o: Kernel/Clause.hpp Lib/Reflection.hpp
Kernel/RobSubstitution.o: Lib/InverseLookup.hpp Kernel/Unit.hpp
Kernel/RobSubstitution.o: Kernel/Renaming.hpp Lib/VirtualIterator.hpp
Kernel/RobSubstitution.o: Indexing/TermSharing.hpp Lib/Set.hpp
Kernel/RobSubstitution.o: Kernel/Term.hpp Kernel/RobSubstitution.hpp
Kernel/RobSubstitution.o: Lib/BacktrackData.hpp Test/Output.hpp
Kernel/Signature.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/Signature.o: Debug/Assertion.hpp Debug/Tracer.hpp Kernel/Signature.hpp
Kernel/Signature.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Stack.hpp
Kernel/Signature.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Kernel/Signature.o: Forwards.hpp Config.hpp Lib/VirtualIterator.hpp
Kernel/Signature.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Kernel/Signature.o: Lib/Map.hpp Lib/Hash.hpp
Kernel/SubformulaIterator.o: Debug/Tracer.hpp Kernel/SubformulaIterator.hpp
Kernel/SubformulaIterator.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp
Kernel/SubformulaIterator.o: Kernel/Connective.hpp
Kernel/Substitution.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/Substitution.o: Debug/Assertion.hpp Debug/Tracer.hpp Kernel/Term.hpp
Kernel/Substitution.o: Forwards.hpp Config.hpp Debug/Tracer.hpp
Kernel/Substitution.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/Substitution.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/Substitution.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/Substitution.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Substitution.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Metaiterators.hpp
Kernel/Substitution.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp
Kernel/Substitution.o: Lib/BitUtils.hpp Kernel/Substitution.hpp
Kernel/Substitution.o: Lib/Random.hpp Lib/Environment.hpp
Kernel/Term.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Environment.hpp
Kernel/Term.o: Forwards.hpp Config.hpp Lib/Stack.hpp Debug/Assertion.hpp
Kernel/Term.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/Term.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Term.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Term.o: Lib/Portability.hpp Lib/Set.hpp Lib/Int.hpp
Kernel/Term.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Kernel/Term.o: Kernel/Substitution.hpp Lib/Random.hpp Kernel/Term.hpp
Kernel/Term.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Term.o: Lib/Metaiterators.hpp Lib/Set.hpp Kernel/MatchTag.hpp
Kernel/Term.o: Lib/BitUtils.hpp Kernel/Ordering.hpp Indexing/TermSharing.hpp
Kernel/Term.o: Kernel/Term.hpp
Kernel/TermFunIterator.o: Debug/Tracer.hpp Kernel/Term.hpp Forwards.hpp
Kernel/TermFunIterator.o: Config.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/TermFunIterator.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/TermFunIterator.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermFunIterator.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/TermFunIterator.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/TermFunIterator.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/TermFunIterator.o: Lib/Portability.hpp Lib/Metaiterators.hpp
Kernel/TermFunIterator.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp
Kernel/TermFunIterator.o: Lib/BitUtils.hpp Kernel/TermFunIterator.hpp
Kernel/TermVarIterator.o: Debug/Tracer.hpp Kernel/Term.hpp Forwards.hpp
Kernel/TermVarIterator.o: Config.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/TermVarIterator.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/TermVarIterator.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermVarIterator.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/TermVarIterator.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/TermVarIterator.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/TermVarIterator.o: Lib/Portability.hpp Lib/Metaiterators.hpp
Kernel/TermVarIterator.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp
Kernel/TermVarIterator.o: Lib/BitUtils.hpp Kernel/TermVarIterator.hpp
Kernel/Unit.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Unit.o: Lib/Portability.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/Unit.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/Allocator.hpp
Kernel/Unit.o: Kernel/Unit.hpp Lib/List.hpp
Indexing/ClauseVariantIndex.o: Lib/List.hpp Lib/Metaiterators.hpp
Indexing/ClauseVariantIndex.o: Forwards.hpp Config.hpp Lib/List.hpp
Indexing/ClauseVariantIndex.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/ClauseVariantIndex.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/ClauseVariantIndex.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/ClauseVariantIndex.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Indexing/ClauseVariantIndex.o: Kernel/Clause.hpp Lib/Allocator.hpp
Indexing/ClauseVariantIndex.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Indexing/ClauseVariantIndex.o: Lib/DHMap.hpp Kernel/Unit.hpp
Indexing/ClauseVariantIndex.o: Kernel/MLMatcher.hpp Kernel/Term.hpp
Indexing/ClauseVariantIndex.o: Lib/Portability.hpp Lib/XML.hpp
Indexing/ClauseVariantIndex.o: Lib/Comparison.hpp Lib/Stack.hpp
Indexing/ClauseVariantIndex.o: Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/ClauseVariantIndex.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/ClauseVariantIndex.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/ClauseVariantIndex.o: Indexing/LiteralMiniIndex.hpp Lib/DArray.hpp
Indexing/ClauseVariantIndex.o: Lib/Random.hpp Kernel/Matcher.hpp
Indexing/ClauseVariantIndex.o: Lib/BacktrackData.hpp Lib/DHMap.hpp
Indexing/ClauseVariantIndex.o: Lib/Hash.hpp Lib/VirtualIterator.hpp
Indexing/ClauseVariantIndex.o: Indexing/LiteralSubstitutionTree.hpp
Indexing/ClauseVariantIndex.o: Indexing/LiteralIndexingStructure.hpp
Indexing/ClauseVariantIndex.o: Indexing/Index.hpp Lib/Event.hpp
Indexing/ClauseVariantIndex.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/ClauseVariantIndex.o: Saturation/ClauseContainer.hpp
Indexing/ClauseVariantIndex.o: Saturation/Limits.hpp
Indexing/ClauseVariantIndex.o: Indexing/ResultSubstitution.hpp
Indexing/ClauseVariantIndex.o: Lib/SmartPtr.hpp Indexing/SubstitutionTree.hpp
Indexing/ClauseVariantIndex.o: Lib/Int.hpp Lib/SkipList.hpp
Indexing/ClauseVariantIndex.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/ClauseVariantIndex.o: Lib/ArrayMap.hpp Lib/DArray.hpp Lib/Array.hpp
Indexing/ClauseVariantIndex.o: Kernel/DoubleSubstitution.hpp Kernel/Term.hpp
Indexing/ClauseVariantIndex.o: Kernel/EGSubstitution.hpp
Indexing/ClauseVariantIndex.o: Kernel/RobSubstitution.hpp
Indexing/ClauseVariantIndex.o: Kernel/RobSubstitution.hpp Kernel/Renaming.hpp
Indexing/ClauseVariantIndex.o: Test/Output.hpp
Indexing/ClauseVariantIndex.o: Indexing/ClauseVariantIndex.hpp
Indexing/Index.o: Indexing/Index.hpp Forwards.hpp Config.hpp Lib/Event.hpp
Indexing/Index.o: Lib/List.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/Index.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/VirtualIterator.hpp
Indexing/Index.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/SmartPtr.hpp
Indexing/Index.o: Lib/Exception.hpp Lib/VirtualIterator.hpp
Indexing/Index.o: Saturation/ClauseContainer.hpp Lib/Stack.hpp
Indexing/Index.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/Index.o: Lib/Portability.hpp Saturation/Limits.hpp Kernel/Clause.hpp
Indexing/Index.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Indexing/Index.o: Lib/Hash.hpp Lib/Reflection.hpp Lib/InverseLookup.hpp
Indexing/Index.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Indexing/Index.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Indexing/Index.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/Index.o: Lib/Comparison.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/IndexManager.o: Lib/Exception.hpp Saturation/SaturationAlgorithm.hpp
Indexing/IndexManager.o: Forwards.hpp Config.hpp Kernel/Clause.hpp
Indexing/IndexManager.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/IndexManager.o: Lib/Metaiterators.hpp Lib/List.hpp
Indexing/IndexManager.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/IndexManager.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Indexing/IndexManager.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp
Indexing/IndexManager.o: Lib/Hash.hpp Lib/Reflection.hpp
Indexing/IndexManager.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp
Indexing/IndexManager.o: Lib/List.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/IndexManager.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Indexing/IndexManager.o: Indexing/Index.hpp Lib/VirtualIterator.hpp
Indexing/IndexManager.o: Saturation/ClauseContainer.hpp Lib/Stack.hpp
Indexing/IndexManager.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/IndexManager.o: Lib/Portability.hpp Saturation/Limits.hpp
Indexing/IndexManager.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Indexing/IndexManager.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/IndexManager.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Indexing/IndexManager.o: Lib/BitUtils.hpp Inferences/InferenceEngine.hpp
Indexing/IndexManager.o: Saturation/SaturationResult.hpp Shell/Statistics.hpp
Indexing/IndexManager.o: Lib/Environment.hpp Indexing/LiteralIndex.hpp
Indexing/IndexManager.o: Indexing/LiteralSubstitutionTree.hpp
Indexing/IndexManager.o: Indexing/LiteralIndexingStructure.hpp
Indexing/IndexManager.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/IndexManager.o: Lib/SkipList.hpp Lib/Random.hpp Lib/BinaryHeap.hpp
Indexing/IndexManager.o: Lib/Metaiterators.hpp Lib/BacktrackData.hpp
Indexing/IndexManager.o: Lib/ArrayMap.hpp Lib/DArray.hpp Lib/Array.hpp
Indexing/IndexManager.o: Kernel/DoubleSubstitution.hpp Kernel/Term.hpp
Indexing/IndexManager.o: Kernel/EGSubstitution.hpp Kernel/RobSubstitution.hpp
Indexing/IndexManager.o: Kernel/RobSubstitution.hpp Kernel/Renaming.hpp
Indexing/IndexManager.o: Test/Output.hpp Indexing/TermIndex.hpp
Indexing/IndexManager.o: Indexing/TermSubstitutionTree.hpp
Indexing/IndexManager.o: Indexing/TermIndexingStructure.hpp
Indexing/IndexManager.o: Indexing/IndexManager.hpp
Indexing/LiteralIndex.o: Kernel/Clause.hpp Forwards.hpp Config.hpp
Indexing/LiteralIndex.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/LiteralIndex.o: Lib/Metaiterators.hpp Lib/List.hpp
Indexing/LiteralIndex.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/LiteralIndex.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Indexing/LiteralIndex.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp
Indexing/LiteralIndex.o: Lib/Hash.hpp Lib/Reflection.hpp
Indexing/LiteralIndex.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp
Indexing/LiteralIndex.o: Lib/List.hpp Indexing/LiteralIndexingStructure.hpp
Indexing/LiteralIndex.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/LiteralIndex.o: Lib/Exception.hpp Lib/VirtualIterator.hpp
Indexing/LiteralIndex.o: Saturation/ClauseContainer.hpp Lib/Stack.hpp
Indexing/LiteralIndex.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/LiteralIndex.o: Lib/Portability.hpp Saturation/Limits.hpp
Indexing/LiteralIndex.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Indexing/LiteralIndex.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/LiteralIndex.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Indexing/LiteralIndex.o: Lib/BitUtils.hpp Indexing/LiteralIndex.hpp
Indexing/LiteralMiniIndex.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/LiteralMiniIndex.o: Indexing/LiteralMiniIndex.hpp Forwards.hpp
Indexing/LiteralMiniIndex.o: Config.hpp Lib/DArray.hpp Debug/Assertion.hpp
Indexing/LiteralMiniIndex.o: Debug/Tracer.hpp Lib/Allocator.hpp
Indexing/LiteralMiniIndex.o: Lib/Comparison.hpp Lib/Random.hpp
Indexing/LiteralMiniIndex.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Indexing/LiteralMiniIndex.o: Lib/Exception.hpp Kernel/Clause.hpp
Indexing/LiteralMiniIndex.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Indexing/LiteralMiniIndex.o: Lib/Hash.hpp Lib/Reflection.hpp
Indexing/LiteralMiniIndex.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Indexing/LiteralMiniIndex.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Matcher.hpp
Indexing/LiteralMiniIndex.o: Lib/BacktrackData.hpp Lib/DHMap.hpp Lib/Hash.hpp
Indexing/LiteralMiniIndex.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/LiteralMiniIndex.o: Lib/Portability.hpp Lib/VirtualIterator.hpp
Indexing/LiteralMiniIndex.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/LiteralMiniIndex.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Indexing/LiteralMiniIndex.o: Lib/BitUtils.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Environment.hpp Forwards.hpp
Indexing/LiteralSubstitutionTree.o: Config.hpp Lib/Metaiterators.hpp
Indexing/LiteralSubstitutionTree.o: Lib/List.hpp Debug/Assertion.hpp
Indexing/LiteralSubstitutionTree.o: Debug/Tracer.hpp Lib/Allocator.hpp
Indexing/LiteralSubstitutionTree.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Exception.hpp Lib/Reflection.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Set.hpp Lib/Hash.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/Signature.hpp Lib/Allocator.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Int.hpp Lib/Comparison.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Portability.hpp Lib/Map.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/Term.hpp Lib/Portability.hpp
Indexing/LiteralSubstitutionTree.o: Lib/XML.hpp Lib/Comparison.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/LiteralSubstitutionTree.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/LiteralIndexingStructure.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/Index.hpp Lib/Event.hpp
Indexing/LiteralSubstitutionTree.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/LiteralSubstitutionTree.o: Lib/VirtualIterator.hpp
Indexing/LiteralSubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/LiteralSubstitutionTree.o: Saturation/Limits.hpp Kernel/Clause.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Indexing/LiteralSubstitutionTree.o: Lib/DHMap.hpp Kernel/Unit.hpp
Indexing/LiteralSubstitutionTree.o: Lib/List.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/ResultSubstitution.hpp
Indexing/LiteralSubstitutionTree.o: Lib/SmartPtr.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/LiteralSubstitutionTree.o: Lib/SkipList.hpp Lib/Random.hpp
Indexing/LiteralSubstitutionTree.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/LiteralSubstitutionTree.o: Lib/BacktrackData.hpp Lib/ArrayMap.hpp
Indexing/LiteralSubstitutionTree.o: Lib/DArray.hpp Lib/Array.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/DoubleSubstitution.hpp
Indexing/LiteralSubstitutionTree.o: Lib/DHMap.hpp Kernel/Term.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/EGSubstitution.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/RobSubstitution.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/RobSubstitution.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/Renaming.hpp Test/Output.hpp
Indexing/ResultSubstitution.o: Kernel/RobSubstitution.hpp
Indexing/ResultSubstitution.o: Kernel/EGSubstitution.hpp Forwards.hpp
Indexing/ResultSubstitution.o: Config.hpp Lib/DHMap.hpp Debug/Assertion.hpp
Indexing/ResultSubstitution.o: Debug/Tracer.hpp Lib/Allocator.hpp
Indexing/ResultSubstitution.o: Debug/Tracer.hpp Lib/Exception.hpp
Indexing/ResultSubstitution.o: Lib/Hash.hpp Lib/VirtualIterator.hpp
Indexing/ResultSubstitution.o: Lib/Reflection.hpp Lib/Stack.hpp
Indexing/ResultSubstitution.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Indexing/ResultSubstitution.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/ResultSubstitution.o: Lib/BacktrackData.hpp Kernel/Term.hpp
Indexing/ResultSubstitution.o: Lib/Allocator.hpp Lib/Portability.hpp
Indexing/ResultSubstitution.o: Lib/XML.hpp Lib/Comparison.hpp
Indexing/ResultSubstitution.o: Lib/Metaiterators.hpp Lib/Set.hpp
Indexing/ResultSubstitution.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/ResultSubstitution.o: Kernel/RobSubstitution.hpp
Indexing/ResultSubstitution.o: Indexing/ResultSubstitution.hpp
Indexing/ResultSubstitution.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Indexing/SubstitutionTree.o: Kernel/Matcher.hpp Forwards.hpp Config.hpp
Indexing/SubstitutionTree.o: Lib/BacktrackData.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/SubstitutionTree.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/SubstitutionTree.o: Lib/Exception.hpp Lib/Hash.hpp
Indexing/SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Reflection.hpp
Indexing/SubstitutionTree.o: Lib/Hash.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Indexing/SubstitutionTree.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/SubstitutionTree.o: Lib/Portability.hpp Lib/VirtualIterator.hpp
Indexing/SubstitutionTree.o: Kernel/Term.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree.o: Lib/Portability.hpp Lib/XML.hpp
Indexing/SubstitutionTree.o: Lib/Comparison.hpp Lib/Metaiterators.hpp
Indexing/SubstitutionTree.o: Lib/Set.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/SubstitutionTree.o: Kernel/Renaming.hpp Kernel/Term.hpp
Indexing/SubstitutionTree.o: Kernel/SubstHelper.hpp Lib/DArray.hpp
Indexing/SubstitutionTree.o: Lib/Random.hpp Lib/BinaryHeap.hpp
Indexing/SubstitutionTree.o: Lib/Metaiterators.hpp Lib/Environment.hpp
Indexing/SubstitutionTree.o: Lib/Recycler.hpp Lib/Stack.hpp Lib/DArray.hpp
Indexing/SubstitutionTree.o: Lib/DHMultiset.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree.o: Indexing/TermSharing.hpp Lib/Set.hpp
Indexing/SubstitutionTree.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Int.hpp
Indexing/SubstitutionTree.o: Test/Output.hpp Indexing/SubstitutionTree.hpp
Indexing/SubstitutionTree.o: Lib/List.hpp Lib/SkipList.hpp Lib/ArrayMap.hpp
Indexing/SubstitutionTree.o: Lib/Array.hpp Kernel/DoubleSubstitution.hpp
Indexing/SubstitutionTree.o: Kernel/EGSubstitution.hpp
Indexing/SubstitutionTree.o: Kernel/RobSubstitution.hpp
Indexing/SubstitutionTree.o: Kernel/RobSubstitution.hpp Kernel/Clause.hpp
Indexing/SubstitutionTree.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Indexing/SubstitutionTree.o: Kernel/Unit.hpp Indexing/Index.hpp Lib/Event.hpp
Indexing/SubstitutionTree.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/SubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/SubstitutionTree.o: Saturation/Limits.hpp
Indexing/SubstitutionTree.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/VirtualIterator.hpp Lib/List.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/SkipList.hpp Debug/Assertion.hpp
Indexing/SubstitutionTree_Nodes.o: Debug/Tracer.hpp Debug/Tracer.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Allocator.hpp Lib/Comparison.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Random.hpp Lib/BacktrackData.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/List.hpp Forwards.hpp Config.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Reflection.hpp Lib/Int.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Portability.hpp Lib/DHMultiset.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Hash.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Metaiterators.hpp Lib/Set.hpp
Indexing/SubstitutionTree_Nodes.o: Indexing/Index.hpp Lib/Event.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/SubstitutionTree_Nodes.o: Saturation/ClauseContainer.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Stack.hpp Saturation/Limits.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/Clause.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/Unit.hpp
Indexing/SubstitutionTree_Nodes.o: Indexing/ResultSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Portability.hpp Lib/XML.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BitUtils.hpp
Indexing/SubstitutionTree_Nodes.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BacktrackData.hpp Lib/ArrayMap.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/DArray.hpp Lib/Array.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/DoubleSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/DHMap.hpp Kernel/Term.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/EGSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/RobSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/RobSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/Renaming.hpp Test/Output.hpp
Indexing/TermIndex.o: Kernel/Clause.hpp Forwards.hpp Config.hpp
Indexing/TermIndex.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/TermIndex.o: Lib/Metaiterators.hpp Lib/List.hpp Debug/Assertion.hpp
Indexing/TermIndex.o: Debug/Tracer.hpp Lib/Allocator.hpp
Indexing/TermIndex.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/TermIndex.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Indexing/TermIndex.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Indexing/TermIndex.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Term.hpp
Indexing/TermIndex.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Indexing/TermIndex.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/TermIndex.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/TermIndex.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/TermIndex.o: Kernel/Ordering.hpp Kernel/EqHelper.hpp
Indexing/TermIndex.o: Lib/VirtualIterator.hpp Lib/PairUtils.hpp
Indexing/TermIndex.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Indexing/TermIndex.o: Kernel/Term.hpp Indexing/TermIndexingStructure.hpp
Indexing/TermIndex.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/TermIndex.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
Indexing/TermIndex.o: Saturation/Limits.hpp Indexing/ResultSubstitution.hpp
Indexing/TermIndex.o: Lib/SmartPtr.hpp Indexing/TermIndex.hpp
Indexing/TermSharing.o: Kernel/Term.hpp Forwards.hpp Config.hpp
Indexing/TermSharing.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Indexing/TermSharing.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/TermSharing.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Indexing/TermSharing.o: Lib/BacktrackData.hpp Lib/List.hpp
Indexing/TermSharing.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/TermSharing.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/TermSharing.o: Lib/Portability.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Indexing/TermSharing.o: Lib/Hash.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/TermSharing.o: Indexing/TermSharing.hpp Lib/Set.hpp
Indexing/TermSubstitutionTree.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Indexing/TermSubstitutionTree.o: Lib/Metaiterators.hpp Lib/List.hpp
Indexing/TermSubstitutionTree.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/TermSubstitutionTree.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/TermSubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/TermSubstitutionTree.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Indexing/TermSubstitutionTree.o: Lib/SmartPtr.hpp Lib/Random.hpp
Indexing/TermSubstitutionTree.o: Kernel/Signature.hpp Lib/Allocator.hpp
Indexing/TermSubstitutionTree.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Indexing/TermSubstitutionTree.o: Lib/Int.hpp Lib/Comparison.hpp
Indexing/TermSubstitutionTree.o: Lib/Portability.hpp Lib/Map.hpp
Indexing/TermSubstitutionTree.o: Kernel/Term.hpp Lib/Portability.hpp
Indexing/TermSubstitutionTree.o: Lib/XML.hpp Lib/Comparison.hpp
Indexing/TermSubstitutionTree.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Indexing/TermSubstitutionTree.o: Kernel/Curryfier.hpp Lib/DHMap.hpp
Indexing/TermSubstitutionTree.o: Lib/DArray.hpp Lib/Random.hpp
Indexing/TermSubstitutionTree.o: Lib/ArrayMap.hpp Lib/DArray.hpp
Indexing/TermSubstitutionTree.o: Indexing/TermSharing.hpp Lib/Set.hpp
Indexing/TermSubstitutionTree.o: Kernel/Term.hpp Kernel/Signature.hpp
Indexing/TermSubstitutionTree.o: Indexing/TermSubstitutionTree.hpp
Indexing/TermSubstitutionTree.o: Kernel/Renaming.hpp Lib/VirtualIterator.hpp
Indexing/TermSubstitutionTree.o: Lib/SkipList.hpp Indexing/Index.hpp
Indexing/TermSubstitutionTree.o: Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/TermSubstitutionTree.o: Lib/Exception.hpp
Indexing/TermSubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/TermSubstitutionTree.o: Saturation/Limits.hpp Kernel/Clause.hpp
Indexing/TermSubstitutionTree.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Indexing/TermSubstitutionTree.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Indexing/TermSubstitutionTree.o: Indexing/ResultSubstitution.hpp
Indexing/TermSubstitutionTree.o: Indexing/TermIndexingStructure.hpp
Indexing/TermSubstitutionTree.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/TermSubstitutionTree.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
Indexing/TermSubstitutionTree.o: Lib/BacktrackData.hpp Lib/Array.hpp
Indexing/TermSubstitutionTree.o: Kernel/DoubleSubstitution.hpp
Indexing/TermSubstitutionTree.o: Kernel/EGSubstitution.hpp
Indexing/TermSubstitutionTree.o: Kernel/RobSubstitution.hpp
Indexing/TermSubstitutionTree.o: Kernel/RobSubstitution.hpp Test/Output.hpp
Inferences/BackwardDemodulation.o: Lib/DHMultiset.hpp Debug/Assertion.hpp
Inferences/BackwardDemodulation.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/BackwardDemodulation.o: Debug/Tracer.hpp Lib/Exception.hpp
Inferences/BackwardDemodulation.o: Lib/Hash.hpp Lib/DHMap.hpp
Inferences/BackwardDemodulation.o: Lib/VirtualIterator.hpp Forwards.hpp
Inferences/BackwardDemodulation.o: Config.hpp Lib/Reflection.hpp
Inferences/BackwardDemodulation.o: Lib/Environment.hpp Lib/Int.hpp
Inferences/BackwardDemodulation.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/BackwardDemodulation.o: Lib/List.hpp Lib/Metaiterators.hpp
Inferences/BackwardDemodulation.o: Lib/List.hpp Lib/Set.hpp
Inferences/BackwardDemodulation.o: Lib/VirtualIterator.hpp Kernel/Term.hpp
Inferences/BackwardDemodulation.o: Lib/Allocator.hpp Lib/Portability.hpp
Inferences/BackwardDemodulation.o: Lib/XML.hpp Lib/Comparison.hpp
Inferences/BackwardDemodulation.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Inferences/BackwardDemodulation.o: Lib/Int.hpp Kernel/MatchTag.hpp
Inferences/BackwardDemodulation.o: Lib/BitUtils.hpp Kernel/Clause.hpp
Inferences/BackwardDemodulation.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Inferences/BackwardDemodulation.o: Kernel/Unit.hpp Kernel/EqHelper.hpp
Inferences/BackwardDemodulation.o: Lib/PairUtils.hpp Lib/Metaiterators.hpp
Inferences/BackwardDemodulation.o: Lib/Metaarrays.hpp Kernel/Term.hpp
Inferences/BackwardDemodulation.o: Kernel/Renaming.hpp Lib/DHMap.hpp
Inferences/BackwardDemodulation.o: Kernel/Ordering.hpp Kernel/Inference.hpp
Inferences/BackwardDemodulation.o: Kernel/Unit.hpp Indexing/Index.hpp
Inferences/BackwardDemodulation.o: Lib/Event.hpp Lib/SmartPtr.hpp
Inferences/BackwardDemodulation.o: Lib/Exception.hpp
Inferences/BackwardDemodulation.o: Saturation/ClauseContainer.hpp
Inferences/BackwardDemodulation.o: Saturation/Limits.hpp
Inferences/BackwardDemodulation.o: Indexing/ResultSubstitution.hpp
Inferences/BackwardDemodulation.o: Lib/SmartPtr.hpp Indexing/TermIndex.hpp
Inferences/BackwardDemodulation.o: Indexing/Index.hpp
Inferences/BackwardDemodulation.o: Indexing/IndexManager.hpp
Inferences/BackwardDemodulation.o: Saturation/SaturationAlgorithm.hpp
Inferences/BackwardDemodulation.o: Inferences/InferenceEngine.hpp
Inferences/BackwardDemodulation.o: Saturation/SaturationResult.hpp
Inferences/BackwardDemodulation.o: Shell/Statistics.hpp
Inferences/BackwardDemodulation.o: Inferences/BackwardDemodulation.hpp
Inferences/BackwardDemodulation.o: Inferences/InferenceEngine.hpp
Inferences/BinaryResolution.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Inferences/BinaryResolution.o: Lib/Int.hpp Lib/Comparison.hpp
Inferences/BinaryResolution.o: Lib/Portability.hpp Debug/Assertion.hpp
Inferences/BinaryResolution.o: Debug/Tracer.hpp Lib/Metaiterators.hpp
Inferences/BinaryResolution.o: Lib/List.hpp Lib/Allocator.hpp
Inferences/BinaryResolution.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Inferences/BinaryResolution.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/BinaryResolution.o: Lib/Set.hpp Lib/Hash.hpp Lib/PairUtils.hpp
Inferences/BinaryResolution.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/BinaryResolution.o: Lib/VirtualIterator.hpp Shell/Statistics.hpp
Inferences/BinaryResolution.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/BinaryResolution.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Inferences/BinaryResolution.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Inferences/BinaryResolution.o: Kernel/Unit.hpp Kernel/Inference.hpp
Inferences/BinaryResolution.o: Indexing/Index.hpp Lib/Event.hpp
Inferences/BinaryResolution.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/BinaryResolution.o: Saturation/ClauseContainer.hpp Lib/Stack.hpp
Inferences/BinaryResolution.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/BinaryResolution.o: Saturation/Limits.hpp
Inferences/BinaryResolution.o: Indexing/ResultSubstitution.hpp
Inferences/BinaryResolution.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Inferences/BinaryResolution.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/BinaryResolution.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Inferences/BinaryResolution.o: Lib/BitUtils.hpp Indexing/LiteralIndex.hpp
Inferences/BinaryResolution.o: Indexing/Index.hpp Indexing/IndexManager.hpp
Inferences/BinaryResolution.o: Lib/DHMap.hpp
Inferences/BinaryResolution.o: Saturation/SaturationAlgorithm.hpp
Inferences/BinaryResolution.o: Inferences/InferenceEngine.hpp
Inferences/BinaryResolution.o: Saturation/SaturationResult.hpp
Inferences/BinaryResolution.o: Inferences/BinaryResolution.hpp
Inferences/BinaryResolution.o: Inferences/InferenceEngine.hpp
Inferences/Condensation.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp
Inferences/Condensation.o: Forwards.hpp Config.hpp Lib/List.hpp
Inferences/Condensation.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/Condensation.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/Condensation.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/Condensation.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Inferences/Condensation.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Inferences/Condensation.o: Lib/DArray.hpp Lib/Random.hpp Kernel/Term.hpp
Inferences/Condensation.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Inferences/Condensation.o: Lib/Comparison.hpp Lib/Stack.hpp
Inferences/Condensation.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/Condensation.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/Condensation.o: Kernel/Clause.hpp Lib/Reflection.hpp
Inferences/Condensation.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/Condensation.o: Kernel/Unit.hpp Lib/List.hpp Kernel/MLMatcher.hpp
Inferences/Condensation.o: Kernel/Ordering.hpp Kernel/Inference.hpp
Inferences/Condensation.o: Kernel/Unit.hpp Kernel/Renaming.hpp Lib/DHMap.hpp
Inferences/Condensation.o: Kernel/Term.hpp Kernel/Matcher.hpp
Inferences/Condensation.o: Lib/BacktrackData.hpp Lib/Hash.hpp
Inferences/Condensation.o: Kernel/RobSubstitution.hpp
Inferences/Condensation.o: Indexing/LiteralMiniIndex.hpp
Inferences/Condensation.o: Saturation/SaturationAlgorithm.hpp Lib/Event.hpp
Inferences/Condensation.o: Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Inferences/Condensation.o: Indexing/Index.hpp Lib/Exception.hpp
Inferences/Condensation.o: Saturation/ClauseContainer.hpp
Inferences/Condensation.o: Saturation/Limits.hpp
Inferences/Condensation.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Inferences/Condensation.o: Inferences/InferenceEngine.hpp
Inferences/Condensation.o: Saturation/SaturationResult.hpp
Inferences/Condensation.o: Shell/Statistics.hpp Lib/Environment.hpp
Inferences/Condensation.o: Inferences/Condensation.hpp Indexing/TermIndex.hpp
Inferences/Condensation.o: Inferences/InferenceEngine.hpp
Inferences/EqualityFactoring.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp
Inferences/EqualityFactoring.o: Forwards.hpp Config.hpp Lib/List.hpp
Inferences/EqualityFactoring.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/EqualityFactoring.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/EqualityFactoring.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/EqualityFactoring.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Inferences/EqualityFactoring.o: Lib/PairUtils.hpp Lib/Metaiterators.hpp
Inferences/EqualityFactoring.o: Lib/Metaarrays.hpp Lib/Environment.hpp
Inferences/EqualityFactoring.o: Shell/Statistics.hpp Kernel/Clause.hpp
Inferences/EqualityFactoring.o: Lib/Allocator.hpp Lib/Reflection.hpp
Inferences/EqualityFactoring.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/EqualityFactoring.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Unit.hpp
Inferences/EqualityFactoring.o: Kernel/Inference.hpp
Inferences/EqualityFactoring.o: Kernel/RobSubstitution.hpp
Inferences/EqualityFactoring.o: Kernel/EqHelper.hpp Kernel/Term.hpp
Inferences/EqualityFactoring.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/EqualityFactoring.o: Lib/Comparison.hpp Lib/Stack.hpp
Inferences/EqualityFactoring.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/EqualityFactoring.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/EqualityFactoring.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/EqualityFactoring.o: Kernel/Ordering.hpp
Inferences/EqualityFactoring.o: Inferences/EqualityFactoring.hpp
Inferences/EqualityFactoring.o: Inferences/InferenceEngine.hpp
Inferences/EqualityResolution.o: Lib/VirtualIterator.hpp
Inferences/EqualityResolution.o: Lib/Metaiterators.hpp Forwards.hpp
Inferences/EqualityResolution.o: Config.hpp Lib/List.hpp Debug/Assertion.hpp
Inferences/EqualityResolution.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/EqualityResolution.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Inferences/EqualityResolution.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/EqualityResolution.o: Lib/Set.hpp Lib/Hash.hpp Lib/PairUtils.hpp
Inferences/EqualityResolution.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/EqualityResolution.o: Lib/Environment.hpp Shell/Statistics.hpp
Inferences/EqualityResolution.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/EqualityResolution.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Inferences/EqualityResolution.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Inferences/EqualityResolution.o: Kernel/Unit.hpp Kernel/Inference.hpp
Inferences/EqualityResolution.o: Kernel/RobSubstitution.hpp
Inferences/EqualityResolution.o: Kernel/EqHelper.hpp Kernel/Term.hpp
Inferences/EqualityResolution.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/EqualityResolution.o: Lib/Comparison.hpp Lib/Stack.hpp
Inferences/EqualityResolution.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/EqualityResolution.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/EqualityResolution.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/EqualityResolution.o: Kernel/Ordering.hpp
Inferences/EqualityResolution.o: Inferences/EqualityResolution.hpp
Inferences/EqualityResolution.o: Inferences/InferenceEngine.hpp
Inferences/Factoring.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Inferences/Factoring.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/Factoring.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp
Inferences/Factoring.o: Forwards.hpp Config.hpp Lib/List.hpp
Inferences/Factoring.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/Factoring.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/Factoring.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Inferences/Factoring.o: Lib/Comparison.hpp Lib/PairUtils.hpp
Inferences/Factoring.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/Factoring.o: Lib/Environment.hpp Shell/Statistics.hpp
Inferences/Factoring.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/Factoring.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Inferences/Factoring.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Inferences/Factoring.o: Kernel/Unit.hpp Kernel/Inference.hpp
Inferences/Factoring.o: Kernel/RobSubstitution.hpp Inferences/Factoring.hpp
Inferences/Factoring.o: Inferences/InferenceEngine.hpp
Inferences/ForwardDemodulation.o: Lib/VirtualIterator.hpp
Inferences/ForwardDemodulation.o: Lib/Metaiterators.hpp Forwards.hpp
Inferences/ForwardDemodulation.o: Config.hpp Lib/List.hpp Debug/Assertion.hpp
Inferences/ForwardDemodulation.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/ForwardDemodulation.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Inferences/ForwardDemodulation.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/ForwardDemodulation.o: Lib/Set.hpp Lib/Hash.hpp Lib/Int.hpp
Inferences/ForwardDemodulation.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/ForwardDemodulation.o: Kernel/Term.hpp Lib/Allocator.hpp
Inferences/ForwardDemodulation.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/ForwardDemodulation.o: Lib/Comparison.hpp Lib/Stack.hpp
Inferences/ForwardDemodulation.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/ForwardDemodulation.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/ForwardDemodulation.o: Kernel/Clause.hpp Lib/Reflection.hpp
Inferences/ForwardDemodulation.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/ForwardDemodulation.o: Kernel/Unit.hpp Lib/List.hpp
Inferences/ForwardDemodulation.o: Kernel/EqHelper.hpp Lib/PairUtils.hpp
Inferences/ForwardDemodulation.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/ForwardDemodulation.o: Kernel/Term.hpp Kernel/Ordering.hpp
Inferences/ForwardDemodulation.o: Kernel/Inference.hpp Kernel/Unit.hpp
Inferences/ForwardDemodulation.o: Kernel/Renaming.hpp Lib/DHMap.hpp
Inferences/ForwardDemodulation.o: Indexing/Index.hpp Lib/Event.hpp
Inferences/ForwardDemodulation.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/ForwardDemodulation.o: Saturation/ClauseContainer.hpp
Inferences/ForwardDemodulation.o: Saturation/Limits.hpp
Inferences/ForwardDemodulation.o: Indexing/ResultSubstitution.hpp
Inferences/ForwardDemodulation.o: Lib/SmartPtr.hpp Indexing/TermIndex.hpp
Inferences/ForwardDemodulation.o: Indexing/Index.hpp
Inferences/ForwardDemodulation.o: Indexing/IndexManager.hpp
Inferences/ForwardDemodulation.o: Saturation/SaturationAlgorithm.hpp
Inferences/ForwardDemodulation.o: Inferences/InferenceEngine.hpp
Inferences/ForwardDemodulation.o: Saturation/SaturationResult.hpp
Inferences/ForwardDemodulation.o: Shell/Statistics.hpp Lib/Environment.hpp
Inferences/ForwardDemodulation.o: Lib/Timer.hpp
Inferences/ForwardDemodulation.o: Inferences/ForwardDemodulation.hpp
Inferences/ForwardDemodulation.o: Inferences/InferenceEngine.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/VirtualIterator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/DArray.hpp Forwards.hpp
Inferences/ForwardSubsumptionAndResolution.o: Config.hpp Debug/Assertion.hpp
Inferences/ForwardSubsumptionAndResolution.o: Debug/Tracer.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Allocator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Debug/Tracer.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Comparison.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Random.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Reflection.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/VirtualIterator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Exception.hpp Lib/List.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Comparison.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Metaiterators.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/List.hpp Lib/Set.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Hash.hpp Kernel/Term.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Allocator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Stack.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/BacktrackData.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Int.hpp Lib/Portability.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/MatchTag.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/BitUtils.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Clause.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Reflection.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/InverseLookup.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/DHMap.hpp Kernel/Unit.hpp
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
Inferences/ForwardSubsumptionAndResolution.o: Inferences/InferenceEngine.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/SaturationResult.hpp
Inferences/ForwardSubsumptionAndResolution.o: Shell/Statistics.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Environment.hpp
Inferences/ForwardSubsumptionAndResolution.o: Inferences/ForwardSubsumptionAndResolution.hpp
Inferences/ForwardSubsumptionAndResolution.o: Inferences/InferenceEngine.hpp
Inferences/InferenceEngine.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Inferences/InferenceEngine.o: Lib/Random.hpp Lib/DArray.hpp
Inferences/InferenceEngine.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/InferenceEngine.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/InferenceEngine.o: Lib/Comparison.hpp Lib/Random.hpp
Inferences/InferenceEngine.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Inferences/InferenceEngine.o: Lib/Exception.hpp Lib/List.hpp
Inferences/InferenceEngine.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/Set.hpp
Inferences/InferenceEngine.o: Lib/Hash.hpp Kernel/Term.hpp Lib/Allocator.hpp
Inferences/InferenceEngine.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/InferenceEngine.o: Lib/Comparison.hpp Lib/Stack.hpp
Inferences/InferenceEngine.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/InferenceEngine.o: Lib/Portability.hpp Kernel/MatchTag.hpp
Inferences/InferenceEngine.o: Lib/BitUtils.hpp Kernel/Clause.hpp
Inferences/InferenceEngine.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Inferences/InferenceEngine.o: Lib/DHMap.hpp Kernel/Unit.hpp
Inferences/InferenceEngine.o: Kernel/Inference.hpp Kernel/Unit.hpp
Inferences/InferenceEngine.o: Shell/Statistics.hpp
Inferences/InferenceEngine.o: Inferences/InferenceEngine.hpp
Inferences/InterpretedEvaluation.o: Lib/Exception.hpp Lib/DArray.hpp
Inferences/InterpretedEvaluation.o: Forwards.hpp Config.hpp
Inferences/InterpretedEvaluation.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/InterpretedEvaluation.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/InterpretedEvaluation.o: Lib/Comparison.hpp Lib/Random.hpp
Inferences/InterpretedEvaluation.o: Lib/Reflection.hpp
Inferences/InterpretedEvaluation.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/InterpretedEvaluation.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Inferences/InterpretedEvaluation.o: Lib/List.hpp Lib/Int.hpp
Inferences/InterpretedEvaluation.o: Lib/Portability.hpp Lib/Environment.hpp
Inferences/InterpretedEvaluation.o: Lib/Metaiterators.hpp Lib/Set.hpp
Inferences/InterpretedEvaluation.o: Lib/Hash.hpp Lib/Int.hpp
Inferences/InterpretedEvaluation.o: Kernel/Signature.hpp Lib/Allocator.hpp
Inferences/InterpretedEvaluation.o: Lib/Map.hpp Kernel/Term.hpp
Inferences/InterpretedEvaluation.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/InterpretedEvaluation.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Inferences/InterpretedEvaluation.o: Lib/BitUtils.hpp Kernel/Clause.hpp
Inferences/InterpretedEvaluation.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Inferences/InterpretedEvaluation.o: Lib/DHMap.hpp Kernel/Unit.hpp
Inferences/InterpretedEvaluation.o: Lib/List.hpp Kernel/Inference.hpp
Inferences/InterpretedEvaluation.o: Kernel/Unit.hpp Indexing/TermSharing.hpp
Inferences/InterpretedEvaluation.o: Lib/Set.hpp Shell/Statistics.hpp
Inferences/InterpretedEvaluation.o: Inferences/InterpretedEvaluation.hpp
Inferences/InterpretedEvaluation.o: Inferences/InferenceEngine.hpp
Inferences/RefutationSeekerFSE.o: Lib/VirtualIterator.hpp
Inferences/RefutationSeekerFSE.o: Lib/Metaiterators.hpp Forwards.hpp
Inferences/RefutationSeekerFSE.o: Config.hpp Lib/List.hpp Debug/Assertion.hpp
Inferences/RefutationSeekerFSE.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/RefutationSeekerFSE.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Inferences/RefutationSeekerFSE.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/RefutationSeekerFSE.o: Lib/Set.hpp Lib/Hash.hpp Lib/Int.hpp
Inferences/RefutationSeekerFSE.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/RefutationSeekerFSE.o: Kernel/Unit.hpp Kernel/Inference.hpp
Inferences/RefutationSeekerFSE.o: Lib/Allocator.hpp Kernel/Clause.hpp
Inferences/RefutationSeekerFSE.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Inferences/RefutationSeekerFSE.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Inferences/RefutationSeekerFSE.o: Indexing/Index.hpp Lib/Event.hpp
Inferences/RefutationSeekerFSE.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/RefutationSeekerFSE.o: Saturation/ClauseContainer.hpp
Inferences/RefutationSeekerFSE.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Inferences/RefutationSeekerFSE.o: Lib/Int.hpp Saturation/Limits.hpp
Inferences/RefutationSeekerFSE.o: Indexing/ResultSubstitution.hpp
Inferences/RefutationSeekerFSE.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Inferences/RefutationSeekerFSE.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/RefutationSeekerFSE.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Inferences/RefutationSeekerFSE.o: Lib/BitUtils.hpp Indexing/LiteralIndex.hpp
Inferences/RefutationSeekerFSE.o: Indexing/Index.hpp
Inferences/RefutationSeekerFSE.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Inferences/RefutationSeekerFSE.o: Saturation/SaturationAlgorithm.hpp
Inferences/RefutationSeekerFSE.o: Inferences/InferenceEngine.hpp
Inferences/RefutationSeekerFSE.o: Saturation/SaturationResult.hpp
Inferences/RefutationSeekerFSE.o: Shell/Statistics.hpp Lib/Environment.hpp
Inferences/RefutationSeekerFSE.o: Inferences/RefutationSeekerFSE.hpp
Inferences/RefutationSeekerFSE.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Comparison.hpp Lib/DArray.hpp
Inferences/SLQueryBackwardSubsumption.o: Forwards.hpp Config.hpp
Inferences/SLQueryBackwardSubsumption.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Comparison.hpp Lib/Random.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Reflection.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/VirtualIterator.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Exception.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Environment.hpp Lib/List.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Metaiterators.hpp Lib/List.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Set.hpp Lib/Hash.hpp Lib/Set.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/VirtualIterator.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Reflection.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/Unit.hpp Kernel/Matcher.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/BacktrackData.hpp Lib/DHMap.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Hash.hpp Lib/Stack.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Portability.hpp Kernel/Term.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
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
Inferences/SLQueryBackwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/SaturationResult.hpp
Inferences/SLQueryBackwardSubsumption.o: Shell/Statistics.hpp
Inferences/SLQueryBackwardSubsumption.o: Inferences/SLQueryBackwardSubsumption.hpp
Inferences/SLQueryBackwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/VirtualIterator.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/BacktrackData.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/SkipList.hpp Debug/Assertion.hpp
Inferences/SLQueryForwardSubsumption.o: Debug/Tracer.hpp Debug/Tracer.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Allocator.hpp Lib/Comparison.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Random.hpp Lib/BacktrackData.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/List.hpp Forwards.hpp Config.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/VirtualIterator.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Int.hpp Lib/Portability.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/DArray.hpp Lib/List.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/DHMap.hpp Lib/Hash.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/DHMultiset.hpp Lib/DHMap.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Comparison.hpp Kernel/Term.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Allocator.hpp Lib/Portability.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/XML.hpp Lib/Stack.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Metaiterators.hpp Lib/Set.hpp
Inferences/SLQueryForwardSubsumption.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/SLQueryForwardSubsumption.o: Kernel/Clause.hpp Lib/Reflection.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/InverseLookup.hpp Kernel/Unit.hpp
Inferences/SLQueryForwardSubsumption.o: Kernel/MLMatcher.hpp
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
Inferences/SLQueryForwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/SaturationResult.hpp
Inferences/SLQueryForwardSubsumption.o: Shell/Statistics.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Environment.hpp
Inferences/SLQueryForwardSubsumption.o: Inferences/SLQueryForwardSubsumption.hpp
Inferences/SLQueryForwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SplittingFSE.o: Lib/DHMap.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/SplittingFSE.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/SplittingFSE.o: Lib/Exception.hpp Lib/Hash.hpp
Inferences/SplittingFSE.o: Lib/VirtualIterator.hpp Forwards.hpp Config.hpp
Inferences/SplittingFSE.o: Lib/Reflection.hpp Lib/Environment.hpp
Inferences/SplittingFSE.o: Lib/IntUnionFind.hpp Lib/Stack.hpp
Inferences/SplittingFSE.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Inferences/SplittingFSE.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/SplittingFSE.o: Kernel/BDD.hpp Lib/Allocator.hpp Lib/Hash.hpp
Inferences/SplittingFSE.o: Lib/Set.hpp Kernel/Clause.hpp
Inferences/SplittingFSE.o: Lib/Metaiterators.hpp Lib/Set.hpp
Inferences/SplittingFSE.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
Inferences/SplittingFSE.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Inferences/SplittingFSE.o: Kernel/Inference.hpp Kernel/Unit.hpp
Inferences/SplittingFSE.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Inferences/SplittingFSE.o: Lib/Comparison.hpp Lib/Stack.hpp
Inferences/SplittingFSE.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/SplittingFSE.o: Shell/Statistics.hpp Inferences/SplittingFSE.hpp
Inferences/SplittingFSE.o: Indexing/ClauseVariantIndex.hpp Lib/Array.hpp
Inferences/SplittingFSE.o: Inferences/InferenceEngine.hpp
Inferences/Superposition.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Inferences/Superposition.o: Lib/Int.hpp Lib/Comparison.hpp
Inferences/Superposition.o: Lib/Portability.hpp Debug/Assertion.hpp
Inferences/Superposition.o: Debug/Tracer.hpp Lib/Metaiterators.hpp
Inferences/Superposition.o: Lib/List.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/Superposition.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/Superposition.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Inferences/Superposition.o: Lib/PairUtils.hpp Lib/Metaiterators.hpp
Inferences/Superposition.o: Lib/Metaarrays.hpp Lib/VirtualIterator.hpp
Inferences/Superposition.o: Shell/Statistics.hpp Kernel/Term.hpp
Inferences/Superposition.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Inferences/Superposition.o: Lib/Comparison.hpp Lib/Stack.hpp
Inferences/Superposition.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/Superposition.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/Superposition.o: Kernel/Clause.hpp Lib/Reflection.hpp
Inferences/Superposition.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/Superposition.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Unit.hpp
Inferences/Superposition.o: Kernel/Inference.hpp Kernel/Ordering.hpp
Inferences/Superposition.o: Kernel/EqHelper.hpp Kernel/Term.hpp
Inferences/Superposition.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Inferences/Superposition.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
Inferences/Superposition.o: Saturation/Limits.hpp
Inferences/Superposition.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Inferences/Superposition.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Inferences/Superposition.o: Indexing/Index.hpp Indexing/TermSharing.hpp
Inferences/Superposition.o: Lib/Set.hpp Saturation/SaturationAlgorithm.hpp
Inferences/Superposition.o: Inferences/InferenceEngine.hpp
Inferences/Superposition.o: Saturation/SaturationResult.hpp
Inferences/Superposition.o: Inferences/Superposition.hpp
Inferences/Superposition.o: Indexing/TermIndex.hpp
Inferences/Superposition.o: Inferences/InferenceEngine.hpp
Inferences/TautologyDeletionFSE.o: Lib/Random.hpp Lib/Environment.hpp
Inferences/TautologyDeletionFSE.o: Forwards.hpp Config.hpp Lib/DArray.hpp
Inferences/TautologyDeletionFSE.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/TautologyDeletionFSE.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/TautologyDeletionFSE.o: Lib/Comparison.hpp Lib/Random.hpp
Inferences/TautologyDeletionFSE.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Inferences/TautologyDeletionFSE.o: Lib/Exception.hpp Kernel/Term.hpp
Inferences/TautologyDeletionFSE.o: Lib/Allocator.hpp Lib/Portability.hpp
Inferences/TautologyDeletionFSE.o: Lib/XML.hpp Lib/Comparison.hpp
Inferences/TautologyDeletionFSE.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Inferences/TautologyDeletionFSE.o: Lib/List.hpp Lib/Int.hpp
Inferences/TautologyDeletionFSE.o: Lib/Portability.hpp Lib/Metaiterators.hpp
Inferences/TautologyDeletionFSE.o: Lib/Set.hpp Lib/Hash.hpp
Inferences/TautologyDeletionFSE.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
Inferences/TautologyDeletionFSE.o: Kernel/Clause.hpp Lib/Reflection.hpp
Inferences/TautologyDeletionFSE.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Inferences/TautologyDeletionFSE.o: Kernel/Unit.hpp Lib/List.hpp
Inferences/TautologyDeletionFSE.o: Shell/Statistics.hpp
Inferences/TautologyDeletionFSE.o: Inferences/TautologyDeletionFSE.hpp
Inferences/TautologyDeletionFSE.o: Inferences/InferenceEngine.hpp
Rule/CASC.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Rule/CASC.o: Lib/Portability.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Rule/CASC.o: Lib/Sort.hpp Lib/Allocator.hpp Lib/DArray.hpp Forwards.hpp
Rule/CASC.o: Config.hpp Lib/Random.hpp Lib/Reflection.hpp
Rule/CASC.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/Environment.hpp
Rule/CASC.o: Kernel/Clause.hpp Lib/Allocator.hpp Lib/Metaiterators.hpp
Rule/CASC.o: Lib/List.hpp Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Rule/CASC.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Rule/CASC.o: Kernel/Signature.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Rule/CASC.o: Lib/Int.hpp Lib/Map.hpp Kernel/Term.hpp Lib/Portability.hpp
Rule/CASC.o: Lib/XML.hpp Lib/Comparison.hpp Kernel/MatchTag.hpp
Rule/CASC.o: Lib/BitUtils.hpp Rule/Rule.hpp Rule/CASC.hpp Kernel/Unit.hpp
Rule/CASC.o: Lib/Array.hpp
Rule/Index.o: Lib/Stack.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Rule/Index.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Rule/Index.o: Lib/List.hpp Forwards.hpp Config.hpp Lib/VirtualIterator.hpp
Rule/Index.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Rule/Index.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Clause.hpp
Rule/Index.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Rule/Index.o: Lib/Hash.hpp Lib/Reflection.hpp Lib/InverseLookup.hpp
Rule/Index.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp Kernel/Signature.hpp
Rule/Index.o: Lib/Map.hpp Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Rule/Index.o: Lib/Comparison.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Rule/Index.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Rule/Index.o: Lib/Exception.hpp Lib/VirtualIterator.hpp
Rule/Index.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
Rule/Index.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Rule/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Rule/Profile.o: Lib/Portability.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Rule/Profile.o: Lib/Sort.hpp Lib/Allocator.hpp Lib/DArray.hpp Forwards.hpp
Rule/Profile.o: Config.hpp Lib/Random.hpp Lib/Reflection.hpp
Rule/Profile.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/Environment.hpp
Rule/Profile.o: Kernel/Clause.hpp Lib/Allocator.hpp Lib/Metaiterators.hpp
Rule/Profile.o: Lib/List.hpp Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Rule/Profile.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp
Rule/Profile.o: Lib/List.hpp Kernel/Signature.hpp Lib/Stack.hpp
Rule/Profile.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Map.hpp Kernel/Term.hpp
Rule/Profile.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Rule/Profile.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Shell/Profile.hpp
Rule/Profile.o: Kernel/Unit.hpp Lib/Array.hpp
Rule/Prolog.o: Kernel/Term.hpp Forwards.hpp Config.hpp Debug/Assertion.hpp
Rule/Prolog.o: Debug/Tracer.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Rule/Prolog.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Rule/Prolog.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Rule/Prolog.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Rule/Prolog.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Rule/Prolog.o: Lib/Portability.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Rule/Prolog.o: Lib/Hash.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Rule/Prolog.o: Kernel/Clause.hpp Lib/Reflection.hpp Lib/InverseLookup.hpp
Rule/Prolog.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp Rule/Prolog.hpp
Rule/Prolog.o: Lib/Map.hpp Rule/Index.hpp Kernel/Unit.hpp Rule/Rule.hpp
Rule/ProofAttempt.o: Debug/Tracer.hpp Lib/Environment.hpp Forwards.hpp
Rule/ProofAttempt.o: Config.hpp Shell/Statistics.hpp Rule/ProofAttempt.hpp
Rule/ProofAttempt.o: Kernel/Unit.hpp
SAT/Assignment.o: Debug/Tracer.hpp SAT/Assignment.hpp Debug/Assertion.hpp
SAT/Assignment.o: Debug/Tracer.hpp SAT/SAT.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Environment.hpp Forwards.hpp
Saturation/AWPassiveClauseContainer.o: Config.hpp Lib/Timer.hpp
Saturation/AWPassiveClauseContainer.o: Debug/Assertion.hpp Debug/Tracer.hpp
Saturation/AWPassiveClauseContainer.o: Kernel/Term.hpp Debug/Tracer.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Allocator.hpp Lib/Portability.hpp
Saturation/AWPassiveClauseContainer.o: Lib/XML.hpp Lib/Comparison.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Stack.hpp Lib/Allocator.hpp
Saturation/AWPassiveClauseContainer.o: Lib/BacktrackData.hpp Lib/List.hpp
Saturation/AWPassiveClauseContainer.o: Lib/VirtualIterator.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Exception.hpp Lib/Reflection.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Int.hpp Lib/Comparison.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Portability.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Metaiterators.hpp Lib/Set.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Hash.hpp Kernel/MatchTag.hpp
Saturation/AWPassiveClauseContainer.o: Lib/BitUtils.hpp Kernel/Clause.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Reflection.hpp
Saturation/AWPassiveClauseContainer.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Saturation/AWPassiveClauseContainer.o: Kernel/Unit.hpp Lib/List.hpp
Saturation/AWPassiveClauseContainer.o: Shell/Statistics.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/SaturationAlgorithm.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Event.hpp Lib/SmartPtr.hpp
Saturation/AWPassiveClauseContainer.o: Indexing/IndexManager.hpp
Saturation/AWPassiveClauseContainer.o: Lib/DHMap.hpp Indexing/Index.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Exception.hpp
Saturation/AWPassiveClauseContainer.o: Lib/VirtualIterator.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/ClauseContainer.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/Limits.hpp
Saturation/AWPassiveClauseContainer.o: Indexing/ResultSubstitution.hpp
Saturation/AWPassiveClauseContainer.o: Lib/SmartPtr.hpp
Saturation/AWPassiveClauseContainer.o: Inferences/InferenceEngine.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/SaturationResult.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/AWPassiveClauseContainer.hpp
Saturation/AWPassiveClauseContainer.o: Kernel/ClauseQueue.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/ClauseContainer.hpp
Saturation/ClauseContainer.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Saturation/ClauseContainer.o: Lib/Set.hpp Lib/Stack.hpp Debug/Assertion.hpp
Saturation/ClauseContainer.o: Debug/Tracer.hpp Debug/Tracer.hpp
Saturation/ClauseContainer.o: Lib/Allocator.hpp Lib/BacktrackData.hpp
Saturation/ClauseContainer.o: Lib/List.hpp Lib/VirtualIterator.hpp
Saturation/ClauseContainer.o: Lib/Exception.hpp Lib/Reflection.hpp
Saturation/ClauseContainer.o: Lib/Int.hpp Lib/Comparison.hpp
Saturation/ClauseContainer.o: Lib/Portability.hpp Kernel/Clause.hpp
Saturation/ClauseContainer.o: Lib/Allocator.hpp Lib/Metaiterators.hpp
Saturation/ClauseContainer.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Saturation/ClauseContainer.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
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
Saturation/ClauseContainer.o: Lib/Portability.hpp Lib/XML.hpp
Saturation/ClauseContainer.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Saturation/ClauseContainer.o: Lib/BitUtils.hpp
Saturation/ClauseContainer.o: Saturation/SaturationAlgorithm.hpp
Saturation/ClauseContainer.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Saturation/ClauseContainer.o: Inferences/InferenceEngine.hpp
Saturation/ClauseContainer.o: Saturation/SaturationResult.hpp
Saturation/ClauseContainer.o: Saturation/ClauseContainer.hpp
Saturation/Discount.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Saturation/Discount.o: Lib/VirtualIterator.hpp Kernel/Clause.hpp
Saturation/Discount.o: Lib/Allocator.hpp Debug/Tracer.hpp
Saturation/Discount.o: Lib/Metaiterators.hpp Lib/List.hpp Debug/Assertion.hpp
Saturation/Discount.o: Debug/Tracer.hpp Lib/Allocator.hpp
Saturation/Discount.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Saturation/Discount.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Saturation/Discount.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Saturation/Discount.o: Kernel/Unit.hpp Lib/List.hpp
Saturation/Discount.o: Kernel/LiteralSelector.hpp Lib/MultiColumnMap.hpp
Saturation/Discount.o: Lib/BitUtils.hpp Shell/Statistics.hpp
Saturation/Discount.o: Saturation/Discount.hpp
Saturation/Discount.o: Saturation/SaturationAlgorithm.hpp Lib/Event.hpp
Saturation/Discount.o: Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Saturation/Discount.o: Lib/DHMap.hpp Indexing/Index.hpp Lib/Exception.hpp
Saturation/Discount.o: Saturation/ClauseContainer.hpp Lib/Stack.hpp
Saturation/Discount.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Saturation/Discount.o: Lib/Portability.hpp Saturation/Limits.hpp
Saturation/Discount.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Saturation/Discount.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Saturation/Discount.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Saturation/Discount.o: Lib/BitUtils.hpp Inferences/InferenceEngine.hpp
Saturation/Discount.o: Saturation/SaturationResult.hpp
Saturation/LRS.o: Lib/Environment.hpp Forwards.hpp Config.hpp Lib/Timer.hpp
Saturation/LRS.o: Debug/Assertion.hpp Debug/Tracer.hpp
Saturation/LRS.o: Lib/VirtualIterator.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Saturation/LRS.o: Debug/Tracer.hpp Lib/Metaiterators.hpp Lib/List.hpp
Saturation/LRS.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Saturation/LRS.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Saturation/LRS.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
Saturation/LRS.o: Kernel/Unit.hpp Lib/List.hpp Kernel/LiteralSelector.hpp
Saturation/LRS.o: Lib/MultiColumnMap.hpp Lib/BitUtils.hpp
Saturation/LRS.o: Shell/Statistics.hpp Shell/Options.hpp Lib/XML.hpp
Saturation/LRS.o: Saturation/LRS.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Saturation/LRS.o: Saturation/SaturationAlgorithm.hpp
Saturation/LRS.o: Indexing/IndexManager.hpp Lib/DHMap.hpp Indexing/Index.hpp
Saturation/LRS.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
Saturation/LRS.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Saturation/LRS.o: Lib/Comparison.hpp Lib/Portability.hpp
Saturation/LRS.o: Saturation/Limits.hpp Indexing/ResultSubstitution.hpp
Saturation/LRS.o: Lib/SmartPtr.hpp Kernel/Term.hpp Lib/Portability.hpp
Saturation/LRS.o: Lib/Comparison.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Saturation/LRS.o: Inferences/InferenceEngine.hpp
Saturation/LRS.o: Saturation/SaturationResult.hpp
Saturation/Otter.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Saturation/Otter.o: Lib/VirtualIterator.hpp Kernel/Clause.hpp
Saturation/Otter.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Metaiterators.hpp
Saturation/Otter.o: Lib/List.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Saturation/Otter.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Saturation/Otter.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp
Saturation/Otter.o: Lib/Hash.hpp Lib/Reflection.hpp Lib/InverseLookup.hpp
Saturation/Otter.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
Saturation/Otter.o: Kernel/LiteralSelector.hpp Lib/MultiColumnMap.hpp
Saturation/Otter.o: Lib/BitUtils.hpp Shell/Statistics.hpp
Saturation/Otter.o: Saturation/Otter.hpp Saturation/SaturationAlgorithm.hpp
Saturation/Otter.o: Lib/Event.hpp Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Saturation/Otter.o: Lib/DHMap.hpp Indexing/Index.hpp Lib/Exception.hpp
Saturation/Otter.o: Saturation/ClauseContainer.hpp Lib/Stack.hpp
Saturation/Otter.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Saturation/Otter.o: Lib/Portability.hpp Saturation/Limits.hpp
Saturation/Otter.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
Saturation/Otter.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Saturation/Otter.o: Lib/Comparison.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Saturation/Otter.o: Inferences/InferenceEngine.hpp
Saturation/Otter.o: Saturation/SaturationResult.hpp
Saturation/SaturationAlgorithm.o: Lib/Environment.hpp Forwards.hpp Config.hpp
Saturation/SaturationAlgorithm.o: Lib/VirtualIterator.hpp Kernel/Clause.hpp
Saturation/SaturationAlgorithm.o: Lib/Allocator.hpp Debug/Tracer.hpp
Saturation/SaturationAlgorithm.o: Lib/Metaiterators.hpp Lib/List.hpp
Saturation/SaturationAlgorithm.o: Debug/Assertion.hpp Debug/Tracer.hpp
Saturation/SaturationAlgorithm.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm.o: Lib/Exception.hpp Lib/Reflection.hpp
Saturation/SaturationAlgorithm.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Saturation/SaturationAlgorithm.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Saturation/SaturationAlgorithm.o: Kernel/Unit.hpp Lib/List.hpp
Saturation/SaturationAlgorithm.o: Kernel/LiteralSelector.hpp
Saturation/SaturationAlgorithm.o: Lib/MultiColumnMap.hpp Lib/BitUtils.hpp
Saturation/SaturationAlgorithm.o: Shell/Statistics.hpp
Saturation/SaturationAlgorithm.o: Saturation/SaturationAlgorithm.hpp
Saturation/SaturationAlgorithm.o: Lib/Event.hpp Lib/SmartPtr.hpp
Saturation/SaturationAlgorithm.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Saturation/SaturationAlgorithm.o: Indexing/Index.hpp Lib/Exception.hpp
Saturation/SaturationAlgorithm.o: Saturation/ClauseContainer.hpp
Saturation/SaturationAlgorithm.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Saturation/SaturationAlgorithm.o: Lib/Int.hpp Lib/Comparison.hpp
Saturation/SaturationAlgorithm.o: Lib/Portability.hpp Saturation/Limits.hpp
Saturation/SaturationAlgorithm.o: Indexing/ResultSubstitution.hpp
Saturation/SaturationAlgorithm.o: Lib/SmartPtr.hpp Kernel/Term.hpp
Saturation/SaturationAlgorithm.o: Lib/Portability.hpp Lib/XML.hpp
Saturation/SaturationAlgorithm.o: Lib/Comparison.hpp Kernel/MatchTag.hpp
Saturation/SaturationAlgorithm.o: Lib/BitUtils.hpp
Saturation/SaturationAlgorithm.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm.o: Saturation/SaturationResult.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Exception.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/KBO.hpp Forwards.hpp
Saturation/SaturationAlgorithm_Construction.o: Config.hpp Lib/DArray.hpp
Saturation/SaturationAlgorithm_Construction.o: Debug/Assertion.hpp
Saturation/SaturationAlgorithm_Construction.o: Debug/Tracer.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Allocator.hpp
Saturation/SaturationAlgorithm_Construction.o: Debug/Tracer.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Comparison.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Random.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Reflection.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Exception.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Ordering.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/LiteralSelector.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/MultiColumnMap.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/BitUtils.hpp Lib/DHMap.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Hash.hpp Shell/Options.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Allocator.hpp Lib/XML.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/SmartPtr.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/List.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/BackwardDemodulation.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/TermIndex.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/Index.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Event.hpp Lib/List.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/SmartPtr.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/ClauseContainer.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Stack.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/BacktrackData.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Int.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Portability.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Limits.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Clause.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Metaiterators.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Set.hpp Lib/Reflection.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/InverseLookup.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Unit.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/ResultSubstitution.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Term.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Portability.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Comparison.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/MatchTag.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/BitUtils.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/BinaryResolution.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/Condensation.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/EqualityFactoring.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/EqualityResolution.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/InterpretedEvaluation.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/Factoring.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/ForwardDemodulation.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/ForwardSubsumptionAndResolution.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/RefutationSeekerFSE.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/SLQueryForwardSubsumption.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/SLQueryBackwardSubsumption.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/SplittingFSE.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/DHMap.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/ClauseVariantIndex.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Array.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/Superposition.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/TautologyDeletionFSE.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/AWPassiveClauseContainer.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/ClauseQueue.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/ClauseContainer.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/SaturationAlgorithm.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/IndexManager.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/SaturationResult.hpp
Saturation/SaturationAlgorithm_Construction.o: Shell/Statistics.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Environment.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Discount.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/LRS.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Otter.hpp
Saturation/SaturationResult.o: Kernel/Clause.hpp Forwards.hpp Config.hpp
Saturation/SaturationResult.o: Lib/Allocator.hpp Debug/Tracer.hpp
Saturation/SaturationResult.o: Lib/Metaiterators.hpp Lib/List.hpp
Saturation/SaturationResult.o: Debug/Assertion.hpp Debug/Tracer.hpp
Saturation/SaturationResult.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Saturation/SaturationResult.o: Lib/Exception.hpp Lib/Reflection.hpp
Saturation/SaturationResult.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Saturation/SaturationResult.o: Lib/InverseLookup.hpp Lib/DHMap.hpp
Saturation/SaturationResult.o: Kernel/Unit.hpp Lib/List.hpp
Saturation/SaturationResult.o: Saturation/SaturationResult.hpp
Saturation/SaturationResult.o: Shell/Statistics.hpp Lib/Environment.hpp
Test/Compit2Output.o: Test/Compit2Output.hpp Config.hpp
Test/CompitOutput.o: Test/CompitOutput.hpp Config.hpp
Test/Output.o: Debug/Assertion.hpp Debug/Tracer.hpp Kernel/Term.hpp
Test/Output.o: Forwards.hpp Config.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Test/Output.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Test/Output.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Test/Output.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Test/Output.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Test/Output.o: Lib/Portability.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Test/Output.o: Lib/Hash.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
Test/Output.o: Kernel/Clause.hpp Lib/Reflection.hpp Lib/InverseLookup.hpp
Test/Output.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp Lib/Int.hpp
Test/Output.o: Test/Output.hpp Lib/Environment.hpp Kernel/Signature.hpp
Test/Output.o: Lib/Map.hpp
Global.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Enumerator.hpp
Global.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp Kernel/Connective.hpp
Global.o: Kernel/Unit.hpp Lib/Environment.hpp Forwards.hpp Config.hpp
compit2.o: compit2.hpp Kernel/Term.hpp Forwards.hpp Config.hpp
compit2.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
compit2.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
compit2.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
compit2.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
compit2.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
compit2.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Metaiterators.hpp
compit2.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
compit2.o: Lib/Timer.hpp
compit2_impl.o: compit2.hpp Kernel/Term.hpp Forwards.hpp Config.hpp
compit2_impl.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
compit2_impl.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
compit2_impl.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
compit2_impl.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
compit2_impl.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
compit2_impl.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Metaiterators.hpp
compit2_impl.o: Lib/Set.hpp Lib/Hash.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
compit2_impl.o: Lib/Allocator.hpp Lib/Random.hpp Lib/Set.hpp Lib/Stack.hpp
compit2_impl.o: Lib/Int.hpp Lib/Timer.hpp Lib/Exception.hpp
compit2_impl.o: Lib/Environment.hpp Lib/VirtualIterator.hpp
compit2_impl.o: Lib/Metaiterators.hpp Kernel/Signature.hpp Lib/Map.hpp
compit2_impl.o: Kernel/Curryfier.hpp Lib/Environment.hpp Lib/DHMap.hpp
compit2_impl.o: Lib/DArray.hpp Lib/Random.hpp Lib/ArrayMap.hpp Lib/DArray.hpp
compit2_impl.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
compit2_impl.o: Kernel/Term.hpp Kernel/Signature.hpp Indexing/TermSharing.hpp
compit2_impl.o: Indexing/TermSubstitutionTree.hpp Kernel/Renaming.hpp
compit2_impl.o: Lib/VirtualIterator.hpp Lib/SkipList.hpp Indexing/Index.hpp
compit2_impl.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
compit2_impl.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
compit2_impl.o: Kernel/Clause.hpp Lib/Reflection.hpp Lib/InverseLookup.hpp
compit2_impl.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
compit2_impl.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
compit2_impl.o: Indexing/TermIndexingStructure.hpp
compit2_impl.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp Lib/BinaryHeap.hpp
compit2_impl.o: Lib/Metaiterators.hpp Lib/BacktrackData.hpp Lib/Array.hpp
compit2_impl.o: Kernel/DoubleSubstitution.hpp Kernel/EGSubstitution.hpp
compit2_impl.o: Kernel/RobSubstitution.hpp Kernel/RobSubstitution.hpp
compit2_impl.o: Test/Output.hpp Shell/Options.hpp Shell/CommandLine.hpp
compit2_impl.o: Shell/Property.hpp Kernel/Unit.hpp Shell/Preprocess.hpp
compit2_impl.o: Shell/Statistics.hpp
test_BinaryHeap.o: Lib/BinaryHeap.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_BinaryHeap.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
test_BinaryHeap.o: Lib/Comparison.hpp Lib/BacktrackData.hpp Lib/List.hpp
test_BinaryHeap.o: Forwards.hpp Config.hpp Lib/VirtualIterator.hpp
test_BinaryHeap.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Portability.hpp
test_BinaryHeap.o: Lib/Metaiterators.hpp Lib/Int.hpp
test_DHMap.o: Lib/DHMap.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_DHMap.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
test_DHMap.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Forwards.hpp Config.hpp
test_DHMap.o: Lib/Reflection.hpp
test_DHMultiset.o: Lib/DHMultiset.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_DHMultiset.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
test_DHMultiset.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/VirtualIterator.hpp
test_DHMultiset.o: Forwards.hpp Config.hpp Lib/Reflection.hpp
test_SkipList.o: Lib/SkipList.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_SkipList.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Comparison.hpp
test_SkipList.o: Lib/Random.hpp Lib/BacktrackData.hpp Lib/List.hpp
test_SkipList.o: Forwards.hpp Config.hpp Lib/VirtualIterator.hpp
test_SkipList.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
test_SkipList.o: Lib/Portability.hpp Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
test_SkipList.o: Lib/DHMultiset.hpp Lib/Hash.hpp Lib/DHMap.hpp Lib/Int.hpp
test_SkipList.o: Lib/DArray.hpp Lib/Timer.hpp Lib/Random.hpp
test_SubstitutionTree.o: Debug/Tracer.hpp Lib/Array.hpp Debug/Assertion.hpp
test_SubstitutionTree.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
test_SubstitutionTree.o: Lib/Random.hpp Lib/Set.hpp Lib/Int.hpp Lib/Timer.hpp
test_SubstitutionTree.o: Lib/Exception.hpp Lib/Environment.hpp Forwards.hpp
test_SubstitutionTree.o: Config.hpp Lib/Vector.hpp Lib/Allocator.hpp
test_SubstitutionTree.o: Kernel/Signature.hpp Lib/Stack.hpp
test_SubstitutionTree.o: Lib/BacktrackData.hpp Lib/List.hpp
test_SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
test_SubstitutionTree.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
test_SubstitutionTree.o: Lib/Portability.hpp Lib/Map.hpp Lib/Hash.hpp
test_SubstitutionTree.o: Kernel/Clause.hpp Lib/Metaiterators.hpp Lib/Set.hpp
test_SubstitutionTree.o: Lib/Reflection.hpp Lib/InverseLookup.hpp
test_SubstitutionTree.o: Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
test_SubstitutionTree.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
test_SubstitutionTree.o: Kernel/FormulaUnit.hpp Indexing/TermSharing.hpp
test_SubstitutionTree.o: Indexing/SubstitutionTree.hpp
test_SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Comparison.hpp
test_SubstitutionTree.o: Lib/Int.hpp Lib/SkipList.hpp Lib/Random.hpp
test_SubstitutionTree.o: Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
test_SubstitutionTree.o: Lib/BacktrackData.hpp Lib/ArrayMap.hpp
test_SubstitutionTree.o: Lib/DArray.hpp Lib/Array.hpp
test_SubstitutionTree.o: Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp
test_SubstitutionTree.o: Kernel/Term.hpp Lib/Portability.hpp
test_SubstitutionTree.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp
test_SubstitutionTree.o: Kernel/EGSubstitution.hpp Kernel/RobSubstitution.hpp
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
test_alloc.o: Lib/Allocator.hpp
test_retrieval.o: Debug/Tracer.hpp Lib/Array.hpp Debug/Assertion.hpp
test_retrieval.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
test_retrieval.o: Lib/Random.hpp Lib/Set.hpp Lib/Int.hpp Lib/Timer.hpp
test_retrieval.o: Lib/Exception.hpp Lib/Environment.hpp Forwards.hpp
test_retrieval.o: Config.hpp Lib/Vector.hpp Lib/Allocator.hpp
test_retrieval.o: Kernel/Signature.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
test_retrieval.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
test_retrieval.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
test_retrieval.o: Lib/Portability.hpp Lib/Map.hpp Lib/Hash.hpp
test_retrieval.o: Kernel/Clause.hpp Lib/Metaiterators.hpp Lib/Set.hpp
test_retrieval.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
test_retrieval.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp Lib/XML.hpp
test_retrieval.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
test_retrieval.o: Indexing/TermSharing.hpp Indexing/SubstitutionTree.hpp
test_retrieval.o: Lib/VirtualIterator.hpp Lib/Comparison.hpp Lib/Int.hpp
test_retrieval.o: Lib/SkipList.hpp Lib/Random.hpp Lib/BinaryHeap.hpp
test_retrieval.o: Lib/Metaiterators.hpp Lib/BacktrackData.hpp
test_retrieval.o: Lib/ArrayMap.hpp Lib/DArray.hpp Lib/Array.hpp
test_retrieval.o: Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp Kernel/Term.hpp
test_retrieval.o: Lib/Portability.hpp Kernel/MatchTag.hpp Lib/BitUtils.hpp
test_retrieval.o: Kernel/EGSubstitution.hpp Kernel/RobSubstitution.hpp
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
ucompit.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
ucompit.o: Lib/Environment.hpp Forwards.hpp Lib/VirtualIterator.hpp
ucompit.o: Lib/Metaiterators.hpp Kernel/Signature.hpp Lib/Allocator.hpp
ucompit.o: Debug/Tracer.hpp Lib/Stack.hpp Lib/Allocator.hpp
ucompit.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
ucompit.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
ucompit.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Map.hpp Lib/Hash.hpp
ucompit.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
ucompit.o: Lib/Metaiterators.hpp Lib/Set.hpp Kernel/MatchTag.hpp
ucompit.o: Lib/BitUtils.hpp Kernel/Curryfier.hpp Lib/Environment.hpp
ucompit.o: Lib/DHMap.hpp Lib/DArray.hpp Lib/Random.hpp Lib/ArrayMap.hpp
ucompit.o: Lib/DArray.hpp Indexing/TermSharing.hpp Lib/Set.hpp
ucompit.o: Kernel/Term.hpp Kernel/Term.hpp Kernel/Signature.hpp
ucompit.o: Indexing/TermSharing.hpp Indexing/TermSubstitutionTree.hpp
ucompit.o: Kernel/Renaming.hpp Lib/VirtualIterator.hpp Lib/SkipList.hpp
ucompit.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
ucompit.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
ucompit.o: Saturation/Limits.hpp Kernel/Clause.hpp Lib/Reflection.hpp
ucompit.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
ucompit.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
ucompit.o: Indexing/TermIndexingStructure.hpp Indexing/SubstitutionTree.hpp
ucompit.o: Lib/Int.hpp Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
ucompit.o: Lib/BacktrackData.hpp Lib/Array.hpp Kernel/DoubleSubstitution.hpp
ucompit.o: Kernel/EGSubstitution.hpp Kernel/RobSubstitution.hpp
ucompit.o: Kernel/RobSubstitution.hpp Test/Output.hpp Shell/Options.hpp
ucompit.o: Shell/CommandLine.hpp Shell/Property.hpp Kernel/Unit.hpp
ucompit.o: Shell/Preprocess.hpp Shell/Statistics.hpp
vampire.o: Debug/Tracer.hpp Lib/Random.hpp Lib/Set.hpp Lib/Int.hpp
vampire.o: Lib/Timer.hpp Debug/Assertion.hpp Debug/Tracer.hpp
vampire.o: Lib/Exception.hpp Lib/Environment.hpp Forwards.hpp Config.hpp
vampire.o: Lib/Vector.hpp Lib/Allocator.hpp Debug/Tracer.hpp Lib/System.hpp
vampire.o: Lib/Metaiterators.hpp Kernel/Signature.hpp Lib/Allocator.hpp
vampire.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp
vampire.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/Reflection.hpp
vampire.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp Lib/Map.hpp
vampire.o: Lib/Hash.hpp Kernel/Clause.hpp Lib/Metaiterators.hpp Lib/Set.hpp
vampire.o: Lib/Reflection.hpp Lib/InverseLookup.hpp Lib/DHMap.hpp
vampire.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp Lib/XML.hpp
vampire.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
vampire.o: Indexing/TermSharing.hpp Indexing/SubstitutionTree.hpp
vampire.o: Lib/VirtualIterator.hpp Lib/Comparison.hpp Lib/Int.hpp
vampire.o: Lib/SkipList.hpp Lib/Random.hpp Lib/BinaryHeap.hpp
vampire.o: Lib/Metaiterators.hpp Lib/BacktrackData.hpp Lib/ArrayMap.hpp
vampire.o: Lib/DArray.hpp Lib/Array.hpp Kernel/DoubleSubstitution.hpp
vampire.o: Lib/DHMap.hpp Kernel/Term.hpp Lib/Portability.hpp
vampire.o: Kernel/MatchTag.hpp Lib/BitUtils.hpp Kernel/EGSubstitution.hpp
vampire.o: Kernel/RobSubstitution.hpp Kernel/RobSubstitution.hpp
vampire.o: Kernel/Renaming.hpp Kernel/Clause.hpp Indexing/Index.hpp
vampire.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
vampire.o: Saturation/ClauseContainer.hpp Saturation/Limits.hpp
vampire.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp Kernel/Term.hpp
vampire.o: Test/Output.hpp Indexing/LiteralMiniIndex.hpp Lib/DArray.hpp
vampire.o: Kernel/Matcher.hpp Lib/Hash.hpp Shell/Options.hpp
vampire.o: Shell/CommandLine.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
vampire.o: Shell/Token.hpp Shell/TPTP.hpp Shell/TPTPParser.hpp
vampire.o: Kernel/Unit.hpp Shell/Parser.hpp Lib/IntNameTable.hpp
vampire.o: Lib/Array.hpp Lib/Map.hpp Shell/Property.hpp Shell/Preprocess.hpp
vampire.o: Shell/Statistics.hpp Shell/Refutation.hpp
vampire.o: Saturation/SaturationAlgorithm.hpp Indexing/IndexManager.hpp
vampire.o: Inferences/InferenceEngine.hpp Saturation/SaturationResult.hpp
vampire.o: Shell/Statistics.hpp Lib/Environment.hpp Lib/MemoryLeak.hpp
vcompit.o: Forwards.hpp Config.hpp Debug/Tracer.hpp Lib/Allocator.hpp
vcompit.o: Lib/Random.hpp Lib/Set.hpp Lib/Int.hpp Lib/Timer.hpp
vcompit.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
vcompit.o: Lib/Environment.hpp Forwards.hpp Lib/VirtualIterator.hpp
vcompit.o: Lib/Metaiterators.hpp Kernel/Signature.hpp Lib/Allocator.hpp
vcompit.o: Debug/Tracer.hpp Lib/Stack.hpp Lib/Allocator.hpp
vcompit.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/VirtualIterator.hpp
vcompit.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
vcompit.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Map.hpp Lib/Hash.hpp
vcompit.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
vcompit.o: Lib/Metaiterators.hpp Lib/Set.hpp Kernel/MatchTag.hpp
vcompit.o: Lib/BitUtils.hpp Kernel/Curryfier.hpp Lib/Environment.hpp
vcompit.o: Lib/DHMap.hpp Lib/DArray.hpp Lib/Random.hpp Lib/ArrayMap.hpp
vcompit.o: Lib/DArray.hpp Indexing/TermSharing.hpp Lib/Set.hpp
vcompit.o: Kernel/Term.hpp Kernel/Term.hpp Kernel/Signature.hpp
vcompit.o: Indexing/TermSharing.hpp Indexing/TermSubstitutionTree.hpp
vcompit.o: Kernel/Renaming.hpp Lib/VirtualIterator.hpp Lib/SkipList.hpp
vcompit.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
vcompit.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
vcompit.o: Saturation/Limits.hpp Kernel/Clause.hpp Lib/Reflection.hpp
vcompit.o: Lib/InverseLookup.hpp Lib/DHMap.hpp Kernel/Unit.hpp Lib/List.hpp
vcompit.o: Indexing/ResultSubstitution.hpp Lib/SmartPtr.hpp
vcompit.o: Indexing/TermIndexingStructure.hpp Indexing/SubstitutionTree.hpp
vcompit.o: Lib/Int.hpp Lib/BinaryHeap.hpp Lib/Metaiterators.hpp
vcompit.o: Lib/BacktrackData.hpp Lib/Array.hpp Kernel/DoubleSubstitution.hpp
vcompit.o: Kernel/EGSubstitution.hpp Kernel/RobSubstitution.hpp
vcompit.o: Kernel/RobSubstitution.hpp Test/Output.hpp Shell/Options.hpp
vcompit.o: Shell/CommandLine.hpp Shell/Property.hpp Kernel/Unit.hpp
vcompit.o: Shell/Preprocess.hpp Shell/Statistics.hpp
