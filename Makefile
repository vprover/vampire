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

#XFLAGS = -O1 -DVDEBUG=1 -DVTEST=1 -DCHECK_LEAKS=1 # full debugging + testing
#XFLAGS = -g -DVDEBUG=1 -DVTEST=1 -DCHECK_LEAKS=1 # full debugging + testing
#XFLAGS = -g -DVDEBUG=0 -DCHECK_LEAKS=0 # debug mode without VDEBUG macro 
#XFLAGS = -g -O6 -DVDEBUG=0 # no debugging, but debugging info present
#XFLAGS = -fprofile-arcs -pg -g -DVDEBUG=0 # coverage & profiling
#XFLAGS = -pg -g -DVDEBUG=0 # profiling
#XFLAGS = -pg -DVDEBUG=0 # profiling without debug info
XFLAGS = -g -DVDEBUG=1 -DCHECK_LEAKS=0 # standard debugging only
#XFLAGS = -O6 -DVDEBUG=0 # no debugging

#XFLAGS = -pg -g -DVDEBUG=1 -DCHECK_LEAKS=0 # profiling & debugging
#XFLAGS = -fprofile-arcs -pg -O6 -DVDEBUG=0 # coverage & profiling optimized
#XFLAGS = -DVDEBUG=0 # no debugging, no optimization
#XFLAGS = -O6 -DVDEBUG=1 -DCHECK_LEAKS=0 # debugging and optimized
#XFLAGS = -O0 -DVDEBUG=0 -DUSE_SYSTEM_ALLOCATION=1 -fno-inline -fno-default-inline -g # Valgrind


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
        Lib/MemoryLeak.o\
        Lib/MultiCounter.o\
        Lib/NameArray.o\
        Lib/Random.o\
        Lib/System.o

VK_OBJ= Kernel/Clause.o\
        Kernel/ClauseQueue.o\
        Kernel/DoubleSubstitution.o\
        Kernel/EqHelper.o\
        Kernel/Formula.o\
        Kernel/FormulaUnit.o\
        Kernel/FormulaVarIterator.o\
        Kernel/Inference.o\
        Kernel/KBO.o\
        Kernel/LiteralSelector.o\
        Kernel/MLMatcher.o\
        Kernel/MMSubstitution.o\
        Kernel/Ordering.o\
        Kernel/OrderingLiteralSelector.o\
        Kernel/Renaming.o\
        Kernel/Signature.o\
        Kernel/SubformulaIterator.o\
        Kernel/Substitution.o\
        Kernel/Term.o\
        Kernel/TermFunIterator.o\
        Kernel/TermVarIterator.o\
        Kernel/Unit.o

VI_OBJ = Indexing/Index.o\
         Indexing/IndexManager.o\
         Indexing/LiteralIndex.o\
         Indexing/LiteralSubstitutionTree.o\
         Indexing/TermIndex.o\
         Indexing/TermSharing.o\
         Indexing/TermSubstitutionTree.o\
         Indexing/SubstitutionTree.o\
         Indexing/SubstitutionTree_Nodes.o

VINF_OBJ=Inferences/BackwardDemodulation.o\
         Inferences/BinaryResolution.o\
         Inferences/EqualityFactoring.o\
         Inferences/EqualityResolution.o\
         Inferences/Factoring.o\
         Inferences/ForwardDemodulation.o\
         Inferences/ForwardSubsumptionAndResolution.o\
         Inferences/InferenceEngine.o\
         Inferences/RefutationSeekerFSE.o\
         Inferences/SLQueryBackwardSubsumption.o\
         Inferences/SLQueryForwardSubsumption.o\
         Inferences/Superposition.o\
         Inferences/TautologyDeletionFSE.o

VST_OBJ= Saturation/AWPassiveClauseContainer.o\
         Saturation/ClauseContainer.o\
         Saturation/Discount.o\
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
VT_OBJ = Test/Output.o


VAMP_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ)  
ALUC_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ)  
VCOMPIT_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VT_OBJ)  

VAMPIRE_OBJ = $(VAMP_BASIC) Global.o vampire.o
VCOMPIT_OBJ = $(VCOMPIT_BASIC) Global.o vcompit.o
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
Lib/Allocator.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Forwards.hpp
Lib/Allocator.o: Lib/Reflection.hpp Shell/Statistics.hpp Lib/Environment.hpp
Lib/Allocator.o: Lib/MemoryLeak.hpp Lib/Set.hpp Kernel/Unit.hpp Lib/List.hpp
Lib/Allocator.o: Lib/Random.hpp
Lib/DHMap.o: Lib/DHMap.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Lib/DHMap.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
Lib/DHMap.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Forwards.hpp
Lib/DHMap.o: Lib/Reflection.hpp
Lib/Environment.o: Debug/Tracer.hpp Lib/Timer.hpp Debug/Assertion.hpp
Lib/Environment.o: Debug/Tracer.hpp Lib/Environment.hpp Shell/Options.hpp
Lib/Environment.o: Lib/Allocator.hpp Lib/XML.hpp Shell/Statistics.hpp
Lib/Event.o: Lib/Event.hpp Lib/List.hpp Forwards.hpp Debug/Assertion.hpp
Lib/Event.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Lib/Event.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/Reflection.hpp
Lib/Event.o: Lib/SmartPtr.hpp
Lib/Exception.o: Lib/Exception.hpp
Lib/Hash.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Lib/Hash.o: Lib/Hash.hpp
Lib/Int.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Lib/Int.o: Debug/Tracer.hpp
Lib/IntNameTable.o: Lib/IntNameTable.hpp Lib/Array.hpp Debug/Assertion.hpp
Lib/IntNameTable.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Lib/IntNameTable.o: Lib/Map.hpp Lib/Allocator.hpp Lib/Hash.hpp
Lib/IntNameTable.o: Lib/Exception.hpp
Lib/IntegerSet.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/IntegerSet.hpp
Lib/MemoryLeak.o: Lib/Hash.hpp Lib/Stack.hpp Debug/Assertion.hpp
Lib/MemoryLeak.o: Debug/Tracer.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Lib/MemoryLeak.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp
Lib/MemoryLeak.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Lib/MemoryLeak.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Lib/MemoryLeak.o: Lib/Portability.hpp Lib/MemoryLeak.hpp Lib/Set.hpp
Lib/MemoryLeak.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Clause.hpp
Lib/MemoryLeak.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/Reflection.hpp
Lib/MemoryLeak.o: Kernel/Unit.hpp Kernel/Inference.hpp Kernel/Formula.hpp
Lib/MemoryLeak.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Lib/MultiCounter.o: Debug/Tracer.hpp Lib/MultiCounter.hpp Debug/Assertion.hpp
Lib/MultiCounter.o: Debug/Tracer.hpp Lib/XML.hpp Lib/Int.hpp
Lib/MultiCounter.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Allocator.hpp
Lib/MultiCounter.o: Lib/Exception.hpp
Lib/NameArray.o: Lib/NameArray.hpp Debug/Tracer.hpp
Lib/Random.o: Lib/Random.hpp
Lib/System.o: Debug/Tracer.hpp Lib/System.hpp
Lib/Timer.o: Lib/Timer.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/CNF.o: Debug/Tracer.hpp Kernel/Clause.hpp Forwards.hpp
Shell/CNF.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/CNF.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/CNF.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/Reflection.hpp
Shell/CNF.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Shell/CNF.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp
Shell/CNF.o: Kernel/Connective.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/CNF.o: Kernel/FormulaUnit.hpp Shell/CNF.hpp Lib/Stack.hpp
Shell/CNF.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/CNF.o: Lib/Portability.hpp
Shell/CommandLine.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Shell/CommandLine.o: Lib/Exception.hpp Shell/CommandLine.hpp
Shell/CommandLine.o: Shell/Options.hpp Lib/Allocator.hpp Lib/XML.hpp
Shell/Flattening.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Flattening.o: Lib/List.hpp Forwards.hpp Debug/Assertion.hpp
Shell/Flattening.o: Debug/Tracer.hpp Lib/Allocator.hpp
Shell/Flattening.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Flattening.o: Lib/Reflection.hpp Lib/Allocator.hpp
Shell/Flattening.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/Flattening.o: Shell/Flattening.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/Flattening.o: Kernel/Connective.hpp
Shell/FunctionDefinition.o: Debug/Tracer.hpp Lib/Allocator.hpp
Shell/FunctionDefinition.o: Kernel/Clause.hpp Forwards.hpp
Shell/FunctionDefinition.o: Lib/Metaiterators.hpp Lib/List.hpp
Shell/FunctionDefinition.o: Debug/Assertion.hpp Debug/Tracer.hpp
Shell/FunctionDefinition.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Shell/FunctionDefinition.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp
Shell/FunctionDefinition.o: Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Shell/FunctionDefinition.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp
Shell/FunctionDefinition.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/FunctionDefinition.o: Kernel/Term.hpp Lib/Portability.hpp
Shell/FunctionDefinition.o: Lib/Comparison.hpp Lib/Stack.hpp
Shell/FunctionDefinition.o: Lib/BacktrackData.hpp Lib/Int.hpp
Shell/FunctionDefinition.o: Lib/Comparison.hpp Lib/Portability.hpp
Shell/FunctionDefinition.o: Kernel/TermVarIterator.hpp
Shell/FunctionDefinition.o: Kernel/TermFunIterator.hpp
Shell/FunctionDefinition.o: Shell/FunctionDefinition.hpp Lib/MultiCounter.hpp
Shell/FunctionDefinition.o: Lib/XML.hpp Kernel/Unit.hpp
Shell/Lexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Shell/Lexer.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/Lexer.o: Shell/Lexer.hpp Lib/Array.hpp Lib/Allocator.hpp
Shell/Lexer.o: Lib/Exception.hpp Shell/Token.hpp
Shell/NNF.o: Lib/Environment.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/NNF.o: Lib/List.hpp Forwards.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/NNF.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/VirtualIterator.hpp
Shell/NNF.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Allocator.hpp
Shell/NNF.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Kernel/Term.hpp
Shell/NNF.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/NNF.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/NNF.o: Lib/Comparison.hpp Lib/Portability.hpp Indexing/TermSharing.hpp
Shell/NNF.o: Lib/Set.hpp Lib/Hash.hpp Shell/NNF.hpp Kernel/Formula.hpp
Shell/NNF.o: Kernel/Connective.hpp
Shell/Naming.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Shell/Naming.o: Lib/Comparison.hpp Lib/Portability.hpp Lib/Environment.hpp
Shell/Naming.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Kernel/Inference.hpp
Shell/Naming.o: Kernel/Unit.hpp Lib/List.hpp Forwards.hpp Debug/Assertion.hpp
Shell/Naming.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/VirtualIterator.hpp
Shell/Naming.o: Lib/Exception.hpp Lib/Reflection.hpp Kernel/Signature.hpp
Shell/Naming.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/Naming.o: Lib/Map.hpp Lib/Hash.hpp Kernel/Term.hpp Lib/Portability.hpp
Shell/Naming.o: Lib/XML.hpp Lib/Comparison.hpp Shell/Statistics.hpp
Shell/Naming.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Naming.hpp
Shell/Naming.o: Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Normalisation.o: Lib/Sort.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Normalisation.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Environment.hpp
Shell/Normalisation.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Shell/Normalisation.o: Lib/Metaiterators.hpp Lib/List.hpp
Shell/Normalisation.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Normalisation.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Shell/Normalisation.o: Lib/Reflection.hpp Kernel/Unit.hpp
Shell/Normalisation.o: Kernel/FormulaUnit.hpp Kernel/Inference.hpp
Shell/Normalisation.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Term.hpp
Shell/Normalisation.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/Normalisation.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/Normalisation.o: Lib/Comparison.hpp Lib/Portability.hpp
Shell/Normalisation.o: Kernel/Signature.hpp Lib/Map.hpp
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
Shell/Parser.o: Lib/List.hpp Forwards.hpp Lib/VirtualIterator.hpp
Shell/Parser.o: Lib/Reflection.hpp
Shell/Preprocess.o: Debug/Tracer.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/Preprocess.o: Forwards.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Preprocess.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Shell/Preprocess.o: Lib/Exception.hpp Lib/Reflection.hpp Kernel/Clause.hpp
Shell/Preprocess.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/Preprocess.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Shell/Preprocess.o: Kernel/Unit.hpp Shell/CNF.hpp Lib/Stack.hpp
Shell/Preprocess.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Preprocess.o: Lib/Portability.hpp Shell/Flattening.hpp
Shell/Preprocess.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/Preprocess.o: Shell/Naming.hpp Shell/Normalisation.hpp
Shell/Preprocess.o: Lib/Comparison.hpp Shell/SymCounter.hpp Shell/NNF.hpp
Shell/Preprocess.o: Shell/Options.hpp Shell/Preprocess.hpp Shell/Property.hpp
Shell/Preprocess.o: Shell/Rectify.hpp Lib/Array.hpp Shell/Skolem.hpp
Shell/Preprocess.o: Kernel/Substitution.hpp Lib/Random.hpp
Shell/Preprocess.o: Lib/Environment.hpp Kernel/Term.hpp Lib/Portability.hpp
Shell/Preprocess.o: Shell/SimplifyFalseTrue.hpp
Shell/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Profile.o: Lib/Portability.hpp Lib/Sort.hpp Debug/Assertion.hpp
Shell/Profile.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Environment.hpp
Shell/Profile.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Shell/Profile.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/VirtualIterator.hpp
Shell/Profile.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp
Shell/Profile.o: Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Shell/Profile.o: Kernel/Signature.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Shell/Profile.o: Lib/Int.hpp Lib/Map.hpp Kernel/Term.hpp Lib/Portability.hpp
Shell/Profile.o: Lib/XML.hpp Lib/Comparison.hpp Shell/Profile.hpp
Shell/Profile.o: Kernel/Unit.hpp Lib/List.hpp Lib/Array.hpp
Shell/Property.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Property.o: Lib/Portability.hpp Kernel/Clause.hpp Forwards.hpp
Shell/Property.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/Property.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/Property.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Property.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Shell/Property.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/FormulaUnit.hpp
Shell/Property.o: Kernel/SubformulaIterator.hpp Kernel/Formula.hpp
Shell/Property.o: Lib/List.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/Property.o: Kernel/Term.hpp Lib/Portability.hpp Lib/Comparison.hpp
Shell/Property.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Shell/Property.o: Shell/FunctionDefinition.hpp Lib/MultiCounter.hpp
Shell/Property.o: Lib/XML.hpp Kernel/Unit.hpp Shell/Property.hpp
Shell/Rectify.o: Lib/Environment.hpp Kernel/Formula.hpp Lib/List.hpp
Shell/Rectify.o: Forwards.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Rectify.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/VirtualIterator.hpp
Shell/Rectify.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/XML.hpp
Shell/Rectify.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/Rectify.o: Lib/Allocator.hpp Kernel/Unit.hpp Kernel/Inference.hpp
Shell/Rectify.o: Kernel/Unit.hpp Kernel/Term.hpp Lib/Portability.hpp
Shell/Rectify.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Shell/Rectify.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Rectify.o: Lib/Portability.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/Rectify.o: Lib/Hash.hpp Shell/Rectify.hpp Lib/Array.hpp
Shell/Refutation.o: Debug/Tracer.hpp Lib/Hash.hpp Lib/Set.hpp
Shell/Refutation.o: Lib/Allocator.hpp Lib/Hash.hpp Lib/Stack.hpp
Shell/Refutation.o: Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Refutation.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp
Shell/Refutation.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Refutation.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Refutation.o: Lib/Portability.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Shell/Refutation.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Reflection.hpp
Shell/Refutation.o: Kernel/Unit.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Refutation.o: Lib/List.hpp Shell/Refutation.hpp
Shell/SimplifyFalseTrue.o: Debug/Tracer.hpp Lib/DArray.hpp Forwards.hpp
Shell/SimplifyFalseTrue.o: Debug/Assertion.hpp Debug/Tracer.hpp
Shell/SimplifyFalseTrue.o: Lib/Allocator.hpp Lib/Comparison.hpp
Shell/SimplifyFalseTrue.o: Lib/Random.hpp Lib/Reflection.hpp
Shell/SimplifyFalseTrue.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/SimplifyFalseTrue.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/SimplifyFalseTrue.o: Lib/Allocator.hpp Kernel/FormulaUnit.hpp
Shell/SimplifyFalseTrue.o: Kernel/Unit.hpp Shell/SimplifyFalseTrue.hpp
Shell/SimplifyFalseTrue.o: Kernel/Formula.hpp Lib/XML.hpp
Shell/SimplifyFalseTrue.o: Kernel/Connective.hpp
Shell/Skolem.o: Kernel/Signature.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/Skolem.o: Lib/Stack.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Skolem.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Shell/Skolem.o: Forwards.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/Skolem.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Skolem.o: Lib/Portability.hpp Lib/Map.hpp Lib/Hash.hpp Kernel/Term.hpp
Shell/Skolem.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/Skolem.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/Skolem.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/Skolem.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Rectify.hpp
Shell/Skolem.o: Lib/Array.hpp Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Skolem.o: Shell/Skolem.hpp Kernel/Substitution.hpp Lib/Random.hpp
Shell/Skolem.o: Lib/Environment.hpp Kernel/Term.hpp
Shell/Statistics.o: Lib/Environment.hpp Shell/Statistics.hpp
Shell/SymCounter.o: Lib/Allocator.hpp Debug/Tracer.hpp Kernel/Term.hpp
Shell/SymCounter.o: Forwards.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/SymCounter.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/SymCounter.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Shell/SymCounter.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/SymCounter.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/SymCounter.o: Lib/Portability.hpp Kernel/Clause.hpp
Shell/SymCounter.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Shell/SymCounter.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/Formula.hpp
Shell/SymCounter.o: Lib/List.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/SymCounter.o: Kernel/Signature.hpp Lib/Map.hpp Kernel/Unit.hpp
Shell/SymCounter.o: Shell/SymCounter.hpp
Shell/TPTP.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Shell/TPTP.o: Kernel/Term.hpp Forwards.hpp Debug/Assertion.hpp
Shell/TPTP.o: Debug/Tracer.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/TPTP.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/TPTP.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Shell/TPTP.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/TPTP.o: Lib/Reflection.hpp Lib/Int.hpp Kernel/Inference.hpp
Shell/TPTP.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp
Shell/TPTP.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/TPTP.o: Kernel/Clause.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Shell/TPTP.o: Lib/Hash.hpp Lib/Reflection.hpp Shell/TPTP.hpp
Shell/TPTPLexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Shell/TPTPLexer.o: Lib/Exception.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
Shell/TPTPLexer.o: Lib/Array.hpp Lib/Allocator.hpp Shell/Token.hpp
Shell/TPTPParser.o: Lib/List.hpp Forwards.hpp Debug/Assertion.hpp
Shell/TPTPParser.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/TPTPParser.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/TPTPParser.o: Lib/Reflection.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Shell/TPTPParser.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/TPTPParser.o: Lib/Portability.hpp Lib/Environment.hpp
Shell/TPTPParser.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/Allocator.hpp
Shell/TPTPParser.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Shell/TPTPParser.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/TPTPParser.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Kernel/Term.hpp
Shell/TPTPParser.o: Lib/Portability.hpp Lib/Comparison.hpp Kernel/Clause.hpp
Shell/TPTPParser.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Reflection.hpp
Shell/TPTPParser.o: Shell/Statistics.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/TPTPParser.o: Shell/Options.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
Shell/TPTPParser.o: Lib/Array.hpp Lib/Exception.hpp Shell/Token.hpp
Shell/TPTPParser.o: Shell/TPTPParser.hpp Shell/Parser.hpp
Shell/TPTPParser.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp
Shell/TheoryFinder.o: Debug/Tracer.hpp Kernel/Clause.hpp Forwards.hpp
Shell/TheoryFinder.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/List.hpp
Shell/TheoryFinder.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Shell/TheoryFinder.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Shell/TheoryFinder.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Shell/TheoryFinder.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/Formula.hpp
Shell/TheoryFinder.o: Lib/List.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/TheoryFinder.o: Kernel/FormulaUnit.hpp Kernel/Term.hpp
Shell/TheoryFinder.o: Lib/Portability.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/TheoryFinder.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/TheoryFinder.o: Lib/Portability.hpp Shell/Property.hpp Kernel/Unit.hpp
Shell/TheoryFinder.o: Shell/TheoryFinder.hpp
Shell/Token.o: Debug/Assertion.hpp Debug/Tracer.hpp Shell/Token.hpp
Kernel/Clause.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Kernel/Clause.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Inference.hpp
Kernel/Clause.o: Kernel/Unit.hpp Lib/List.hpp Forwards.hpp
Kernel/Clause.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/Clause.o: Lib/VirtualIterator.hpp Lib/Exception.hpp Lib/Reflection.hpp
Kernel/Clause.o: Kernel/Clause.hpp Lib/Metaiterators.hpp Lib/List.hpp
Kernel/Clause.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Kernel/Clause.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/Clause.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Kernel/Clause.o: Lib/Int.hpp Test/Output.hpp
Kernel/ClauseQueue.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Random.hpp
Kernel/ClauseQueue.o: Lib/Environment.hpp Kernel/Clause.hpp Forwards.hpp
Kernel/ClauseQueue.o: Lib/Metaiterators.hpp Lib/List.hpp Debug/Assertion.hpp
Kernel/ClauseQueue.o: Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/ClauseQueue.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/ClauseQueue.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/ClauseQueue.o: Lib/Reflection.hpp Kernel/Unit.hpp
Kernel/ClauseQueue.o: Kernel/ClauseQueue.hpp
Kernel/DoubleSubstitution.o: Lib/Int.hpp Lib/Comparison.hpp
Kernel/DoubleSubstitution.o: Lib/Portability.hpp Lib/DArray.hpp Forwards.hpp
Kernel/DoubleSubstitution.o: Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/DoubleSubstitution.o: Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/DoubleSubstitution.o: Lib/Random.hpp Lib/Reflection.hpp
Kernel/DoubleSubstitution.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/DoubleSubstitution.o: Kernel/Term.hpp Lib/Allocator.hpp
Kernel/DoubleSubstitution.o: Lib/Portability.hpp Lib/XML.hpp
Kernel/DoubleSubstitution.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/DoubleSubstitution.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/DoubleSubstitution.o: Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp
Kernel/DoubleSubstitution.o: Lib/Hash.hpp
Kernel/EqHelper.o: Kernel/EqHelper.hpp Forwards.hpp Lib/VirtualIterator.hpp
Kernel/EqHelper.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Kernel/EqHelper.o: Lib/Allocator.hpp Lib/Exception.hpp Lib/Reflection.hpp
Kernel/EqHelper.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/VirtualIterator.hpp
Kernel/EqHelper.o: Lib/Set.hpp Lib/Hash.hpp Lib/PairUtils.hpp
Kernel/EqHelper.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp Kernel/Term.hpp
Kernel/EqHelper.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/EqHelper.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Kernel/EqHelper.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/Formula.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/MultiCounter.hpp
Kernel/Formula.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/XML.hpp
Kernel/Formula.o: Kernel/Term.hpp Forwards.hpp Lib/Allocator.hpp
Kernel/Formula.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Formula.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/Formula.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Formula.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Formula.o: Lib/Portability.hpp Kernel/Formula.hpp Lib/List.hpp
Kernel/Formula.o: Kernel/Connective.hpp Kernel/SubformulaIterator.hpp
Kernel/Formula.o: Kernel/FormulaVarIterator.hpp
Kernel/FormulaUnit.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/FormulaUnit.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/List.hpp
Kernel/FormulaUnit.o: Forwards.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/FormulaUnit.o: Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/FormulaUnit.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/FormulaUnit.o: Lib/Reflection.hpp Lib/Allocator.hpp Kernel/Formula.hpp
Kernel/FormulaUnit.o: Lib/XML.hpp Kernel/Connective.hpp
Kernel/FormulaUnit.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Kernel/FormulaVarIterator.o: Debug/Tracer.hpp Kernel/FormulaVarIterator.hpp
Kernel/FormulaVarIterator.o: Lib/MultiCounter.hpp Debug/Assertion.hpp
Kernel/FormulaVarIterator.o: Debug/Tracer.hpp Lib/XML.hpp Kernel/Formula.hpp
Kernel/FormulaVarIterator.o: Lib/List.hpp Forwards.hpp Lib/Allocator.hpp
Kernel/FormulaVarIterator.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/FormulaVarIterator.o: Lib/Reflection.hpp Lib/XML.hpp
Kernel/FormulaVarIterator.o: Kernel/Connective.hpp Kernel/Term.hpp
Kernel/FormulaVarIterator.o: Lib/Allocator.hpp Lib/Portability.hpp
Kernel/FormulaVarIterator.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/FormulaVarIterator.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/FormulaVarIterator.o: Lib/Comparison.hpp Lib/Portability.hpp
Kernel/Inference.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Inference.o: Lib/List.hpp Forwards.hpp Debug/Assertion.hpp
Kernel/Inference.o: Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/Inference.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Inference.o: Lib/Reflection.hpp Lib/Allocator.hpp
Kernel/KBO.o: Debug/Tracer.hpp Lib/Environment.hpp Lib/Comparison.hpp
Kernel/KBO.o: Lib/DArray.hpp Forwards.hpp Debug/Assertion.hpp
Kernel/KBO.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Comparison.hpp
Kernel/KBO.o: Lib/Random.hpp Lib/Reflection.hpp Lib/VirtualIterator.hpp
Kernel/KBO.o: Lib/Exception.hpp Lib/DHMap.hpp Lib/Hash.hpp Lib/Int.hpp
Kernel/KBO.o: Lib/Portability.hpp Lib/Metaiterators.hpp Lib/List.hpp
Kernel/KBO.o: Lib/Set.hpp Kernel/Term.hpp Lib/Allocator.hpp
Kernel/KBO.o: Lib/Portability.hpp Lib/XML.hpp Lib/Stack.hpp
Kernel/KBO.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/KBO.hpp
Kernel/KBO.o: Kernel/Ordering.hpp Kernel/Signature.hpp Lib/Map.hpp
Kernel/LiteralSelector.o: Kernel/Term.hpp Forwards.hpp Debug/Assertion.hpp
Kernel/LiteralSelector.o: Debug/Tracer.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/LiteralSelector.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/LiteralSelector.o: Lib/Stack.hpp Lib/Allocator.hpp
Kernel/LiteralSelector.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/LiteralSelector.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/LiteralSelector.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/LiteralSelector.o: Lib/Portability.hpp Kernel/Clause.hpp
Kernel/LiteralSelector.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/LiteralSelector.o: Lib/Reflection.hpp Kernel/Unit.hpp
Kernel/LiteralSelector.o: Kernel/LiteralSelector.hpp
Kernel/MLMatcher.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp
Kernel/MLMatcher.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/MLMatcher.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Kernel/MLMatcher.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Kernel/MLMatcher.o: Lib/Comparison.hpp Lib/Portability.hpp
Kernel/MLMatcher.o: Lib/BacktrackIterators.hpp Lib/DArray.hpp Lib/Random.hpp
Kernel/MLMatcher.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Metaiterators.hpp
Kernel/MLMatcher.o: Lib/BinaryHeap.hpp Lib/DArray.hpp Lib/DHMap.hpp
Kernel/MLMatcher.o: Lib/Hash.hpp Lib/Int.hpp Lib/Metaarrays.hpp
Kernel/MLMatcher.o: Lib/PairUtils.hpp Lib/Metaarrays.hpp Lib/Stack.hpp
Kernel/MLMatcher.o: Kernel/Clause.hpp Lib/Allocator.hpp Lib/Metaiterators.hpp
Kernel/MLMatcher.o: Lib/Set.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Kernel/MLMatcher.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/MLMatcher.o: Lib/Comparison.hpp Kernel/Matcher.hpp Lib/Hash.hpp
Kernel/MLMatcher.o: Lib/VirtualIterator.hpp Kernel/MLMatcher.hpp
Kernel/MLMatcher.o: Test/Output.hpp
Kernel/MMSubstitution.o: Lib/Environment.hpp Lib/Hash.hpp Lib/DArray.hpp
Kernel/MMSubstitution.o: Forwards.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/MMSubstitution.o: Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/MMSubstitution.o: Lib/Comparison.hpp Lib/Random.hpp Lib/Reflection.hpp
Kernel/MMSubstitution.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/MMSubstitution.o: Lib/List.hpp Lib/Random.hpp Lib/DHMultiset.hpp
Kernel/MMSubstitution.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/DHMap.hpp
Kernel/MMSubstitution.o: Lib/SkipList.hpp Lib/BacktrackData.hpp Lib/List.hpp
Kernel/MMSubstitution.o: Lib/Int.hpp Lib/Portability.hpp Lib/Int.hpp
Kernel/MMSubstitution.o: Kernel/Term.hpp Lib/Allocator.hpp
Kernel/MMSubstitution.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/MMSubstitution.o: Lib/Stack.hpp Kernel/Clause.hpp
Kernel/MMSubstitution.o: Lib/Metaiterators.hpp Lib/Set.hpp Lib/Reflection.hpp
Kernel/MMSubstitution.o: Kernel/Unit.hpp Kernel/Renaming.hpp
Kernel/MMSubstitution.o: Lib/VirtualIterator.hpp Indexing/TermSharing.hpp
Kernel/MMSubstitution.o: Lib/Set.hpp Kernel/Term.hpp
Kernel/MMSubstitution.o: Kernel/MMSubstitution.hpp Lib/BacktrackData.hpp
Kernel/MMSubstitution.o: Test/Output.hpp
Kernel/Ordering.o: Lib/Environment.hpp Lib/Exception.hpp Shell/Options.hpp
Kernel/Ordering.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/XML.hpp
Kernel/Ordering.o: Kernel/Ordering.hpp Forwards.hpp Kernel/KBO.hpp
Kernel/OrderingLiteralSelector.o: Lib/List.hpp Forwards.hpp
Kernel/OrderingLiteralSelector.o: Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/OrderingLiteralSelector.o: Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/OrderingLiteralSelector.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/OrderingLiteralSelector.o: Lib/Reflection.hpp Kernel/Term.hpp
Kernel/OrderingLiteralSelector.o: Lib/Allocator.hpp Lib/Portability.hpp
Kernel/OrderingLiteralSelector.o: Lib/XML.hpp Lib/Comparison.hpp
Kernel/OrderingLiteralSelector.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Kernel/OrderingLiteralSelector.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/OrderingLiteralSelector.o: Lib/Portability.hpp Kernel/Clause.hpp
Kernel/OrderingLiteralSelector.o: Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/OrderingLiteralSelector.o: Lib/Hash.hpp Lib/Reflection.hpp
Kernel/OrderingLiteralSelector.o: Kernel/Unit.hpp
Kernel/OrderingLiteralSelector.o: Kernel/OrderingLiteralSelector.hpp
Kernel/OrderingLiteralSelector.o: Lib/SmartPtr.hpp Kernel/Ordering.hpp
Kernel/OrderingLiteralSelector.o: Kernel/LiteralSelector.hpp
Kernel/Renaming.o: Lib/DArray.hpp Forwards.hpp Debug/Assertion.hpp
Kernel/Renaming.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/Renaming.o: Lib/Comparison.hpp Lib/Random.hpp Lib/Reflection.hpp
Kernel/Renaming.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Renaming.o: Indexing/TermSharing.hpp Lib/Set.hpp Lib/Hash.hpp
Kernel/Renaming.o: Kernel/Term.hpp Lib/Allocator.hpp Lib/Portability.hpp
Kernel/Renaming.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Kernel/Renaming.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/Renaming.o: Lib/Portability.hpp Kernel/Renaming.hpp Lib/DHMap.hpp
Kernel/Renaming.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Kernel/Renaming.o: Kernel/Term.hpp Lib/Int.hpp
Kernel/Signature.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/Signature.o: Kernel/Signature.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/Signature.o: Lib/Stack.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/Signature.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Kernel/Signature.o: Forwards.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Signature.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Map.hpp Lib/Hash.hpp
Kernel/SubformulaIterator.o: Debug/Tracer.hpp Kernel/SubformulaIterator.hpp
Kernel/SubformulaIterator.o: Kernel/Formula.hpp Lib/List.hpp Forwards.hpp
Kernel/SubformulaIterator.o: Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/SubformulaIterator.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Kernel/SubformulaIterator.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/XML.hpp
Kernel/SubformulaIterator.o: Kernel/Connective.hpp
Kernel/Substitution.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Kernel/Substitution.o: Kernel/Term.hpp Forwards.hpp Debug/Assertion.hpp
Kernel/Substitution.o: Debug/Tracer.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Kernel/Substitution.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Substitution.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/Substitution.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Substitution.o: Lib/Reflection.hpp Lib/Int.hpp Kernel/Substitution.hpp
Kernel/Substitution.o: Lib/Random.hpp Lib/Environment.hpp
Kernel/Term.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Environment.hpp
Kernel/Term.o: Lib/Stack.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/Term.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Kernel/Term.o: Forwards.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Term.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Term.o: Lib/Portability.hpp Lib/Int.hpp Kernel/Signature.hpp
Kernel/Term.o: Lib/Map.hpp Lib/Hash.hpp Kernel/Substitution.hpp
Kernel/Term.o: Lib/Random.hpp Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/Term.o: Lib/Comparison.hpp Kernel/Ordering.hpp
Kernel/Term.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
Kernel/Term.o: Test/Output.hpp
Kernel/TermFunIterator.o: Debug/Tracer.hpp Kernel/Term.hpp Forwards.hpp
Kernel/TermFunIterator.o: Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/TermFunIterator.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/TermFunIterator.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermFunIterator.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/TermFunIterator.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/TermFunIterator.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/TermFunIterator.o: Lib/Portability.hpp Kernel/TermFunIterator.hpp
Kernel/TermVarIterator.o: Debug/Tracer.hpp Kernel/Term.hpp Forwards.hpp
Kernel/TermVarIterator.o: Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/TermVarIterator.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/TermVarIterator.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermVarIterator.o: Lib/BacktrackData.hpp Lib/List.hpp
Kernel/TermVarIterator.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/TermVarIterator.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/TermVarIterator.o: Lib/Portability.hpp Kernel/TermVarIterator.hpp
Kernel/Unit.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Unit.o: Lib/Portability.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Unit.o: Lib/List.hpp Forwards.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/Unit.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Kernel/Unit.o: Lib/Reflection.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Indexing/Index.o: Indexing/Index.hpp Forwards.hpp Kernel/MMSubstitution.hpp
Indexing/Index.o: Lib/DHMap.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/Index.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
Indexing/Index.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Lib/Reflection.hpp
Indexing/Index.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Indexing/Index.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Term.hpp
Indexing/Index.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/Index.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Indexing/Index.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/Index.o: Lib/VirtualIterator.hpp Saturation/ClauseContainer.hpp
Indexing/IndexManager.o: Lib/Exception.hpp Saturation/SaturationAlgorithm.hpp
Indexing/IndexManager.o: Forwards.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Indexing/IndexManager.o: Debug/Tracer.hpp Lib/Metaiterators.hpp Lib/List.hpp
Indexing/IndexManager.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/IndexManager.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Indexing/IndexManager.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp
Indexing/IndexManager.o: Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Indexing/IndexManager.o: Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/IndexManager.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Indexing/IndexManager.o: Indexing/Index.hpp Kernel/MMSubstitution.hpp
Indexing/IndexManager.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/IndexManager.o: Lib/Portability.hpp Kernel/Term.hpp
Indexing/IndexManager.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Indexing/IndexManager.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Indexing/IndexManager.o: Lib/VirtualIterator.hpp
Indexing/IndexManager.o: Saturation/ClauseContainer.hpp
Indexing/IndexManager.o: Inferences/InferenceEngine.hpp Lib/SmartPtr.hpp
Indexing/IndexManager.o: Lib/List.hpp Saturation/Limits.hpp
Indexing/IndexManager.o: Saturation/SaturationResult.hpp Shell/Statistics.hpp
Indexing/IndexManager.o: Lib/Environment.hpp Indexing/LiteralIndex.hpp
Indexing/IndexManager.o: Indexing/LiteralSubstitutionTree.hpp
Indexing/IndexManager.o: Indexing/LiteralIndexingStructure.hpp
Indexing/IndexManager.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/IndexManager.o: Lib/SkipList.hpp Lib/Random.hpp Lib/BinaryHeap.hpp
Indexing/IndexManager.o: Kernel/DoubleSubstitution.hpp Kernel/Matcher.hpp
Indexing/IndexManager.o: Lib/Hash.hpp Kernel/Renaming.hpp Test/Output.hpp
Indexing/IndexManager.o: Indexing/TermIndex.hpp
Indexing/IndexManager.o: Indexing/TermSubstitutionTree.hpp
Indexing/IndexManager.o: Indexing/TermIndexingStructure.hpp
Indexing/IndexManager.o: Indexing/IndexManager.hpp
Indexing/LiteralIndex.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Indexing/LiteralIndex.o: Debug/Tracer.hpp Lib/Metaiterators.hpp Lib/List.hpp
Indexing/LiteralIndex.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/LiteralIndex.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Indexing/LiteralIndex.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp
Indexing/LiteralIndex.o: Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Indexing/LiteralIndex.o: Indexing/LiteralIndexingStructure.hpp
Indexing/LiteralIndex.o: Indexing/Index.hpp Kernel/MMSubstitution.hpp
Indexing/LiteralIndex.o: Lib/DHMap.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/LiteralIndex.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/LiteralIndex.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/LiteralIndex.o: Lib/Comparison.hpp Lib/Stack.hpp
Indexing/LiteralIndex.o: Lib/BacktrackData.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/LiteralIndex.o: Lib/Exception.hpp Lib/VirtualIterator.hpp
Indexing/LiteralIndex.o: Saturation/ClauseContainer.hpp
Indexing/LiteralIndex.o: Indexing/LiteralIndex.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Environment.hpp Lib/Metaiterators.hpp
Indexing/LiteralSubstitutionTree.o: Forwards.hpp Lib/List.hpp
Indexing/LiteralSubstitutionTree.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/LiteralSubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Reflection.hpp Lib/Set.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Hash.hpp Kernel/Signature.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Allocator.hpp Lib/Stack.hpp
Indexing/LiteralSubstitutionTree.o: Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Map.hpp Kernel/Term.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Portability.hpp Lib/XML.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Comparison.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/LiteralSubstitutionTree.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/LiteralIndexingStructure.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/Index.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Indexing/LiteralSubstitutionTree.o: Lib/BacktrackData.hpp Kernel/Term.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Exception.hpp Lib/VirtualIterator.hpp
Indexing/LiteralSubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/LiteralSubstitutionTree.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/LiteralSubstitutionTree.o: Lib/List.hpp Lib/SkipList.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Random.hpp Lib/BinaryHeap.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/DoubleSubstitution.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/Matcher.hpp Lib/Hash.hpp
Indexing/LiteralSubstitutionTree.o: Kernel/Renaming.hpp Kernel/Clause.hpp
Indexing/LiteralSubstitutionTree.o: Lib/Reflection.hpp Kernel/Unit.hpp
Indexing/LiteralSubstitutionTree.o: Test/Output.hpp
Indexing/SubstitutionTree.o: Kernel/Term.hpp Forwards.hpp Debug/Assertion.hpp
Indexing/SubstitutionTree.o: Debug/Tracer.hpp Debug/Tracer.hpp
Indexing/SubstitutionTree.o: Lib/Allocator.hpp Lib/Portability.hpp
Indexing/SubstitutionTree.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Indexing/SubstitutionTree.o: Lib/Allocator.hpp Lib/BacktrackData.hpp
Indexing/SubstitutionTree.o: Lib/List.hpp Lib/VirtualIterator.hpp
Indexing/SubstitutionTree.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Indexing/SubstitutionTree.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/SubstitutionTree.o: Kernel/Renaming.hpp Lib/DHMap.hpp Lib/Hash.hpp
Indexing/SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Metaiterators.hpp
Indexing/SubstitutionTree.o: Lib/Set.hpp Kernel/Term.hpp Lib/BinaryHeap.hpp
Indexing/SubstitutionTree.o: Lib/Environment.hpp Indexing/TermSharing.hpp
Indexing/SubstitutionTree.o: Lib/Set.hpp Kernel/Signature.hpp Lib/Map.hpp
Indexing/SubstitutionTree.o: Lib/Int.hpp Test/Output.hpp
Indexing/SubstitutionTree.o: Indexing/SubstitutionTree.hpp Lib/List.hpp
Indexing/SubstitutionTree.o: Lib/SkipList.hpp Lib/Random.hpp
Indexing/SubstitutionTree.o: Lib/BacktrackData.hpp
Indexing/SubstitutionTree.o: Kernel/DoubleSubstitution.hpp
Indexing/SubstitutionTree.o: Kernel/MMSubstitution.hpp Kernel/Matcher.hpp
Indexing/SubstitutionTree.o: Lib/Hash.hpp Kernel/Clause.hpp
Indexing/SubstitutionTree.o: Lib/Reflection.hpp Kernel/Unit.hpp
Indexing/SubstitutionTree.o: Indexing/Index.hpp Lib/Event.hpp
Indexing/SubstitutionTree.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/SubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/VirtualIterator.hpp Forwards.hpp
Indexing/SubstitutionTree_Nodes.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/SubstitutionTree_Nodes.o: Debug/Tracer.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Exception.hpp Lib/Reflection.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/List.hpp Lib/VirtualIterator.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/SkipList.hpp Lib/Comparison.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Random.hpp Lib/BacktrackData.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/List.hpp Lib/Int.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Portability.hpp Lib/DHMultiset.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Hash.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Metaiterators.hpp Lib/Set.hpp
Indexing/SubstitutionTree_Nodes.o: Indexing/Index.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BacktrackData.hpp Kernel/Term.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Allocator.hpp Lib/Portability.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/XML.hpp Lib/Comparison.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Stack.hpp Lib/Event.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/SubstitutionTree_Nodes.o: Saturation/ClauseContainer.hpp
Indexing/SubstitutionTree_Nodes.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BinaryHeap.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/DoubleSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/Matcher.hpp Lib/Hash.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/Renaming.hpp Kernel/Clause.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Reflection.hpp Kernel/Unit.hpp
Indexing/SubstitutionTree_Nodes.o: Test/Output.hpp
Indexing/TermIndex.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Indexing/TermIndex.o: Debug/Tracer.hpp Lib/Metaiterators.hpp Lib/List.hpp
Indexing/TermIndex.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Indexing/TermIndex.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/TermIndex.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Indexing/TermIndex.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/Term.hpp
Indexing/TermIndex.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Indexing/TermIndex.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/TermIndex.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/TermIndex.o: Kernel/Ordering.hpp Kernel/EqHelper.hpp
Indexing/TermIndex.o: Lib/VirtualIterator.hpp Lib/PairUtils.hpp
Indexing/TermIndex.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Indexing/TermIndex.o: Kernel/Term.hpp Indexing/TermIndexingStructure.hpp
Indexing/TermIndex.o: Indexing/Index.hpp Kernel/MMSubstitution.hpp
Indexing/TermIndex.o: Lib/DHMap.hpp Lib/BacktrackData.hpp Lib/Event.hpp
Indexing/TermIndex.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/TermIndex.o: Saturation/ClauseContainer.hpp Indexing/TermIndex.hpp
Indexing/TermSharing.o: Kernel/Term.hpp Forwards.hpp Debug/Assertion.hpp
Indexing/TermSharing.o: Debug/Tracer.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Indexing/TermSharing.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Indexing/TermSharing.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Indexing/TermSharing.o: Lib/List.hpp Lib/VirtualIterator.hpp
Indexing/TermSharing.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Indexing/TermSharing.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/TermSharing.o: Indexing/TermSharing.hpp Lib/Set.hpp Lib/Hash.hpp
Indexing/TermSubstitutionTree.o: Lib/Environment.hpp Lib/Metaiterators.hpp
Indexing/TermSubstitutionTree.o: Forwards.hpp Lib/List.hpp
Indexing/TermSubstitutionTree.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/TermSubstitutionTree.o: Lib/Allocator.hpp Debug/Tracer.hpp
Indexing/TermSubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Indexing/TermSubstitutionTree.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Indexing/TermSubstitutionTree.o: Lib/SmartPtr.hpp Kernel/Signature.hpp
Indexing/TermSubstitutionTree.o: Lib/Allocator.hpp Lib/Stack.hpp
Indexing/TermSubstitutionTree.o: Lib/BacktrackData.hpp Lib/Int.hpp
Indexing/TermSubstitutionTree.o: Lib/Comparison.hpp Lib/Portability.hpp
Indexing/TermSubstitutionTree.o: Lib/Map.hpp Kernel/Term.hpp
Indexing/TermSubstitutionTree.o: Lib/Portability.hpp Lib/XML.hpp
Indexing/TermSubstitutionTree.o: Lib/Comparison.hpp
Indexing/TermSubstitutionTree.o: Indexing/TermSubstitutionTree.hpp
Indexing/TermSubstitutionTree.o: Lib/SkipList.hpp Lib/Random.hpp
Indexing/TermSubstitutionTree.o: Indexing/Index.hpp Kernel/MMSubstitution.hpp
Indexing/TermSubstitutionTree.o: Lib/DHMap.hpp Lib/BacktrackData.hpp
Indexing/TermSubstitutionTree.o: Kernel/Term.hpp Lib/Event.hpp
Indexing/TermSubstitutionTree.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/TermSubstitutionTree.o: Lib/VirtualIterator.hpp
Indexing/TermSubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/TermSubstitutionTree.o: Indexing/TermIndexingStructure.hpp
Indexing/TermSubstitutionTree.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/TermSubstitutionTree.o: Lib/List.hpp Lib/BinaryHeap.hpp
Indexing/TermSubstitutionTree.o: Kernel/DoubleSubstitution.hpp
Indexing/TermSubstitutionTree.o: Kernel/Matcher.hpp Lib/Hash.hpp
Indexing/TermSubstitutionTree.o: Kernel/Renaming.hpp Kernel/Clause.hpp
Indexing/TermSubstitutionTree.o: Lib/Reflection.hpp Kernel/Unit.hpp
Indexing/TermSubstitutionTree.o: Test/Output.hpp
Inferences/BinaryResolution.o: Lib/Environment.hpp Lib/Int.hpp
Inferences/BinaryResolution.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/BinaryResolution.o: Lib/Metaiterators.hpp Forwards.hpp
Inferences/BinaryResolution.o: Lib/List.hpp Debug/Assertion.hpp
Inferences/BinaryResolution.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/BinaryResolution.o: Debug/Tracer.hpp Lib/VirtualIterator.hpp
Inferences/BinaryResolution.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/BinaryResolution.o: Lib/Set.hpp Lib/Hash.hpp Lib/PairUtils.hpp
Inferences/BinaryResolution.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/BinaryResolution.o: Lib/VirtualIterator.hpp Shell/Statistics.hpp
Inferences/BinaryResolution.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/BinaryResolution.o: Lib/Reflection.hpp Kernel/Unit.hpp
Inferences/BinaryResolution.o: Kernel/Unit.hpp Lib/List.hpp
Inferences/BinaryResolution.o: Kernel/Inference.hpp Indexing/Index.hpp
Inferences/BinaryResolution.o: Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Inferences/BinaryResolution.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/BinaryResolution.o: Kernel/Term.hpp Lib/Portability.hpp
Inferences/BinaryResolution.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Inferences/BinaryResolution.o: Lib/BacktrackData.hpp Lib/Event.hpp
Inferences/BinaryResolution.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/BinaryResolution.o: Saturation/ClauseContainer.hpp
Inferences/BinaryResolution.o: Indexing/LiteralIndex.hpp Indexing/Index.hpp
Inferences/BinaryResolution.o: Indexing/IndexManager.hpp
Inferences/BinaryResolution.o: Saturation/SaturationAlgorithm.hpp
Inferences/BinaryResolution.o: Inferences/InferenceEngine.hpp
Inferences/BinaryResolution.o: Lib/SmartPtr.hpp Saturation/Limits.hpp
Inferences/BinaryResolution.o: Saturation/SaturationResult.hpp
Inferences/BinaryResolution.o: Inferences/BinaryResolution.hpp
Inferences/BinaryResolution.o: Inferences/InferenceEngine.hpp
Inferences/EqualityFactoring.o: Lib/VirtualIterator.hpp Forwards.hpp
Inferences/EqualityFactoring.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/EqualityFactoring.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/EqualityFactoring.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/EqualityFactoring.o: Lib/Metaiterators.hpp Lib/List.hpp
Inferences/EqualityFactoring.o: Lib/VirtualIterator.hpp Lib/Set.hpp
Inferences/EqualityFactoring.o: Lib/Hash.hpp Lib/PairUtils.hpp
Inferences/EqualityFactoring.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/EqualityFactoring.o: Lib/Environment.hpp Shell/Statistics.hpp
Inferences/EqualityFactoring.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/EqualityFactoring.o: Lib/Reflection.hpp Kernel/Unit.hpp
Inferences/EqualityFactoring.o: Kernel/Unit.hpp Lib/List.hpp
Inferences/EqualityFactoring.o: Kernel/Inference.hpp
Inferences/EqualityFactoring.o: Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Inferences/EqualityFactoring.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/EqualityFactoring.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/EqualityFactoring.o: Kernel/Term.hpp Lib/Portability.hpp
Inferences/EqualityFactoring.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Inferences/EqualityFactoring.o: Lib/BacktrackData.hpp Kernel/EqHelper.hpp
Inferences/EqualityFactoring.o: Kernel/Ordering.hpp
Inferences/EqualityFactoring.o: Inferences/EqualityFactoring.hpp
Inferences/EqualityFactoring.o: Inferences/InferenceEngine.hpp
Inferences/EqualityResolution.o: Lib/VirtualIterator.hpp Forwards.hpp
Inferences/EqualityResolution.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/EqualityResolution.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/EqualityResolution.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/EqualityResolution.o: Lib/Metaiterators.hpp Lib/List.hpp
Inferences/EqualityResolution.o: Lib/VirtualIterator.hpp Lib/Set.hpp
Inferences/EqualityResolution.o: Lib/Hash.hpp Lib/PairUtils.hpp
Inferences/EqualityResolution.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/EqualityResolution.o: Lib/Environment.hpp Shell/Statistics.hpp
Inferences/EqualityResolution.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/EqualityResolution.o: Lib/Reflection.hpp Kernel/Unit.hpp
Inferences/EqualityResolution.o: Kernel/Unit.hpp Lib/List.hpp
Inferences/EqualityResolution.o: Kernel/Inference.hpp
Inferences/EqualityResolution.o: Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Inferences/EqualityResolution.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/EqualityResolution.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/EqualityResolution.o: Kernel/Term.hpp Lib/Portability.hpp
Inferences/EqualityResolution.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Inferences/EqualityResolution.o: Lib/BacktrackData.hpp Kernel/EqHelper.hpp
Inferences/EqualityResolution.o: Kernel/Ordering.hpp
Inferences/EqualityResolution.o: Inferences/EqualityResolution.hpp
Inferences/EqualityResolution.o: Inferences/InferenceEngine.hpp
Inferences/Factoring.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Inferences/Factoring.o: Lib/VirtualIterator.hpp Forwards.hpp
Inferences/Factoring.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Inferences/Factoring.o: Lib/Allocator.hpp Lib/Exception.hpp
Inferences/Factoring.o: Lib/Reflection.hpp Lib/Metaiterators.hpp Lib/List.hpp
Inferences/Factoring.o: Lib/VirtualIterator.hpp Lib/Set.hpp Lib/Hash.hpp
Inferences/Factoring.o: Lib/Comparison.hpp Lib/PairUtils.hpp
Inferences/Factoring.o: Lib/Metaiterators.hpp Lib/Metaarrays.hpp
Inferences/Factoring.o: Lib/Environment.hpp Shell/Statistics.hpp
Inferences/Factoring.o: Kernel/Clause.hpp Lib/Allocator.hpp
Inferences/Factoring.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/Unit.hpp
Inferences/Factoring.o: Lib/List.hpp Kernel/Inference.hpp
Inferences/Factoring.o: Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Inferences/Factoring.o: Lib/BacktrackData.hpp Lib/Int.hpp Kernel/Term.hpp
Inferences/Factoring.o: Lib/Portability.hpp Lib/XML.hpp Lib/Stack.hpp
Inferences/Factoring.o: Lib/BacktrackData.hpp Inferences/Factoring.hpp
Inferences/Factoring.o: Inferences/InferenceEngine.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/VirtualIterator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Forwards.hpp
Inferences/ForwardSubsumptionAndResolution.o: Debug/Assertion.hpp
Inferences/ForwardSubsumptionAndResolution.o: Debug/Tracer.hpp
Inferences/ForwardSubsumptionAndResolution.o: Debug/Tracer.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Allocator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Exception.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Reflection.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/BacktrackData.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/List.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/VirtualIterator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Int.hpp Lib/Comparison.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Portability.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/SkipList.hpp Lib/Random.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/BacktrackData.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/DArray.hpp Lib/List.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/DHMap.hpp Lib/Hash.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/DHMultiset.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/DHMap.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Comparison.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Metaiterators.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Set.hpp Kernel/Term.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Allocator.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Stack.hpp Kernel/Clause.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Reflection.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Unit.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Inference.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Unit.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/MMSubstitution.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/Term.hpp
Inferences/ForwardSubsumptionAndResolution.o: Kernel/MLMatcher.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/Index.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Event.hpp Lib/SmartPtr.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Exception.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/ClauseContainer.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/LiteralIndex.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/Index.hpp
Inferences/ForwardSubsumptionAndResolution.o: Indexing/IndexManager.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/SaturationAlgorithm.hpp
Inferences/ForwardSubsumptionAndResolution.o: Inferences/InferenceEngine.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/SmartPtr.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/Limits.hpp
Inferences/ForwardSubsumptionAndResolution.o: Saturation/SaturationResult.hpp
Inferences/ForwardSubsumptionAndResolution.o: Shell/Statistics.hpp
Inferences/ForwardSubsumptionAndResolution.o: Lib/Environment.hpp
Inferences/ForwardSubsumptionAndResolution.o: Inferences/ForwardSubsumptionAndResolution.hpp
Inferences/ForwardSubsumptionAndResolution.o: Inferences/InferenceEngine.hpp
Inferences/InferenceEngine.o: Lib/Environment.hpp Lib/Random.hpp
Inferences/InferenceEngine.o: Lib/DArray.hpp Forwards.hpp Debug/Assertion.hpp
Inferences/InferenceEngine.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/InferenceEngine.o: Debug/Tracer.hpp Lib/Comparison.hpp
Inferences/InferenceEngine.o: Lib/Random.hpp Lib/Reflection.hpp
Inferences/InferenceEngine.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/InferenceEngine.o: Lib/List.hpp Lib/Metaiterators.hpp Lib/List.hpp
Inferences/InferenceEngine.o: Lib/Set.hpp Lib/Hash.hpp Kernel/Term.hpp
Inferences/InferenceEngine.o: Lib/Allocator.hpp Lib/Portability.hpp
Inferences/InferenceEngine.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Inferences/InferenceEngine.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/InferenceEngine.o: Lib/Portability.hpp Kernel/Clause.hpp
Inferences/InferenceEngine.o: Lib/Reflection.hpp Kernel/Unit.hpp
Inferences/InferenceEngine.o: Kernel/Inference.hpp Kernel/Unit.hpp
Inferences/InferenceEngine.o: Shell/Statistics.hpp
Inferences/InferenceEngine.o: Inferences/InferenceEngine.hpp
Inferences/RefutationSeekerFSE.o: Lib/VirtualIterator.hpp Forwards.hpp
Inferences/RefutationSeekerFSE.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/RefutationSeekerFSE.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/RefutationSeekerFSE.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/RefutationSeekerFSE.o: Lib/Metaiterators.hpp Lib/List.hpp
Inferences/RefutationSeekerFSE.o: Lib/VirtualIterator.hpp Lib/Set.hpp
Inferences/RefutationSeekerFSE.o: Lib/Hash.hpp Lib/Int.hpp Lib/Comparison.hpp
Inferences/RefutationSeekerFSE.o: Lib/Portability.hpp Kernel/Unit.hpp
Inferences/RefutationSeekerFSE.o: Lib/List.hpp Kernel/Inference.hpp
Inferences/RefutationSeekerFSE.o: Lib/Allocator.hpp Kernel/Clause.hpp
Inferences/RefutationSeekerFSE.o: Lib/Reflection.hpp Kernel/Unit.hpp
Inferences/RefutationSeekerFSE.o: Indexing/Index.hpp
Inferences/RefutationSeekerFSE.o: Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Inferences/RefutationSeekerFSE.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/RefutationSeekerFSE.o: Kernel/Term.hpp Lib/Portability.hpp
Inferences/RefutationSeekerFSE.o: Lib/XML.hpp Lib/Comparison.hpp
Inferences/RefutationSeekerFSE.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Inferences/RefutationSeekerFSE.o: Lib/Event.hpp Lib/SmartPtr.hpp
Inferences/RefutationSeekerFSE.o: Lib/Exception.hpp
Inferences/RefutationSeekerFSE.o: Saturation/ClauseContainer.hpp
Inferences/RefutationSeekerFSE.o: Indexing/LiteralIndex.hpp
Inferences/RefutationSeekerFSE.o: Indexing/Index.hpp
Inferences/RefutationSeekerFSE.o: Indexing/IndexManager.hpp
Inferences/RefutationSeekerFSE.o: Saturation/SaturationAlgorithm.hpp
Inferences/RefutationSeekerFSE.o: Inferences/InferenceEngine.hpp
Inferences/RefutationSeekerFSE.o: Lib/SmartPtr.hpp Saturation/Limits.hpp
Inferences/RefutationSeekerFSE.o: Saturation/SaturationResult.hpp
Inferences/RefutationSeekerFSE.o: Shell/Statistics.hpp Lib/Environment.hpp
Inferences/RefutationSeekerFSE.o: Inferences/RefutationSeekerFSE.hpp
Inferences/RefutationSeekerFSE.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/VirtualIterator.hpp Forwards.hpp
Inferences/SLQueryBackwardSubsumption.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/SLQueryBackwardSubsumption.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/BacktrackData.hpp Lib/List.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/VirtualIterator.hpp Lib/Int.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Comparison.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Portability.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/BinaryHeap.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/BacktrackData.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/SkipList.hpp Lib/Random.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/DArray.hpp Lib/List.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/DHMap.hpp Lib/Hash.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/DHMultiset.hpp Lib/DHMap.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Comparison.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Metaiterators.hpp Lib/Set.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/Term.hpp Lib/Allocator.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Portability.hpp Lib/XML.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Stack.hpp Kernel/Clause.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Reflection.hpp Kernel/Unit.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/MMSubstitution.hpp
Inferences/SLQueryBackwardSubsumption.o: Kernel/Term.hpp Kernel/MLMatcher.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/Index.hpp Lib/Event.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/ClauseContainer.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/LiteralIndex.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/Index.hpp
Inferences/SLQueryBackwardSubsumption.o: Indexing/IndexManager.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/SaturationAlgorithm.hpp
Inferences/SLQueryBackwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/SmartPtr.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/Limits.hpp
Inferences/SLQueryBackwardSubsumption.o: Saturation/SaturationResult.hpp
Inferences/SLQueryBackwardSubsumption.o: Shell/Statistics.hpp
Inferences/SLQueryBackwardSubsumption.o: Lib/Environment.hpp
Inferences/SLQueryBackwardSubsumption.o: Inferences/SLQueryBackwardSubsumption.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/VirtualIterator.hpp Forwards.hpp
Inferences/SLQueryForwardSubsumption.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/SLQueryForwardSubsumption.o: Debug/Tracer.hpp Lib/Allocator.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Exception.hpp Lib/Reflection.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/BacktrackData.hpp Lib/List.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/VirtualIterator.hpp Lib/Int.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Comparison.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Portability.hpp Lib/SkipList.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Random.hpp Lib/BacktrackData.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/DArray.hpp Lib/List.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/DHMap.hpp Lib/Hash.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/DHMultiset.hpp Lib/DHMap.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Comparison.hpp Kernel/Term.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Allocator.hpp Lib/Portability.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/XML.hpp Lib/Stack.hpp
Inferences/SLQueryForwardSubsumption.o: Kernel/Clause.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Metaiterators.hpp Lib/Set.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Reflection.hpp Kernel/Unit.hpp
Inferences/SLQueryForwardSubsumption.o: Kernel/MMSubstitution.hpp
Inferences/SLQueryForwardSubsumption.o: Kernel/Term.hpp Kernel/MLMatcher.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/Index.hpp Lib/Event.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/ClauseContainer.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/LiteralIndex.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/Index.hpp
Inferences/SLQueryForwardSubsumption.o: Indexing/IndexManager.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/SaturationAlgorithm.hpp
Inferences/SLQueryForwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/SmartPtr.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/Limits.hpp
Inferences/SLQueryForwardSubsumption.o: Saturation/SaturationResult.hpp
Inferences/SLQueryForwardSubsumption.o: Shell/Statistics.hpp
Inferences/SLQueryForwardSubsumption.o: Lib/Environment.hpp
Inferences/SLQueryForwardSubsumption.o: Inferences/SLQueryForwardSubsumption.hpp
Inferences/SLQueryForwardSubsumption.o: Inferences/InferenceEngine.hpp
Inferences/Superposition.o: Lib/Environment.hpp Lib/Int.hpp
Inferences/Superposition.o: Lib/Comparison.hpp Lib/Portability.hpp
Inferences/Superposition.o: Lib/Metaiterators.hpp Forwards.hpp Lib/List.hpp
Inferences/Superposition.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/Superposition.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/Superposition.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Inferences/Superposition.o: Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Inferences/Superposition.o: Lib/PairUtils.hpp Lib/Metaiterators.hpp
Inferences/Superposition.o: Lib/Metaarrays.hpp Lib/VirtualIterator.hpp
Inferences/Superposition.o: Shell/Statistics.hpp Kernel/Term.hpp
Inferences/Superposition.o: Lib/Allocator.hpp Lib/Portability.hpp Lib/XML.hpp
Inferences/Superposition.o: Lib/Comparison.hpp Lib/Stack.hpp
Inferences/Superposition.o: Lib/BacktrackData.hpp Lib/Int.hpp
Inferences/Superposition.o: Kernel/Clause.hpp Lib/Reflection.hpp
Inferences/Superposition.o: Kernel/Unit.hpp Kernel/Unit.hpp Lib/List.hpp
Inferences/Superposition.o: Kernel/Inference.hpp Kernel/Ordering.hpp
Inferences/Superposition.o: Kernel/EqHelper.hpp Kernel/Term.hpp
Inferences/Superposition.o: Indexing/Index.hpp Kernel/MMSubstitution.hpp
Inferences/Superposition.o: Lib/DHMap.hpp Lib/BacktrackData.hpp Lib/Event.hpp
Inferences/Superposition.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Inferences/Superposition.o: Saturation/ClauseContainer.hpp
Inferences/Superposition.o: Indexing/IndexManager.hpp Indexing/Index.hpp
Inferences/Superposition.o: Indexing/TermSharing.hpp Lib/Set.hpp
Inferences/Superposition.o: Saturation/SaturationAlgorithm.hpp
Inferences/Superposition.o: Inferences/InferenceEngine.hpp Lib/SmartPtr.hpp
Inferences/Superposition.o: Saturation/Limits.hpp
Inferences/Superposition.o: Saturation/SaturationResult.hpp
Inferences/Superposition.o: Inferences/Superposition.hpp
Inferences/Superposition.o: Indexing/TermIndex.hpp
Inferences/Superposition.o: Inferences/InferenceEngine.hpp
Inferences/TautologyDeletionFSE.o: Lib/Random.hpp Lib/Environment.hpp
Inferences/TautologyDeletionFSE.o: Lib/DArray.hpp Forwards.hpp
Inferences/TautologyDeletionFSE.o: Debug/Assertion.hpp Debug/Tracer.hpp
Inferences/TautologyDeletionFSE.o: Lib/Allocator.hpp Debug/Tracer.hpp
Inferences/TautologyDeletionFSE.o: Lib/Comparison.hpp Lib/Random.hpp
Inferences/TautologyDeletionFSE.o: Lib/Reflection.hpp Lib/VirtualIterator.hpp
Inferences/TautologyDeletionFSE.o: Lib/Exception.hpp Kernel/Term.hpp
Inferences/TautologyDeletionFSE.o: Lib/Allocator.hpp Lib/Portability.hpp
Inferences/TautologyDeletionFSE.o: Lib/XML.hpp Lib/Comparison.hpp
Inferences/TautologyDeletionFSE.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Inferences/TautologyDeletionFSE.o: Lib/List.hpp Lib/Int.hpp
Inferences/TautologyDeletionFSE.o: Lib/Portability.hpp Kernel/Clause.hpp
Inferences/TautologyDeletionFSE.o: Lib/Metaiterators.hpp Lib/Set.hpp
Inferences/TautologyDeletionFSE.o: Lib/Hash.hpp Lib/Reflection.hpp
Inferences/TautologyDeletionFSE.o: Kernel/Unit.hpp Shell/Statistics.hpp
Inferences/TautologyDeletionFSE.o: Inferences/TautologyDeletionFSE.hpp
Inferences/TautologyDeletionFSE.o: Inferences/InferenceEngine.hpp
Rule/CASC.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Rule/CASC.o: Lib/Portability.hpp Lib/Sort.hpp Debug/Assertion.hpp
Rule/CASC.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Environment.hpp
Rule/CASC.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Rule/CASC.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/VirtualIterator.hpp
Rule/CASC.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Rule/CASC.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/Signature.hpp
Rule/CASC.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp Lib/Map.hpp
Rule/CASC.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Rule/CASC.o: Lib/Comparison.hpp Rule/Rule.hpp Rule/CASC.hpp Kernel/Unit.hpp
Rule/CASC.o: Lib/List.hpp Lib/Array.hpp
Rule/Index.o: Lib/Stack.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Rule/Index.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Rule/Index.o: Lib/List.hpp Forwards.hpp Lib/VirtualIterator.hpp
Rule/Index.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Int.hpp
Rule/Index.o: Lib/Comparison.hpp Lib/Portability.hpp Kernel/Clause.hpp
Rule/Index.o: Lib/Allocator.hpp Lib/Metaiterators.hpp Lib/Set.hpp
Rule/Index.o: Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Rule/Index.o: Kernel/Signature.hpp Lib/Map.hpp Kernel/Term.hpp
Rule/Index.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Rule/Index.o: Indexing/Index.hpp Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Rule/Index.o: Lib/BacktrackData.hpp Kernel/Term.hpp Lib/Event.hpp
Rule/Index.o: Lib/SmartPtr.hpp Lib/Exception.hpp Lib/VirtualIterator.hpp
Rule/Index.o: Saturation/ClauseContainer.hpp
Rule/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Rule/Profile.o: Lib/Portability.hpp Lib/Sort.hpp Debug/Assertion.hpp
Rule/Profile.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Environment.hpp
Rule/Profile.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Rule/Profile.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/VirtualIterator.hpp
Rule/Profile.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Set.hpp Lib/Hash.hpp
Rule/Profile.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/Signature.hpp
Rule/Profile.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp Lib/Map.hpp
Rule/Profile.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Rule/Profile.o: Lib/Comparison.hpp Shell/Profile.hpp Kernel/Unit.hpp
Rule/Profile.o: Lib/List.hpp Lib/Array.hpp
Rule/Prolog.o: Kernel/Term.hpp Forwards.hpp Debug/Assertion.hpp
Rule/Prolog.o: Debug/Tracer.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Rule/Prolog.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Rule/Prolog.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Rule/Prolog.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Rule/Prolog.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Rule/Prolog.o: Lib/Portability.hpp Kernel/Clause.hpp Lib/Metaiterators.hpp
Rule/Prolog.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Rule/Prolog.o: Rule/Prolog.hpp Lib/Map.hpp Rule/Index.hpp Kernel/Unit.hpp
Rule/Prolog.o: Lib/List.hpp Rule/Rule.hpp
Rule/ProofAttempt.o: Debug/Tracer.hpp Lib/Environment.hpp
Rule/ProofAttempt.o: Shell/Statistics.hpp Rule/ProofAttempt.hpp
Rule/ProofAttempt.o: Kernel/Unit.hpp Lib/List.hpp Forwards.hpp
Rule/ProofAttempt.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Rule/ProofAttempt.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
Rule/ProofAttempt.o: Lib/Reflection.hpp
SAT/Assignment.o: Debug/Tracer.hpp SAT/Assignment.hpp Debug/Assertion.hpp
SAT/Assignment.o: Debug/Tracer.hpp SAT/SAT.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Environment.hpp Kernel/Term.hpp
Saturation/AWPassiveClauseContainer.o: Forwards.hpp Debug/Assertion.hpp
Saturation/AWPassiveClauseContainer.o: Debug/Tracer.hpp Debug/Tracer.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Allocator.hpp Lib/Portability.hpp
Saturation/AWPassiveClauseContainer.o: Lib/XML.hpp Lib/Comparison.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Stack.hpp Lib/Allocator.hpp
Saturation/AWPassiveClauseContainer.o: Lib/BacktrackData.hpp Lib/List.hpp
Saturation/AWPassiveClauseContainer.o: Lib/VirtualIterator.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Exception.hpp Lib/Reflection.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Int.hpp Lib/Comparison.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Portability.hpp Kernel/Clause.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Metaiterators.hpp Lib/Set.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Hash.hpp Lib/Reflection.hpp
Saturation/AWPassiveClauseContainer.o: Kernel/Unit.hpp Shell/Statistics.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/AWPassiveClauseContainer.hpp
Saturation/AWPassiveClauseContainer.o: Kernel/ClauseQueue.hpp
Saturation/AWPassiveClauseContainer.o: Saturation/ClauseContainer.hpp
Saturation/AWPassiveClauseContainer.o: Lib/Event.hpp Lib/SmartPtr.hpp
Saturation/AWPassiveClauseContainer.o: Lib/VirtualIterator.hpp
Saturation/ClauseContainer.o: Lib/Environment.hpp Kernel/Clause.hpp
Saturation/ClauseContainer.o: Forwards.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Saturation/ClauseContainer.o: Lib/Metaiterators.hpp Lib/List.hpp
Saturation/ClauseContainer.o: Debug/Assertion.hpp Debug/Tracer.hpp
Saturation/ClauseContainer.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Saturation/ClauseContainer.o: Lib/Exception.hpp Lib/Reflection.hpp
Saturation/ClauseContainer.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Saturation/ClauseContainer.o: Kernel/Unit.hpp Shell/Statistics.hpp
Saturation/ClauseContainer.o: Saturation/ClauseContainer.hpp Lib/Event.hpp
Saturation/ClauseContainer.o: Lib/SmartPtr.hpp Lib/VirtualIterator.hpp
Saturation/ClauseContainer.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
Saturation/ClauseContainer.o: Lib/Comparison.hpp Lib/Portability.hpp
Saturation/Discount.o: Lib/Environment.hpp Lib/VirtualIterator.hpp
Saturation/Discount.o: Forwards.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Saturation/Discount.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Exception.hpp
Saturation/Discount.o: Lib/Reflection.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Saturation/Discount.o: Lib/Metaiterators.hpp Lib/List.hpp
Saturation/Discount.o: Lib/VirtualIterator.hpp Lib/Set.hpp Lib/Hash.hpp
Saturation/Discount.o: Lib/Reflection.hpp Kernel/Unit.hpp
Saturation/Discount.o: Kernel/LiteralSelector.hpp Shell/Statistics.hpp
Saturation/Discount.o: Saturation/Discount.hpp
Saturation/Discount.o: Saturation/SaturationAlgorithm.hpp Lib/Event.hpp
Saturation/Discount.o: Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Saturation/Discount.o: Lib/DHMap.hpp Indexing/Index.hpp
Saturation/Discount.o: Kernel/MMSubstitution.hpp Lib/BacktrackData.hpp
Saturation/Discount.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Saturation/Discount.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Saturation/Discount.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Saturation/Discount.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
Saturation/Discount.o: Inferences/InferenceEngine.hpp Lib/SmartPtr.hpp
Saturation/Discount.o: Lib/List.hpp Saturation/Limits.hpp
Saturation/Discount.o: Saturation/SaturationResult.hpp
Saturation/Otter.o: Lib/Environment.hpp Lib/VirtualIterator.hpp Forwards.hpp
Saturation/Otter.o: Debug/Assertion.hpp Debug/Tracer.hpp Debug/Tracer.hpp
Saturation/Otter.o: Lib/Allocator.hpp Lib/Exception.hpp Lib/Reflection.hpp
Saturation/Otter.o: Kernel/Clause.hpp Lib/Allocator.hpp Lib/Metaiterators.hpp
Saturation/Otter.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Set.hpp
Saturation/Otter.o: Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Saturation/Otter.o: Kernel/LiteralSelector.hpp Shell/Statistics.hpp
Saturation/Otter.o: Saturation/Otter.hpp Saturation/SaturationAlgorithm.hpp
Saturation/Otter.o: Lib/Event.hpp Lib/SmartPtr.hpp Indexing/IndexManager.hpp
Saturation/Otter.o: Lib/DHMap.hpp Indexing/Index.hpp
Saturation/Otter.o: Kernel/MMSubstitution.hpp Lib/BacktrackData.hpp
Saturation/Otter.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
Saturation/Otter.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Saturation/Otter.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Saturation/Otter.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
Saturation/Otter.o: Inferences/InferenceEngine.hpp Lib/SmartPtr.hpp
Saturation/Otter.o: Lib/List.hpp Saturation/Limits.hpp
Saturation/Otter.o: Saturation/SaturationResult.hpp
Saturation/SaturationAlgorithm.o: Lib/Environment.hpp Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm.o: Forwards.hpp Debug/Assertion.hpp
Saturation/SaturationAlgorithm.o: Debug/Tracer.hpp Debug/Tracer.hpp
Saturation/SaturationAlgorithm.o: Lib/Allocator.hpp Lib/Exception.hpp
Saturation/SaturationAlgorithm.o: Lib/Reflection.hpp Kernel/Clause.hpp
Saturation/SaturationAlgorithm.o: Lib/Allocator.hpp Lib/Metaiterators.hpp
Saturation/SaturationAlgorithm.o: Lib/List.hpp Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Saturation/SaturationAlgorithm.o: Kernel/Unit.hpp Kernel/LiteralSelector.hpp
Saturation/SaturationAlgorithm.o: Shell/Statistics.hpp
Saturation/SaturationAlgorithm.o: Saturation/SaturationAlgorithm.hpp
Saturation/SaturationAlgorithm.o: Lib/Event.hpp Lib/SmartPtr.hpp
Saturation/SaturationAlgorithm.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Saturation/SaturationAlgorithm.o: Indexing/Index.hpp
Saturation/SaturationAlgorithm.o: Kernel/MMSubstitution.hpp
Saturation/SaturationAlgorithm.o: Lib/BacktrackData.hpp Lib/Int.hpp
Saturation/SaturationAlgorithm.o: Lib/Comparison.hpp Lib/Portability.hpp
Saturation/SaturationAlgorithm.o: Kernel/Term.hpp Lib/Portability.hpp
Saturation/SaturationAlgorithm.o: Lib/XML.hpp Lib/Comparison.hpp
Saturation/SaturationAlgorithm.o: Lib/Stack.hpp Lib/BacktrackData.hpp
Saturation/SaturationAlgorithm.o: Lib/Exception.hpp
Saturation/SaturationAlgorithm.o: Saturation/ClauseContainer.hpp
Saturation/SaturationAlgorithm.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm.o: Lib/SmartPtr.hpp Lib/List.hpp
Saturation/SaturationAlgorithm.o: Saturation/Limits.hpp
Saturation/SaturationAlgorithm.o: Saturation/SaturationResult.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Exception.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/KBO.hpp Forwards.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Ordering.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/OrderingLiteralSelector.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/SmartPtr.hpp
Saturation/SaturationAlgorithm_Construction.o: Debug/Assertion.hpp
Saturation/SaturationAlgorithm_Construction.o: Debug/Tracer.hpp
Saturation/SaturationAlgorithm_Construction.o: Debug/Tracer.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/LiteralSelector.hpp
Saturation/SaturationAlgorithm_Construction.o: Shell/Options.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Allocator.hpp Lib/XML.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Allocator.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Exception.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Reflection.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/List.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/VirtualIterator.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/BinaryResolution.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/InferenceEngine.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/EqualityFactoring.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/Factoring.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/ForwardSubsumptionAndResolution.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/RefutationSeekerFSE.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/SLQueryForwardSubsumption.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/SLQueryBackwardSubsumption.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/Superposition.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/TermIndex.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/Index.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/MMSubstitution.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/DHMap.hpp Lib/Hash.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/BacktrackData.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/List.hpp Lib/Int.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Comparison.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Portability.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Term.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Portability.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Comparison.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Stack.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/BacktrackData.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Event.hpp Lib/SmartPtr.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/ClauseContainer.hpp
Saturation/SaturationAlgorithm_Construction.o: Inferences/TautologyDeletionFSE.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/AWPassiveClauseContainer.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/ClauseQueue.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/ClauseContainer.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/SaturationAlgorithm.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Clause.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Metaiterators.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Set.hpp Lib/Reflection.hpp
Saturation/SaturationAlgorithm_Construction.o: Kernel/Unit.hpp
Saturation/SaturationAlgorithm_Construction.o: Indexing/IndexManager.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Limits.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/SaturationResult.hpp
Saturation/SaturationAlgorithm_Construction.o: Shell/Statistics.hpp
Saturation/SaturationAlgorithm_Construction.o: Lib/Environment.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Discount.hpp
Saturation/SaturationAlgorithm_Construction.o: Saturation/Otter.hpp
Saturation/SaturationResult.o: Kernel/Clause.hpp Forwards.hpp
Saturation/SaturationResult.o: Lib/Allocator.hpp Debug/Tracer.hpp
Saturation/SaturationResult.o: Lib/Metaiterators.hpp Lib/List.hpp
Saturation/SaturationResult.o: Debug/Assertion.hpp Debug/Tracer.hpp
Saturation/SaturationResult.o: Lib/Allocator.hpp Lib/VirtualIterator.hpp
Saturation/SaturationResult.o: Lib/Exception.hpp Lib/Reflection.hpp
Saturation/SaturationResult.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp
Saturation/SaturationResult.o: Kernel/Unit.hpp
Saturation/SaturationResult.o: Saturation/SaturationResult.hpp
Saturation/SaturationResult.o: Shell/Statistics.hpp Lib/Environment.hpp
Test/Output.o: Debug/Assertion.hpp Debug/Tracer.hpp Kernel/Term.hpp
Test/Output.o: Forwards.hpp Debug/Tracer.hpp Lib/Allocator.hpp
Test/Output.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Test/Output.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Test/Output.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
Test/Output.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Comparison.hpp
Test/Output.o: Lib/Portability.hpp Kernel/Clause.hpp Lib/Metaiterators.hpp
Test/Output.o: Lib/Set.hpp Lib/Hash.hpp Lib/Reflection.hpp Kernel/Unit.hpp
Test/Output.o: Lib/Int.hpp Test/Output.hpp Lib/Environment.hpp
Test/Output.o: Kernel/Signature.hpp Lib/Map.hpp
Global.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Enumerator.hpp
Global.o: Kernel/Formula.hpp Lib/List.hpp Forwards.hpp Debug/Assertion.hpp
Global.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/VirtualIterator.hpp
Global.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/XML.hpp
Global.o: Kernel/Connective.hpp Kernel/Unit.hpp Lib/Environment.hpp
alucard.o: Forwards.hpp Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
alucard.o: Lib/Random.hpp Lib/Set.hpp Lib/Allocator.hpp Lib/Hash.hpp
alucard.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp Lib/Timer.hpp
alucard.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
alucard.o: Lib/Environment.hpp Lib/Vector.hpp Lib/VirtualIterator.hpp
alucard.o: Forwards.hpp Lib/Exception.hpp Lib/Reflection.hpp
alucard.o: Lib/Metaiterators.hpp Lib/List.hpp Lib/VirtualIterator.hpp
alucard.o: Lib/Set.hpp Kernel/Signature.hpp Lib/Allocator.hpp Lib/Stack.hpp
alucard.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Map.hpp Kernel/Clause.hpp
alucard.o: Lib/Metaiterators.hpp Lib/Reflection.hpp Kernel/Unit.hpp
alucard.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp Kernel/Connective.hpp
alucard.o: Kernel/FormulaUnit.hpp Kernel/KBO.hpp Kernel/Ordering.hpp
alucard.o: Kernel/LiteralSelector.hpp Kernel/OrderingLiteralSelector.hpp
alucard.o: Lib/SmartPtr.hpp Kernel/LiteralSelector.hpp
alucard.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
alucard.o: Lib/Portability.hpp Lib/Comparison.hpp Shell/Options.hpp
alucard.o: Shell/CommandLine.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
alucard.o: Lib/Array.hpp Lib/Exception.hpp Shell/Token.hpp Shell/TPTP.hpp
alucard.o: Shell/TPTPParser.hpp Kernel/Unit.hpp Shell/Parser.hpp
alucard.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp Shell/Property.hpp
alucard.o: Shell/Preprocess.hpp Shell/Statistics.hpp Shell/Refutation.hpp
alucard.o: Shell/TheoryFinder.hpp Saturation/AWPassiveClauseContainer.hpp
alucard.o: Kernel/ClauseQueue.hpp Saturation/ClauseContainer.hpp
alucard.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/VirtualIterator.hpp
alucard.o: Saturation/SaturationAlgorithm.hpp Kernel/Clause.hpp
alucard.o: Indexing/IndexManager.hpp Lib/DHMap.hpp Indexing/Index.hpp
alucard.o: Kernel/MMSubstitution.hpp Lib/BacktrackData.hpp Kernel/Term.hpp
alucard.o: Saturation/ClauseContainer.hpp Inferences/InferenceEngine.hpp
alucard.o: Saturation/Limits.hpp Saturation/SaturationResult.hpp
alucard.o: Shell/Statistics.hpp Lib/Environment.hpp Saturation/Discount.hpp
alucard.o: Saturation/SaturationAlgorithm.hpp Saturation/Otter.hpp
alucard.o: Inferences/InferenceEngine.hpp Inferences/BinaryResolution.hpp
alucard.o: Inferences/InferenceEngine.hpp Inferences/Factoring.hpp
alucard.o: Inferences/ForwardSubsumptionAndResolution.hpp
alucard.o: Inferences/RefutationSeekerFSE.hpp
alucard.o: Inferences/SLQueryForwardSubsumption.hpp
alucard.o: Inferences/SLQueryBackwardSubsumption.hpp
alucard.o: Inferences/TautologyDeletionFSE.hpp Lib/MemoryLeak.hpp
sat.o: Lib/Random.hpp
test_BinaryHeap.o: Lib/BinaryHeap.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_BinaryHeap.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
test_BinaryHeap.o: Lib/Comparison.hpp Lib/BacktrackData.hpp Lib/List.hpp
test_BinaryHeap.o: Forwards.hpp Lib/VirtualIterator.hpp Lib/Reflection.hpp
test_BinaryHeap.o: Lib/Int.hpp Lib/Portability.hpp Lib/Int.hpp
test_DHMap.o: Lib/DHMap.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_DHMap.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
test_DHMap.o: Lib/Hash.hpp Lib/VirtualIterator.hpp Forwards.hpp
test_DHMap.o: Lib/Reflection.hpp
test_DHMultiset.o: Lib/DHMultiset.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_DHMultiset.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Exception.hpp
test_DHMultiset.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/VirtualIterator.hpp
test_DHMultiset.o: Forwards.hpp Lib/Reflection.hpp
test_SkipList.o: Lib/SkipList.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_SkipList.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Comparison.hpp
test_SkipList.o: Lib/Random.hpp Lib/BacktrackData.hpp Lib/List.hpp
test_SkipList.o: Forwards.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
test_SkipList.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Portability.hpp
test_SkipList.o: Lib/BinaryHeap.hpp Lib/DHMultiset.hpp Lib/Hash.hpp
test_SkipList.o: Lib/DHMap.hpp Lib/Int.hpp Lib/DArray.hpp Lib/Timer.hpp
test_SkipList.o: Lib/Random.hpp
test_SubstitutionTree.o: Debug/Tracer.hpp Lib/Array.hpp Debug/Assertion.hpp
test_SubstitutionTree.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
test_SubstitutionTree.o: Lib/Random.hpp Lib/Set.hpp Lib/Allocator.hpp
test_SubstitutionTree.o: Lib/Hash.hpp Lib/Int.hpp Lib/Comparison.hpp
test_SubstitutionTree.o: Lib/Portability.hpp Lib/Timer.hpp Lib/Exception.hpp
test_SubstitutionTree.o: Lib/Environment.hpp Lib/Vector.hpp
test_SubstitutionTree.o: Kernel/Signature.hpp Lib/Stack.hpp
test_SubstitutionTree.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp
test_SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
test_SubstitutionTree.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Map.hpp
test_SubstitutionTree.o: Kernel/Clause.hpp Lib/Metaiterators.hpp Lib/Set.hpp
test_SubstitutionTree.o: Lib/Reflection.hpp Kernel/Unit.hpp
test_SubstitutionTree.o: Kernel/Formula.hpp Lib/List.hpp Lib/XML.hpp
test_SubstitutionTree.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
test_SubstitutionTree.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
test_SubstitutionTree.o: Lib/Portability.hpp Lib/Comparison.hpp
test_SubstitutionTree.o: Indexing/SubstitutionTree.hpp
test_SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Int.hpp Lib/SkipList.hpp
test_SubstitutionTree.o: Lib/Random.hpp Lib/BinaryHeap.hpp
test_SubstitutionTree.o: Lib/BacktrackData.hpp Kernel/DoubleSubstitution.hpp
test_SubstitutionTree.o: Lib/DHMap.hpp Kernel/Term.hpp
test_SubstitutionTree.o: Kernel/MMSubstitution.hpp Kernel/Matcher.hpp
test_SubstitutionTree.o: Lib/Hash.hpp Kernel/Renaming.hpp Kernel/Clause.hpp
test_SubstitutionTree.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
test_SubstitutionTree.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp
test_SubstitutionTree.o: Test/Output.hpp Shell/Options.hpp
test_SubstitutionTree.o: Shell/CommandLine.hpp Shell/TPTPLexer.hpp
test_SubstitutionTree.o: Shell/Lexer.hpp Lib/Array.hpp Shell/Token.hpp
test_SubstitutionTree.o: Shell/TPTP.hpp Shell/TPTPParser.hpp Kernel/Unit.hpp
test_SubstitutionTree.o: Shell/Parser.hpp Lib/IntNameTable.hpp Lib/Array.hpp
test_SubstitutionTree.o: Lib/Map.hpp Shell/Property.hpp Shell/Preprocess.hpp
test_SubstitutionTree.o: Shell/Statistics.hpp Shell/Refutation.hpp
test_SubstitutionTree.o: Shell/TheoryFinder.hpp Rule/CASC.hpp Rule/Prolog.hpp
test_SubstitutionTree.o: Rule/Index.hpp Rule/Rule.hpp Rule/Index.hpp
test_SubstitutionTree.o: Rule/ProofAttempt.hpp Test/Output.hpp
test_SubstitutionTree.o: Lib/MemoryLeak.hpp
test_alloc.o: Lib/Allocator.hpp Debug/Tracer.hpp
test_retrieval.o: Debug/Tracer.hpp Lib/Array.hpp Debug/Assertion.hpp
test_retrieval.o: Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
test_retrieval.o: Lib/Random.hpp Lib/Set.hpp Lib/Allocator.hpp Lib/Hash.hpp
test_retrieval.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp
test_retrieval.o: Lib/Timer.hpp Lib/Exception.hpp Lib/Environment.hpp
test_retrieval.o: Lib/Vector.hpp Kernel/Signature.hpp Lib/Stack.hpp
test_retrieval.o: Lib/BacktrackData.hpp Lib/List.hpp Forwards.hpp
test_retrieval.o: Lib/VirtualIterator.hpp Lib/Exception.hpp
test_retrieval.o: Lib/Reflection.hpp Lib/Int.hpp Lib/Map.hpp
test_retrieval.o: Kernel/Clause.hpp Lib/Metaiterators.hpp Lib/Set.hpp
test_retrieval.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/Formula.hpp
test_retrieval.o: Lib/List.hpp Lib/XML.hpp Kernel/Connective.hpp
test_retrieval.o: Kernel/FormulaUnit.hpp Indexing/TermSharing.hpp Lib/Set.hpp
test_retrieval.o: Kernel/Term.hpp Lib/Portability.hpp Lib/Comparison.hpp
test_retrieval.o: Indexing/SubstitutionTree.hpp Lib/VirtualIterator.hpp
test_retrieval.o: Lib/Int.hpp Lib/SkipList.hpp Lib/Random.hpp
test_retrieval.o: Lib/BinaryHeap.hpp Lib/BacktrackData.hpp
test_retrieval.o: Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp Kernel/Term.hpp
test_retrieval.o: Kernel/MMSubstitution.hpp Kernel/Matcher.hpp Lib/Hash.hpp
test_retrieval.o: Kernel/Renaming.hpp Kernel/Clause.hpp Indexing/Index.hpp
test_retrieval.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
test_retrieval.o: Saturation/ClauseContainer.hpp Test/Output.hpp
test_retrieval.o: Shell/Options.hpp Shell/CommandLine.hpp Shell/TPTPLexer.hpp
test_retrieval.o: Shell/Lexer.hpp Lib/Array.hpp Shell/Token.hpp
test_retrieval.o: Shell/TPTP.hpp Shell/TPTPParser.hpp Kernel/Unit.hpp
test_retrieval.o: Shell/Parser.hpp Lib/IntNameTable.hpp Lib/Array.hpp
test_retrieval.o: Lib/Map.hpp Shell/Property.hpp Shell/Preprocess.hpp
test_retrieval.o: Shell/Statistics.hpp Shell/Refutation.hpp
test_retrieval.o: Shell/TheoryFinder.hpp Rule/CASC.hpp Rule/Prolog.hpp
test_retrieval.o: Rule/Index.hpp Rule/Rule.hpp Rule/Index.hpp
test_retrieval.o: Rule/ProofAttempt.hpp Test/Output.hpp Lib/MemoryLeak.hpp
vampire.o: Debug/Tracer.hpp Lib/Random.hpp Lib/Set.hpp Lib/Allocator.hpp
vampire.o: Debug/Tracer.hpp Lib/Hash.hpp Lib/Int.hpp Lib/Comparison.hpp
vampire.o: Lib/Portability.hpp Lib/Timer.hpp Debug/Assertion.hpp
vampire.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/Environment.hpp
vampire.o: Lib/Vector.hpp Lib/System.hpp Lib/Metaiterators.hpp Forwards.hpp
vampire.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Exception.hpp
vampire.o: Lib/Reflection.hpp Lib/Set.hpp Kernel/Signature.hpp
vampire.o: Lib/Allocator.hpp Lib/Stack.hpp Lib/BacktrackData.hpp Lib/Int.hpp
vampire.o: Lib/Map.hpp Kernel/Clause.hpp Lib/Metaiterators.hpp
vampire.o: Lib/Reflection.hpp Kernel/Unit.hpp Kernel/Formula.hpp Lib/List.hpp
vampire.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
vampire.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
vampire.o: Lib/Portability.hpp Lib/Comparison.hpp
vampire.o: Indexing/SubstitutionTree.hpp Lib/VirtualIterator.hpp Lib/Int.hpp
vampire.o: Lib/SkipList.hpp Lib/Random.hpp Lib/BinaryHeap.hpp
vampire.o: Lib/BacktrackData.hpp Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp
vampire.o: Kernel/Term.hpp Kernel/MMSubstitution.hpp Kernel/Matcher.hpp
vampire.o: Lib/Hash.hpp Kernel/Renaming.hpp Kernel/Clause.hpp
vampire.o: Indexing/Index.hpp Lib/Event.hpp Lib/SmartPtr.hpp
vampire.o: Lib/Exception.hpp Saturation/ClauseContainer.hpp Test/Output.hpp
vampire.o: Shell/Options.hpp Shell/CommandLine.hpp Shell/TPTPLexer.hpp
vampire.o: Shell/Lexer.hpp Lib/Array.hpp Shell/Token.hpp Shell/TPTP.hpp
vampire.o: Shell/TPTPParser.hpp Kernel/Unit.hpp Shell/Parser.hpp
vampire.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp Shell/Property.hpp
vampire.o: Shell/Preprocess.hpp Shell/Statistics.hpp Shell/Refutation.hpp
vampire.o: Saturation/SaturationAlgorithm.hpp Indexing/IndexManager.hpp
vampire.o: Inferences/InferenceEngine.hpp Lib/SmartPtr.hpp
vampire.o: Saturation/Limits.hpp Saturation/SaturationResult.hpp
vampire.o: Shell/Statistics.hpp Lib/Environment.hpp Lib/MemoryLeak.hpp
vcompit.o: Forwards.hpp Debug/Tracer.hpp Lib/Allocator.hpp Debug/Tracer.hpp
vcompit.o: Lib/Random.hpp Lib/Set.hpp Lib/Allocator.hpp Lib/Hash.hpp
vcompit.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Portability.hpp Lib/Timer.hpp
vcompit.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
vcompit.o: Lib/Environment.hpp Lib/VirtualIterator.hpp Forwards.hpp
vcompit.o: Lib/Exception.hpp Lib/Reflection.hpp Lib/Metaiterators.hpp
vcompit.o: Lib/List.hpp Lib/VirtualIterator.hpp Lib/Set.hpp
vcompit.o: Kernel/Signature.hpp Lib/Allocator.hpp Lib/Stack.hpp
vcompit.o: Lib/BacktrackData.hpp Lib/Int.hpp Lib/Map.hpp Kernel/Term.hpp
vcompit.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
vcompit.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
vcompit.o: Indexing/TermSubstitutionTree.hpp Lib/SkipList.hpp Lib/Random.hpp
vcompit.o: Indexing/Index.hpp Kernel/MMSubstitution.hpp Lib/DHMap.hpp
vcompit.o: Lib/BacktrackData.hpp Kernel/Term.hpp Lib/Event.hpp
vcompit.o: Lib/SmartPtr.hpp Lib/Exception.hpp Lib/VirtualIterator.hpp
vcompit.o: Saturation/ClauseContainer.hpp Indexing/TermIndexingStructure.hpp
vcompit.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp Lib/List.hpp
vcompit.o: Lib/BinaryHeap.hpp Kernel/DoubleSubstitution.hpp
vcompit.o: Kernel/Matcher.hpp Lib/Hash.hpp Kernel/Renaming.hpp
vcompit.o: Lib/Metaiterators.hpp Kernel/Clause.hpp Lib/Reflection.hpp
vcompit.o: Kernel/Unit.hpp Test/Output.hpp Shell/Options.hpp
vcompit.o: Shell/CommandLine.hpp Shell/Property.hpp Kernel/Unit.hpp
vcompit.o: Shell/Preprocess.hpp Shell/Statistics.hpp
