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
#XFLAGS = -g -DVDEBUG=0 -DCHECK_LEAKS=0 # debug mode without VDEBUG macro 
#XFLAGS = -fprofile-arcs -pg -g -DVDEBUG=0 # profiling
XFLAGS = -g -DVDEBUG=1 -DCHECK_LEAKS=0 # standard debugging only
#XFLAGS = -O6 -DVDEBUG=0 # no debugging
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
        Kernel/Formula.o\
        Kernel/FormulaUnit.o\
        Kernel/FormulaVarIterator.o\
        Kernel/Inference.o\
        Kernel/LiteralSelector.o\
        Kernel/MMSubstitution.o\
        Kernel/Signature.o\
        Kernel/SubformulaIterator.o\
        Kernel/Substitution.o\
        Kernel/Term.o\
        Kernel/TermFunIterator.o\
        Kernel/TermVarIterator.o\
        Kernel/Unit.o

VI_OBJ = Indexing/Index.o\
         Indexing/IndexManager.o\
         Indexing/TermSharing.o\
         Indexing/SubstitutionTree.o\
         Indexing/SubstitutionTree_Nodes.o

VINF_OBJ=Inferences/BinaryResolution.o

VST_OBJ= Saturation/AWPassiveClauseContainer.o\
         Saturation/ClauseContainer.o\
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

VRES_OBJ = Resolution/Active.o\
           Resolution/BinaryResolution.o\
           Resolution/Passive.o\
           Resolution/ProofAttempt.o\
           Resolution/Tautology.o\
           Resolution/Unprocessed.o

VRULE_OBJ = Rule/Index.o\
            Rule/CASC.o\
            Rule/Prolog.o\
            Rule/ProofAttempt.o

# testing procedures
VT_OBJ = Test/Output.o

SAT = SAT/Assignment.o
#      SAT/Watch2.o\
#      SAT/Clause.o\
#      SAT/AssignmentStack.o


# MathSat
#MS_OBJ = MathSat/Expression.o\
#         MathSat/Lexer.o\
#         MathSat/Parser.o
#
#RESOLUTION_OBJ = Resolution/Atom.o\
#                 Resolution/Clause.o\
#                 Resolution/FlatClause.o\
#                 Resolution/Inference.o\
#                 Resolution/KBO.o\
#                 Resolution/Literal.o\
#                 Resolution/Passive.o\
#                 Resolution/ProofAgent.o\
#                 Resolution/SubstitutionTree.o\
#                 Resolution/Term.o
#
#DPLL_OBJ=DPLL/Assignment.o\
#         DPLL/Prover.o\
#         DPLL/Unassigned.o
#
#SHELL_OBJ= Shell/Atom.o\

VAMP_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VS_OBJ) $(VRES_OBJ) $(VRULE_OBJ) $(SAT) $(VT_OBJ)  
ALUC_BASIC = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ)  

VAMPIRE_OBJ = $(VAMP_BASIC) Global.o vampire.o
SAT_OBJ = $(VD_OBJ) $(SAT) sat.o
TEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ) Global.o test_SubstitutionTree.o
RTEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VINF_OBJ) $(VST_OBJ) $(VS_OBJ) $(VT_OBJ) Global.o test_retrieval.o
DHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_DHMap.o
DHMSTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_DHMultiset.o
BHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_BinaryHeap.o
SLTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_SkipList.o
ALUCARD_OBJ = $(ALUC_BASIC) Global.o alucard.o

################################################################

all:#default make disabled

dracula: $(VAMPIRE_OBJ)
	$(CXX) $(CXXFLAGS) $(VAMPIRE_OBJ) -o dracula
	strip dracula

vampire: $(VAMPIRE_OBJ)
	$(CXX) $(CXXFLAGS) $(VAMPIRE_OBJ) -o vampire
	strip vampire

vamp: $(VAMPIRE_OBJ)
	$(CXX) $(CXXFLAGS) $(VAMPIRE_OBJ) -o vamp
	strip vamp

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


dhtest: $(DHTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(DHTEST_OBJ) -o test_DHMap

dhmstest: $(DHMSTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(DHMSTEST_OBJ) -o test_DHMultiset

bhtest: $(BHTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(BHTEST_OBJ) -o test_BinaryHeap

sltest: $(SLTEST_OBJ)
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
	cd Resolution ; rm -f *.o *~ *.bak ; cd ..
	cd Rule ; rm -f *.o *~ *.bak ; cd ..
	cd SAT ; rm -f *.o *~ *.bak ; cd ..
	cd Saturation ; rm -f *.o *~ *.bak ; cd ..
	cd Test ; rm -f *.o *~ *.bak ; cd ..
	rm -f *.o *~ *.bak

depend:
	makedepend -Y $(XFLAGS) Debug/*.cpp Lib/*.cpp Shell/*.cpp Kernel/*.cpp Indexing/*.cpp Resolution/*.cpp Rule/*.cpp SAT/*.cpp Test/*.cpp *.cpp

.PHONY: doc
doc:
	rm -fr doc/html
	doxygen config.doc

# DO NOT DELETE

Debug/Assertion.o: Debug/Assertion.hpp Debug/Tracer.hpp
Debug/Tracer.o: Debug/Tracer.hpp
Lib/Allocator.o: Debug/Assertion.hpp Debug/Tracer.hpp Shell/Statistics.hpp
Lib/Allocator.o: Lib/Exception.hpp Lib/Environment.hpp Lib/Allocator.hpp
Lib/DHMap.o: Lib/DHMap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Lib/DHMap.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/Hash.hpp
Lib/Environment.o: Debug/Tracer.hpp Lib/Timer.hpp Debug/Assertion.hpp
Lib/Environment.o: Lib/Environment.hpp Shell/Options.hpp Lib/Allocator.hpp
Lib/Environment.o: Lib/XML.hpp Shell/Statistics.hpp
Lib/Event.o: Lib/Event.hpp Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Lib/Event.o: Debug/Tracer.hpp Lib/SmartPtr.hpp
Lib/Exception.o: Lib/Exception.hpp
Lib/Hash.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Hash.hpp
Lib/Int.o: Lib/Int.hpp Lib/Comparison.hpp Debug/Tracer.hpp
Lib/IntNameTable.o: Lib/IntNameTable.hpp Lib/Array.hpp Debug/Assertion.hpp
Lib/IntNameTable.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Map.hpp
Lib/IntNameTable.o: Lib/Allocator.hpp Lib/Hash.hpp Lib/Exception.hpp
Lib/IntegerSet.o: Debug/Assertion.hpp Lib/IntegerSet.hpp
Lib/MultiCounter.o: Debug/Tracer.hpp Lib/MultiCounter.hpp Debug/Assertion.hpp
Lib/MultiCounter.o: Lib/XML.hpp Lib/Int.hpp Lib/Comparison.hpp
Lib/MultiCounter.o: Lib/Allocator.hpp Lib/Exception.hpp
Lib/NameArray.o: Lib/NameArray.hpp Debug/Tracer.hpp
Lib/Random.o: Lib/Random.hpp
Lib/System.o: Lib/System.hpp
Lib/Timer.o: Lib/Timer.hpp Debug/Assertion.hpp
Shell/CNF.o: Debug/Tracer.hpp Kernel/Clause.hpp Forwards.hpp
Shell/CNF.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/CNF.o: Debug/Assertion.hpp Lib/Allocator.hpp Kernel/Formula.hpp
Shell/CNF.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/Inference.hpp
Shell/CNF.o: Kernel/Unit.hpp Kernel/FormulaUnit.hpp Shell/CNF.hpp
Shell/CNF.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/CNF.o: Lib/Comparison.hpp
Shell/CommandLine.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
Shell/CommandLine.o: Shell/CommandLine.hpp Shell/Options.hpp
Shell/CommandLine.o: Lib/Allocator.hpp Lib/XML.hpp
Shell/Flattening.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Flattening.o: Lib/Allocator.hpp Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/Flattening.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/Flattening.o: Shell/Flattening.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/Flattening.o: Kernel/Connective.hpp
Shell/FunctionDefinition.o: Debug/Tracer.hpp Lib/Allocator.hpp
Shell/FunctionDefinition.o: Kernel/Clause.hpp Forwards.hpp Kernel/Unit.hpp
Shell/FunctionDefinition.o: Lib/List.hpp Debug/Assertion.hpp
Shell/FunctionDefinition.o: Lib/Allocator.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/FunctionDefinition.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/FunctionDefinition.o: Kernel/Term.hpp Lib/Portability.hpp
Shell/FunctionDefinition.o: Lib/Comparison.hpp Lib/Stack.hpp
Shell/FunctionDefinition.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/FunctionDefinition.o: Lib/Comparison.hpp Kernel/TermVarIterator.hpp
Shell/FunctionDefinition.o: Kernel/TermFunIterator.hpp
Shell/FunctionDefinition.o: Shell/FunctionDefinition.hpp Lib/MultiCounter.hpp
Shell/FunctionDefinition.o: Lib/XML.hpp Kernel/Unit.hpp
Shell/Lexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Int.hpp
Shell/Lexer.o: Lib/Comparison.hpp Shell/Lexer.hpp Lib/Array.hpp
Shell/Lexer.o: Lib/Allocator.hpp Lib/Exception.hpp Shell/Token.hpp
Shell/NNF.o: Lib/Environment.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/NNF.o: Lib/Allocator.hpp Debug/Tracer.hpp Kernel/FormulaUnit.hpp
Shell/NNF.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Shell/NNF.o: Lib/Allocator.hpp Kernel/Term.hpp Lib/Portability.hpp
Shell/NNF.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/NNF.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/NNF.o: Lib/Comparison.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/NNF.o: Shell/NNF.hpp Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Naming.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Shell/Naming.o: Lib/Comparison.hpp Lib/Environment.hpp Kernel/FormulaUnit.hpp
Shell/Naming.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Shell/Naming.o: Lib/Allocator.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Naming.o: Kernel/Signature.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Shell/Naming.o: Lib/List.hpp Lib/Int.hpp Lib/Map.hpp Lib/Hash.hpp
Shell/Naming.o: Lib/Exception.hpp Kernel/Term.hpp Lib/Portability.hpp
Shell/Naming.o: Lib/XML.hpp Lib/Comparison.hpp Shell/Statistics.hpp
Shell/Naming.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Naming.hpp
Shell/Naming.o: Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Normalisation.o: Lib/Sort.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Normalisation.o: Lib/Allocator.hpp Lib/Environment.hpp
Shell/Normalisation.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Shell/Normalisation.o: Kernel/Unit.hpp Lib/List.hpp Kernel/FormulaUnit.hpp
Shell/Normalisation.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/Term.hpp
Shell/Normalisation.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/Normalisation.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp
Shell/Normalisation.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Signature.hpp
Shell/Normalisation.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
Shell/Normalisation.o: Kernel/SubformulaIterator.hpp Kernel/Formula.hpp
Shell/Normalisation.o: Kernel/Connective.hpp Shell/Normalisation.hpp
Shell/Normalisation.o: Shell/SymCounter.hpp
Shell/Options.o: Debug/Tracer.hpp Debug/Assertion.hpp Lib/Int.hpp
Shell/Options.o: Lib/Comparison.hpp Lib/NameArray.hpp Lib/Random.hpp
Shell/Options.o: Lib/Exception.hpp Shell/Options.hpp Lib/Allocator.hpp
Shell/Options.o: Lib/XML.hpp
Shell/Parser.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Int.hpp
Shell/Parser.o: Lib/Comparison.hpp Lib/IntNameTable.hpp Lib/Array.hpp
Shell/Parser.o: Lib/Allocator.hpp Lib/Map.hpp Lib/Allocator.hpp Lib/Hash.hpp
Shell/Parser.o: Lib/Exception.hpp Shell/Lexer.hpp Lib/Array.hpp
Shell/Parser.o: Lib/Exception.hpp Shell/Token.hpp Shell/Parser.hpp
Shell/Parser.o: Lib/XML.hpp Kernel/Unit.hpp
Shell/Preprocess.o: Debug/Tracer.hpp Kernel/Unit.hpp Kernel/Clause.hpp
Shell/Preprocess.o: Forwards.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Shell/Preprocess.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/Preprocess.o: Shell/CNF.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Shell/Preprocess.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Preprocess.o: Shell/Flattening.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/Preprocess.o: Kernel/Connective.hpp Shell/Naming.hpp
Shell/Preprocess.o: Shell/Normalisation.hpp Lib/Comparison.hpp
Shell/Preprocess.o: Shell/SymCounter.hpp Shell/NNF.hpp Shell/Options.hpp
Shell/Preprocess.o: Shell/Preprocess.hpp Shell/Property.hpp Shell/Rectify.hpp
Shell/Preprocess.o: Lib/Array.hpp Shell/Skolem.hpp Kernel/Substitution.hpp
Shell/Preprocess.o: Lib/Random.hpp Lib/Environment.hpp Kernel/Term.hpp
Shell/Preprocess.o: Lib/Portability.hpp Shell/SimplifyFalseTrue.hpp
Shell/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp Lib/Sort.hpp
Shell/Profile.o: Debug/Assertion.hpp Lib/Allocator.hpp Lib/Environment.hpp
Shell/Profile.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Shell/Profile.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Signature.hpp
Shell/Profile.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/Profile.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp Kernel/Term.hpp
Shell/Profile.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/Profile.o: Shell/Profile.hpp Kernel/Unit.hpp Lib/Array.hpp
Shell/Property.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Property.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Shell/Property.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Shell/Property.o: Lib/Allocator.hpp Kernel/FormulaUnit.hpp
Shell/Property.o: Kernel/SubformulaIterator.hpp Kernel/Formula.hpp
Shell/Property.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/Term.hpp
Shell/Property.o: Lib/Portability.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/Property.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/Property.o: Shell/FunctionDefinition.hpp Lib/MultiCounter.hpp
Shell/Property.o: Lib/XML.hpp Kernel/Unit.hpp Shell/Property.hpp
Shell/Rectify.o: Lib/Environment.hpp Kernel/Formula.hpp Lib/List.hpp
Shell/Rectify.o: Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/Rectify.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/Rectify.o: Lib/Allocator.hpp Kernel/Unit.hpp Kernel/Inference.hpp
Shell/Rectify.o: Kernel/Unit.hpp Kernel/Term.hpp Lib/Portability.hpp
Shell/Rectify.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Shell/Rectify.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Rectify.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Rectify.hpp
Shell/Rectify.o: Lib/Array.hpp
Shell/Refutation.o: Debug/Tracer.hpp Lib/Hash.hpp Lib/Set.hpp
Shell/Refutation.o: Lib/Allocator.hpp Lib/Stack.hpp Debug/Assertion.hpp
Shell/Refutation.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/Refutation.o: Lib/Comparison.hpp Kernel/Clause.hpp Forwards.hpp
Shell/Refutation.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/Refutation.o: Kernel/Inference.hpp Kernel/Unit.hpp Shell/Refutation.hpp
Shell/SimplifyFalseTrue.o: Debug/Tracer.hpp Lib/DArray.hpp
Shell/SimplifyFalseTrue.o: Debug/Assertion.hpp Lib/Allocator.hpp
Shell/SimplifyFalseTrue.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/SimplifyFalseTrue.o: Lib/Allocator.hpp Kernel/FormulaUnit.hpp
Shell/SimplifyFalseTrue.o: Kernel/Unit.hpp Lib/List.hpp
Shell/SimplifyFalseTrue.o: Shell/SimplifyFalseTrue.hpp Kernel/Formula.hpp
Shell/SimplifyFalseTrue.o: Lib/XML.hpp Kernel/Connective.hpp
Shell/Skolem.o: Kernel/Signature.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/Skolem.o: Lib/Stack.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/Skolem.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/Skolem.o: Lib/Comparison.hpp Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
Shell/Skolem.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Shell/Skolem.o: Lib/Comparison.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Skolem.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/Skolem.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Rectify.hpp
Shell/Skolem.o: Lib/Array.hpp Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Skolem.o: Shell/Skolem.hpp Kernel/Substitution.hpp Lib/Random.hpp
Shell/Skolem.o: Lib/Environment.hpp Kernel/Term.hpp
Shell/Statistics.o: Shell/Statistics.hpp
Shell/SymCounter.o: Lib/Allocator.hpp Debug/Tracer.hpp Kernel/Term.hpp
Shell/SymCounter.o: Debug/Assertion.hpp Lib/Portability.hpp Lib/XML.hpp
Shell/SymCounter.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Shell/SymCounter.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/SymCounter.o: Lib/Comparison.hpp Kernel/Clause.hpp Forwards.hpp
Shell/SymCounter.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp
Shell/SymCounter.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/SymCounter.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Shell/SymCounter.o: Lib/Exception.hpp Kernel/Unit.hpp Shell/SymCounter.hpp
Shell/TPTP.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Term.hpp
Shell/TPTP.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Portability.hpp
Shell/TPTP.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Shell/TPTP.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/TPTP.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/Allocator.hpp
Shell/TPTP.o: Kernel/Formula.hpp Lib/List.hpp Kernel/Connective.hpp
Shell/TPTP.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Kernel/Clause.hpp
Shell/TPTP.o: Forwards.hpp Shell/TPTP.hpp
Shell/TPTPLexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
Shell/TPTPLexer.o: Shell/TPTPLexer.hpp Shell/Lexer.hpp Lib/Array.hpp
Shell/TPTPLexer.o: Lib/Allocator.hpp Shell/Token.hpp
Shell/TPTPParser.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/TPTPParser.o: Debug/Tracer.hpp Lib/Stack.hpp Lib/BacktrackData.hpp
Shell/TPTPParser.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/TPTPParser.o: Lib/Environment.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/TPTPParser.o: Lib/Allocator.hpp Kernel/Signature.hpp Lib/Map.hpp
Shell/TPTPParser.o: Lib/Hash.hpp Lib/Exception.hpp Kernel/Formula.hpp
Shell/TPTPParser.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/TPTPParser.o: Kernel/Unit.hpp Kernel/Term.hpp Lib/Portability.hpp
Shell/TPTPParser.o: Lib/Comparison.hpp Kernel/Clause.hpp Forwards.hpp
Shell/TPTPParser.o: Shell/Statistics.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/TPTPParser.o: Shell/Options.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
Shell/TPTPParser.o: Lib/Array.hpp Lib/Exception.hpp Shell/Token.hpp
Shell/TPTPParser.o: Shell/TPTPParser.hpp Shell/Parser.hpp
Shell/TPTPParser.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp
Shell/TheoryFinder.o: Debug/Tracer.hpp Kernel/Clause.hpp Forwards.hpp
Shell/TheoryFinder.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/TheoryFinder.o: Debug/Assertion.hpp Lib/Allocator.hpp
Shell/TheoryFinder.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/TheoryFinder.o: Kernel/FormulaUnit.hpp Kernel/Term.hpp
Shell/TheoryFinder.o: Lib/Portability.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/TheoryFinder.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Shell/TheoryFinder.o: Lib/Comparison.hpp Shell/Property.hpp Kernel/Unit.hpp
Shell/TheoryFinder.o: Shell/TheoryFinder.hpp
Shell/Token.o: Debug/Assertion.hpp Shell/Token.hpp
Kernel/Clause.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Kernel/Clause.o: Lib/Comparison.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Clause.o: Kernel/Clause.hpp Forwards.hpp Kernel/Unit.hpp Lib/List.hpp
Kernel/Clause.o: Debug/Assertion.hpp Lib/Allocator.hpp Kernel/Term.hpp
Kernel/Clause.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Clause.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/ClauseQueue.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Random.hpp
Kernel/ClauseQueue.o: Lib/Environment.hpp Kernel/Clause.hpp Forwards.hpp
Kernel/ClauseQueue.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Kernel/ClauseQueue.o: Lib/Allocator.hpp Kernel/ClauseQueue.hpp
Kernel/DoubleSubstitution.o: Lib/Int.hpp Lib/Comparison.hpp Lib/DArray.hpp
Kernel/DoubleSubstitution.o: Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/DoubleSubstitution.o: Debug/Tracer.hpp Kernel/Term.hpp
Kernel/DoubleSubstitution.o: Lib/Portability.hpp Lib/XML.hpp
Kernel/DoubleSubstitution.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/DoubleSubstitution.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/DoubleSubstitution.o: Kernel/DoubleSubstitution.hpp Forwards.hpp
Kernel/DoubleSubstitution.o: Lib/DHMap.hpp Lib/Exception.hpp Lib/Hash.hpp
Kernel/Formula.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/MultiCounter.hpp
Kernel/Formula.o: Debug/Assertion.hpp Lib/XML.hpp Kernel/Term.hpp
Kernel/Formula.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Formula.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/Formula.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Formula.o: Kernel/Formula.hpp Lib/List.hpp Kernel/Connective.hpp
Kernel/Formula.o: Kernel/SubformulaIterator.hpp Kernel/FormulaVarIterator.hpp
Kernel/FormulaUnit.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Inference.hpp
Kernel/FormulaUnit.o: Kernel/Unit.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/FormulaUnit.o: Kernel/Formula.hpp Lib/List.hpp Debug/Assertion.hpp
Kernel/FormulaUnit.o: Lib/Allocator.hpp Lib/XML.hpp Kernel/Connective.hpp
Kernel/FormulaUnit.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Kernel/FormulaVarIterator.o: Debug/Tracer.hpp Kernel/FormulaVarIterator.hpp
Kernel/FormulaVarIterator.o: Lib/MultiCounter.hpp Debug/Assertion.hpp
Kernel/FormulaVarIterator.o: Lib/XML.hpp Kernel/Formula.hpp Lib/List.hpp
Kernel/FormulaVarIterator.o: Lib/Allocator.hpp Lib/XML.hpp
Kernel/FormulaVarIterator.o: Kernel/Connective.hpp Kernel/Term.hpp
Kernel/FormulaVarIterator.o: Lib/Portability.hpp Lib/Comparison.hpp
Kernel/FormulaVarIterator.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp
Kernel/FormulaVarIterator.o: Lib/Int.hpp Lib/Comparison.hpp
Kernel/Inference.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Inference.o: Lib/Allocator.hpp
Kernel/KBO.o: Debug/Tracer.hpp Kernel/Term.hpp Debug/Assertion.hpp
Kernel/KBO.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/KBO.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/KBO.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp Kernel/KBO.hpp
Kernel/KBO.o: Kernel/Ordering.hpp Kernel/Signature.hpp Lib/Allocator.hpp
Kernel/KBO.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
Kernel/LiteralSelector.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Kernel/LiteralSelector.o: Debug/Tracer.hpp Kernel/Unit.hpp Lib/List.hpp
Kernel/LiteralSelector.o: Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/LiteralSelector.o: Kernel/LiteralSelector.hpp
Kernel/MMSubstitution.o: Lib/Hash.hpp Lib/DArray.hpp Debug/Assertion.hpp
Kernel/MMSubstitution.o: Lib/Allocator.hpp Debug/Tracer.hpp
Kernel/MMSubstitution.o: Lib/Environment.hpp Lib/Random.hpp
Kernel/MMSubstitution.o: Lib/DHMultiset.hpp Lib/Exception.hpp Lib/Hash.hpp
Kernel/MMSubstitution.o: Lib/DHMap.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Kernel/MMSubstitution.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/MMSubstitution.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/MMSubstitution.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/MMSubstitution.o: Lib/Comparison.hpp Kernel/Term.hpp
Kernel/MMSubstitution.o: Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Kernel/MMSubstitution.o: Lib/BacktrackData.hpp Test/Output.hpp Lib/Int.hpp
Kernel/Signature.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Signature.hpp
Kernel/Signature.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Stack.hpp
Kernel/Signature.o: Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/Signature.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/Signature.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
Kernel/SubformulaIterator.o: Debug/Tracer.hpp Kernel/SubformulaIterator.hpp
Kernel/SubformulaIterator.o: Kernel/Formula.hpp Lib/List.hpp
Kernel/SubformulaIterator.o: Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/SubformulaIterator.o: Lib/XML.hpp Kernel/Connective.hpp
Kernel/Substitution.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Term.hpp
Kernel/Substitution.o: Debug/Assertion.hpp Debug/Tracer.hpp
Kernel/Substitution.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Substitution.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Kernel/Substitution.o: Lib/List.hpp Lib/Int.hpp Kernel/Substitution.hpp
Kernel/Substitution.o: Lib/Random.hpp Lib/Allocator.hpp Lib/Environment.hpp
Kernel/Term.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Environment.hpp
Kernel/Term.o: Lib/Stack.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/Term.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/Term.o: Lib/Comparison.hpp Lib/Int.hpp Kernel/Signature.hpp
Kernel/Term.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
Kernel/Term.o: Kernel/Substitution.hpp Lib/Random.hpp Kernel/Term.hpp
Kernel/Term.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/Term.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
Kernel/TermFunIterator.o: Debug/Tracer.hpp Kernel/Term.hpp
Kernel/TermFunIterator.o: Debug/Assertion.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/TermFunIterator.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermFunIterator.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/TermFunIterator.o: Lib/Comparison.hpp Kernel/TermFunIterator.hpp
Kernel/TermVarIterator.o: Debug/Tracer.hpp Kernel/Term.hpp
Kernel/TermVarIterator.o: Debug/Assertion.hpp Lib/Portability.hpp Lib/XML.hpp
Kernel/TermVarIterator.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermVarIterator.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Kernel/TermVarIterator.o: Lib/Comparison.hpp Kernel/TermVarIterator.hpp
Kernel/Unit.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Unit.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/Allocator.hpp
Kernel/Unit.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Kernel/Unit.o: Lib/Allocator.hpp
Indexing/Index.o: Indexing/Index.hpp Forwards.hpp Kernel/MMSubstitution.hpp
Indexing/Index.o: Lib/DHMap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Indexing/Index.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/Hash.hpp
Indexing/Index.o: Lib/BacktrackData.hpp Kernel/Term.hpp Lib/Portability.hpp
Indexing/Index.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Indexing/Index.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Indexing/Index.o: Lib/Comparison.hpp Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/Index.o: Lib/Exception.hpp Lib/VirtualIterator.hpp
Indexing/Index.o: Saturation/ClauseContainer.hpp Kernel/Clause.hpp
Indexing/Index.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Indexing/IndexManager.o: Lib/Exception.hpp Lib/Environment.hpp
Indexing/IndexManager.o: Kernel/Signature.hpp Lib/Allocator.hpp
Indexing/IndexManager.o: Debug/Tracer.hpp Lib/Stack.hpp Debug/Assertion.hpp
Indexing/IndexManager.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Indexing/IndexManager.o: Lib/Int.hpp Lib/Comparison.hpp Lib/Map.hpp
Indexing/IndexManager.o: Lib/Hash.hpp Lib/Exception.hpp
Indexing/IndexManager.o: Saturation/SaturationAlgorithm.hpp Forwards.hpp
Indexing/IndexManager.o: Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/IndexManager.o: Indexing/IndexManager.hpp Lib/DHMap.hpp
Indexing/IndexManager.o: Indexing/Index.hpp Kernel/MMSubstitution.hpp
Indexing/IndexManager.o: Lib/BacktrackData.hpp Kernel/Term.hpp
Indexing/IndexManager.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Indexing/IndexManager.o: Lib/VirtualIterator.hpp
Indexing/IndexManager.o: Saturation/ClauseContainer.hpp
Indexing/IndexManager.o: Inferences/InferenceEngine.hpp Saturation/Limits.hpp
Indexing/IndexManager.o: Saturation/SaturationResult.hpp Shell/Statistics.hpp
Indexing/IndexManager.o: Test/Output.hpp Indexing/SubstitutionTree.hpp
Indexing/IndexManager.o: Lib/Int.hpp Lib/List.hpp Lib/SkipList.hpp
Indexing/IndexManager.o: Lib/Random.hpp Lib/BinaryHeap.hpp
Indexing/IndexManager.o: Kernel/DoubleSubstitution.hpp
Indexing/IndexManager.o: Indexing/IndexManager.hpp
Indexing/SubstitutionTree.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree.o: Debug/Tracer.hpp Kernel/Unit.hpp Lib/List.hpp
Indexing/SubstitutionTree.o: Debug/Assertion.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Indexing/SubstitutionTree.o: Lib/Comparison.hpp Lib/Stack.hpp
Indexing/SubstitutionTree.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Indexing/SubstitutionTree.o: Lib/Comparison.hpp Lib/BinaryHeap.hpp
Indexing/SubstitutionTree.o: Lib/Exception.hpp Kernel/Signature.hpp
Indexing/SubstitutionTree.o: Lib/Map.hpp Lib/Hash.hpp Lib/Environment.hpp
Indexing/SubstitutionTree.o: Lib/Int.hpp Test/Output.hpp
Indexing/SubstitutionTree.o: Indexing/SubstitutionTree.hpp
Indexing/SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/SkipList.hpp
Indexing/SubstitutionTree.o: Lib/Random.hpp Lib/BacktrackData.hpp
Indexing/SubstitutionTree.o: Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree.o: Kernel/Term.hpp Kernel/MMSubstitution.hpp
Indexing/SubstitutionTree.o: Indexing/Index.hpp Lib/Event.hpp
Indexing/SubstitutionTree.o: Lib/SmartPtr.hpp Lib/Exception.hpp
Indexing/SubstitutionTree.o: Saturation/ClauseContainer.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/VirtualIterator.hpp
Indexing/SubstitutionTree_Nodes.o: Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/List.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/SkipList.hpp Lib/Comparison.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Random.hpp Lib/BacktrackData.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/List.hpp Lib/Int.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/DHMultiset.hpp Lib/Exception.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Hash.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree_Nodes.o: Indexing/Index.hpp Forwards.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/MMSubstitution.hpp Lib/DHMap.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BacktrackData.hpp Kernel/Term.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Portability.hpp Lib/XML.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Comparison.hpp Lib/Stack.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Event.hpp Lib/SmartPtr.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/Exception.hpp
Indexing/SubstitutionTree_Nodes.o: Saturation/ClauseContainer.hpp
Indexing/SubstitutionTree_Nodes.o: Indexing/SubstitutionTree.hpp Lib/Int.hpp
Indexing/SubstitutionTree_Nodes.o: Lib/BinaryHeap.hpp
Indexing/SubstitutionTree_Nodes.o: Kernel/DoubleSubstitution.hpp
Indexing/SubstitutionTree_Nodes.o: Test/Output.hpp
Indexing/TermSharing.o: Kernel/Term.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/TermSharing.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Indexing/TermSharing.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Indexing/TermSharing.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp
Indexing/TermSharing.o: Indexing/TermSharing.hpp Lib/Set.hpp
Resolution/Active.o: Lib/Environment.hpp Kernel/Term.hpp Debug/Assertion.hpp
Resolution/Active.o: Debug/Tracer.hpp Lib/Portability.hpp Lib/XML.hpp
Resolution/Active.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Resolution/Active.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Resolution/Active.o: Lib/Comparison.hpp Kernel/Clause.hpp Forwards.hpp
Resolution/Active.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/Active.o: Shell/Statistics.hpp Resolution/Active.hpp
Resolution/Active.o: Kernel/ClauseQueue.hpp
Resolution/BinaryResolution.o: Lib/DArray.hpp Debug/Assertion.hpp
Resolution/BinaryResolution.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Resolution/BinaryResolution.o: Lib/Comparison.hpp
Resolution/BinaryResolution.o: Kernel/DoubleSubstitution.hpp Forwards.hpp
Resolution/BinaryResolution.o: Lib/DHMap.hpp Lib/Exception.hpp Lib/Hash.hpp
Resolution/BinaryResolution.o: Kernel/Term.hpp Lib/Portability.hpp
Resolution/BinaryResolution.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Resolution/BinaryResolution.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Resolution/BinaryResolution.o: Kernel/Term.hpp Kernel/Clause.hpp
Resolution/BinaryResolution.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/BinaryResolution.o: Kernel/Inference.hpp Kernel/Unit.hpp
Resolution/BinaryResolution.o: Resolution/BinaryResolution.hpp
Resolution/BinaryResolution.o: Resolution/ProofAttempt.hpp
Resolution/BinaryResolution.o: Resolution/Active.hpp Kernel/ClauseQueue.hpp
Resolution/BinaryResolution.o: Resolution/Passive.hpp
Resolution/BinaryResolution.o: Resolution/Unprocessed.hpp
Resolution/Passive.o: Lib/Environment.hpp Kernel/Term.hpp Debug/Assertion.hpp
Resolution/Passive.o: Debug/Tracer.hpp Lib/Portability.hpp Lib/XML.hpp
Resolution/Passive.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Resolution/Passive.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Resolution/Passive.o: Lib/Comparison.hpp Kernel/Clause.hpp Forwards.hpp
Resolution/Passive.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/Passive.o: Shell/Statistics.hpp Resolution/Passive.hpp
Resolution/Passive.o: Kernel/ClauseQueue.hpp
Resolution/ProofAttempt.o: Lib/Environment.hpp Lib/DArray.hpp
Resolution/ProofAttempt.o: Debug/Assertion.hpp Lib/Allocator.hpp
Resolution/ProofAttempt.o: Debug/Tracer.hpp Lib/Random.hpp Kernel/Clause.hpp
Resolution/ProofAttempt.o: Forwards.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Resolution/ProofAttempt.o: Lib/List.hpp Kernel/Term.hpp Lib/Portability.hpp
Resolution/ProofAttempt.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Resolution/ProofAttempt.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Resolution/ProofAttempt.o: Lib/Comparison.hpp Kernel/Inference.hpp
Resolution/ProofAttempt.o: Kernel/Unit.hpp Shell/Statistics.hpp
Resolution/ProofAttempt.o: Shell/Options.hpp Resolution/Tautology.hpp
Resolution/ProofAttempt.o: Resolution/BinaryResolution.hpp
Resolution/ProofAttempt.o: Resolution/ProofAttempt.hpp Resolution/Active.hpp
Resolution/ProofAttempt.o: Kernel/ClauseQueue.hpp Resolution/Passive.hpp
Resolution/ProofAttempt.o: Resolution/Unprocessed.hpp
Resolution/Tautology.o: Lib/DArray.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Resolution/Tautology.o: Debug/Tracer.hpp Lib/Random.hpp Lib/Environment.hpp
Resolution/Tautology.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Resolution/Tautology.o: Lib/Comparison.hpp Lib/Stack.hpp
Resolution/Tautology.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Resolution/Tautology.o: Lib/Comparison.hpp Kernel/Clause.hpp Forwards.hpp
Resolution/Tautology.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/Tautology.o: Shell/Statistics.hpp Resolution/Tautology.hpp
Resolution/Unprocessed.o: Lib/Environment.hpp Kernel/Term.hpp
Resolution/Unprocessed.o: Debug/Assertion.hpp Debug/Tracer.hpp
Resolution/Unprocessed.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Resolution/Unprocessed.o: Lib/Stack.hpp Lib/Allocator.hpp
Resolution/Unprocessed.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Resolution/Unprocessed.o: Lib/Comparison.hpp Kernel/Clause.hpp Forwards.hpp
Resolution/Unprocessed.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/Unprocessed.o: Shell/Statistics.hpp Resolution/Unprocessed.hpp
Resolution/Unprocessed.o: Kernel/ClauseQueue.hpp
Rule/CASC.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp Lib/Sort.hpp
Rule/CASC.o: Debug/Assertion.hpp Lib/Allocator.hpp Lib/Environment.hpp
Rule/CASC.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Rule/CASC.o: Lib/List.hpp Kernel/Signature.hpp Lib/Stack.hpp
Rule/CASC.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp Lib/Map.hpp
Rule/CASC.o: Lib/Hash.hpp Lib/Exception.hpp Kernel/Term.hpp
Rule/CASC.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp Rule/Rule.hpp
Rule/CASC.o: Rule/CASC.hpp Kernel/Unit.hpp Lib/Array.hpp
Rule/Index.o: Lib/Stack.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Rule/Index.o: Lib/Allocator.hpp Lib/BacktrackData.hpp Lib/List.hpp
Rule/Index.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Clause.hpp Forwards.hpp
Rule/Index.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Rule/Index.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
Rule/Index.o: Kernel/Term.hpp Lib/Portability.hpp Lib/XML.hpp
Rule/Index.o: Lib/Comparison.hpp Indexing/Index.hpp Kernel/MMSubstitution.hpp
Rule/Index.o: Lib/DHMap.hpp Lib/BacktrackData.hpp Kernel/Term.hpp
Rule/Index.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
Rule/Index.o: Lib/VirtualIterator.hpp Saturation/ClauseContainer.hpp
Rule/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp Lib/Sort.hpp
Rule/Profile.o: Debug/Assertion.hpp Lib/Allocator.hpp Lib/Environment.hpp
Rule/Profile.o: Kernel/Clause.hpp Forwards.hpp Lib/Allocator.hpp
Rule/Profile.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Signature.hpp
Rule/Profile.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
Rule/Profile.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp Kernel/Term.hpp
Rule/Profile.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Rule/Profile.o: Shell/Profile.hpp Kernel/Unit.hpp Lib/Array.hpp
Rule/Prolog.o: Kernel/Term.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Rule/Prolog.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Rule/Prolog.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Rule/Prolog.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp Kernel/Clause.hpp
Rule/Prolog.o: Forwards.hpp Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Rule/Prolog.o: Rule/Prolog.hpp Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
Rule/Prolog.o: Rule/Index.hpp Kernel/Unit.hpp Rule/Rule.hpp
Rule/ProofAttempt.o: Debug/Tracer.hpp Lib/Environment.hpp
Rule/ProofAttempt.o: Shell/Statistics.hpp Resolution/ProofAttempt.hpp
Rule/ProofAttempt.o: Resolution/Active.hpp Kernel/ClauseQueue.hpp
Rule/ProofAttempt.o: Debug/Assertion.hpp Resolution/Passive.hpp
Rule/ProofAttempt.o: Resolution/Unprocessed.hpp
SAT/Assignment.o: Debug/Tracer.hpp SAT/Assignment.hpp Debug/Assertion.hpp
SAT/Assignment.o: SAT/SAT.hpp
Test/Output.o: Debug/Assertion.hpp Kernel/Term.hpp Debug/Tracer.hpp
Test/Output.o: Lib/Portability.hpp Lib/XML.hpp Lib/Comparison.hpp
Test/Output.o: Lib/Stack.hpp Lib/Allocator.hpp Lib/BacktrackData.hpp
Test/Output.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp Kernel/Clause.hpp
Test/Output.o: Forwards.hpp Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Test/Output.o: Lib/Int.hpp Test/Output.hpp Lib/Environment.hpp
Test/Output.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Test/Output.o: Lib/Exception.hpp
Global.o: Debug/Assertion.hpp Lib/Enumerator.hpp Kernel/Formula.hpp
Global.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Global.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/Unit.hpp
Global.o: Lib/Environment.hpp
alucard.o: Forwards.hpp Debug/Tracer.hpp Lib/Random.hpp Lib/Set.hpp
alucard.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
alucard.o: Lib/Timer.hpp Debug/Assertion.hpp Lib/Exception.hpp
alucard.o: Lib/Environment.hpp Lib/Vector.hpp Lib/VirtualIterator.hpp
alucard.o: Kernel/Signature.hpp Lib/Allocator.hpp Lib/Stack.hpp
alucard.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp Lib/Map.hpp
alucard.o: Lib/Hash.hpp Lib/Exception.hpp Kernel/Clause.hpp Forwards.hpp
alucard.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp Lib/XML.hpp
alucard.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
alucard.o: Kernel/LiteralSelector.hpp Indexing/TermSharing.hpp Lib/Set.hpp
alucard.o: Kernel/Term.hpp Lib/Portability.hpp Lib/Comparison.hpp
alucard.o: Shell/Options.hpp Shell/CommandLine.hpp Shell/TPTPLexer.hpp
alucard.o: Shell/Lexer.hpp Lib/Array.hpp Lib/Exception.hpp Shell/Token.hpp
alucard.o: Shell/TPTP.hpp Shell/TPTPParser.hpp Kernel/Unit.hpp
alucard.o: Shell/Parser.hpp Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp
alucard.o: Shell/Property.hpp Shell/Preprocess.hpp Shell/Statistics.hpp
alucard.o: Shell/Refutation.hpp Shell/TheoryFinder.hpp
alucard.o: Saturation/SaturationAlgorithm.hpp Lib/Event.hpp Lib/SmartPtr.hpp
alucard.o: Indexing/IndexManager.hpp Lib/DHMap.hpp Indexing/Index.hpp
alucard.o: Kernel/MMSubstitution.hpp Lib/BacktrackData.hpp Kernel/Term.hpp
alucard.o: Lib/VirtualIterator.hpp Saturation/ClauseContainer.hpp
alucard.o: Inferences/InferenceEngine.hpp Saturation/Limits.hpp
alucard.o: Saturation/SaturationResult.hpp Shell/Statistics.hpp
alucard.o: Lib/Environment.hpp Test/Output.hpp
alucard.o: Saturation/AWPassiveClauseContainer.hpp Kernel/ClauseQueue.hpp
alucard.o: Saturation/ClauseContainer.hpp Inferences/InferenceEngine.hpp
alucard.o: Inferences/BinaryResolution.hpp Inferences/InferenceEngine.hpp
sat.o: Lib/Random.hpp
test_BinaryHeap.o: Lib/BinaryHeap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
test_BinaryHeap.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/Comparison.hpp
test_BinaryHeap.o: Lib/Int.hpp
test_DHMap.o: Lib/DHMap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
test_DHMap.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/Hash.hpp
test_DHMultiset.o: Lib/DHMultiset.hpp Debug/Assertion.hpp Lib/Allocator.hpp
test_DHMultiset.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/Hash.hpp
test_DHMultiset.o: Lib/DHMap.hpp
test_SkipList.o: Lib/SkipList.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_SkipList.o: Lib/Allocator.hpp Lib/Comparison.hpp Lib/Random.hpp
test_SkipList.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
test_SkipList.o: Lib/BinaryHeap.hpp Lib/Exception.hpp Lib/DHMultiset.hpp
test_SkipList.o: Lib/Hash.hpp Lib/DHMap.hpp Lib/Int.hpp Lib/Timer.hpp
test_SkipList.o: Lib/Random.hpp
test_SubstitutionTree.o: Debug/Tracer.hpp Lib/Array.hpp Debug/Assertion.hpp
test_SubstitutionTree.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Random.hpp
test_SubstitutionTree.o: Lib/Set.hpp Lib/Allocator.hpp Lib/Int.hpp
test_SubstitutionTree.o: Lib/Comparison.hpp Lib/Timer.hpp Lib/Exception.hpp
test_SubstitutionTree.o: Lib/Environment.hpp Lib/Vector.hpp
test_SubstitutionTree.o: Kernel/Signature.hpp Lib/Stack.hpp
test_SubstitutionTree.o: Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
test_SubstitutionTree.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
test_SubstitutionTree.o: Kernel/Clause.hpp Forwards.hpp Kernel/Unit.hpp
test_SubstitutionTree.o: Lib/List.hpp Kernel/Formula.hpp Lib/XML.hpp
test_SubstitutionTree.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
test_SubstitutionTree.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
test_SubstitutionTree.o: Lib/Portability.hpp Lib/Comparison.hpp
test_SubstitutionTree.o: Indexing/SubstitutionTree.hpp
test_SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/Int.hpp Lib/SkipList.hpp
test_SubstitutionTree.o: Lib/Random.hpp Lib/BinaryHeap.hpp
test_SubstitutionTree.o: Lib/BacktrackData.hpp Kernel/DoubleSubstitution.hpp
test_SubstitutionTree.o: Lib/DHMap.hpp Kernel/Term.hpp
test_SubstitutionTree.o: Kernel/MMSubstitution.hpp Indexing/Index.hpp
test_SubstitutionTree.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
test_SubstitutionTree.o: Saturation/ClauseContainer.hpp Test/Output.hpp
test_SubstitutionTree.o: Shell/Options.hpp Shell/CommandLine.hpp
test_SubstitutionTree.o: Shell/TPTPLexer.hpp Shell/Lexer.hpp Lib/Array.hpp
test_SubstitutionTree.o: Shell/Token.hpp Shell/TPTP.hpp Shell/TPTPParser.hpp
test_SubstitutionTree.o: Kernel/Unit.hpp Shell/Parser.hpp
test_SubstitutionTree.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp
test_SubstitutionTree.o: Shell/Property.hpp Shell/Preprocess.hpp
test_SubstitutionTree.o: Shell/Statistics.hpp Shell/Refutation.hpp
test_SubstitutionTree.o: Shell/TheoryFinder.hpp Resolution/ProofAttempt.hpp
test_SubstitutionTree.o: Resolution/Active.hpp Kernel/ClauseQueue.hpp
test_SubstitutionTree.o: Resolution/Passive.hpp Resolution/Unprocessed.hpp
test_SubstitutionTree.o: Rule/CASC.hpp Rule/Prolog.hpp Rule/Index.hpp
test_SubstitutionTree.o: Rule/Rule.hpp Rule/Index.hpp Rule/ProofAttempt.hpp
test_SubstitutionTree.o: Test/Output.hpp
test_retrieval.o: Debug/Tracer.hpp Lib/Array.hpp Debug/Assertion.hpp
test_retrieval.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Random.hpp
test_retrieval.o: Lib/Set.hpp Lib/Allocator.hpp Lib/Int.hpp
test_retrieval.o: Lib/Comparison.hpp Lib/Timer.hpp Lib/Exception.hpp
test_retrieval.o: Lib/Environment.hpp Lib/Vector.hpp Kernel/Signature.hpp
test_retrieval.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp
test_retrieval.o: Lib/Int.hpp Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
test_retrieval.o: Kernel/Clause.hpp Forwards.hpp Kernel/Unit.hpp Lib/List.hpp
test_retrieval.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
test_retrieval.o: Kernel/FormulaUnit.hpp Indexing/TermSharing.hpp Lib/Set.hpp
test_retrieval.o: Kernel/Term.hpp Lib/Portability.hpp Lib/Comparison.hpp
test_retrieval.o: Indexing/SubstitutionTree.hpp Lib/VirtualIterator.hpp
test_retrieval.o: Lib/Int.hpp Lib/SkipList.hpp Lib/Random.hpp
test_retrieval.o: Lib/BinaryHeap.hpp Lib/BacktrackData.hpp
test_retrieval.o: Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp Kernel/Term.hpp
test_retrieval.o: Kernel/MMSubstitution.hpp Indexing/Index.hpp Lib/Event.hpp
test_retrieval.o: Lib/SmartPtr.hpp Lib/Exception.hpp
test_retrieval.o: Saturation/ClauseContainer.hpp Test/Output.hpp
test_retrieval.o: Shell/Options.hpp Shell/CommandLine.hpp Shell/TPTPLexer.hpp
test_retrieval.o: Shell/Lexer.hpp Lib/Array.hpp Shell/Token.hpp
test_retrieval.o: Shell/TPTP.hpp Shell/TPTPParser.hpp Kernel/Unit.hpp
test_retrieval.o: Shell/Parser.hpp Lib/IntNameTable.hpp Lib/Array.hpp
test_retrieval.o: Lib/Map.hpp Shell/Property.hpp Shell/Preprocess.hpp
test_retrieval.o: Shell/Statistics.hpp Shell/Refutation.hpp
test_retrieval.o: Shell/TheoryFinder.hpp Resolution/ProofAttempt.hpp
test_retrieval.o: Resolution/Active.hpp Kernel/ClauseQueue.hpp
test_retrieval.o: Resolution/Passive.hpp Resolution/Unprocessed.hpp
test_retrieval.o: Rule/CASC.hpp Rule/Prolog.hpp Rule/Index.hpp Rule/Rule.hpp
test_retrieval.o: Rule/Index.hpp Rule/ProofAttempt.hpp Test/Output.hpp
vampire.o: Debug/Tracer.hpp Lib/Random.hpp Lib/Set.hpp Lib/Allocator.hpp
vampire.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp Lib/Timer.hpp
vampire.o: Debug/Assertion.hpp Lib/Exception.hpp Lib/Environment.hpp
vampire.o: Lib/Vector.hpp Kernel/Signature.hpp Lib/Allocator.hpp
vampire.o: Lib/Stack.hpp Lib/BacktrackData.hpp Lib/List.hpp Lib/Int.hpp
vampire.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp Kernel/Clause.hpp
vampire.o: Forwards.hpp Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp
vampire.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
vampire.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
vampire.o: Lib/Portability.hpp Lib/Comparison.hpp
vampire.o: Indexing/SubstitutionTree.hpp Lib/VirtualIterator.hpp Lib/Int.hpp
vampire.o: Lib/SkipList.hpp Lib/Random.hpp Lib/BinaryHeap.hpp
vampire.o: Lib/BacktrackData.hpp Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp
vampire.o: Kernel/Term.hpp Kernel/MMSubstitution.hpp Indexing/Index.hpp
vampire.o: Lib/Event.hpp Lib/SmartPtr.hpp Lib/Exception.hpp
vampire.o: Saturation/ClauseContainer.hpp Test/Output.hpp Shell/Options.hpp
vampire.o: Shell/CommandLine.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
vampire.o: Lib/Array.hpp Shell/Token.hpp Shell/TPTP.hpp Shell/TPTPParser.hpp
vampire.o: Kernel/Unit.hpp Shell/Parser.hpp Lib/IntNameTable.hpp
vampire.o: Lib/Array.hpp Lib/Map.hpp Shell/Property.hpp Shell/Preprocess.hpp
vampire.o: Shell/Statistics.hpp Shell/Refutation.hpp Shell/TheoryFinder.hpp
vampire.o: Rule/CASC.hpp Rule/Prolog.hpp Rule/Index.hpp Rule/Rule.hpp
vampire.o: Rule/Index.hpp Rule/ProofAttempt.hpp
