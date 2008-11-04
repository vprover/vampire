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
#XFLAGS = -pg -g -DVDEBUG=0 # profiling
#XFLAGS = -g -DVDEBUG=1 -DCHECK_LEAKS=0 # standard debugging only
XFLAGS = -O6 -DVDEBUG=0 # no debugging
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
        Lib/Hash.o\
        Lib/Int.o\
        Lib/IntNameTable.o\
        Lib/MemoryLeak.o\
        Lib/MultiCounter.o\
        Lib/NameArray.o\
        Lib/Random.o\
        Lib/System.o\
        Lib/Environment.o\
        Lib/Exception.o

VK_OBJ= Kernel/Clause.o\
        Kernel/ClauseQueue.o\
        Kernel/DoubleSubstitution.o\
        Kernel/Formula.o\
        Kernel/FormulaUnit.o\
        Kernel/FormulaVarIterator.o\
        Kernel/Inference.o\
        Kernel/Signature.o\
        Kernel/SubformulaIterator.o\
        Kernel/Substitution.o\
        Kernel/Term.o\
        Kernel/TermFunIterator.o\
        Kernel/TermVarIterator.o\
        Kernel/Unit.o

VI_OBJ = Indexing/TermSharing.o\
         Indexing/SubstitutionTree.o

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
           Resolution/LiteralSelection.o\
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

VAMPIRE_OBJ = $(VAMP_BASIC) Global.o vampire.o
SAT_OBJ = $(VD_OBJ) $(SAT) sat.o
TEST_OBJ = $(VD_OBJ) $(VL_OBJ) $(VK_OBJ) $(VI_OBJ) $(VS_OBJ) $(VT_OBJ) Global.o test_SubstitutionTree.o
DHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_DHMap.o
BHTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_BinaryHeap.o
SLTEST_OBJ = $(VD_OBJ) $(VL_OBJ) Global.o test_SkipList.o
ALUCARD_OBJ = $(VAMP_BASIC) Global.o alucard.o

################################################################

all: test

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



dhtest: $(DHTEST_OBJ)
	$(CXX) $(CXXFLAGS) $(DHTEST_OBJ) -o test_DHMap

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
	cd Shell ; rm -f *.o *~ *.bak ; cd ..
	cd Resolution ; rm -f *.o *~ *.bak ; cd ..
	cd Rule ; rm -f *.o *~ *.bak ; cd ..
	cd SAT ; rm -f *.o *~ *.bak ; cd ..
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
Shell/CNF.o: Debug/Tracer.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Shell/CNF.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Shell/CNF.o: Lib/Allocator.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/CNF.o: Kernel/Connective.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/CNF.o: Kernel/FormulaUnit.hpp Shell/CNF.hpp Lib/Stack.hpp
Shell/CommandLine.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
Shell/CommandLine.o: Shell/CommandLine.hpp Shell/Options.hpp
Shell/CommandLine.o: Lib/Allocator.hpp Lib/XML.hpp
Shell/Flattening.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Flattening.o: Lib/Allocator.hpp Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/Flattening.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/Flattening.o: Shell/Flattening.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/Flattening.o: Kernel/Connective.hpp
Shell/FunctionDefinition.o: Debug/Tracer.hpp Lib/Allocator.hpp
Shell/FunctionDefinition.o: Kernel/Clause.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/FunctionDefinition.o: Debug/Assertion.hpp Lib/Allocator.hpp
Shell/FunctionDefinition.o: Kernel/Formula.hpp Lib/XML.hpp
Shell/FunctionDefinition.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/FunctionDefinition.o: Kernel/Term.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/FunctionDefinition.o: Kernel/TermVarIterator.hpp
Shell/FunctionDefinition.o: Kernel/TermFunIterator.hpp
Shell/FunctionDefinition.o: Shell/FunctionDefinition.hpp Lib/MultiCounter.hpp
Shell/FunctionDefinition.o: Lib/XML.hpp Kernel/Unit.hpp
Shell/Lexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Int.hpp
Shell/Lexer.o: Lib/Comparison.hpp Shell/Lexer.hpp Lib/Array.hpp
Shell/Lexer.o: Lib/Allocator.hpp Lib/Exception.hpp Shell/Token.hpp
Shell/NNF.o: Lib/Environment.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/NNF.o: Lib/Allocator.hpp Debug/Tracer.hpp Kernel/FormulaUnit.hpp
Shell/NNF.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Shell/NNF.o: Lib/Allocator.hpp Kernel/Term.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/NNF.o: Lib/Stack.hpp Indexing/TermSharing.hpp Lib/Set.hpp Shell/NNF.hpp
Shell/NNF.o: Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Naming.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Shell/Naming.o: Lib/Comparison.hpp Lib/Environment.hpp Kernel/FormulaUnit.hpp
Shell/Naming.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Shell/Naming.o: Lib/Allocator.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Naming.o: Kernel/Signature.hpp Lib/Stack.hpp Lib/Map.hpp Lib/Hash.hpp
Shell/Naming.o: Lib/Exception.hpp Kernel/Term.hpp Lib/XML.hpp
Shell/Naming.o: Lib/Comparison.hpp Shell/Statistics.hpp
Shell/Naming.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Naming.hpp
Shell/Naming.o: Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Normalisation.o: Lib/Sort.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Shell/Normalisation.o: Lib/Allocator.hpp Lib/Environment.hpp
Shell/Normalisation.o: Kernel/Clause.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Shell/Normalisation.o: Lib/List.hpp Kernel/FormulaUnit.hpp
Shell/Normalisation.o: Kernel/Inference.hpp Kernel/Unit.hpp Kernel/Term.hpp
Shell/Normalisation.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/Normalisation.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Shell/Normalisation.o: Lib/Exception.hpp Kernel/SubformulaIterator.hpp
Shell/Normalisation.o: Kernel/Formula.hpp Kernel/Connective.hpp
Shell/Normalisation.o: Shell/Normalisation.hpp Shell/SymCounter.hpp
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
Shell/Preprocess.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Shell/Preprocess.o: Debug/Assertion.hpp Lib/Allocator.hpp Shell/CNF.hpp
Shell/Preprocess.o: Lib/Stack.hpp Shell/Flattening.hpp Kernel/Formula.hpp
Shell/Preprocess.o: Lib/XML.hpp Kernel/Connective.hpp Shell/Naming.hpp
Shell/Preprocess.o: Shell/Normalisation.hpp Lib/Comparison.hpp
Shell/Preprocess.o: Shell/SymCounter.hpp Shell/NNF.hpp Shell/Options.hpp
Shell/Preprocess.o: Shell/Preprocess.hpp Shell/Property.hpp Shell/Rectify.hpp
Shell/Preprocess.o: Lib/Array.hpp Shell/Skolem.hpp Kernel/Substitution.hpp
Shell/Preprocess.o: Lib/Random.hpp Lib/Environment.hpp Kernel/Term.hpp
Shell/Preprocess.o: Shell/SimplifyFalseTrue.hpp
Shell/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp Lib/Sort.hpp
Shell/Profile.o: Debug/Assertion.hpp Lib/Allocator.hpp Lib/Environment.hpp
Shell/Profile.o: Kernel/Clause.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Shell/Profile.o: Lib/List.hpp Kernel/Signature.hpp Lib/Stack.hpp Lib/Map.hpp
Shell/Profile.o: Lib/Hash.hpp Lib/Exception.hpp Kernel/Term.hpp Lib/XML.hpp
Shell/Profile.o: Lib/Comparison.hpp Shell/Profile.hpp Kernel/Unit.hpp
Shell/Profile.o: Lib/Array.hpp
Shell/Property.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Shell/Property.o: Kernel/Clause.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Shell/Property.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/Property.o: Kernel/FormulaUnit.hpp Kernel/SubformulaIterator.hpp
Shell/Property.o: Kernel/Formula.hpp Lib/XML.hpp Kernel/Connective.hpp
Shell/Property.o: Kernel/Term.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/Property.o: Shell/FunctionDefinition.hpp Lib/MultiCounter.hpp
Shell/Property.o: Lib/XML.hpp Kernel/Unit.hpp Shell/Property.hpp
Shell/Rectify.o: Lib/Environment.hpp Kernel/Formula.hpp Lib/List.hpp
Shell/Rectify.o: Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/Rectify.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/Rectify.o: Lib/Allocator.hpp Kernel/Unit.hpp Kernel/Inference.hpp
Shell/Rectify.o: Kernel/Unit.hpp Kernel/Term.hpp Lib/Comparison.hpp
Shell/Rectify.o: Lib/Stack.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/Rectify.o: Shell/Rectify.hpp Lib/Array.hpp
Shell/Refutation.o: Debug/Tracer.hpp Lib/Hash.hpp Lib/Set.hpp
Shell/Refutation.o: Lib/Allocator.hpp Lib/Stack.hpp Debug/Assertion.hpp
Shell/Refutation.o: Kernel/Clause.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Shell/Refutation.o: Lib/List.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Shell/Refutation.o: Shell/Refutation.hpp
Shell/SimplifyFalseTrue.o: Debug/Tracer.hpp Lib/DArray.hpp
Shell/SimplifyFalseTrue.o: Debug/Assertion.hpp Lib/Allocator.hpp
Shell/SimplifyFalseTrue.o: Kernel/Inference.hpp Kernel/Unit.hpp
Shell/SimplifyFalseTrue.o: Lib/Allocator.hpp Kernel/FormulaUnit.hpp
Shell/SimplifyFalseTrue.o: Kernel/Unit.hpp Lib/List.hpp
Shell/SimplifyFalseTrue.o: Shell/SimplifyFalseTrue.hpp Kernel/Formula.hpp
Shell/SimplifyFalseTrue.o: Lib/XML.hpp Kernel/Connective.hpp
Shell/Skolem.o: Kernel/Signature.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Shell/Skolem.o: Lib/Stack.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/Skolem.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp Kernel/Term.hpp
Shell/Skolem.o: Lib/XML.hpp Lib/Comparison.hpp Kernel/Inference.hpp
Shell/Skolem.o: Kernel/Unit.hpp Kernel/FormulaUnit.hpp Kernel/Unit.hpp
Shell/Skolem.o: Lib/List.hpp Indexing/TermSharing.hpp Lib/Set.hpp
Shell/Skolem.o: Shell/Rectify.hpp Lib/Array.hpp Kernel/Formula.hpp
Shell/Skolem.o: Kernel/Connective.hpp Shell/Skolem.hpp
Shell/Skolem.o: Kernel/Substitution.hpp Lib/Random.hpp Lib/Environment.hpp
Shell/Skolem.o: Kernel/Term.hpp
Shell/Statistics.o: Shell/Statistics.hpp
Shell/SymCounter.o: Lib/Allocator.hpp Debug/Tracer.hpp Kernel/Term.hpp
Shell/SymCounter.o: Debug/Assertion.hpp Lib/XML.hpp Lib/Comparison.hpp
Shell/SymCounter.o: Lib/Stack.hpp Lib/Allocator.hpp Kernel/Clause.hpp
Shell/SymCounter.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp
Shell/SymCounter.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/SymCounter.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Shell/SymCounter.o: Lib/Exception.hpp Kernel/Unit.hpp Shell/SymCounter.hpp
Shell/TPTP.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Term.hpp
Shell/TPTP.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/XML.hpp
Shell/TPTP.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Shell/TPTP.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/Allocator.hpp
Shell/TPTP.o: Kernel/Formula.hpp Lib/List.hpp Kernel/Connective.hpp
Shell/TPTP.o: Kernel/FormulaUnit.hpp Kernel/Unit.hpp Kernel/Clause.hpp
Shell/TPTP.o: Shell/TPTP.hpp
Shell/TPTPLexer.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/Exception.hpp
Shell/TPTPLexer.o: Shell/TPTPLexer.hpp Shell/Lexer.hpp Lib/Array.hpp
Shell/TPTPLexer.o: Lib/Allocator.hpp Shell/Token.hpp
Shell/TPTPParser.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Shell/TPTPParser.o: Debug/Tracer.hpp Lib/Stack.hpp Lib/Environment.hpp
Shell/TPTPParser.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/Allocator.hpp
Shell/TPTPParser.o: Kernel/Signature.hpp Lib/Map.hpp Lib/Hash.hpp
Shell/TPTPParser.o: Lib/Exception.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/TPTPParser.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/TPTPParser.o: Kernel/Unit.hpp Kernel/Term.hpp Lib/Comparison.hpp
Shell/TPTPParser.o: Kernel/Clause.hpp Shell/Statistics.hpp
Shell/TPTPParser.o: Indexing/TermSharing.hpp Lib/Set.hpp Shell/Options.hpp
Shell/TPTPParser.o: Shell/TPTPLexer.hpp Shell/Lexer.hpp Lib/Array.hpp
Shell/TPTPParser.o: Lib/Exception.hpp Shell/Token.hpp Shell/TPTPParser.hpp
Shell/TPTPParser.o: Shell/Parser.hpp Lib/IntNameTable.hpp Lib/Array.hpp
Shell/TPTPParser.o: Lib/Map.hpp
Shell/TheoryFinder.o: Debug/Tracer.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Shell/TheoryFinder.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Shell/TheoryFinder.o: Lib/Allocator.hpp Kernel/Formula.hpp Lib/XML.hpp
Shell/TheoryFinder.o: Kernel/Connective.hpp Kernel/FormulaUnit.hpp
Shell/TheoryFinder.o: Kernel/Term.hpp Lib/Comparison.hpp Lib/Stack.hpp
Shell/TheoryFinder.o: Shell/Property.hpp Kernel/Unit.hpp
Shell/TheoryFinder.o: Shell/TheoryFinder.hpp
Shell/Token.o: Debug/Assertion.hpp Shell/Token.hpp
Kernel/Clause.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Kernel/Clause.o: Lib/Comparison.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Clause.o: Kernel/Clause.hpp Kernel/Unit.hpp Lib/List.hpp
Kernel/Clause.o: Debug/Assertion.hpp Lib/Allocator.hpp Kernel/Term.hpp
Kernel/Clause.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Kernel/ClauseQueue.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Random.hpp
Kernel/ClauseQueue.o: Lib/Environment.hpp Kernel/Clause.hpp Kernel/Unit.hpp
Kernel/ClauseQueue.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/ClauseQueue.o: Kernel/ClauseQueue.hpp
Kernel/DoubleSubstitution.o: Lib/Int.hpp Lib/Comparison.hpp Lib/DArray.hpp
Kernel/DoubleSubstitution.o: Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/DoubleSubstitution.o: Debug/Tracer.hpp Kernel/Term.hpp Lib/XML.hpp
Kernel/DoubleSubstitution.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/DoubleSubstitution.o: Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp
Kernel/DoubleSubstitution.o: Lib/Exception.hpp Lib/Hash.hpp
Kernel/Formula.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/MultiCounter.hpp
Kernel/Formula.o: Debug/Assertion.hpp Lib/XML.hpp Kernel/Term.hpp Lib/XML.hpp
Kernel/Formula.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
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
Kernel/FormulaVarIterator.o: Lib/Comparison.hpp Lib/Stack.hpp
Kernel/Inference.o: Debug/Tracer.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Kernel/Inference.o: Lib/Allocator.hpp
Kernel/KBO.o: Debug/Tracer.hpp Kernel/Term.hpp Debug/Assertion.hpp
Kernel/KBO.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/KBO.o: Kernel/KBO.hpp Kernel/Ordering.hpp Kernel/Signature.hpp
Kernel/KBO.o: Lib/Allocator.hpp Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
Kernel/Signature.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Signature.hpp
Kernel/Signature.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Stack.hpp
Kernel/Signature.o: Debug/Assertion.hpp Lib/Allocator.hpp Lib/Map.hpp
Kernel/Signature.o: Lib/Hash.hpp Lib/Exception.hpp
Kernel/SubformulaIterator.o: Debug/Tracer.hpp Kernel/SubformulaIterator.hpp
Kernel/SubformulaIterator.o: Kernel/Formula.hpp Lib/List.hpp
Kernel/SubformulaIterator.o: Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/SubformulaIterator.o: Lib/XML.hpp Kernel/Connective.hpp
Kernel/Substitution.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Term.hpp
Kernel/Substitution.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/XML.hpp
Kernel/Substitution.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Kernel/Substitution.o: Kernel/Substitution.hpp Lib/Random.hpp
Kernel/Substitution.o: Lib/Allocator.hpp Lib/Environment.hpp
Kernel/Term.o: Debug/Tracer.hpp Lib/Allocator.hpp Lib/Environment.hpp
Kernel/Term.o: Lib/Stack.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Kernel/Term.o: Lib/Int.hpp Lib/Comparison.hpp Kernel/Signature.hpp
Kernel/Term.o: Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
Kernel/Term.o: Kernel/Substitution.hpp Lib/Random.hpp Kernel/Term.hpp
Kernel/Term.o: Lib/XML.hpp Lib/Comparison.hpp Indexing/TermSharing.hpp
Kernel/Term.o: Lib/Set.hpp Kernel/Term.hpp
Kernel/TermFunIterator.o: Debug/Tracer.hpp Kernel/Term.hpp
Kernel/TermFunIterator.o: Debug/Assertion.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/TermFunIterator.o: Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermFunIterator.o: Kernel/TermFunIterator.hpp
Kernel/TermVarIterator.o: Debug/Tracer.hpp Kernel/Term.hpp
Kernel/TermVarIterator.o: Debug/Assertion.hpp Lib/XML.hpp Lib/Comparison.hpp
Kernel/TermVarIterator.o: Lib/Stack.hpp Lib/Allocator.hpp
Kernel/TermVarIterator.o: Kernel/TermVarIterator.hpp
Kernel/Unit.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp
Kernel/Unit.o: Kernel/Inference.hpp Kernel/Unit.hpp Lib/Allocator.hpp
Kernel/Unit.o: Kernel/Unit.hpp Lib/List.hpp Debug/Assertion.hpp
Kernel/Unit.o: Lib/Allocator.hpp
Indexing/SubstitutionTree.o: Kernel/Clause.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree.o: Debug/Tracer.hpp Kernel/Unit.hpp Lib/List.hpp
Indexing/SubstitutionTree.o: Debug/Assertion.hpp Lib/Allocator.hpp
Indexing/SubstitutionTree.o: Kernel/Term.hpp Lib/XML.hpp Lib/Comparison.hpp
Indexing/SubstitutionTree.o: Lib/Stack.hpp Lib/DHMap.hpp Lib/Exception.hpp
Indexing/SubstitutionTree.o: Lib/Hash.hpp Kernel/Signature.hpp Lib/Map.hpp
Indexing/SubstitutionTree.o: Lib/Environment.hpp Lib/Int.hpp
Indexing/SubstitutionTree.o: Lib/Comparison.hpp Test/Output.hpp
Indexing/SubstitutionTree.o: Indexing/SubstitutionTree.hpp
Indexing/SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/BinaryHeap.hpp
Indexing/SubstitutionTree.o: Lib/SkipList.hpp Lib/Random.hpp
Indexing/TermSharing.o: Kernel/Term.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Indexing/TermSharing.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Indexing/TermSharing.o: Lib/Allocator.hpp Indexing/TermSharing.hpp
Indexing/TermSharing.o: Lib/Set.hpp
Resolution/Active.o: Lib/Environment.hpp Kernel/Term.hpp Debug/Assertion.hpp
Resolution/Active.o: Debug/Tracer.hpp Lib/XML.hpp Lib/Comparison.hpp
Resolution/Active.o: Lib/Stack.hpp Lib/Allocator.hpp Kernel/Clause.hpp
Resolution/Active.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/Active.o: Shell/Statistics.hpp Resolution/Active.hpp
Resolution/Active.o: Kernel/ClauseQueue.hpp
Resolution/BinaryResolution.o: Lib/DArray.hpp Debug/Assertion.hpp
Resolution/BinaryResolution.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Int.hpp
Resolution/BinaryResolution.o: Lib/Comparison.hpp
Resolution/BinaryResolution.o: Kernel/DoubleSubstitution.hpp Lib/DHMap.hpp
Resolution/BinaryResolution.o: Lib/Exception.hpp Lib/Hash.hpp Kernel/Term.hpp
Resolution/BinaryResolution.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp
Resolution/BinaryResolution.o: Kernel/Term.hpp Kernel/Clause.hpp
Resolution/BinaryResolution.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/BinaryResolution.o: Kernel/Inference.hpp Kernel/Unit.hpp
Resolution/BinaryResolution.o: Resolution/BinaryResolution.hpp
Resolution/BinaryResolution.o: Resolution/ProofAttempt.hpp
Resolution/BinaryResolution.o: Resolution/Active.hpp Kernel/ClauseQueue.hpp
Resolution/BinaryResolution.o: Resolution/Passive.hpp
Resolution/BinaryResolution.o: Resolution/Unprocessed.hpp
Resolution/LiteralSelection.o: Kernel/Term.hpp Debug/Assertion.hpp
Resolution/LiteralSelection.o: Debug/Tracer.hpp Lib/XML.hpp
Resolution/LiteralSelection.o: Lib/Comparison.hpp Lib/Stack.hpp
Resolution/LiteralSelection.o: Lib/Allocator.hpp Kernel/Clause.hpp
Resolution/LiteralSelection.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/LiteralSelection.o: Resolution/LiteralSelection.hpp
Resolution/Passive.o: Lib/Environment.hpp Kernel/Term.hpp Debug/Assertion.hpp
Resolution/Passive.o: Debug/Tracer.hpp Lib/XML.hpp Lib/Comparison.hpp
Resolution/Passive.o: Lib/Stack.hpp Lib/Allocator.hpp Kernel/Clause.hpp
Resolution/Passive.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/Passive.o: Shell/Statistics.hpp Resolution/Passive.hpp
Resolution/Passive.o: Kernel/ClauseQueue.hpp
Resolution/ProofAttempt.o: Lib/Environment.hpp Lib/DArray.hpp
Resolution/ProofAttempt.o: Debug/Assertion.hpp Lib/Allocator.hpp
Resolution/ProofAttempt.o: Debug/Tracer.hpp Lib/Random.hpp Kernel/Clause.hpp
Resolution/ProofAttempt.o: Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Resolution/ProofAttempt.o: Kernel/Term.hpp Lib/XML.hpp Lib/Comparison.hpp
Resolution/ProofAttempt.o: Lib/Stack.hpp Kernel/Inference.hpp Kernel/Unit.hpp
Resolution/ProofAttempt.o: Shell/Statistics.hpp Shell/Options.hpp
Resolution/ProofAttempt.o: Resolution/LiteralSelection.hpp
Resolution/ProofAttempt.o: Resolution/Tautology.hpp
Resolution/ProofAttempt.o: Resolution/BinaryResolution.hpp
Resolution/ProofAttempt.o: Resolution/ProofAttempt.hpp Resolution/Active.hpp
Resolution/ProofAttempt.o: Kernel/ClauseQueue.hpp Resolution/Passive.hpp
Resolution/ProofAttempt.o: Resolution/Unprocessed.hpp
Resolution/Tautology.o: Lib/DArray.hpp Debug/Assertion.hpp Lib/Allocator.hpp
Resolution/Tautology.o: Debug/Tracer.hpp Lib/Random.hpp Lib/Environment.hpp
Resolution/Tautology.o: Kernel/Term.hpp Lib/XML.hpp Lib/Comparison.hpp
Resolution/Tautology.o: Lib/Stack.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Resolution/Tautology.o: Kernel/Unit.hpp Lib/List.hpp Shell/Statistics.hpp
Resolution/Tautology.o: Resolution/Tautology.hpp
Resolution/Unprocessed.o: Lib/Environment.hpp Kernel/Term.hpp
Resolution/Unprocessed.o: Debug/Assertion.hpp Debug/Tracer.hpp Lib/XML.hpp
Resolution/Unprocessed.o: Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Resolution/Unprocessed.o: Kernel/Clause.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Resolution/Unprocessed.o: Lib/List.hpp Shell/Statistics.hpp
Resolution/Unprocessed.o: Resolution/Unprocessed.hpp Kernel/ClauseQueue.hpp
Rule/CASC.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp Lib/Sort.hpp
Rule/CASC.o: Debug/Assertion.hpp Lib/Allocator.hpp Lib/Environment.hpp
Rule/CASC.o: Kernel/Clause.hpp Lib/Allocator.hpp Kernel/Unit.hpp Lib/List.hpp
Rule/CASC.o: Kernel/Signature.hpp Lib/Stack.hpp Lib/Map.hpp Lib/Hash.hpp
Rule/CASC.o: Lib/Exception.hpp Kernel/Term.hpp Lib/XML.hpp Lib/Comparison.hpp
Rule/CASC.o: Rule/Rule.hpp Rule/CASC.hpp Kernel/Unit.hpp Lib/Array.hpp
Rule/Index.o: Lib/Stack.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Rule/Index.o: Lib/Allocator.hpp Kernel/Clause.hpp Lib/Allocator.hpp
Rule/Index.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Signature.hpp Lib/Map.hpp
Rule/Index.o: Lib/Hash.hpp Lib/Exception.hpp Kernel/Term.hpp Lib/XML.hpp
Rule/Index.o: Lib/Comparison.hpp Rule/Index.hpp Kernel/Unit.hpp Rule/Rule.hpp
Rule/Profile.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp Lib/Sort.hpp
Rule/Profile.o: Debug/Assertion.hpp Lib/Allocator.hpp Lib/Environment.hpp
Rule/Profile.o: Kernel/Clause.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Rule/Profile.o: Lib/List.hpp Kernel/Signature.hpp Lib/Stack.hpp Lib/Map.hpp
Rule/Profile.o: Lib/Hash.hpp Lib/Exception.hpp Kernel/Term.hpp Lib/XML.hpp
Rule/Profile.o: Lib/Comparison.hpp Shell/Profile.hpp Kernel/Unit.hpp
Rule/Profile.o: Lib/Array.hpp
Rule/Prolog.o: Kernel/Term.hpp Debug/Assertion.hpp Debug/Tracer.hpp
Rule/Prolog.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Rule/Prolog.o: Kernel/Clause.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Rule/Prolog.o: Lib/List.hpp Rule/Prolog.hpp Lib/Map.hpp Lib/Hash.hpp
Rule/Prolog.o: Lib/Exception.hpp Rule/Index.hpp Kernel/Unit.hpp Rule/Rule.hpp
Rule/ProofAttempt.o: Debug/Tracer.hpp Lib/Environment.hpp
Rule/ProofAttempt.o: Shell/Statistics.hpp Resolution/ProofAttempt.hpp
Rule/ProofAttempt.o: Resolution/Active.hpp Kernel/ClauseQueue.hpp
Rule/ProofAttempt.o: Debug/Assertion.hpp Resolution/Passive.hpp
Rule/ProofAttempt.o: Resolution/Unprocessed.hpp
SAT/Assignment.o: Debug/Tracer.hpp SAT/Assignment.hpp Debug/Assertion.hpp
SAT/Assignment.o: SAT/SAT.hpp
Test/Output.o: Debug/Assertion.hpp Kernel/Term.hpp Debug/Tracer.hpp
Test/Output.o: Lib/XML.hpp Lib/Comparison.hpp Lib/Stack.hpp Lib/Allocator.hpp
Test/Output.o: Kernel/Clause.hpp Lib/Allocator.hpp Kernel/Unit.hpp
Test/Output.o: Lib/List.hpp Lib/Int.hpp Lib/Comparison.hpp Test/Output.hpp
Test/Output.o: Lib/Environment.hpp Kernel/Signature.hpp Lib/Map.hpp
Test/Output.o: Lib/Hash.hpp Lib/Exception.hpp
Global.o: Debug/Assertion.hpp Lib/Enumerator.hpp Kernel/Formula.hpp
Global.o: Lib/List.hpp Debug/Assertion.hpp Lib/Allocator.hpp Debug/Tracer.hpp
Global.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/Unit.hpp
Global.o: Lib/Environment.hpp
alucard.o: Debug/Tracer.hpp Lib/Random.hpp Lib/Set.hpp Lib/Allocator.hpp
alucard.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp Lib/Timer.hpp
alucard.o: Debug/Assertion.hpp Lib/Exception.hpp Lib/Environment.hpp
alucard.o: Lib/Vector.hpp Kernel/Signature.hpp Lib/Allocator.hpp
alucard.o: Lib/Stack.hpp Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
alucard.o: Kernel/Clause.hpp Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp
alucard.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
alucard.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
alucard.o: Lib/Comparison.hpp Indexing/SubstitutionTree.hpp
alucard.o: Lib/VirtualIterator.hpp Lib/BinaryHeap.hpp Lib/Int.hpp
alucard.o: Lib/SkipList.hpp Lib/Random.hpp Shell/Options.hpp
alucard.o: Shell/CommandLine.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
alucard.o: Lib/Array.hpp Lib/Exception.hpp Shell/Token.hpp Shell/TPTP.hpp
alucard.o: Shell/TPTPParser.hpp Kernel/Unit.hpp Shell/Parser.hpp
alucard.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp Shell/Property.hpp
alucard.o: Shell/Preprocess.hpp Shell/Statistics.hpp Shell/Refutation.hpp
alucard.o: Shell/TheoryFinder.hpp Resolution/ProofAttempt.hpp
alucard.o: Resolution/Active.hpp Kernel/ClauseQueue.hpp
alucard.o: Resolution/Passive.hpp Resolution/Unprocessed.hpp Rule/CASC.hpp
alucard.o: Rule/Prolog.hpp Rule/Index.hpp Rule/Rule.hpp Rule/Index.hpp
alucard.o: Rule/ProofAttempt.hpp
sat.o: Lib/Random.hpp
test_BinaryHeap.o: Lib/BinaryHeap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
test_BinaryHeap.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/Comparison.hpp
test_BinaryHeap.o: Lib/Int.hpp
test_DHMap.o: Lib/DHMap.hpp Debug/Assertion.hpp Lib/Allocator.hpp
test_DHMap.o: Debug/Tracer.hpp Lib/Exception.hpp Lib/Hash.hpp
test_SkipList.o: Lib/SkipList.hpp Debug/Assertion.hpp Debug/Tracer.hpp
test_SkipList.o: Lib/Allocator.hpp Lib/Comparison.hpp Lib/Random.hpp
test_SkipList.o: Lib/BinaryHeap.hpp Lib/Exception.hpp Lib/Int.hpp
test_SubstitutionTree.o: Debug/Tracer.hpp Lib/Array.hpp Debug/Assertion.hpp
test_SubstitutionTree.o: Lib/Allocator.hpp Debug/Tracer.hpp Lib/Random.hpp
test_SubstitutionTree.o: Lib/Set.hpp Lib/Allocator.hpp Lib/Int.hpp
test_SubstitutionTree.o: Lib/Comparison.hpp Lib/Timer.hpp Lib/Exception.hpp
test_SubstitutionTree.o: Lib/Environment.hpp Lib/Vector.hpp
test_SubstitutionTree.o: Kernel/Signature.hpp Lib/Stack.hpp Lib/Map.hpp
test_SubstitutionTree.o: Lib/Hash.hpp Lib/Exception.hpp Kernel/Clause.hpp
test_SubstitutionTree.o: Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp
test_SubstitutionTree.o: Lib/XML.hpp Kernel/Connective.hpp
test_SubstitutionTree.o: Kernel/FormulaUnit.hpp Indexing/TermSharing.hpp
test_SubstitutionTree.o: Lib/Set.hpp Kernel/Term.hpp Lib/Comparison.hpp
test_SubstitutionTree.o: Indexing/SubstitutionTree.hpp
test_SubstitutionTree.o: Lib/VirtualIterator.hpp Lib/BinaryHeap.hpp
test_SubstitutionTree.o: Lib/Int.hpp Lib/SkipList.hpp Lib/Random.hpp
test_SubstitutionTree.o: Shell/Options.hpp Shell/CommandLine.hpp
test_SubstitutionTree.o: Shell/TPTPLexer.hpp Shell/Lexer.hpp Lib/Array.hpp
test_SubstitutionTree.o: Lib/Exception.hpp Shell/Token.hpp Shell/TPTP.hpp
test_SubstitutionTree.o: Shell/TPTPParser.hpp Kernel/Unit.hpp
test_SubstitutionTree.o: Shell/Parser.hpp Lib/IntNameTable.hpp Lib/Array.hpp
test_SubstitutionTree.o: Lib/Map.hpp Shell/Property.hpp Shell/Preprocess.hpp
test_SubstitutionTree.o: Shell/Statistics.hpp Shell/Refutation.hpp
test_SubstitutionTree.o: Shell/TheoryFinder.hpp Resolution/ProofAttempt.hpp
test_SubstitutionTree.o: Resolution/Active.hpp Kernel/ClauseQueue.hpp
test_SubstitutionTree.o: Resolution/Passive.hpp Resolution/Unprocessed.hpp
test_SubstitutionTree.o: Rule/CASC.hpp Rule/Prolog.hpp Rule/Index.hpp
test_SubstitutionTree.o: Rule/Rule.hpp Rule/Index.hpp Rule/ProofAttempt.hpp
test_SubstitutionTree.o: Test/Output.hpp
vampire.o: Debug/Tracer.hpp Lib/Random.hpp Lib/Set.hpp Lib/Allocator.hpp
vampire.o: Debug/Tracer.hpp Lib/Int.hpp Lib/Comparison.hpp Lib/Timer.hpp
vampire.o: Debug/Assertion.hpp Lib/Exception.hpp Lib/Environment.hpp
vampire.o: Lib/Vector.hpp Kernel/Signature.hpp Lib/Allocator.hpp
vampire.o: Lib/Stack.hpp Lib/Map.hpp Lib/Hash.hpp Lib/Exception.hpp
vampire.o: Kernel/Clause.hpp Kernel/Unit.hpp Lib/List.hpp Kernel/Formula.hpp
vampire.o: Lib/XML.hpp Kernel/Connective.hpp Kernel/FormulaUnit.hpp
vampire.o: Indexing/TermSharing.hpp Lib/Set.hpp Kernel/Term.hpp
vampire.o: Lib/Comparison.hpp Indexing/SubstitutionTree.hpp
vampire.o: Lib/VirtualIterator.hpp Lib/BinaryHeap.hpp Lib/Int.hpp
vampire.o: Lib/SkipList.hpp Lib/Random.hpp Shell/Options.hpp
vampire.o: Shell/CommandLine.hpp Shell/TPTPLexer.hpp Shell/Lexer.hpp
vampire.o: Lib/Array.hpp Lib/Exception.hpp Shell/Token.hpp Shell/TPTP.hpp
vampire.o: Shell/TPTPParser.hpp Kernel/Unit.hpp Shell/Parser.hpp
vampire.o: Lib/IntNameTable.hpp Lib/Array.hpp Lib/Map.hpp Shell/Property.hpp
vampire.o: Shell/Preprocess.hpp Shell/Statistics.hpp Shell/Refutation.hpp
vampire.o: Shell/TheoryFinder.hpp Rule/CASC.hpp Rule/Prolog.hpp
vampire.o: Rule/Index.hpp Rule/Rule.hpp Rule/Index.hpp Rule/ProofAttempt.hpp
