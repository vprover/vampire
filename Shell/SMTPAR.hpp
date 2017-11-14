
/*
 * File SMTPAR.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file SMTPAR.hpp
 * Defines class SMTParser for parsing SMT files.
 *
 * @since 22/01/2009 Manchester
 */

#ifndef __SMTParser__
#define __SMTParser__

#include <iostream>

#include "Lib/VString.hpp"
#include "../Lib/Exception.hpp"
#include "PARSER_TKV.hpp"

using namespace std;

namespace Shell {

class SMTLexer;

/**
 * Class SMTParser, implements a SMT Parser.
 *
 * @since 22/01/2009 Manchester
 */
class SMTParser
  : public Parser
{
public:
  /** The logic used */
  enum Logic {
    /** Quantifier-free rational linear arithmetic */
//    QF_RDL
//Nestan changed 12.02.09
    QF_LRA

  };
  /** The problem status */
  enum Status {
    /** satisfiable */
    SAT,
    /** unsatisfiable */
    UNSAT,
    /** unknown */
    UNKNOWN
  };

  /** Sorts */
  enum Sort {
    /** Real, corresponds to the Real sort in SMT LIB */
    REAL
  };

  /** Annotations, pair attribute-value  */
  struct Annotation {
    /** attribute */
    vstring attribute;
    /** value */
    vstring value;
    /** next annotation in the list */
    Annotation* next;
  }; 

  /** Function declarations, correpond to the :extrafuns in the SMT LIB syntax */
  struct FunctionDeclaration {
    FunctionDeclaration(const vstring& name);
    /** name of the function */
    vstring name;
    /** sort */
    Sort sort;
    /** annotations */
    Annotation* annotations;
    /** next function declaration in the list */
    FunctionDeclaration* next;
  }; 

  /** Predicate declarations, correpond to the :extrapreds in the SMT LIB syntax */
  struct PredicateDeclaration {
    PredicateDeclaration(const vstring& name);
    /** name of the predicate */
    vstring name;
    /** sort */
    Sort sort;
    /** annotations */
    Annotation* annotations;
    /** next declaration in the list */
    PredicateDeclaration* next;
  }; 

  /** connectives use to build formulas */
  enum Connective {
    /** atomic formula */
    ATOM,
    /** negation */
    NOT,
    /** conjunction */
    AND,
    /** disjunction */
    OR,
    /** implication */
    IMPLY,
    /** equivalence */
    IFF,
    /** exclusive or */
    XOR,
    /** universal quantifier */
    FORALL,
    /** existential quantifier */
    EXISTS
  };

  /** type of the term */
  enum TermType {
    TERM_INT,
    TERM_REAL,
    TERM_ARITH,
    TERM_COMPLEX
  }; 

  /** term in the SMT syntax */
  struct Term {
    /** term kind */
    TermType kind;
    /** function symbol or number written as a vstring */
    vstring fun;
    /** list of arguments */
    Term* args;
    /** next subformula, if this term is part of a list */
    Term* next;
    /** build a new term with a given kind and function symbol, empty
     *  arguments and null next term */
    /** occasional annotation(s) */
    Annotation* annotations;
    Term(TermType tt,vstring str)
      : kind(tt),
	fun(str),
	args(0),
	next(0),
	annotations(0)
    {};

    void toString (){//cout<<endl;
      cout<<this->fun<<" ";
        if (this->args != 0){
          this->args->toString();
        };
        if (this->next != 0){
          this->next->toString();
        };
    };

  };

  /** atomic formula in the SMT syntax */
  struct Atom {
    /** Create a new atom with a given name and no arguments */
    Atom(vstring nm)
      : pred(nm),
	args(0),
	annotations(0)
    {}
    /** predicate symbol */
    vstring pred;
    /** arguments */
    Term* args;
    /** occasional annotation(s) */
    Annotation* annotations;
    void toString (){
      this->args->toString();
    };


  };




  /** formulas in the SMT LIB syntax */
  struct Formula {
    /** Create a new formula with the given connective and empty next formula */
    Formula(Connective con)
      : connective(con),
	args(0),
	next(0)
    {}
    /** connective of this formula */
    Connective connective;
    union {
      /** immediate subformulas, if the formula is not atomic */
      Formula* args;
      /** atomic formula */
      Atom* atom;
    };
    /** next subformula, if this formula is part of a list */
    Formula* next;
  };

  /** Benchmark */
  struct Benchmark {
    Benchmark(const vstring& nm);
    /** name */
    vstring name;
    /** logic used */
    Logic logic;
    /** status */
    Status status;
    /** Function/variable declarations */
    FunctionDeclaration* functionDeclarations;
    /** Predicate declarations */
    PredicateDeclaration* predicateDeclarations;
    /** List of extra annotations */
    Annotation* annotations;
    /** Formula */
    Formula* formula;
  };

  explicit SMTParser(SMTLexer& lexer);
  Benchmark* benchmark();
  Annotation* annotation();
private:
  void predicates(PredicateDeclaration**);
  void functions(FunctionDeclaration**);
  void formula(Formula**);
  void formulas(Formula**);
  void term(Term**);
  void terms(Term**);

}; // class SMTParser

}

#endif

