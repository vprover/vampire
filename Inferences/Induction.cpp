/*
 * File Induction 
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
 * @file Induction.cpp
 * Implements class Induction.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"
#include "Lib/Array.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Connective.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Inferences/BinaryResolution.hpp"

#include "Induction.hpp"

namespace Inferences
{
using namespace Kernel;
using namespace Lib; 


TermList ConstantReplacement::transformSubterm(TermList trm)
{
  CALL("ConstantReplacement::transformSubterm");

  if(trm.isTerm() && trm.term()->functor()==_f){
   return _r;
  }
  return trm;
}

ClauseIterator Induction::generateClauses(Clause* premise)
{
  CALL("Induction::generateClauses");

  return pvi(InductionClauseIterator(premise));
}

InductionClauseIterator::InductionClauseIterator(Clause* premise)
{
  CALL("InductionClauseIterator::InductionClauseIterator");

  static bool structInd = env.options->induction() == Options::Induction::BOTH ||
                         env.options->induction() == Options::Induction::STRUCTURAL;
  static bool mathInd = env.options->induction() == Options::Induction::BOTH ||
                         env.options->induction() == Options::Induction::MATHEMATICAL;

  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal = (kind == Options::InductionChoice::GOAL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);

  static unsigned maxD = env.options->maxInductionDepth();

  bool negOnly = env.options->inductionNegOnly();


  if(premise->length()==1 && 
     (all || ( (goal || goal_plus) && premise->isGoal())) &&
     (maxD == 0 || premise->inductionDepth() < maxD)
    )
  {
    Literal* lit = (*premise)[0];

     // TODO change to allow for positive occurence of <
    if((!negOnly || lit->isNegative() || 
         (theory->isInterpretedPredicate(lit) && theory->isInequality(theory->interpretPredicate(lit)))
       )&& 
       lit->ground()
      ){

      Set<unsigned> ta_constants;
      Set<unsigned> int_constants;
      TermFunIterator it(lit);
      it.next(); // to move past the lit symbol
      while(it.hasNext()){
        unsigned f = it.next();
        if(env.signature->functionArity(f)==0 &&
           (
               all
            || env.signature->getFunction(f)->inGoal()
            || (goal_plus && env.signature->getFunction(f)->inductionSkolem())
           )
        ){
         if(structInd && 
            env.signature->isTermAlgebraSort(env.signature->getFunction(f)->fnType()->result()) &&
            !env.signature->getFunction(f)->termAlgebraCons()
           ){
            ta_constants.insert(f);
          }
          if(mathInd && 
             env.signature->getFunction(f)->fnType()->result()==Sorts::SRT_INTEGER &&
             !theory->isInterpretedConstant(f)
            ){
            int_constants.insert(f);
          }
        }
      }
      Set<unsigned>::Iterator citer1(int_constants);
      while(citer1.hasNext()){
        unsigned c = citer1.next();
        performMathInduction(premise,lit,c);
      }
      Set<unsigned>::Iterator citer2(ta_constants);
      while(citer2.hasNext()){
        unsigned c = citer2.next();
        //cout << "PERFORM INDUCTION on " << env.signature->functionName(c) << endl;
        static bool one = env.options->structInduction() == Options::StructuralInductionKind::ONE ||
                          env.options->structInduction() == Options::StructuralInductionKind::ALL; 
        static bool two = env.options->structInduction() == Options::StructuralInductionKind::TWO ||
                          env.options->structInduction() == Options::StructuralInductionKind::ALL; 

        if(notDone(lit,c)){

          if(one){
            performStructInductionOne(premise,lit,c);
          }
          if(two){
            performStructInductionTwo(premise,lit,c);
          }
        }
      } 
    }
  }
}

      // deal with integer constants
      // introduce new clauses per eligable constant:
      // L[zero] | L[fresh+1] | L[fresh-1] 
      // L[zero] | L[fresh+1] | c<0
      // L[zero] | ~[fresh] 
      // where fresh is a fresh constant
void InductionClauseIterator::performMathInduction(Clause* premise, Literal* lit, unsigned c)
{
  CALL("InductionClauseIterator::performMathInduction");

        //cout << "PERFORM INDUCTION on " << env.signature->functionName(c) << endl;

        // create fresh
        unsigned freshS = env.signature->addSkolemFunction(0);
        Signature::Symbol* symbol = env.signature->getFunction(freshS);
        symbol->setType(OperatorType::getConstantsType(Sorts::SRT_INTEGER));
        symbol->markInductionSkolem();
        TermList fresh(Term::createConstant(freshS));

        TermList zero(theory->representConstant(IntegerConstantType(0)));
        TermList one(theory->representConstant(IntegerConstantType(1)));
        TermList mone(theory->representConstant(IntegerConstantType(-1)));

        // create L[zero]
        ConstantReplacement cr1(c,zero);
        Literal* Lzero = cr1.transform(lit);

        // create L[fresh+1]
        TermList fpo(Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS),fresh,one));
        ConstantReplacement cr2(c,fpo);
        Literal* Lfpo = cr2.transform(lit);

        // create L[fresh-1]
        TermList fpmo(Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS),fresh,mone));
        ConstantReplacement cr3(c,fpmo);
        Literal* Lfpmo = cr3.transform(lit);

        // create ~L[fresh]
        ConstantReplacement cr4(c,fresh);
        Literal* nLfresh = Literal::complementaryLiteral(cr4.transform(lit));

        // create c<0
        Literal* cLz = Literal::create2(env.signature->getInterpretingSymbol(Theory::INT_LESS),true,TermList(Term::createConstant(c)),zero);

        // put it all together i.e. create three clauses
        // L[zero] | L[fresh+1] | L[fresh-1] 
        // L[zero] | L[fresh+1] | c<0
        // L[zero] | ~L[fresh] 
        Inference* inf1 = new Inference1(Inference::INDUCTION,premise);
        Inference* inf2 = new Inference1(Inference::INDUCTION,premise);
        Inference* inf3 = new Inference1(Inference::INDUCTION,premise);
        Clause* r1 = new(3) Clause(3,premise->inputType(),inf1);
        Clause* r2 = new(3) Clause(3,premise->inputType(),inf2);
        Clause* r3 = new(2) Clause(2,premise->inputType(),inf3);

        (*r1)[0] = Lzero;
        (*r1)[1] = Lfpo; 
        (*r1)[2] = Lfpmo;

        (*r2)[0] = Lzero;
        (*r2)[1] = Lfpo;
        (*r2)[2] = cLz;

        (*r3)[0] = Lzero;
        (*r3)[1] = nLfresh;

        _clauses.push(r1);
        _clauses.push(r2);
        _clauses.push(r3);
        env.statistics->induction++;

 }

/**
 * Introduce the Induction Hypothesis
 * ( L[base1] & ... & L[basen] & (L[x] => L[c1(x)]) & ... (L[x] => L[cm(x)]) ) => L[x]
 * for some lit ~L[a]
 * and then force binary resolution on L for each resultant clause
 */

void InductionClauseIterator::performStructInductionOne(Clause* premise, Literal* lit, unsigned c)
{
  CALL("InductionClauseIterator::performStructInductionOne"); 

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(c)->fnType()->result());
  unsigned ta_sort = ta->sort();

  FormulaList* formulas = FormulaList::empty();

  Literal* clit = Literal::complementaryLiteral(lit);
  unsigned var = 0;

  // first produce the formula
  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();
    Formula* f = 0;

    // non recursive get L[_]
    if(!con->recursive()){
      if(arity==0){
        ConstantReplacement cr(c,TermList(Term::createConstant(con->functor())));
        f = new AtomicFormula(cr.transform(clit)); 
      }
      else{
        Stack<TermList> argTerms;
        for(unsigned i=0;i<arity;i++){
          argTerms.push(TermList(var,false));
          var++;
        }
        ConstantReplacement cr(c,TermList(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin())));
        f = new AtomicFormula(cr.transform(clit));
      }
    }
    // recursive get (L[x] => L[c(x)])
    else{
      ASS(arity>0);
      Stack<TermList> argTerms;
      Stack<TermList> ta_vars;
      for(unsigned i=0;i<arity;i++){
        TermList x(var,false);
        var++;
        if(con->argSort(i) == ta_sort){
          ta_vars.push(x);
        }
        argTerms.push(x);
      }
      ConstantReplacement cr(c,TermList(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin())));
      Formula* right = new AtomicFormula(cr.transform(clit));
      Formula* left = 0;
      ASS(ta_vars.size()>=1);
      if(ta_vars.size()==1){
        ConstantReplacement cr(c,ta_vars[0]);
        left = new AtomicFormula(cr.transform(clit));
      }
      else{
        FormulaList* args = FormulaList::empty();
        Stack<TermList>::Iterator tvit(ta_vars);
        while(tvit.hasNext()){
          ConstantReplacement cr(c,tvit.next());
          args = new FormulaList(new AtomicFormula(cr.transform(clit)),args);
        }
        left = new JunctionFormula(Connective::AND,args);
      }
      f = new BinaryFormula(Connective::IMP,left,right);
    }

    ASS(f);
    formulas = new FormulaList(f,formulas);
  }
  ConstantReplacement cr(c,TermList(var,false));
  Literal* conclusion = cr.transform(clit);
  Formula* hypothesis = new BinaryFormula(Connective::IMP,
                            Formula::quantify(new JunctionFormula(Connective::AND,formulas)),
                            Formula::quantify(new AtomicFormula(conclusion)));

  NewCNF cnf(0);
  Stack<Clause*> hyp_clauses;
  FormulaUnit* fu = new FormulaUnit(hypothesis,new Inference(Inference::INDUCTION),Unit::AXIOM);
  cnf.clausify(NNF::ennf(fu), hyp_clauses);

  //cout << "Clausify " << fu->toString() << endl;

  // Now perform resolution between lit and the hyp_clauses on clit, which should be contained in each clause!
  Stack<Clause*>::Iterator cit(hyp_clauses);
  while(cit.hasNext()){
    Clause* c = cit.next();
    static ResultSubstitutionSP identity = ResultSubstitutionSP(new IdentitySubstitution());
    SLQueryResult qr(lit,premise,identity);
    Clause* r = BinaryResolution::generateClause(c,conclusion,qr,*env.options);
    _clauses.push(r);
  }
  env.statistics->induction++;
}

/**
 * This idea (taken from the CVC4 paper) is that there exists some smallest k that makes lit true
 * We produce the clause ~L[x] \/ ?y : L[y] & !z (z subterm y -> ~L[z])
 * and perform resolution with lit L[c]
 */
void InductionClauseIterator::performStructInductionTwo(Clause* premise, Literal* lit, unsigned c)
{

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(c)->fnType()->result());
  unsigned ta_sort = ta->sort();

  Literal* clit = Literal::complementaryLiteral(lit);

  // make L[y]
  TermList y(0,false); 
  ConstantReplacement cr(c,y);
  Literal* Ly = cr.transform(lit);

  // for each constructor and destructor make
  // ![Z] : y = cons(Z,dec(y)) -> ( ~L[dec1(y)] & ~L[dec2(y)]
  FormulaList* formulas = FormulaList::empty();

  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();
  
    // ignore a constructor if it doesn't mention ta_sort
    bool ignore = (arity == 0);
    for(unsigned j=0;j<arity; j++){ ignore &= (con->argSort(j)!=ta_sort); } 

    if(!ignore){
  
      // First generate all argTerms and remember those that are of sort ta_sort 
      Stack<TermList> argTerms;
      Stack<TermList> taTerms; 
      for(unsigned j=0;j<arity;j++){
        unsigned dj = con->destructorFunctor(j);
        TermList djy(Term::create1(dj,y));
        argTerms.push(djy);
        if(con->argSort(j) == ta_sort){
          taTerms.push(djy);
        }
      }
      // create y != con1(...d1(y)...d2(y)...)
      TermList coni(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
      Literal* kneq = Literal::createEquality(true,y,coni,ta_sort);
      FormulaList* And = FormulaList::empty(); 
      Stack<TermList>::Iterator tit(taTerms);
      unsigned and_terms = 0;
      while(tit.hasNext()){
        TermList djy = tit.next();
        ConstantReplacement cr(c,djy);
        Literal* nLdjy = cr.transform(clit);
        Formula* f = new AtomicFormula(nLdjy); 
        And = new FormulaList(f,And);
        and_terms++;
      }
      ASS(and_terms>0);
      Formula* imp = new BinaryFormula(Connective::IMP,
                            new AtomicFormula(kneq),
                            (and_terms>1) ? new JunctionFormula(Connective::AND,And)
                                          : And->head()
                            );
      formulas = new FormulaList(imp,formulas);
      
    }
  }
  Formula* exists = new QuantifiedFormula(Connective::EXISTS, new Formula::VarList(y.var(),0),0,
                  new JunctionFormula(Connective::AND,new FormulaList(new AtomicFormula(Ly),formulas))); 
  
  ConstantReplacement cr2(c,TermList(1,false));
  Literal* conclusion = cr2.transform(clit);
  FormulaList* orf = new FormulaList(exists,new FormulaList(Formula::quantify(new AtomicFormula(conclusion)),FormulaList::empty()));
  Formula* hypothesis = new JunctionFormula(Connective::OR,orf);

  NewCNF cnf(0);
  Stack<Clause*> hyp_clauses;
  FormulaUnit* fu = new FormulaUnit(hypothesis,new Inference(Inference::INDUCTION),Unit::AXIOM);
  cnf.clausify(NNF::ennf(fu), hyp_clauses);

  //cout << "Clausify " << fu->toString() << endl;

  // Now perform resolution between lit and the hyp_clauses on clit, which should be contained in each clause!
  Stack<Clause*>::Iterator cit(hyp_clauses);
  while(cit.hasNext()){
    Clause* c = cit.next();
    static ResultSubstitutionSP identity = ResultSubstitutionSP(new IdentitySubstitution());
    SLQueryResult qr(lit,premise,identity);
    Clause* r = BinaryResolution::generateClause(c,conclusion,qr,*env.options);
    _clauses.push(r);
  }
  env.statistics->induction++;  

}

void InductionClauseIterator::performStructInductionThree(Clause* premise, Literal* lit, unsigned constant)
{
  CALL("InductionClauseIterator::performStructInductionThree");

}

bool InductionClauseIterator::notDone(Literal* lit, unsigned constant)
{
  CALL("InductionClauseIterator::notDone");

  static DHSet<Literal*> done;
  static DHMap<unsigned,TermList> blanks; 
  unsigned srt = env.signature->getFunction(constant)->fnType()->result();

  if(!blanks.find(srt)){
    unsigned fresh = env.signature->addFreshFunction(0,"blank");
    env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(srt));
    TermList blank = TermList(Term::createConstant(fresh));
    blanks.insert(srt,blank);
  }

  ConstantReplacement cr(constant,blanks.get(srt));
  Literal* rep = cr.transform(lit);

  if(done.contains(rep)){ 
    return false; 
  }

  done.insert(rep);

  return true;
}

}
