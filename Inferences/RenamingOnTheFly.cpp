/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ProxyElimination.cpp
 *
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Statistics.hpp"
#include "Shell/Skolem.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "RenamingOnTheFly.hpp"

namespace Inferences {
using namespace Indexing;

typedef ApplicativeHelper AH;

void RenamingOnTheFly::attach(SaturationAlgorithm* salg)
{
  CALL("RenamingOnTheFly::attach");

  SimplificationEngine::attach(salg);
  _formulaIndex=static_cast<RenamingFormulaIndex*> (
   _salg->getIndexManager()->request(RENAMING_FORMULA_INDEX) );
}

void RenamingOnTheFly::detach()
{
  CALL("RenamingOnTheFly::detach");

  _formulaIndex=0;
  _salg->getIndexManager()->release(RENAMING_FORMULA_INDEX);
  SimplificationEngine::detach();
}

ClauseIterator RenamingOnTheFly::produceClauses(Clause* c)
{
  CALL("RenamingOnTheFly::produceClauses");  

  //0 means dont rename
  static int namingBound = env.options->naming();

  TermList troo = TermList(Term::foolTrue());
  TermList boolSort = AtomicSort::boolSort();

  unsigned clen = c->length();
  UnitList* defs = 0;
  ClauseStack newClauses;
  LiteralStack lits;
  static TermStack args;
  TermList head;
  bool modified = false;

  for(unsigned i = 0; i<clen; i++){
    Literal* lit = (*c)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    TermList formula;
    TermList boolVal;
    if(AH::isBool(lhs)){
      boolVal = lhs;
      formula = rhs;
    } else if(AH::isBool(rhs)){
      boolVal = rhs;
      formula = lhs;
    } else {
      lits.push(lit);
      continue;
    }

    bool positive = AH::isTrue(boolVal) == lit->polarity();

    AH::getHeadAndArgs(formula, head, args);
    Signature::Proxy prox = AH::getProxy(head);
    
    if(prox != Signature::NOT_PROXY){
      auto results = _formulaIndex->getGeneralizations(formula, true);
      
      bool nameExists = false;
      bool needToAddDefClause = true;
      TermQueryResult tqr;
      TermList nameS;
      TermList name;
      while(results.hasNext()){
        nameExists = true;
        tqr = results.next();
        
        name = tqr.term;
        nameS = tqr.substitution->applyToBoundResult(name);

        Literal* defLit = tqr.literal;
        if(positive == defLit->polarity()){
          needToAddDefClause = false;
          break;
        }
      } 

      if(nameExists){
        //cout << "the clause is " + c->toString() << endl;
        //cout << "the formula is " + formula.toString() << endl;
        //cout << "the name is " + name.toString() << endl;
        //cout << "the lit is " + tqr.literal->toString() << endl;
        //cout << "other clause is " + tqr.clause->toString() << endl;
        //cout << "the sub is " + tqr.substitution->toString() << endl;
        Literal* newLit = Literal::createEquality(positive, nameS, troo, boolSort);
        if(needToAddDefClause){
          Clause* defClause = tqr.clause;
          ASS(defClause->size() == 2);
          Literal* l1 = (*defClause)[0];
          Literal* l2 = (*defClause)[1];
          Literal* l1RevPol = Literal::complementaryLiteral(l1);
          Literal* l2RevPol = Literal::complementaryLiteral(l2);
          Inference* inf = new Inference(Inference::PREDICATE_DEFINITION);
          Clause* defClauseRevPol = new(2) Clause(2, Unit::AXIOM, inf);
          (*defClauseRevPol)[0] = l1RevPol;
          (*defClauseRevPol)[1] = l2RevPol;
          UnitList::push(defClauseRevPol, defs);
          newClauses.push(defClauseRevPol);
          if(isNamingLit(l1)){
            addToQueue(getFormula(l2), name, l1RevPol, defClauseRevPol);
          } else {
            addToQueue(getFormula(l1), name, l2RevPol, defClauseRevPol);
          }
        }
        lits.push(newLit);
        modified = true;
        continue;
      }

      if(namingBound > 0 && 
         env.signature->formulaCount(formula.term()) >= namingBound) {
        env.signature->formulaNamed(formula.term());

        //create name
        static DHMap<unsigned,TermList> varSorts;
        varSorts.reset();
   
        VariableIterator2 vit(formula.term());
        while(vit.hasNext()){
          pair<TermList, TermList> varTypePair = vit.next();
          if(!varSorts.find(varTypePair.first.var())){
            varSorts.insert(varTypePair.first.var(), varTypePair.second);
          }
        }
   
        static Stack<TermList> argSorts;
        static Stack<TermList> termArgs;
        static Stack<TermList> args;
        argSorts.reset();
        termArgs.reset();
        args.reset();
   
        unsigned var;
        TermList varSort; 
        DHMap<unsigned, TermList>::Iterator mapIt(varSorts);
        while(mapIt.hasNext()) {
          mapIt.next(var, varSort);
          if(varSort == AtomicSort::superSort()){
            args.push(TermList(var, false));
          } else {
            argSorts.push(varSort);
            termArgs.push(TermList(var, false));
          }
        }
        ASS(termArgs.size() == argSorts.size());

        VList* vl = VList::empty();
        for(int i = args.size() -1; i >= 0 ; i--){
          VList::push(args[i].var(), vl);
        }

        unsigned fun = env.signature->addNameFunction(args.size());
        TermList sort = AtomicSort::arrowSort(argSorts, AtomicSort::boolSort());
        Signature::Symbol* sym = env.signature->getFunction(fun);
        sym->setType(OperatorType::getConstantsType(sort, vl)); 
        TermList funApplied = TermList(Term::create(fun, args.size(), args.begin()));
        TermList name = AH::createAppTerm(sort, funApplied, termArgs);


        //create definition clause
        Inference* inf = new Inference(Inference::PREDICATE_DEFINITION);
        Clause* defClause = new(2) Clause(2, Unit::AXIOM, inf);
        Literal* l1 = Literal::createEquality(!positive, name, troo, boolSort);
        Literal* l2 = Literal::createEquality(positive, formula, troo, boolSort);
        (*defClause)[0] = l1;
        (*defClause)[1] = l2;
        UnitList::push(defClause, defs);
        newClauses.push(defClause);
        addToQueue(formula, name, l1, defClause);

        Literal* newLit = Literal::createEquality(positive, name, troo, boolSort);
        lits.push(newLit);
        modified = true;
        continue;
      }

      lits.push(lit);
      continue;
    }
    lits.push(lit);

  }
 
  if(!modified){
    ASS(newClauses.isEmpty());
    return ClauseIterator::getEmpty();
  }

  UnitList::push(c, defs);
  Inference* inf = new InferenceMany(Inference::DEFINITION_FOLDING, defs);
  Clause* res = Clause::fromStack(lits, c->inputType(), inf);
  newClauses.push(res);   
  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(newClauses)));
}

ClauseIterator RenamingOnTheFly::perform(Clause* c)
{
  CALL("RenamingOnTheFly::perform");
  
  if(c->inference()->rule() == Inference::PREDICATE_DEFINITION){
    //dont want to name definitions
    return ClauseIterator::getEmpty();
  }

  ClauseIterator cit = produceClauses(c);
  processQueue();
  return cit;
}

void RenamingOnTheFly::addToQueue(TermList formula, TermList name, Literal* lit, Clause* c)
{
  CALL("RenamingOnTheFly::addToQueue");
  
  _formulas.push(formula);
  _names.push(name);
  _lits.push(lit);
  _clauses.push(c);
}

void RenamingOnTheFly::processQueue()
{
  CALL("RenamingOnTheFly::processQueue");

  while(!_formulas.isEmpty()){
    _formulaIndex->insertFormula(_formulas.pop(), _names.pop(), _lits.pop(), _clauses.pop());
  }

}


bool RenamingOnTheFly::isNamingLit(Literal* lit)
{
  CALL("RenamingOnTheFly::isNamingLit");

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);
  bool lhsIsAtom = AH::getProxy(AH::getHead(lhs)) == Signature::NOT_PROXY;
  bool rhsIsAtom = AH::getProxy(AH::getHead(rhs)) == Signature::NOT_PROXY;
  return lhsIsAtom && rhsIsAtom;
}

TermList RenamingOnTheFly::getFormula(Literal* lit)
{
  CALL("RenamingOnTheFly::getFormula");

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);
  return AH::isBool(lhs) ? rhs : lhs;
}


}
