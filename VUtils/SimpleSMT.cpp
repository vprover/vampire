/**
 * @file SimpleSMT.cpp
 * Implements class SimpleSMT.
 */

#include <map>

#include "Debug/Tracer.hpp"
#include "Forwards.hpp"
#include "VUtils/SimpleSMT.hpp"

#include "DP/SimpleCongruenceClosure.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "SAT/SATLiteral.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/TWLSolver.hpp"
#include "SAT/Preprocess.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Options.hpp"
#include "PreprocessingEvaluator.hpp"

namespace VUtils
{

using namespace Shell;
using namespace Kernel;
using namespace SAT;


int SimpleSMT::foToSAT(Literal *l, MyMap *map)
{
    
    NOT_IMPLEMENTED;
//    int value;
//    //if the literal is already in the map, then return the value, otherwise insert it
//  
//    if(map->find(l, value ))
//        return value;
//    else
//        {
//        map->insert(l, map->size()+1);
//        return map->size();
//        }
}

SAT::SATLiteral SimpleSMT::litTOSAT(Literal *l, TwoWayMap& map)
{
     CALL("SimpleSMT::litToSAT");
  unsigned var = map.get(Literal::positiveLiteral(l));
  ASS_G(var,0);
  return SATLiteral(var, l->isPositive());

//  int num=0;
//  
//  num=map->get(l);
//  if(num!=0 )
//  {
//      return SATLiteral(abs(num), num>0?1:0);
//  }
//
//  
//  //one can use positiveLiteral(l) - nicer way of doing the same thing
//  if(l->isPositive())
//  {
//      //take good care at the number you insert!!! - not final 
//      map->assign(l, num);
//      //map->add(l, map->size()+1);
//      //instead of num it should be map->getMax - or getSize()
//      return SATLiteral(num, 1);
//  }
  
  
//  Literal* posLit=Literal::complementaryLiteral(l);
//  if(num=map->get(posLit)) {
//    map->assign(l, -num);
//    return SATLiteral(num, 0);
//  }
// 
//  //map.getSize()
//  num= 0;//map->size()+1;
//
//  map->assign(posLit, num);
//  map->assign(l, -num);
//  
//  return SAT::SATLiteral(num, 0);
}

int SimpleSMT::perform(int argc, char** argv)
{
  CALL("SimpleSMT::perform");

  string fname;
  if(argc<3) {
      fname="";
  }
  else {
        fname = argv[2];
  }

  
  if(fname.substr(fname.size()-4)== ".smt")
      env.options->setInputSyntax(Options::IS_SMTLIB);
  cout << "Now we should be solving "<<fname<<endl;
  
  env.options->setInputFile(fname);
  Problem* prb=UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  Shell::Preprocess prepro(*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(*prb);
  
  
  //keeps a map between the literals found in the clauses and the SAT literals
  TwoWayMap map;
   
  SATClauseList *clauses = 0;

  ClauseIterator clite = prb->clauseIterator();
  
  while(clite.hasNext())
  {
      Clause* cl = clite.next();
      
      //iterate over the set of literals in the clause
      
      Clause::Iterator ite(*cl);
      
      //create a satLiteral stack, needed for the creation of SATClause
      SAT::SATLiteralStack *satLitStack = new SAT::SATLiteralStack ();
      
      //as long as you have literals, check if they are in the map, if they are 
      //then do nothing otherwise add them to the map.
      
      while(ite.hasNext())
      {
          
          Literal *literal=ite.next();
          
          //check if it is already in the map and/or add it 
          
          SAT::SATLiteral slit(litTOSAT(literal, map)); 
          //how to create a sat literal? 
          satLitStack->push(slit);
          
          
      }
      
      
      unsigned clen=cl->length();
      SAT::SATClause *clause;

      //create a clause from stack of literals
      clause= SAT::SATClause::fromStack(*satLitStack);
      //add the clause to the list of problem clauses
      //clauses->addLast(clause);
      clause=SAT::Preprocess::removeDuplicateLiterals(clause);
      if(clause==0)
          ;
      else
      {
        SATClauseList::push(clause, clauses);
        //cout<<clause->toString()<<endl;
      }
  }
  
  //clauses - should contain the list of all cluases appearing in the problem
  SAT::SATClauseIterator clauseIterator = pvi(SATClauseList::Iterator(clauses)); 
  
  Shell::Options opt;

  ScopedPtr<SATSolver> solver( new TWLSolver(opt, false)); 
  
  solver->ensureVarCnt(map.getNumberUpperBound()+1);
  solver->addClauses(clauseIterator,false);
  
  //better switch 
  
  LiteralStack litAsgn;
  
  switch(solver->getStatus())
  {
  case SAT::SATSolver::SATISFIABLE :
  
      cout<<"Sat\n";
      
      Literal *literal;
      //for each positive literal appearing in the map
      for(unsigned i=1; i<= map.getNumberUpperBound() ; i++) {
        literal = map.obj(i);
        ASS(literal->isPositive());
          
        switch(solver->getAssignment(i))
        {
        case SAT::SATSolver::TRUE : 
            break;
        
        case SAT::SATSolver::FALSE :
            literal = Literal::complementaryLiteral(literal);
            break;
        case SAT::SATSolver::DONT_CARE:
            continue;
        case SAT::SATSolver::NOT_KNOWN:
            ASSERTION_VIOLATION;
        }
        litAsgn.push(literal);
        //cout<<(*literal)<<endl;
      }
      break;
  case SAT::SATSolver::UNSATISFIABLE: 
      cout<<"Unsat\n";
      return 0;
      break;
  default: 
      cout<<"Unknown: "<<solver->getStatus()<<"\n";
  break;
  }
  
  DP::SimpleCongruenceClosure cc;
  cc.addLiterals(pvi(LiteralStack::Iterator(litAsgn)));
  DP::DecisionProcedure::Status status = cc.getStatus();
  cout << "dec proc: " << (status==DP::DecisionProcedure::SATISFIABLE ? "SAT" : "UNSAT")<<endl;
  //if unsatisfiable, get the unsat subset and create a clause out of it and run SAT again;
  if(status == DP::DecisionProcedure::UNSATISFIABLE)
  {
      LiteralStack litStack;
      cc.getUnsatisfiableSubset(litStack);
      SAT::SATClause *cl;
      LiteralStack::Iterator iter(litStack); 
      
      SAT::SATLiteralStack stack;
      //as long as you have literals, check if they are in the map, if they are 
      //then do nothing otherwise add them to the map.
      
      while(iter.hasNext())
      {
          
          Literal *literal=iter.next();
          
          //check if it is already in the map and/or add it 
          
          SAT::SATLiteral slit(litTOSAT(literal, map)); 
          //how to create a sat literal? 
          stack.push(slit);
          
          
      }
      
      SAT::SATClause *new_clause;

      //create a clause from stack of literals
      new_clause= SAT::SATClause::fromStack(stack);
      solver->addClauses(pvi(getSingletonIterator(new_clause)));
     
  }
  
  return 0;
}

}


////if(literal->polarity())
//                        cout<<literal->predicateName()<<TRUE<<endl;
//                else cout<<literal->predicateName()<<FALSE<<endl;