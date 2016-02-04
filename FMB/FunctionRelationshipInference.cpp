/**
 * @file FunctionRelationshipInference.cpp
 * Implements class FunctionRelationshipInference.
 *
 */

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VString.hpp"
#include "Lib/Timer.hpp"
#include "Lib/IntUnionFind.hpp"
    
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Connective.hpp" 
#include "Kernel/Inference.hpp"
#include "Kernel/MainLoop.hpp"                      
#include "Kernel/Sorts.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/LabelFinder.hpp"
    
#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/CNF.hpp"
#include "Shell/NNF.hpp" 

#include "FunctionRelationshipInference.hpp"

namespace FMB
{
using namespace Shell;

void FunctionRelationshipInference::findFunctionRelationships(ClauseIterator clauses, 
                 Stack<DHSet<unsigned>*>& eq_classes, DHSet<std::pair<unsigned,unsigned>>& cons)
{
  CALL("FunctionRelationshipInference::findFunctionRelationships");

  ClauseList* checkingClauses = getCheckingClauses();

  ClauseIterator cit = pvi(getConcatenatedIterator(clauses,pvi(ClauseList::Iterator(checkingClauses))));

  Problem prb(cit,false);
  Options opt; // default saturation algorithm options

  // because of bad things the time limit is actually taken from env!
  int oldTimeLimit = env.options->timeLimitInDeciseconds();
  env.options->setTimeLimitInSeconds(1);
  //opt.setTimeLimitInSeconds(5);
  opt.setSplitting(false);
  Timer::setTimeLimitEnforcement(false);

  LabelFinder* labelFinder = new LabelFinder();

  //cout << "START" << endl;
  try{
    SaturationAlgorithm* salg = SaturationAlgorithm::createFromOptions(prb,opt);
    salg->setLabelFinder(labelFinder);
    MainLoopResult sres(salg->run());
  }catch (TimeLimitExceededException){
    // This is expected behaviour
  }
  //cout << "DONE" << endl;
  //TODO do we even care about sres?

  Timer::setTimeLimitEnforcement(false);
  env.options->setTimeLimitInDeciseconds(oldTimeLimit);

  Stack<unsigned> foundLabels = labelFinder->getFoundLabels();
  DHSet<std::pair<unsigned,unsigned>> constraints;
  Stack<unsigned>::Iterator it(foundLabels);
  while(it.hasNext()){
    unsigned l = it.next();
    std::pair<unsigned,unsigned> constraint = _labelMap.get(l);
    constraints.insert(constraint);
  }

  // Compute transitive closure badly
/*
  bool closed = false;
  while(!closed){
    DHSet<std::pair<unsigned,unsigned>> newConstraints;
    closed=true;
    DHSet<std::pair<unsigned,unsigned>>::Iterator it1(constraints);
    while(it1.hasNext()){
      std::pair<unsigned,unsigned> con1 = it1.next();
      DHSet<std::pair<unsigned,unsigned>>::Iterator it2(constraints);
      while(it2.hasNext()){
        std::pair<unsigned,unsigned> con2 = it2.next();
        if(con1.second == con2.first){
          std::pair<unsigned,unsigned> con3 = make_pair(con1.first,con2.second);
          if(!constraints.contains(con3) && !newConstraints.contains(con3)){
            newConstraints.insert(con3);
            closed=false;
          }
        }
      }
    }
    constraints.loadFromIterator(DHSet<std::pair<unsigned,unsigned>>::Iterator(newConstraints));
  }
*/
  // Find equalities
  IntUnionFind uf(env.sorts->sorts());
  {
    DHSet<std::pair<unsigned,unsigned>>::Iterator it1(constraints);
    while(it1.hasNext()){
      std::pair<unsigned,unsigned> con1 = it1.next();
      if(con1.first==con1.second) continue;
      DHSet<std::pair<unsigned,unsigned>>::Iterator it2(constraints);
      while(it2.hasNext()){
        std::pair<unsigned,unsigned> con2 = it2.next();
        if(con1.second == con2.first && con1.first == con2.second){
          uf.doUnion(con1.first,con1.second);
        }
      }
    }
  }
  uf.evalComponents();

  //cout << "Equalities:" << endl;
  {
    for(unsigned s=0;s<env.sorts->sorts();s++){
      DHSet<unsigned>* cls = new DHSet<unsigned>();
      for(unsigned t=0;t<env.sorts->sorts();t++){
        if(uf.root(t)==s) cls->insert(t);
      }
      if(cls->size()>1){
       //cout << "= ";
       //DHSet<unsigned>::Iterator it(cls);
       //while(it.hasNext()) cout << it.next() << " ";
       //cout << endl;
       eq_classes.push(cls);   
      }
    }
  }
  //cout << endl; cout << "All constraints:" << endl;
  {
    DHSet<std::pair<unsigned,unsigned>>::Iterator it1(constraints);
    while(it1.hasNext()){ 
      std::pair<unsigned,unsigned> con = it1.next();
      unsigned frst = uf.root(con.first);
      unsigned snd = uf.root(con.second);
      if(frst==snd) continue;
      //cout << env.sorts->sortName(frst) << " >= " << env.sorts->sortName(snd) << endl;
      cons.insert(make_pair(frst,snd));
    }
  }


}

ClauseList* FunctionRelationshipInference::getCheckingClauses()
{
  CALL("FunctionRelationshipInference::getCheckingClauses");

  ClauseList* newClauses = 0;

  unsigned initial_functions = env.signature->functions();
  for(unsigned f=0; f < initial_functions; f++){

    FunctionType* ftype = env.signature->getFunction(f)->fnType();
    unsigned ret_srt = ftype->result();
    unsigned arity = env.signature->functionArity(f);

    bool different_sorted=false;
    for(unsigned i=0;i<arity;i++){
      if(ret_srt != ftype->arg(i)){
        different_sorted=true;
        break;
      }
    }
    if(!different_sorted) continue;

    TermList x(0,false);
    TermList y(1,false);


    // ignore constants
    if(arity==0) continue;

    // For unary functions it's straight forward
    if(arity == 1){
      unsigned arg_srt = ftype->arg(0);
      TermList fx(Term::create1(f,x));
      TermList fy(Term::create1(f,y));
      addClaimForFunction(x,y,fx,fy,f,arg_srt,ret_srt,0,newClauses);
    }
    else{
    // Otherwise we need to existentially quantify over some of the variables
    // First go, let's use each argument as a singleton variable once
    // i.e. f(x,_,_), f(_,x,_), f(_,_,x)
    // and ignore cases like f(x,x,_)
      Formula::VarList* existential = Formula::VarList::empty();
      for(unsigned i=0;i<arity-1;i++){
        existential = new Formula::VarList(i+2,existential);
      }

      for(unsigned i=0;i<arity;i++){
        unsigned arg_srt = ftype->arg(i);

        if(arg_srt == ret_srt) continue; // not interested

        TermList xargs[arity];
        TermList yargs[arity];

        unsigned v=2;
        for(unsigned j=0;j<arity;j++){
          if(i==j){
            xargs[j]=x;
            yargs[j]=y;
          }
          else{
            xargs[j]=TermList(v,false);
            yargs[j]=TermList(v,false);
            v++;
          }
        }
        TermList fx(Term::create(f,arity,xargs));
        TermList fy(Term::create(f,arity,yargs));

        addClaimForFunction(x,y,fx,fy,f,arg_srt,ret_srt,existential,newClauses);
      }
    }

  }
  return newClauses;

}

void FunctionRelationshipInference::addClaimForFunction(TermList x, TermList y, TermList fx, TermList fy,
                                               unsigned fname,
                                               unsigned arg_srt, unsigned ret_srt, Formula::VarList* existential,
                                               ClauseList*& newClauses)
{
    CALL("FunctionRelationshipInference::addClaimForFunction");

    Formula::VarList* xy = new Formula::VarList(0,new Formula::VarList(1));

    Formula* eq_fxfy = new AtomicFormula(Literal::createEquality(true,fx,fy,ret_srt));
    Formula* eq_xy = new AtomicFormula(Literal::createEquality(true,x,y,arg_srt));

    Formula* injective = 
      new QuantifiedFormula(FORALL,xy,0,new BinaryFormula(IMP,eq_fxfy,eq_xy));

    Formula* surjective =
      new QuantifiedFormula(FORALL, new Formula::VarList(1),0,
      new QuantifiedFormula(EXISTS, new Formula::VarList(0),0,
      new AtomicFormula(Literal::createEquality(true,fx,y,ret_srt))));


    if(existential){
      injective  = new QuantifiedFormula(EXISTS, existential, 0, injective);
      surjective = new QuantifiedFormula(EXISTS, existential, 0, surjective);
    }
    // Add names (true/false relates to being injective or not i.e. surjective)
    injective = new BinaryFormula(IMP,injective,getName(ret_srt,arg_srt));
    surjective = new BinaryFormula(IMP,surjective,getName(arg_srt,ret_srt));

    addClaim(injective,newClauses);
    addClaim(surjective,newClauses);
}

void FunctionRelationshipInference::addClaim(Formula* conjecture, ClauseList*& newClauses)
{
    CALL("FunctionRelationshipInference::addClaim");
    
    FormulaUnit* fu = new FormulaUnit(conjecture,
                      new Inference(Inference::INPUT),Unit::CONJECTURE); //TODO create new Inference kind?

    fu = Rectify::rectify(fu);
    fu = NNF::ennf(fu);
    fu = Flattening::flatten(fu);
    fu = Skolem::skolemise(fu);
    fu = Flattening::flatten(fu);

    Stack<Clause*> cls;
    CNF cnf;
    cnf.clausify(fu,cls);

    ClauseList::pushFromIterator(Stack<Clause*>::Iterator(cls),newClauses);
}

// get a name for a formula that captures the relationship that |fromSrt| >= |toSrt|
Formula* FunctionRelationshipInference::getName(unsigned fromSrt, unsigned toSrt)
{
    CALL("FunctionRelationshipInference::getName");

    unsigned label= env.signature->addFreshPredicate(0,"label");
    env.signature->getPredicate(label)->markLabel();

    _labelMap.insert(label,make_pair(fromSrt,toSrt));

    return new AtomicFormula(Literal::create(label,0,true,false,0)); 
}

}
