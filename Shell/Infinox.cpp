/**
 * @file Infinox.cpp
 *
 * @since 28/01/2016 Manchester
 * @author Giles
 */

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VString.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MainLoop.hpp"

#include "Saturation/ProvingHelper.hpp"
#include "Saturation/LabelFinder.hpp"

#include "UIHelper.hpp"
#include "Statistics.hpp"
#include "Skolem.hpp"
#include "Rectify.hpp"
#include "Flattening.hpp"
#include "CNF.hpp"
#include "NNF.hpp"

#include "Infinox.hpp"

namespace Shell{

using namespace Lib;
using namespace Kernel;
using namespace Saturation;

DHMap<unsigned,std::pair<unsigned,unsigned>> Infinox::_labelMap_nonstrict;
DHMap<unsigned,std::pair<unsigned,unsigned>> Infinox::_labelMap_strict;

void Infinox::doCheck(Problem& prb)
{
  CALL("Infinox::doCheck");

  // Add the checking clauses
  addCheckingClauses(prb);

  ProvingHelper::runVampireSaturation(prb, *env.options);

  if(env.statistics->terminationReason == Statistics::REFUTATION){
    cout << ">> Lack of Finite Model Detected" << endl;
  }
  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

}


void Infinox::addCheckingClauses(Problem& prb)
{
  CALL("Infinox::addCheckingClauses");

  UnitList* newClauses = 0;

  // For each unary function f add the conjecture that f is injective and non-surjective
  // i.e.
  // (![X,Y] : (f(X)=f(Y) => X=Y)) & (?[Y]:![X]: f(X) != Y)

  unsigned initial_functions = env.signature->functions();
  for(unsigned f=0; f < initial_functions; f++){

    FunctionType* ftype = env.signature->getFunction(f)->fnType();
    unsigned ret_srt = ftype->result();
    TermList x(0,false);
    TermList y(1,false);

    unsigned arity = env.signature->functionArity(f);

    // ignore constants
    if(arity==0) continue;

    // For unary functions it's straight forward 
    if(arity == 1){
      unsigned arg_srt = ftype->arg(0);
      TermList fx(Term::create1(f,x));
      TermList fy(Term::create1(f,y));
      if(ret_srt == arg_srt) 
        addClaimForSingleSortFunction(x,y,fx,fy,arg_srt,ret_srt,0,newClauses);
      else
        addClaimForMultiSortFunction(x,y,fx,fy,arg_srt,ret_srt,0,newClauses);
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

        if(ret_srt == arg_srt) 
          addClaimForSingleSortFunction(x,y,fx,fy,arg_srt,ret_srt,0,newClauses);
        else
          addClaimForMultiSortFunction(x,y,fx,fy,arg_srt,ret_srt,0,newClauses);
      }
    }

  }
  prb.addUnits(newClauses);
}
    


void Infinox::addClaimForSingleSortFunction(TermList x, TermList y, TermList fx, TermList fy, 
                                               unsigned arg_srt, unsigned ret_srt, Formula::VarList* existential, 
                                               UnitList*& newClauses)
{
    CALL("Infinox::addClaimForSingleSortFunction");

    Formula::VarList* xy = new Formula::VarList(0,new Formula::VarList(1));

    Formula* eq_fxfy = new AtomicFormula(Literal::createEquality(true,fx,fy,ret_srt));
    Formula* eq_xy = new AtomicFormula(Literal::createEquality(true,x,y,arg_srt));

    Formula* injective =  
      new QuantifiedFormula(FORALL,xy,0,new BinaryFormula(IMP,eq_fxfy,eq_xy));

    Formula* nonsurjective =
      new QuantifiedFormula(EXISTS, new Formula::VarList(1),0,
      new QuantifiedFormula(FORALL, new Formula::VarList(0),0,
      new AtomicFormula(Literal::createEquality(false,fx,y,ret_srt))));

    
    Formula* conjecture = 
      new JunctionFormula(AND,new FormulaList(injective,new FormulaList(nonsurjective)));

    if(existential){
      conjecture = new QuantifiedFormula(EXISTS, existential, 0, conjecture);
    }

    Formula* negated_conjecture = new NegatedFormula(conjecture);

    FormulaUnit* conjecture_fu = new FormulaUnit(conjecture,
                                 new Inference(Inference::INFINOX_CLAIM),Unit::CONJECTURE);
    FormulaUnit* fu = new FormulaUnit(negated_conjecture,
                      new Inference1(Inference::NEGATED_CONJECTURE,conjecture_fu),
                      Unit::CONJECTURE); 

    // Important, need to rectify
    fu = Rectify::rectify(fu);
    fu = NNF::ennf(fu);
    fu = Flattening::flatten(fu);
    fu = Skolem::skolemise(fu);
    fu = Flattening::flatten(fu);

    Stack<Clause*> cls;
    CNF cnf;
    cnf.clausify(fu,cls);
    
    UnitList::pushFromIterator(Stack<Clause*>::Iterator(cls),newClauses);
} 

void Infinox::addClaimForMultiSortFunction(TermList x, TermList y, TermList fx, TermList fy,
                                               unsigned arg_srt, unsigned ret_srt, Formula::VarList* existential,
                                               UnitList*& newClauses)
{
    CALL("Infinox::addClaimForMultiSortFunction");

    Formula::VarList* xy = new Formula::VarList(0,new Formula::VarList(1));

    Formula* eq_fxfy = new AtomicFormula(Literal::createEquality(true,fx,fy,ret_srt));
    Formula* eq_xy = new AtomicFormula(Literal::createEquality(true,x,y,arg_srt));

    Formula* injective =
      new QuantifiedFormula(FORALL,xy,0,new BinaryFormula(IMP,eq_fxfy,eq_xy));

    Formula* surjective =
      new QuantifiedFormula(FORALL, new Formula::VarList(1),0,
      new QuantifiedFormula(EXISTS, new Formula::VarList(0),0,
      new AtomicFormula(Literal::createEquality(true,fx,y,ret_srt))));

    Formula* ing_and_nons = new JunctionFormula(AND,
                            new FormulaList(injective, new FormulaList(new NegatedFormula(surjective))));
    Formula* sur_and_noni = new JunctionFormula(AND,
                            new FormulaList(surjective, new FormulaList(new NegatedFormula(injective))));

    if(existential){
      injective  = new QuantifiedFormula(EXISTS, existential, 0, injective);
      surjective = new QuantifiedFormula(EXISTS, existential, 0, surjective);
      ing_and_nons = new QuantifiedFormula(EXISTS, existential, 0, ing_and_nons);
      sur_and_noni = new QuantifiedFormula(EXISTS, existential, 0, sur_and_noni);
    }
    // Add names (true/false relates to being injective or not i.e. surjective)
    injective    = new BinaryFormula(IMP,injective,getName(ret_srt,arg_srt,false));
    surjective   = new BinaryFormula(IMP,surjective,getName(arg_srt,ret_srt,false));
    ing_and_nons = new BinaryFormula(IMP,ing_and_nons,getName(ret_srt,arg_srt,true));
    sur_and_noni = new BinaryFormula(IMP,sur_and_noni,getName(arg_srt,ret_srt,true));

    addClaim(injective,newClauses);
    addClaim(surjective,newClauses);
    addClaim(ing_and_nons,newClauses);
    addClaim(sur_and_noni,newClauses);

}

void Infinox::addClaim(Formula* conjecture, UnitList*& newClauses)
{
    CALL("Infinox::addClaim");

    FormulaUnit* fu = new FormulaUnit(conjecture,
                      new Inference(Inference::INFINOX_CLAIM),Unit::CONJECTURE); 

    fu = Rectify::rectify(fu);
    fu = NNF::ennf(fu);
    fu = Flattening::flatten(fu);
    fu = Skolem::skolemise(fu);
    fu = Flattening::flatten(fu);

    Stack<Clause*> cls;
    CNF cnf;
    cnf.clausify(fu,cls);

    UnitList::pushFromIterator(Stack<Clause*>::Iterator(cls),newClauses);
}

// get a name for a formula that captures the relationship that |fromSrt| >= |toSrt|
Formula* Infinox::getName(unsigned fromSrt, unsigned toSrt, bool strict)
{
    CALL("Infinox::getName");

    vstring name = "label_"+Lib::Int::toString(fromSrt)+"_"+Lib::Int::toString(toSrt)+"_";
    if(strict) name += "s";
    unsigned label= env.signature->addFreshPredicate(0,name.c_str());
    env.signature->getPredicate(label)->markLabel();

    if(strict)
      _labelMap_strict.insert(label,make_pair(fromSrt,toSrt));
    else
      _labelMap_nonstrict.insert(label,make_pair(fromSrt,toSrt));

    return new AtomicFormula(Literal::create(label,0,true,false,0));
}

void Infinox::checkLabels(LabelFinder* labelFinder)
{
  CALL("Infinox::checkLabels");

  Stack<unsigned> foundLabels = labelFinder->getFoundLabels();
  DHSet<std::pair<unsigned,unsigned>> single_constraints;
  DHSet<std::pair<unsigned,unsigned>> strict_constraints;

  // need to seperate the constraints for producing a refutation
  DHMap<std::pair<unsigned,unsigned>,Clause*> nonstrict_clauses;
  DHMap<std::pair<unsigned,unsigned>,Clause*> strict_clauses;

  Stack<unsigned>::Iterator it(foundLabels);
  while(it.hasNext()){
    unsigned l = it.next();
    std::pair<unsigned,unsigned> constraint;
    if(_labelMap_strict.find(l,constraint)){
      single_constraints.insert(constraint);
      strict_constraints.insert(constraint);
      strict_clauses.insert(constraint,labelFinder->getLabelClause(l));
    }
    if(_labelMap_nonstrict.find(l,constraint)){
      single_constraints.insert(constraint);
      nonstrict_clauses.insert(constraint,labelFinder->getLabelClause(l));
    }
  }

  // if there are no strict constraints then there can be no infinite domain
  if(strict_constraints.isEmpty()){
    //cout << "no strict constraints" << endl;
    return;
  }

  //cout << "There are " << strict_constraints.size() << " strict constraints" << endl;

  // now transitively close the union of constraints
  // this is an inefficient way of finding cycles, but I expect the graphs to be very small

  DHSet<std::pair<unsigned,unsigned>> constraints;
  constraints.loadFromIterator(DHSet<std::pair<unsigned,unsigned>>::Iterator(single_constraints));

  // This is even a bad way of computing transitive closure!
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


  // if we can reach the start of a strict constraint from the end we have a
  // cycle containing a strict constraint
  DHSet<std::pair<unsigned,unsigned>>::Iterator strict_it(strict_constraints);
  while(strict_it.hasNext()){
    std::pair<unsigned,unsigned> strictc = strict_it.next();
    std::pair<unsigned,unsigned> rev = make_pair(strictc.second,strictc.first);
    if(constraints.contains(rev)){
      //cout << "FOUND CYCLE" << endl;

      // construct a clause that captures this cycle
      UnitList* prems = 0;
      UnitList::push(strict_clauses.get(strictc),prems);

      unsigned end = strictc.first;
      unsigned start = strictc.second;
      // which means we need to find the cycle!
      // we step out from the end of the strict constraint
      // again.... I haven't thought about efficiency!
      while(end!=start){
        // search for a constraint from start to x such that there is a path from x to end 
        DHSet<std::pair<unsigned,unsigned>>::Iterator singles(single_constraints); 
        unsigned mid;
        while(singles.hasNext()){
          std::pair<unsigned,unsigned> single = singles.next();
          if(single.first == start){
            std::pair<unsigned,unsigned> jump = make_pair(single.second,end);
            if(constraints.contains(jump)){
              mid = single.second; 
              break;
            }
          }
        } 
        std::pair<unsigned,unsigned> next = make_pair(start,mid);
        Clause* cl;
        if(!nonstrict_clauses.find(next,cl)){
          ALWAYS(strict_clauses.find(next,cl));
        }
        UnitList::push(cl,prems);
        start=mid;
      }
     
      Inference* inf = new InferenceMany(Inference::INFINOX_SORT_CYCLE,prems); 
      Clause* ref = Clause::fromIterator(LiteralIterator::getEmpty(),Unit::CONJECTURE,inf);

      MainLoopResult result(Statistics::REFUTATION, ref);
      result.updateStatistics();
      return;
    }
  }

}

}
