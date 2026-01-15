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
 * @file FunctionRelationshipInference.cpp
 * Implements class FunctionRelationshipInference.
 *
 */

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"
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
#include "Kernel/OperatorType.hpp"

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
using namespace std;
using namespace Shell;

void FunctionRelationshipInference::findFunctionRelationships(ClauseIterator clauses,
                 DHSet<std::pair<unsigned,unsigned>>& nonstrict_cons,
                 DHSet<std::pair<unsigned,unsigned>>& strict_cons)
{
  bool print = env.options->showFMBsortInfo();

  ClauseList* checkingClauses = getCheckingClauses();

  ClauseIterator cit = pvi(concatIters(clauses,ClauseList::Iterator(checkingClauses)));

  Problem prb(cit,false);
  Options opt; // default saturation algorithm options

  Problem* inputProblem = env.getMainProblem();
  env.setMainProblem(&prb);
  unsigned useTimeLimit = env.options->fmbDetectSortBoundsTimeLimit();
  opt.setSplitting(false);

  LabelFinder* labelFinder = new LabelFinder();

  try{
    SaturationAlgorithm* salg = SaturationAlgorithm::createFromOptions(prb,opt);
    salg->setLabelFinder(labelFinder);
    salg->setSoftTimeLimit(useTimeLimit);
    salg->run();
  }catch (TimeLimitExceededException&){
    // This is expected behaviour
  }

  env.setMainProblem(inputProblem);

  Stack<unsigned> foundLabels = labelFinder->getFoundLabels();

  if(foundLabels.size()>0 && print){ cout << "Found constraints:" << endl; }

  DHSet<std::pair<unsigned,unsigned>> nonstrict_constraints;
  DHSet<std::pair<unsigned,unsigned>> strict_constraints;
  Stack<unsigned>::Iterator it(foundLabels);
  while(it.hasNext()){
    unsigned l = it.next();
    std::pair<unsigned,unsigned> constraint;
    if(_labelMap_nonstrict.find(l,constraint)){
      nonstrict_constraints.insert(constraint);
      if(print) cout << constraint.first << " >= " << constraint.second << endl;
    }
    else{
      ALWAYS(_labelMap_strict.find(l,constraint));
      strict_constraints.insert(constraint);
      if(print) cout << constraint.first << " > " << constraint.second << endl;
    }
  }

  // Normalise constraints
  unsigned constraint_count = 0;
  {
    DHSet<std::pair<unsigned,unsigned>>::Iterator it1(nonstrict_constraints);
    while(it1.hasNext()){ 
      constraint_count++;
      std::pair<unsigned,unsigned> con = it1.next();
/*
      unsigned frst = uf.root(con.first);
      unsigned snd = uf.root(con.second);
      if(frst==snd) continue;
      nonstrict_cons.insert(make_pair(frst,snd));
*/
      nonstrict_cons.insert(con);
    }
  }
  if(print){
    cout << "There were " << constraint_count << " non-strict constraints between sorts" << endl;
  }
  constraint_count = 0;
  {
    DHSet<std::pair<unsigned,unsigned>>::Iterator it1(strict_constraints);
    while(it1.hasNext()){
      constraint_count++;
      std::pair<unsigned,unsigned> con = it1.next();
/*
      unsigned frst = uf.root(con.first);
      unsigned snd = uf.root(con.second);
      if(frst==snd) continue;
      strict_cons.insert(make_pair(frst,snd));
*/
      ASS(con.first != con.second);
      if(con.first == con.second){
        // should not happen by construction (constraints must be between different sorts)
        continue;
      }
      strict_cons.insert(con);
    }
  }
  if(print){
    cout << "There were " << constraint_count << " strict constraints between sorts" << endl;
  }

}

ClauseList* FunctionRelationshipInference::getCheckingClauses()
{
  ClauseList* newClauses = 0;

  unsigned initial_functions = env.signature->functions();
  for(unsigned f=0; f < initial_functions; f++){

    OperatorType* ftype = env.signature->getFunction(f)->fnType();
    TermList ret_srt = ftype->result();
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
      TermList arg_srt = ftype->arg(0);
      TermList fx(Term::create1(f,x));
      TermList fy(Term::create1(f,y));
      addClaimForFunction(x,y,fx,fy,f,arg_srt,ret_srt,0,newClauses);
    }
    else{
    // Otherwise we need to existentially quantify over some of the variables
    // First go, let's use each argument as a singleton variable once
    // i.e. f(x,_,_), f(_,x,_), f(_,_,x)
    // and ignore cases like f(x,x,_)
      VList* existential = VList::empty();
      for(unsigned i=0;i<arity-1;i++){
        VList::push(i+2,existential);
      }

      for(unsigned i=0;i<arity;i++){
        TermList arg_srt = ftype->arg(i);

        if(arg_srt == ret_srt) continue; // not interested

        Stack<TermList> xargs(arity);
        Stack<TermList> yargs(arity);

        unsigned v=2;
        for(unsigned j=0;j<arity;j++){
          if(i==j){
            xargs.push(x);
            yargs.push(y);
          }
          else{
            xargs.push(TermList(v,false));
            yargs.push(TermList(v,false));
            v++;
          }
        }
        TermList fx(Term::create(f,arity,xargs.begin()));
        TermList fy(Term::create(f,arity,yargs.begin()));

        addClaimForFunction(x,y,fx,fy,f,arg_srt,ret_srt,existential,newClauses);
      }
    }

  }
  return newClauses;

}

void FunctionRelationshipInference::addClaimForFunction(TermList x, TermList y, TermList fx, TermList fy,
                                               unsigned fname,
                                               TermList arg_srt, TermList ret_srt, VList* existential,
                                               ClauseList*& newClauses)
{
    // Build VSList for variables 0,1 with arg_srt
    VSList* xySorted = VSList::empty();
    VSList::push(std::make_pair(1, arg_srt), xySorted);
    VSList::push(std::make_pair(0, arg_srt), xySorted);

    Formula* eq_fxfy = new AtomicFormula(Literal::createEquality(true,fx,fy,ret_srt));
    Formula* eq_xy = new AtomicFormula(Literal::createEquality(true,x,y,arg_srt));

    Formula* injective =
      new QuantifiedFormula(FORALL, xySorted, new BinaryFormula(IMP,eq_fxfy,eq_xy));

    // For surjective: variable 1 has ret_srt, variable 0 has arg_srt
    VSList* ySorted = VSList::singleton(std::make_pair(1, ret_srt));
    VSList* xSorted = VSList::singleton(std::make_pair(0, arg_srt));

    Formula* surjective =
      new QuantifiedFormula(FORALL, ySorted,
      new QuantifiedFormula(EXISTS, xSorted,
      new AtomicFormula(Literal::createEquality(true,fx,y,ret_srt))));

    Formula* ing_and_nons = new JunctionFormula(AND,
                            new FormulaList(injective, new FormulaList(new NegatedFormula(surjective))));
    Formula* sur_and_noni = new JunctionFormula(AND,
                            new FormulaList(surjective, new FormulaList(new NegatedFormula(injective))));

    if(existential){
      // Convert existential VList* to VSList* with appropriate sorts
      // Need to determine sort from context - these are function quantifiers
      VSList* existentialSorted = VSList::empty();
      VList::Iterator vit(existential);
      while (vit.hasNext()) {
        unsigned var = vit.next();
        // These are function-typed variables, get their sort from the outer context
        // For this case, they should have the function sort
        TermList varSort;
        // The existential variables quantify over functions, so we need to get their sorts
        // This is complex - for now, we try to infer from one of the formulas
        if (!SortHelper::tryGetVariableSort(var, injective, varSort)) {
          // Fallback: use default sort (this shouldn't happen in well-formed formulas)
          varSort = AtomicSort::defaultSort();
        }
        VSList::push(std::make_pair(var, varSort), existentialSorted);
      }
      injective  = new QuantifiedFormula(EXISTS, existentialSorted, injective);
      surjective = new QuantifiedFormula(EXISTS, existentialSorted, surjective);
      ing_and_nons = new QuantifiedFormula(EXISTS, existentialSorted, ing_and_nons);
      sur_and_noni = new QuantifiedFormula(EXISTS, existentialSorted, sur_and_noni);
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

void FunctionRelationshipInference::addClaim(Formula* conjecture, ClauseList*& newClauses)
{
    FormulaUnit* fu = new FormulaUnit(conjecture,
                      FromInput(UnitInputType::CONJECTURE)); //TODO create new Inference kind?

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
Formula* FunctionRelationshipInference::getName(TermList fromSrt, TermList toSrt, bool strict)
{
    unsigned label= env.signature->addFreshPredicate(0,"label");
    env.signature->getPredicate(label)->markLabel();

    unsigned fsT = fromSrt.term()->functor();
    unsigned tsT = toSrt.term()->functor();

    if(strict)
      _labelMap_strict.insert(label,make_pair(fsT, tsT));
    else
      _labelMap_nonstrict.insert(label,make_pair(fsT,tsT));

    return new AtomicFormula(Literal::create(label, /* polarity */ true, {})); 
}

}
