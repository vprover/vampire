/**
 * @file TheoryInstAndSimp.cpp
 * Implements class TheoryInstAndSimp.
 */

#if VZ3

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TheoryFlattening.hpp"

#include "SAT/SATLiteral.hpp"
#include "SAT/SAT2FO.hpp"
#include "SAT/Z3Interfacing.hpp"

#include "TheoryInstAndSimp.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;
using namespace SAT;


/**
 * Apply theory flattening to cl and return the flattened clause. The theoryLits *of the flattened clause* will be inserted into the stack
 **/
Clause* TheoryInstAndSimp::selectTheoryLiterals(Clause* cl, Stack<Literal*>& theoryLits)
{
  CALL("TheoryInstAndSimp::selectTheoryLiterals");

  static TheoryFlattening flattener;

  Clause* flattened = flattener.apply(cl);

  Clause::Iterator it(*flattened);
  while(it.hasNext()){
    Literal* lit = it.next();
    bool interpreted = theory->isInterpretedPredicate(lit);
    if(lit->isEquality() && !lit->isTwoVarEquality()) {  // two var equalities are correctly identified as interpreted and should be added
      interpreted=false; // for the other equalities, we make sure they don't contain uninterpreted stuff (after flattenning)
      for(TermList* ts = lit->args(); ts->isNonEmpty(); ts = ts->next()){
        if(ts->isTerm() && env.signature->getFunction(ts->term()->functor())->interpreted()){
          interpreted=true;
        }
      }
    }
    if(interpreted){
      theoryLits.push(lit);
    } 
  }

  return flattened;
}

Term* getFreshConstant(unsigned index, unsigned srt)
{
  CALL("TheoryInstAndSimp::getFreshConstant");
  static Stack<Stack<Term*>*> constants;

  while(srt+1 > constants.length()){
    Stack<Term*>* stack = new Stack<Term*>;
    constants.push(stack);
  }
  Stack<Term*>* sortedConstants = constants[srt]; 
  while(index+1 > sortedConstants->length()){
    unsigned sym = env.signature->addFreshFunction(0,"$$inst");
    FunctionType* type = new FunctionType(srt);
    env.signature->getFunction(sym)->setType(type);
    Term* fresh = Term::createConstant(sym);
    sortedConstants->push(fresh);
  }
  return (*sortedConstants)[index];
}

VirtualIterator<Solution> TheoryInstAndSimp::getSolutions(Stack<Literal*>& theoryLiterals){
  CALL("TheoryInstAndSimp::getSolutions");

  // Currently we just get the single solution from Z3

  // We use a new SMT solver
  SAT2FO naming;
  Z3Interfacing solver(*env.options,naming);

  // Firstly, we need to consistently replace variables by constants (i.e. Skolemize)
  // Secondly, we take the complement of each literal and consider the conjunction
  // This subst is for the consistent replacement
  Substitution subst;

  Stack<Literal*>::Iterator it(theoryLiterals);
  Stack<unsigned> vars;
  while(it.hasNext()){
    // get the complementary of the literal
    Literal* lit = Literal::complementaryLiteral(it.next());
    // replace variables consistently by fresh constants 
    DHMap<unsigned,unsigned > srtMap;
    SortHelper::collectVariableSorts(lit,srtMap); 
    TermVarIterator vit(lit);
    unsigned used = 0;
    while(vit.hasNext()){
      unsigned var = vit.next();
      unsigned sort = srtMap.get(var);
      TermList fc;
      if(!subst.findBinding(var,fc)){
        Term* fc = getFreshConstant(used++,sort);
        subst.bind(var,fc);
        vars.push(var);
      }
    }
    lit = SubstHelper::apply(lit,subst);

    // register the lit in naming in such a way that the solver will pick it up!
    SATLiteral slit = naming.toSAT(lit);

    // now add the SAT representation
    static SATLiteralStack satLits;
    satLits.reset();
    satLits.push(slit);
    SATClause* sc = SATClause::fromStack(satLits); 
    //clause->setInference(new FOConversionInference(cl));
    solver.addClause(sc);
  }

  // now we can call the solver
  SATSolver::Status status = solver.solve(UINT_MAX);

  if(status == SATSolver::UNSATISFIABLE){
    return pvi(getSingletonIterator(Solution(false)));
  }
  else if(status == SATSolver::SATISFIABLE){
    Solution sol = Solution(true);
    Stack<unsigned>::Iterator vit(vars);
    while(vit.hasNext()){
      unsigned v = vit.next();
      Term* t = subst.apply(v).term();
      t = solver.evaluateInModel(t);
      cout << "bind " << v << " to " << t->toString() << endl;
      sol.subst.bind(v,t);
    }
    cout << "solution with " << sol.subst.toString() << endl;
    return pvi(getSingletonIterator(sol));
  }

  // SMT solving was incomplete
  return VirtualIterator<Solution>::getEmpty(); 

}


struct InstanceFn
{
  InstanceFn(Clause* cl) : _cl(cl) {}
  
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(Solution sol)
  {
    CALL("TheoryInstAndSimp::InstanceFn::operator()");

    // We should be deleting cl, but we don't support that for now
    if(!sol.status){
      return 0;
    }
    cout << "Instantiate " << _cl->toString() << endl;
    cout << "with " << sol.subst.toString() << endl;
    Inference* inf = new Inference1(Inference::INSTANTIATION,_cl);
    Clause* res = new(_cl->length()) Clause(_cl->length(),_cl->inputType(),inf);
    for(unsigned i=0;i<_cl->length();i++){
      (*res)[i] = SubstHelper::apply((*_cl)[i],sol.subst);
    }
    return res;
  }

private:
  Clause* _cl;
};

ClauseIterator TheoryInstAndSimp::generateClauses(Clause* premise)
{
  CALL("TheoryInstAndSimp::generateClauses");

  //Limits* limits = _salg->getLimits();

  static Stack<Literal*> theoryLiterals;
  theoryLiterals.reset();

  Clause* flattened = selectTheoryLiterals(premise,theoryLiterals);

  if(theoryLiterals.isEmpty()){
     return ClauseIterator::getEmpty();
  }

  auto it1 = getSolutions(theoryLiterals);

  auto it2 = getMappingIterator(it1,InstanceFn(flattened));

  // filter out only non-zero results
  auto it3 = getFilteredIterator(it2, NonzeroFn());

  // measure time of the overall processing
  auto it4 = getTimeCountedIterator(it3,TC_THEORY_INST_SIMP);

  return pvi(it4);
}

}

#endif
