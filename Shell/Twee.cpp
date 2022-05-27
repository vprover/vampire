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
 * Implements Twee's goal-directed preprocessing technique for equational reasoning.
 * To quote "Twee: An Equational Theorem Prover" (Smallbone, 2021):
 *
 * ----- 
 * Twee’s frontend can optionally transform the problem to make the prover more goal-directed.
 * The transformation is simple, but strange.
 * For every function term f(...) appearing in the goal, we introduce a fresh constant symbol a and add the axiom f(...) = a
 * For example, if the goal is f(g(a), b) = h(c) we add the axioms f(g(a), b) = sF0, g(a) = sF1, and h(c) = sF2.
 * Simplification will rewrite the first axiom to f(sF1, b) = sF0 and the goal to sF0 = sF2.
 * -----
 * 
 * We take an intepretation of this for our purposes, NB:
 *  - any ground term, in a clause derived from the conjecture, is transformed in this way
 *  - introduced definitions are considered derived from the conjecture
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/Renaming.hpp"

#include "Twee.hpp"

using Kernel::Clause;
using Kernel::Literal;
using Kernel::Problem;
using Kernel::Unit;
using Kernel::UnitList;

/*
 * The actual worker for the twee trick.
 # - evaluates conjucture literals bottom up (as orchestrated by Twee::apply)
 # - and eagerly introduces new definitions for its subterms
 # - already encountered subterms reuse older definitions
 */
class Definizator : public BottomUpTermTransformer {

  bool _groundOnly;
  Renaming _renaming;

  public: // so that Twee::apply can directly access
    // all the new definitions (as clauses) introduced along the way
    UnitList* newUnits;

    // accumlating the defining units as premises for the current "rewrite"
    // (reset responsibility is with Twee::apply)
    UnitList* premises;

    // for each relevant term, cache the introduced symbol and the corresponding definition
    DHMap<Term*,std::pair<unsigned,Unit*>> _cache;  

    Definizator(bool groundOnly) : _groundOnly(groundOnly), newUnits(UnitList::empty()) {}

  protected:
    TermList transformSubterm(TermList trm) override {
        cout << "tf: " << trm.toString() << endl;
        if (trm.isVar()) return trm;
        Term* t = trm.term();
        if (t->isSort() || t->arity() == 0 || (!t->ground() && _groundOnly)) return trm;

        if (!t->ground()) {
          // as we go bottom up, t is never too big (well, it could be wide, but at least not deep)          
          _renaming.reset();
          _renaming.normalizeVariables(t);
          Term* key = _renaming.apply(t);

          // TODO: care about sorts?
        }
        
        std::pair<unsigned,Unit*> symAndDef; 
        TermList res;
        if (!_cache.find(t,symAndDef)) {
          TermList sort = SortHelper::getResultSort(t);
          OperatorType *type = OperatorType::getConstantsType(sort);
          symAndDef.first = env.signature->addFreshFunction(0, "sF");
          env.signature->getFunction(symAndDef.first)->setType(type);
          TermList constant = TermList(Term::createConstant(symAndDef.first));
          Literal* equation = Literal::createEquality(true, TermList(t), constant, sort);
          Inference inference(NonspecificInference0(UnitInputType::AXIOM,InferenceRule::FUNCTION_DEFINITION));      
          Clause *clause = new (1) Clause(1, inference);
          clause->literals()[0] = equation;

          // record globally
          UnitList::push(clause,newUnits);          
          if(env.options->showPreprocessing()) {
              env.out() << "[PP] twee: " << clause->toString() << std::endl;
          }

          symAndDef.second = clause;
          _cache.insert(t,symAndDef);
          res = constant;
        } else {
          res = TermList(Term::createConstant(symAndDef.first));          
        }
        // record as a new premise
        UnitList::push(symAndDef.second,premises);
        cout << "r: " << res.toString() << endl;
        return res;
    }
};

void Shell::Twee::apply(Problem &prb, bool groundOnly)
{
  CALL("Twee::apply");

  Stack<Literal*> newLits;
  Definizator df(groundOnly);

  UnitList::RefIterator uit(prb.units());
  while (uit.hasNext()) {
    Unit* &u = uit.next();
    if (!u->derivedFromGoal())
      continue;

    ASS(u->isClause());
    Clause* c = u->asClause();

    df.premises = UnitList::empty(); // will get filled as we traverse and rewrite

    newLits.reset();
    for (unsigned i = 0; i < c->size(); i++) {
      Literal* l = c->literals()[i];
      cout << "L: " << l->toString() << endl;
      Literal* nl = df.transform(l);
      cout << "NL: " << nl->toString() << endl;
      newLits.push(nl);
    }
    if (df.premises) {
      UnitList::push(c,df.premises);
      Clause* nc = Clause::fromStack(newLits,
        NonspecificInferenceMany(InferenceRule::DEFINITION_FOLDING,df.premises));
      u = nc; // replace the original in the Problem's list
    }
  }
  if (df.newUnits) {
    prb.addUnits(df.newUnits);
    prb.reportEqualityAdded(false);
  }
}
