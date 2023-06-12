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
 * There are a few minor differences in our take on the idea:
 * - the defitions are introduced bottum up and cached (so each subterm is only defined once)
 * - the bottom-up approach also means the rules and the conjecture "are born" already inter-reduced
 * - optionally, also non-ground subterms are considered, but never in the case this would not lead 
 *  to a demodulator under the standard (constant weight) KBO: 
 *  in particular linear terms such as f(X,Y,Z) are not defined
 * - the implementation should work for polymorphic inputs
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/Renaming.hpp"

#include "TweeGoalTransformation.hpp"

using Kernel::Clause;
using Kernel::Literal;
using Kernel::Problem;
using Kernel::Unit;
using Kernel::UnitList;

/*
 * The actual worker for the twee trick.
 # - evaluates conjucture literals bottom up (as orchestrated by TweeGoalTransformation::apply)
 # - and eagerly introduces new definitions for its subterms
 # - already encountered subterms reuse older definitions
 */
class Definizator : public BottomUpTermTransformer {
  public: // so that TweeGoalTransformation::apply can directly access
    // all the new definitions (as clauses) introduced along the way
    UnitList* newUnits;

    // accumlating the defining units as premises for the current "rewrite"
    // (reset responsibility is with TweeGoalTransformation::apply)
    UnitList* premises;

    // for each relevant term, cache the introduced symbol and the corresponding definition
    DHMap<Term*,std::pair<unsigned,Clause*>> _cache;

    Definizator(bool groundOnly) : newUnits(UnitList::empty()), _groundOnly(groundOnly) {}
  private:
    bool _groundOnly;

    unsigned _typeArity;
    TermStack _typeVars;
    TermStack _termVars;
    TermStack _allVars; // including typeVars, which will come first, then termVars
    TermStack _termVarSorts;

    // a helper function to collect terms variables and their sorts
    // all stored in the above private fields to be looked up by transformSubterm
    void scanVars(Term* t) {
      CALL("Definizator::scanVars");

      static DHSet<unsigned> varSeen;
      varSeen.reset();
      _typeArity = 0;
      _allVars.reset();
      _typeVars.reset();
      _termVars.reset();
      _termVarSorts.reset();

      // fake scanVars cheaply
      if (t->ground()) return;

      VariableWithSortIterator it(t);
      while (it.hasNext()) {
        auto varAndSort = it.next();
        TermList v = varAndSort.first;
        TermList s = varAndSort.second;
        if (varSeen.insert(v.var())) {
          if(s == AtomicSort::superSort()) {
            _allVars.push(v);
            _typeVars.push(v);
          } else {
            _termVars.push(v);
            _termVarSorts.push(s);
          }
        }
      }
      _typeArity = _allVars.size(); // allVars only collected typeVars until now
      for(unsigned i = 0; i < _termVars.size()
#if VHOL
        && !env.property->higherOrder()
#endif
        ; i++){
        _allVars.push(_termVars[i]);
      }

      SortHelper::normaliseArgSorts(_typeVars, _termVarSorts);
    }

  protected:
    TermList transformSubterm(TermList trm) override {
      CALL("Definizator::transformSubterm");

      // cout << "tf: " << trm.toString() << endl;
      if (trm.isVar()) return trm;

      Term* t = trm.term();
      if (t->isSort() || t->arity() == 0 || (!t->ground() && _groundOnly)) return trm;

#if VHOL
      if (env.property->higherOrder() && trm.containsLooseIndex())
      { return trm; }
#endif

      Term* key = t;
      if (!t->ground()) {
        // as we go bottom up, t is never too big (well, it could be wide, but at least not deep)
        static Renaming rnm;
        rnm.reset();
        rnm.normalizeVariables(t);
        key = rnm.apply(t);
      }

      std::pair<unsigned,Clause*> symAndDef;
      TermList res;
      if (!_cache.find(key,symAndDef)) {
        TermList outSort = SortHelper::getResultSort(t);
        unsigned newSym;
        Clause* newDef;
        scanVars(t);

        SortHelper::normaliseSort(_typeVars, outSort);


        // will the definition folding decrease term weight?
        // (whether we will also demodulate in this direction may depend on the ordering, but with a constant-weight KBO we will)
        if (t->weight() > _allVars.size()+1) {
          // this is always true in the ground case (where t->weight()>=2 and _allVars.size() == 0)
#if VHOL
          if(!env.property->higherOrder()){
#endif
            newSym = env.signature->addFreshFunction(_allVars.size(), "sF");
            OperatorType* type = OperatorType::getFunctionType(_termVarSorts.size(),_termVarSorts.begin(),outSort,_typeArity);
            env.signature->getFunction(newSym)->setType(type);

            // res is used both to replace here, but also in the new definition
            res = TermList(Term::create(newSym,_allVars.size(),_allVars.begin()));
#if VHOL           
          } else {
            newSym = env.signature->addFreshFunction(_typeVars.size(), "sF");
            TermList sort = AtomicSort::arrowSort(_termVarSorts, outSort);
            Signature::Symbol* sym = env.signature->getFunction(newSym);
            sym->setType(OperatorType::getConstantsType(sort, _typeVars.size())); 

            TermList head = TermList(Term::create(newSym, _typeVars.size(), _typeVars.begin()));
            res= ApplicativeHelper::app(head, _termVars);
          }
#endif

          // (we don't care the definition is not rectified, as long as it's correct)
          // it is correct, because the lhs below is t and not key
          Literal* equation = Literal::createEquality(true, TermList(t), res, SortHelper::getResultSort(res.term()));
          Inference inference(NonspecificInference0(UnitInputType::AXIOM,InferenceRule::FUNCTION_DEFINITION));
          newDef = new (1) Clause(1, inference);
          newDef->literals()[0] = equation;
        } else {
          // linear term, don't replace (and remember it in cache)
          symAndDef.first = 0;
          symAndDef.second = nullptr;
          _cache.insert(key,symAndDef);
          return trm;
        }

        // record globally
        UnitList::push(newDef,newUnits);
        if(env.options->showPreprocessing()) {
          env.out() << "[PP] twee: " << newDef->toString() << std::endl;
        }
        symAndDef.first = newSym;
        symAndDef.second = newDef;
        _cache.insert(key,symAndDef);
      } else {
        if (symAndDef.second == nullptr) {
          // we recalled this term is not worth replacing
          return trm;
        }

        scanVars(t);
#if VHOL
        if(!env.property->higherOrder()){
#endif
          res = TermList(Term::create(symAndDef.first,_allVars.size(),_allVars.begin()));
#if VHOL           
        } else {
          TermList head = TermList(Term::create(symAndDef.first, _typeVars.size(), _typeVars.begin()));
          res= ApplicativeHelper::app(head, _termVars);
        }
#endif

      }
      // record as a new premise
      UnitList::push(symAndDef.second,premises);
      // cout << "r: " << res.toString() << endl;
      return res;
    }
};

void Shell::TweeGoalTransformation::apply(Problem &prb, bool groundOnly)
{
  CALL("TweeGoalTransformation::apply");

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
      // cout << "L: " << l->toString() << endl;
      Literal* nl = df.transform(l);
      // cout << "NL: " << nl->toString() << endl;
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
