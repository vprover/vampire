/**
 * @file FOOLElimination.cpp
 * Implements class FOOLElimination.
 */

#include "Indexing/TermSharing.hpp"

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"

#include "Shell/Options.hpp"

#include "Rectify.hpp"

#include "FOOLElimination.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

FOOLElimination::FOOLElimination() : _defs(0) {}

bool FOOLElimination::containsFOOL(FormulaUnit* unit) {
  CALL("FOOLElimination::containsFOOL");

  SubformulaIterator sfi(unit->formula());
  while(sfi.hasNext()) {
    Formula* f = sfi.next();
    switch(f->connective()) {
      case LITERAL:
        if(!f->literal()->shared()) {
          return true;
        }
        break;
      case BOOL_TERM:
        return true;
      default:
        break;
    }
  }
  return false;
}

void FOOLElimination::apply(Problem& prb)  {
  CALL("FOOLElimination::apply(Problem*)");

  apply(prb.units());
  prb.reportFOOLEliminated();
  prb.invalidateProperty();
}

void FOOLElimination::apply(UnitList*& units) {
  CALL("FOOLElimination::apply(UnitList*&)");

  UnitList::DelIterator us(units);
  while(us.hasNext()) {
    Unit* u = us.next();
    if(u->isClause()) {
#if VDEBUG
      Clause* cl = static_cast<Clause*>(u);
      for (unsigned i = 0; i < cl->length(); i++) {
        // we do not allow special terms in clauses so we check that all clause literals
        // are shared (special terms can not be shared)
        ASS((*cl)[i]->shared());
      }
#endif
      continue;
    }
    Unit* v = apply(static_cast<FormulaUnit*>(u));
    if (v != u) {
      us.replace(v);
    }
  }

  // append the FOOL axiom "$true != $false"
  TermList t(Term::createConstant(Signature::FOOL_TRUE));
  TermList f(Term::createConstant(Signature::FOOL_FALSE));

  Formula* dc = new AtomicFormula(Literal::createEquality(false, t, f, Sorts::SRT_FOOL_BOOL));
  FormulaUnit* disjointConstants = new FormulaUnit(dc, new Inference(Inference::FOOL_AXIOM), Unit::AXIOM);

  addDefinition(disjointConstants);

  units = UnitList::concat(_defs, units);
  _defs = 0;
}

FormulaUnit* FOOLElimination::apply(FormulaUnit* unit) {
  CALL("FOOLElimination::apply(FormulaUnit*)");

  if (!containsFOOL(unit)) {
    return unit;
  }

  FormulaUnit* rectifiedUnit = Rectify::rectify(unit);

  Formula* f = rectifiedUnit->formula();

  _unit = rectifiedUnit;
  _varSorts.reset();

  SortHelper::collectVariableSorts(f, _varSorts);

  Formula* g = process(f);
  if (f == g) {
    return rectifiedUnit;
  }

  Inference* inference = new Inference1(Inference::FOOL_ELIMINATION, rectifiedUnit);
  FormulaUnit* res = new FormulaUnit(g, inference, rectifiedUnit->inputType());

  if (unit->included()) {
    res->markIncluded();
  }

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] " << unit->toString() << std::endl;
    env.out() << "[PP] " << res->toString()  << std::endl;
    env.endOutput();
  }

  return res;
}

Formula* FOOLElimination::process(Formula* formula) {
  CALL("FOOLElimination::process(Formula*)");

  switch (formula->connective()) {
    case LITERAL:
      return new AtomicFormula(process(formula->literal()));

    case AND:
    case OR:
      return new JunctionFormula(formula->connective(), process(formula->args()));

    case IMP:
    case IFF:
    case XOR:
      return new BinaryFormula(formula->connective(), process(formula->left()), process(formula->right()));

    case NOT:
      return new NegatedFormula(process(formula->uarg()));

    case FORALL:
    case EXISTS:
      return new QuantifiedFormula(formula->connective(), formula->vars(), process(formula->qarg()));

    case BOOL_TERM: {
      /**
       * Having a boolean term t in a formula context,
       * we simply replace it with t = true, where true is FOOL truth.
       */
      TermList terms = process(formula->getBooleanTerm());
      TermList truth(Term::createConstant(Signature::FOOL_TRUE));
      Literal* equality = Literal::createEquality(true, terms, truth, Sorts::SRT_FOOL_BOOL);
      Formula* processedFormula = new AtomicFormula(equality);

      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] FOOL in: " << formula->toString() << std::endl;
        env.out() << "[PP] FOOL out: " << processedFormula->toString() << std::endl;
        env.endOutput();
      }

      return processedFormula;
    }

    case TRUE:
    case FALSE:
      return formula;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
  }
}

FormulaList* FOOLElimination::process(FormulaList* formulas) {
  CALL ("FOOLElimination::process(FormulaList*)");
  return formulas->isEmpty() ? formulas : new FormulaList(process(formulas->head()), process(formulas->tail()));
}

Literal* FOOLElimination::process(Literal* literal) {
  CALL("FOOLElimination::process(Literal*)");

  unsigned predicate = literal->functor();
  unsigned arity = literal->arity();
  bool polarity = (bool)literal->polarity();
  bool commutative = literal->commutative();

  Literal* processedLiteral = new (arity) Literal(predicate, arity, polarity, commutative);
  unsigned i = 0;
  Term::Iterator ait(literal);
  while (ait.hasNext()) {
    *processedLiteral->nthArgument(i++) = process(ait.next());
  }

  if (literal->isTwoVarEquality()) {
    processedLiteral->markTwoVarEquality();
  }

  if (!processedLiteral->shared()) {
    if (processedLiteral->isTwoVarEquality()) {
      processedLiteral = env.sharing->insertVariableEquality(processedLiteral, processedLiteral->twoVarEqSort());
    } else {
      processedLiteral = env.sharing->insert(processedLiteral);
    }
  }

  return processedLiteral;
}

TermList FOOLElimination::process(TermList ts) {
  CALL("FOOLElimination::process(TermList*)");

  if (!ts.isTerm() || !ts.term()->isSpecial()) {
    return ts;
  }

  TermList processedTermList = process(ts.term());
  if (processedTermList.isTerm() && !processedTermList.term()->shared()) {
    Term* processedTerm = processedTermList.term();
    if (processedTerm->isLiteral()) {
      Literal* processedLiteral = static_cast<Literal*>(processedTerm);
      if (processedLiteral->isTwoVarEquality()) {
        processedTerm = env.sharing->insertVariableEquality(processedLiteral, processedLiteral->twoVarEqSort());
      } else {
        processedTerm = env.sharing->insert(processedLiteral);
      }
    } else {
      processedTerm = env.sharing->insert(processedTerm);
    }
    processedTermList = TermList(processedTerm);
  }

  return processedTermList;
}

/**
 * Process a given term. The actual work is done if the term is special.
 * Returns TermList rather than Term* to cover the situation when $let-term
 * with a variable body is processed. That way, the result would be just the
 * variable, and we cannot put it inside Term*.
 */
TermList FOOLElimination::process(Term* term) {
  CALL("FOOLElimination::process(Term*)");

  if (!term->isSpecial()) {
    return TermList(term);
  }

  Term::SpecialTermData* sd = term->getSpecialData();

  TermList processedTerm;
  /**
   * In order to process a special term (that is, a term that is syntactically
   * valid in FOOL but not in FOL), we will replace the whole term or some of
   * its parts with an application of a fresh function symbol and add one or
   * more definitions of this symbol to _defs.
   *
   * Note that process() is called recursively on all the subterms of the given
   * term. That way, every definition that is put into _defs doesn't have FOOL
   * subterms and we don't have to further process it.
   *
   * To prevent variables from escaping their lexical scope, we collect those
   * of them, that have free occurrences in the term and make the applications
   * of the fresh symbol take them as arguments.
   *
   * Note that we don't have to treat in a similar way occurrences of function
   * symbols, defined in $let-expressions, because the parser already made sure
   * to resolve scope issues, made them global (by renaming) and added them to
   * the signature.
   */

  // collect free variables X1, ..., Xn of the term and their sorts
  Formula::VarList* freeVars = term->freeVariables();
  Stack<unsigned> freeVarsSorts = collectSorts(freeVars);

  /**
   * Note that we collected free variables before processing subterms. That
   * assumes that process() preserves free variables. This assumption relies
   * on the following:
   *  1) All variables are disjoint within a term or formula, therefore we never
   *     have to rename them.
   *  2) Free variables of the term always occur in the processed term.
   */

  switch (term->functor()) {
    case Term::SF_TERM_ITE: {
      /**
       * Having a term of the form $ite(f, s, t) and the list X1, ..., Xn of
       * its free variables (it is the union of free variables of f, s and t)
       * we will do the following:
       *  1) Create a fresh function symbol g of arity n that spans over sorts
       *     of X1, ..., Xn and the return sort of the term
       *  2) Add two definitions:
       *     * ![X1, ..., Xn]: ( f => g(X1, ..., Xn) = s)
       *     * ![X1, ..., Xn]: (~f => g(X1, ..., Xn) = t)
       *  3) Replace the term with g(X1, ..., Xn)
       */

      Formula* condition  = process(sd->getCondition());
      TermList thenBranch = process(*term->nthArgument(0));
      TermList elseBranch = process(*term->nthArgument(1));

      // the sort of the term is the sort of the then branch
      unsigned resultSort = SortHelper::getResultSort(thenBranch, _varSorts);
      ASS_EQ(resultSort, SortHelper::getResultSort(elseBranch, _varSorts));

      // create a fresh symbol g and build g(X1, ..., Xn)
      unsigned arity = (unsigned)freeVarsSorts.length();
      unsigned freshSymbol = env.signature->addIteFunction(arity, freeVarsSorts.begin(), resultSort);
      TermList freshSymbolApplication = buildFunctionApplication(freshSymbol, freeVars);

      // build ![X1, ..., Xn]: (f => g(X1, ..., Xn) = s)
      Literal* thenEquality = Literal::createEquality(true, freshSymbolApplication, thenBranch, resultSort);
      Formula* thenImplication = new BinaryFormula(IMP, condition, new AtomicFormula(thenEquality));
      Formula* thenFormula = arity > 0 ? (Formula*)new QuantifiedFormula(FORALL, freeVars, thenImplication) : thenImplication;

      // build ![X1, ..., Xn]: (~f => g(X1, ..., Xn) = t)
      Literal* elseEquality = Literal::createEquality(true, freshSymbolApplication, elseBranch, resultSort);
      Formula* elseImplication = new BinaryFormula(IMP, new NegatedFormula(condition), new AtomicFormula(elseEquality));
      Formula* elseFormula = arity > 0 ? (Formula*)new QuantifiedFormula(FORALL, freeVars, elseImplication) : elseImplication;

      // add both definitions
      Inference* iteInference = new Inference1(Inference::FOOL_ITE_ELIMINATION, _unit);
      addDefinition(new FormulaUnit(thenFormula, iteInference, _unit->inputType()));
      addDefinition(new FormulaUnit(elseFormula, iteInference, _unit->inputType()));

      processedTerm = freshSymbolApplication;
      break;
    }

    case Term::SF_TERM_LET: {
      /**
       * Having a term of the form $let(f(Y1, ..., Yk) := s, t), where f is a
       * function or predicate symbol and the list X1, ..., Xn of free variables
       * of the binding of f (it is the set of free variables of s minus
       * Y1, ..., Yk) we will do the following:
       *  1) Create a fresh function or predicate symbol g (depending on which
       *     one is f) of arity n + k that spans over sorts of
       *     X1, ..., Xn, Y1, ..., Yk
       *  2) If f is a predicate symbol, add the following definition:
       *       ![X1, ..., Xn, Y1, ..., Yk]: g(X1, ..., Xn, Y1, ..., Yk) <=> s
       *     Otherwise, add
       *       ![X1, ..., Xn, Y1, ..., Yk]: g(X1, ..., Xn, Y1, ..., Yk) = s
       *  3) Build a term t' by replacing all of its subterms of the form
       *     f(t1, ..., tk) by g(X1, ..., Xn, t1, ..., tk)
       *  4) Replace the term with t'
       */

      Term* symbolDefinition = sd->getLhs().term();
      TermList body = sd->getRhs(); // deliberately unprocessed here

      /**
       * $let-expressions are used for binding both function and predicate symbols.
       * The binding f(Y1, ..., Yk) := s, however, is always stored as a pair of
       * terms f(Y1, ..., Yk) and s. In case f is a predicate symbol, both of them
       * are formulas, wrapped inside a term. This is how we check that it is a
       * predicate binding.
       */
      bool isPredicate = symbolDefinition->isFormula();
      ASS_EQ(isPredicate, body.isTerm() && body.term()->isFormula());

      // in case of predicate binding, take the literal of the definition
      Literal* predicateDefinition;
      if (isPredicate) {
        predicateDefinition = symbolDefinition->getSpecialData()->getFormula()->literal();
      }

      // collect variables Y1, ..., Yk
      Formula::VarList* argumentVars(0);
      TermList* arguments = isPredicate ? predicateDefinition->args() : symbolDefinition->args();
      for (; arguments->isNonEmpty(); arguments = arguments->next()) {
        argumentVars = new Formula::VarList(arguments->var(), argumentVars);
      }

      // collect variables X1, ..., Xn
      Formula::VarList* bodyFreeVars(0);
      Formula::VarList::Iterator bfvi(body.freeVariables());
      while (bfvi.hasNext()) {
        int var = bfvi.next();
        if (!argumentVars->member(var)) {
          bodyFreeVars = new Formula::VarList(var, bodyFreeVars);
        }
      }

      // build the list X1, ..., Xn, Y1, ..., Yk of variables and their sorts
      Formula::VarList* vars = bodyFreeVars->append(argumentVars);
      Stack<unsigned> sorts = collectSorts(vars);

      // take the defined function symbol and its result sort
      unsigned symbol   = isPredicate ? predicateDefinition->functor() : symbolDefinition->functor();
      unsigned bodySort = isPredicate ? Sorts::SRT_BOOL : SortHelper::getResultSort(body, _varSorts);

      /**
       * Here we can take a simple shortcut. If the there are no free variables,
       * f and g would have the same type, but g would have an ugly generated name.
       * So, in this case, instead of creating a new symbol, we will just
       * reuse f and leave the t term as it is.
       */
      bool renameSymbol = bodyFreeVars->isNonEmpty();

      // create a fresh function or predicate symbol g
      unsigned arity = (unsigned)vars->length();
      unsigned freshSymbol = symbol;
      if (renameSymbol) {
        freshSymbol = isPredicate ? env.signature->addLetPredicate(arity, sorts.begin())
                                  : env.signature->addLetFunction (arity, sorts.begin(), bodySort);
      }

      // build the definition of the function or predicate symbol
      Formula* freshSymbolDefinition;
      if (isPredicate) {
        // process the body of the function that is a formula
        Formula* formula = process(body.term()->getSpecialData()->getFormula());

        // build g(X1, ..., Xn, Y1, ..., Yk)
        Literal* freshSymbolApplication = buildPredicateApplication(freshSymbol, vars);

        // build ![X1, ..., Xn, Y1, ..., Yk]: g(X1, ..., Xn, Y1, ..., Yk) <=> s
        freshSymbolDefinition = new BinaryFormula(IFF, new AtomicFormula(freshSymbolApplication), formula);
      } else {
        // process the body of the function that is a term
        body = process(body);

        // build g(X1, ..., Xn, Y1, ..., Yk)
        TermList freshSymbolApplication = buildFunctionApplication(freshSymbol, vars);

        // build ![X1, ..., Xn, Y1, ..., Yk]: g(X1, ..., Xn, Y1, ..., Yk) = s
        freshSymbolDefinition = new AtomicFormula(Literal::createEquality(true, freshSymbolApplication, body, bodySort));
      }

      Formula* definition = arity > 0 ? (Formula*) new QuantifiedFormula(FORALL, vars, freshSymbolDefinition)
                                      : freshSymbolDefinition;

      // add the introduced definition
      Inference* letInference = new Inference1(Inference::FOOL_LET_ELIMINATION, _unit);
      addDefinition(new FormulaUnit(definition, letInference, _unit->inputType()));

      TermList contents = *term->nthArgument(0); // deliberately unprocessed here

      // replace occurrences of f(t1, ..., tk) by g(X1, ..., Xn, t1, ..., tk)
      if (renameSymbol) {
        if (env.options->showPreprocessing()) {
          env.beginOutput();
          env.out() << "[PP] FOOL replace in: " << contents.toString() << std::endl;
        }
        contents = replace(symbol, freshSymbol, bodyFreeVars, contents);
        if (env.options->showPreprocessing()) {
          env.out() << "[PP] FOOL replace out: " << contents.toString() << std::endl;
          env.endOutput();
        }
      }

      processedTerm = process(contents);
      break;
    }

    case Term::SF_FORMULA: {
      Connective connective = sd->getFormula()->connective();

      if (connective == TRUE) {
        return TermList(Term::createConstant(Signature::FOOL_TRUE));
      }

      if (connective == FALSE) {
        return TermList(Term::createConstant(Signature::FOOL_FALSE));
      }

      /**
       * Having a formula in a term context and the list X1, ..., Xn of its
       * free variables we will do the following:
       *  1) Create a fresh function symbol g of arity n that spans over sorts of X1, ..., Xn
       *  2) Add the definition: ![X1, ..., Xn]: (f <=> g(X1, ..., Xn) = true),
       *     where true is FOOL constant
       *  3) Replace the term with g(X1, ..., Xn)
       */

      Formula *formula = process(sd->getFormula());

      // create a fresh symbol g and build g(X1, ..., Xn)
      unsigned arity = (unsigned)freeVarsSorts.length();
      unsigned freshSymbol = env.signature->addBooleanFunction(arity, freeVarsSorts.begin());
      TermList freshSymbolApplication = buildFunctionApplication(freshSymbol, freeVars);

      // build ![X1, ..., Xn]: (f <=> g(X1, ..., Xn) = true)
      static TermList truth(Term::createConstant(Signature::FOOL_TRUE));
      Literal* equality = Literal::createEquality(true, freshSymbolApplication, truth, Sorts::SRT_FOOL_BOOL);
      Formula* equivalence = new BinaryFormula(IFF, formula, new AtomicFormula(equality));
      Formula* def = arity > 0 ? (Formula*) new QuantifiedFormula(FORALL, freeVars, equivalence) : equivalence;

      // add the introduced definition
      Inference* inference = new Inference1(Inference::FOOL_ELIMINATION, _unit);
      addDefinition(new FormulaUnit(def, inference, _unit->inputType()));

      processedTerm = freshSymbolApplication;
      break;
    }

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
  }

  if (processedTerm != TermList(term) && env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] FOOL in: " << term->toString() << std::endl;
    env.out() << "[PP] FOOL out: " << processedTerm.toString() << std::endl;
    env.endOutput();
  }

#if VDEBUG
  // a check that freeVars and processedTerm->freeVariables() coincide

  Formula::VarList* processedFreeVars = processedTerm.isVar() ? new List<int>(processedTerm.var())
                                                              : processedTerm.term()->freeVariables();

  Formula::VarList::Iterator ufv(freeVars);
  while (ufv.hasNext()) {
    unsigned var = (unsigned)ufv.next();
    ASS_REP(processedFreeVars->member(var), var);
  }
  Formula::VarList::Iterator pfv(processedFreeVars);
  while (pfv.hasNext()) {
    unsigned var = (unsigned)pfv.next();
    ASS_REP(freeVars->member(var), var);
  }
#endif

  // process(TermList*) expects that literals are still literals after processing
  ASS_EQ(term->isLiteral(), processedTerm.isTerm() && processedTerm.term()->isLiteral());

  ASS(processedTerm.isSafe());

  return processedTerm;
}

/**
 * Given a function symbol g of a given arity n and a list of variables X1, ..., Xn
 * builds a term g(X1, ..., Xn).
 */
TermList FOOLElimination::buildFunctionApplication(unsigned function, Formula::VarList* vars) {
  CALL("FOOLElimination::buildFunctionApplication");

  unsigned arity = (unsigned)vars->length();
  ASS_EQ(env.signature->functionArity(function), arity);

  Stack<TermList> arguments;
  Formula::VarList::Iterator vit(vars);
  while (vit.hasNext()) {
    unsigned var = (unsigned)vit.next();
    arguments.push(TermList(var, false));
  }
  return TermList(Term::create(function, arity, arguments.begin()));
}

/**
 * Given a predicate symbol g of a given arity n and a list of variables X1, ..., Xn
 * builds a term g(X1, ..., Xn).
 */
Literal* FOOLElimination::buildPredicateApplication(unsigned predicate, Formula::VarList* vars) {
  CALL("FOOLElimination::buildPredicateApplication");

  unsigned arity = (unsigned)vars->length();
  ASS_EQ(env.signature->predicateArity(predicate), arity);

  Stack<TermList> arguments;
  Formula::VarList::Iterator vit(vars);
  while (vit.hasNext()) {
    unsigned var = (unsigned)vit.next();
    arguments.push(TermList(var, false));
  }
  return Literal::create(predicate, arity, true, false, arguments.begin());
}

/**
 * Creates a stack of sorts for the given variables, using the sorting context
 * of the current formula.
 */
Stack<unsigned> FOOLElimination::collectSorts(Formula::VarList* vars) {
  CALL("FOOLElimination::collectSorts");

  Stack<unsigned> sorts;
  Formula::VarList::Iterator fvi(vars);
  while (fvi.hasNext()) {
    unsigned var = (unsigned)fvi.next();
    ASS_REP(_varSorts.find(var), var);
    sorts.push(_varSorts.get(var));
  }
  return sorts;
}

/**
 * Extends the list of definitions with a given unit, making sure that it
 * doesn't have FOOL subterms.
 */
void FOOLElimination::addDefinition(FormulaUnit* def) {
  CALL("FOOLElimination::addDefinition");

  ASS_REP(!containsFOOL(def), def->toString());

  _defs = new UnitList(def, _defs);

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] FOOL added definition: " << def->toString() << std::endl;
    env.endOutput();
  }
}

Term* FOOLElimination::replace(unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars, Term* term) {
  CALL("FOOLElimination::replace(..., Term*)");
  if (term->isSpecial()) {
    Term::SpecialTermData* sd = term->getSpecialData();
    switch (term->functor()) {
      case Term::SF_TERM_ITE: {
        Formula* formula    = replace(symbol, freshSymbol, freeVars, sd->getCondition());
        TermList thenBranch = replace(symbol, freshSymbol, freeVars, *term->nthArgument(0));
        TermList elseBranch = replace(symbol, freshSymbol, freeVars, *term->nthArgument(1));
        return Term::createITE(formula, thenBranch, elseBranch);
      }

      case Term::SF_TERM_LET: {
        TermList lhs = sd->getLhs();
        TermList rhs = replace(symbol, freshSymbol, freeVars, sd->getRhs());
        TermList contents = replace(symbol, freshSymbol, freeVars, *term->nthArgument(0));
        return Term::createLet(lhs, rhs, contents);
      }

      case Term::SF_FORMULA: {
        Formula* formula = replace(symbol, freshSymbol, freeVars, sd->getFormula());
        return Term::createFormula(formula);
      }

#if VDEBUG
      default:
        ASSERTION_VIOLATION;
#endif
    }
  }

  unsigned arity = term->arity();
  unsigned function = term->functor();

  bool renaming = function == symbol;

  if (renaming) {
    function = freshSymbol;
    arity += freeVars->length();
  }

  Stack<TermList> arguments;

  if (renaming) {
    Formula::VarList::Iterator fvit(freeVars);
    while (fvit.hasNext()) {
      unsigned var = (unsigned)fvit.next();
      arguments.push(TermList(var, false));
    }
  }

  Term::Iterator it(term);
  while (it.hasNext()) {
    arguments.push(replace(symbol, freshSymbol, freeVars, it.next()));
  }

  return Term::create(function, arity, arguments.begin());
}

TermList FOOLElimination::replace(unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars, TermList ts) {
  CALL("FOOLElimination::replace(..., TermList)");

  if (!ts.isTerm()) {
    return ts;
  }

  return TermList(replace(symbol, freshSymbol, freeVars, ts.term()));
}

Formula* FOOLElimination::replace(unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars, Formula* formula) {
  CALL("FOOLElimination::replace(..., Formula*)");
  switch (formula->connective()) {
    case LITERAL: {
      Literal *literal = formula->literal();
      unsigned functor = literal->functor();
      unsigned arity = literal->arity();
      bool polarity = (bool)literal->polarity();
      bool commutative = (bool)literal->commutative();

      bool renaming = functor == symbol;

      if (renaming) {
        functor = freshSymbol;
        arity += freeVars->length();
      }

      Stack<TermList> arguments;

      if (renaming) {
        Formula::VarList::Iterator fvit(freeVars);
        while (fvit.hasNext()) {
          arguments.push(TermList((unsigned)fvit.next(), false));
        }
      }

      Term::Iterator lit(literal);
      while (lit.hasNext()) {
        arguments.push(replace(symbol, freshSymbol, freeVars, lit.next()));
      }

      return new AtomicFormula(Literal::create(functor, arity, polarity, commutative, arguments.begin()));
    }

    case AND:
    case OR:
      return new JunctionFormula(formula->connective(), replace(symbol, freshSymbol, freeVars, formula->args()));

    case IMP:
    case IFF:
    case XOR:
      return new BinaryFormula(formula->connective(),
                               replace(symbol, freshSymbol, freeVars, formula->left()),
                               replace(symbol, freshSymbol, freeVars, formula->right()));

    case NOT:
      return new NegatedFormula(replace(symbol, freshSymbol, freeVars, formula->uarg()));

    case FORALL:
    case EXISTS:
      return new QuantifiedFormula(formula->connective(), formula->vars(), process(formula->qarg()));

    case BOOL_TERM:
      return new BoolTermFormula(replace(symbol, freshSymbol, freeVars, formula->getBooleanTerm()));

    case TRUE:
    case FALSE:
      return formula;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
  }
}

FormulaList* FOOLElimination::replace(unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars, FormulaList* formulas) {
  CALL("FOOLElimination::replace(..., FormulaList*)");
  return formulas->isEmpty() ? formulas : new FormulaList(replace(symbol, freshSymbol, freeVars, formulas->head()),
                                                          replace(symbol, freshSymbol, freeVars, formulas->tail()));
}

}
