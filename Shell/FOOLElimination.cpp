/**
 * @file FOOLElimination.cpp
 * Implements the FOOL-to-FOL translation procedure, described in "A First
 * Class Boolean Sort in First-Order Theorem Proving and TPTP" [1] by
 * Kotelnikov, Kovacs and Voronkov.
 *
 * [1] http://arxiv.org/abs/1505.01682
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
      Formula* processedFormula = processAsFormula(formula->getBooleanTerm());

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

/**
 * Processes a list of terms.
 *
 * Takes a context argument (whos value is either TERM_CONTEXT or
 * FORMULA_CONTEXT) and rather than returning the result of processing, writes
 * it to termResult (when context is TERM_CONTEXT) or formulaResult (when
 * context is FORMULA_CONTEXT). In other words, the result of processing is
 * either a term or a formula, depending on the context.
 *
 * The meaning of the context is the following. Rather than having two versions
 * of e.g. $ite-expressions (term-level and formula-level), this implementation
 * considers only the term-level case, the formula case is encoded using the
 * formula-inside-term special case of term. That is, the formula $ite(C, A, B),
 * where A, B and C are all formulas, is stored as $formula{$ite(C, $term{A}, $term{B})}.
 * The processing of an $ite-term should be different, depending on whether or
 * not it occures directly under $formula. In the former case, we should unpack
 * A and B from $term and introduce a fresh predicate symbol, whereas in the
 * latter case we should introduce a fresh function symbol. So, the context
 * argument tells the process function if the term is inside of a $formula.
 *
 * A similar reasoning is applied to the way $let-terms are stored.
 *
 * An alternative and slightly simpler implementation would have been to always
 * go for the TERM_CONTEXT case. That way, instead of introducing a fresh
 * predicate symbol when inside $formula, we would introduce a fresh function
 * symbol of the sort FOOL_BOOL. That would result, however, in more
 * definitions with more boilerplate. In particular, instead of predicate
 * applications we would have equalities of function symbol applications to
 * FOOL_TRUE all over the place.
 */
void FOOLElimination::process(TermList ts, context context, TermList& termResult, Formula*& formulaResult) {
  CALL("FOOLElimination::process(TermList ts, context context, ...)");

  if (!ts.isTerm() || !ts.term()->isSpecial()) {
    if (context == TERM_CONTEXT) {
      termResult = ts;
    } else {
      formulaResult = toEquality(ts);
    }
    return;
  }

  process(ts.term(), context, termResult, formulaResult);

  if (context == FORMULA_CONTEXT) {
    return;
  }

  if (termResult.isTerm() && !termResult.term()->shared()) {
    Term* processedTerm = termResult.term();
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
    termResult = TermList(processedTerm);
  }

  // preprocessing of the term does not affect the sort
  ASS_EQ(SortHelper::getResultSort(ts, _varSorts),
         SortHelper::getResultSort(termResult, _varSorts));
}

/**
 * A shortcut of process(TermList, context) for TERM_CONTEXT.
 */
TermList FOOLElimination::process(TermList terms) {
  CALL("FOOLElimination::process(TermList terms)");
  TermList ts;
  Formula* dummy;
  process(terms, TERM_CONTEXT, ts, dummy);
  return ts;
}

/**
 * A shortcut of process(TermList, context) for FORMULA_CONTEXT.
 */
Formula* FOOLElimination::processAsFormula(TermList terms) {
  CALL("FOOLElimination::processAsFormula(TermList terms)");
  Formula* formula;
  TermList dummy;
  process(terms, FORMULA_CONTEXT, dummy, formula);
  return formula;
}

/**
 * Process a given term. The actual work is done if the term is special.
 *
 * Similarly to process(TermList, context, ...) takes a context as an argument
 * and depending on its value (TERM_CONTEXT or FORMULA_CONTEXT) writes the
 * result to termResult or formulaResult, respectively.
 *
 * Returns TermList rather than Term* to cover the situation when $let-term
 * with a variable body is processed. That way, the result would be just the
 * variable, and we cannot put it inside Term*.
 */
void FOOLElimination::process(Term* term, context context, TermList& termResult, Formula*& formulaResult) {
  CALL("FOOLElimination::process(Term* term, context context, ...)");

  if (!term->isSpecial()) {
    if (context == TERM_CONTEXT) {
      termResult = TermList(term);
    } else {
      formulaResult = toEquality(TermList(term));
    }
    return;
  }

  Term::SpecialTermData* sd = term->getSpecialData();

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] FOOL in: " << term->toString() << std::endl;
    env.endOutput();
  }

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
   * the signature. The only thing to be cautious about is that processing of
   * the contents of the $let-term should be done after the occurrences of the
   * defined symbol in it are replaced with the fresh one.
   */

  // collect free variables X1, ..., Xn of the term and their sorts
  Formula::VarList* freeVars = term->freeVariables();
  Stack<unsigned> freeVarsSorts = collectSorts(freeVars);

  /**
   * Note that we collected free variables before processing subterms. That
   * assumes that process() preserves free variables. This assumption relies
   * on the fact that $ite and formula terms are rewritten into an fresh symbol
   * applied to free variables, and the processing of $let-terms itself doesn't
   * remove occurrences of variables.
   */

  switch (term->functor()) {
    case Term::SF_ITE: {
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

      Formula* condition = process(sd->getCondition());

      TermList thenBranch = *term->nthArgument(0);
      TermList elseBranch = *term->nthArgument(1);

      Formula* thenBranchFormula;
      Formula* elseBranchFormula;

      if (context == FORMULA_CONTEXT) {
        ASS(thenBranch.isTerm() && thenBranch.term()->isFormula());
        ASS(elseBranch.isTerm() && elseBranch.term()->isFormula());
        thenBranchFormula = process(thenBranch.term()->getSpecialData()->getFormula());
        elseBranchFormula = process(elseBranch.term()->getSpecialData()->getFormula());
      } else {
        thenBranch = process(thenBranch);
        elseBranch = process(elseBranch);
      }

      bool isPredicate = context == FORMULA_CONTEXT;

      // the sort of the term is the sort of the then branch
      unsigned resultSort = SortHelper::getResultSort(thenBranch, _varSorts);
      ASS_EQ(resultSort, SortHelper::getResultSort(elseBranch, _varSorts));

      // create a fresh symbol g
      unsigned arity = (unsigned)freeVarsSorts.length();
      unsigned freshSymbol = isPredicate ? env.signature->addItePredicate(arity, freeVarsSorts.begin())
                                         : env.signature->addIteFunction (arity, freeVarsSorts.begin(), resultSort);

      // build g(X1, ..., Xn)
      TermList freshFunctionApplication;
      Formula* freshPredicateApplication;
      if (isPredicate) {
        freshPredicateApplication = buildPredicateApplication(freshSymbol, freeVars);
      } else {
        freshFunctionApplication  = buildFunctionApplication (freshSymbol, freeVars);
      }

      // build g(X1, ..., Xn) == s
      Formula* thenEq;
      if (isPredicate) {
        thenEq = new BinaryFormula(IFF, freshPredicateApplication, thenBranchFormula);
      } else {
        thenEq = new AtomicFormula(Literal::createEquality(true, freshFunctionApplication, thenBranch, resultSort));
      }

      // build (f => g(X1, ..., Xn) == s)
      Formula* thenImplication = new BinaryFormula(IMP, condition, thenEq);

      // build ![X1, ..., Xn]: (f => g(X1, ..., Xn) == s)
      Formula* thenFormula = arity > 0 ? (Formula*)new QuantifiedFormula(FORALL, freeVars, thenImplication)
                                       : thenImplication;

      // build g(X1, ..., Xn) == t
      Formula* elseEq;
      if (isPredicate) {
        elseEq = new BinaryFormula(IFF, freshPredicateApplication, elseBranchFormula);
      } else {
        elseEq = new AtomicFormula(Literal::createEquality(true, freshFunctionApplication, elseBranch, resultSort));
      }

      // build ~f => g(X1, ..., Xn) == t
      Formula* elseImplication = new BinaryFormula(IMP, new NegatedFormula(condition), elseEq);

      // build ![X1, ..., Xn]: (~f => g(X1, ..., Xn) == t)
      Formula* elseFormula = arity > 0 ? (Formula*)new QuantifiedFormula(FORALL, freeVars, elseImplication)
                                       : elseImplication;

      // add both definitions
      Inference* iteInference = new Inference1(Inference::FOOL_ITE_ELIMINATION, _unit);
      addDefinition(new FormulaUnit(thenFormula, iteInference, _unit->inputType()));
      addDefinition(new FormulaUnit(elseFormula, iteInference, _unit->inputType()));

      if (isPredicate) {
        formulaResult = freshPredicateApplication;
      } else {
        termResult = freshFunctionApplication;
      }
      break;
    }

    case Term::SF_LET: {
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

      TermList body = sd->getBody(); // deliberately unprocessed here

      /**
       * $let-expressions are used for binding both function and predicate symbols.
       * The body of the binding, however, is always stored as a term. When f is a
       * predicate, the body is a formula, wrapped in a term. So, this is how we
       * check that it is a predicate binding.
       */
      bool isPredicate = body.isTerm() && body.term()->isFormula();

      // collect variables Y1, ..., Yk
      Formula::VarList* argumentVars = sd->getVariables();

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
      unsigned symbol   = sd->getFunctor();
      unsigned bodySort = SortHelper::getResultSort(body, _varSorts);

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
        Formula* freshPredicateApplication = buildPredicateApplication(freshSymbol, vars);

        // build ![X1, ..., Xn, Y1, ..., Yk]: g(X1, ..., Xn, Y1, ..., Yk) <=> s
        freshSymbolDefinition = new BinaryFormula(IFF, freshPredicateApplication, formula);
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

      Formula* contentsFormula;
      if (context == FORMULA_CONTEXT) {
        ASS(contents.isTerm() && contents.term()->isFormula());
        contentsFormula = contents.term()->getSpecialData()->getFormula();
      }

      // replace occurrences of f(t1, ..., tk) by g(X1, ..., Xn, t1, ..., tk)
      if (renameSymbol) {
        if (env.options->showPreprocessing()) {
          env.beginOutput();
          env.out() << "[PP] FOOL replace in: " << contents.toString() << std::endl;
          env.endOutput();
        }

        if (context == FORMULA_CONTEXT) {
          contentsFormula = replace(symbol, freshSymbol, bodyFreeVars, contentsFormula);
        } else {
          contents = replace(symbol, freshSymbol, bodyFreeVars, contents);
        }

        if (env.options->showPreprocessing()) {
          env.beginOutput();
          env.out() << "[PP] FOOL replace out: " << contents.toString() << std::endl;
          env.endOutput();
        }
      }

      if (context == FORMULA_CONTEXT) {
        formulaResult = process(contentsFormula);
      } else {
        termResult = process(contents);
      }
      break;
    }

    case Term::SF_FORMULA: {
      if (context == FORMULA_CONTEXT) {
        formulaResult = process(sd->getFormula());
        break;
      }

      Connective connective = sd->getFormula()->connective();

      if (connective == TRUE) {
        termResult = TermList(Term::createConstant(Signature::FOOL_TRUE));
        break;
      }

      if (connective == FALSE) {
        termResult = TermList(Term::createConstant(Signature::FOOL_FALSE));
        break;
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
      Formula* equivalence = new BinaryFormula(IFF, formula, toEquality(freshSymbolApplication));
      Formula* def = arity > 0 ? (Formula*) new QuantifiedFormula(FORALL, freeVars, equivalence) : equivalence;

      // add the introduced definition
      Inference* inference = new Inference1(Inference::FOOL_ELIMINATION, _unit);
      addDefinition(new FormulaUnit(def, inference, _unit->inputType()));

      termResult = freshSymbolApplication;
      break;
    }

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
  }

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] FOOL out: " << (context == FORMULA_CONTEXT
                                       ? formulaResult->toString()
                                       : termResult.toString()) << std::endl;
    env.endOutput();
  }

#if VDEBUG
  if (context == TERM_CONTEXT) {
    // freeVars and processedTerm->freeVariables() coincide
    Formula::VarList* processedFreeVars = termResult.isVar() ? new List<int>(termResult.var())
                                                             : termResult.term()->freeVariables();

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

    // special subterms should be eliminated
    ASS(termResult.isSafe());
  }
#endif
}

/**
 * A shortcut of process(Term*, context) for TERM_CONTEXT.
 */
TermList FOOLElimination::process(Term* term) {
  CALL("FOOLElimination::process(Term* term)");
  TermList termList;
  Formula* dummy;
  process(term, TERM_CONTEXT, termList, dummy);
  return termList;
}

/**
 * A shortcut of process(Term*, context) for FORMULA_CONTEXT.
 */
Formula* FOOLElimination::processAsFormula(Term* term) {
  CALL("FOOLElimination::processAsFormula(Term* term)");
  Formula* formula;
  TermList dummy;
  process(term, FORMULA_CONTEXT, dummy, formula);
  ASS(formula);
  return formula;
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
 * builds a literal g(X1, ..., Xn).
 */
Formula* FOOLElimination::buildPredicateApplication(unsigned predicate, Formula::VarList* vars) {
  CALL("FOOLElimination::buildPredicateApplication");

  unsigned arity = (unsigned)vars->length();
  ASS_EQ(env.signature->predicateArity(predicate), arity);

  Stack<TermList> arguments;
  Formula::VarList::Iterator vit(vars);
  while (vit.hasNext()) {
    unsigned var = (unsigned)vit.next();
    arguments.push(TermList(var, false));
  }
  return new AtomicFormula(Literal::create(predicate, arity, true, false, arguments.begin()));
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

Formula* FOOLElimination::toEquality(TermList booleanTerm) {
  TermList truth(Term::createConstant(Signature::FOOL_TRUE));
  Literal* equality = Literal::createEquality(true, booleanTerm, truth, Sorts::SRT_FOOL_BOOL);
  return new AtomicFormula(equality);
}

Term* FOOLElimination::replace(unsigned symbol, unsigned freshSymbol, Formula::VarList* freeVars, Term* term) {
  CALL("FOOLElimination::replace(..., Term*)");
  if (term->isSpecial()) {
    Term::SpecialTermData* sd = term->getSpecialData();
    switch (term->functor()) {
      case Term::SF_ITE: {
        Formula* formula    = replace(symbol, freshSymbol, freeVars, sd->getCondition());
        TermList thenBranch = replace(symbol, freshSymbol, freeVars, *term->nthArgument(0));
        TermList elseBranch = replace(symbol, freshSymbol, freeVars, *term->nthArgument(1));
        return Term::createITE(formula, thenBranch, elseBranch);
      }

      case Term::SF_LET: {
        unsigned functor = sd->getFunctor();
        IntList* variables = sd->getVariables();
        TermList body = replace(symbol, freshSymbol, freeVars, sd->getBody());
        TermList contents = replace(symbol, freshSymbol, freeVars, *term->nthArgument(0));
        return Term::createLet(functor, variables, body, contents);
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
      return new QuantifiedFormula(formula->connective(), formula->vars(),
                                   replace(symbol, freshSymbol, freeVars, formula->qarg()));

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
