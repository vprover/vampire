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
 * @file FormulaVarIterator.cpp
 * Implements a class FormulaVarIterator that iterates
 * over free variables in a formula or a term.
 *
 * @since 06/01/2004, Manchester
 * @since 02/09/2009 Redmond, reimplemented to work with non-rectified
 * formulas and return each variable only once
 * @since 15/05/2015 Gothenburg, FOOL support added
 */

#include "Debug/Tracer.hpp"

#include "FormulaVarIterator.hpp"

using namespace Lib;
using namespace Kernel;

/**
 * Build an iterator over f.
 * @since 02/09/2009 Redmond
 */
FormulaVarIterator::FormulaVarIterator(const Formula* f)
  : _found(false)
{
  _instructions.push(FVI_FORMULA);
  _formulas.push(f);
} // FormulaVarIterator::FormulaVarIterator

/**
 * Build an iterator over a term.
 * @since 15/05/2015 Gothenburg
 */
FormulaVarIterator::FormulaVarIterator(const Term* t)
  : _found(false)
{
  CALL("FormulaVarIterator::FormulaVarIterator(Term*)");
  _instructions.push(FVI_TERM);
  _terms.push(t);
} // FormulaVarIterator::FormulaVarIterator

/**
 * Build an iterator over a list of terms.
 * @since 15/05/2015 Gothenburg
 */
FormulaVarIterator::FormulaVarIterator(const TermList* ts)
  : _found(false)
{
  CALL("FormulaVarIterator::FormulaVarIterator(TermList)");
  _instructions.push(FVI_TERM_LIST);
  _termLists.push(*ts);
} // FormulaVarIterator::FormulaVarIterator

/**
 * Return the next free variable.
 * @since 06/01/2004 Manchester
 */
unsigned FormulaVarIterator::next()
{
  CALL("FormulaVarIterator::next");

  ASS(_found);
  _found = false;
  return _nextVar;
} // FormulaVarIterator::next

/**
 * True if there is the next free variable.
 * @since 06/01/2004 Manchester
 * @since 11/12/2004 Manchester, true and false added
 * @since 15/05/2015 Gothenburg, FOOL support added
 */
bool FormulaVarIterator::hasNext()
{
  CALL("FormulaVarIterator::hasNext");

  if (_found) return true;

  while (_instructions.isNonEmpty()) {
    switch (_instructions.pop()) {
      case FVI_FORMULA: {
        const Formula* f = _formulas.pop();
        switch (f->connective()) {
          case LITERAL: { 
            Literal* lit = const_cast<Literal*>(f->literal());
            if(lit->isTwoVarEquality()){
              _instructions.push(FVI_TERM_LIST);
              _termLists.push(lit->twoVarEqSort());              
            }
            _instructions.push(FVI_TERM);
            _terms.push(lit);
            break;
          }

          case AND:
          case OR: {
            FormulaList::Iterator fs(f->args());
            while (fs.hasNext()) {
              _instructions.push(FVI_FORMULA);
              _formulas.push(fs.next());
            }
            break;
          }

          case IMP:
          case IFF:
          case XOR:
            _instructions.push(FVI_FORMULA);
            _formulas.push(f->left());
            _instructions.push(FVI_FORMULA);
            _formulas.push(f->right());
            break;

          case NOT:
            _instructions.push(FVI_FORMULA);
            _formulas.push(f->uarg());
            break;

          case FORALL:
          case EXISTS:
            _instructions.push(FVI_UNBIND);
            _instructions.push(FVI_FORMULA);
            _formulas.push(f->qarg());
            _instructions.push(FVI_BIND);
            _vars.push(f->vars());
            break;

          case BOOL_TERM:
            _instructions.push(FVI_TERM_LIST);
            _termLists.push(f->getBooleanTerm());
            break;

          case TRUE:
          case FALSE:
          case NAME:
            break;
          default:
            ASSERTION_VIOLATION;
        }
        break;
      }

      case FVI_TERM: {
        const Term* t = _terms.pop();

        // TODO: is there a better iterator over arguments of const Term*?
        Term::Iterator ts(const_cast<Term*>(t));
        while (ts.hasNext()) {
          _instructions.push(FVI_TERM_LIST);
          _termLists.push(ts.next());
        }

        if (t->isSpecial()) {
          const Term::SpecialTermData* sd = t->getSpecialData();
          switch (t->functor()) {
            case Term::SF_ITE:
              _instructions.push(FVI_FORMULA);
              _formulas.push(sd->getCondition());
              break;

            case Term::SF_FORMULA:
              _instructions.push(FVI_FORMULA);
              _formulas.push(sd->getFormula());
              break;

            case Term::SF_LET: {
              _instructions.push(FVI_UNBIND);

              _instructions.push(FVI_TERM_LIST);
              _termLists.push(sd->getBinding());

              _instructions.push(FVI_BIND);
              _vars.push(sd->getVariables());

              break;
            }

            case Term::SF_LET_TUPLE: {
              _instructions.push(FVI_TERM_LIST);
              _termLists.push(sd->getBinding());
              break;
            }

            case Term::SF_TUPLE: {
              Term* tt = sd->getTupleTerm();
              Term::Iterator tts(tt);
              while (tts.hasNext()) {
                _instructions.push(FVI_TERM_LIST);
                _termLists.push(tts.next());
              }
              break;
            }
      
            case Term::SF_LAMBDA:{
              _instructions.push(FVI_UNBIND);
              SList* sorts = sd->getLambdaVarSorts();
              while(sorts){
                _instructions.push(FVI_TERM_LIST);
                _termLists.push(sorts->head());
                sorts = sorts->tail();
              }
              _instructions.push(FVI_TERM_LIST);
              _termLists.push(sd->getLambdaExpSort());
              _instructions.push(FVI_TERM_LIST);
              _termLists.push(sd->getLambdaExp());
              _instructions.push(FVI_BIND);
              _vars.push(sd->getLambdaVars());
              break;
            }

            case Term::SF_MATCH: {
              for (unsigned int i = 0; i < t->arity(); i++) {
                _instructions.push(FVI_TERM_LIST);
                _termLists.push(*t->nthArgument(i));
              }
              break;
            }

#if VDEBUG
            default:
              ASSERTION_VIOLATION;
#endif
          }
        }

        break;
      }

      case FVI_TERM_LIST: {
        TermList ts = _termLists.pop();
        if (ts.isVar()) {
          unsigned var = ts.var();
          if (!_free.get(var) && !_bound.get(var)) {
            _nextVar = var;
            _found = true;
            _free.inc(var);
            return true;
          }
        } else {
          _instructions.push(FVI_TERM);
          _terms.push(ts.term());
        }
        break;
      }

      case FVI_BIND: {
        VList::Iterator vs(_vars.top());
        while (vs.hasNext()) {
          _bound.inc(vs.next());
        }
        break;
      }

      case FVI_UNBIND: {
        VList::Iterator vs(_vars.pop());
        while (vs.hasNext()) {
          _bound.dec(vs.next());
        }
        break;
      }
    }
  }

  return false;
} // FormulaVarIterator::hasNext
