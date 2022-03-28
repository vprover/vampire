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
 * @file Naming.cpp
 * Implements the naming technique
 * @since 05/05/2005 Manchester
 * @since 07/07/2007 Manchester, changed to new datastructures
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"
#include "Shell/NameReuse.hpp"

#include "Indexing/TermSharing.hpp"

#include "Naming.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * Initialise a naming.
 * @param threshold Must be between 1 and 32767. If a non-unit clause is
 *   going to be used the number of times greater than the threshold,
 *   it will be named.
 * @param preserveEpr If true, names will not be introduced if it would
 *   lead to introduction of non-constant Skolem functions.
 */
Naming::Naming(int threshold, bool preserveEpr, bool appify) :
    _threshold(threshold + 1), _preserveEpr(preserveEpr), 
    _appify(appify), _varsInScope(false) {
  ASS(threshold < 32768);
} // Naming::Naming

/**
 * Apply naming to a unit.
 *
 * @warning @b unit must not be a clause
 * @warning @b unit must not have any free variables
 * @since 13/07/2005 Haifa
 * @since 14/07/2005 Tel-Aviv airport, changed to replace the unit
 */
FormulaUnit* Naming::apply(FormulaUnit* unit, UnitList*& defs) {
  CALL("Naming::apply(Unit*)");
  ASS(!unit->isClause());
  ASS_REP(unit->formula()->freeVariables() == 0, *unit);
  ASS(!_varsInScope); //_varsInScope can be true only when traversing inside a formula

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] naming args: " << unit->toString() << std::endl;
    env.endOutput();
  }

  Formula* f = unit->formula();
  switch (f->connective()) {
  case TRUE:
  case FALSE:
    defs = UnitList::empty();
    return unit;
  default:
    break;
  }

  _defs = UnitList::empty();

  // The original recursive call was here:

  // int pos;
  // int neg;
  // Formula* g = apply_sub(f,ON_TOP,pos,neg);

  Formula* g = apply_iter(f);

  if (f == g) { // not changed
    ASS(UnitList::isEmpty(_defs));
    defs = UnitList::empty();
    return unit;
  }
  ASS(UnitList::isNonEmpty(_defs) || env.options->definitionReuse());
  UnitList::Iterator defit(_defs);

  defs = _defs;
  UnitList* premises = UnitList::copy(_defs);
  UnitList::push(unit, premises);
  return new FormulaUnit(g,
      FormulaTransformationMany(InferenceRule::DEFINITION_FOLDING, premises));
} // Naming::apply

Formula* Naming::apply_iter(Formula* top_f) {
  CALL("Naming::apply_iter");

  TimeCounter tc(TC_NAMING);

  Stack<Task> todo_stack;
  Stack<Result> result_stack;

  {
    Task t;
    t.fncTag = APPLY_SUB_TOP;
    t.taskApplySub = {top_f, ON_TOP};
    todo_stack.push(t);
  }

  while(todo_stack.isNonEmpty()) {
    // Careful: this is a potentially risky practice,
    // referencess to the stack become invalid after push !!!
    Task& t = todo_stack.top();

    switch (t.fncTag) {
    case APPLY_SUB_TOP: {
      TaskApplySub& tas = t.taskApplySub;

      switch (tas.f->connective()) {
      case LITERAL: {
        Result r;
        r.resSub = {1,1,tas.f};
        result_stack.push(r);
        todo_stack.pop(); // finished with the current Task
      } break;

      case BOOL_TERM:
        ASSERTION_VIOLATION;

      case AND: {
        FormulaList* fs = tas.f->args();
        unsigned length = FormulaList::length(fs);
        void* mem = ALLOC_UNKNOWN(length * sizeof(int), "Naming::apply");
        int* cls = array_new<int>(mem, length);
        int* negCls = 0;
        if (tas.where == UNDER_IFF) {
          mem = ALLOC_UNKNOWN(length * sizeof(int), "Naming::apply");
          negCls = array_new<int>(mem, length);
        }

        t.fncTag = APPLY_SUB_AND;
        tas.taskAndOr = {cls,negCls};

        // fs = apply_list(fs, where, cls, negCls);
        Task t_new;
        t_new.fncTag = APPLY_LIST_TOP;
        t_new.taskApplyList = {fs,tas.where,cls,negCls};

        todo_stack.push(t_new);
      } break;

      case OR: {
        FormulaList* fs = tas.f->args();
        unsigned length = FormulaList::length(fs);
        void* mem = ALLOC_UNKNOWN(length * sizeof(int), "Naming::apply");
        int* cls = array_new<int>(mem, length);
        int* negCls = 0;
        if (tas.where == UNDER_IFF) {
          mem = ALLOC_UNKNOWN(length * sizeof(int), "Naming::apply");
          negCls = array_new<int>(mem, length);
        }
        if (tas.where == ON_TOP) {
          tas.where = OTHER;
        }

        t.fncTag = APPLY_SUB_OR;
        tas.taskAndOr = {cls,negCls};

        // fs = apply_list(fs, where, cls, negCls);
        Task t_new;
        t_new.fncTag = APPLY_LIST_TOP;
        t_new.taskApplyList = {fs,tas.where,cls,negCls};

        todo_stack.push(t_new);
      } break;

      case IFF:
      case XOR: {
        //there is no need to call the canBeInDefinition function here, since
        //the arguments will in the end appear both positive and negative anyway

        Formula* f = tas.f; // important to have the copy, we touch f after push!

        /*
        if (con == IFF) {
          l = apply_sub(f->left(), UNDER_IFF, posl, negl);
          r = apply_sub(f->right(), UNDER_IFF, posr, negr);
        } else {
          l = apply_sub(f->left(), UNDER_IFF, negl, posl);
          r = apply_sub(f->right(), UNDER_IFF, negr, posr);
        }
        */

        t.fncTag = APPLY_SUB_IFFXOR;
        {
          Task t_new;
          t_new.fncTag = APPLY_SUB_TOP;
          t_new.taskApplySub.where = UNDER_IFF;

          // left done first; must be pushed later
          t_new.taskApplySub.f = f->right();
          todo_stack.push(t_new);
          t_new.taskApplySub.f = f->left();
          todo_stack.push(t_new);
        }
      } break;

      case FORALL:
      case EXISTS: {
        tas.taskForallExists.varFlagSet = tas.f->connective() == FORALL && !_varsInScope;
        if (tas.taskForallExists.varFlagSet) {
          _varsInScope = true;
        }

        // Formula* g = apply_sub(f->qarg(), where, pos, neg);
        t.fncTag = APPLY_SUB_FORALLEXISTS;
        {
          Task t_new;
          t_new.fncTag = APPLY_SUB_TOP;
          t_new.taskApplySub = {tas.f->qarg(),tas.where};

          todo_stack.push(t_new);
        }
      } break;
      default:
        ASSERTION_VIOLATION_REP(*tas.f);
      }
    } break;

    case APPLY_SUB_AND: {
      TaskApplySub& tas = t.taskApplySub;
      SubtaskAndOr& sand = tas.taskAndOr;

      Formula* f = tas.f;
      FormulaList* fs = f->args();
      unsigned length = FormulaList::length(fs);

      // fs = apply_list(fs, where, cls, negCls);
      {
        Result r = result_stack.pop();
        fs = r.resList.res;
      }

      bool split = false;
      // formula array, initialised only upon demand
      Formula** gs = 0;
      // WARNING: QUADRATIC ALGORITHM BELOW, SHOULD BE IMPROVED
      for (;;) {
        int sum = 0; // result: the sum of all members
        int product = 1;
        int maxPos = 0;
        int maxNeg = 0;
        int maxPosIndex = 0;
        int maxNegIndex = 0;
        FormulaList* currArg = f->args();
        for (unsigned i = 0; i < length; i++) {
          int c = sand.cls[i];
          sum = Int::min(_threshold, sum + c);
          bool canBeDefEvaluated = false;
          bool canBeDef;
          if (c > maxPos) {
            canBeDefEvaluated = true;
            canBeDef = canBeInDefinition(currArg->head(), tas.where);
            if (canBeDef) {
              maxPos = c;
              maxPosIndex = i;
            }
          }
          if (tas.where == UNDER_IFF) {
            int d = sand.negCls[i];
            product = Int::min(_threshold, product * d);
            if (d > maxNeg) {
              if (!canBeDefEvaluated) {
                canBeDef = canBeInDefinition(currArg->head(), tas.where);
              }
              if (canBeDef) {
                maxNeg = d;
                maxNegIndex = i;
              }
            }
          }
          currArg = currArg->tail();
        }
        ASS(currArg == 0);
        ASS(maxPos > 0 || _preserveEpr);
        ASS(tas.where != UNDER_IFF || maxNeg > 0);
        // splitWhat & 1 => split due to the positive part
        // splitWhat & 2 => split due to the negative part
        int splitWhat = 0;
        if (tas.where != UNDER_IFF || product > 1) { // not all formulas are atomic
          if (tas.where != ON_TOP && maxPos > 1 && sum >= _threshold) {
            splitWhat |= 1;
          }
          if (tas.where == UNDER_IFF && product >= _threshold && maxNeg > 1) {
            splitWhat |= 2;
          }
        }
        if (!splitWhat) { // no more splits
          if (split) {
            FormulaList* rs = FormulaList::empty();
            for (int i = length - 1; i >= 0; i--) {
              FormulaList::push(gs[i], rs);
            }
            f = new JunctionFormula(AND, rs);
            DEALLOC_UNKNOWN(gs, "Naming::apply");
          } else if (fs != f->args()) {
            f = new JunctionFormula(AND, fs);
          }
          DEALLOC_UNKNOWN(sand.cls, "Naming::apply");
          if (sand.negCls) {
            DEALLOC_UNKNOWN(sand.negCls, "Naming::apply");
          }

          {
            Result r;
            r.resSub.neg = product;
            r.resSub.pos = sum;
            r.resSub.res = f;
            result_stack.push(r);
          }

          todo_stack.pop();  // finished
          break; // for (;;)
        }

        // conjunction under disjunction or IFF, should be split
        split = true;
        if (!gs) {
          void* mem = ALLOC_UNKNOWN(length * sizeof(Formula*), "Naming::apply");
          gs = array_new<Formula*>(mem, length);
          int j = 0;
          FormulaList::Iterator hs(fs);
          while (hs.hasNext()) {
            gs[j] = hs.next();
            j++;
          }
        }
        // gs has been initialised
        int maxIndex =
            splitWhat == 1 || (splitWhat == 3 && sum > product) || maxNeg == 1 ?
                maxPosIndex : maxNegIndex;

        Formula* nm = introduceDefinition(gs[maxIndex], tas.where == UNDER_IFF);
        gs[maxIndex] = nm;
        sand.cls[maxIndex] = 1;
        if (tas.where == UNDER_IFF) {
          sand.negCls[maxIndex] = 1;
        }
      } // for (;;)
    } break;

    case APPLY_SUB_OR: {
      TaskApplySub& tas = t.taskApplySub;
      SubtaskAndOr& sor = tas.taskAndOr;

      Formula* f = tas.f;
      FormulaList* fs = f->args();
      unsigned length = FormulaList::length(fs);

      // fs = apply_list(fs, where, cls, negCls);
      {
        Result r = result_stack.pop();
        fs = r.resList.res;
      }

      bool split = false;
      // formula array, initialised only upon demand
      Formula** gs = 0;
      // WARNING: QUADRATIC ALGORITHM BELOW, SHOULD BE IMPROVED
      for (;;) {
        int sum = 0; // result: the sum of all members
        int product = 1;
        int maxPos = 0;
        int maxNeg = 0;
        int maxPosIndex = 0;
        int maxNegIndex = 0;
        FormulaList* currArg = f->args();
        for (unsigned i = 0; i < length; i++) {
          int c = sor.cls[i];
          product = Int::min(_threshold, product * c);
          bool canBeDefEvaluated = false;
          bool canBeDef;
          if (c > maxPos) {
            canBeDefEvaluated = true;
            canBeDef = canBeInDefinition(currArg->head(), tas.where);
            if (canBeDef) {
              maxPos = c;
              maxPosIndex = i;
            }
          }
          if (tas.where == UNDER_IFF) {
            int d = sor.negCls[i];
            sum = Int::min(_threshold, sum + d);
            if (d > maxNeg) {
              if (!canBeDefEvaluated) {
                canBeDef = canBeInDefinition(currArg->head(), tas.where);
              }
              if (canBeDef) {
                maxNeg = d;
                maxNegIndex = i;
              }
            }
          }
          currArg = currArg->tail();
        }
        ASS(currArg == 0);
        ASS(maxPos > 0 || _preserveEpr);
        ASS(tas.where != UNDER_IFF || maxNeg > 0);
        // splitWhat & 1 => split due to the positive part
        // splitWhat & 2 => split due to the negative part
        int splitWhat = 0;
        if (maxPos > 0 && (tas.where != UNDER_IFF || product > 1)) { // not all formulas are atomic
          if (product >= _threshold && maxPos > 1) {
            splitWhat |= 1;
          }
          if (tas.where == UNDER_IFF && sum >= _threshold && maxNeg > 1) {
            splitWhat |= 2;
          }
        }
        if (!splitWhat) { // no more splits
          if (split) {
            FormulaList* rs = FormulaList::empty();
            for (int i = length - 1; i >= 0; i--) {
              FormulaList::push(gs[i], rs);
            }
            f = new JunctionFormula(OR, rs);
            DEALLOC_UNKNOWN(gs, "Naming::apply");
          } else if (fs != f->args()) {
            f = new JunctionFormula(OR, fs);
          }
          DEALLOC_UNKNOWN(sor.cls, "Naming::apply");
          if (sor.negCls) {
            DEALLOC_UNKNOWN(sor.negCls, "Naming::apply");
          }

          {
            Result r;
            r.resSub.neg = sum;
            r.resSub.pos = product;
            r.resSub.res = f;
            result_stack.push(r);
          }

          todo_stack.pop();  // finished
          break; // for (;;)
        }

        // splitWhat != 0
        split = true;
        if (!gs) {
          void* mem = ALLOC_UNKNOWN(length * sizeof(Formula*), "Naming::apply");
          gs = array_new<Formula*>(mem, length);

          int j = 0;
          FormulaList::Iterator hs(fs);
          while (hs.hasNext()) {
            gs[j] = hs.next();
            j++;
          }
        }
        // gs has been initialised
        int maxIndex =
            splitWhat == 1 || (splitWhat == 3 && product > sum) || maxNeg == 1 ?
                maxPosIndex : maxNegIndex;

        Formula* nm = introduceDefinition(gs[maxIndex], tas.where == UNDER_IFF);
        gs[maxIndex] = nm;
        sor.cls[maxIndex] = 1;
        if (tas.where == UNDER_IFF) {
          sor.negCls[maxIndex] = 1;
        }
      } // for (;;)

    } break;

    case APPLY_SUB_IFFXOR: {
      TaskApplySub& tas = t.taskApplySub;

      Formula* f = tas.f;
      int negl;
      int posl;
      int negr;
      int posr;
      Connective con = f->connective();
      Formula* l;
      Formula* r;

      /*
      if (con == IFF) {
        l = apply_sub(f->left(), UNDER_IFF, posl, negl);
        r = apply_sub(f->right(), UNDER_IFF, posr, negr);
      } else {
        l = apply_sub(f->left(), UNDER_IFF, negl, posl);
        r = apply_sub(f->right(), UNDER_IFF, negr, posr);
      }
      */

      {
        Result rr = result_stack.pop();
        r = rr.resSub.res;
        if (con == IFF) {
          posr = rr.resSub.pos;
          negr = rr.resSub.neg;
        } else {
          negr = rr.resSub.pos;
          posr = rr.resSub.neg;
        }
        Result lr = result_stack.pop();
        l = lr.resSub.res;
        if (con == IFF) {
          posl = lr.resSub.pos;
          negl = lr.resSub.neg;
        } else {
          negl = lr.resSub.pos;
          posl = lr.resSub.neg;
        }
      }

      if (tas.where == ON_TOP
          && ((posl == 1 && posr == 1) || (negl == 1 && negr == 1))) {
        if (l != f->left() || r != f->right()) {
          f = new BinaryFormula(con, l, r);
        }

        // pos = Int::min(_threshold, Int::max(posl, posr));
        // return f;

        {
          Result r;
          r.resSub.pos = Int::min(_threshold, Int::max(posl, posr));
          r.resSub.res = f;
          result_stack.push(r);
        }

        todo_stack.pop();  // finished
        break; // case APPLY_SUB_IFFXOR
      }
      int pos = Int::min(negl * posr + negr * posl, _threshold);
      int neg = Int::min(posl * posr + negl * negr, _threshold);
      bool left; // name left
      if (pos < _threshold) {
        if (tas.where != UNDER_IFF || neg < _threshold) {
          if (l != f->left() || r != f->right()) {
            f = new BinaryFormula(con, l, r);
          }
          // return f
          {
            Result r;
            r.resSub.pos = pos;
            r.resSub.neg = neg;
            r.resSub.res = f;
            result_stack.push(r);
          }

          todo_stack.pop();  // finished
          break; // case APPLY_SUB_IFFXOR
        }
        // must be split because of the neg
        left = posl * posr > negl * negr ? (posl >= posr) : (negl >= negr);
      } else { // pos == threshold
        left = negl * posr > negr * posl ? (negl >= posr) : (posl >= negr);
        // checking if both must be named
        bool splitBoth =
            left ? (posr + negr >= _threshold) : (posl + negl >= _threshold);
        if (splitBoth) {
          Formula* newl = introduceDefinition(l, true);
          Formula* newr = introduceDefinition(r, true);
          f = new BinaryFormula(con, newl, newr);

          // neg = 2;
          // pos = 2;
          // return f;
          {
            Result r;
            r.resSub = {2,2,f};
            result_stack.push(r);
          }

          todo_stack.pop();  // finished
          break; // case APPLY_SUB_IFFXOR
        }
      }

      if (left) {
        Formula* newl = introduceDefinition(l, true);
        f = new BinaryFormula(con, newl, r);
        // neg = Int::min(posr + negr, _threshold);
        // pos = neg;
        // return f;
        {
          Result r;
          r.resSub.neg = Int::min(posr + negr, _threshold);
          r.resSub.pos = neg;
          r.resSub.res = f;
          result_stack.push(r);
        }

        todo_stack.pop();  // finished
        break; // case APPLY_SUB_IFFXOR
      }

      Formula* newr = introduceDefinition(r, true);
      f = new BinaryFormula(con, l, newr);
      // neg = Int::min(posl + negl, _threshold);
      // pos = neg;
      // return f;
      {
        Result r;
        r.resSub.neg = Int::min(posl + negl, _threshold);
        r.resSub.pos = neg;
        r.resSub.res = f;
        result_stack.push(r);
      }
      todo_stack.pop();  // finished
    } break;

    case APPLY_SUB_FORALLEXISTS: {
      TaskApplySub& tas = t.taskApplySub;
      SubtaskForallExists& tfe = t.taskApplySub.taskForallExists;

      Formula* f = tas.f;
      Formula* g;
      int pos;
      int neg;

      // Formula* g = apply_sub(f->qarg(), where, pos, neg);
      {
        Result r = result_stack.pop();
        g = r.resSub.res;
        pos = r.resSub.pos;
        neg = r.resSub.neg;
      }
      ASS(pos <= _threshold || _preserveEpr);
      if (g != f->qarg()) {
        f = new QuantifiedFormula(f->connective(), f->vars(),f->sorts(), g);
      }
      if (tfe.varFlagSet) {
        _varsInScope = false;
      }
      // return f;
      {
        Result r;
        r.resSub.pos = pos;
        r.resSub.neg = neg;
        r.resSub.res = f;
        result_stack.push(r);
      }

      todo_stack.pop();  // finished
    } break;

    case APPLY_LIST_TOP: {
      TaskApplyList& tal = t.taskApplyList;

      if (FormulaList::isEmpty(tal.fs)) {
        Result r;
        r.resList.res = tal.fs;
        result_stack.push(r);

        todo_stack.pop();  // finished
      } else {
        // two subcalls, in reverse order:

        t.fncTag = APPLY_LIST_POST;

        // FormulaList* gs = apply_list(fs->tail(), where, results + 1, negResults + 1);
        Task t1;
        t1.fncTag = APPLY_LIST_TOP;
        t1.taskApplyList = {tal.fs->tail(),tal.where,tal.results+1,tal.negResults+1};

        // Formula* g = apply_sub(fs->head(), where, results[0], neg);
        Task t2;
        t2.fncTag = APPLY_SUB_TOP;
        t2.taskApplySub = {tal.fs->head(),tal.where};

        todo_stack.push(t1);
        todo_stack.push(t2);
      }
    } break;

    case APPLY_LIST_POST: {
      TaskApplyList& tal = t.taskApplyList;
      FormulaList* fs = tal.fs;

      // retrieve results for the two recursive calls (again fetched in reversed order)

      // FormulaList* gs = apply_list(fs->tail(), where, results + 1, negResults + 1);
      FormulaList* gs = result_stack.pop().resList.res;

      // Formula* g = apply_sub(fs->head(), where, results[0], neg);
      Formula* g;
      {
        Result r = result_stack.pop();
        g = r.resSub.res;
        tal.results[0] = r.resSub.pos;
        if (tal.where == UNDER_IFF) {
          tal.negResults[0] = r.resSub.neg;
        }
      }
      if (g != fs->head() || gs != fs->tail()) {
        fs = new FormulaList(g, gs);
      }

      // return fs;
      {
        Result r;
        r.resList.res = fs;
        result_stack.push(r);
      }
      todo_stack.pop();  // finished
    } break;

    default:
      ASSERTION_VIOLATION;
    }
  }

  ASS_EQ(result_stack.size(),1);
  return result_stack.top().resSub.res;
}

/**
 * Apply naming to a subformula.
 *
 * @param f the subformula, it must be in ENNF and different from TRUE
 *    and FALSE
 * @param where describes the position of the subformula
 * @param pos return the number of clauses resulting in converting f to CNF
 * @param neg return the number of clauses resulting in converting ~f to CNF
 * @since 01/07/2005 Manchester
 * @since 11/07/2005 flight Barcelona-Tel-Aviv
 */
Formula* Naming::apply_sub(Formula* f, Where where, int& pos, int& neg) {
  CALL("Naming::apply_sub(Formula* ...)");

  switch (f->connective()) {
  case LITERAL:
  case BOOL_TERM:
    pos = 1;
    neg = 1;
    return f;

  case AND: {
    FormulaList* fs = f->args();
    unsigned length = FormulaList::length(fs);
    void* mem = ALLOC_UNKNOWN(length * sizeof(int), "Naming::apply");
    int* cls = array_new<int>(mem, length);
    int* negCls = 0;
    if (where == UNDER_IFF) {
      mem = ALLOC_UNKNOWN(length * sizeof(int), "Naming::apply");
      negCls = array_new<int>(mem, length);
    }
    fs = apply_list(fs, where, cls, negCls);
    bool split = false;
    // formula array, initialised only upon demand
    Formula** gs = 0;
    // WARNING: QUADRATIC ALGORITHM BELOW, SHOULD BE IMPROVED
    for (;;) {
      int sum = 0; // result: the sum of all members
      int product = 1;
      int maxPos = 0;
      int maxNeg = 0;
      int maxPosIndex = 0;
      int maxNegIndex = 0;
      FormulaList* currArg = f->args();
      for (unsigned i = 0; i < length; i++) {
        int c = cls[i];
        sum = Int::min(_threshold, sum + c);
        bool canBeDefEvaluated = false;
        bool canBeDef;
        if (c > maxPos) {
          canBeDefEvaluated = true;
          canBeDef = canBeInDefinition(currArg->head(), where);
          if (canBeDef) {
            maxPos = c;
            maxPosIndex = i;
          }
        }
        if (where == UNDER_IFF) {
          int d = negCls[i];
          product = Int::min(_threshold, product * d);
          if (d > maxNeg) {
            if (!canBeDefEvaluated) {
              canBeDef = canBeInDefinition(currArg->head(), where);
            }
            if (canBeDef) {
              maxNeg = d;
              maxNegIndex = i;
            }
          }
        }
        currArg = currArg->tail();
      }
      ASS(currArg == 0);
      ASS(maxPos > 0 || _preserveEpr);
      ASS(where != UNDER_IFF || maxNeg > 0);
      // splitWhat & 1 => split due to the positive part
      // splitWhat & 2 => split due to the negative part
      int splitWhat = 0;
      if (where != UNDER_IFF || product > 1) { // not all formulas are atomic
        if (where != ON_TOP && maxPos > 1 && sum >= _threshold) {
          splitWhat |= 1;
        }
        if (where == UNDER_IFF && product >= _threshold && maxNeg > 1) {
          splitWhat |= 2;
        }
      }
      if (!splitWhat) { // no more splits
        if (split) {
          FormulaList* rs = FormulaList::empty();
          for (int i = length - 1; i >= 0; i--) {
            FormulaList::push(gs[i], rs);
          }
          f = new JunctionFormula(AND, rs);
          DEALLOC_UNKNOWN(gs, "Naming::apply");
        } else if (fs != f->args()) {
          f = new JunctionFormula(AND, fs);
        }
        DEALLOC_UNKNOWN(cls, "Naming::apply");
        if (negCls) {
          DEALLOC_UNKNOWN(negCls, "Naming::apply");
        }
        neg = product;
        pos = sum;
        return f;
      }

      // conjunction under disjunction or IFF, should be split
      split = true;
      if (!gs) {
        void* mem = ALLOC_UNKNOWN(length * sizeof(Formula*), "Naming::apply");
        gs = array_new<Formula*>(mem, length);
        int j = 0;
        FormulaList::Iterator hs(fs);
        while (hs.hasNext()) {
          gs[j] = hs.next();
          j++;
        }
      }
      // gs has been initialised
      int maxIndex =
          splitWhat == 1 || (splitWhat == 3 && sum > product) || maxNeg == 1 ?
              maxPosIndex : maxNegIndex;
      Formula* nm = introduceDefinition(gs[maxIndex], where == UNDER_IFF);
      gs[maxIndex] = nm;
      cls[maxIndex] = 1;
      if (where == UNDER_IFF) {
        negCls[maxIndex] = 1;
      }
    } // for (;;)
  } // case AND

  case OR: {
    FormulaList* fs = f->args();
    unsigned length = FormulaList::length(fs);
    void* mem = ALLOC_UNKNOWN(length * sizeof(int), "Naming::apply");
    int* cls = array_new<int>(mem, length);
    int* negCls = 0;
    if (where == UNDER_IFF) {
      mem = ALLOC_UNKNOWN(length * sizeof(int), "Naming::apply");
      negCls = array_new<int>(mem, length);
    }
    if (where == ON_TOP) {
      where = OTHER;
    }
    fs = apply_list(fs, where, cls, negCls);
    bool split = false;
    // formula array, initialised only upon demand
    Formula** gs = 0;
    // WARNING: QUADRATIC ALGORITHM BELOW, SHOULD BE IMPROVED
    for (;;) {
      int sum = 0; // result: the sum of all members
      int product = 1;
      int maxPos = 0;
      int maxNeg = 0;
      int maxPosIndex = 0;
      int maxNegIndex = 0;
      FormulaList* currArg = f->args();
      for (unsigned i = 0; i < length; i++) {
        int c = cls[i];
        product = Int::min(_threshold, product * c);
        bool canBeDefEvaluated = false;
        bool canBeDef;
        if (c > maxPos) {
          canBeDefEvaluated = true;
          canBeDef = canBeInDefinition(currArg->head(), where);
          if (canBeDef) {
            maxPos = c;
            maxPosIndex = i;
          }
        }
        if (where == UNDER_IFF) {
          int d = negCls[i];
          sum = Int::min(_threshold, sum + d);
          if (d > maxNeg) {
            if (!canBeDefEvaluated) {
              canBeDef = canBeInDefinition(currArg->head(), where);
            }
            if (canBeDef) {
              maxNeg = d;
              maxNegIndex = i;
            }
          }
        }
        currArg = currArg->tail();
      }
      ASS(currArg == 0);
      ASS(maxPos > 0 || _preserveEpr);
      ASS(where != UNDER_IFF || maxNeg > 0);
      // splitWhat & 1 => split due to the positive part
      // splitWhat & 2 => split due to the negative part
      int splitWhat = 0;
      if (maxPos > 0 && (where != UNDER_IFF || product > 1)) { // not all formulas are atomic
        if (product >= _threshold && maxPos > 1) {
          splitWhat |= 1;
        }
        if (where == UNDER_IFF && sum >= _threshold && maxNeg > 1) {
          splitWhat |= 2;
        }
      }
      if (!splitWhat) { // no more splits
        if (split) {
          FormulaList* rs = FormulaList::empty();
          for (int i = length - 1; i >= 0; i--) {
            FormulaList::push(gs[i], rs);
          }
          f = new JunctionFormula(OR, rs);
          DEALLOC_UNKNOWN(gs, "Naming::apply");
        } else if (fs != f->args()) {
          f = new JunctionFormula(OR, fs);
        }
        DEALLOC_UNKNOWN(cls, "Naming::apply");
        if (negCls) {
          DEALLOC_UNKNOWN(negCls, "Naming::apply");
        }
        neg = sum;
        pos = product;
        return f;
      }

      // splitWhat != 0
      split = true;
      if (!gs) {
        void* mem = ALLOC_UNKNOWN(length * sizeof(Formula*), "Naming::apply");
        gs = array_new<Formula*>(mem, length);
        int j = 0;
        FormulaList::Iterator hs(fs);
        while (hs.hasNext()) {
          gs[j] = hs.next();
          j++;
        }
      }
      // gs has been initialised
      int maxIndex =
          splitWhat == 1 || (splitWhat == 3 && product > sum) || maxNeg == 1 ?
              maxPosIndex : maxNegIndex;
      Formula* nm = introduceDefinition(gs[maxIndex], where == UNDER_IFF);
      gs[maxIndex] = nm;
      cls[maxIndex] = 1;
      if (where == UNDER_IFF) {
        negCls[maxIndex] = 1;
      }
    } // for (;;)
  } // case OR

  case IFF:
  case XOR: {
    //there is no need to call the canBeInDefinition function here, since
    //the arguments will in the end appear both positive and negative anyway

    int negl;
    int posl;
    int negr;
    int posr;
    Connective con = f->connective();
    Formula* l;
    Formula* r;
    if (con == IFF) {
      l = apply_sub(f->left(), UNDER_IFF, posl, negl);
      r = apply_sub(f->right(), UNDER_IFF, posr, negr);
    } else {
      l = apply_sub(f->left(), UNDER_IFF, negl, posl);
      r = apply_sub(f->right(), UNDER_IFF, negr, posr);
    }
    if (where == ON_TOP
        && ((posl == 1 && posr == 1) || (negl == 1 && negr == 1))) {
      if (l != f->left() || r != f->right()) {
        f = new BinaryFormula(con, l, r);
      }
      pos = Int::min(_threshold, Int::max(posl, posr));
      return f;
    }
    pos = Int::min(negl * posr + negr * posl, _threshold);
    neg = Int::min(posl * posr + negl * negr, _threshold);
    bool left; // name left
    if (pos < _threshold) {
      if (where != UNDER_IFF || neg < _threshold) {
        if (l != f->left() || r != f->right()) {
          f = new BinaryFormula(con, l, r);
        }

        return f;
      }
      // must be split because of the neg
      left = posl * posr > negl * negr ? (posl >= posr) : (negl >= negr);
    } else { // pos == threshold
      left = negl * posr > negr * posl ? (negl >= posr) : (posl >= negr);
      // checking if both must be named
      bool splitBoth =
          left ? (posr + negr >= _threshold) : (posl + negl >= _threshold);
      if (splitBoth) {
        Formula* newl = introduceDefinition(l, true);
        Formula* newr = introduceDefinition(r, true);
        f = new BinaryFormula(con, newl, newr);
        neg = 2;
        pos = 2;
        return f;
      }
    }

    if (left) {
      Formula* newl = introduceDefinition(l, true);
      f = new BinaryFormula(con, newl, r);
      neg = Int::min(posr + negr, _threshold);
      pos = neg;
      return f;
    }

    Formula* newr = introduceDefinition(r, true);
    f = new BinaryFormula(con, l, newr);
    neg = Int::min(posl + negl, _threshold);
    pos = neg;
    return f;
  }

  case FORALL:
  case EXISTS: {
    bool varFlagSet = f->connective() == FORALL && !_varsInScope;
    if (varFlagSet) {
      _varsInScope = true;
    }
    Formula* g = apply_sub(f->qarg(), where, pos, neg);
    ASS(pos <= _threshold || _preserveEpr);
    if (g != f->qarg()) {
      f = new QuantifiedFormula(f->connective(), f->vars(),f->sorts(), g);
    }
    if (varFlagSet) {
      _varsInScope = false;
    }
    return f;
  }

  default:
    ASSERTION_VIOLATION_REP(*f);
  }
} // Naming::apply

/**
 * Return true if a definition for the formula @b f may be introduced
 */
bool Naming::canBeInDefinition(Formula* f, Where where) {
  CALL("Naming::canBeInDefinition");

  if (!_preserveEpr) {
    return true;
  }

  bool unQuant = false;
  bool exQuant = false;
  SubformulaIterator sfit(f);
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    if (sf->connective() == FORALL) {
      unQuant = true;
    }
    if (sf->connective() == EXISTS) {
      exQuant = true;
    }
  }

  VList* fvars = f->freeVariables();
  bool freeVars = fvars;
  VList::destroy(fvars);

  if (!_varsInScope && freeVars
      && (exQuant || (unQuant && where == UNDER_IFF))) {
    return false;
  }

  return true;
}

Literal* Naming::getDefinitionLiteral(Formula* f, VList* freeVars) {
  CALL("Naming::getDefinitionLiteral");

  NameReuse *name_reuse = env.options->definitionReuse()
    ? NameReuse::definitionInstance()
    : nullptr;
  unsigned reused_symbol = 0;
  bool successfully_reused = false;
  vstring reuse_key;
  if(name_reuse) {
    reuse_key = name_reuse->key(f);
    successfully_reused = name_reuse->get(reuse_key, reused_symbol);
  }
  if(successfully_reused)
    env.statistics->reusedFormulaNames++;

  unsigned arity = VList::length(freeVars);

  static TermStack termVarSorts;
  static TermStack termVars;
  static TermStack typeVars;
  static DHMap<unsigned, TermList> varSorts;
  termVarSorts.reset();
  termVars.reset();
  typeVars.reset();
  varSorts.reset();

  SortHelper::collectVariableSorts(f, varSorts);

  // if we re-use a symbol, we _must_ close over free variables in some fixed order
  VirtualIterator<unsigned> keyOrderIt;
  if(name_reuse)
    keyOrderIt = name_reuse->freeVariablesInKeyOrder(f);

  VList::Iterator vit(freeVars);
  while (name_reuse ? keyOrderIt.hasNext() : vit.hasNext()) {
    unsigned uvar = name_reuse ? keyOrderIt.next() : vit.next();
    TermList sort = varSorts.get(uvar, AtomicSort::defaultSort());
    if(sort == AtomicSort::superSort()){
      typeVars.push(TermList(uvar, false));     
    } else {
      termVars.push(TermList(uvar, false));
      termVarSorts.push(sort);
    }
  }

  unsigned typeArgArity = typeVars.size();
  TermStack& allVars = typeVars;

  SortHelper::normaliseArgSorts(typeVars, termVarSorts);

  for(unsigned i = 0; i < termVars.size() && !_appify; i++){
    allVars.push(termVars[i]);
  }

  if(!_appify){
    unsigned pred = reused_symbol;
    if(!successfully_reused) {
      pred = env.signature->addNamePredicate(arity);
      env.statistics->formulaNames++;
      if(name_reuse)
        name_reuse->put(reuse_key, pred);
      Signature::Symbol* predSym = env.signature->getPredicate(pred);

      if (env.colorUsed) {
        Color fc = f->getColor();
        if (fc != COLOR_TRANSPARENT) {
          predSym->addColor(fc);
        }
        if (f->getSkip()) {
          predSym->markSkip();
        }
      }

      predSym->setType(OperatorType::getPredicateType(arity - typeArgArity, termVarSorts.begin(), typeArgArity));
    }
    return Literal::create(pred, arity, true, false, allVars.begin());
  } else {
    unsigned fun = reused_symbol;
    if(!successfully_reused) {
      fun = env.signature->addNameFunction(typeVars.size());
      TermList sort = AtomicSort::arrowSort(termVarSorts, AtomicSort::boolSort());
      Signature::Symbol* sym = env.signature->getFunction(fun);
      sym->setType(OperatorType::getConstantsType(sort, typeArgArity)); 
      if(name_reuse)
        name_reuse->put(reuse_key, fun);
    }
    TermList head = TermList(Term::create(fun, typeVars.size(), typeVars.begin()));
    TermList t = ApplicativeHelper::createAppTerm(
                 SortHelper::getResultSort(head.term()), head, termVars);
    return  Literal::createEquality(true, TermList(t), TermList(Term::foolTrue()), AtomicSort::boolSort());  
  }
}

/**
 * Introduce definition (A X)(p(X) &lt;-&gt; f), where X are all variables
 * of f and add it to _definitions. If @b iff is false, then the
 * definition is the ENNF of (A X)(~p(X) -&gt; f).
 *
 * @param f formula for which a name should be introduced
 * @param iff if true then the definition is an iff-definition
 * @returns placeholder for p(X)
 *
 * @since 01/07/2005 Manchester
 */
Formula* Naming::introduceDefinition(Formula* f, bool iff) {
  CALL("Naming::introduceDefinition");

  ASS_NEQ(f->connective(), LITERAL);
  ASS_NEQ(f->connective(), NOT);

  RSTAT_CTR_INC("naming_introduced_defs");

  VList* vs;
  vs = f->freeVariables();
  Literal* atom = getDefinitionLiteral(f, vs);
  Formula* name = new AtomicFormula(atom);

  // have we introduced this definition before?
  // if no, already_seen is nullptr
  // if yes, but only =>, *already_seen is false
  // if yes and <=>, *already_seen is true
  bool *already_seen = _already_seen.findPtr(atom);

  if(already_seen) {
    // either we don't need to "upgrade" the definition to <=>, or we already did
    if(!iff || *already_seen)
      return name;
  }

  Formula* def;
  if (iff) {
    // if we're upgrading a previously-seen definition, only need one direction
    if(already_seen)
      // this is not in ENNF, but the emitted definitions need not be
      // (Naming is followed by a NNF transform that can handle implications)
      def = new BinaryFormula(IMP, f, name);
    // otherwise we need both directions
    else
      def = new BinaryFormula(IFF, name, f);
  }
  // iff = false
  else {
    FormulaList* fs = f->connective() == OR ? f->args() : new FormulaList(f);
    Formula* nameFormula = new NegatedFormula(name);
    FormulaList::push(nameFormula, fs);
    def = new JunctionFormula(OR, fs);
  }
  if (VList::isNonEmpty(vs)) {
    //TODO do we know the sorts of the free variabls vs?
    def = new QuantifiedFormula(FORALL, vs, 0, def);
  }
  Unit* definition = new FormulaUnit(def, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::PREDICATE_DEFINITION));

  InferenceStore::instance()->recordIntroducedSymbol(definition, false,
      atom->functor());

  UnitList::push(definition, _defs);

  if(already_seen)
    // must be upgrading if we're here
    *already_seen = true;
  else
    _already_seen.insert(atom, iff);

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] naming defs: " << definition->toString() << std::endl;
    env.endOutput();
  }

  return name;
} // Naming::introduceDefinition

/**
 * Apply naming to a list of subformulas.
 *
 * @param fs the list
 * @param results placeholder for results
 * @param where the position of the list in the top formula
 * @param negResults placeholder for results for a negative occurrence
 *        of the list
 *
 * @returns the number of clauses
 * @since 01/07/2005 Manchester
 */
FormulaList* Naming::apply_list(FormulaList* fs, Where where, int* results,
    int* negResults) {
  CALL("Naming::apply_list(FormulaList*...)");

  if (FormulaList::isEmpty(fs)) {
    return fs;
  }

  int neg;
  Formula* g = apply_sub(fs->head(), where, results[0], neg);
  if (where == UNDER_IFF) {
    negResults[0] = neg;
  }
  FormulaList* gs = apply_list(fs->tail(), where, results + 1, negResults + 1);

  if (g != fs->head() || gs != fs->tail()) {
    fs = new FormulaList(g, gs);
  }
  return fs;
} // Naming::apply (FormulaList&...)

