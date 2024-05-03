/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "SubstHelper.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "KBOComparator.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

KBOComparator* KBOComparator::create(TermList tl1, TermList tl2, const KBO& kbo)
{
  auto res = new KBOComparator(kbo);
  Stack<pair<TermList,TermList>> todo;
  todo.push(make_pair(tl1,tl2));

  while (todo.isNonEmpty()) {
    auto kv = todo.pop();
    auto lhs = kv.first;
    auto rhs = kv.second;
    auto comp = kbo.compare(lhs,rhs);
    // cout << "subcase " << lhs << " " << rhs << endl;

    switch (comp) {
      case Ordering::LESS:
      case Ordering::LESS_EQ: {
        return res;
      }
      case Ordering::GREATER:
      case Ordering::GREATER_EQ: {
        res->_instructions.push(Instruction(static_cast<unsigned>(InstructionTag::SUCCESS)));
        return res;
      }
      default:
        break;
    }
    if (comp != Ordering::INCOMPARABLE) {
      continue;
    }
    if (lhs.isVar() || rhs.isVar()) {
      if (lhs.isVar() && rhs.isVar()) {
        res->_instructions.push(Instruction(static_cast<unsigned>(InstructionTag::COMPARE_VV),lhs.var()));
        res->_instructions.push(Instruction(rhs.var()));
      } else if (lhs.isVar()) {
        res->_instructions.push(Instruction(static_cast<unsigned>(InstructionTag::COMPARE_VT),lhs.var()));
        res->_instructions.push(Instruction(rhs.term()));
      } else if (rhs.isVar()) {
        res->_instructions.push(Instruction(static_cast<unsigned>(InstructionTag::COMPARE_TV),rhs.var()));
        res->_instructions.push(Instruction(lhs.term()));
      }

      // Prepare further cases if this is equal.
      // Note that lhs and rhs are incomparable,
      // so we don't need an occurs check.
      Substitution subst;
      if (lhs.isVar()) {
        subst.bind(lhs.var(),rhs);
      } else {
        subst.bind(rhs.var(),lhs);
      }
      for (auto& kv : todo) {
        kv.first = SubstHelper::apply(kv.first,subst);
        kv.second = SubstHelper::apply(kv.second,subst);
      }
      continue;
    }

    DHMap<unsigned,int> vars;
    int w = 0;
    countSymbols(kbo, vars, w, lhs, 1);
    countSymbols(kbo, vars, w, rhs, -1);

    bool varInbalance = false;
    DHMap<unsigned,int>::Iterator vit(vars);
    Stack<pair<unsigned,int>> nonzeros;
    while (vit.hasNext()) {
      unsigned v;
      int cnt;
      vit.next(v,cnt);
      if (cnt!=0) {
        nonzeros.push(make_pair(v,cnt));
      }
      if (cnt<0) {
        varInbalance = true;
      }
    }
    if (w < 0 || varInbalance) {
      res->_instructions.push(Instruction(static_cast<unsigned>(InstructionTag::WEIGHT)));
      res->_instructions.push(Instruction((unsigned)nonzeros.size(),w));
      sort(nonzeros.begin(),nonzeros.end(),[](const auto& e1, const auto& e2) {
        return e1.second>e2.second;
      });
      for (const auto& [v,cnt] : nonzeros) {
        res->_instructions.push(Instruction(v,cnt));
      }
    }
    auto lhst = lhs.term();
    auto rhst = rhs.term();

    Ordering::Result prec = lhst->isSort()
      ? kbo.compareTypeConPrecedences(lhst->functor(),rhst->functor())
      : kbo.compareFunctionPrecedences(lhst->functor(),rhst->functor());
    switch (prec)
    {
      case Ordering::LESS:
      case Ordering::LESS_EQ: {
        return res;
      }
      case Ordering::GREATER:
      case Ordering::GREATER_EQ: {
        res->_instructions.push(Instruction(static_cast<unsigned>(InstructionTag::SUCCESS)));
        return res;
      }
      case Ordering::EQUAL: {
        for (unsigned i = 0; i < lhst->arity(); i++) {
          auto lhsArg = *lhst->nthArgument(lhst->arity()-i-1);
          auto rhsArg = *rhst->nthArgument(lhst->arity()-i-1);
          todo.push(make_pair(lhsArg,rhsArg));
        }
        break;
      }
      default: {
        ASSERTION_VIOLATION;
      }
    }
  }
  return res;
}

bool KBOComparator::check(const SubstApplicator* applicator) const
{
  for (unsigned i = 0; i < _instructions.size();) {
    switch (static_cast<InstructionTag>(_instructions[i]._v1)) {
      case InstructionTag::WEIGHT: {
        auto arity = _instructions[i+1]._v1;
        auto weight = _instructions[i+1]._v2._int;
        ZIArray<int> varDiffs;
        for (unsigned j = i+2; j < i+2+arity; j++) {
          auto var = _instructions[j]._v1;
          auto coeff = _instructions[j]._v2._int;
          AppliedTerm tt(TermList(var,false), applicator, true);

          VariableIterator vit(tt.term);
          while (vit.hasNext()) {
            auto v = vit.next();
            varDiffs[v.var()] += coeff;
            if (varDiffs[v.var()]<0) {
              return false;
            }
          }
          auto w = _kbo.computeWeight(tt);
          weight += coeff*w;
          if (coeff<0 && weight<0) {
            return false;
          }
        }

        if (weight > 0) {
          return true;
        } else if (weight < 0) {
          return false;
        }
        i += 2+arity;
        break;
      }
      case InstructionTag::COMPARE_VV: {
        auto res = _kbo.isGreaterOrEq(
          AppliedTerm(TermList(_instructions[i]._v2._uint,false), applicator, true),
          AppliedTerm(TermList(_instructions[i+1]._v1,false), applicator, true));
        if (res==Ordering::EQUAL) {
            i += 2;
            break;
        }
        return res==Ordering::GREATER;
      }
      case InstructionTag::COMPARE_VT: {
        auto res = _kbo.isGreaterOrEq(
          AppliedTerm(TermList(_instructions[i]._v2._uint,false), applicator, true),
          AppliedTerm(TermList(_instructions[i+1]._t), applicator, true));
        if (res==Ordering::EQUAL) {
            i += 2;
            break;
        }
        return res==Ordering::GREATER;
      }
      case InstructionTag::COMPARE_TV: {
        auto res = _kbo.isGreaterOrEq(
          AppliedTerm(TermList(_instructions[i+1]._t), applicator, true),
          AppliedTerm(TermList(_instructions[i]._v2._uint,false), applicator, true));
        if (res==Ordering::EQUAL) {
            i += 2;
            break;
        }
        return res==Ordering::GREATER;
      }
      case InstructionTag::SUCCESS: {
        return true;
      }
      default:
        ASSERTION_VIOLATION;
    }
  }
  return false;
}


void KBOComparator::countSymbols(const KBO& kbo, DHMap<unsigned,int>& vars, int& w, TermList t, int coeff)
{
  if (t.isVar()) {
    int* vcnt;
    vars.getValuePtr(t.var(), vcnt, 0);
    (*vcnt) += coeff;
    return;
  }

  w += coeff*kbo.symbolWeight(t.term());
  SubtermIterator sti(t.term());
  while (sti.hasNext()) {
    auto st = sti.next();
    if (st.isVar()) {
      int* vcnt;
      vars.getValuePtr(st.var(), vcnt, 0);
      (*vcnt) += coeff;
    } else {
      w += coeff*kbo.symbolWeight(st.term());
    }
  }
}

vstring KBOComparator::toString() const
{
  vstringstream str;

  unsigned cnt = 1;
  for (unsigned i = 0; i < _instructions.size();) {
    switch (static_cast<InstructionTag>(_instructions[i]._v1)) {
      case InstructionTag::SUCCESS: {
        str << Int::toString(cnt++) << " success" << endl;
        i += 1;
        break;
      }
      case InstructionTag::WEIGHT: {
        auto arity = _instructions[i+1]._v1;
        auto w = _instructions[i+1]._v2._int;
        str << Int::toString(cnt++) << " weight " << Int::toString(w);

        for (unsigned j = i+2; j < i+2+arity; j++) {
          auto var = _instructions[j]._v1;
          auto coeff = _instructions[j]._v2._int;

          str << " w(X" << Int::toString(var) << ")*" << Int::toString(coeff);
        }
        str << endl;
        i += 2+arity;
        break;
      }
      case InstructionTag::COMPARE_VV: {
        auto v1 = _instructions[i]._v2._uint;
        auto v2 = _instructions[i+1]._v1;
        str << Int::toString(cnt++) << " compare X" << Int::toString(v1) << " X" << Int::toString(v2) << endl;
        i += 2;
        break;
      }
      case InstructionTag::COMPARE_VT: {
        auto v1 = _instructions[i]._v2._uint;
        auto t2 = _instructions[i+1]._t;
        str << Int::toString(cnt++) << " compare X" << Int::toString(v1) << " " << *t2 << endl;
        i += 2;
        break;
      }
      case InstructionTag::COMPARE_TV: {
        auto t1 = _instructions[i+1]._t;
        auto v2 = _instructions[i]._v2._uint;
        str << Int::toString(cnt++) << " compare " << *t1 << " X" << Int::toString(v2) << endl;
        i += 2;
        break;
      }
      default:
        ASSERTION_VIOLATION;
    }
  }
  str << endl;
  return str.str();
}


}
