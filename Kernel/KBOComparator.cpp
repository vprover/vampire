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

KBOComparator::KBOComparator(TermList lhs, TermList rhs, const KBO& kbo)
  : OrderingComparator(lhs, rhs, kbo), _root(lhs, rhs)
{
}

// void KBOComparator::makeReady()
// {
//   ASS(!_ready);

//   const auto& kbo = static_cast<const KBO&>(_ord);

//   // stack of subcomparisons in lexicographic order (w.r.t. tl1 and tl2)
//   Stack<pair<TermList,TermList>> todo;
//   todo.push(make_pair(_lhs,_rhs));

//   while (todo.isNonEmpty()) {
//     auto kv = todo.pop();
//     auto lhs = kv.first;
//     auto rhs = kv.second;

//     auto comp = kbo.compare(lhs,rhs);
//     switch (comp) {
//       case Ordering::LESS: {
//         // at this point the execution will fail, no further instructions
//         return;
//       }
//       case Ordering::GREATER: {
//         // at this point the execution will succeed, push SUCCESS
//         _instructions.push(Instruction::uintUint(InstructionTag::SUCCESS));
//         return;
//       }
//       default:
//         break;
//     }
//     // this essentially means the EQUAL case
//     if (comp != Ordering::INCOMPARABLE) {
//       continue;
//     }
//     // if either term is a variable, we cannot preprocess them further
//     if (lhs.isVar() || rhs.isVar()) {
//       if (lhs.isVar() && rhs.isVar()) {
//         _instructions.push(Instruction::uintUint(InstructionTag::COMPARE_VV,lhs.var(),rhs.var()));
//       } else if (lhs.isVar()) {
//         _instructions.push(Instruction::uintUint(InstructionTag::COMPARE_VT,lhs.var()));
//         _instructions.push(Instruction::term(rhs.term()));
//       } else if (rhs.isVar()) {
//         // note that lhs is the second argument in this case
//         _instructions.push(Instruction::uintUint(InstructionTag::COMPARE_TV,rhs.var()));
//         _instructions.push(Instruction::term(lhs.term()));
//       }

//       // Prepare further cases if this is equal.
//       // Note that lhs and rhs are incomparable,
//       // so we don't need an occurs check.
//       Substitution subst;
//       if (lhs.isVar()) {
//         subst.bind(lhs.var(),rhs);
//       } else {
//         subst.bind(rhs.var(),lhs);
//       }
//       for (auto& kv : todo) {
//         kv.first = SubstHelper::apply(kv.first,subst);
//         kv.second = SubstHelper::apply(kv.second,subst);
//       }
//       continue;
//     }

//     // if both are proper terms, we calculate
//     // weight and variable balances first

//     // we only care about the non-zero weights and counts
//     bool varInbalance = false;
//     auto state = kbo._state;
// #if VDEBUG
//     // we make sure kbo._state is not used while we're using it
//     kbo._state = nullptr;
// #endif
//     auto w = state->_weightDiff;
//     decltype(state->_varDiffs)::Iterator vit(state->_varDiffs);
//     Stack<pair<unsigned,int>> nonzeros;
//     while (vit.hasNext()) {
//       unsigned v;
//       int cnt;
//       vit.next(v,cnt);
//       if (cnt!=0) {
//         nonzeros.push(make_pair(v,cnt));
//         w-=cnt; // we have to remove the variable weights from w
//       }
//       if (cnt<0) {
//         varInbalance = true;
//       }
//     }
// #if VDEBUG
//     kbo._state = state;
//     state = nullptr;
// #endif

//     // if the condition below does not hold, the weight/var balances are satisfied
//     if (w < 0 || varInbalance) {
//       // reinterpret weight here to unsigned because the compiler might not do it
//       unsigned wu = reinterpret_cast<unsigned&>(w);

//       _instructions.push(Instruction::uintUint(InstructionTag::WEIGHT, (unsigned)nonzeros.size(), wu));
//       // sort the [var,count] pairs by count descending so that
//       // we can exit early during execution if needed
//       sort(nonzeros.begin(),nonzeros.end(),[](const auto& e1, const auto& e2) {
//         return e1.second>e2.second;
//       });
//       for (const auto& [v,cnt] : nonzeros) {
//         // see same with weight above
//         unsigned cntu = reinterpret_cast<const unsigned&>(cnt);

//         _instructions.push(Instruction::uintUint(InstructionTag::DATA, v, cntu));
//       }
//     }

//     auto lhst = lhs.term();
//     auto rhst = rhs.term();

//     Ordering::Result prec = lhst->isSort()
//       ? kbo.compareTypeConPrecedences(lhst->functor(),rhst->functor())
//       : kbo.compareFunctionPrecedences(lhst->functor(),rhst->functor());
//     switch (prec)
//     {
//       case Ordering::LESS: {
//         // again, this means the execution failed
//         return;
//       }
//       case Ordering::GREATER: {
//         // and this means the execution succeeded
//         _instructions.push(Instruction::uintUint(InstructionTag::SUCCESS));
//         return;
//       }
//       case Ordering::EQUAL: {
//         // push the arguments in reverse order to maintain
//         // left-to-right lexicographic order in todo
//         for (unsigned i = 0; i < lhst->arity(); i++) {
//           auto lhsArg = *lhst->nthArgument(lhst->arity()-i-1);
//           auto rhsArg = *rhst->nthArgument(lhst->arity()-i-1);
//           todo.push(make_pair(lhsArg,rhsArg));
//         }
//         break;
//       }
//       default: {
//         ASSERTION_VIOLATION;
//       }
//     }
//   }
// }

// bool KBOComparator::check(const SubstApplicator* applicator)
// {
//   if (!_ready) {
//     makeReady();
//     _ready = true;
//   }

//   const auto& kbo = static_cast<const KBO&>(_ord);

//   for (unsigned i = 0; i < _instructions.size();) {
//     switch (static_cast<InstructionTag>(_instructions[i]._tag())) {
//       case InstructionTag::WEIGHT: {

//         // check weight and var balance
//         auto arity = _instructions[i]._firstUint();
//         auto weight = _instructions[i]._coeff();
//         ZIArray<int> varDiffs;
//         for (unsigned j = i+1; j < i+1+arity; j++) {
//           ASS(_instructions[j]._tag()==InstructionTag::DATA);

//           auto var = _instructions[j]._firstUint();
//           auto coeff = _instructions[j]._coeff();
//           AppliedTerm tt(TermList::var(var), applicator, true);

//           VariableIterator vit(tt.term);
//           while (vit.hasNext()) {
//             auto v = vit.next();
//             varDiffs[v.var()] += coeff;
//             // since the counts are sorted in descending order,
//             // this can only mean we will fail
//             if (varDiffs[v.var()]<0) {
//               return false;
//             }
//           }
//           auto w = kbo.computeWeight(tt);
//           weight += coeff*w;
//           // due to descending order of counts,
//           // this also means failure
//           if (coeff<0 && weight<0) {
//             return false;
//           }
//         }

//         if (weight > 0) {
//           return true;
//         } else if (weight < 0) {
//           return false;
//         }
//         // jump over the [var,count] pairs
//         i += 1+arity;
//         break;
//       }
//       case InstructionTag::COMPARE_VV: {
//         auto res = kbo.isGreaterOrEq(
//           AppliedTerm(TermList::var(_instructions[i]._firstUint()), applicator, true),
//           AppliedTerm(TermList::var(_instructions[i]._secondUint()), applicator, true));
//         if (res==Ordering::EQUAL) {
//             i++;
//             break;
//         }
//         return res==Ordering::GREATER;
//       }
//       case InstructionTag::COMPARE_VT: {
//         ASS(_instructions[i+1]._tag()==InstructionTag::DATA);
//         auto res = kbo.isGreaterOrEq(
//           AppliedTerm(TermList::var(_instructions[i]._firstUint()), applicator, true),
//           AppliedTerm(TermList(_instructions[i+1]._term()), applicator, true));
//         if (res==Ordering::EQUAL) {
//             i += 2;
//             break;
//         }
//         return res==Ordering::GREATER;
//       }
//       case InstructionTag::COMPARE_TV: {
//         ASS(_instructions[i+1]._tag()==InstructionTag::DATA);
//         // note that in this case the term is the second argument
//         auto res = kbo.isGreaterOrEq(
//           AppliedTerm(TermList(_instructions[i+1]._term()), applicator, true),
//           AppliedTerm(TermList::var(_instructions[i]._firstUint()), applicator, true));
//         if (res==Ordering::EQUAL) {
//             i += 2;
//             break;
//         }
//         return res==Ordering::GREATER;
//       }
//       case InstructionTag::SUCCESS: {
//         return true;
//       }
//       default:
//         ASSERTION_VIOLATION;
//     }
//   }
//   return false;
// }

ostream& operator<<(ostream& out, const KBOComparator::BranchTag& t)
{
  switch (t) {
    case KBOComparator::BranchTag::T_NOT_GREATER:
      out << "!>";
      break;
    case KBOComparator::BranchTag::T_GREATER:
      out << ">";
      break;
    case KBOComparator::BranchTag::T_COMPARISON:
      out << "$";
      break;
    case KBOComparator::BranchTag::T_WEIGHT:
      out << "w";
      break;
    case KBOComparator::BranchTag::T_UNKNOWN:
      out << "?";
      break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& str, const KBOComparator::Branch& branch)
{
  str << branch.tag << " ";
  if (branch.n) {
    if (branch.tag==KBOComparator::BranchTag::T_WEIGHT) {
      auto n = static_cast<KBOComparator::WeightNode*>(branch.n.ptr());
      str << n->w << " ";
      for (const auto& [var, coeff] : n->varCoeffPairs) {
        str << "X" << var << " " << coeff << " ";
      }
    } else {
      auto n = static_cast<KBOComparator::ComparisonNode*>(branch.n.ptr());
      str << n->lhs << " " << n->rhs;
    }
  } else {
    str << "null";
  }
  return str;
}

ostream& operator<<(ostream& str, const KBOComparator& comp)
{
  str << "comparator for " << comp._lhs << " > " << comp._rhs << endl;
  // return str;

  Stack<pair<const KBOComparator::Branch*, unsigned>> todo;
  todo.push(make_pair(&comp._root,0));
  unsigned cnt = 1;

  while (todo.isNonEmpty()) {
    auto kv = todo.pop();
    str << cnt++ << " ";
    for (unsigned i = 0; i < kv.second; i++) {
      str << "  ";
    }
    str << *kv.first << endl;
    if (kv.first->n) {
      todo.push(make_pair(&kv.first->n->incBranch,kv.second+1));
      todo.push(make_pair(&kv.first->n->gtBranch,kv.second+1));
      todo.push(make_pair(&kv.first->n->eqBranch,kv.second+1));
    }
  }
  return str;
}

std::string KBOComparator::toString() const
{
  std::stringstream str;
  str << *this << endl;
  return str.str();
}

bool KBOComparator::check(const SubstApplicator* applicator)
{
  const auto& kbo = static_cast<const KBO&>(_ord);
  auto curr = &_root;

  while (curr->n) {
    expand(*curr, kbo);
    if (!curr->n) {
      break;
    }
    ASS(curr->n);
    Ordering::Result comp = Ordering::INCOMPARABLE;
    if (curr->tag==BranchTag::T_COMPARISON) {
      auto node = static_cast<ComparisonNode*>(curr->n.ptr());
      comp = kbo.isGreaterOrEq(AppliedTerm(node->lhs,applicator,true),AppliedTerm(node->rhs,applicator,true));
    } else {
      ASS(curr->tag==BranchTag::T_WEIGHT);
      auto node = static_cast<WeightNode*>(curr->n.ptr());
      auto weight = node->w;
      ZIArray<int> varDiffs;
      for (const auto& [var, coeff] : node->varCoeffPairs) {
        AppliedTerm tt(TermList::var(var), applicator, true);

        VariableIterator vit(tt.term);
        while (vit.hasNext()) {
          auto v = vit.next();
          varDiffs[v.var()] += coeff;
          // since the counts are sorted in descending order,
          // this can only mean we will fail
          if (varDiffs[v.var()]<0) {
            goto loop_end;
          }
        }
        auto w = kbo.computeWeight(tt);
        weight += coeff*w;
        // due to descending order of counts,
        // this also means failure
        if (coeff<0 && weight<0) {
          goto loop_end;
        }
      }

      if (weight > 0) {
        comp = Ordering::GREATER;
      } else if (weight == 0) {
        comp = Ordering::EQUAL;
      }
    }
loop_end:
    curr = &curr->n->getBranch(comp);
  }
  return curr->tag == BranchTag::T_GREATER;
}

void KBOComparator::expand(Branch& branch, const KBO& kbo)
{
  while (branch.tag == BranchTag::T_UNKNOWN)
  {
    // take temporary ownership of node
    Branch nodeHolder = branch;
    auto node = static_cast<ComparisonNode*>(nodeHolder.n.ptr());

    // Use compare here to filter out as many
    // precomputable comparisons as possible.
    auto comp = kbo.compare(node->lhs,node->rhs);
    if (comp != Ordering::INCOMPARABLE) {
      if (comp == Ordering::LESS) {
        branch = node->incBranch;
      } else if (comp == Ordering::GREATER) {
        branch = node->gtBranch;
      } else {
        branch = node->eqBranch;
      }
      continue;
    }
    // If we have a variable, we cannot preprocess further.
    if (node->lhs.isVar() || node->rhs.isVar()) {
      branch.tag = BranchTag::T_COMPARISON;
      continue;
    }

    // if both are proper terms, we calculate
    // weight and variable balances first

    // we only care about the non-zero weights and counts
    bool varInbalance = false;
    auto state = kbo._state;
#if VDEBUG
    // we make sure kbo._state is not used while we're using it
    kbo._state = nullptr;
#endif
    auto w = state->_weightDiff;
    decltype(state->_varDiffs)::Iterator vit(state->_varDiffs);
    Stack<pair<unsigned,int>> nonzeros;
    while (vit.hasNext()) {
      unsigned v;
      int cnt;
      vit.next(v,cnt);
      if (cnt!=0) {
        nonzeros.push(make_pair(v,cnt));
        w-=cnt; // we have to remove the variable weights from w
      }
      if (cnt<0) {
        varInbalance = true;
      }
    }
#if VDEBUG
    kbo._state = state;
    state = nullptr;
#endif

    auto curr = &branch;

    // if the condition below does not hold, the weight/var balances are satisfied
    if (w < 0 || varInbalance) {
      sort(nonzeros.begin(),nonzeros.end(),[](const auto& e1, const auto& e2) {
        return e1.second>e2.second;
      });
      *curr = Branch(w, std::move(nonzeros));
      curr->n->gtBranch = node->gtBranch;
      curr->n->incBranch = node->incBranch;
      curr = &branch.n->eqBranch;
    }

    auto lhst = node->lhs.term();
    auto rhst = node->rhs.term();

    Ordering::Result prec = lhst->isSort()
      ? kbo.compareTypeConPrecedences(lhst->functor(),rhst->functor())
      : kbo.compareFunctionPrecedences(lhst->functor(),rhst->functor());
    switch (prec)
    {
      case Ordering::LESS: {
        *curr = node->incBranch;
        break;
      }
      case Ordering::GREATER: {
        *curr = node->gtBranch;
        break;
      }
      case Ordering::EQUAL: {
        // push the arguments in reverse order to maintain
        // left-to-right lexicographic order in todo
        for (unsigned i = 0; i < lhst->arity(); i++) {
          auto lhsArg = *lhst->nthArgument(i);
          auto rhsArg = *rhst->nthArgument(i);
          *curr = Branch(lhsArg,rhsArg);
          curr = &curr->n->eqBranch;
        }
        *curr = node->eqBranch;
        break;
      }
      default: {
        ASSERTION_VIOLATION;
      }
    }
  }
}

// std::string KBOComparator::toString() const
// {
//   std::stringstream str;

//   unsigned cnt = 1;
//   for (unsigned i = 0; i < _instructions.size();) {
//     switch (static_cast<InstructionTag>(_instructions[i]._tag())) {
//       case InstructionTag::SUCCESS: {
//         str << Int::toString(cnt++) << " success, ";
//         i += 1;
//         break;
//       }
//       case InstructionTag::WEIGHT: {
//         auto arity = _instructions[i]._firstUint();
//         auto w = _instructions[i]._coeff();
//         str << Int::toString(cnt++) << " weight " << Int::toString(w);

//         for (unsigned j = i+1; j < i+1+arity; j++) {
//           ASS(_instructions[j]._tag()==InstructionTag::DATA);
//           auto var = _instructions[j]._firstUint();
//           auto coeff = _instructions[j]._coeff();

//           str << " w(X" << Int::toString(var) << ")*" << Int::toString(coeff);
//         }
//         str << ", ";
//         i += 1+arity;
//         break;
//       }
//       case InstructionTag::COMPARE_VV: {
//         auto v1 = _instructions[i]._firstUint();
//         auto v2 = _instructions[i]._secondUint();
//         str << Int::toString(cnt++) << " compare X" << Int::toString(v1) << " X" << Int::toString(v2) << ", ";
//         i++;
//         break;
//       }
//       case InstructionTag::COMPARE_VT: {
//         ASS(_instructions[i+1]._tag()==InstructionTag::DATA);
//         auto v1 = _instructions[i]._firstUint();
//         auto t2 = _instructions[i+1]._term();
//         str << Int::toString(cnt++) << " compare X" << Int::toString(v1) << " " << *t2 << ", ";
//         i += 2;
//         break;
//       }
//       case InstructionTag::COMPARE_TV: {
//         ASS(_instructions[i+1]._tag()==InstructionTag::DATA);
//         auto t1 = _instructions[i+1]._term();
//         auto v2 = _instructions[i]._firstUint();
//         str << Int::toString(cnt++) << " compare " << *t1 << " X" << Int::toString(v2) << ", ";
//         i += 2;
//         break;
//       }
//       default:
//         ASSERTION_VIOLATION;
//     }
//   }
//   return str.str();
// }

// bool KBOComparator::subsumes(OrderingComparator& other)
// {
//   if (!_ready) {
//     makeReady();
//     _ready = true;
//   }
//   auto& otherKBO = static_cast<KBOComparator&>(other);
//   if (!otherKBO._ready) {
//     otherKBO.makeReady();
//     otherKBO._ready = true;
//   }
//   if (_instructions.size()<otherKBO._instructions.size()) {
//     return false;
//   }
//   for (unsigned i = 0; i < otherKBO._instructions.size();) {
//     if (_instructions[i]._tag() != otherKBO._instructions[i]._tag()) {
//       return false;
//     }
//     switch (static_cast<InstructionTag>(_instructions[i]._tag())) {
//       case InstructionTag::WEIGHT: {
//         // check weight and var balance
//         auto arity = _instructions[i]._firstUint();
//         auto weight = _instructions[i]._coeff();
//         auto arityOther = otherKBO._instructions[i]._firstUint();
//         auto weightOther = otherKBO._instructions[i]._coeff();
//         if (arity != arityOther || weight != weightOther) {
//           return false;
//         }
//         for (unsigned j = i+1; j < i+1+arity; j++) {
//           ASS(_instructions[j]._tag()==InstructionTag::DATA);

//           auto var = _instructions[j]._firstUint();
//           auto coeff = _instructions[j]._coeff();
//           auto varOther = otherKBO._instructions[j]._firstUint();
//           auto coeffOther = otherKBO._instructions[j]._coeff();
//           // if ((*renaming)(var) != TermList::var(varOther) || coeff != coeffOther) {
//           //   return false;
//           // }
//           if (var != varOther || coeff != coeffOther) {
//             return false;
//           }
//         }
//         // jump over the [var,count] pairs
//         i += 1+arity;
//         break;
//       }
//       case InstructionTag::COMPARE_VV: {
//         auto var1 = _instructions[i]._firstUint();
//         auto var2 = _instructions[i]._secondUint();
//         auto var1Other = otherKBO._instructions[i]._firstUint();
//         auto var2Other = otherKBO._instructions[i]._secondUint();
//         // if ((*renaming)(var1) != TermList::var(var1Other) || (*renaming)(var2) != TermList::var(var2Other)) {
//         //   return false;
//         // }
//         if (var1 != var1Other || var2 != var2Other) {
//           return false;
//         }
//         i++;
//         break;
//       }
//       case InstructionTag::COMPARE_VT:
//       case InstructionTag::COMPARE_TV: {
//         ASS(_instructions[i+1]._tag()==InstructionTag::DATA);
//         auto var = _instructions[i]._firstUint();
//         auto term = _instructions[i+1]._term();
//         auto varOther = otherKBO._instructions[i]._firstUint();
//         auto termOther = otherKBO._instructions[i+1]._term();
//         // if ((*renaming)(var) != TermList::var(varOther) || SubstHelper::apply(TermList(term),*renaming) != TermList(termOther)) {
//         //   return false;
//         // }
//         if (var != varOther || term != termOther) {
//           return false;
//         }
//         i += 2;
//         break;
//       }
//       default:
//         return true;
//     }
//   }
//   return true;
// }

}
