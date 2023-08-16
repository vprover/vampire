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
 * @file InductionRewriting.cpp
 * Implements class InductionRewriting.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "InductionRewriting.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

// iterators and filters

TermList SingleOccurrenceReplacementIterator::Replacer::transformSubterm(TermList trm)
{
  if (trm.isVar() || _matchCount > _i) {
    return trm;
  }
  if (trm.term() == _o && _i == _matchCount++) {
    return _r;
  }
  return trm;
}

Term* SingleOccurrenceReplacementIterator::next()
{
  ASS(hasNext());
  if (_t == _o) {
    _iteration++;
    return _r.term();
  }
  Replacer sor(_o, _r, _iteration++);
  return sor.transform(_t);
}

// inference

void InductionRewriting::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_RHS_CODE_TREE) );
  _subtermIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(REMODULATION_SUBTERM_CODE_TREE) );
  // _induction->attach(salg);
}

void InductionRewriting::detach()
{
  // _induction->detach();
  // delete _induction;
  _lhsIndex = 0;
  _subtermIndex=0;
  _salg->getIndexManager()->release(DEMODULATION_RHS_CODE_TREE);
  _salg->getIndexManager()->release(REMODULATION_SUBTERM_CODE_TREE);
  GeneratingInferenceEngine::detach();
}

#define MAX_DEPTH 10

Term* replace(Term* t, Term* orig, Term* repl, const Stack<unsigned>& pos)
{
  Stack<pair<Term*,unsigned>> todo;
  Term* curr = t;
  for (unsigned i = 0; i < pos.size(); i++) {
    auto p = pos[i];
    ASS_L(p,curr->arity());
    todo.push(make_pair(curr,p));

    auto next = curr->nthArgument(p);
    ASS(next->isTerm());
    curr = next->term();
  }
  ASS_EQ(orig,curr);
  Term* res = repl;

  while(todo.isNonEmpty()) {
    auto kv = todo.pop();
    TermStack args; 
    for (unsigned i = 0; i < kv.first->arity(); i++) {
      if (i == kv.second) {
        args.push(TermList(res));
      } else {
        args.push(*kv.first->nthArgument(i));
      }
    }
    res = Term::create(kv.first,args.begin());
  }
  return res;
}

pair<Term*,Stack<unsigned>> PositionalNonVariableNonTypeIterator::next()
{
  auto kv = _stack.pop();
  TermList* ts;
  auto t = kv.first;

  for(unsigned i = t->numTypeArguments(); i < t->arity(); i++){
    ts = t->nthArgument(i);
    if (ts->isTerm()) {
      auto newPos = kv.second;
      newPos.push(i);
      _stack.push(make_pair(const_cast<Term*>(ts->term()),std::move(newPos)));
    }
  }
  return kv;
}

bool toTheLeftStrict(const Position& p1, const Position& p2)
{
  for (unsigned i = 0; i < p1.size(); i++) {
    if (p2.size() <= i) {
      return false;
    }
    if (p1[i] != p2[i]) {
      return p1[i] < p2[i];
    }
  }
  return false;
} 

bool toTheLeft(const Position& p1, const Position& p2)
{
  for (unsigned i = 0; i < p1.size(); i++) {
    if (p2.size() <= i) {
      return true;
    }
    if (p1[i] != p2[i]) {
      return p1[i] < p2[i];
    }
  }
  return true;
}

vstring posToString(const Position& pos)
{
  vstring res;
  for (unsigned i = 0; i < pos.size(); i++) {
    res += Int::toString(pos[i]);
    if (i+1 < pos.size()) {
      res += '.';
    }
  }
  return res;
}

// void InductionRewriting::exploreTerm(Term* t, bool left)
// {
//   TIME_TRACE("InductionRewriting::exploreTerm");
//   auto& terms = left ? _leftTerms : _rightTerms;
//   terms.reset();
//   terms.insert(t);

//   Stack<pair<Term*,unsigned>> todo;
//   todo.push(make_pair(t,0));
//   const auto& ord = _salg->getOrdering();

//   while(todo.isNonEmpty()) {
//     auto kv = todo.pop();
//     auto curr = kv.first;
//     auto depth = kv.second;
//     if (depth >= MAX_DEPTH) {
//       continue;
//     }
//     // cout << "rewriting term " << *curr << endl;
//     iterTraits(vi(new NonVariableNonTypeIterator(curr,true)))
//       .unique()
//       .timeTraced("term iter")
//       .flatMap([this](Term* st) {
//         // cout << "st " << *st << endl;
//         return pvi(pushPairIntoRightIterator(st,_lhsIndex->getGeneralizations(st, true)));
//       })
//       .timeTraced("lhs index query")
//       .flatMap([curr,&ord](pair<Term*,TermQueryResult> arg) {
//         auto lhsS = arg.first;
//         auto qr = arg.second;
//         if (SortHelper::getResultSort(lhsS) != SortHelper::getEqualityArgumentSort(qr.literal)) {
//           return VirtualIterator<Term*>::getEmpty();
//         }
//         // cout << "eq " << *qr.literal << endl;
//         auto rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
//         auto rhsS = qr.substitution->applyToBoundResult(rhs);
//         if (ord.compare(TermList(lhsS),rhsS)!=Ordering::Result::LESS) {
//           return VirtualIterator<Term*>::getEmpty();
//         }
//         return pvi(vi(new SingleOccurrenceReplacementIterator(curr, lhsS, rhsS)));
//       })
//       .timeTraced("rewrite")
//       .forEach([&terms,&todo,depth](Term* res) {
//         if (terms.insert(res)) {
//           todo.push(make_pair(res,depth+1));
//         }
//       });
//   }
// }

Stack<Position> insertPosition(const Stack<Position>& ps, const Position& p)
{
  Stack<Position> res;
  for (const auto& q : ps) {
    bool diverged = false;
    for (unsigned i = 0; i < q.size(); i++) {
      if (p.size() <= i) {
        break;
      }
      if (p[i] != q[i]) {
        diverged = true;
        break;
      }
    }
    if (diverged) {
      res.push(q);
    }
  }
  res.push(p);
  return res;
}

void InductionRewriting::exploreTermLMIM(Term* t, bool left)
{
  TIME_TRACE("InductionRewriting::exploreTermLMIM");
  auto& terms = left ? _leftTerms : _rightTerms;
  terms.reset();
  Stack<Position> ps;
  ps.push(Position());
  terms.insert(t,std::move(ps));

  Stack<tuple<Term*,Stack<unsigned>,unsigned>> todo;
  todo.push(make_tuple(t,Stack<unsigned>(),0));
  const auto& ord = _salg->getOrdering();

  while(todo.isNonEmpty()) {
    auto tp = todo.pop();
    auto curr = get<0>(tp);
    auto pos = get<1>(tp);
    auto depth = get<2>(tp);
    if (depth >= MAX_DEPTH) {
      continue;
    }
    // cout << "lmim rewriting term " << *curr << endl;
    iterTraits(vi(new PositionalNonVariableNonTypeIterator(curr)))
      .filter([pos](pair<Term*,Stack<unsigned>> arg) {
        return toTheLeft(pos, arg.second);
      })
      .flatMap([this](pair<Term*,Stack<unsigned>> arg) {
        // cout << "st " << *arg.first << " in " << posToString(arg.second) << endl;
        return pvi(pushPairIntoRightIterator(arg,_lhsIndex->getGeneralizations(arg.first, true)));
      })
      .map([curr,&ord](pair<pair<Term*,Stack<unsigned>>,TermQueryResult> arg) {
        auto lhsS = arg.first.first;
        auto pos = arg.first.second;
        auto qr = arg.second;
        if (SortHelper::getResultSort(lhsS) != SortHelper::getEqualityArgumentSort(qr.literal)) {
          return make_pair((Term*)nullptr,pos);
        }
        // cout << "eq " << *qr.literal << endl;
        auto rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        auto rhsS = qr.substitution->applyToBoundResult(rhs);
        if (ord.compare(TermList(lhsS),rhsS)!=Ordering::Result::LESS) {
          return make_pair((Term*)nullptr,pos);
        }
        return make_pair(replace(curr, lhsS, rhsS.term(), pos), pos);
      })
      .filter([](pair<Term*,Stack<unsigned>> res) {
        return res.first;
      })
      .forEach([&terms,&todo,depth,curr](pair<Term*,Stack<unsigned>> res) {
        if (!terms.find(res.first)) {
          // cout << "res " << *res.first << endl;
          todo.push(make_tuple(res.first,res.second,depth+1));
          terms.insert(res.first,insertPosition(terms.get(curr), res.second));
        }
      });
  }
}

Term* getTermAtPos(Term* t, const Position& p)
{
  Term* curr = t;
  for (const auto& i : p) {
    ASS_L(i,curr->arity());
    curr = curr->nthArgument(i)->term();
  }
  return curr;
}

bool isInductionTerm(Term* t)
{
  if (!InductionHelper::isInductionTermFunctor(t->functor())) {
    return false;
  }
  if (!InductionHelper::isStructInductionTerm(t)) {
    return false;
  }
  NonVariableNonTypeIterator nvi(t, true);
  while (nvi.hasNext()) {
    if (env.signature->getFunction(nvi.next()->functor())->skolem()) return true;
  }
  return false;
}

// void getTermsToInductOn(Term* t, const Stack<Position>& ps, DHSet<Term*>& indTerms)
// {
//   indTerms.reset();
//   ASS(ps.isNonEmpty());
//   auto st = getTermAtPos(t,ps[0]);
//   NonVariableNonTypeIterator nvi(st,true);
//   while (nvi.hasNext()) {
//     auto stt = nvi.next();
//     if (isInductionTerm(stt)) {
//       indTerms.insert(stt);
//     }
//   }
//   if (indTerms.isEmpty()) {
//     return;
//   }
//   for (unsigned i = 1; i < ps.size(); i++) {
//     DHSet<Term*> inner;
//     auto st = getTermAtPos(t,ps[i]);
//     NonVariableNonTypeIterator nvi(st,true);
//     while (nvi.hasNext()) {
//       auto stt = nvi.next();
//       if (isInductionTerm(stt) && indTerms.contains(stt)) {
//         inner.insert(stt);
//       }
//     }
//     DHSet<Term*>::DelIterator it(indTerms);
//     while (it.hasNext()) {
//       if (!inner.contains(it.next())) {
//         it.del();
//       }
//     }
//   }
// }

Position getRightmostPosition(const Stack<pair<Position,bool>>& ps, bool left) {
  Position curr;
  for (auto& kv : ps) {
    if (kv.second != left) {
      continue;
    }
    if (toTheLeft(curr,kv.first)) {
      curr = kv.first;
    }
  }
  return curr;
}

void assertPositionIn(const Position& p, Term* t) {
  Term* curr = t;
  // cout << "assert pos " << *t << " " << posToString(p) << endl;
  for (const auto& i : p) {
    ASS_L(i,curr->arity());
    curr = curr->nthArgument(i)->term();
  }
}

inline bool hasTermToInductOn(Term* t) {
  NonVariableNonTypeIterator stit(t);
  while (stit.hasNext()) {
    auto st = stit.next();
    if (InductionHelper::isInductionTermFunctor(st->functor()) && InductionHelper::isStructInductionTerm(st)) {
      return true;
    }
  }
  return false;
}

ClauseIterator InductionRewriting::generateClauses(Clause* premise)
{
  // cout << "premise " << *premise << endl;
  // ClauseIterator res = _induction->generateClauses(premise);
  auto res = ClauseIterator::getEmpty();

  if (premise->length()==1) {
    auto lit = (*premise)[0];
    // cout << "lit " << *lit << endl;
    if (lit->isEquality() && lit->isNegative() && lit->ground()) {
      // auto t0 = lit->termArg(0);
      // auto t1 = lit->termArg(1);

      // exploreTerm(t0.term(),true);
      // int s0 = _leftTerms.size();

      // exploreTermLMIM(t0.term(),true);
      // int s0_0 = _leftTerms.size();

      // // exploreTerm(t1.term(),false);
      // // int s1 = _rightTerms.size();

      // exploreTermLMIM(t1.term(),false);
      // int s1_0 = _rightTerms.size();
      // // cout << "left diff " << s0-s0_0 << endl
      // //      << "right diff " << s1-s1_0 << endl;
      // // cout << s0 << " and " << s1 << " or " << s0_0 << " and " << s1_0 << endl << endl;
      // unsigned cnt = 0;
      // unsigned matches = 0;
      // DHSet<Term*> indTerms;
      // DHMap<Term*,Stack<Position>>::Iterator leftIt(_leftTerms);
      // DHMap<Term*,Stack<Term*>> leftIndTermIndex;
      // while (leftIt.hasNext()) {
      //   Term* t;
      //   auto& ps = leftIt.nextRef(t);
      //   getTermsToInductOn(t, ps, indTerms);
      //   cnt += indTerms.size();
      //   // cout << *t << ": " << endl;
      //   DHSet<Term*>::Iterator lIt(indTerms);
      //   while (lIt.hasNext()) {
      //     auto indTerm = lIt.next();
      //     Stack<Term*>* index;
      //     leftIndTermIndex.getValuePtr(indTerm, index);
      //     index->push(t);
      //     // cout << *lIt.next() << " ";
      //   }
      //   // cout << endl;
      // }
      // cout << "left terms to induct on " << cnt << endl;
      // cnt = 0;
      // DHMap<Term*,Stack<Position>>::Iterator rightIt(_rightTerms);
      // while (rightIt.hasNext()) {
      //   Term* t;
      //   auto& ps = rightIt.nextRef(t);
      //   getTermsToInductOn(t, ps, indTerms);
      //   cnt += indTerms.size();
      //   // cout << *t << ": " << endl;
      //   DHSet<Term*>::Iterator lIt(indTerms);
      //   while (lIt.hasNext()) {
      //     auto indTerm = lIt.next();
      //     auto ptr = leftIndTermIndex.findPtr(indTerm);
      //     if (ptr) {
      //       matches += ptr->size();
      //     }
      //     // cout << *lIt.next() << " ";
      //   }
      //   // cout << endl;
      // }
      // cout << "right terms to induct on " << cnt << endl;
      // cout << "matches " << matches << endl;

      const auto& ord = _salg->getOrdering();
      auto ps = premise->backwardRewritingPositions();

      res = pvi(getConcatenatedIterator(res, pvi(iterTraits(getConcatenatedIterator(
          pvi(getSingletonIterator(make_pair(lit->termArg(0),true/*left*/))),
          pvi(getSingletonIterator(make_pair(lit->termArg(1),false/*left*/)))
        ))
        .flatMap([](pair<TermList,bool> arg) {
          return pvi(pushPairIntoRightIterator(make_pair(arg.first.term(),arg.second),vi(new PositionalNonVariableNonTypeIterator(arg.first.term()))));
        })
        .filter([ps](pair<pair<Term*,bool>,pair<Term*,Position>> arg) {
          return !ps || toTheLeft(getRightmostPosition(*ps, arg.first.second), arg.second.second);
        })
        .flatMap([this](pair<pair<Term*,bool>,pair<Term*,Position>> arg) {
          // cout << "st " << *arg.first << " in " << posToString(arg.second) << endl;
          return pvi(pushPairIntoRightIterator(arg,_lhsIndex->getGeneralizations(arg.second.first, true)));
        })
        .map([&ord,lit,ps,premise](pair<pair<pair<Term*,bool>,pair<Term*,Position>>,TermQueryResult> arg) -> Clause* {
          auto side = arg.first.first.first;
          auto lhsS = arg.first.second.first;
          auto pos = arg.first.second.second;
          auto qr = arg.second;
          if (!qr.clause->splits()->isSubsetOf(premise->splits())) {
            TIME_TRACE("splitset not subset");
            return nullptr;
          }
          if (premise->remDepth()>=MAX_DEPTH) {
            return nullptr;
          }
          if (SortHelper::getResultSort(lhsS) != SortHelper::getEqualityArgumentSort(qr.literal)) {
            return nullptr;
          }
          // cout << "eq " << *qr.literal << endl;
          auto rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
          auto rhsS = qr.substitution->applyToBoundResult(rhs);
          if (ord.compare(TermList(lhsS),rhsS)!=Ordering::Result::LESS) {
            return nullptr;
          }

          auto sideR = replace(side, lhsS, rhsS.term(), pos);
          auto other = EqHelper::getOtherEqualitySide(lit, TermList(side));
          ASS_NEQ(sideR,other.term());
          auto resLit = Literal::createEquality(false, TermList(sideR), other, SortHelper::getEqualityArgumentSort(lit));

          Clause* res = new(1) Clause(1,
            SimplifyingInference2(InferenceRule::FORWARD_REMODULATION, premise, qr.clause));
          (*res)[0]=resLit;

          auto resPs = new Stack<pair<Position,bool>>();
          res->setBackwardRewritingPositions(resPs);
          res->setRemDepth(premise->remDepth()+1);
          bool left = lit->termArg(0).term() == side;
          // cout << "side " << *side << " " << (left ? "left" : "right") << " in " << *lit << endl;
          bool reversed = resLit->termArg(left ? 1 : 0).term() == sideR;
          if (ps) {
            for (const auto& kv : *ps) {
              bool diverged = false;
              const auto& q = kv.first;
              const auto& leftPrev = kv.second;
              if (left != leftPrev) {
                resPs->push(make_pair(q,reversed?!leftPrev:leftPrev));
                continue; // skip position corresponding to the other side
              }
              for (unsigned i = 0; i < q.size(); i++) {
                if (pos.size() <= i) {
                  break;
                }
                if (pos[i] != q[i]) {
                  diverged = true;
                  break;
                }
              }
              if (diverged) {
                resPs->push(make_pair(q,reversed?!leftPrev:leftPrev));
              }
            }
          }
          // assertPositionIn(pos,sideR);
          resPs->push(make_pair(pos,reversed?!left:left));
          // cout << *res << endl << " with positions " << endl;
          // for (const auto& kv : *resPs) {
          //   cout << kv.second << " " << posToString(kv.first) << endl;
          //   assertPositionIn(kv.first,resLit->termArg(kv.second?0:1).term());
          // }

          env.statistics->forwardRemodulations++;
          return res;
        })
        .filter(NonzeroFn())
        .timeTraced("forward remodulation"))));
    }


    if (lit->isEquality() && lit->isPositive()) {
      const auto& ord = _salg->getOrdering();
      const auto& opt = _salg->getOptions();

      res = pvi(getConcatenatedIterator(res,pvi(iterTraits(EqHelper::getDemodulationLHSIterator(lit, true, ord, opt))
        .filter([lit](TermList lhs) {
          return EqHelper::getOtherEqualitySide(lit,lhs).containsAllVariablesOf(lhs);// && lhs.isTerm() && hasTermToInductOn(lhs.term());
        })
        .map([lit](TermList lhs) {
          return EqHelper::getOtherEqualitySide(lit,lhs);
        })
        .flatMap([lit,this](TermList rhs) {
          return pvi(pushPairIntoRightIterator(rhs,_subtermIndex->getInstances(TypedTermList(rhs,SortHelper::getEqualityArgumentSort(lit)),true)));
        })
        .filter([premise](pair<TermList,TermQueryResult> arg) {
          return arg.second.clause->splits()->isSubsetOf(premise->splits());
        })
        .flatMap([](pair<TermList,TermQueryResult> arg) {
          auto t = arg.second.term.term();
          auto t0 = arg.second.literal->termArg(0).term();
          auto t1 = arg.second.literal->termArg(1).term();
          return pushPairIntoRightIterator(arg,
            pvi(getConcatenatedIterator(
              pvi(pushPairIntoRightIterator(make_pair(t0,true),iterTraits(vi(new PositionalNonVariableNonTypeIterator(t0)))
                .filter([t](pair<Term*,Position> arg) {
                  return arg.first == t;
                }))),
              pvi(pushPairIntoRightIterator(make_pair(t1,false),iterTraits(vi(new PositionalNonVariableNonTypeIterator(t1)))
                .filter([t](pair<Term*,Position> arg) {
                  return arg.first == t;
                }))))));
        })
        .filter([](pair<pair<TermList,TermQueryResult>,pair<pair<Term*,bool>,pair<Term*,Position>>> arg) {
          auto ps = arg.first.second.clause->backwardRewritingPositions();
          return !ps || toTheLeft(getRightmostPosition(*ps, arg.second.first.first), arg.second.second.second);
        })
        .map([&ord,lit,premise](pair<pair<TermList,TermQueryResult>,pair<pair<Term*,bool>,pair<Term*,Position>>> arg) -> Clause* {
          auto side = arg.second.first.first;
          auto lhsS = arg.first.second.term;
          auto pos = arg.second.second.second;
          auto qr = arg.first.second;
          if (qr.clause->remDepth()>=MAX_DEPTH) {
            return nullptr;
          }
          if (SortHelper::getResultSort(lhsS.term()) != SortHelper::getEqualityArgumentSort(lit)) {
            return nullptr;
          }
          // cout << "eq " << *qr.literal << endl;
          auto rhs = EqHelper::getOtherEqualitySide(lit,arg.first.first);
          auto rhsS = qr.substitution->applyToBoundQuery(rhs);
          if (ord.compare(lhsS,rhsS)!=Ordering::Result::LESS) {
            return nullptr;
          }

          auto sideR = replace(side, lhsS.term(), rhsS.term(), pos);
          auto other = EqHelper::getOtherEqualitySide(qr.literal, TermList(side));
          ASS_NEQ(sideR,other.term());
          auto resLit = Literal::createEquality(false, TermList(sideR), other, SortHelper::getEqualityArgumentSort(qr.literal));

          Clause* res = new(1) Clause(1,
            SimplifyingInference2(InferenceRule::BACKWARD_REMODULATION, qr.clause, premise));
          (*res)[0]=resLit;

          auto ps = qr.clause->backwardRewritingPositions();
          auto resPs = new Stack<pair<Position,bool>>();
          res->setBackwardRewritingPositions(resPs);
          res->setRemDepth(qr.clause->remDepth()+1);
          bool left = qr.literal->termArg(0).term() == side;
          // cout << "side " << *side << " " << (left ? "left" : "right") << " in " << *lit << endl;
          bool reversed = resLit->termArg(left ? 1 : 0).term() == sideR;
          if (ps) {
            for (const auto& kv : *ps) {
              bool diverged = false;
              const auto& q = kv.first;
              const auto& leftPrev = kv.second;
              if (left != leftPrev) {
                resPs->push(make_pair(q,reversed?!leftPrev:leftPrev));
                continue; // skip position corresponding to the other side
              }
              for (unsigned i = 0; i < q.size(); i++) {
                if (pos.size() <= i) {
                  break;
                }
                if (pos[i] != q[i]) {
                  diverged = true;
                  break;
                }
              }
              if (diverged) {
                resPs->push(make_pair(q,reversed?!leftPrev:leftPrev));
              }
            }
          }
          // assertPositionIn(pos,sideR);
          resPs->push(make_pair(pos,reversed?!left:left));
          // cout << *res << endl << " with positions " << endl;
          // for (const auto& kv : *resPs) {
          //   cout << kv.second << " " << posToString(kv.first) << endl;
          //   assertPositionIn(kv.first,resLit->termArg(kv.second?0:1).term());
          // }

          env.statistics->backwardRemodulations++;
          return res;
        })
        .filter(NonzeroFn())
        .timeTraced("backward remodulation"))));
    }
  }
  return res;
}

}