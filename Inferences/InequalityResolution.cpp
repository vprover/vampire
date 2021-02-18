
/*
 * File InequalityResolution.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file InequalityResolution.cpp
 * Implements class InequalityResolution.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/SortHelper.hpp"
#include "Lib/TypeList.hpp"

#include "Indexing/Index.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "InequalityResolution.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/InequalityNormalizer.hpp"
#include "Indexing/TermIndexingStructure.hpp"
#define DEBUG(...) DBG(__VA_ARGS__)

using Kernel::InequalityLiteral;
namespace Indexing {


template<class NumTraits>
bool InequalityResolutionIndex::handleLiteral(Literal* lit, Clause* c, bool adding)
{
  /* normlizing to t >= 0 */
  auto norm_ = this->normalizer().normalize<NumTraits>(lit);
  if (norm_.isSome()) {
    auto norm = norm_.unwrap();
    for (auto monom : norm.term().iterSummands()) {
      if (!monom.tryNumeral().isSome()) {

        auto term = monom.factors->denormalize();
        if (adding) {
          DEBUG("inserting: ", term);
          _is->insert(term, lit, c);
        } else {
          DEBUG("removing: ", term);
          _is->remove(term, lit, c);
        }
      }
    }
    return true;
  } else {
    return false;
  }
}

void InequalityResolutionIndex::handleClause(Clause* c, bool adding)
{
  CALL("InequalityResolutionIndex::handleClause");

  for (unsigned i = 0; i < c->size(); i++) {
    auto lit = (*c)[i];
    handleLiteral< IntTraits>(lit, c, adding) 
    || handleLiteral< RatTraits>(lit, c, adding)
    || handleLiteral<RealTraits>(lit, c, adding);
  }
}

}


namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void InequalityResolution::attach(SaturationAlgorithm* salg)
{
  CALL("InequalityResolution::attach");
  ASS(!_index);

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<InequalityResolutionIndex*> (
	  _salg->getIndexManager()->request(INEQUALITY_RESOLUTION_SUBST_TREE) );

  _unificationWithAbstraction = env.options->unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF;
}

void InequalityResolution::detach()
{
  CALL("InequalityResolution::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(INEQUALITY_RESOLUTION_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}


// struct InequalityResolution::UnificationsFn
// {
//   UnificationsFn(GeneratingLiteralIndex* index,bool cU)
//   : _index(index),_unificationWithAbstraction(cU) {}
//   VirtualIterator<pair<Literal*, SLQueryResult> > operator()(Literal* lit)
//   {
//     if(lit->isEquality()) {
//       //Binary resolution is not performed with equality literals
//       return VirtualIterator<pair<Literal*, SLQueryResult> >::getEmpty();
//     }
//     if(_unificationWithAbstraction){
//       return pvi( pushPairIntoRightIterator(lit, _index->getUnificationsWithConstraints(lit, true)) );
//     }
//     return pvi( pushPairIntoRightIterator(lit, _index->getUnifications(lit, true)) );
//   }
// private:
//   GeneratingLiteralIndex* _index;
//   bool _unificationWithAbstraction;
// };
//
// struct InequalityResolution::ResultFn
// {
//   ResultFn(Clause* cl, PassiveClauseContainer* passiveClauseContainer, bool afterCheck, Ordering* ord, LiteralSelector& selector, InequalityResolution& parent)
//   : _cl(cl), _passiveClauseContainer(passiveClauseContainer), _afterCheck(afterCheck), _ord(ord), _selector(selector), _parent(parent) {}
//   Clause* operator()(pair<Literal*, SLQueryResult> arg)
//   {
//     CALL("InequalityResolution::ResultFn::operator()");
//
//     SLQueryResult& qr = arg.second;
//     Literal* resLit = arg.first;
//
//     return InequalityResolution::generateClause(_cl, resLit, qr, _parent.getOptions(), _passiveClauseContainer, _afterCheck ? _ord : 0, &_selector);
//   }
// private:
//   Clause* _cl;
//   PassiveClauseContainer* _passiveClauseContainer;
//   bool _afterCheck;
//   Ordering* _ord;
//   LiteralSelector& _selector;
//   InequalityResolution& _parent;
// };
//
// /**
//  * Ordering aftercheck is performed iff ord is not 0,
//  * in which case also ls is assumed to be not 0.
//  */
// Clause* InequalityResolution::generateClause(Clause* queryCl, Literal* queryLit, SLQueryResult qr, const Options& opts, PassiveClauseContainer* passiveClauseContainer, Ordering* ord, LiteralSelector* ls)
// {
//   CALL("InequalityResolution::generateClause");
//   ASS(qr.clause->store()==Clause::ACTIVE);//Added to check that generation only uses active clauses
//
//   if(!ColorHelper::compatible(queryCl->color(),qr.clause->color()) ) {
//     env.statistics->inferencesSkippedDueToColors++;
//     if(opts.showBlocked()) {
//       env.beginOutput();
//       env.out()<<"Blocked resolution of "<<queryCl->toString()<<" and "<<qr.clause->toString()<<endl;
//       env.endOutput();
//     }
//     if(opts.colorUnblocking()) {
//       SaturationAlgorithm* salg = SaturationAlgorithm::tryGetInstance();
//       if(salg) {
// 	ColorHelper::tryUnblock(queryCl, salg);
// 	ColorHelper::tryUnblock(qr.clause, salg);
//       }
//     }
//     return 0;
//   }
//
//   auto constraints = qr.constraints;
//   bool withConstraints = !constraints.isEmpty() && !constraints->isEmpty();
//   unsigned clength = queryCl->length();
//   unsigned dlength = qr.clause->length();
//
//   // LRS-specific optimization:
//   // check whether we can conclude that the resulting clause will be discarded by LRS since it does not fulfil the age/weight limits (in which case we can discard the clause)
//   // we already know the age here so we can immediately conclude whether the clause fulfils the age limit
//   // since we have not built the clause yet we compute lower bounds on the weight of the clause after each step and recheck whether the weight-limit can still be fulfilled.
//   unsigned wlb=0;//weight lower bound
//   unsigned numPositiveLiteralsLowerBound = // lower bound on number of positive literals, don't know at this point whether duplicate positive literals will occur
//       Int::max(queryLit->isPositive() ? queryCl->numPositiveLiterals()-1 : queryCl->numPositiveLiterals(),
//               qr.literal->isPositive() ? qr.clause->numPositiveLiterals()-1 : qr.clause->numPositiveLiterals());
//
//   Inference inf(GeneratingInference2(withConstraints?
//       InferenceRule::CONSTRAINED_RESOLUTION:InferenceRule::RESOLUTION,queryCl, qr.clause));
//   Inference::Destroyer inf_destroyer(inf); // will call destroy on inf when coming out of scope unless disabled
//
//   bool needsToFulfilWeightLimit = passiveClauseContainer && !passiveClauseContainer->fulfilsAgeLimit(wlb, numPositiveLiteralsLowerBound, inf) && passiveClauseContainer->weightLimited();
//
//   if(needsToFulfilWeightLimit) {
//     for(unsigned i=0;i<clength;i++) {
//       Literal* curr=(*queryCl)[i];
//       if(curr!=queryLit) {
//         wlb+=curr->weight();
//       }
//     }
//     for(unsigned i=0;i<dlength;i++) {
//       Literal* curr=(*qr.clause)[i];
//       if(curr!=qr.literal) {
//         wlb+=curr->weight();
//       }
//     }
//     if(!passiveClauseContainer->fulfilsWeightLimit(wlb, numPositiveLiteralsLowerBound, inf)) {
//       RSTAT_CTR_INC("binary resolutions skipped for weight limit before building clause");
//       env.statistics->discardedNonRedundantClauses++;
//       return 0;
//     }
//   }
//
//   unsigned conlength = withConstraints ? constraints->size() : 0;
//   unsigned newLength = clength+dlength-2+conlength;
//
//   inf_destroyer.disable(); // ownership passed to the the clause below
//   Clause* res = new(newLength) Clause(newLength, inf); // the inference object owned by res from now on
//
//   Literal* queryLitAfter = 0;
//   if (ord && queryCl->numSelected() > 1) {
//     TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
//     queryLitAfter = qr.substitution->applyToQuery(queryLit);
//   }
// #if VDEBUG
// /*
//   if(withConstraints && constraints->size() > 0){
//     cout << "Other: " << qr.clause->toString() << endl;
//     cout << "queryLit: " << queryLit->toString() << endl;
//     cout << "resLit: " << qr.literal->toString() << endl;
//     cout << "SUB:" << endl << qr.substitution->toString() << endl;
// */
// /*
//     cout << "SUB(deref):" << endl << qr.substitution->toString(true) << endl;
// */
//   //}
// #endif
//
//   unsigned next = 0;
//   if(withConstraints){
//   for(unsigned i=0;i<constraints->size();i++){
//       pair<pair<TermList,unsigned>,pair<TermList,unsigned>> con = (*constraints)[i]; 
//
// #if VDEBUG
//       //cout << "con pair " << con.first.toString() << " , " << con.second.toString() << endl;
// #endif
//
//       TermList qT = qr.substitution->applyTo(con.first.first,con.first.second);
//       TermList rT = qr.substitution->applyTo(con.second.first,con.second.second);
//
//       unsigned sort = SortHelper::getResultSort(rT.term()); 
//       Literal* constraint = Literal::createEquality(false,qT,rT,sort);
//
//       static Options::UnificationWithAbstraction uwa = opts.unificationWithAbstraction();
//       if(uwa==Options::UnificationWithAbstraction::GROUND &&
//          !constraint->ground() &&
//          (!UnificationWithAbstractionConfig::isInterpreted(qT) && 
//           !UnificationWithAbstractionConfig::isInterpreted(rT))) {
//
//         // the unification was between two uninterpreted things that were not ground 
//         res->destroy();
//         return 0;
//       } 
//
//       (*res)[next] = constraint; 
//       next++;    
//   }
//   }
//   for(unsigned i=0;i<clength;i++) {
//     Literal* curr=(*queryCl)[i];
//     if(curr!=queryLit) {
//       Literal* newLit=qr.substitution->applyToQuery(curr);
//       if(needsToFulfilWeightLimit) {
//         wlb+=newLit->weight() - curr->weight();
//         if(!passiveClauseContainer->fulfilsWeightLimit(wlb, numPositiveLiteralsLowerBound, res->inference())) {
//           RSTAT_CTR_INC("binary resolutions skipped for weight limit while building clause");
//           env.statistics->discardedNonRedundantClauses++;
//           res->destroy();
//           return 0;
//         }
//       }
//       if (queryLitAfter && i < queryCl->numSelected()) {
//         TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
//
//         Ordering::Result o = ord->compare(newLit,queryLitAfter);
//
//         if (o == Ordering::GREATER ||
//             (ls->isPositiveForSelection(newLit)    // strict maximimality for positive literals
//                 && (o == Ordering::GREATER_EQ || o == Ordering::EQUAL))) { // where is GREATER_EQ ever coming from?
//           env.statistics->inferencesBlockedForOrderingAftercheck++;
//           res->destroy();
//           return 0;
//         }
//       }
//       ASS(next < newLength);
//       (*res)[next] = newLit;
//       next++;
//     }
//   }
//
//   Literal* qrLitAfter = 0;
//   if (ord && qr.clause->numSelected() > 1) {
//     TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
//     qrLitAfter = qr.substitution->applyToResult(qr.literal);
//   }
//
//   for(unsigned i=0;i<dlength;i++) {
//     Literal* curr=(*qr.clause)[i];
//     if(curr!=qr.literal) {
//       Literal* newLit = qr.substitution->applyToResult(curr);
//       if(needsToFulfilWeightLimit) {
//         wlb+=newLit->weight() - curr->weight();
//         if(!passiveClauseContainer->fulfilsWeightLimit(wlb, numPositiveLiteralsLowerBound, res->inference())) {
//           RSTAT_CTR_INC("binary resolutions skipped for weight limit while building clause");
//           env.statistics->discardedNonRedundantClauses++;
//           res->destroy();
//           return 0;
//         }
//       }
//       if (qrLitAfter && i < qr.clause->numSelected()) {
//         TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
//
//         Ordering::Result o = ord->compare(newLit,qrLitAfter);
//
//         if (o == Ordering::GREATER ||
//             (ls->isPositiveForSelection(newLit)   // strict maximimality for positive literals
//                 && (o == Ordering::GREATER_EQ || o == Ordering::EQUAL))) { // where is GREATER_EQ ever coming from?
//           env.statistics->inferencesBlockedForOrderingAftercheck++;
//           res->destroy();
//           return 0;
//         }
//       }
//
//       (*res)[next] = newLit;
//       next++;
//     }
//   }
//
//   if(withConstraints){
//     env.statistics->cResolution++;
//   }
//   else{ 
//     env.statistics->resolution++;
//   }
//
//   //cout << "RESULT " << res->toString() << endl;
//
//   return res;
// }


/* 
 * maps (num1, num2) -> (k1, k2) 
 * s.t.  num1 * k1 = - num2 * k2
 */
template<class Numeral>
pair<Numeral,Numeral> computeFactors(Numeral num1, Numeral num2)
{ 
  ASS(num1 != Numeral(0))
  ASS(num2 != Numeral(0))
  // num1 * k1 = - num2 * k2
  // let k1 = 1
  // ==> num1 = - num2 * k2 ==> k2 = - num1 / num2
  return std::make_pair(Numeral(1), -(num1 / num2));
}

/* 
 * maps (num1, num2) -> (k1, k2) 
 * s.t.  num1 * k1 = - num2 * k2
 */
pair<IntegerConstantType,IntegerConstantType> computeFactors(IntegerConstantType num1, IntegerConstantType num2)
{ 
  ASS(num1 != IntegerConstantType(0))
  ASS(num2 != IntegerConstantType(0))
  // num1 * k1 = - num2 * k2
  // let k1 =   num2 / gcd(num1, num2)
  //     k2 = - num1 / gcd(num1, num2)
  // num1 * num2 / gcd(num1, num2) = - num2 * (- num1 / gcd(num1, num2))
  auto gcd = IntegerConstantType::gcd(num1, num2);
  ASS(gcd.divides(num1));
  ASS(gcd.divides(num2));
  return std::make_pair(num2.quotientE(gcd) , -num1.quotientE(gcd));
}


// template<template<class...> class C, class... Args>
// class Adaptor 
// { 
//   std::tuple<Args...> _args; 
//
// public:
//   Adaptor(Args... args) : _args(std::tuple<Args>(args)...) {}
//
//   template<class Iter>
//   C<Iter, Args...> operator()(Iter i) 
//   { return apply(std::move(i), Indices<List<Args...>>{}); }
//
//   template<class Iter, int ...idx>
//   C<Iter, Args...> apply(Iter iter, UnsignedList<idx ...>)
//   { return C<Iter, Args...>(std::move(iter), std::move(std::get<idx>(_args))...); }
// };

using Lib::TypeList::List;
using Lib::TypeList::Indices;
using Lib::TypeList::UnsignedList;

template<class F, class... Capt>
class Capture
{
  
  template<class... Args> using Result = typename std::result_of<F(Capt..., Args...)>::type;
  F _fun;
  std::tuple<Capt...> _capt;
public:
  Capture(F fun, Capt... capt) : _fun(std::move(fun)), _capt(std::forward<Capt>(capt)...) {}

  template<class... Args>
  Result<Args...> operator()(Args... args)
  { return apply(Indices<List<Args...>>{}, std::forward<Args>(args)...); }

  template<class... Args, int... idx>
  Result<Args...> apply(UnsignedList<idx...>, Args... args)
  { return _fun(std::get<idx>(_capt)..., std::forward<Args>(args)...); }
};

template<class F, class... Capt>
Capture<F, Capt...> capture(F f, Capt... capt) 
{ return Capture<F,Capt...>(std::move(f), capt...); }

template<class NumTraits>
ClauseIterator InequalityResolution::generateClauses(Clause* cl1, Literal* lit) const
{
  using Polynom           = Polynom<NumTraits>;
  using Monom             = Monom<NumTraits>;
  using MonomFactors      = MonomFactors<NumTraits>;
  using Numeral           = typename Monom::Numeral;
  using InequalityLiteral = InequalityLiteral<NumTraits>;

  auto lit_ = this->normalizer().normalize<NumTraits>(lit);
  if (lit_.isNone()) 
    ClauseIterator::getEmpty();

  // The rule we compute looks as follows:
  //
  // num1 * term + rest1 >= 0 \/ C1      num2 * term2 + rest2 >= 0 \/ C2
  // --------------------------------------------------------------------
  //         k1 * rest1 + k2 * rest2 >= 0 \/ C1 \/ C2


  auto lit1 = lit_.unwrap();
  //   ^^^^--> num1 * term + rest1 >= 0

  return pvi(iterTraits(maxTerms(lit1))
    .flatMap([this, cl1, lit1](Monom monom)  -> VirtualIterator<Clause*> { 
      auto num1  = monom.numeral;
      auto term1 = monom.factors;

      return pvi(iterTraits(_index->getUnificationsWithConstraints(term1->denormalize(), true))
                .map([this, cl1, lit1, num1, term1](TermQueryResult res) -> Clause* {
                  auto cl2   = res.clause;
                  auto term2 = normalizeTerm(TypedTermList(res.term, NumTraits::sort))
                                .downcast<NumTraits>().unwrap()
                                ->tryMonom().unwrap()
                                .factors;
                  auto lit2_ = res.literal;
                  auto lit2 = this->normalizer().normalize<NumTraits>(lit2_).unwrap();
                  //   ^^^^ ~=  num2 * term2 + rest2 >= 0

                  auto strictness = lit1.strict() || lit2.strict();
                  //   ^^^^^^^^^^ if either of the two inequalities is strict, the result will be as well.
                  //              consider e.g.
                  //                    s + t > 0 /\ u - t >= 0 
                  //                ==> s + t > 0 /\ 0 >= t - u 
                  //                ==> s + t > t - u 
                  //                ==> s + u > 0

                  auto num2 = lit2.term()
                                  .iterSummands()
                                  .find([&](Monom m) { return m.factors == term2; })
                                  .unwrap()
                                  .numeral;

                  auto factors = computeFactors(num1, num2);
                  //   ^^^^^^^--> (k1, k2)

                  Stack<Monom> resolventTerm(lit1.term().nSummands() + lit2.term().nSummands() - 2);
                  //           ^^^^^^^^^^^^^--> gonna be k1 * rest1 + k2 * rest2
                  {
                    auto pushTerms = [&resolventTerm](InequalityLiteral lit, Perfect<MonomFactors> termToSkip, Numeral num)
                              {
                                resolventTerm.loadFromIterator(lit.term().iterSummands()
                                    .filter([&](Monom m) { return m.factors != termToSkip; })
                                    .map   ([&](Monom m) { return Monom(m.numeral * num, m.factors); })
                                );
                              };

                    pushTerms(lit1, term1, factors.first);
                    pushTerms(lit2, term2, factors.second);
                  }

                  // TODO check whether we need to pre-sort the resolventTerms
                  auto resolventLit = InequalityLiteral(perfect(Polynom(std::move(resolventTerm))), strictness);
                  //   ^^^^^^^^^^^^--> k1 * rest1 + k2 * rest2 >= 0

                  Inference inf(GeneratingInference2(Kernel::InferenceRule::INEQUALITY_RESOLUTION, cl1, cl2));
                  auto size = cl1->size() + cl2->size() - 1;
                  auto& resolvent = *new(size) Clause(size, inf);
                  //    ^^^^^^^^^--> gonna be k1 * rest1 + k2 * rest2 >= 0 \/ C1 \/ C2
                  {
                    unsigned offset = 0;
                    resolvent[offset++] = resolventLit.denormalize();
                    auto pushLiterals = 
                      [&resolvent, &offset](Clause& cl, Literal* skipLiteral)
                      {
                        for (unsigned i = 0; i < cl.size(); i++) {
                          if (cl[i] != skipLiteral) {
                            resolvent[offset++] = cl[i];
                          }
                        }
                      };
                    pushLiterals(*cl1, lit1.denormalize());
                    pushLiterals(*cl2, lit2.denormalize());
                  }
                  return &resolvent;
                }));
    }));
}

ClauseIterator InequalityResolution::generateClauses(Clause* premise)
{
  CALL("InequalityResolution::generateClauses");

  return pvi(iterTraits(premise->getSelectedLiteralIterator())
    .flatMap([&](Literal* lit) {
        return getConcatenatedIterator(getConcatenatedIterator(
              generateClauses< IntTraits>(premise, lit) ,
              generateClauses< RatTraits>(premise, lit)),
              generateClauses<RealTraits>(premise, lit));
    }));
}

}
