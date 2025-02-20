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
 * @file Superposition.hpp
 * Defines class Superposition
 *
 */

#ifndef __ALASCA_Inferences_Superposition__
#define __ALASCA_Inferences_Superposition__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Indexing/IndexManager.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/State.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/NumTraits.hpp"
#include "BinInf.hpp"
#include "Lib/Reflection.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct SuperpositionConf
{
  std::shared_ptr<AlascaState> _shared;
  // TODO make option and test and double check (?)
  bool _simultaneousSuperposition;

  SuperpositionConf(std::shared_ptr<AlascaState> shared, bool simultanious = true) : _shared(shared), _simultaneousSuperposition(simultanious) {  }

  static const char* name() { return "alasca superposition"; }

  struct Lhs : public SelectedEquality
  {
    static const char* name() { return "alasca superposition lhs"; }

    Lhs(SelectedEquality inner) : SelectedEquality(std::move(inner)) {}


    static auto iter(AlascaState& shared, Clause* cl)
    {
      return shared.selectedEqualities(cl, /* literal */ SelectionCriterion::NOT_LEQ, 
                                           /* terms   */ SelectionCriterion::NOT_LEQ,
                                           /* include number vars */ false)
             .filter([](auto x) { return x.literal()->isPositive(); })
             .filter([](auto& l) { return !forAnyNumTraits([&](auto n) { return n.isNumeral(l.biggerSide()); }); })
             .map([](auto x) { return Lhs(std::move(x)); });
    }

    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_LHS_SUBST_TREE; }
  };

  struct Rhs : public SelectedLiteral
  {
    static const char* name() { return "alasca superposition rhs"; }
    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_RHS_SUBST_TREE; }

    Rhs(SelectedLiteral lit, TypedTermList toRewrite, bool inLitPlus) 
      : SelectedLiteral(std::move(lit))
      , _toRewrite(toRewrite)
      , _inLitPlus(inLitPlus)
    {  }

    TypedTermList _toRewrite;
    bool _inLitPlus;

    TypedTermList toRewrite() const { return _toRewrite; }

    TypedTermList key() const { return toRewrite(); }
    TermList sort() const { return toRewrite().sort(); }

    bool inLitPlus() const
    { return _inLitPlus; }

    static auto activePositions(AlascaState& shared, Clause* cl) 
    {
      return shared.selectedActivePositions(cl, 
          /* literals */ SelectionCriterion::NOT_LESS, 
          /* terms    */ SelectionCriterion::NOT_LEQ,
          /* include number vars */ false);
    }

    static auto iter(AlascaState& shared, Clause* cl)
    { 
      using Out = Rhs;
      return activePositions(shared, cl)
        .flatMap([&](auto sel_lit) -> VirtualIterator<Out> {
           auto tup = sel_lit.match(
             [=](SelectedSummand& x) -> std::tuple<SelectedLiteral, TermList, bool, bool> 
             {
                auto inLitPlus = 
                      x.isInequality() 
                        // x =  `+k s + t > 0`
                        ? x.numeral().apply([](auto n) { return n.isPositive(); })
                        // x =  `t ~ 0`
                        : x.literal()->isPositive();
                auto term = x.selectedAtom();
                return std::make_tuple(std::move(x), term, inLitPlus, /* includeSelf */ true);
             },

             [](SelectedUninterpretedEquality& x) 
             {  
                auto inLitPlus = x.literal()->isPositive();
                auto term = x.biggerSide();
                return std::make_tuple(std::move(x), term, inLitPlus, /* includeSelf */ true); 
             },

             [](SelectedUninterpretedPredicate& x)
             { 
                auto inLitPlus = x.literal()->isPositive();
                auto term = TermList(x.literal());
                return std::make_tuple(std::move(x), term, inLitPlus, /* includeSelf */ false); 
             });

           auto sel = std::get<0>(tup);
           auto term = std::get<1>(tup);
           auto inLitPlus = std::get<2>(tup);
           auto includeSelf = std::get<3>(tup);

           if (term.isVar()) {
             return VirtualIterator<Out>::getEmpty();
           } else {
             return pvi(iterTraits(vi(new NonVariableNonTypeIterator(term.term(), includeSelf)))
                 // .filter([](auto& t) { return SortHelper::getResultSort(t) == IntTraits::sort() || AlascaState::globalState->isAtomic(t); })
                 .filter([](auto& t) { return AlascaState::globalState->isAtomic(t); })
                 .map([=](auto t) { return Rhs(sel, t, inLitPlus); }))
               ;
           }
        })
      .inspect([](auto& x) { ASS_REP(x.literal()->containsSubterm(x.toRewrite()), Output::cat(x, "\n", *x.literal(), "\n", x.toRewrite())); })
      ;
    }
      

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { 
      out << *self.literal();
      for (auto l : self.contextLiterals()) {
        out << " \\/ " << *l;
      }
      out << "[ " << self.toRewrite() << " ] ( inLitPlus: " << self.inLitPlus() << " )";
      return out; 
    }
  };


  auto applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const 
  { return applyRule_(lhs,lhsVarBank, rhs, rhsVarBank, uwa).intoIter(); }

  Option<Clause*> applyRule_(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const;
};

struct Superposition 
: public BinInf<SuperpositionConf> 
{
  template<class... Args>
  Superposition(std::shared_ptr<AlascaState> shared, Args... args) : BinInf<SuperpositionConf>(shared, SuperpositionConf(shared, args...)) {}
};

struct SuperpositionDemodConf
{
  std::shared_ptr<AlascaState> _shared;

  SuperpositionDemodConf(std::shared_ptr<AlascaState> shared) : _shared(shared) {  }

  static const char* name() { return "alasca superposition demodulation"; }

  struct Condition {
    Term* bigger;
    TermList smaller;
    Clause* cl;

    Clause* clause() const { return cl; }
    TypedTermList key() const { return bigger; };
    auto asTuple() const { return std::tie(bigger, smaller); };
    IMPL_COMPARISONS_FROM_TUPLE(Condition);
    auto smallerSide() const { return smaller; }
    auto biggerSide() const { return bigger; }

    friend std::ostream& operator<<(std::ostream& out, Condition const& self)
    { return out << self.bigger << " -> " << self.smaller; }

    static auto iter(AlascaState& shared, Clause* cl)
    { return ifElseIter(cl->size() != 1 || !(*cl)[0]->isEquality()
        , []() { return iterItems<Condition>(); }
        , [&]() { return SuperpositionConf::Lhs::iter(shared, cl)
                          .map([](auto lhs) { 
                              ASS_REP(lhs.biggerSide().isTerm(), "rewriting a variable to something does not make any sense") 
                              return Condition { .bigger = lhs.biggerSide().term(), .smaller = lhs.smallerSide(), .cl = lhs.clause()  }; }); }); }

    static const char* name() { return "superposition demod condition"; }
    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_DEMOD_CONDITION_SUBST_TREE; }
  };


  struct ToSimpl {
    Term* term;
    Clause* cl;
    Clause* clause() const { return cl; }
    TypedTermList key() const { return term; };
    auto asTuple() const { return std::tie(term, cl); };
    IMPL_COMPARISONS_FROM_TUPLE(ToSimpl);

    friend std::ostream& operator<<(std::ostream& out, ToSimpl const& self)
    { return out << *self.clause() << "[ " << *self.term << " ]"; }

    static auto iter(AlascaState& shared, Clause* cl)
    { 
      return iterTraits(cl->iterLits())
        .flatMap([=](auto lit) {
            // TODO remove the new stuff and virtualization here
            return iterTraits(vi(new NonVariableNonTypeIterator(lit)))
              .map([=](Term* t) -> ToSimpl { return ToSimpl { .term = t, .cl = cl, }; });
        });
    }

    static const char* name() { return "superposition demod toSimpl"; }
    static IndexType indexType() { return Indexing::ALASCA_SUPERPOSITION_DEMOD_TO_SIMPL_SUBST_TREE; }
  };

  // s ≈ t           C[sσ]       
  // ====================
  //       C[tσ]
  //
  // where
  // - sσ ≻ tσ
  // - C[sσ] ≻ (s = t)σ
  template<class Sigma>
  Option<Clause*> apply(
      Condition const& cond,
      ToSimpl const& simpl,
      Sigma sigma
      ) const 
  {
    DEBUG(1, "cond:   ", cond)
    DEBUG(1, "simpl:  ", simpl)
    auto s = cond.biggerSide();
    auto t = cond.smallerSide();
    auto sσ = simpl.key();
    auto tσ = sigma(t);


// TODO unify this aproach among all alasca rules
#define check_side_condition(cond, cond_code)                                             \
    if (!(cond_code)) {                                                                   \
      DEBUG(1, "side condition not fulfiled: ", cond)                                     \
      return {};                                                                   \
    }                                                                                     \

    ASS_EQ(sigma(TermList(s)), sσ)

    check_side_condition("sσ ≻ tσ", 
        _shared->greater(TermList(sσ), tσ))

    auto condσ = Literal::createEquality(true, sσ, tσ, sσ.sort());
    check_side_condition("C[sσ] ≻ (s ≈ t)σ", 
         /* optimization for alasca literal ordering:
          * if we have some literal L[sσ] ∈ C[sσ] that is not a positive equality, 
          * then we know that  L[sσ] ≻ (s ≈ t)σ  in alasca's literal ordering */
        (_shared->ordering->isAlascaLiteralOrdering() && 
           /* check L[sσ] ≻ (s ≈ t)σ */
           iterTraits(simpl.clause()->iterLits())
             .any([](auto lit) { return !lit->isEquality() || lit->isNegative(); }))

       || iterTraits(simpl.clause()->iterLits())
            .any([&](auto lit)
                { return _shared->greater(lit, condσ); })
        )

#undef check_side_condition

    auto cl =  Clause::fromIterator(
            iterTraits(simpl.clause()->iterLits())
              .map([&](auto lit) { return EqHelper::replace(lit, sσ, tσ); }),
            Inference(SimplifyingInference2(
                Kernel::InferenceRule::ALASCA_SUPERPOSITION_DEMOD, 
                simpl.clause(), cond.clause()))
            );
    DEBUG(1, "result: ", *cl)
    DEBUG(1, "")
    return some(cl);
  }
};
#undef DEBUG
} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_Superposition__*/
