/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ALASCA_Inferences_TautologyDeletion__
#define __ALASCA_Inferences_TautologyDeletion__

#include "Forwards.hpp"

#include "Kernel/ALASCA.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class TautologyDeletion
: public ImmediateSimplificationEngine
{
  std::shared_ptr<AlascaState> _shared;
public:
  USE_ALLOCATOR(TautologyDeletion);

  TautologyDeletion(std::shared_ptr<AlascaState> shared) 
    : _shared(std::move(shared)) {}

  struct TermOccurrences {
    bool eq = false;
    bool gt = false;
    bool lt = false;
    int touches = 0;
    TermOccurrences() {};

    friend std::ostream& operator<<(std::ostream& out, TermOccurrences const& self)
    { return out << "{ " << 
          iterItems(
            std::make_tuple(self.lt, "<"),
            std::make_tuple(self.eq, "="),
            std::make_tuple(self.gt, ">"))
          .filter([](auto x) { return std::get<0>(x); })
          .map([](auto x) { return std::get<1>(x); })
          .output(", ") << " }";
      ; }
  };

  virtual Clause* simplify(Clause* premise) override 
  {
    // Map<AlascaLiteralItpAny, bool> lits;
    TIME_TRACE("alasca tautology detection")

    Recycled<Map<AlascaTermItpAny, TermOccurrences>> lits;

    RStack<Literal*> simpl;
    bool merged = false;
    for (auto lit : premise->iterLits()) {
      if (auto l = InequalityNormalizer::normalize(lit).asItp()) {
        l->apply([&](auto l) {
            auto self = AlascaTermItpAny(l.term());
            auto opposite = AlascaTermItpAny(-l.term());
            auto smaller = self < opposite ? self : opposite;

            TermOccurrences* cont;
            if (auto x = lits->getPtr(smaller)) {
              merged = true;
              cont = x;
            } else {
              cont = &lits->insert(smaller, TermOccurrences());
            }
            cont->touches++;

            switch (l.symbol()) {
              case AlascaPredicate::EQ: 
                 cont->eq = true;
                 break;
              case AlascaPredicate::NEQ: 
                 cont->gt = true;
                 cont->lt = true;
                 break;
              case AlascaPredicate::GREATER: 
                 if (smaller == self) {
                   cont->gt = true;
                 } else {
                   cont->lt = true;
                 }
                 break;
              case AlascaPredicate::GREATER_EQ: 
                 if (smaller == self) {
                   cont->gt = true;
                 } else {
                   cont->lt = true;
                 }
                 cont->eq = true;
                 break;
            }
        });
      } else {
        simpl->push(lit);
      }
    }
    if (merged) {
      for (auto& entry : iterTraits(lits->iter())) {
        auto& cont = entry.value();
        auto pushLit = [&](auto f)  {
          entry.key().apply([&](auto t) {
              auto n = t.numTraits();
              auto lit = f(n, t);
              if (cont.touches > 1) {
                DEBUG(1, "merging ", t, " ", cont, " ", 0, " ==> ", *lit)
              }
              simpl->push(lit);
          });
        };
        if (cont.gt && cont.eq && cont.lt) {
          /* tautology */
          DEBUG(0, "deleting tautology: ", entry.key(), " ", cont, " ", 0);
          return nullptr;

        } else if ( cont.gt && !cont.eq && !cont.lt) {
          pushLit([](auto n, auto t) 
              { return n.greater(true, t.toTerm(), n.zero()); });

        } else if (!cont.gt && !cont.eq &&  cont.lt) {
          pushLit([](auto n, auto t) 
              { return n.greater(true, (-t).toTerm(), n.zero()); });

        } else if ( cont.gt &&  cont.eq && !cont.lt) {
          pushLit([](auto n, auto t) 
              { return n.geq(true, t.toTerm(), n.zero()); });

        } else if (!cont.gt &&  cont.eq &&  cont.lt) {
          pushLit([](auto n, auto t) 
              { return n.geq(true, (-t).toTerm(), n.zero()); });

        } else if ( cont.gt && !cont.eq &&  cont.lt) {
          pushLit([](auto n, auto t) 
              { return n.eq(false, t.toTerm(), n.zero()); });

        } else if (!cont.gt &&  cont.eq && !cont.lt) {
          pushLit([](auto n, auto t) 
              { return n.eq(true, t.toTerm(), n.zero()); });

        } else {
          ASSERTION_VIOLATION_REP(std::make_tuple(cont.gt, cont.eq, cont.lt))
        }
      }

      return Clause::fromStack(*simpl, Inference(SimplifyingInference1(Kernel::InferenceRule::ALASCA_INEQUALITY_MERGING, premise)));
    } else {
      return premise;
    }
    
    // for (auto lit : iterTraits(premise->iterLits())) {
    //   auto norm_ = _shared->norm().tryNormalizeInterpreted(lit);
    //   if (norm_.isSome()) {
    //     auto norm = norm_.unwrap();
    //     lits.insert(norm, true);
    //     auto opposite = norm.apply([&](auto lit) { return AlascaLiteralItpAny(lit.negation()); });
    //     if (lits.find(opposite)) {
    //       // std::cout << "bla" << std::endl;
    //       return nullptr;
    //     }
    //   }
    // }

    return premise;
  }
};

#undef DEBUG
} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_TautologyDeletion__*/
