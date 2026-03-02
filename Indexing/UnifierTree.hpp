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
 * @file UnifierTree.hpp
 * Defines class UnifierTree.
 */

#ifndef __UnifierTree__
#define __UnifierTree__

#include "Debug/Assertion.hpp"
#include "Indexing/Index.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Metaiterators.hpp"
#include "SubstitutionTree.hpp"
#include "TermIndexingStructure.hpp"

namespace Indexing {

class UnifierTree : public TermIndexingStructure<TermLiteralClause>
{
public:
  ~UnifierTree() override {
    for (const auto& [f,ptr] : iterTraits(data.items())) {
      delete ptr;
    }
  }

  void handle(TermLiteralClause t, bool insert) final
  {
    if (t.term.isVar()) {
      if (insert) {
        vars.push(new TermLiteralClause(t));
      } else {
        for (unsigned i = 0; i < vars.size();) {
          if (*vars[i] == t) {
            std::swap(vars[i],vars.top());
            delete vars.pop();
          } else {
            i++;
          }
        }
      }
      return;
    }

    if (insert) {
      DHSet<TermLiteralClause*>** ptr;
      if (data.getValuePtr(t.term.term()->functor(), ptr)) {
        *ptr = new DHSet<TermLiteralClause*>();
      }
      ALWAYS((*ptr)->insert(new TermLiteralClause(t)));
    } else {
      auto ptr = data.findPtr(t.term.term()->functor());
      bool found = false;
      DHSet<TermLiteralClause*>::DelIterator dit(**ptr);
      while (dit.hasNext()) {
        auto e = dit.next();
        if (*e == t) {
          delete e;
          dit.del();
          found = true;
        }
      }
      ASS(found);
    }
  }

  VirtualIterator<QueryRes<AbstractingUnifier*, TermLiteralClause>> getUwa(TypedTermList t, Options::UnificationWithAbstraction, bool fixedPointIteration) override
  {
    if (t.isVar()) {
      ASS(vars.isEmpty()); // we shouldn't unify vars with vars in the current setup

      return pvi(iterTraits(data.items())
        .flatMap([](auto kv) {
          return kv.second->iterator();
        })
        .map([this,t](TermLiteralClause* val) {
          absUnif.subs().reset();
          absUnif.constr().reset();

          ALWAYS(absUnif.subs().unify(t, RetrievalAlgorithms::DefaultVarBanks::query, val->term, RetrievalAlgorithms::DefaultVarBanks::internal));
          return QueryRes<AbstractingUnifier*, TermLiteralClause>(&absUnif, val);
        }));
    }

    ASS(t.isTerm());

    auto ptr = data.findPtr(t.term()->functor());
    if (!ptr) {
      return VirtualIterator<QueryRes<AbstractingUnifier*, TermLiteralClause>>::getEmpty();
    }

    return pvi(iterTraits((*ptr)->iter())
      .map([this,t](TermLiteralClause* val) -> QueryRes<AbstractingUnifier*, TermLiteralClause> {
        absUnif.subs().reset();
        absUnif.constr().reset();

        ASS_EQ(t.term()->functor(), val->term.term()->functor());
        for (unsigned i = 0; i < t.term()->arity(); i++) {
          auto lhs = *t.term()->nthArgument(i);
          auto rhs = *val->term.term()->nthArgument(i);

          if (lhs.isVar()) {
            if (!absUnif.subs().unify(lhs, RetrievalAlgorithms::DefaultVarBanks::query, rhs, RetrievalAlgorithms::DefaultVarBanks::internal)) {
              // std::cout << "failed1" << std::endl;
              // return QueryRes<AbstractingUnifier*, TermLiteralClause>(nullptr, nullptr);
              absUnif.constr().add(UnificationConstraint(
                TermSpec(lhs, RetrievalAlgorithms::DefaultVarBanks::query),
                TermSpec(rhs, RetrievalAlgorithms::DefaultVarBanks::internal),
                TermSpec(SortHelper::getArgSort(t.term(), i), RetrievalAlgorithms::DefaultVarBanks::query)),
              Option<BacktrackData&>());
            }
          } else if (rhs.isVar()) {
            if (!absUnif.subs().unify(rhs, RetrievalAlgorithms::DefaultVarBanks::internal, lhs, RetrievalAlgorithms::DefaultVarBanks::query)) {
              // std::cout << "failed2" << std::endl;
              // return QueryRes<AbstractingUnifier*, TermLiteralClause>(nullptr, nullptr);
              absUnif.constr().add(UnificationConstraint(
                TermSpec(lhs, RetrievalAlgorithms::DefaultVarBanks::query),
                TermSpec(rhs, RetrievalAlgorithms::DefaultVarBanks::internal),
                TermSpec(SortHelper::getArgSort(t.term(), i), RetrievalAlgorithms::DefaultVarBanks::query)),
              Option<BacktrackData&>());
            }
          } else {
            absUnif.constr().add(UnificationConstraint(
              TermSpec(lhs, RetrievalAlgorithms::DefaultVarBanks::query),
              TermSpec(rhs, RetrievalAlgorithms::DefaultVarBanks::internal),
              TermSpec(SortHelper::getArgSort(t.term(), i), RetrievalAlgorithms::DefaultVarBanks::query)),
            Option<BacktrackData&>());
          }
          // std::cout << "unifier tree " << lhs << " " << rhs << " " << absUnif << std::endl;
        }
        // std::cout << "val " << &val << " " << val << std::endl;

        return QueryRes<AbstractingUnifier*, TermLiteralClause>(&absUnif, val);
      }));
      // .filter([](const auto& val) { return val.unifier; }));
  }

  void output(std::ostream& out) const final { out << data; }

private:
  DHMap<unsigned, DHSet<TermLiteralClause*>*> data;
  Stack<TermLiteralClause*> vars;
  AbstractingUnifier absUnif;
};

}
#endif // __UnifierTree__
