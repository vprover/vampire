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
 * @file LiteralSubstitutionTree.hpp
 * Defines class LiteralSubstitutionTree.
 */


#ifndef __LiteralSubstitutionTree__
#define __LiteralSubstitutionTree__

#include "Indexing/Index.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Lib/VirtualIterator.hpp"
#include "LiteralIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

/** A wrapper class around SubstitutionTree that makes it usable  as a LiteralIndexingStructure */
class LiteralSubstitutionTree
: public LiteralIndexingStructure
{
  using FastInstancesIterator = SubstitutionTree::FastInstancesIterator;
  using BindingMap = SubstitutionTree::BindingMap;
  using LDIterator = SubstitutionTree::LDIterator;
  using FastGeneralizationsIterator = SubstitutionTree::FastGeneralizationsIterator;
  using LeafData = SubstitutionTree::LeafData;
  using LeafIterator = SubstitutionTree::LeafIterator;
  using Leaf = SubstitutionTree::Leaf;

public:
  CLASS_NAME(LiteralSubstitutionTree);
  USE_ALLOCATOR(LiteralSubstitutionTree);

  LiteralSubstitutionTree(Shell::Options::UnificationWithAbstraction uwa);

  void insert(Literal* lit, Clause* cls) override { handleLiteral(lit, cls, /* insert */ true); }
  void remove(Literal* lit, Clause* cls) override { handleLiteral(lit, cls, /* insert */ false); }

  SLQueryResultIterator getAll() final override;
  void handleLiteral(Literal* lit, Clause* cls, bool insert)
  { getTree(lit, /* complementary */ false).handle(lit, SubstitutionTree::LeafData(cls, lit), insert); }

  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions) final override;
  VirtualIterator<LQueryRes<AbstractingUnifier*>> getUwa(Literal* lit, bool complementary) final override;
  SLQueryResultIterator getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions) final override;
  SLQueryResultIterator getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions) final override;
  SLQueryResultIterator getVariants(Literal* lit, bool complementary, bool retrieveSubstitutions) final override;

#if VDEBUG
  virtual void markTagged() final override { }
#endif

  friend std::ostream& operator<<(std::ostream& out, LiteralSubstitutionTree const& self)
  { 
    int i = 0;
    out << "{ ";
    for (auto& t : self._trees) {
      auto f = env.signature->getPredicate(i / 2);
      bool p = i % 2;
      if (p) out << "~";
      out << *f << "(" << t << "), "; 
      i++;
    }
    return out << "} ";
  }
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<LiteralSubstitutionTree> const& self)
  { 
    int i = 0;
    out << "{ " << endl;
    for (auto& t : self.self._trees) {
      auto f = env.signature->getPredicate(i / 2);
      bool p = i % 2;
      OutputMultiline<LiteralSubstitutionTree>::outputIndent(out, self.indent);
      out << (p ? "~" : " ") << *f << "(" << multiline(t, self.indent + 1) << ")" << endl; 
      i++;
    }
    return out << "} ";
  }


private:
  SubstitutionTree& getTree(Literal* lit, bool complementary);

  // static auto createSLQueryResult(SubstitutionTree::QueryResult<Option<AbstractingUnifier*>> r)
  // { return lQueryRes(r.data->literal, r.data->clause, *r.unif); }
  //
  // static auto createSLQueryResult(SubstitutionTree::QueryResult<Option<RobSubstitutionSP>> r)
  // { return SLQueryResult(r.data->literal, r.data->clause, ResultSubstitutionSP((ResultSubstitution*)&*r.unif.unwrapOrElse([](){return RobSubstitutionSP();}))); }


  template<class Iterator, class... Args>
  auto getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, Args... args)
  {
    CALL("LiteralSubstitutionTree::getResultIterator");

    auto iter = [=](bool reversed) 
      { return iterTraits(getTree(lit, complementary).iterator<Iterator>(lit, retrieveSubstitutions, reversed, args...)) ; };

    auto filterResults = [=](auto it) { 
      return pvi(
          std::move(it)
          .map([](auto r) { return lQueryRes(r.data->literal, r.data->clause, std::move(r.unif)); })
          ); 
    };
    return !lit->commutative() 
      ?  filterResults(iter( /* reversed */ false))
      :  filterResults(concatIters(
          iter( /* reversed */ false),
          iter( /* reversed */ true)
        ));
  }


  Stack<SubstitutionTree> _trees;
  MismatchHandler _mismatchHandler;
};

};

#endif /* __LiteralSubstitutionTree__ */
