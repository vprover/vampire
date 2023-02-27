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
 * @file TermSubstitutionTree.hpp
 * Defines class TermSubstitutionTree.
 */


#ifndef __TermSubstitutionTree__
#define __TermSubstitutionTree__


#include "Forwards.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/BiMap.hpp"

#include "Index.hpp"
#include "TermIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

/*
 * Note that unlike LiteralSubstitutionTree, TermSubstitutionTree does
 * not (yet) carry out sort checking when attempting to find unifiers, generalisations
 * or instances. In particular, if the query or result is a variable, it is the callers'
 * responsibility to ensure that the sorts are unifiable/matchable
 * (edit: if the caller inserts a TypedTermList instead of a TermList, this will be handled automatically.)
 */


/** A wrapper class around SubstitutionTree that makes it usable  as a TermIndexingStructure */
class TermSubstitutionTree
: public TermIndexingStructure, SubstitutionTree
{
public:
  CLASS_NAME(TermSubstitutionTree);
  USE_ALLOCATOR(TermSubstitutionTree);

  /*
   * The extra flag is a higher-order concern. it is set to true when
   * we require the term query result to include two terms, the result term
   * and another.
   *
   * The main use case is to store a different term in the leaf to the one indexed
   * in the tree. This is used for example in Skolemisation on the fly where we
   * store Terms of type $o (formulas) in the tree, but in the leaf we store
   * the skolem terms used to witness them (to facilitate the reuse of Skolems)
   */
  TermSubstitutionTree(Shell::Options::UnificationWithAbstraction uwa, bool uwaPostpro, bool extra);

  void handle(TypedTermList tt, Literal* lit, Clause* cls, bool insert)
  { handleTerm(tt, LeafData(cls,lit,tt), insert); }

  void insert(TermList t, Literal* lit, Clause* cls) override
  { handleTerm(t, LeafData(cls,lit,t), /* insert */ true); }

  void remove(TermList t, Literal* lit, Clause* cls) override
  { handleTerm(t, LeafData(cls,lit,t), /* insert */ false); }

  void insert(TermList t, TermList trm) override
  { handleTerm(t, LeafData(0, 0, t, trm), /* insert */ true); }

  void insert(TermList t, TermList trm, Literal* lit, Clause* cls) override
  { handleTerm(t, LeafData(cls, lit, t, trm), /* insert */ true); }

  bool generalizationExists(TermList t) override
  { return t.isVar() ? false : SubstitutionTree::generalizationExists(t); }


#if VDEBUG
  virtual void markTagged() override { SubstitutionTree::markTagged();}
  virtual void output(std::ostream& out) const final override { out << *this; }
#endif

private:

  template<class TypedOrUntypedTermList>
  void handleTerm(TypedOrUntypedTermList tt, LeafData ld, bool insert)
  { SubstitutionTree::handle(tt, ld, insert); }

  template<class Iterator, class TypedOrUntypedTermList, class... Args>
  auto getResultIterator(TypedOrUntypedTermList query, bool retrieveSubstitutions, Args... args)
  {
    return iterTraits(SubstitutionTree::iterator<Iterator>(query, retrieveSubstitutions, /* reversed */  false, std::move(args)...))
      .map([this](auto qr)
        { return tQueryRes(
            _extra ? qr.data->extraTerm : qr.data->term,
            qr.data->literal, qr.data->clause, std::move(qr.unif)); }) ;
  }

  MismatchHandler _mismatchHandler;
  bool _uwaPostpro;
  //higher-order concerns
  bool _extra;

  friend std::ostream& operator<<(std::ostream& out, TermSubstitutionTree const& self)
  { return out << (SubstitutionTree const&) self; }
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<TermSubstitutionTree> const& self)
  { return out << multiline((SubstitutionTree const&) self.self, self.indent); }

  auto nopostproUwa(TypedTermList t)
  { return getResultIterator<UnificationsIterator<UnificationAlgorithms::UnificationWithAbstraction>>(t, /* retrieveSubstitutions */ true, _mismatchHandler); }

  auto postproUwa(TypedTermList t)
  { return iterTraits(getResultIterator<UnificationsIterator<UnificationAlgorithms::UnificationWithAbstractionWithPostprocessing>>(t, /* retrieveSubstitutions */ true, _mismatchHandler))
    .filterMap([](TQueryRes<UnificationAlgorithms::UnificationWithAbstractionWithPostprocessing::NotFinalized> r)
        { return r.unifier.fixedPointIteration().map([&](AbstractingUnifier* unif) { return tQueryRes(r.term, r.literal, r.clause, unif); }); }); }

public:
  TermQueryResultIterator getInstances(TermList t, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions)); }

  TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<FastGeneralizationsIterator>(t, retrieveSubstitutions)); }


  VirtualIterator<TQueryRes<AbstractingUnifier*>> getUwa(TypedTermList t) override
  { return _uwaPostpro ? pvi(  postproUwa(t))
                       : pvi(nopostproUwa(t)); }

  TermQueryResultIterator getUnifications(TermList t, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<UnificationsIterator<UnificationAlgorithms::RobUnification>>(t, retrieveSubstitutions)); }

  TermQueryResultIterator getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<UnificationsIterator<UnificationAlgorithms::RobUnification>>(tt, retrieveSubstitutions)); }


};

};

#endif /* __TermSubstitutionTree__ */
