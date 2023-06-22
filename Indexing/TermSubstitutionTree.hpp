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

#if VHOL
#include "Kernel/HOLUnification.hpp"
#endif

namespace Indexing {

/*
 * As of 22/03/2023 TermSubstitutionTrees carry our type checking.
 * Thus, there is no need to check whether the type of returned terms match those of the query
 * as this is now done within the tree.
 */


/** A wrapper class around SubstitutionTree that makes it usable  as a TermIndexingStructure */
class TermSubstitutionTree
: public TermIndexingStructure
{
  using AbstractingAlgo = UnificationAlgorithms::AbstractingUnification;
  using RobAlgo = UnificationAlgorithms::RobUnification;
  using LeafData = SubstitutionTree::LeafData;
  using FastInstancesIterator = SubstitutionTree::FastInstancesIterator;
  using FastGeneralizationsIterator = SubstitutionTree::FastGeneralizationsIterator;  
#if VHOL
  using HOLAlgo = UnificationAlgorithms::HOLUnification;
  using HOLInstAlgo = UnificationAlgorithms::HOLInstantiation;
  using HOLGenAlgo = UnificationAlgorithms::HOLGeneralisation;    
#endif

public:
  CLASS_NAME(TermSubstitutionTree);
  USE_ALLOCATOR(TermSubstitutionTree);

  explicit TermSubstitutionTree(SplittingAlgo algo = SplittingAlgo::NONE);

  void handle(TypedTermList t, Literal* lit, Clause* cls, bool adding)
  { handleTerm(t, LeafData(cls, lit, t), adding); }

  void insert(TypedTermList t, Literal* lit, Clause* cls) override 
  { handleTerm(t, LeafData(cls,lit,t), /* insert */ true); }

  void remove(TypedTermList t, Literal* lit, Clause* cls) override
  { handleTerm(t, LeafData(cls,lit,t), /* insert */ false); }

  void insert(TypedTermList t, TermList trm) override 
  { handleTerm(t, LeafData(0, 0, t, trm), /* insert */ true); }

  void insert(TypedTermList t, TermList trm, Literal* lit, Clause* cls) override 
  { handleTerm(t, LeafData(cls, lit, t, trm), /* insert */ true); }

  void remove(TypedTermList t, TermList trm, Literal* lit, Clause* cls) override 
  { handleTerm(t, LeafData(cls, lit, t, trm), /* insert */ false); }

  bool generalizationExists(TermList t) override
  { return t.isVar() ? false : _tree->generalizationExists(TypedTermList(t.term())); }

#if VDEBUG
  virtual void markTagged() override { _tree->markTagged();}
#endif

  virtual void output(std::ostream& out) const final override { out << *this; }

#if VHOL
  void useExtra(){ _extra = true; }
#endif

private:
  
  void handleTerm(TypedTermList tt, LeafData ld, bool insert){
#if VHOL
    if(env.property->higherOrder() && _algo == SplittingAlgo::HOL_UNIF){
      // replace higher-order terms with placeholder constants
      tt = TypedTermList(ToPlaceholders().replace(tt), tt.sort());
    }
#endif
    _tree->handle(tt, ld, insert); }

  template<class Iterator, class... Args>
  auto getResultIterator(TypedTermList query, bool retrieveSubstitutions, Args... args)
  {
    return iterTraits(_tree->iterator<Iterator>(query, retrieveSubstitutions, /* reversed */  false, std::move(args)...))
      .map([
#if VHOL
        this
#endif
        ](auto qr)
        { return tQueryRes(
#if VHOL
            _extra ? qr.data->extraTerm : 
#endif
            qr.data->term,
            qr.data->literal, qr.data->clause, std::move(qr.unif)); }) ;
  }

#if VHOL
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
  bool _extra;
#endif
  SplittingAlgo _algo;
  unique_ptr<SubstitutionTree> _tree;

  friend std::ostream& operator<<(std::ostream& out, TermSubstitutionTree const& self)
  { return out <<  *self._tree; }
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<TermSubstitutionTree> const& self)
  { return out << multiline(*self.self._tree, self.indent); }

public:
  TermQueryResultIterator getInstances(TypedTermList t, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions)); }

  TermQueryResultIterator getGeneralizations(TypedTermList t, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<FastGeneralizationsIterator>(t, retrieveSubstitutions)); }

  TermQueryResultIterator getUwa(TypedTermList t) final override
  { 
    static auto uwa                 = env.options->unificationWithAbstraction();
    static bool fixedPointIteration = env.options->unificationWithAbstractionFixedPointIteration();

    return pvi(getResultIterator<SubstitutionTree::TreeIterator<AbstractingAlgo>>(t, true, MismatchHandler(uwa), fixedPointIteration));
  }

  TermQueryResultIterator getUnifications(TypedTermList t, bool retrieveSubstitutions) override
  { return pvi(getResultIterator<SubstitutionTree::TreeIterator<RobAlgo>>(t, retrieveSubstitutions)); }

#if VHOL
  TermQueryResultIterator getHOLUnifiers(TypedTermList t) final override
  { 
    TypedTermList tp = TypedTermList(ToPlaceholders().replace(t), t.sort());
    return pvi(getResultIterator<SubstitutionTree::TreeIterator<HOLAlgo>>(tp, true, t));
  }

  TermQueryResultIterator getHOLInstances(TypedTermList t) final override
  {  return pvi(getResultIterator<SubstitutionTree::TreeIterator<HOLInstAlgo>>(t, true)); }

  TermQueryResultIterator getHOLGeneralizations(TypedTermList t) final override
  {  return pvi(getResultIterator<SubstitutionTree::TreeIterator<HOLGenAlgo>>(t, true)); }    
#endif  
};

};

#endif /* __TermSubstitutionTree__ */
