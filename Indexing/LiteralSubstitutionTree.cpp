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
 * @file LiteralSubstitutionTree.cpp
 * Implements class LiteralSubstitutionTree.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Statistics.hpp"

#include "LiteralSubstitutionTree.hpp"

namespace Indexing
{

LiteralSubstitutionTree::LiteralSubstitutionTree(bool useC)
: _useC(useC)
, _trees(env.signature->predicates() * 2)
{
  //EqualityProxy transformation can introduce polymorphism in a monomorphic problem
  //However, there is no need to guard aginst it, as equalityProxy removes all
  //equality literals. The flag below is only used during the unification of 
  //equality literals.
  _polymorphic = env.property->hasPolymorphicSym() || env.property->higherOrder();
}

void LiteralSubstitutionTree::insert(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTree::insert");
  handleLiteral(lit,cls,true);
}

void LiteralSubstitutionTree::remove(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTree::remove");
  handleLiteral(lit,cls,false);
}

void LiteralSubstitutionTree::handleLiteral(Literal* lit, Clause* cls, bool insert)
{
  CALL("LiteralSubstitutionTree::handleLiteral");
  // TODO make this and insnert one fuction

  Literal* normLit=Renaming::normalize(lit);
  auto& tree = getTree(lit, /* complementary */ false);

  BindingMap svBindings;
  SubstitutionTree::createInitialBindings(normLit, /* reversed */ false, /* withoutTop */ false, 
      [&](auto var, auto term) { 
        svBindings.insert(var, term);
        tree._nextVar = max(tree._nextVar, (int)var + 1);
      });

  tree.handle(svBindings, SubstitutionTree::LeafData(cls, lit), insert);
}

SLQueryResultIterator LiteralSubstitutionTree::getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getUnifications");
  // TODO write non-polymorphic optimization
  return getResultIterator<UnificationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false);
}
SLQueryResultIterator LiteralSubstitutionTree::getUnificationsWithConstraints(Literal* lit, bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getUnificationsWithConstraints");
  // if(_polymorphic){
  return getResultIterator<UnificationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ true);
  // }
}

SLQueryResultIterator LiteralSubstitutionTree::getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getGeneralizations");

  // TODO write non-polymorphic optimization
  return getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false);
}

SLQueryResultIterator LiteralSubstitutionTree::getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getInstances");
  return getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false);
}


class RenamingSubstitution 
: public ResultSubstitution 
{
public:
  Renaming _query;
  Renaming _result;
  RenamingSubstitution(): _query(), _result() {}
  virtual ~RenamingSubstitution() override {}
  virtual TermList applyToQuery(TermList t) final override { return _query.apply(t); }
  virtual Literal* applyToQuery(Literal* l) final override { return _query.apply(l); }
  virtual TermList applyToResult(TermList t) final override { return _result.apply(t); }
  virtual Literal* applyToResult(Literal* l) final override { return _result.apply(l); }

  virtual TermList applyTo(TermList t, unsigned index) final override { ASSERTION_VIOLATION; }
  virtual Literal* applyTo(Literal* l, unsigned index) final override { NOT_IMPLEMENTED; }

  virtual size_t getQueryApplicationWeight(TermList t) final override { return t.weight(); }
  virtual size_t getQueryApplicationWeight(Literal* l) final override  { return l->weight(); }
  virtual size_t getResultApplicationWeight(TermList t) final override { return t.weight(); }
  virtual size_t getResultApplicationWeight(Literal* l) final override { return l->weight(); }

  void output(std::ostream& out) const final override
  { out << "{ _query: " << _query << ", _result: " << _result << " }"; }

};


SLQueryResultIterator LiteralSubstitutionTree::getVariants(Literal* query, bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getVariants");


  auto& tree = getTree(query, complementary);

  RenamingSubstitution* renaming = retrieveSubstitutions ? new RenamingSubstitution() : nullptr;
  ResultSubstitutionSP resultSubst = retrieveSubstitutions ? ResultSubstitutionSP(renaming) : ResultSubstitutionSP();

  Literal* normLit;
  if (retrieveSubstitutions) {
    renaming->_query.normalizeVariables(query);
    normLit = renaming->_query.apply(query);
  } else {
    normLit = Renaming::normalize(query);
  }

  BindingMap svBindings;
  SubstitutionTree::createInitialBindings(normLit, /* reversed */ false, /* withoutTop */ false, 
      [&](auto v, auto t) { {
        tree._nextVar = max<int>(tree._nextVar, v + 1);
        svBindings.insert(v, t);
      } });
  Leaf* leaf = tree.findLeaf(svBindings);
  if(leaf==0) {
    return SLQueryResultIterator::getEmpty();
  }

  return pvi(iterTraits(leaf->allChildren())
    .map([](LeafData ld) { return SLQueryResult(ld.literal, ld.clause);  })
    .map([retrieveSubstitutions, renaming, resultSubst](auto r) 
      {
        if (retrieveSubstitutions) {
          renaming->_result.normalizeVariables(r.literal);
          r.substitution = resultSubst;
        }
        return r;
      })
    );
}

SLQueryResultIterator LiteralSubstitutionTree::getAll()
{
  CALL("LiteralSubstitutionTree::getAll");

  return pvi(
        iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
         .flatMap([this](auto i) { return LeafIterator(&*_trees[i]); })
        // iterTraits(LeafIterator(&tree))
         .flatMap([](Leaf* l) { return l->allChildren(); })
         .map([](const LeafData& ld) { return SLQueryResult(ld.literal, ld.clause); })
      );
}

SubstitutionTree& LiteralSubstitutionTree::getTree(Literal* lit, bool complementary)
{
  auto idx = complementary ? lit->header() : lit->complementaryHeader();
  while (idx >= _trees.size()) {
    _trees.push(make_unique<SubstitutionTree>(_useC));
  }
  return *_trees[idx];
}

template<class Iterator>
SLQueryResultIterator LiteralSubstitutionTree::getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, bool useConstraints)
{
  CALL("LiteralSubstitutionTree::getResultIterator");

  // auto& tree = getTree(lit, complementary);
  auto iter = [&](bool reversed) 
    { return iterTraits(getTree(lit, complementary).iterator<Iterator>(lit, retrieveSubstitutions, useConstraints, /* funcSubtermMap */ nullptr, reversed)) ; };

  auto filterResults = [=](auto it) { 
    return pvi(
        std::move(it)
        // .filter([=](auto& qr) { return complementary ? qr.data->literal->polarity() != lit->polarity() 
        //                                              : qr.data->literal->polarity() == lit->polarity(); })
        .map([](QueryResult qr) { return SLQueryResult(qr.data->literal, qr.data->clause, qr.subst,qr.constr); })
        ); 
  };
  return !lit->commutative() 
    ?  filterResults(iter( /* reversed */ false))
    :  filterResults(concatIters(
        iter( /* reversed */ false),
        iter( /* reversed */ true)
      ));
}

} // namespace Indexing
