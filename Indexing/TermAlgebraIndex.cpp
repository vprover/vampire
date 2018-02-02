
/*
 * File TermAlgebraIndex.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file ChainIndex.cpp
 * Implements class ChainIndex
 */

#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Lib/Backtrackable.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Shell/TermAlgebra.hpp"

#include "TermAlgebraIndex.hpp"

using namespace Kernel;
using namespace Lib;

namespace Indexing
{
  unsigned ChainQueryResult::totalLengthClauses()
  {
    CALL("ChainQueryResult::totalLengthClauses");

    unsigned n = 0;
    List<Clause*>::Iterator it(premises);
    while (it.hasNext()) {
      n += it.next()->length();
    }

    return n;
  }

  // add t if not already present in l (set union, but based on term
  // equality)
  void addSubterm(TermList t, List<TermList>*& l)
  {
    CALL("addSubterm");
    
    List<TermList>::Iterator it(l);
    while (it.hasNext()) {
      if (TermList::equals(t, it.next())) {
        return;
      }
    }
    List<TermList>::push(t, l);
  }
  
  List<TermList>* ChainIndex::getSubterms(Term *t)
  {
    CALL("ChainIndex::getSubterms");
    
    Stack<Term*> toVisit;
    List<TermList>* res = List<TermList>::empty();
    
    unsigned sort = SortHelper::getResultSort(t);
    ASS(env.signature->isTermAlgebraSort(sort));
    TermAlgebra* ta = env.signature->getTermAlgebraOfSort(sort);

    toVisit.push(t);

    while (toVisit.isNonEmpty()) {
      Term *u = toVisit.pop();
      if (env.signature->getFunction(u->functor())->termAlgebraCons()) {
        for (unsigned i = 0; i < u->arity(); i++) {
          if (ta->isMutualTypeSort(SortHelper::getArgSort(u, i))) {
            TermList *s = u->nthArgument(i);
            addSubterm(*s, res);
            if (s->isTerm()) {
              toVisit.push(s->term());
            }
          }
        }
      }
    }
    
    return res;
  }

  bool ChainIndex::matchesPattern(Literal *lit, TermList *&fs, TermList *&t, unsigned *sort, bool matchDT, bool matchCDT)
  {
    CALL("ChainIndex::matchesPattern");

    if (!lit->isEquality() || !lit->polarity()) {
      return false;
    }

    *sort = SortHelper::getEqualityArgumentSort(lit);
    if (!env.signature->isTermAlgebraSort(*sort)) {
      return false;
    }
    if (!matchCDT && env.signature->getTermAlgebraOfSort(*sort)->allowsCyclicTerms()) {
      return false;
    }
    if (!matchDT && !env.signature->getTermAlgebraOfSort(*sort)->allowsCyclicTerms()) {
      return false;
    }

    TermList *l = lit->nthArgument(0);
    TermList *r = lit->nthArgument(1);
    
    bool termAlgebraConsL = l->isTerm() && env.signature->getFunction(l->term()->functor())->termAlgebraCons();
    bool termAlgebraConsR = r->isTerm() && env.signature->getFunction(r->term()->functor())->termAlgebraCons();
    
    if (!termAlgebraConsL && termAlgebraConsR) {
      t = l;
      fs = r;
      Ordering::Result o = _ord.getEqualityArgumentOrder(lit);
      return (o == Ordering::INCOMPARABLE || o == Ordering::LESS || o == Ordering::LESS_EQ);
    } else if (termAlgebraConsL && !termAlgebraConsR) {
      fs = l;
      t = r;
      Ordering::Result o = _ord.getEqualityArgumentOrder(lit);
      return (o == Ordering::INCOMPARABLE || o == Ordering::GREATER || o == Ordering::GREATER_EQ);
    } else {
      return false;
    }
  }
  
  struct ChainIndex::IndexEntry {
  public:
    IndexEntry(Literal *l, Clause *c, TermList t, List<TermList>* subterms) :
      lit(l),
      clause(c),
      t(t),
      subterms(subterms)
    {}

    CLASS_NAME(ChainIndex::IndexEntry);
    USE_ALLOCATOR(ChainIndex::IndexEntry);

    Literal* lit;
    Clause* clause;
    TermList t;
    List<TermList>* subterms;
  };

  /* The search algorithm is explained in the paper "An inference rule
     for the acyclicity property of term algebras", where it is
     described as a recursive algorithm, essentially a DFS. Here it is
     implemented non-recursively, with a stack.

     The nodes represent the tree built during the search. There are
     two types of nodes, subterm nodes and unification nodes
     (corresponding to the two static builder methods). An invariant
     of the tree is that a unification node has for parent a subterm
     node, as well as the other way around.

     The root of the tree is a unification node (with the literal that
     the query originates from)
   */
  struct ChainIndex::ChainSearchTreeNode
  {
    ChainSearchTreeNode(TermList t,
                        Literal *l,
                        Clause *c,
                        ChainSearchTreeNode *n,
                        unsigned i)
      :
      term(t),
      lit(l),
      clause(c),
      parent(n),
      substIndex(i),
      refCnt(0)
    {     
      if (parent) {
        parent->refCnt++;
        depth = parent->depth + 1;
      } else {
        depth = 0;
      }
    }

    TermList getNonConstructorSide()
    {
      CALL("ChainIndex::ChainSearchTreeNode::getNonConstructorSide");

      TermList *l = lit->nthArgument(0);
    
      bool leftc = l->isTerm() && env.signature->getFunction(l->term()->functor())->termAlgebraCons();
      return leftc ? *lit->nthArgument(1) : *lit->nthArgument(0);
    }

    CLASS_NAME(ChainIndex::ChainSearchTreeNode);
    USE_ALLOCATOR(ChainIndex::ChainSearchTreeNode);

    TermList term;
    Literal *lit;
    Clause *clause;
    ChainSearchTreeNode *parent;
    unsigned depth;
    unsigned substIndex;
    unsigned refCnt;
  };

  /*struct ChainIndex::ChainSearchTreeNode
  {
    ChainSearchTreeNode(TermList t,
                        Literal *l,
                        Clause *c,
                        ChainSearchTreeNode *n,
                        unsigned d,
                        unsigned i,
                        bool b)
      :
      term(t),
      lit(l),
      clause(c),
      parent(n),
      depth(d),
      substIndex(i),
      isUnificationNode(b),
      refCnt(0)
    {
      if (parent) {
        parent->refCnt++;
      }
    }

    static ChainSearchTreeNode *subtermNode(TermList t,
                                            Literal *l,
                                            Clause *c,
                                            ChainSearchTreeNode *n,
                                            unsigned substIndex)
    {
      return new ChainSearchTreeNode(t, l, c, n, n ? n->depth + 1 : 0, substIndex, false);
    }

    static ChainSearchTreeNode *unificationNode(TermList t,
                                                Literal *l,
                                                Clause *c,
                                                ChainSearchTreeNode *n,
                                                unsigned substIndex)
    {
      return new ChainSearchTreeNode(t, l, c, n, n ? n->depth : 0, substIndex, true);
    }

    CLASS_NAME(ChainIndex::ChainSearchTreeNode);
    USE_ALLOCATOR(ChainIndex::ChainSearchTreeNode);

    TermList term;
    Literal *lit;
    Clause *clause;
    ChainSearchTreeNode *parent;
    unsigned depth;
    unsigned substIndex;
    bool isUnificationNode;
    unsigned refCnt;
  };*/
  
  struct ChainIndex::NextLinkIterator
    : public IteratorCore<TermQueryResult>
  {
    NextLinkIterator(TermList t, ChainIndex& cindex)
      :
      _cindex(cindex),
      _uni(cindex._tis->getUnifications(t)),
      _entry(nullptr),
      _nthsubterm(0),
      _lit(nullptr),
      _clause(nullptr),
      _subst()
    {}

    bool hasNext()
    {
      CALL("ChainIndex::NextLinkIterator::hasNext");
      
      if (_entry) {
        if (_nthsubterm < List<TermList>::length(_entry->subterms)) {
          return true;
        } else {
          _nthsubterm = 0;
        }
      }
      while (_uni.hasNext()) {
        TermQueryResult tqr = _uni.next();
        _lit = tqr.literal;
        _clause = tqr.clause;
        _subst = tqr.substitution;
        // TODO check ordering conditions after substitution
        if (_cindex._lIndex.get(make_pair(_lit, _clause))) {
          _entry = _cindex._lIndex.get(make_pair(_lit, _clause));
          if (List<TermList>::length(_entry->subterms) > 0) {
            ASS_EQ(_nthsubterm, 0);
            return true;
          }
        }
      }
      return false;
    }

    TermQueryResult next()
    {
      CALL("ChainIndex::NextLinkIterator::next");

      return TermQueryResult(List<TermList>::nth(_entry->subterms, _nthsubterm++),
                             _lit,
                             _clause,
                             _subst);
    }

  private:
    ChainIndex& _cindex;
    TermQueryResultIterator _uni;
    IndexEntry* _entry;
    unsigned _nthsubterm;
    Literal* _lit;
    Clause* _clause;
    ResultSubstitutionSP _subst;
  };

  struct ChainIndex::ChainSearchIterator
    : public IteratorCore<ChainQueryResult>
  {
    ChainSearchIterator(Literal *queryLit,
                        Clause *queryClause,
                        ChainIndex& cindex,
                        bool codatatype)
      :
      _queryLit(queryLit),
      _queryClause(queryClause),
      _cindex(cindex),
      _nextResult(nullptr),
      _stack(0),
      _subst(new RobSubstitution()),
      _substChanges(0),
      _nextAvailableIndex(1), // 0 is for the query lit
      _currentDepth(0),
      _withContext(codatatype)
    {
      CALL("ChainIndex::ChainSearchIterator");

      TermList *t;
      TermList *fs;
      if (_cindex.matchesPattern(queryLit, fs, t, &_querySort, !codatatype, codatatype)) {
        ASS(_cindex._lIndex.find(make_pair(queryLit, queryClause)));
        _queryTerm = TermList(*t);
        IndexEntry *entry = _cindex._lIndex.get(make_pair(queryLit, queryClause));
        List<TermList>::Iterator it(entry->subterms);
        while (it.hasNext()) {
          // push all subterm of fs on the stack
          _stack.push(new ChainSearchTreeNode(it.next(),
                                              queryLit,
                                              queryClause,
                                              nullptr,
                                              0));
        }
      }
      ASS_EQ(_currentDepth, _substChanges.size());
    }

    ~ChainSearchIterator()
    {
      CALL("ChainIndex::ChainSearchIterator::~ChainSearchIterator");
      ASS(_stack.isEmpty());
      if (_nextResult) {
        delete _nextResult;
      }
    }

    // check that the clause is not found in the path from the root to
    // the node
    bool alreadyInChain(ChainSearchTreeNode *node, Clause *c)
    {
      CALL("ChainIndex::ChainSearchIterator::alreadyInChain");

      ChainSearchTreeNode *n = node;
      while (n) {
        if (n->clause == c) {
          return true;
        }
        n = n->parent;
      }

      return false;
    }

    Clause *applySubstitution(Clause *c, unsigned index)
    {
      CALL("ChainIndex::ChainSearchIterator::applySubstitution");
      
      unsigned clen = c->length();
      Inference* inf = new Inference1(Inference::INSTANTIATION, c);
      Clause* res = new(clen) Clause(clen,
                                     c->inputType(),
                                     inf);

      for (unsigned i = 0; i < clen; i++) {
        (*res)[i] = _subst->apply((*c)[i], index);
      }

      return res;
    }

    bool constructorPositionIn(TermList& subterm, TermList* term, TermList::Position*& position)
    {
      CALL("ChainIndex::ChainSearchIterator::constructorPositionIn(TermList)");

      if(!term->isTerm()){
        if(subterm.isTerm()) return false;
        if (term->var()==subterm.var()) {
          return true;
        }
        return false;
      }
      return constructorPositionIn(subterm, term->term(), position);
    }

    bool constructorPositionIn(TermList& subterm, Term* term, TermList::Position*& position)
    {
      CALL("TermList::constructorPositionIn(Term, List<unsigned>)");

      if(subterm.isTerm() && subterm.term() == term) {
        return true;
      }

      if (env.signature->getFunction(term->functor())->termAlgebraCons()) {
        for (unsigned i = 0; i < term->arity(); i++) {
          if (constructorPositionIn(subterm, term->nthArgument(i), position)) {
            TermList::Position::push(i, position);
            return true;
          }
        }
      }
      return false;
    }

    void buildContext(TermList &context, TermList &t, Literal *lit, unsigned substIndex, TermList::Position*& pos)
    {
      CALL("ChainIndex::ChainSearchIterator::buildContext");

      // hack to detect first call for the chain
      bool first = TermList::Position::isEmpty(pos);
      
      TermList *cons = lit->nthArgument(0);
      TermList *tnext;
      if (!cons->isTerm() || !env.signature->getFunction(cons->term()->functor())->termAlgebraCons()) {
        cons = lit->nthArgument(1);
        tnext = lit->nthArgument(0);
      } else {
        tnext = lit->nthArgument(1);
      }

      TermList::Position* newPos = TermList::Position::empty();
      TermList consS = _subst->apply(*cons, substIndex);
      ALWAYS(constructorPositionIn(t, &consS, newPos));
      t = _subst->apply(*tnext, substIndex);

      if (first) {
        context = consS;
      } else {
        context = TermList::replacePosition(context, consS, newPos);
      }
      pos = TermList::Position::append(newPos, pos);
    }

    ChainQueryResult *resultFromNode(ChainSearchTreeNode *node, bool withContext)
    {
      CALL("ChainIndex::ChainSearchIterator::openChainResult");

      ASS(node);

      ChainSearchTreeNode *n = node;
      LiteralList* l = LiteralList::empty();
      ClauseList* c = ClauseList::empty();
      ClauseList* cTheta = ClauseList::empty();
      TermList t1(_subst->apply(_queryTerm, 0));
      TermList tn(_subst->apply(n->term, n->substIndex));
      unsigned tnsort = SortHelper::getTermSort(node->term, node->lit);
      bool cycle = (_querySort == tnsort && TermList::equals(t1, tn));
      TermList context = TermList();
      TermList::Position* position = TermList::Position::empty();

      TermList t;
      if (withContext) {
        t = tn;
      }
      
      while (n) {
        LiteralList::push(n->lit, l);
        ClauseList::push(n->clause, c);
        ClauseList::push(applySubstitution(n->clause, n->substIndex), cTheta);
        if (withContext) {
          buildContext(context, t, n->lit, n->substIndex, position);
        }
        n = n->parent;
      }

      return new ChainQueryResult(l, c, cTheta, t1, _querySort, tn, tnsort, cycle, context, position);
    }

    // this deletes only if the node has no children
    void deleteNodeAndParents(ChainSearchTreeNode *n) {
      CALL("ChainIndex::ChainSearchIterator::deleteNodeAndParents");
      
      ChainSearchTreeNode* node = n;

      while (node && node->refCnt == 0) {
        ChainSearchTreeNode* next = n->parent;
        if (next) {
          next->refCnt--;
        }
        delete node;
        node = next;
      }
    }

    bool hasNext()
    {
      CALL("ChainIndex::ChainSearchIterator::hasNext");

      // if hasNext() has already been called without being followed
      // by a call to next(), the next value is already computed
      if (_nextResult) { return true; }
      
      while (_stack.isNonEmpty()) {
        ChainSearchTreeNode *n = _stack.pop();

        // backtrack the unifier
        while (_currentDepth > n->depth) {
          _substChanges.pop().backtrack();
          _currentDepth--;
          ASS_EQ(_currentDepth, _substChanges.size());
        }

        if (n->parent) {
          cout << "testing" << endl;
          if (SortHelper::getTermSort(n->parent->term, n->parent->lit)
              != SortHelper::getTermSort(n->getNonConstructorSide(), n->lit)) {
            // unification can fail because the term indexing
            // structure can return "false positives", i.e. terms
            // that cannot unify (because they come from the same
            // clause)
            cout << "failed" << endl;
            deleteNodeAndParents(n);
            continue;
          }
          BacktrackData btData;
          _subst->bdRecord(btData);
          // update the correct unifier
          ALWAYS(_subst->unify(n->parent->term,
                               n->parent->substIndex,
                               n->getNonConstructorSide(),
                               n->substIndex));
          _substChanges.push(btData);
          _currentDepth++;
          ASS_EQ(_currentDepth, _substChanges.size());
          _subst->bdDone();
          /*} else {
            _subst->bdDone();
            ASS(btData.isEmpty());
 
            deleteNodeAndParents(n);
            continue;
            }*/
        }

        // test whether we found a cycle
        TermList term1S(_subst->apply(_queryTerm, 0));
        TermList termS(_subst->apply(n->term, n->substIndex));
        unsigned termsort = SortHelper::getTermSort(n->term, n->lit);
        if (_querySort == termsort && TermList::equals(term1S, termS)) {
          // return cycle
          delete _nextResult;
          _nextResult = resultFromNode(n, _withContext);
          deleteNodeAndParents(n);
          return true;
        }

        // test whether we found a variable-ended chain
        if (n->term.isVar()) {
          // only unary chains should be variable ended
          ASS(!n->parent);
          // return variable-ended chain
          delete _nextResult;
          _nextResult = resultFromNode(n, _withContext);
          deleteNodeAndParents(n);
          return true;
        }

        NextLinkIterator nextLinks(termS, _cindex);
        Stack<TermQueryResult> nextLinksStack;

        // go through results once to check whether there exists a bad
        // extension of the chain
        while (nextLinks.hasNext()) {
          TermQueryResult tqr = nextLinks.next();
          if (alreadyInChain(n, tqr.clause)) {
            // return chain
            delete _nextResult;
            _nextResult = resultFromNode(n, _withContext);
            deleteNodeAndParents(n);
            return true;
          }
          nextLinksStack.push(tqr);
        }

        // push next links to continue the DFS
        while (nextLinksStack.isNonEmpty()) {
          TermQueryResult tqr = nextLinksStack.pop();
          // push only non-variable terms
          if (tqr.term.isTerm()) {
            _stack.push(new ChainSearchTreeNode(tqr.term,
                                                tqr.literal,
                                                tqr.clause,
                                                n,
                                                _nextAvailableIndex++));
          }
        }
      }

      return false;
    }

    ChainQueryResult next()
    {
      CALL("ChainIndex::ChainSearchIterator::next()");

      ASS(_nextResult);
      ChainQueryResult *res = _nextResult;
      _nextResult = nullptr;
      return *res;
    }

  private:
    Literal *_queryLit;
    Clause *_queryClause;
    TermList _queryTerm;
    unsigned _querySort;
    ChainIndex &_cindex;
    ChainQueryResult *_nextResult;
    Stack<ChainSearchTreeNode*> _stack;
    RobSubstitution *_subst;
    Stack<BacktrackData> _substChanges;
    int _nextAvailableIndex;
    unsigned _currentDepth;
    bool _withContext; // should the result include the constructor context
  };
  
  /*
  struct ChainIndex::ChainSearchIterator
    : public IteratorCore<ChainQueryResult>
  {
    ChainSearchIterator(Literal *queryLit,
                        Clause *queryClause,
                        ChainIndex& cindex,
                        bool codatatype)
      :
      _queryLit(queryLit),
      _queryClause(queryClause),
      _cindex(cindex),
      _nextResult(nullptr),
      _stack(0),
      _subst(new RobSubstitution()),
      _substChanges(0),
      _nextAvailableIndex(0),
      _currentDepth(0),
      _withContext(codatatype)
    {
      CALL("ChainIndex::ChainSearchIterator");

      TermList *t;
      TermList *fs;
      if (_cindex.matchesPattern(queryLit, fs, t, &_querySort, !codatatype, codatatype)) {
        ASS(_cindex._lIndex.find(make_pair(queryLit, queryClause)));
        _queryTerm = TermList(*t);
        _stack.push(ChainSearchTreeNode::unificationNode(_queryTerm,
                                                         queryLit,
                                                         queryClause,
                                                         nullptr,
                                                         _nextAvailableIndex++));
      }
      ASS_EQ(_currentDepth, _substChanges.size());
    }

    ~ChainSearchIterator()
    {
      CALL("ChainIndex::ChainSearchIterator::~ChainSearchIterator");
      ASS(_stack.isEmpty());
      if (_nextResult) {
        delete _nextResult;
      }
    }
    
    Clause *applySubstitution(Clause *c, unsigned index)
    {
      CALL("ChainIndex::ChainSearchIterator::applySubstitution");
      
      unsigned clen = c->length();
      Inference* inf = new Inference1(Inference::INSTANTIATION, c);
      Clause* res = new(clen) Clause(clen,
                                     c->inputType(),
                                     inf);

      for (unsigned i = 0; i < clen; i++) {
        (*res)[i] = _subst->apply((*c)[i], index);
      }

      return res;
    }

    bool constructorPositionIn(TermList& subterm, TermList* term, TermList::Position*& position)
    {
      CALL("ChainIndex::ChainSearchIterator::constructorPositionIn(TermList)");

      if(!term->isTerm()){
        if(subterm.isTerm()) return false;
        if (term->var()==subterm.var()) {
          return true;
        }
        return false;
      }
      return constructorPositionIn(subterm, term->term(), position);
    }

    bool constructorPositionIn(TermList& subterm, Term* term, TermList::Position*& position)
    {
      CALL("TermList::constructorPositionIn(Term, List<unsigned>)");

      if(subterm.isTerm() && subterm.term() == term) {
        return true;
      }

      if (env.signature->getFunction(term->functor())->termAlgebraCons()) {
        for (unsigned i = 0; i < term->arity(); i++) {
          if (constructorPositionIn(subterm, term->nthArgument(i), position)) {
            TermList::Position::push(i, position);
            return true;
          }
        }
      }
      return false;
    }

    void buildContext(TermList &context, TermList &t, Literal *lit, unsigned substIndex, TermList::Position*& pos)
    {
      CALL("ChainIndex::ChainSearchIterator::buildContext");

      // hack to detect first call for the chain
      bool first = TermList::Position::isEmpty(pos);
      
      TermList *cons = lit->nthArgument(0);
      TermList *tnext;
      if (!cons->isTerm() || !env.signature->getFunction(cons->term()->functor())->termAlgebraCons()) {
        cons = lit->nthArgument(1);
        tnext = lit->nthArgument(0);
      } else {
        tnext = lit->nthArgument(1);
      }

      TermList::Position* newPos = TermList::Position::empty();
      TermList consS = _subst->apply(*cons, substIndex);
      ALWAYS(constructorPositionIn(t, &consS, newPos));
      t = _subst->apply(*tnext, substIndex);

      if (first) {
        context = consS;
      } else {
        context = TermList::replacePosition(context, consS, newPos);
      }
      pos = TermList::Position::append(newPos, pos);
    }

    ChainQueryResult *resultFromNode(ChainSearchTreeNode *node, bool withContext)
    {
      CALL("ChainIndex::ChainSearchIterator::openChainResult");

      ASS(node);
      ASS(!node->isUnificationNode);

      ChainSearchTreeNode *n = node;
      LiteralList* l = LiteralList::empty();
      ClauseList* c = ClauseList::empty();
      ClauseList* cTheta = ClauseList::empty();
      TermList t1(_subst->apply(_queryTerm, 0));
      TermList tn(_subst->apply(n->term, n->substIndex));
      unsigned tnsort = SortHelper::getTermSort(node->term, node->lit);
      bool cycle = (_querySort == tnsort && TermList::equals(t1, tn));
      TermList context = TermList();
      TermList::Position* position = TermList::Position::empty();

      TermList t;
      if (withContext) {
        t = tn;
      }
      
      while (n) {
        ASS(!n->isUnificationNode);
        LiteralList::push(n->lit, l);
        ClauseList::push(n->clause, c);
        ClauseList::push(applySubstitution(n->clause, n->substIndex), cTheta);
        if (withContext) {
          buildContext(context, t, n->lit, n->substIndex, position);
        }
        n = n->parent->parent;
      }

      return new ChainQueryResult(l, c, cTheta, t1, _querySort, tn, tnsort, cycle, context, position);
    }

    // if there exists an extension of the chain that uses the same
    // clause twice, or the chain is a cycle, this method returns
    // false and does nothing. If n->term is a variable it returns
    // true and does nothing. Otherwise it pushes all unifications of
    // n->term and the stack and returns true
    bool pushUnificationsOnStack(ChainSearchTreeNode *n)
    {
      CALL("Acyclicity::pushUnificationOnStack");
      ASS(!n->isUnificationNode);

      if (n->term.isVar()) {
        // only unary variable-ended chains can be eligible, no need
        // to look further here
        return true;
      }

      Stack<TermQueryResult> tmpStack;

      TermQueryResultIterator tqrIt = _cindex._tis->getUnifications(_subst->apply(n->term, n->substIndex));
      unsigned sort = SortHelper::getTermSort(n->term, n->lit);
      int index;
      // go through results before to avoid some unneeded allocations
      while (tqrIt.hasNext()) {
        TermQueryResult tqr = tqrIt.next();
        if (alreadyInChain(n, tqr.literal)) {
          // this means there exists a "bad extension" or that the
          // chain is a cycle
          return false;
        }
        tmpStack.push(tqr);
      }

      while (tmpStack.isNonEmpty()) {
        TermQueryResult tqr = tmpStack.pop();
        if (n->term.isVar() && tqr.literal != _queryLit) {
          // found a variable-ended chain, no need to explore further
          continue;
        }
        // check sort to avoid unification with variable of wrong type
        if (SortHelper::getTermSort(tqr.term, tqr.literal) == sort) {
          if (tqr.literal == _queryLit) {
            index = 0;
          } else if (n && tqr.clause == n->clause) {
            index = n->substIndex;
          } else {
            index = _nextAvailableIndex++;
          }
          _stack.push(ChainSearchTreeNode::unificationNode(tqr.term,
                                                           tqr.literal,
                                                           tqr.clause,
                                                           n,
                                                           index));
        }
      }
      return true;
    }

    // check that the literal is not found in the path from the root
    // to the node (either the chain is a cycle or there is an
    // extension of the chain that uses the same clause twice)
    bool alreadyInChain(ChainSearchTreeNode *node, Literal *l)
    {
      CALL("ChainIndex::ChainSearchIterator::alreadyInChain");

      ChainSearchTreeNode *n = node;
      while (n) {
        if (n->lit == l) {
          return true;
        }
        n = n->parent;
      }

      return false;
    }

    // this deletes only if the node has no children
    void deleteNodeAndParents(ChainSearchTreeNode *n) {
      CALL("ChainIndex::ChainSearchIterator::deleteNodeAndParents");
      
      ChainSearchTreeNode* node = n;

      while (node && node->refCnt == 0) {
        ChainSearchTreeNode* next = n->parent;
        if (next) {
          next->refCnt--;
        }
        delete node;
        node = next;
      }
    }

    bool hasNext()
    {
      CALL("ChainIndex::ChainSearchIterator::hasNext");

      // if hasNext() has already been called without being followed
      // by a call to next(), the next value is already computed
      if (_nextResult) { return true; }
      
      while (_stack.isNonEmpty()) {
        ChainSearchTreeNode *n = _stack.pop();

        while (_currentDepth > n->depth) {
          _substChanges.pop().backtrack();
          _currentDepth--;
          ASS_EQ(_currentDepth, _substChanges.size());
        }

        if (n->isUnificationNode) {
          if (n->parent) { // not the root
            BacktrackData btData;
            _subst->bdRecord(btData);
            if (_subst->unify(n->parent->term,
                              n->parent->substIndex,
                              n->term,
                              n->substIndex)) {
              _substChanges.push(btData);
              _currentDepth++;
              ASS_EQ(_currentDepth, _substChanges.size());
              _subst->bdDone();
            } else {
              _subst->bdDone();
              ASS(btData.isEmpty());
              // unification can fail because the term indexing
              // structure can return "false positives", i.e. terms
              // that cannot unify (because they come from the same
              // clause)
              deleteNodeAndParents(n);
              continue;
            }
          }
          // add subterm nodes to the stack if applicable
          if (_cindex._lIndex.find(make_pair(n->lit, n->clause))) {
            IndexEntry *entry = _cindex._lIndex.get(make_pair(n->lit, n->clause));
            List<TermList>::Iterator it(entry->subterms);
            while (it.hasNext()) {
              TermList t = it.next();
              _stack.push(ChainSearchTreeNode::subtermNode(t,
                                                           entry->lit,
                                                           entry->clause,
                                                           n,
                                                           n->substIndex));
            }
          }
        } else { // n is a subterm node
          // if n is a variable, return a variable-ended chain, else
          // check that we don't have a cycle or there doesn't exist a
          // bad extension, in which cases we must return a result.
          // If none of those conditions are met, push unifications
          if (n->term.isVar() || !pushUnificationsOnStack(n)) {
            delete _nextResult;
            _nextResult = resultFromNode(n, _withContext);
            deleteNodeAndParents(n);
            return true;
          }
        }
        deleteNodeAndParents(n);
      }
      return false;
    }
    
    ChainQueryResult next()
    {
      CALL("ChainIndex::ChainSearchIterator::next()");

      ASS(_nextResult);
      ChainQueryResult *res = _nextResult;
      _nextResult = nullptr;
      return *res;
    }
  private:
    Literal *_queryLit;
    Clause *_queryClause;
    TermList _queryTerm;
    unsigned _querySort;
    ChainIndex &_cindex;
    ChainQueryResult *_nextResult;
    Stack<ChainSearchTreeNode*> _stack;
    RobSubstitution *_subst;
    Stack<BacktrackData> _substChanges;
    int _nextAvailableIndex;
    unsigned _currentDepth;
    bool _withContext; // should the result include the constructor context
  };
  */

  void ChainIndex::handleClause(Clause* c, bool adding)
  {
    CALL("ChainIndex::handleClause");

    // TODO timer?
    
    ArrayishObjectIterator<Clause> it = c->getSelectedLiteralIterator();
    while (it.hasNext()) {
      if (adding) {
        insert(it.next(), c);
      } else {
        remove(it.next(), c);
      }
    }
  }
    
  void ChainIndex::insert(Literal *lit, Clause *c)
  {
    CALL("ChainIndex::insert");

    TermList *fs;
    TermList *t;
    unsigned sort;

    static bool matchDT = (env.options->termAlgebraCyclicityCheck() == Options::TACyclicityCheck::RULE);
    static bool matchCDT = (env.options->termAlgebraUniquenessCheck() == Options::TAUniquenessCheck::RULE);

    if (matchesPattern(lit, fs, t, &sort, matchDT, matchCDT)) {
      ASS(fs->isTerm());

      ULit ulit = make_pair(lit, c);
      if (!_lIndex.find(ulit)) {
        _lIndex.insert(ulit, new IndexEntry(lit, c, *t, getSubterms(fs->term())));
        _tis->insert(*t, lit, c);
      }
    }
  }

  void ChainIndex::remove(Literal *lit, Clause *c)
  {
    CALL("ChainIndex::remove");

    TermList *fs;
    TermList *t;
    unsigned sort;
     
    if (matchesPattern(lit, fs, t, &sort, true, true)) {
      ULit ulit = make_pair(lit, c);
      if (!_lIndex.find(ulit))
        return;

      _lIndex.remove(ulit);
     _tis->remove(*t, lit, c);
    }
  }

  VirtualIterator<ChainQueryResult> ChainIndex::queryChains(Literal *lit, Clause *c, bool withContext)
  {
    CALL("ChainIndex::queryCycle");

    return vi(new ChainSearchIterator(lit, c, *this, withContext));
  }

  bool TARulesRHSIndex::rhsEligible(Literal* lit, const Ordering& ord, TermList*& lhs, TermList*& rhs)
  {
    CALL("TARulesRHSIndex::rhsEligible");

    if (lit->isEquality()
        && lit->isPositive()
        && env.signature->isTermAlgebraSort(SortHelper::getEqualityArgumentSort(lit))) {

      TermList *s = lit->nthArgument(0);
      TermList *t = lit->nthArgument(1);
      bool cons0 =  s->isTerm() && env.signature->getFunction(s->term()->functor())->termAlgebraCons();
      bool cons1 =  t->isTerm() && env.signature->getFunction(t->term()->functor())->termAlgebraCons();

      if (cons0) {
        if (cons1) {
          // literals of the form f(...) = g(...) should already have
          // been simplified, no need to consider them
          return false;
        }
        lhs = lit->nthArgument(0);
        rhs = lit->nthArgument(1);
        Ordering::Result o = ord.getEqualityArgumentOrder(lit);
        return (o == Ordering::INCOMPARABLE || o == Ordering::GREATER || o == Ordering::GREATER_EQ);
      } else if (cons1) {
        lhs = lit->nthArgument(1);
        rhs = lit->nthArgument(0);
        Ordering::Result o = ord.getEqualityArgumentOrder(lit);
        return (o == Ordering::INCOMPARABLE || o == Ordering::LESS || o == Ordering::LESS_EQ);
      }
    }
    return false;
  }

  void TARulesRHSIndex::handleClause(Clause* c, bool adding)
  {
    CALL("TARulesRHSIndex::handleClause");

    // TODO timer?

    unsigned selCnt=c->numSelected();
    TermList *lhs, *rhs;
    for (unsigned i=0; i<selCnt; i++) {
      Literal* lit=(*c)[i];
      if (rhsEligible(lit, _ord, lhs, rhs)) {
        if (adding) {
          _is->insert(*rhs, lit, c);
        } else {
          _is->remove(*rhs, lit, c);
        }
      }        
    }
  }
}
