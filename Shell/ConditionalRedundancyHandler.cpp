/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "ConditionalRedundancyHandler.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Inferences/DemodulationHelper.hpp"

#include "Statistics.hpp"

using namespace std;
using namespace Indexing;

using Subsumption = ConditionalRedundancySubsumption;

namespace Shell
{

template<class T>
bool checkVars(const TermStack& ts, T s)
{
  DHSet<TermList> vars;
  for (const auto& t : ts) {
    VariableIterator vit(t);
    while (vit.hasNext()) {
      vars.insert(vit.next());
    }
  }

  VariableIterator vit(s);
  while (vit.hasNext()) {
    auto var = vit.next();
    if (!vars.contains(var)) {
      return false;
    }
  }
  return true;
}

std::ostream& operator<<(std::ostream& str, const ConditionalRedundancyEntry& e)
{
  if (!e.active) {
    str << "not active";
  } else {
    str << *e.splits << "; " << *e.lits << "; ";
#if DEBUG_ORDERING
    iterTraits(e.ordCons.iter()).forEach([&str](const Ordering::Constraint& con) {
      str << con;
    });
#endif
  }
  return str;
}

class ConditionalRedundancyHandler::ConstraintIndex
  : public CodeTree
{
public:
  ConstraintIndex(Clause* cl) : _varSorts()
  {
    _clauseCodeTree=false;
    _onCodeOpDestroying = onCodeOpDestroying;
#if VDEBUG
    _cl = cl;
#endif
    for (unsigned i = 0; i < cl->length(); i++) {
      SortHelper::collectVariableSorts((*cl)[i], _varSorts);
      _litSubs.push({ nullptr, nullptr });
      _litRedundant.push({ false, false });
    }
  }

  bool check(const Ordering* ord, ResultSubstitution* subst, bool result, const OrderingConstraints& ordCons, const LiteralSet* lits, const SplitSet* splits)
  {
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    return !check(ts, ord, ordCons, lits, splits);
  }

  bool insert(const Ordering* ord, ResultSubstitution* subst, bool result, Splitter* splitter,
    OrderingConstraints&& ordCons, const LiteralSet* lits, SplitSet* splits)
  {
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    return insert(ord, ts, createEntry(ts, splitter, std::move(ordCons), lits, splits));
  }

  bool checkAndInsert(const Ordering* ord, ResultSubstitution* subst, bool result, bool doInsert, Splitter* splitter,
    OrderingConstraints&& ordCons, const LiteralSet* lits, const SplitSet* splits)
  {
    ASS(lits);
    // TODO if this correct if we allow non-unit simplifications?
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    if (check(ts, ord, ordCons, lits, splits)) {
      return false;
    }
    if (doInsert) {
      return insert(ord, ts, createEntry(ts, splitter, std::move(ordCons), lits, splits));
    }
    return true;
  }

#if VDEBUG
  Clause* _cl;
#endif

  bool insert(const Ordering* ord, Entries* entries, ConditionalRedundancyEntry* ptr)
  {
    ASS(ptr->active);

    ASS(entries->comparator);

#if DEBUG_ORDERING
    // we push subsumed ones as well to check subsumption
    entries->comps.push(ptr);
#endif

    entries->comparator->insert(ptr->ordCons, (void*)0x1);
    return true;
  }

  bool insert(const Ordering* ord, const TermStack& ts, ConditionalRedundancyEntry* ptr)
  {
    CodeStack code;
#define LINEARIZE 1
#if LINEARIZE
    Compiler<false, true> compiler(code);
#else
    TermCompiler compiler(code);
#endif
    for (const auto& t : ts) {
      if (t.isVar()) {
        compiler.handleVar(t.var());
        continue;
      }
      ASS(t.isTerm());
      compiler.handleTerm(t.term());
    }
    for (const auto& [x,y] : compiler.eqCons) {
      ptr->ordCons.push({ TermList::var(x), TermList::var(y), Ordering::EQUAL });
    }
    compiler.updateCodeTree(this);

    auto es = new Entries();
#if DEBUG_ORDERING
    es->comps.push(ptr);
#endif
    es->comparator = ord->createComparator();
    es->comparator->insert(ptr->ordCons, (void*)0x1);
    code.push(CodeOp::getSuccess(es));

#if LINEARIZE
    if (!isEmpty()) {
      VariantMatcher vm;
      Stack<CodeOp*> firstsInBlocks;

      FlatTerm* ft = FlatTerm::createUnexpanded(ts);
      vm.init(ft, this, &firstsInBlocks);

      if (vm.next()) {
        ASS(vm.op->isSuccess());
        auto es = vm.op->template getSuccessResult<Entries>();
        ft->destroy();
        return insert(ord, es, ptr);
      }
      ft->destroy();
    }
#endif

    incorporate(code);
    return true;
  }

  bool check(const TermStack& ts, const Ordering* ord, const OrderingConstraints& ordCons, const LiteralSet* lits, const SplitSet* splits)
  {
    if (isEmpty()) {
      return false;
    }

    static SubstMatcher matcher;
    struct Applicator : public SubstApplicator {
      TermList operator()(unsigned v) const override { return matcher.bindings[v]; }
    } applicator;

    matcher.init(this, ts);
    Entries* es;
    while ((es = matcher.next()))
    {
      ASS(es->comparator);
      es->comparator->init(&applicator);
      bool res = es->comparator->next();
#if DEBUG_ORDERING
      auto ordCons_crosscheck = iterTraits(es->comps.iter()).any([ord,&applicator](auto e) {
        return iterTraits(e->ordCons.iter()).all([ord,&applicator](auto& ordCon) {
          return ord->compare(AppliedTerm(ordCon.lhs,&applicator,true),AppliedTerm(ordCon.rhs,&applicator,true))==ordCon.rel;
        });
      });
      if (res != ordCons_crosscheck) {
        cout << res << " " << ordCons_crosscheck << endl;
        cout << *es->comparator << endl;
        for (const auto& e : es->comps) {
          cout << *e << endl;
        }
        INVALID_OPERATION("conditional redundancy ordering check mismatch");
      }
#endif
      if (res) {
        matcher.reset();
        return true;
      }
    }
    matcher.reset();

    return false;
  }

  template<class Applicator>
  TermStack getInstances(Applicator applicator) const
  {
    DHMap<unsigned,TermList>::Iterator vit(_varSorts);
    TermStack res;
    while (vit.hasNext()) {
      auto v = vit.nextKey();
      res.push(applicator(v));
    }
    return res;
  }

  DHMap<unsigned,TermList> _varSorts;
  Subsumption* _subs = nullptr;
  bool _redundant = false;
  Stack<std::pair<Subsumption*, Subsumption*>> _litSubs;
  Stack<std::pair<bool,bool>> _litRedundant;

  ConditionalRedundancyEntry* createEntry(const TermStack& ts, Splitter* splitter, OrderingConstraints&& ordCons, const LiteralSet* lits, SplitSet* splits) const
  {
    auto e = new ConditionalRedundancyEntry();
    Renaming r;
    if (ordCons.isNonEmpty() || !lits->isEmpty()) {
      // normalize constraints, the same way as
      // terms from ts are normalized upon insertion
      for (const auto t : ts) {
        r.normalizeVariables(t);
      }
    }

    for (auto& ordCon : ordCons) {
      ASS(checkVars(ts,ordCon.lhs));
      ASS(checkVars(ts,ordCon.rhs));
      ASS(ordCon.lhs.containsAllVariablesOf(ordCon.rhs));
      ordCon.lhs = r.apply(ordCon.lhs);
      ordCon.rhs = r.apply(ordCon.rhs);
    }
    e->ordCons = std::move(ordCons);

#if VDEBUG
    lits->iter().forEach([&ts](Literal* lit) {
      ASS(checkVars(ts,lit));
    });
#endif

    e->lits = LiteralSet::getFromIterator(lits->iter().map([&r](Literal* lit) {
      return r.apply(lit);
    }));

    ASS(splits);
    e->splits = splits;

    if (!splits->isEmpty()) {
      splitter->addConditionalRedundancyEntry(splits, e);
    }
  
    return e;
  }

  struct SubstMatcher
  : public Matcher
  {
    void init(CodeTree* tree, const TermStack& ts)
    {
      Matcher::init(tree,tree->getEntryPoint());

      ft = FlatTerm::createUnexpanded(ts);

      op=entry;
      tp=0;
    }

    void reset()
    {
      ft->destroy();
    }

    Entries* next()
    {
      if (finished()) {
        //all possible matches are exhausted
        return nullptr;
      }

      _matched=execute();
      if (!_matched) {
        return nullptr;
      }

      ASS(op->isSuccess());
      return op->getSuccessResult<Entries>();
    }
  };

  struct VariantMatcher
  : public RemovingMatcher
  {
  public:
    void init(FlatTerm* ft_, CodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_) {
      RemovingMatcher::init(tree_->getEntryPoint(), 0, 0, tree_, firstsInBlocks_);
      ft=ft_;
      tp=0;
      op=entry;
    }
  };

  static void onCodeOpDestroying(CodeOp* op) {
    if (op->isSuccess()) {
      auto es = op->getSuccessResult<Entries>();
#if DEBUG_ORDERING
      iterTraits(decltype(es->comps)::Iterator(es->comps)).forEach([](ConditionalRedundancyEntry* e) { delete e; });
#endif
      delete es;
    }
  }
};

ConditionalRedundancySubsumption::ConditionalRedundancySubsumption(
  OrderingComparator& subsumer, OrderingComparator& subsumed, bool ground)
  : subsumer(subsumer), subsumed(subsumed), ground(ground)
{
  path.push({ &subsumer._source, nullptr, &subsumed._source });
}

#define SUBSUMPTION_MAX_ITERATIONS 500

bool ConditionalRedundancySubsumption::check()
{
  unsigned cnt = 0;
  while (path.isNonEmpty()) {
    if (cnt++ > SUBSUMPTION_MAX_ITERATIONS) {
      return false;
    }

    if (path.size()==1) {
      subsumer._prev = nullptr;
    } else {
      subsumer._prev = get<0>(path[path.size()-2]);
    }
    subsumer._curr = get<0>(path.top());
    subsumer.processCurrentNode();

    auto lnode = subsumer._curr->node();
    if (lnode->tag == OrderingComparator::Node::T_DATA && lnode->data) {
      pushNext();
      continue;
    }

    auto trace = lnode->trace ? lnode->trace : subsumer.getCurrentTrace();
    if (!trace || (ground && trace->hasIncomp())) {
      pushNext();
      continue;
    }

    subsumed._prev = get<1>(path.top());
    subsumed._curr = get<2>(path.top());
    subsumed.processCurrentNode();
    auto rnode = subsumed._curr->node();

    switch (rnode->tag) {
      case OrderingComparator::Node::T_POLY: {
        if (lnode->tag == OrderingComparator::Node::T_DATA) {
          return false;
        }
        path.push({ &lnode->getBranch(Ordering::GREATER), subsumed._prev, subsumed._curr });
        break;
      }
      case OrderingComparator::Node::T_DATA: {
        if (rnode->data) {
          if (lnode->tag == OrderingComparator::Node::T_DATA) {
            return false;
          }
          path.push({ &lnode->getBranch(Ordering::GREATER), subsumed._prev, subsumed._curr });
        } else {
          pushNext();
        }
        break;
      }
      case OrderingComparator::Node::T_TERM: {
        auto lhs = rnode->lhs;
        auto rhs = rnode->rhs;
        Ordering::Result val;
        if (!trace->get(lhs, rhs, val)) {
          if (lnode->tag == OrderingComparator::Node::T_DATA) {
            return false;
          }
          path.push({ &lnode->getBranch(Ordering::GREATER), subsumed._prev, subsumed._curr });
        } else {
          switch (val) {
            case Ordering::GREATER: {
              path.top() = { subsumer._curr, subsumed._curr, &rnode->getBranch(Ordering::GREATER) };
              break;
            }
            case Ordering::EQUAL: {
              path.top() = { subsumer._curr, subsumed._curr, &rnode->getBranch(Ordering::EQUAL) };
              break;
            }
            default: {
              path.top() = { subsumer._curr, subsumed._curr, &rnode->getBranch(Ordering::INCOMPARABLE) };
              break;
            }
          }
        }
        break;
      }
    }
  }

  ASS(path.isEmpty());
  return true;
}

void ConditionalRedundancySubsumption::pushNext()
{
  while (path.isNonEmpty()) {
    auto curr = get<0>(path.pop());
    if (path.isEmpty()) {
      continue;
    }

    auto prevE = path.top();
    auto prev = get<0>(prevE)->node();
    ASS(prev->tag == OrderingComparator::Node::T_POLY ||
        prev->tag == OrderingComparator::Node::T_TERM);
    // if there is a previous node and we were either in the gt or eq
    // branches, just go to next branch in order, otherwise backtrack
    if (curr == &prev->getBranch(Ordering::GREATER)) {
      path.push({ &prev->getBranch(Ordering::EQUAL), get<1>(prevE), get<2>(prevE) });
      break;
    }
    if (curr == &prev->getBranch(Ordering::EQUAL)) {
      path.push({ &prev->getBranch(Ordering::LESS), get<1>(prevE), get<2>(prevE) });
      break;
    }
  }
}

ConditionalRedundancySubsumption2::ConditionalRedundancySubsumption2(
  const Ordering& ord, OrderingComparator& left,
  Stack<std::pair<OrderingComparator&, const SubstApplicator*>>& rights)
  : ord(ord), left(left), rights(rights)
{
#if VDEBUG
  ASS(left._ground);
  for (const auto& [tod,appl] : rights) {
    ASS(tod._ground);
  }
#endif
}

#define SUBSUMPTION2_LIMIT 500

bool ConditionalRedundancySubsumption2::check()
{
  Stack<pair<OrderingComparator::Branch*,OrderingComparator::Branch*>> todo;
  todo.push({ nullptr, &left._source });

  while (todo.isNonEmpty()) {
    auto [prev,curr] = todo.pop();
    left._prev = prev;
    left._curr = curr;
    left.processCurrentNode();

    auto node = left._curr->node();
    ASS(node->ready);

    if (node->tag != OrderingComparator::Node::T_DATA) {
      todo.push({ left._curr, &node->getBranch(Ordering::GREATER) });
      todo.push({ left._curr, &node->getBranch(Ordering::EQUAL) });
      todo.push({ left._curr, &node->getBranch(Ordering::LESS) });
      continue;
    }
    if (!node->data) {
      continue;
    }

    auto trace = node->trace;

    bool found = false;
    for (auto& [tod, appl] : rights) {
      if (checkRight(tod, appl, trace)) {
        found = true;
        break;
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}

bool ConditionalRedundancySubsumption2::checkRight(OrderingComparator& tod, const SubstApplicator* appl, const TermPartialOrdering* tpo)
{
  using Node = OrderingComparator::Node;

  Stack<tuple<Branch*,const TermPartialOrdering*,std::unique_ptr<OrderingComparator::Iterator>>> path;
  path.push({ &tod._source, tpo, unique_ptr<OrderingComparator::Iterator>() });
  while (path.isNonEmpty()) {
    if (cnt++ >= SUBSUMPTION2_LIMIT) {
      return false;
    }
    if (path.size()==1) {
      tod._prev = nullptr;
    } else {
      tod._prev = get<0>(path[path.size()-2]);
    }
    auto& [curr, trace, iterator] = path.top();
    ASS(trace);
    tod._curr = curr;
    tod.processCurrentNode();

    auto node = tod._curr->node();
    ASS(node->ready);

    if (node->tag == Node::T_DATA) {
      if (node->data) {
        // push next
        while (path.isNonEmpty()) {
          path.pop();
          if (path.isEmpty()) {
            break;
          }

          auto& [prev, prevTrace, prevIt] = path.top();
          auto prevN = prev->node();
          ASS(prevN->tag == Node::T_POLY || prevN->tag == Node::T_TERM);
          if (!prevIt->hasNext()) {
            // go one up further
            continue;
          }
          auto [res,resTrace] = prevIt->next();
          ASS_NEQ(res,Ordering::INCOMPARABLE);
          path.push({ &prevN->getBranch(res), resTrace, unique_ptr<OrderingComparator::Iterator>() });
          break;
        }
        continue;
      }
      return false;
    }

    ASS_EQ(node->tag, Node::T_TERM);
    ASS(node->lhs.isVar());
    ASS(node->rhs.isVar());

    auto lhsS = (*appl)(node->lhs.var());
    auto rhsS = (*appl)(node->rhs.var());

    ASS(!iterator);
    iterator = make_unique<OrderingComparator::Iterator>(ord, trace, lhsS, rhsS);
    if (iterator->hasNext()) {
      // go down
      auto [res,resTrace] = iterator->next();
      ASS_NEQ(res,Ordering::INCOMPARABLE);
      path.push({ &node->getBranch(res), resTrace, unique_ptr<OrderingComparator::Iterator>() });
      continue;
    }
    INVALID_OPERATION("should have at least one result");
  }
  return true;
}

template<bool contrapositive>
ConditionalRedundancySubsumption3<contrapositive>::ConditionalRedundancySubsumption3(
  const Ordering& ord, Stack<CompSubstPair>& lefts, Stack<CompSubstPair>& rights)
  : ord(ord), lefts(lefts), rights(rights)
{
#if VDEBUG
  for (const auto& [tod,appl] : lefts) {
    ASS(tod._ground);
  }
  for (const auto& [tod,appl] : rights) {
    ASS(tod._ground);
  }
#endif
}

#define SUBSUMPTION3_LIMIT 500

template<bool contrapositive>
bool ConditionalRedundancySubsumption3<contrapositive>::check()
{
  Stack<Iterator> iterators;
  for (const auto& [comp,appl] : lefts) {
    iterators.push(Iterator(comp));
  }
  unsigned i = 0;
  if (lefts.isNonEmpty()) {
    iterators[i].init(TermPartialOrdering::getEmpty(ord), lefts[i].second);
  } else {
    bool found = false;
    for (auto& [tod, appl] : rights) {
      if (checkRight(tod, appl, TermPartialOrdering::getEmpty(ord))) {
        found = true;
        break;
      }
    }
    return found;
  }
  while (true) {
    auto& it = iterators[i];
    const TermPartialOrdering* curr = nullptr;
    // try to get a next success
    while (it.hasNext()) {
      auto [val,tpo] = it.next();
      if constexpr (contrapositive) {
        if (val == Ordering::GREATER) {
          continue;
        }
      } else {
        if (val != Ordering::GREATER) {
          continue;
        }
      }
      curr = tpo;
      break;
    }
    // if there are no more successes, backtrack
    if (!curr) {
      // cannot backtrack, exit
      if (i == 0) {
        break;
      }
      i--;
      continue;
    }

    // if there is a next item, go to it
    if (i+1 < lefts.size()) {
      i++;
      iterators[i].init(curr, lefts[i].second);
      continue;
    }

    // if there is no next, check rights
    bool found = false;
    for (auto& [tod, appl] : rights) {
      if (checkRight(tod, appl, curr)) {
        found = true;
        break;
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}

template<bool contrapositive>
bool ConditionalRedundancySubsumption3<contrapositive>::checkRight(OrderingComparator& tod, const SubstApplicator* appl, const TermPartialOrdering* tpo)
{
  Iterator it(tod);
  it.init(tpo, appl);
  while (it.hasNext()) {
    auto [val,trace] = it.next();
    if constexpr (contrapositive) {
      if (val == Ordering::GREATER) {
        return false;
      }
    } else {
      if (val != Ordering::GREATER) {
        return false;
      }
    }
  }
  return true;
}

template<bool contrapositive>
void ConditionalRedundancySubsumption3<contrapositive>::Iterator::init(const TermPartialOrdering* tpo, const SubstApplicator* appl)
{
  _tpo = tpo;
  _appl = appl;
  _path.reset();
  _path.push({ &_comp._source, tpo, unique_ptr<OrderingComparator::Iterator>() });
}

template<bool contrapositive>
bool ConditionalRedundancySubsumption3<contrapositive>::Iterator::hasNext()
{
  using Node = OrderingComparator::Node;

  while (_path.isNonEmpty()) {
    auto& [curr, trace, iterator] = _path.top();
    ASS(trace);

    _comp._prev = (_path.size()==1) ? nullptr : get<0>(_path[_path.size()-2]);
    _comp._curr = curr;
    _comp.processCurrentNode();

    auto node = _comp._curr->node();
    ASS(node->ready);

    if (node->tag == Node::T_DATA) {
      _res.second = trace;
      if (_comp._threeValued) {
        if (node->data == (void*)0x1) {
          _res.first = Ordering::GREATER;
        } else if (node->data == (void*)0x2) {
          _res.first = Ordering::EQUAL;
        } else if (node->data == (void*)0x3) {
          _res.first = Ordering::LESS;
        } else {
          _res.first = Ordering::INCOMPARABLE;
        }
      } else {
        _res.first = node->data ? Ordering::GREATER : Ordering::INCOMPARABLE;
      }
      // push next first
      while (_path.isNonEmpty()) {
        _path.pop();
        if (_path.isEmpty()) {
          break;
        }

        auto& [prev, prevTrace, prevIt] = _path.top();
        auto prevN = prev->node();
        ASS(prevN->tag == Node::T_POLY || prevN->tag == Node::T_TERM);
        if (prevN->tag == Node::T_POLY) {
          if (_comp._curr == &prevN->getBranch(Ordering::GREATER)) {
            _path.push({ &prevN->getBranch(Ordering::EQUAL), prevTrace, unique_ptr<OrderingComparator::Iterator>() });
            break;
          } else if (_comp._curr == &prevN->getBranch(Ordering::EQUAL)) {
            _path.push({ &prevN->getBranch(Ordering::LESS), prevTrace, unique_ptr<OrderingComparator::Iterator>() });
            break;
          }
          continue;
        }
        if (!prevIt->hasNext()) {
          // go one up further
          continue;
        }
        auto [res,resTrace] = prevIt->next();
        ASS_NEQ(res,Ordering::INCOMPARABLE);
        _path.push({ &prevN->getBranch(res), resTrace, unique_ptr<OrderingComparator::Iterator>() });
        break;
      }
      return true;
    }

    if (node->tag == Node::T_POLY) {
      _path.push({ &node->getBranch(Ordering::GREATER), trace, unique_ptr<OrderingComparator::Iterator>() });
      continue;
    }

    ASS_EQ(node->tag, Node::T_TERM);
    // ASS(node->lhs.isVar());
    // ASS(node->rhs.isVar());

    // auto lhsS = (*_appl)(node->lhs.var());
    // auto rhsS = (*_appl)(node->rhs.var());

    auto lhsS = AppliedTerm(node->lhs, _appl, true).apply();
    auto rhsS = AppliedTerm(node->rhs, _appl, true).apply();

    ASS(!iterator);
    iterator = make_unique<OrderingComparator::Iterator>(_comp._ord, trace, lhsS, rhsS);
    if (iterator->hasNext()) {
      // go down
      auto [res,resTrace] = iterator->next();
      ASS_NEQ(res,Ordering::INCOMPARABLE);
      _path.push({ &node->getBranch(res), resTrace, unique_ptr<OrderingComparator::Iterator>() });
      continue;
    }
    INVALID_OPERATION("should have at least one result");
  }
  return false;
}

template class ConditionalRedundancySubsumption3<false>;
template class ConditionalRedundancySubsumption3<true>;

// ConditionalRedundancyHandler

ConditionalRedundancyHandler* ConditionalRedundancyHandler::create(const Options& opts, const Ordering* ord, Splitter* splitter)
{
  if (!opts.conditionalRedundancyCheck()) {
    return new ConditionalRedundancyHandlerImpl</*enabled*/false,false,false,false>(opts,ord,splitter);
  }
  auto ordC = opts.conditionalRedundancyOrderingConstraints();
  // check for av=on here as otherwise we would have to null-check splits inside the handler
  auto avatarC = opts.splitting() && opts.conditionalRedundancyAvatarConstraints();
  auto litC = opts.conditionalRedundancyLiteralConstraints();
  if (ordC) {
    if (avatarC) {
      if (litC) {
        return new ConditionalRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/true,/*litC*/true>(opts,ord,splitter);
      }
      return new ConditionalRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/true,/*litC*/false>(opts,ord,splitter);
    }
    if (litC) {
      return new ConditionalRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/false,/*litC*/true>(opts,ord,splitter);
    }
    return new ConditionalRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/false,/*litC*/false>(opts,ord,splitter);
  }
  if (avatarC) {
    if (litC) {
      return new ConditionalRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/true,/*litC*/true>(opts,ord,splitter);
    }
    return new ConditionalRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/true,/*litC*/false>(opts,ord,splitter);
  }
  if (litC) {
    return new ConditionalRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/false,/*litC*/true>(opts,ord,splitter);
  }
  return new ConditionalRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/false,/*litC*/false>(opts,ord,splitter);
}

void ConditionalRedundancyHandler::destroyClauseData(Clause* cl)
{
  ConstraintIndex* ptr = nullptr;
  clauseData.pop(cl, ptr);
  delete ptr;
}

void ConditionalRedundancyHandler::destroyAllClauseData()
{
  decltype(clauseData)::Iterator it(clauseData);
  while (it.hasNext()) {
    auto data = it.next();
    delete data;
  }
}

ConditionalRedundancyHandler::ConstraintIndex** ConditionalRedundancyHandler::getDataPtr(Clause* cl, bool doAllocate)
{
  if (!doAllocate) {
    return clauseData.findPtr(cl);
  }
  ConstraintIndex** ptr;
  clauseData.getValuePtr(cl, ptr, nullptr);
  if (!*ptr) {
    *ptr = new ConstraintIndex(cl);
  }
  return ptr;
}

void ConditionalRedundancyHandler::transfer(Clause* from, Clause* to)
{
  ConstraintIndex* ptr = nullptr;
  clauseData.pop(from, ptr);
  if (!ptr) {
    return;
  }
  ALWAYS(clauseData.insert(to, ptr));
}

DHMap<Clause*,typename ConditionalRedundancyHandler::ConstraintIndex*> ConditionalRedundancyHandler::clauseData;

// ConditionalRedundancyHandlerImpl

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkSuperposition(
  Clause* eqClause, Literal* eqLit, TermList eqLHS, Clause* rwClause, Literal* rwLit, TermList rwTerm,
  bool eqIsResult, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }

  auto eqClDataPtr = getDataPtr(eqClause, /*doAllocate=*/false);
  if (eqClDataPtr) {
    if ((*eqClDataPtr)->_redundant) {
      env.statistics->skippedSuperposition++;
      return false;
    }
    auto i = eqClause->getLiteralPosition(eqLit);
    if (eqLHS == eqLit->termArg(0) && (*eqClDataPtr)->_litRedundant[i].first) {
      env.statistics->skippedSuperposition++;
      return false;
    }
    if (eqLHS == eqLit->termArg(1) && (*eqClDataPtr)->_litRedundant[i].second) {
      env.statistics->skippedSuperposition++;
      return false;
    }
  }

  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/false);
  if (rwClDataPtr) {
    if ((*rwClDataPtr)->_redundant) {
      env.statistics->skippedSuperposition++;
      return false;
    }
    auto i = rwClause->getLiteralPosition(rwLit);
    auto leftred = (*rwClDataPtr)->_litRedundant[i].first;
    auto rightred = (*rwClDataPtr)->_litRedundant[i].second;
    if (leftred && rightred) {
      env.statistics->skippedSuperposition++;
      return false;
    }
    if (leftred && !rwLit->termArg(1).containsSubterm(rwTerm)) {
      env.statistics->skippedSuperposition++;
      return false;
    }
    if (rightred && !rwLit->termArg(0).containsSubterm(rwTerm)) {
      env.statistics->skippedSuperposition++;
      return false;
    }
  }

  auto rwLits = LiteralSet::getEmpty();
  if constexpr (litC) {
    rwLits = LiteralSet::getFromIterator(rwClause->iterLits().filter([rwLit](Literal* lit) {
      return lit != rwLit && rwLit->containsAllVariablesOf(lit);
    }).map([subs,eqIsResult](Literal* lit) {
      return subs->applyTo(lit,!eqIsResult);
    }));
  }

  auto rwSplits = SplitSet::getEmpty();
  if constexpr (avatarC) {
    rwSplits = rwClause->splits();
  }

  if (eqClDataPtr && !(*eqClDataPtr)->check(_ord, subs, eqIsResult, OrderingConstraints(), rwLits, rwSplits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }

  auto eqLits = LiteralSet::getEmpty();
  if constexpr (litC) {
    eqLits = LiteralSet::getFromIterator(eqClause->iterLits().filter([eqLit](Literal* lit) {
      return lit != eqLit && eqLit->containsAllVariablesOf(lit);
    }).map([subs,eqIsResult](Literal* lit) {
      return subs->applyTo(lit,eqIsResult);
    }));
  }

  auto eqSplits = SplitSet::getEmpty();
  if constexpr (avatarC) {
    eqSplits = eqClause->splits();
  }

  if (rwClDataPtr && !(*rwClDataPtr)->check(_ord, subs, !eqIsResult, OrderingConstraints(), eqLits, eqSplits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }

  return true;
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::insertSuperposition(
  Clause* eqClause, Clause* rwClause, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
  Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }

  struct Applicator : SubstApplicator {
    Applicator(ResultSubstitution* subst, bool result) : subst(subst) {}
    TermList operator()(unsigned v) const override {
      return subst->apply(TermList::var(v), result);
    }
    ResultSubstitution* subst;
    bool result;
  };

  Applicator appl(subs, !eqIsResult);
  Ordering::Result otherComp;

  auto premiseRedundant = isSuperpositionPremiseRedundant(
    rwClause, rwLitS, rwTermS, tgtTermS, eqClause, eqLHS, &appl, otherComp);

  // create ordering constraints
  OrderingConstraints ordCons;
  if constexpr (ordC) {
    // TODO we cannot handle them together yet
    if (eqComp != Ordering::LESS) {
      if (!rwTermS.containsAllVariablesOf(tgtTermS)) {
        return true;
      }
      ordCons.push({ rwTermS, tgtTermS, Ordering::GREATER });
    }
    if (!premiseRedundant) {
      TermList other = EqHelper::getOtherEqualitySide(rwLitS, rwTermS);
      if (otherComp != Ordering::INCOMPARABLE || !other.containsAllVariablesOf(tgtTermS)) {
        return true;
      }
      ordCons.push({ other, tgtTermS, Ordering::GREATER });
    }
  } else {
    if (eqComp != Ordering::LESS || !premiseRedundant) {
      return true;
    }
  }

  // create literal constraints
  auto lits = LiteralSet::getEmpty();
  if constexpr (litC) {
    if (eqClause->numSelected()!=1) {
      return true;
    }
    lits = LiteralSet::getFromIterator(eqClause->iterLits().filter([eqLit,eqLHS](Literal* lit) {
      return lit != eqLit && eqLHS.containsAllVariablesOf(TermList(lit));
    }).map([subs,eqIsResult](Literal* lit) {
      return subs->applyTo(lit,eqIsResult);
    }));
    if (eqClause->size()>lits->size()+1) {
      return true;
    }
  } else {
    if (eqClause->length()!=1) {
      return true;
    }
  }

  // create AVATAR constraints
  auto splits = SplitSet::getEmpty();
  if constexpr (avatarC) {
    splits = eqClause->splits()->subtract(rwClause->splits());
  } else {
    if (!eqClause->noSplits()) {
      return true;
    }
  }

  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/true);
  if (!(*rwClDataPtr)->insert(_ord, subs, !eqIsResult, _splitter, std::move(ordCons), lits, splits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }
  return true;
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::handleResolution(
  Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }

  // Note that we're inserting into the data of one clause based on the *other* clause
  {
    bool doInsert = resultLit->isPositive();

    // create literal constraints
    auto lits = LiteralSet::getEmpty();
    if constexpr (litC) {
      lits = LiteralSet::getFromIterator(resultCl->iterLits().filter([resultLit](Literal* lit) {
        return lit != resultLit && resultLit->containsAllVariablesOf(lit);
      }).map([subs](Literal* lit) {
        return subs->applyToResult(lit);
      }));
      if (resultCl->numSelected()>1 || resultCl->length()>lits->size()+1) {
        doInsert = false;
      }
    } else {
      if (resultCl->length()!=1) {
        doInsert = false;
      }
    }

    // create AVATAR constraints
    auto splits = SplitSet::getEmpty();
    if constexpr (avatarC) {
      splits = resultCl->splits()->subtract(queryCl->splits());
    } else {
      if (!resultCl->noSplits()) {
        doInsert = false;
      }
    }

    auto dataPtr = getDataPtr(queryCl, /*doAllocate=*/doInsert);
    if (dataPtr && !(*dataPtr)->checkAndInsert(
      _ord, subs, /*result*/false, doInsert, _splitter, OrderingConstraints(), lits, splits))
    {
      env.statistics->skippedResolution++;
      return false;
    }
  }
  {
    bool doInsert = queryLit->isPositive();

    // create literal constraints
    auto lits = LiteralSet::getEmpty();
    if constexpr (litC) {
      lits = LiteralSet::getFromIterator(queryCl->iterLits().filter([queryLit](Literal* lit) {
        return lit != queryLit && queryLit->containsAllVariablesOf(lit);
      }).map([subs](Literal* lit) {
        return subs->applyToQuery(lit);
      }));
      if (queryCl->numSelected()>1 || queryCl->length()>lits->size()+1) {
        doInsert = false;
      }
    } else {
      if (queryCl->length()!=1) {
        doInsert = false;
      }
    }

    // create AVATAR constraints
    auto splits = SplitSet::getEmpty();
    if constexpr (avatarC) {
      splits = queryCl->splits()->subtract(resultCl->splits());
    } else {
      if (!queryCl->noSplits()) {
        doInsert = false;
      }
    }

    auto dataPtr = getDataPtr(resultCl, /*doAllocate=*/doInsert);
    if (dataPtr && !(*dataPtr)->checkAndInsert(
      _ord, subs, /*result*/true, doInsert, _splitter, OrderingConstraints(), lits, splits))
    {
      env.statistics->skippedResolution++;
      return false;
    }
  }
  return true;
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::handleReductiveUnaryInference(
  Clause* premise, RobSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }
  auto dataPtr = getDataPtr(premise, /*doAllocate=*/true);
  auto subst = ResultSubstitution::fromSubstitution(subs, 0, 0);
  auto lits = LiteralSet::getEmpty();
  auto splits = SplitSet::getEmpty();
  if (!(*dataPtr)->checkAndInsert(
    _ord, subst.ptr(), /*result*/false, /*doInsert=*/true, _splitter, OrderingConstraints(), lits, splits))
  {
    return false;
  }
  return true;
}

/**
 * This function is similar to @b DemodulationHelper::isPremiseRedundant.
 * However, here we do not assume that the rewriting equation is unit, which necessitates some additional checks.
 */
template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::isSuperpositionPremiseRedundant(
  Clause* rwCl, Literal* rwLit, TermList rwTerm, TermList tgtTerm, Clause* eqCl, TermList eqLHS,
  const SubstApplicator* eqApplicator, Ordering::Result& tord) const
{
  ASS(enabled);

  // if check is turned off, we always report redundant
  if (!_redundancyCheck) {
    return true;
  }

  // if the top-level terms are not involved, premise is redundant
  if (!rwLit->isEquality() || (rwTerm!=*rwLit->nthArgument(0) && rwTerm!=*rwLit->nthArgument(1))) {
    return true;
  }

  // we can only check encompassment demodulation if eqCl is unit
  if (_encompassing && eqCl->length()==1) {
    // if we have a negative literal or non-unit, premise is redundant
    if (rwLit->isNegative() || rwCl->length() != 1) {
      return true;
    }
    // otherwise (we have a positive unit), if substitution is not
    // renaming on side premise, main premise is redundant
    if (!Inferences::DemodulationHelper::isRenamingOn(eqApplicator,eqLHS)) {
      return true;
    }
  }

  // else we do standard redundancy check
  TermList other=EqHelper::getOtherEqualitySide(rwLit, rwTerm);
  tord = _ord->compare(tgtTerm, other);
  return tord == Ordering::LESS;
  // TODO perform ordering check for rest of rwCl
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
void ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::initWithEquation(Clause* resClause, TermList rwTerm, TermList tgtTerm) const
{
  if (!enabled) {
    return;
  }

  if (!ordC) {
    return;
  }

  if (!tgtTerm.containsAllVariablesOf(rwTerm)) {
    return;
  }
  OrderingConstraints ordCons;
  ordCons.push({ tgtTerm, rwTerm, Ordering::GREATER });
  auto lits = LiteralSet::getEmpty();
  auto splits = SplitSet::getEmpty();

  struct RenamingSubstitution : public ResultSubstitution {
    TermList applyTo(TermList t, unsigned index) override { return t; }
    void output(std::ostream&) const override {}
  } subst;

  auto clDataPtr = getDataPtr(resClause, /*doAllocate=*/true);
  (*clDataPtr)->insert(_ord, &subst, true, _splitter, std::move(ordCons), lits, splits);
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
void ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkEquations(Clause* cl) const
{
  if (!enabled) {
    return;
  }

  // TODO return if not enabled
  cl->iterLits().forEach([cl,this](Literal* lit){
    if (!lit->isEquality() || lit->isNegative()) {
      return;
    }
    auto t0 = lit->termArg(0);
    auto t1 = lit->termArg(1);
    RobSubstitution subs;
    if (!subs.unify(t0,0,t1,0)) {
      return;
    }
    auto clDataPtr = getDataPtr(cl, /*doAllocate=*/true);
    auto rsubs = ResultSubstitution::fromSubstitution(&subs, 0, 0);
    (*clDataPtr)->insert(_ord, rsubs.ptr(), /*result*/false, /*splitter*/nullptr, OrderingConstraints(), LiteralSet::getEmpty(), SplitSet::getEmpty());
  });
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
void ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkSubsumption(Clause* cl) const
{
  if (!enabled) {
    return;
  }

//   auto clDataPtr = getDataPtr(cl, /*doAllocate=*/false);
//   if (!clDataPtr) {
//     return;
//   }
//   auto cld = *clDataPtr;

//   if (cld->_redundant || cld->isEmpty()) {
//     return;
//   }

//   if (!cld->_subs) {
//     auto ts = cld->getInstances([](unsigned v) { return TermList::var(v); });
//     static ConstraintIndex::SubstMatcher matcher;
//     matcher.init((*clDataPtr), ts);
//     Entries* es = matcher.next();
//     matcher.reset();
//     // there can be only one such matching under linearization
// #if !LINEARIZE
//     static_assert(false);
// #endif
//     if (!es) {
//       // in this case we try to create the subsumption next time
//       return;
//     }
//     ASS(es->comparator);

//     cld->_subs = new Subsumption(*es->comparator.get(), *_ord, OrderingConstraints(), /*ground=*/true);
//     for (unsigned i = 0; i < cl->numSelected(); i++) {
//       auto lit = (*cl)[i];
//       if (!lit->isEquality() || _ord->getEqualityArgumentOrder(lit)!=Ordering::INCOMPARABLE) {
//         continue;
//       }

//       auto& [subsLtr, subsRtl] = cld->_litSubs[i];
//       ASS(!subsLtr && !subsRtl);
//       Renaming r;
//       for (const auto t : ts) {
//         r.normalizeVariables(t);
//       }
//       auto lhs = r.apply(lit->termArg(0));
//       auto rhs = r.apply(lit->termArg(1));
//       subsLtr = new Subsumption(*es->comparator.get(), *_ord, { { lhs, rhs, Ordering::GREATER } }, /*ground=*/true);
//       subsRtl = new Subsumption(*es->comparator.get(), *_ord, { { rhs, lhs, Ordering::GREATER } }, /*ground=*/true);
//     }
//   }
//   if (cld->_subs->check()) {
//     cld->_redundant = true;
//     env.statistics->groundRedundantClauses++;
//     return;
//   }

//   for (unsigned i = 0; i < cl->numSelected(); i++) {
//     auto& [subsLtr, subsRtl] = cld->_litSubs[i];
//     auto& [redLtr, redRtl] = cld->_litRedundant[i];
//     if (!redLtr && subsLtr && subsLtr->check()) {
//       redLtr = true;
//       env.statistics->groundRedundantEquationOrientations++;
//     }
//     if (!redRtl && subsRtl && subsRtl->check()) {
//       redRtl = true;
//       env.statistics->groundRedundantEquationOrientations++;
//     }
//   }
}

}
