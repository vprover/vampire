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
 * @file OrderingComparator.cpp
 * Implements class OrderingComparator.
 */

#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"

#include "KBO.hpp"
#include "SubstHelper.hpp"

#include "OrderingComparator.hpp"

using namespace std;

namespace Kernel {

// OrderingComparator

static Ordering::Result kGtPtr = Ordering::GREATER;
static Ordering::Result kEqPtr = Ordering::EQUAL;
static Ordering::Result kLtPtr = Ordering::LESS;

OrderingComparator* OrderingComparator::createForSingleComparison(const Ordering& ord, TermList lhs, TermList rhs, bool ground)
{
  static Map<tuple<TermList,TermList,bool>,OrderingComparator*> cache; // TODO this leaks now

  OrderingComparator** ptr;
  if (cache.getValuePtr({ lhs, rhs, ground }, ptr, nullptr)) {
    *ptr = ord.createComparator(ground).release();
    // (*ptr)->_threeValued = true;
    (*ptr)->_source = Branch(lhs, rhs);
    (*ptr)->_source.node()->gtBranch = Branch(&kGtPtr, (*ptr)->_sink);
    (*ptr)->_source.node()->eqBranch = Branch(&kEqPtr, (*ptr)->_sink);
    if (ground) {
      (*ptr)->_source.node()->ngeBranch = Branch(&kLtPtr, (*ptr)->_sink);
    } else {
      (*ptr)->_source.node()->ngeBranch = (*ptr)->_sink;
    }
  }
  return *ptr;
}

OrderingComparator::OrderingComparator(const Ordering& ord, bool ground)
: _ord(ord), _source(nullptr, Branch()), _sink(_source),
  _curr(&_source), _prev(nullptr), _appl(nullptr), _ground(ground)
{
  _sink.node()->ready = true;
}

OrderingComparator::~OrderingComparator() = default;

void OrderingComparator::init(const SubstApplicator* appl)
{
  _curr = &_source;
  _prev = nullptr;
  _appl = appl;
}

void* OrderingComparator::next()
{
  ASS(_appl);
  ASS(_curr);
  ASS(!_ground);

  for (;;) {
    processCurrentNode();

    auto node = _curr->node();
    ASS(node->ready);

    if (node->tag == Node::T_DATA) {
      if (!node->data) {
        return nullptr;
      }
      _prev = _curr;
      _curr = &node->alternative;
      return node->data;
    }

    Ordering::Result comp = Ordering::INCOMPARABLE;
    if (node->tag == Node::T_TERM) {

      comp = _ord.compareUnidirectional(
        AppliedTerm(node->lhs, _appl, true),
        AppliedTerm(node->rhs, _appl, true));

    } else {
      ASS_EQ(node->tag, Node::T_POLY);

      const auto& kbo = static_cast<const KBO&>(_ord);
      auto weight = node->poly->constant;
      ZIArray<int> varDiffs;
      for (const auto& [var, coeff] : node->poly->varCoeffPairs) {
        AppliedTerm tt(TermList::var(var), _appl, true);

        VariableIterator vit(tt.term);
        while (vit.hasNext()) {
          auto v = vit.next();
          varDiffs[v.var()] += coeff;
          // since the counts are sorted in descending order,
          // this can only mean we will fail
          if (varDiffs[v.var()]<0) {
            goto loop_end;
          }
        }
        int64_t w = kbo.computeWeight(tt);
        weight += coeff*w;
        // due to descending order of counts,
        // this also means failure
        if (coeff<0 && weight<0) {
          goto loop_end;
        }
      }

      if (weight > 0) {
        comp = Ordering::GREATER;
      } else if (weight == 0) {
        comp = Ordering::EQUAL;
      }
    }
loop_end:
    _prev = _curr;
    _curr = &node->getBranch(comp);
  }
  return nullptr;
}

void OrderingComparator::insert(const Stack<TermOrderingConstraint>& comps, void* data)
{
  ASS(data);
  static Ordering::Result ordVals[] = { Ordering::GREATER, Ordering::EQUAL, Ordering::INCOMPARABLE };
  // we mutate current fail node and add a new one
  auto curr = &_sink;
  Branch newFail(nullptr, Branch());
  newFail.node()->ready = true;

  curr->node()->~Node();
  curr->node()->ready = false;

  if (comps.isNonEmpty()) {
    curr->node()->tag = Node::T_TERM;
    curr->node()->lhs = comps[0].lhs;
    curr->node()->rhs = comps[0].rhs;
    for (unsigned i = 0; i < 3; i++) {
      if (ordVals[i] != comps[0].rel) {
        curr->node()->getBranch(ordVals[i]) = newFail;
      }
    }
    curr = &curr->node()->getBranch(comps[0].rel);
    for (unsigned i = 1; i < comps.size(); i++) {
      auto [lhs,rhs,rel] = comps[i];
      *curr = OrderingComparator::Branch(lhs, rhs);
      for (unsigned i = 0; i < 3; i++) {
        if (ordVals[i] != rel) {
          curr->node()->getBranch(ordVals[i]) = newFail;
        }
      }
      curr = &curr->node()->getBranch(rel);
    }
    *curr = Branch(data, newFail);
  } else {
    curr->node()->tag = Node::T_DATA;
    curr->node()->data = data;
    curr->node()->alternative = newFail;
  }

  _sink = newFail;
}

void OrderingComparator::processCurrentNode()
{
  ASS(_curr->node());
  while (!_curr->node()->ready)
  {
    auto node = _curr->node();

    if (node->tag == Node::T_DATA) {
      ASS(node->data); // no fail nodes here
      // if refcnt > 1 we have to copy the node,
      // otherwise we can mutate the original
      if (node->refcnt > 1) {
        *_curr = Branch(node->data, node->alternative);
      }
      auto trace = getCurrentTrace();
      // If this happens this branch is invalid.
      // Since normal execution cannot reach it,
      // we can put a "success" here.
      if (!trace) {
        *_curr = _sink;
        return;
      }
      _curr->node()->trace = trace;
      _curr->node()->ready = true;
      return;
    }
    if (node->tag == Node::T_POLY) {
      processPolyNode();
      continue;
    }

    // Use compare here to filter out as many
    // precomputable comparisons as possible.
    auto comp = _ord.compare(node->lhs,node->rhs);
    if (comp != Ordering::INCOMPARABLE) {
      if (comp == Ordering::LESS) {
        *_curr = node->ngeBranch;
      } else if (comp == Ordering::GREATER) {
        *_curr = node->gtBranch;
      } else {
        *_curr = node->eqBranch;
      }
      continue;
    }
    // If we have a variable, we cannot expand further.
    if (node->lhs.isVar() || node->rhs.isVar()) {
      processVarNode();
      continue;
    }
    processTermNode();
  }
}

void OrderingComparator::processVarNode()
{
  auto node = _curr->node();
  auto trace = getCurrentTrace();

  // If this happens this branch is invalid.
  // Since normal execution cannot reach it,
  // we can put a "success" here.
  if (!trace) {
    *_curr = _sink;
    return;
  }

  Ordering::Result val;
  if (trace->get(node->lhs, node->rhs, val)) {
    if (val == Ordering::GREATER) {
      *_curr = node->gtBranch;
    } else if (val == Ordering::EQUAL) {
      *_curr = node->eqBranch;
    } else {
      *_curr = node->ngeBranch;
    }
    return;
  }
  // if refcnt > 1 we have to copy the node,
  // otherwise we can mutate the original
  if (node->refcnt > 1) {
    *_curr = Branch(node->lhs, node->rhs);
    _curr->node()->eqBranch = node->eqBranch;
    _curr->node()->gtBranch = node->gtBranch;
    _curr->node()->ngeBranch = node->ngeBranch;
  }
  _curr->node()->ready = true;
  _curr->node()->trace = trace;
}

void OrderingComparator::processPolyNode()
{
  auto node = _curr->node();
  auto trace = getCurrentTrace();

  // If this happens this branch is invalid.
  // Since normal execution cannot reach it,
  // we can put a "success" here.
  if (!trace) {
    *_curr = _sink;
    return;
  }

  unsigned pos = 0;
  unsigned neg = 0;

  auto vcs = node->poly->varCoeffPairs;

  for (unsigned i = 0; i < vcs.size();) {
    auto& [var, coeff] = vcs[i];
    for (unsigned j = i+1; j < vcs.size();) {
      auto& [var2, coeff2] = vcs[j];
      Ordering::Result res;
      if (trace->get(TermList::var(var), TermList::var(var2), res) && res == Ordering::EQUAL) {
        coeff += coeff2;
        swap(vcs[j],vcs.top());
        vcs.pop();
        continue;
      }
      j++;
    }
    if (coeff == 0) {
      swap(vcs[i],vcs.top());
      vcs.pop();
      continue;
    } else if (coeff > 0) {
      pos++;
    } else {
      neg++;
    }
    i++;
  }

  auto constant = node->poly->constant;
  if (constant == 0 && pos == 0 && neg == 0) {
    *_curr = node->eqBranch;
    return;
  }
  if (constant >= 0 && neg == 0) {
    *_curr = node->gtBranch;
    return;
  }
  if (constant <= 0 && pos == 0) {
    *_curr = node->ngeBranch;
    return;
  }
  auto poly = Polynomial::get(constant, vcs);

  // if refcnt > 1 we have to copy the node,
  // otherwise we can mutate the original
  if (node->refcnt > 1) {
    *_curr = Branch(poly);
    _curr->node()->eqBranch = node->eqBranch;
    _curr->node()->gtBranch = node->gtBranch;
    _curr->node()->ngeBranch = node->ngeBranch;
  } else {
    _curr->node()->poly = poly;
  }
  _curr->node()->trace = trace;
  _curr->node()->ready = true;
}

void OrderingComparator::processTermNode()
{
  ASS(_curr->node() && !_curr->node()->ready);
  _curr->node()->ready = true;
  _curr->node()->trace = Trace::getEmpty(_ord);
}

const OrderingComparator::Trace* OrderingComparator::getCurrentTrace()
{
  ASS(!_curr->node()->ready);

  if (!_prev) {
    return Trace::getEmpty(_ord);
  }

  ASS(_prev->node()->ready);
  ASS(_prev->node()->trace);

  switch (_prev->node()->tag) {
    case Node::T_TERM: {
      auto lhs = _prev->node()->lhs;
      auto rhs = _prev->node()->rhs;
      Ordering::Result res;
      if (_curr == &_prev->node()->eqBranch) {
        res = Ordering::EQUAL;
      } else if (_curr == &_prev->node()->gtBranch) {
        res = Ordering::GREATER;
      } else {
        ASS_EQ(_curr, &_prev->node()->ngeBranch);
        if (_ground) {
          res = Ordering::LESS;
        } else {
          res = Ordering::INCOMPARABLE;
        }
      }
      return Trace::set(_prev->node()->trace, { lhs, rhs, res });
    }
    case Node::T_DATA:
    case Node::T_POLY: {
      return _prev->node()->trace;
    }
  }
  ASSERTION_VIOLATION;
}

// Branch

OrderingComparator::Branch::Branch(void* data, Branch alt)
{
  setNode(new Node(data, alt));
}

OrderingComparator::Branch::Branch(TermList lhs, TermList rhs)
{
  setNode(new Node(lhs, rhs));
}

OrderingComparator::Branch::Branch(const Polynomial* p)
{
  setNode(new Node(p));
}

OrderingComparator::Branch::~Branch()
{
  setNode(nullptr);
}

OrderingComparator::Branch::Branch(const Branch& other)
{
  setNode(other._node);
}

OrderingComparator::Node* OrderingComparator::Branch::node() const
{
  return _node;
}

void OrderingComparator::Branch::setNode(Node* node)
{
  if (node) {
    node->incRefCnt();
  }
  if (_node) {
    _node->decRefCnt();
  }
  _node = node;
}

OrderingComparator::Branch::Branch(Branch&& other)
{
  swap(_node,other._node);
}

OrderingComparator::Branch& OrderingComparator::Branch::operator=(Branch other)
{
  swap(_node,other._node);
  return *this;
}

// Node

OrderingComparator::Node::Node(void* data, Branch alternative)
  : tag(T_DATA), data(data), alternative(alternative) {}

OrderingComparator::Node::Node(TermList lhs, TermList rhs)
  : tag(T_TERM), lhs(lhs), rhs(rhs) {}

OrderingComparator::Node::Node(const Polynomial* p)
  : tag(T_POLY), poly(p) {}

OrderingComparator::Node::~Node()
{
  if (tag==T_DATA) {
    alternative.~Branch();
  }
  ready = false;
}

void OrderingComparator::Node::incRefCnt()
{
  refcnt++;
}

void OrderingComparator::Node::decRefCnt()
{
  ASS(refcnt>=0);
  refcnt--;
  if (refcnt==0) {
    delete this;
  }
}

OrderingComparator::Branch& OrderingComparator::Node::getBranch(Ordering::Result r)
{
  switch (r) {
    case Ordering::EQUAL: return eqBranch;
    case Ordering::GREATER: return gtBranch;
    case Ordering::INCOMPARABLE:
    case Ordering::LESS:
      // no distinction between less and incomparable
      return ngeBranch;
  }
  ASSERTION_VIOLATION_REP(r);
}

// Polynomial

const OrderingComparator::Polynomial* OrderingComparator::Polynomial::get(int constant, const Stack<VarCoeffPair>& varCoeffPairs)
{
  static Set<Polynomial*, DerefPtrHash<DefaultHash>> polys;

  sort(varCoeffPairs.begin(),varCoeffPairs.end(),[](const auto& vc1, const auto& vc2) {
    auto vc1pos = vc1.second>0;
    auto vc2pos = vc2.second>0;
    return (vc1pos && !vc2pos) || (vc1pos == vc2pos && vc1.first<vc2.first);
  });

  Polynomial poly{ constant, varCoeffPairs };
  // The code below depends on the fact that the first argument
  // is only called when poly is not used anymore, otherwise the
  // move would give undefined behaviour.
  bool unused;
  return polys.rawFindOrInsert(
    [&](){ return new Polynomial(std::move(poly)); },
    poly.defaultHash(),
    [&](Polynomial* p) { return *p == poly; },
    unused);
}

// VarOrderExtractor

OrderingComparator::VarOrderExtractor::VarOrderExtractor(OrderingComparator* comp, const SubstApplicator* appl, POStruct po_struct)
  : comp(comp), appl(appl), res(po_struct)
{
  ASS(po_struct.tpo && po_struct.tpo->isGround());
  path->push({ &comp->_source, po_struct, nullptr });
}

bool OrderingComparator::VarOrderExtractor::hasNext(bool& nodebug)
{
  if (fresh) {
    fresh = false;
  } else {
    if (!backtrack()) {
      return false;
    }
  }
  while (path->isNonEmpty()) {
    auto& [curr,ps,voe] = path->top();
    comp->_prev = (path.size()==1) ? nullptr : get<0>(path[path.size()-2]);
    comp->_curr = curr;
    comp->processCurrentNode();

    auto node = comp->_curr->node();
    switch (node->tag) {
      case Node::T_DATA: {
        // we have success, return true
        if (node->data) {
          res = ps;
          return true;
        }
        if (!backtrack()) {
          return false;
        }
        break;
      }
      case Node::T_POLY: {
        // TODO this could be just branching three ways for now
        nodebug = true;
        return false;
      }
      case Node::T_TERM: {
        auto lhs = AppliedTerm(node->lhs, appl, true).apply();
        auto rhs = AppliedTerm(node->rhs, appl, true).apply();
        if (voe == nullptr) {
          voe = make_unique<Iterator>(comp->_ord, lhs, rhs, ps);
        }
        auto [comp,new_ps] = voe->next();
        // a null tpo signifies the end of the iterator
        if (!new_ps.tpo) {
          if (!backtrack()) {
            return false;
          }
          break;
        }
        btStack.push(path.size());
        path->push({ &node->getBranch(comp), new_ps, nullptr });
        break;
      }
    }
  }
  return false;
}

bool OrderingComparator::VarOrderExtractor::backtrack()
{
  if (btStack.isEmpty()) {
    return false;
  }
  path->truncate(btStack.pop());
  return true;
}

OrderingComparator::VarOrderExtractor::Iterator::Iterator(const Ordering& ord, TermList lhs, TermList rhs, POStruct po_struct)
  : _comp(), _po_struct(po_struct)
{
  _comp = createForSingleComparison(ord, lhs, rhs, /*ground=*/false);
  _path->push({ &_comp->_source, _po_struct, 0 });
}

std::pair<Result,POStruct> OrderingComparator::VarOrderExtractor::Iterator::next()
{
  while (_path->isNonEmpty()) {
    auto& [branch, ps, index] = _path->top();
    _comp->_prev = (_path.size()==1) ? nullptr : get<0>(_path[_path.size()-2]);
    _comp->_curr = branch;
    _comp->processCurrentNode();

    auto node = branch->node();
    if (node->tag == Node::T_DATA) {
      auto res_ps = ps; // save result before popping _path
      _path->pop();
      if (node->data) {
        return { *static_cast<Result*>(node->data), res_ps };
      }
      _retIncomp = true;
      continue;
    }

    Stack<BranchingPoint>* ptr;
    if (_map.getValuePtr(branch, ptr, Stack<BranchingPoint>())) {
      initCurrent(ptr);
    }
    bool success = false;
    while (index < ptr->size()) {
      auto& bp = (*ptr)[index++];
      POStruct eps = ps;
      if (tryExtend(eps, bp.cons)) {
        // go one down
        _path->push({ bp.branch, eps, 0 });
        success = true;
        break;
      }
    }
    if (!success) {
      _path->pop();
    }
  }
  // incomparable is the default we return at the end,
  // if the diagram contains it at all
  if (_retIncomp) {
    _retIncomp = false;
    return { Ordering::INCOMPARABLE, _po_struct };
  }
  return { Ordering::INCOMPARABLE, POStruct(nullptr) };
}

bool OrderingComparator::VarOrderExtractor::Iterator::tryExtend(POStruct& po_struct, const Stack<TermOrderingConstraint>& cons)
{
  for (const auto& con : cons) {
    // already contains relation
    Ordering::Result res;
    if (po_struct.tpo->get(con.lhs, con.rhs, res) && res == con.rel) {
      continue;
    }
    auto etpo = TermPartialOrdering::set(po_struct.tpo, con);
    // extension failed
    if (!etpo) {
      return false;
    }
    stringstream str;
    // str << *po_struct.tpo << endl << "===" << endl << con << endl << "===" << endl << *etpo << endl;
    ASS_REP(etpo->isGround(), str.str());
    // relation did not change
    if (etpo == po_struct.tpo) {
      continue;
    }
    po_struct.tpo = etpo;
    po_struct.cons.push(con);
  }
  return true;
}

void OrderingComparator::VarOrderExtractor::Iterator::initCurrent(Stack<BranchingPoint>* ptr)
{
  auto node = _comp->_curr->node();
  ASS(node->ready);

  // TODO not sure if we should enforce LESS on ngeBranches, those
  // constraints are technically not needed to get GREATER in the end

  switch (node->tag) {
    case Node::T_DATA: {
      break;
    }
    case Node::T_TERM: {
      auto lhs = node->lhs;
      auto rhs = node->rhs;
      ASS(lhs.isVar() || rhs.isVar());
      if (lhs.isVar() && rhs.isVar()) {
        // x ? y
        ptr->push({ { { lhs, rhs, Result::GREATER } }, &node->gtBranch });
        ptr->push({ { { lhs, rhs, Result::EQUAL   } }, &node->eqBranch });
      } else if (rhs.isVar()) {
        ASS(lhs.isTerm());
        DHSet<TermList> seen;
        // s[x_1,...,x_n] ? y
        VariableIterator vit(lhs.term());
        while (vit.hasNext()) {
          auto v = vit.next();
          if (!seen.insert(v)) {
            continue;
          }
          // x_i ≥ y ⇒ s[x_1,...,x_n] > y
          ptr->push({ { { v, rhs, Result::GREATER } }, &node->gtBranch });
          ptr->push({ { { v, rhs, Result::EQUAL   } }, &node->gtBranch });
        }
      }
      ptr->push({ Stack<TermOrderingConstraint>(), &node->ngeBranch });
      break;
    }
    case Node::T_POLY: {
      ASSERTION_VIOLATION;
      break;
    }
  }
}

// Printing

std::ostream& operator<<(std::ostream& out, const OrderingComparator::Node::Tag& t)
{
  using Tag = OrderingComparator::Node::Tag;
  switch (t) {
    case Tag::T_DATA: return out << "d";
    case Tag::T_TERM: return out << "t";
    case Tag::T_POLY: return out << "p";
  }
  ASSERTION_VIOLATION;
}

std::ostream& operator<<(std::ostream& out, const OrderingComparator::Node& node)
{
  using Tag = OrderingComparator::Node::Tag;
  out << (Tag)node.tag << (node.ready?" ":"? ");
  switch (node.tag) {
    case Tag::T_DATA: return out << node.data;
    case Tag::T_POLY: return out << *node.poly;
    case Tag::T_TERM: return out << node.lhs << " " << node.rhs;
  }
  ASSERTION_VIOLATION;
}

std::ostream& operator<<(std::ostream& out, const OrderingComparator::Polynomial& poly)
{
  bool first = true;
  for (const auto& [var, coeff] : poly.varCoeffPairs) {
    if (coeff > 0) {
      out << (first ? "" : " + ");
    } else {
      out << (first ? "- " : " - ");
    }
    first = false;
    auto abscoeff = std::abs(coeff);
    if (abscoeff!=1) {
      out << abscoeff << " * ";
    }
    out << TermList::var(var);
  }
  if (poly.constant) {
    out << (poly.constant<0 ? " - " : " + ");
    out << std::abs(poly.constant);
  }
  return out;
}

std::ostream& operator<<(std::ostream& str, const OrderingComparator& comp)
{
  Stack<std::pair<const OrderingComparator::Branch*, unsigned>> todo;
  todo.push(std::make_pair(&comp._source,0));
  // Note: using this set we get a more compact representation
  DHSet<OrderingComparator::Node*> seen;

  while (todo.isNonEmpty()) {
    auto kv = todo.pop();
    for (unsigned i = 0; i < kv.second; i++) {
      str << ((i+1 == kv.second) ? "  |--" : "  |  ");
    }
    str << *kv.first->node() << std::endl;
    if (seen.insert(kv.first->node())) {
      if (kv.first->node()->tag==OrderingComparator::Node::T_DATA) {
        if (kv.first->node()->data) {
          todo.push(std::make_pair(&kv.first->node()->alternative,kv.second+1));
        }
      } else {
        todo.push(std::make_pair(&kv.first->node()->ngeBranch,kv.second+1));
        todo.push(std::make_pair(&kv.first->node()->eqBranch,kv.second+1));
        todo.push(std::make_pair(&kv.first->node()->gtBranch,kv.second+1));
      }
    }
  }
  return str;
}

}
