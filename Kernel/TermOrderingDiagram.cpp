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
 * @file TermOrderingDiagram.cpp
 * Implements class TermOrderingDiagram.
 */

#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"

#include "KBO.hpp"
#include "SubstHelper.hpp"

#include "TermOrderingDiagram.hpp"

using namespace std;

namespace Kernel {

// TermOrderingDiagram

TermOrderingDiagram::TermOrderingDiagram(const Ordering& ord)
: _ord(ord), _source(nullptr, Branch()), _sink(_source), _curr(&_source), _prev(nullptr), _appl(nullptr)
{
  _sink.node()->ready = true;
}

TermOrderingDiagram::~TermOrderingDiagram() = default;

void TermOrderingDiagram::init(const SubstApplicator* appl)
{
  _curr = &_source;
  _prev = nullptr;
  _appl = appl;
}

void* TermOrderingDiagram::next()
{
  ASS(_appl);
  ASS(_curr);

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
        AppliedTerm(node->lhs, _appl),
        AppliedTerm(node->rhs, _appl));

    } else {
      ASS_EQ(node->tag, Node::T_POLY);

      const auto& kbo = static_cast<const KBO&>(_ord);
      int weight = 0;
      ZIArray<int> varDiffs;
      if (kbo.positivityCheckHelper</*sign=*/1>(weight, varDiffs, node->linexp, _appl)) {
        if (weight > 0) {
          comp = Ordering::GREATER;
        } else if (weight == 0) {
          comp = Ordering::EQUAL;
        }
      }
    }
loop_end:
    _prev = _curr;
    _curr = &node->getBranch(comp);
  }
  return nullptr;
}

void TermOrderingDiagram::insert(const Stack<TermOrderingConstraint>& comps, void* data)
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
      *curr = TermOrderingDiagram::Branch(lhs, rhs);
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

void TermOrderingDiagram::processCurrentNode()
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
      _curr->node()->trace = getCurrentTrace();
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

void TermOrderingDiagram::processVarNode()
{
  auto node = _curr->node();
  auto trace = getCurrentTrace();
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

void TermOrderingDiagram::processPolyNode()
{
  auto node = _curr->node();
  auto trace = getCurrentTrace();

  unsigned pos = 0;
  unsigned neg = 0;

  auto vcs = node->linexp->varCoeffPairs;

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

  auto constant = node->linexp->constant;
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
  auto linexp = LinearExpression::get(constant, vcs);

  // if refcnt > 1 we have to copy the node,
  // otherwise we can mutate the original
  if (node->refcnt > 1) {
    *_curr = Branch(linexp);
    _curr->node()->eqBranch = node->eqBranch;
    _curr->node()->gtBranch = node->gtBranch;
    _curr->node()->ngeBranch = node->ngeBranch;
  } else {
    _curr->node()->linexp = linexp;
  }
  _curr->node()->trace = trace;
  _curr->node()->ready = true;
}

void TermOrderingDiagram::processTermNode()
{
  ASS(_curr->node() && !_curr->node()->ready);
  _curr->node()->ready = true;
  _curr->node()->trace = Trace::getEmpty(_ord);
}

const TermOrderingDiagram::Trace* TermOrderingDiagram::getCurrentTrace()
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
        res = Ordering::INCOMPARABLE;
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

TermOrderingDiagram::Branch::Branch(void* data, Branch alt)
{
  setNode(new Node(data, alt));
}

TermOrderingDiagram::Branch::Branch(TermList lhs, TermList rhs)
{
  setNode(new Node(lhs, rhs));
}

TermOrderingDiagram::Branch::Branch(const LinearExpression* e)
{
  setNode(new Node(e));
}

TermOrderingDiagram::Branch::~Branch()
{
  setNode(nullptr);
}

TermOrderingDiagram::Branch::Branch(const Branch& other)
{
  setNode(other._node);
}

TermOrderingDiagram::Node* TermOrderingDiagram::Branch::node() const
{
  return _node;
}

void TermOrderingDiagram::Branch::setNode(Node* node)
{
  if (node) {
    node->incRefCnt();
  }
  if (_node) {
    _node->decRefCnt();
  }
  _node = node;
}

TermOrderingDiagram::Branch::Branch(Branch&& other)
{
  swap(_node,other._node);
}

TermOrderingDiagram::Branch& TermOrderingDiagram::Branch::operator=(Branch other)
{
  swap(_node,other._node);
  return *this;
}

// Node

TermOrderingDiagram::Node::Node(void* data, Branch alternative)
  : tag(T_DATA), data(data), alternative(alternative) {}

TermOrderingDiagram::Node::Node(TermList lhs, TermList rhs)
  : tag(T_TERM), lhs(lhs), rhs(rhs) {}

TermOrderingDiagram::Node::Node(const LinearExpression* e)
  : tag(T_POLY), linexp(e) {}

TermOrderingDiagram::Node::~Node()
{
  if (tag==T_DATA) {
    alternative.~Branch();
  }
  ready = false;
}

void TermOrderingDiagram::Node::incRefCnt()
{
  refcnt++;
}

void TermOrderingDiagram::Node::decRefCnt()
{
  ASS(refcnt>=0);
  refcnt--;
  if (refcnt==0) {
    delete this;
  }
}

TermOrderingDiagram::Branch& TermOrderingDiagram::Node::getBranch(Ordering::Result r)
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

// Printing

std::ostream& operator<<(std::ostream& out, const TermOrderingDiagram::Node::Tag& t)
{
  using Tag = TermOrderingDiagram::Node::Tag;
  switch (t) {
    case Tag::T_DATA: return out << "d";
    case Tag::T_TERM: return out << "t";
    case Tag::T_POLY: return out << "p";
  }
  ASSERTION_VIOLATION;
}

std::ostream& operator<<(std::ostream& out, const TermOrderingDiagram::Node& node)
{
  using Tag = TermOrderingDiagram::Node::Tag;
  out << (Tag)node.tag << (node.ready?" ":"? ");
  switch (node.tag) {
    case Tag::T_DATA: return out << node.data;
    case Tag::T_POLY: return out << *node.linexp;
    case Tag::T_TERM: return out << node.lhs << " " << node.rhs;
  }
  ASSERTION_VIOLATION;
}

std::ostream& operator<<(std::ostream& str, const TermOrderingDiagram& tod)
{
  Stack<std::pair<const TermOrderingDiagram::Branch*, unsigned>> stack;
  stack.push(std::make_pair(&tod._source,0));
  // Note: using this set we get a more compact representation
  DHSet<TermOrderingDiagram::Node*> seen;

  while (stack.isNonEmpty()) {
    auto kv = stack.pop();
    for (unsigned i = 0; i < kv.second; i++) {
      str << ((i+1 == kv.second) ? "  |--" : "  |  ");
    }
    str << *kv.first->node() << std::endl;
    if (seen.insert(kv.first->node())) {
      if (kv.first->node()->tag==TermOrderingDiagram::Node::T_DATA) {
        if (kv.first->node()->data) {
          stack.push(std::make_pair(&kv.first->node()->alternative,kv.second+1));
        }
      } else {
        stack.push(std::make_pair(&kv.first->node()->ngeBranch,kv.second+1));
        stack.push(std::make_pair(&kv.first->node()->eqBranch,kv.second+1));
        stack.push(std::make_pair(&kv.first->node()->gtBranch,kv.second+1));
      }
    }
  }
  return str;
}

}
