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
      _curr->node()->prevPoly = getPrevPoly();
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
  _curr->node()->prevPoly = getPrevPoly();
  _curr->node()->trace = trace;
}

void TermOrderingDiagram::processPolyNode()
{
  auto node = _curr->node();
  auto trace = getCurrentTrace();
  auto prevPoly = getPrevPoly();

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

  // check if we have seen this polynomial
  // on the path leading here
  LinearConstraints linCons;
  auto polyIt = prevPoly;
  while (polyIt.first) {
    ASS_EQ(polyIt.first->tag, Node::T_POLY);
    switch (polyIt.second) {
      case Ordering::GREATER: {
        if (polyIt.first->poly == poly) {
          *_curr = node->gtBranch;
          return;
        }
        linCons.push({ polyIt.first->poly, LCSign::GT });
        break;
      }
      case Ordering::EQUAL: {
        if (polyIt.first->poly == poly) {
          *_curr = node->eqBranch;
          return;
        }
        linCons.push({ polyIt.first->poly, LCSign::GEQ });
        break;
      }
      case Ordering::INCOMPARABLE: {
        if (polyIt.first->poly == poly) {
          *_curr = node->ngeBranch;
          return;
        }
        break;
      }
      default:
        break;
    }
    polyIt = polyIt.first->prevPoly;
  }
 
  if (trace) {
    for (const auto& [var, coeff] : poly->varCoeffPairs) {
      auto trs = trace->collectForVariable(TermList::var(var));
      for (const auto& [t,r] : trs) {
        // TODO turn terms into polynomials with KBO
        if (t.isTerm()) {
          continue;
        }
        switch (r) {
          case Ordering::GREATER:
            // x > y → |x| - |y| ≥ 0
            linCons.push({ Polynomial::get(0, { { var, 1 }, { t.var(), -1 } }), LCSign::GEQ });
            break;
          case Ordering::EQUAL:
            // x = y → |x| - |y| = 0
            linCons.push({ Polynomial::get(0, { { var, 1 }, { t.var(), -1 } }), LCSign::EQ });
            break;
          case Ordering::LESS:
            // x < y → |y| - |x| ≥ 0
            linCons.push({ Polynomial::get(0, { { var, -1 }, { t.var(), 1 } }), LCSign::GEQ });
            break;
          default:
            break;
        }
      }
    }
  }

  if (linCons.isNonEmpty()) {
    linCons.push({ poly, LCSign::GT });
    auto gt_ok = fourierMotzkin(linCons);

    linCons.top().sign = LCSign::EQ;
    auto eq_ok = fourierMotzkin(linCons);

    linCons.top().poly = poly->negate();
    linCons.top().sign = LCSign::GT;
    auto lt_ok = fourierMotzkin(linCons);

    if (gt_ok) {
      if (!eq_ok && !lt_ok) {
        *_curr = node->gtBranch;
        return;
      }
    } else if (!lt_ok) {
      ASS(eq_ok);
      *_curr = node->eqBranch;
      return;
    } else if (!eq_ok) {
      *_curr = node->ngeBranch;
      return;
    }
  }

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
  _curr->node()->prevPoly = prevPoly;
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

std::pair<TermOrderingDiagram::Node*, Ordering::Result> TermOrderingDiagram::getPrevPoly()
{
  auto res = make_pair((Node*)nullptr, Ordering::INCOMPARABLE);
  if (_prev) {
    // take value from previous node by default
    res = _prev->node()->prevPoly;

    // override value if the previous is a poly node 
    if (_prev->node()->tag == Node::T_POLY) {
      res.first = _prev->node();
      if (_curr == &_prev->node()->gtBranch) {
        res.second = Ordering::GREATER;
      } else if (_curr == &_prev->node()->eqBranch) {
        res.second = Ordering::EQUAL;
      } else {
        ASS_EQ(_curr, &_prev->node()->ngeBranch);
        res.second = Ordering::INCOMPARABLE;
      }
    }
  }
  return res;
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

TermOrderingDiagram::Branch::Branch(const Polynomial* p)
{
  setNode(new Node(p));
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

TermOrderingDiagram::Node::Node(const Polynomial* p)
  : tag(T_POLY), poly(p) {}

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

// Polynomial

bool TermOrderingDiagram::fourierMotzkin(LinearConstraints linCons)
{
  // first eliminate equations
  for (unsigned i = 0; i < linCons.size();) {
    const auto& [P, eqSign] = linCons[i];
    if (eqSign != LCSign::EQ) {
      i++;
      continue;
    }

    if (P->varCoeffPairs.isEmpty()) {
      if (P->constant != 0) {
        return false;
      }
      continue;
    }

    auto [x, c] = P->varCoeffPairs[0];

    for (unsigned j = 0; j < linCons.size(); j++) {
      if (i == j) {
        continue;
      }
      auto& [Q, sign] = linCons[j];
      bool containsX = false;
      int d;
      for (const auto& [var, coeff] : Q->varCoeffPairs) {
        if (var == x) {
          containsX = true;
          d = coeff;
          break;
        }
      }
      if (containsX) {
        // we eliminate x with c ⋅ x + P = 0 from expression d ⋅ x + Q ≥ 0
        // if c > 0, by creating c(d ⋅ x + Q) - d(c ⋅ x + P) ≥ 0
        if (c > 0) {
          Q = Q->add(c, P, -d);
        }
        // if c < 0, by creating -c(d ⋅ x + Q) + d(c ⋅ x + P) ≥ 0
        else {
          Q = Q->add(-c, P, d);
        }
      }
    }
    std::swap(linCons[i],linCons.top());
    linCons.pop();
  }

  while (linCons.isNonEmpty()) {
    LinearConstraints newLinCons;
    unsigned x;
    bool foundX = false;
    // tuples (P,c,b) s.t. if b is true, then P < c⋅x, otherwise P ≤ c⋅x
    Stack<tuple<const Polynomial*, int, bool>> less;
    // tuples (P,c,b) s.t. if b is true, then P > c⋅x, otherwise P ≥ c⋅x
    Stack<tuple<const Polynomial*, int, bool>> greater;

    for (const auto& [poly, sign] : linCons) {
      ASS_NEQ(sign, LCSign::EQ);

      // check unsatisfiability of constraint without variables
      if (poly->varCoeffPairs.isEmpty()) {
        if (sign == LCSign::GEQ && poly->constant < 0) {
          return false;
        }
        if (sign == LCSign::GT && poly->constant <= 0) {
          return false;
        }
        continue;
      }

      // set variable x if needed
      if (!foundX) {
        x = poly->varCoeffPairs[0].first;
        foundX = true;
      }

      int c;
      bool coeffFound = false;
      for (const auto& [var, coeff] : poly->varCoeffPairs) {
        if (var == x) {
          ASS(!coeffFound);
          coeffFound = true;
          c = coeff;
          break;
        }
      }
      if (coeffFound) {
        ASS_NEQ(c,0);
        // -c ⋅ x + P ≥ 0 implies P / c ≥ x
        if (c < 0) {
          greater.push({ poly, std::abs(c), sign == LCSign::GT });
        }
        // d ⋅ x + Q ≥ 0 implies x ≥ -Q / d
        else {
          less.push({ poly, std::abs(c), sign == LCSign::GT });
        }
      } else {
        newLinCons.push({ poly, sign });
      }
    }
    for (const auto& [P, c, gstrict] : greater) {
      for (const auto& [Q, d, lstrict] : less) {
        newLinCons.push({
          // As noted above, we have P / c ≥ x ≥ -Q / d,
          // so we need the constraint d ⋅ P + c ⋅ Q ≥ 0.
          // We get this simply by d(-c ⋅ x + P) + c(d ⋅ x + Q) ≥ 0
          P->add(d, Q, c),
          // if either inequation is strict, we get > instead of ≥
          (lstrict || gstrict) ? LCSign::GT : LCSign::GEQ
        });
      }
    }
    linCons = newLinCons;
  }
  return true;
}

const TermOrderingDiagram::Polynomial* TermOrderingDiagram::Polynomial::get(int constant, const Stack<VarCoeffPair>& varCoeffPairs)
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

const TermOrderingDiagram::Polynomial* TermOrderingDiagram::Polynomial::negate() const
{
  Stack<VarCoeffPair> res;
  for (const auto& [var, coeff] : varCoeffPairs) {
    res.push({ var, -coeff });
  }
  return Polynomial::get(-constant, res);
}

const TermOrderingDiagram::Polynomial* TermOrderingDiagram::Polynomial::add(
  int c, const Polynomial* Q, int d) const
{
  ZIArray<int> varCoeffs;

  for (const auto& [var, coeff] : varCoeffPairs) {
    varCoeffs[var] += coeff * c;
  }
  for (const auto& [var, coeff] : Q->varCoeffPairs) {
    varCoeffs[var] += coeff * d;
  }
  
  Stack<VarCoeffPair> res;
  for (unsigned i = 0; i < varCoeffs.size(); i++) {
    if (varCoeffs[i]) {
      res.push({ i, varCoeffs[i] });
    }
  }
  return Polynomial::get(constant * c + Q->constant * d, res);
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
    case Tag::T_POLY: return out << *node.poly;
    case Tag::T_TERM: return out << node.lhs << " " << node.rhs;
  }
  ASSERTION_VIOLATION;
}

std::ostream& operator<<(std::ostream& out, const TermOrderingDiagram::Polynomial& poly)
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

std::ostream& operator<<(std::ostream& str, const TermOrderingDiagram::LCSign& lcSign)
{
  switch (lcSign) {
    case TermOrderingDiagram::LCSign::EQ:
      str << "=";
      break;
    case TermOrderingDiagram::LCSign::GEQ:
      str << "≥";
      break;
    case TermOrderingDiagram::LCSign::GT:
      str << ">";
      break;
  }
  return str;
}

std::ostream& operator<<(std::ostream& str, const TermOrderingDiagram::LinearConstraint& linCon)
{
  str << *linCon.poly << " " << linCon.sign << " 0";
  return str;
}

}
