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

#include <deque>

using namespace std;

namespace Kernel {

std::ostream& operator<<(std::ostream& out, const OrderingComparator::BranchTag& t)
{
  switch (t) {
    case OrderingComparator::BranchTag::T_DATA:
      out << "d";
      break;
    case OrderingComparator::BranchTag::T_TERM:
      out << "t";
      break;
    case OrderingComparator::BranchTag::T_POLY:
      out << "p";
      break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, const OrderingComparator::Node& node)
{
  out << (OrderingComparator::BranchTag)node.tag << (node.ready?" ":"? ");
  switch (node.tag) {
    case OrderingComparator::BranchTag::T_DATA: {
      out << node.data;
      break;
    }
    case OrderingComparator::BranchTag::T_POLY: {
      out << *node.poly;
      break;
    }
    case OrderingComparator::BranchTag::T_TERM: {
      out << node.lhs << " " << node.rhs;
      break;
    }
  }
  return out;
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
      if (i+1 == kv.second) {
        str << "  |--";
      } else {
        str << "  |  ";
      }
    }
    str << *kv.first->node() << std::endl;
    if (seen.insert(kv.first->node())) {
      if (kv.first->node()->tag==OrderingComparator::BranchTag::T_DATA) {
        if (kv.first->node()->data) {
          todo.push(std::make_pair(&kv.first->node()->alternative,kv.second+1));
        }
      } else {
        todo.push(std::make_pair(&kv.first->node()->ngeBranch,kv.second+1));
        todo.push(std::make_pair(&kv.first->node()->gtBranch,kv.second+1));
        todo.push(std::make_pair(&kv.first->node()->eqBranch,kv.second+1));
      }
    }
  }
  return str;
}

std::string to_tikz_term(TermList t)
{
  if (t.isVar()) {
    switch (t.var()) {
      case 0:
        return "x";
      case 1:
        return "y";
      case 2:
        return "z";
      default:
        return "x_"+Int::toString(t.var());
    }
  }
  auto tt = t.term();
  auto res = tt->functionName() + "(";
  for (unsigned i = 0; i < tt->arity(); i++) {
    res += to_tikz_term(*tt->nthArgument(i)) + ",";
  }
  res += ")";
  return res;
}

std::string OrderingComparator::to_dot() const
{
  std::deque<const OrderingComparator::Node*> todo;
  todo.push_back(_source.node());
  // Note: using this set we get a more compact representation
  DHMap<const OrderingComparator::Node*,unsigned> seen;

  seen.insert(_source.node(), 0);
  unsigned cnt = 1;

  auto getId = [&todo,&seen,&cnt](auto n) {
    unsigned* ptr;
    if (seen.getValuePtr(n,ptr)) {
      todo.push_back(n);
      *ptr = cnt++;
    }
    return *ptr;
  };

  enum class EdgeTag {
    GT,
    EQ,
    INC,
    ALT,
  };
  auto getBranch = [&getId](unsigned from, auto to_node, EdgeTag tag) -> std::string
  {
    auto res = "n" + Int::toString(from) + " -> n" + Int::toString(getId(to_node));
    switch (tag) {
      case EdgeTag::GT:
        res += " [style = gtedge]";
        break;
      case EdgeTag::EQ:
        res += " [style = eqedge]";
        break;
      case EdgeTag::INC:
        res += " [style = ngeedge]";
        break;
      case EdgeTag::ALT:
        res += " [style = trueedge]";
        break;
    }
    return res + ";\n";
  };

  std::string nodes = "source [style = invisible, label = \"\"];\n";
  std::string edges = "source -> n0 [style = trueedge];\n";

  while (!todo.empty()) {
    auto n = todo.front();
    todo.pop_front();
    auto id = seen.get(n);

    std::string style = "";
    std::string label = "";
    if (n->ready) {
      style += "processed,";
    }
    switch (n->tag) {
      case BranchTag::T_DATA: {
        auto alt = n->alternative.node();
        if (!alt) {
          // do not output anything for the fail node
          style += "sinknode,";
          label += "";
          break;
        }
        style += "datanode,";
        label += Int::toString((unsigned long)n->data);
        edges += getBranch(id, alt, EdgeTag::ALT);
        break;
      }
      case BranchTag::T_TERM: {
        // nodes += "termnode] (n" + Int::toString(id) + ") at (" + Int::toString(x) + "," + Int::toString(y) + ") {$"
        //   + to_tikz_term(n->lhs) + " \\comp " + to_tikz_term(n->rhs) + "$};\n";
        style += "termnode,";
        label += "$" + to_tikz_term(n->lhs) + " \\comp " + to_tikz_term(n->rhs) + "$";
        edges += getBranch(id, n->gtBranch.node(), EdgeTag::GT);
        edges += getBranch(id, n->eqBranch.node(), EdgeTag::EQ);
        edges += getBranch(id, n->ngeBranch.node(), EdgeTag::INC);
        break;
      }
      case BranchTag::T_POLY: {
        style += "polynode,";
        bool first = true;
        label += "$";
        for (const auto& [var, coeff] : n->poly->varCoeffPairs) {
          if (coeff > 0) {
            label += first ? "" : "+";
          } else {
            label += "-";
          }
          first = false;
          auto a = std::abs(coeff);
          if (a==1) {
            label += to_tikz_term(TermList::var(var));
          } else {
            label += Int::toString(a) + "\\cdot " + to_tikz_term(TermList::var(var));
          }
        }
        if (n->poly->constant) {
          label += n->poly->constant<0 ? "-" : (first ? "" : "+");
          label += Int::toString((int)std::abs(n->poly->constant));
        }
        label += "$";
        edges += getBranch(id, n->gtBranch.node(), EdgeTag::GT);
        edges += getBranch(id, n->eqBranch.node(), EdgeTag::EQ);
        edges += getBranch(id, n->ngeBranch.node(), EdgeTag::INC);
        break;
      }
    }
    nodes += "n" + Int::toString(id) + " [\n  style = \"" + style + "\"\n  label = \"" + label + "\"\n];\n";
  }
  return "digraph {\nnodesep = 0;\nsep = 0;\nranksep = 0;\nesep = 0;\n" + nodes + "\n" + edges + "}\n";
}

OrderingComparator::OrderingComparator(const Ordering& ord)
: _ord(ord), _source(nullptr, Branch()), _sink(_source), _curr(&_source), _prev(nullptr)
{
  _sink.node()->ready = true;
}

OrderingComparator::~OrderingComparator() = default;

void* OrderingComparator::next(const SubstApplicator* applicator)
{
  ASS(_curr);
  for (;;) {
    expand();
    auto node = _curr->node();
    ASS(node->ready);

    if (node->tag == BranchTag::T_DATA) {
      if (!node->data) {
        return nullptr;
      }
      _prev = _curr;
      _curr = &node->alternative;
      return node->data;
    }

    Ordering::Result comp = Ordering::INCOMPARABLE;
    if (node->tag == BranchTag::T_TERM) {

      comp = _ord.isGreaterOrEq(AppliedTerm(node->lhs,applicator,true),AppliedTerm(node->rhs,applicator,true));

    } else {
      ASS(node->tag == BranchTag::T_POLY);

      const auto& kbo = static_cast<const KBO&>(_ord);
      auto weight = node->poly->constant;
      ZIArray<int> varDiffs;
      for (const auto& [var, coeff] : node->poly->varCoeffPairs) {
        AppliedTerm tt(TermList::var(var), applicator, true);

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

void OrderingComparator::insert(const Stack<Ordering::Constraint>& comps, void* result)
{
  ASS(result);
  static Ordering::Result ordVals[] = { Ordering::EQUAL, Ordering::GREATER, Ordering::INCOMPARABLE };
  // we mutate current fail node and add a new one
  auto curr = &_sink;
  Branch newFail(nullptr, Branch());
  newFail.node()->ready = true;

  curr->node()->~Node();
  curr->node()->ready = false;

  if (comps.isNonEmpty()) {
    curr->node()->tag = T_TERM;
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
    *curr = Branch(result, newFail);
  } else {
    curr->node()->tag = T_DATA;
    curr->node()->data = result;
    curr->node()->alternative = newFail;
  }

  _sink = newFail;
}

void OrderingComparator::expand()
{
  ASS(_curr->node());
  while (!_curr->node()->ready)
  {
    auto node = _curr->node();

    if (node->tag == BranchTag::T_DATA) {
      ASS(node->data); // no fail nodes here
      // if refcnt > 1 we copy the node and
      // we can also safely use the original
      if (node->refcnt > 1) {
        *_curr = Branch(node->data, node->alternative);
      }
      _curr->node()->trace = getCurrentTrace();
      _curr->node()->prevPoly = getPrevPoly();
      _curr->node()->ready = true;
      return;
    }
    if (node->tag == BranchTag::T_POLY) {
      processPolyCase();
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
      processVarCase();
      continue;
    }

    expandTermCase();
  }
}

void OrderingComparator::expandTermCase()
{
  ASS(_curr->node() && !_curr->node()->ready);
  _curr->node()->ready = true;
}

std::ostream& operator<<(std::ostream& str, const OrderingComparator::LCSign& lcSign)
{
  switch (lcSign) {
    case OrderingComparator::LCSign::EQ:
      str << "=";
      break;
    case OrderingComparator::LCSign::GEQ:
      str << "≥";
      break;
    case OrderingComparator::LCSign::GT:
      str << ">";
      break;
  }
  return str;
}

std::ostream& operator<<(std::ostream& str, const OrderingComparator::LinearConstraint& linCon)
{
  str << *linCon.poly << " " << linCon.sign << " 0";
  return str;
}

bool OrderingComparator::fourierMotzkin(LinearConstraints linCons)
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

void OrderingComparator::processPolyCase()
{
  auto node = _curr->node();
  auto trace = getCurrentTrace();

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
  auto prevPoly = getPrevPoly();

  // check if we have seen this polynomial
  // on the path leading here
  LinearConstraints linCons;
  auto polyIt = prevPoly;
  while (polyIt.first) {
    ASS_EQ(polyIt.first->tag, BranchTag::T_POLY);
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
          env.statistics->intDBDownInduction++;
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

  // if refcnt > 1 we copy the node and
  // we can also safely use the original
  if (node->refcnt > 1) {
    *_curr = Branch(node->poly);
    _curr->node()->eqBranch = node->eqBranch;
    _curr->node()->gtBranch = node->gtBranch;
    _curr->node()->ngeBranch = node->ngeBranch;
  }

  _curr->node()->poly = poly;
  _curr->node()->prevPoly = prevPoly;
  _curr->node()->trace = trace;
  _curr->node()->ready = true;
}

void OrderingComparator::processVarCase()
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
  // if refcnt > 1 we copy the node and
  // we can also safely use the original
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

const OrderingComparator::Polynomial* OrderingComparator::Polynomial::negate() const
{
  Stack<VarCoeffPair> res;
  for (const auto& [var, coeff] : varCoeffPairs) {
    res.push({ var, -coeff });
  }
  return Polynomial::get(-constant, res);
}

const OrderingComparator::Polynomial* OrderingComparator::Polynomial::add(
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

const OrderingComparator::Trace* OrderingComparator::getCurrentTrace()
{
  ASS(!_curr->node()->ready);

  if (!_prev) {
    return Trace::getEmpty(_ord);
  }

  ASS(_prev->node()->ready);
  ASS(_prev->node()->trace);

  switch (_prev->node()->tag) {
    case BranchTag::T_TERM: {
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
    case BranchTag::T_DATA:
    case BranchTag::T_POLY: {
      return _prev->node()->trace;
    }
  }
  ASSERTION_VIOLATION;
}

std::pair<OrderingComparator::Node*, Ordering::Result> OrderingComparator::getPrevPoly()
{
  auto res = make_pair((Node*)nullptr, Ordering::INCOMPARABLE);
  if (_prev) {
    // take value from previous node by default
    res = _prev->node()->prevPoly;

    // override value if the previous is a poly node 
    if (_prev->node()->tag == BranchTag::T_POLY) {
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

OrderingComparator::Branch::~Branch()
{
  setNode(nullptr);
}

OrderingComparator::Branch::Branch(const Branch& other)
{
  setNode(other._node);
}

OrderingComparator::Branch& OrderingComparator::Branch::operator=(const Branch& other)
{
  if (&other==this) {
    return *this;
  }
  setNode(other.node());
  return *this;
}

OrderingComparator::Branch::Branch(Branch&& other)
  : _node(other._node)
{
  other._node = nullptr;
}

OrderingComparator::Branch& OrderingComparator::Branch::operator=(Branch&& other)
{
  if (&other==this) {
    return *this;
  }
  swap(_node,other._node);
  return *this;
}

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

}
