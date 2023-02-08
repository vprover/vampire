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
 * @file RewritingPositionTree.cpp

 * Implements class RewritingPositionTree.
 */

#include <cstring>

#include "Lib/Allocator.hpp"
#include "Lib/DArray.hpp"

#include "Term.hpp"
#include "TermIterators.hpp"

#include "RewritingPositionTree.hpp"

namespace Kernel
{

using namespace Lib;

RewritingPositionTree* RewritingPositionTree::createFromRewrite(RewritingPositionTree*& old, TermList term, TermList rwTerm, RewritingPositionTree* rhs)
{
  CALL("static RewritingPositionTree::createNewFromRewrite");
  TIME_TRACE("rewriting position tree maintenance");
  ASS(term.isTerm());
  ASS(rwTerm.isTerm());
  ASS(term.containsSubterm(rwTerm));

  Path rhsPath;
  // auto rhsPath = extractPath(rhs);
  if (term == rwTerm) {
    return nullptr;
    // return create(rhsPath);
  }

  if (!old) {
    auto oldRoot = new Node(nullptr); // owns
    auto newRoot = new Node(&oldRoot->getOwn()); // owns
    buildTree(oldRoot, newRoot, term.term(), rwTerm.term());
    old = new RewritingPositionTree(oldRoot);
    old->_active = true;
    return new RewritingPositionTree(newRoot);
  }
  ASS(old->_active);
  ASS(old->_root);
  auto res = old->createFromRewrite(term.term(), rwTerm.term(), rhsPath);
  return res;
}

RewritingPositionTree* RewritingPositionTree::createFromRewrite(Term* term, Term* rwTerm, const Path& rhsPath)
{
  CALL("RewritingPositionTree::createNewFromRewrite");
  if (!_root->hasMain() && !_root->getOwn().active) {
    auto newRoot = new Node(&_root->getOwn());
    buildTree(_root, newRoot, term, rwTerm);
    return new RewritingPositionTree(newRoot);
  }
  Term* curr = term;
  Node* currO = _root;
  State* currS = currO->hasMain() ? currO->getRef() : &currO->getOwn();
  Node* currN = new Node(currS);
  auto res = new RewritingPositionTree(currN);

  while (curr) {
    ASS(currS->active);
    auto reversed = currS->reversed;

    // TODO it suffices to start from main
    for (unsigned i = 0; i < curr->numTermArguments(); i++) {
      auto j = reversed ? curr->numTermArguments()-i-1 : i;
      TermList arg = curr->termArg(j);
      // if current argument does not contain rwTerm, continue
      if (arg.isVar() || !arg.containsSubterm(TermList(rwTerm))) {
        continue;
      }
      // check indices are valid
      ASS(!currO->hasMain() || (reversed ? currO->main() >= j : currO->main() <= j));
      // add index as main
      ALWAYS(currN->mains.insert(j).second);
      // if arg is actually rwTerm, return
      if (arg.term() == rwTerm) {
        return res;
      }
      // otherwise try to find the node for this arg 
      auto node = currO->indices.findPtr(j);
      if (node) {
        // node exists
        curr = arg.term();
        currO = *node;
        currS = currO->hasMain() ? currO->getRef() : &currO->getOwn();
        auto ext = new Node(currS);
        ALWAYS(currN->indices.insert(j, ext));
        currN = ext;
        // if the node is active, we recurse, otherwise we have to extend
        if (currS->active) {
          break;
        }
      } else {
        // this hack is needed because buildTree adds the index again
        ASS(currN->hasMain());
        currN->mains.clear();
      }
      // extend tree from last available node
      buildTree(currO, currN, curr, rwTerm);
      return res;
    }
  }
  ASSERTION_VIOLATION;
}

RewritingPositionTree* RewritingPositionTree::create(RewritingPositionTree* other)
{
  CALL("RewritingPositionTree::create");
  TIME_TRACE("rewriting position tree maintenance");

  if (!other) {
    return nullptr;
  }
  return other->create();
}

RewritingPositionTree* RewritingPositionTree::create()
{
  CALL("RewritingPositionTree::create");
  ASS(_root);
  if (_root->mains.empty()) {
    return nullptr;
  }
  auto res = new RewritingPositionTree(new Node(_root->getRef()));
  Stack<pair<Node*,Node*>> todo;
  todo.push(make_pair(_root, res->_root));

  while (todo.isNonEmpty()) {
    auto tp = todo.pop();
    auto cO = tp.first;
    auto cN = tp.second;
    ASS(!cO->mains.empty());
    for (const auto& i : cO->mains) {
      ALWAYS(cN->mains.insert(i).second);
      auto nextP = cO->indices.findPtr(i);
      if (!nextP || (*nextP)->mains.empty()) {
        continue;
      }
      auto nextN = new Node((*nextP)->getRef());
      ALWAYS(cN->indices.insert(i, nextN));

      todo.push(make_pair((*nextP), nextN));
    }
  }
  return res;
}

RewritingPositionTree* RewritingPositionTree::createTruncated(RewritingPositionTree* old, TermList term, TermList rwTerm)
{
  CALL("RewritingPositionTree::createTruncated");
  TIME_TRACE("rewriting position tree maintenance");
  ASS(rwTerm.isTerm());

  if (!old || term.isVar()) {
    return nullptr;
  }
  return old->createTruncated(term.term(), rwTerm.term());
}

RewritingPositionTree* RewritingPositionTree::createTruncated(Term* term, Term* rwTerm)
{
  CALL("RewritingPositionTree::createTruncated");
  ASS(_root);
  // cout << "adjust " << *term << " " << *rwTerm << " " << toString() << endl;
  if (term == rwTerm || _root->mains.empty()) {
    // I'm not sure about this, return instead null
    // return rhsPosition;
    return nullptr;
  }
  auto res = new RewritingPositionTree(new Node(_root->getRef()));
  Stack<tuple<Term*,Node*,Node*>> todo;
  todo.push(make_tuple(term, _root, res->_root));

  while (todo.isNonEmpty()) {
    auto tp = todo.pop();
    auto cT = get<0>(tp);
    auto cO = get<1>(tp);
    auto cN = get<2>(tp);
    ASS(!cO->mains.empty());
    for (const auto& i : cO->mains) {
      auto arg = cT->termArg(i);
      ALWAYS(cN->mains.insert(i).second);
      if (arg.isVar() || arg.term() == rwTerm) {
        continue;
      }
      auto nextP = cO->indices.findPtr(i);
      if (!nextP || (*nextP)->mains.empty()) {
        continue;
      }
      auto nextN = new Node((*nextP)->getRef());
      ALWAYS(cN->indices.insert(i, nextN));

      todo.push(make_tuple(arg.term(), (*nextP), nextN));
    }
  }
  return res;
}

void RewritingPositionTree::buildTree(Node*& oldRoot, Node*& newRoot, Term* term, Term* rwTerm)
{
  CALL("RewritingPositionTree::buildTree");
  ASS_NEQ(term, rwTerm);
  Stack<tuple<Term*,Node*,Node*>> todo;
  todo.push(make_tuple(term, oldRoot, newRoot));

  while (todo.isNonEmpty()) {
    auto tp = todo.pop();
    auto cT = get<0>(tp);
    auto cO = get<1>(tp);
    auto cN = get<2>(tp);

    auto arity = cT->numTermArguments();
    ASS(cT->containsSubterm(TermList(rwTerm)));
    for (unsigned i = 0; i < arity; i++) {
      auto arg = cT->termArg(i);
      if (arg.isVar() || !arg.term()->containsSubterm(TermList(rwTerm))) {
        continue;
      }
      ALWAYS(cN->mains.insert(i).second);
      if (arg.term() == rwTerm) {
        continue;
      }

      // no such node in current tree, extend it
      auto nextP = cO->indices.findPtr(i);
      Node* nextO;
      if (nextP) {
        nextO = *nextP;
        ASS(!nextO->getOwn().active);
      } else {
        nextO = new Node(nullptr); // owns
        nextO->getOwn().active = false;
        ALWAYS(cO->indices.insert(i, nextO));
      }

      // add to new tree
      auto nextN = new Node(&nextO->getOwn());
      ALWAYS(cN->indices.insert(i, nextN));

      todo.push(make_tuple(arg.term(), nextO, nextN));
    }
  }
}

TermIterator RewritingPositionTree::getSubtermIterator(RewritingPositionTree* old, TermList term)
{
  CALL("static RewritingPositionTree::getSubtermIterator");
  TIME_TRACE("rewriting position tree maintenance");
  if (term.isVar()) {
    return TermIterator::getEmpty();
  }

  if (!old) {
    return vi(new NonVariableNonTypeIterator(term.term(), !term.term()->isLiteral()));
  }
  if (!old->_active) {
    old->activate(term.term());
  }
  ASS(old->_active);
  return old->getSubtermIterator(term.term());
}

TermIterator RewritingPositionTree::getSubtermIterator(Term* term)
{
  CALL("RewritingPositionTree::getSubtermIterator");
  // add term itself if not literal
  auto res = term->isLiteral()
    ? TermIterator::getEmpty()
    : pvi(getSingletonIterator(TermList(term)));
  auto curr = term;
  auto currN = _root;
  DHSet<TermList> excluded;
  ASS(_active);

  while (currN) {
    if (!currN->hasMain()) {
      break;
    }
    auto index = currN->main();
    ASS(currN->getRef()->active);
    bool reversed = currN->getRef()->reversed;
    ASS_L(index, curr->numTermArguments());

    unsigned exci = reversed ? index+1 : 0;
    unsigned excj = reversed ? curr->numTermArguments() : index;
    unsigned inci = reversed ? 0 : index+1;
    unsigned incj = reversed ? index : curr->numTermArguments();

    // update excluded
    for (unsigned i = exci; i < excj; i++) {
      auto arg = curr->termArg(i);
      if (arg.isVar()) {
        continue;
      }
      excluded.loadFromIterator(NonVariableNonTypeIterator(arg.term(), true));
    }

    // add possible rewritable terms
    for (unsigned i = inci; i < incj; i++) {
      auto arg = curr->termArg(i);
      if (arg.isVar()) {
        continue;
      }
      res = pvi(getConcatenatedIterator(res, vi(new NonVariableNonTypeIterator(arg.term(), true))));
    }
    auto next = curr->termArg(index);
    if (next.isVar()) {
      break;
    }
    res = pvi(getConcatenatedIterator(res, getSingletonIterator(next)));
    curr = next.term();
    auto nextN = currN->indices.findPtr(index);
    if (!nextN) {
      break;
    }
    currN = *nextN;
  }
  res = pvi(getConcatenatedIterator(res, vi(new NonVariableNonTypeIterator(curr, false))));

  return pvi(iterTraits(res)
    .filter([excluded = std::move(excluded)](TermList t) {
      return !excluded.contains(t);
    }));
}

bool RewritingPositionTree::isExcluded(RewritingPositionTree* tree, TermList term, TermList rwTerm)
{
  CALL("static RewritingPositionTree::isExcluded");
  TIME_TRACE("rewriting position tree maintenance");
  ASS(rwTerm.isTerm());

  if (term.isVar() || !tree) {
    return false;
  }

  if (!tree->_active) {
    tree->activate(term.term());
  }
  ASS(tree->_active);
  return tree->isExcluded(term.term(), rwTerm.term());
}

bool RewritingPositionTree::isExcluded(Term* term, Term* rwTerm)
{
  CALL("RewritingPositionTree::isExcluded");
  // add term itself if not literal
  auto res = term->isLiteral()
    ? TermIterator::getEmpty()
    : pvi(getSingletonIterator(TermList(term)));
  auto curr = term;
  auto currN = _root;

  while (currN) {
    if (curr == rwTerm || !currN->hasMain()) {
      break;
    }
    auto index = currN->main();
    ASS(currN->getRef()->active);
    bool reversed = currN->getRef()->reversed;
    ASS_L(index, curr->numTermArguments());

    unsigned exci = reversed ? index+1 : 0;
    unsigned excj = reversed ? curr->numTermArguments() : index;

    for (unsigned i = exci; i < excj; i++) {
      auto arg = curr->termArg(i);
      if (arg.containsSubterm(TermList(rwTerm))) {
        return true;
      }
    }

    auto next = curr->termArg(index);
    if (next.isVar()) {
      break;
    }
    curr = next.term();
    auto nextN = currN->indices.findPtr(index);
    if (!nextN) {
      break;
    }
    currN = *nextN;
  }
  return false;
}

void RewritingPositionTree::activate(RewritingPositionTree* tree, TermList term)
{
  CALL("static RewritingPositionTree::activate");
  TIME_TRACE("rewriting position tree maintenance");

  if (term.isVar() || !tree) {
    ASS(!tree);
    return;
  }

  ASS(!tree->_active);
  tree->activate(term.term());
}

void RewritingPositionTree::activate(Term* term)
{
  CALL("RewritingPositionTree::activate");
  if (_active) {
    return;
  }
  auto curr = term;
  auto currN = _root;
  // cout << "activate " << *term << " " << toString() << endl;

  while (currN) {
    // update state
    auto ref = currN->getRef();
    if (!ref->active) {
      // this is the main "heuristic"
      if (currN->mains.count(curr->numTermArguments()-1)) {
        ref->reversed = true;
      }
      ref->active = true;
      // cout << "activating " << ref << " " << *term << endl;
    }

    // remove unneeded stuff
    ASS_GE(currN->mains.size(),1);
    for (unsigned i = 0; i < curr->numTermArguments(); i++) {
      auto j = ref->reversed ? curr->numTermArguments()-i-1 : i;
      if (!currN->mains.count(j)) {
        continue;
      }
      decltype(currN->indices)::DelIterator it(currN->indices);
      Node* next = nullptr;
      while (it.hasNext()) {
        Node* n;
        unsigned index;
        it.next(index,n);
        if (index == j) {
          next = n;
        } else {
          destroy(n);
          it.del();
        }
      }
      currN->mains = { j };
      auto arg = curr->termArg(j);
      currN = next;
      if (arg.isVar()) {
        ASS(!next);
      } else {
        curr = arg.term();
      }
      break;
    }
  }
  _active = true;
}

bool RewritingPositionTree::isValid(TermList term) const
{
  CALL("RewritingPositionTree::isValid");
  if (term.isVar()) {
    return !_root;
  }
  auto curr = term.term();
  auto currN = _root;

  while (currN) {
    if (!currN->hasMain()) {
      break;
    }
    auto index = currN->main();
    if (index >= curr->numTermArguments()) {
      return false;
    }
    auto nextN = currN->indices.findPtr(index);
    if (!nextN) {
      break;
    }
    auto next = curr->termArg(index);
    if (!next.isTerm()) {
      return false;
    }
    curr = next.term();
    currN = *nextN;
  }
  return true;
}

vstring RewritingPositionTree::toString() const
{
  CALL("RewritingPositionTree::toString");
  vstring res;
  res += _active ? "[a]" : "[n]";
  auto currN = _root;

  while (currN) {
    if (!currN->hasMain()) {
      res += "[e" + Int::toString(currN->mains.size()) + "]";
      break;
    }
    auto index = currN->main();
    if (currN->getRef()->active) {
      vstringstream str;
      str << currN->getRef();
      res += str.str();
      res += currN->getRef()->reversed ? "[<-]" : "[->]";
    } else {
      res += "[?]";
    }
    res += Int::toString(index+1);
    auto nextN = currN->indices.findPtr(index);
    if (!nextN) {
      break;
    }
    res += ".";
    currN = *nextN;
  }
  return res;
}

void RewritingPositionTree::destroy(Node* n)
{
  CALL("RewritingPositionTree::destroy");

  Stack<Node*> todo { n };
  while (todo.isNonEmpty()) {
    auto curr = todo.pop();
    DHMap<unsigned, Node*>::Iterator it(curr->indices);
    while (it.hasNext()) {
      todo.push(it.next());
    }
    delete curr;
  }
}

}