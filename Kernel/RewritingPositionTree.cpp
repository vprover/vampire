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

RewritingPositionTree* RewritingPositionTree::create(const Path& path)
{
  CALL("static RewritingPositionTree::create");
  if (path.isEmpty()) {
    return nullptr;
  }
  auto res = new RewritingPositionTree(new Node(path[0].first, path[0].second));
  Node* curr = res->_root;

  for (unsigned i = 1; i < path.size(); i++) {
    auto next = new Node(path[i].first, path[i].second);
    curr->indices.insert(curr->main, next);
    curr = next;
  }
  return res;
}

RewritingPositionTree::Path RewritingPositionTree::extractPath(RewritingPositionTree* tree)
{
  CALL("static RewritingPositionTree::extractPath");
  Path path;
  if (!tree) {
    return path;
  }
  Node* curr = tree->_root;
  while (curr) {
    path.push(make_pair(curr->main, curr->reversed));
    if (curr->main < 0) {
      break;
    }
    auto next = curr->indices.findPtr(curr->main);
    if (!next) {
      break;
    }
    curr = *next;
  }
  return path;
}

RewritingPositionTree* RewritingPositionTree::create(RewritingPositionTree* other)
{
  CALL("static RewritingPositionTree::create(RewritingPositionTree*)");
  TIME_TRACE("rewriting position tree maintenance");
  return create(extractPath(other));
}

RewritingPositionTree* RewritingPositionTree::createFromRewrite(RewritingPositionTree*& old, TermList term, TermList rwTerm, RewritingPositionTree* rhs)
{
  CALL("static RewritingPositionTree::createNewFromRewrite");
  TIME_TRACE("rewriting position tree maintenance");
  ASS(term.isTerm());
  ASS(rwTerm.isTerm());
  ASS(term.containsSubterm(rwTerm));

  auto rhsPath = extractPath(rhs);
  if (term == rwTerm) {
    return create(rhsPath);
  }

  if (!old) {
    auto ext = new Node();
    Path path;
    assignNewPath(path, ext, term.term(), rwTerm.term());
    old = new RewritingPositionTree(ext);
    path.loadFromIterator(Path::BottomFirstIterator(rhsPath));
    return create(path);
  }
  ASS(old->_root);
  return old->createFromRewrite(term.term(), rwTerm.term(), rhsPath);
}

RewritingPositionTree* RewritingPositionTree::createFromRewrite(Term* term, Term* rwTerm, const Path& rhsPath)
{
  CALL("RewritingPositionTree::createNewFromRewrite");
  // cout << "createNewFromRewrite " << *term << " " << *rwTerm << endl;
  Term* curr = term;
  Node* currN = _root;
  Path path;

  while (curr) {
    // TODO it suffices to start from main
    for (unsigned i = 0; i < curr->numTermArguments(); i++) {
      auto j = currN->reversed ? curr->numTermArguments()-i-1 : i;
      TermList t = curr->termArg(j);
      if (t.isVar() || !t.containsSubterm(TermList(rwTerm))) {
        continue;
      }
      path.push(make_pair(j, currN->reversed));
      if (t.term() == rwTerm) {
        path.loadFromIterator(Path::BottomFirstIterator(rhsPath));
        return create(path);
      }
      // cout << positionToString(cp) << endl;
      auto node = currN->indices.findPtr(j);
      if (node) {
        // find in node
        curr = t.term();
        currN = *node;
        break;
      }
      // extend tree
      auto ext = new Node();
      currN->indices.insert(j, ext);
      assignNewPath(path, ext, t.term(), rwTerm);
      path.loadFromIterator(Path::BottomFirstIterator(rhsPath));
      return create(path);
    }
  }
  ASSERTION_VIOLATION;
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
  if (term == rwTerm) {
    // I'm not sure about this, return instead null
    // return rhsPosition;
    return nullptr;
  }
  auto curr = term;
  auto currN = _root;
  Path path;

  while (currN) {
    path.push(make_pair(currN->main, currN->reversed));
    auto index = currN->main;
    // cout << "iter adjust " << *curr << " " << index << endl;
    // check if some argument is rewritten
    if (index < 0) {
      break;
    }
    ASS_L(index,curr->numTermArguments());
    // check if there is a next node
    auto nextN = currN->indices.findPtr(index);
    if (!nextN) {
      break;
    }
    // if there is a next node, the argument should be a term
    auto t = curr->termArg(index);
    ASS(t.isTerm());
    curr = t.term();
    // cout << "CURR " << curr << endl;
    if (curr == rwTerm) {
      break;
    }
    // if currently rewritten and next term are not the same,
    // we can extend the new tree further
    currN = *nextN;
  }
  return create(path);
}

void RewritingPositionTree::assignNewPath(Path& path, Node* n, Term* term, Term* rwTerm)
{
  CALL("RewritingPositionTree::assignNewPath");
  ASS(n);
  ASS_NEQ(term, rwTerm);
  auto curr = term;
  auto currN = n;

  while (curr) {
    // cout << *curr << " " << *rwTerm << endl;
    auto arity = curr->numTermArguments();
    ASS(curr->containsSubterm(TermList(rwTerm)));
    for (unsigned i = 0; i < arity; i++) {
      auto arg = curr->termArg(i);
      // cout << i << " " << arity << " " << arg << endl;
      if (!arg.containsSubterm(TermList(rwTerm))) {
        continue;
      }

      if (i == arity-1) {
        currN->reversed = true;
      }
      curr = arg.term();
      path.push(make_pair(i,currN->reversed));
      if (curr == rwTerm) {
        return;
      }
      auto ext = new Node();
      currN->indices.insert(i,ext);
      currN = ext;
      break;
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
    ASS(!term.term()->isLiteral());
    return vi(new NonVariableNonTypeIterator(term.term(), true));
  }
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

  while (currN) {
    auto index = currN->main;
    if (index < 0) {
      break;
    }
    bool reversed = currN->reversed;
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
  DHSet<TermList> excluded;

  while (currN) {
    if (curr == rwTerm) {
      break;
    }
    auto index = currN->main;
    if (index < 0) {
      break;
    }
    bool reversed = currN->reversed;
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

bool RewritingPositionTree::isValid(TermList term) const
{
  CALL("RewritingPositionTree::checkValid");
  if (term.isVar()) {
    return !_root;
  }
  auto curr = term.term();
  auto currN = _root;

  while (currN) {
    auto index = currN->main;
    if (index < 0) {
      break;
    }
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
  vstring res;
  auto currN = _root;

  while (currN) {
    auto index = currN->main;
    if (index < 0) {
      break;
    }
    res += currN->reversed ? "[<-]" : "[->]";
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

}