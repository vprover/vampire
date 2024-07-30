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
 * @file ConfluenceTree.hpp
 */

#ifndef __ConfluenceTree__
#define __ConfluenceTree__

#include "Forwards.hpp"

#include "VarOrder.hpp"

namespace Kernel {

using namespace Lib;

class ConfluenceTree
{
public:
  ~ConfluenceTree()
  {
    deleteNode(root);
  }

  void add(const VarOrder& vo) {
    auto tr = vo.transitive_reduction();
    // the location where we should add new nodes
    Node** prevPtr = &root;
    DHSet<Edge> done;
    auto curr = root;
    while (curr) {
      if (curr->success) {
        // entirely covered, we can return
        return;
      }
      auto c = vo.query(curr->x, curr->y);
      auto i = Node::branchIndex(c);
      if (c != PoComp::INCOMPARABLE) {
        Edge e;
        e.c = c;
        e.x = curr->x;
        e.y = curr->y;
        done.insert(e);

        e.c = Ordering::reverse(c);
        e.x = curr->y;
        e.y = curr->x;
        done.insert(e);
      }
      prevPtr = &curr->branches[i];
      curr = curr->branches[i];
    }

    while (tr) {
      auto edge = tr->head();
      if (done.contains(edge)) {
        tr = tr->tail();
        continue;
      } 
      auto curr = new Node();
      curr->x = edge.x;
      curr->y = edge.y;

      *prevPtr = curr;
      prevPtr = &curr->branches[Node::branchIndex(edge.c)];
      tr = tr->tail();
    }
    auto successNode = new Node();
    successNode->success = true;
    *prevPtr = successNode;
  }

  bool evaluate(const Ordering* ord, const SubstApplicator* applicator) const
  {
    auto curr = root;
    while (curr) {
      if (curr->success) {
        return true;
      }
      auto comp = ord->compare(AppliedTerm(TermList::var(curr->x), applicator, true), AppliedTerm(TermList::var(curr->y), applicator, true));
      curr = curr->branches[Node::branchIndex(comp)];
    }
    return false;
  }

  std::string toString() const
  {
    std::string res;
    Stack<std::tuple<Node*,PoComp,unsigned>> todo;
    todo.push(std::make_tuple(root,PoComp::INCOMPARABLE,0));

    while (todo.isNonEmpty()) {
      auto [curr,branch,depth] = todo.pop();
      std::stringstream str;
      for (unsigned i = 0; i < depth; i++) {
        str << "  ";
      }
      str << Ordering::resultToStringInfix(branch) << " ";
      if (!curr) {
        str << "fail";
      } else if (curr->success) {
        str << "success";
      } else {
        str << "compare " << curr->x << " " << curr->y;
        todo.push(std::make_tuple(curr->branches[3],PoComp::INCOMPARABLE,depth+1));
        todo.push(std::make_tuple(curr->branches[2],PoComp::EQUAL,depth+1));
        todo.push(std::make_tuple(curr->branches[1],PoComp::LESS,depth+1));
        todo.push(std::make_tuple(curr->branches[0],PoComp::GREATER,depth+1));
      }
      str << std::endl;
      res += str.str();
    }
    return res;
  }

private:
  struct Node {
    bool success = false;
    unsigned x;
    unsigned y;
    Node* branches[4];

    static unsigned branchIndex(PoComp c) {
      return static_cast<unsigned>(c)-1;
    }
  };

  static void deleteNode(Node* n) {
    Stack<Node*> todo;
    todo.push(n);
    while (todo.isNonEmpty()) {
      auto curr = todo.pop();
      if (!curr) {
        continue;
      }
      todo.push(curr->branches[0]);
      todo.push(curr->branches[1]);
      todo.push(curr->branches[2]);
      todo.push(curr->branches[3]);
      delete curr;
    }
  }

  Node* root = nullptr;
};

}
#endif
