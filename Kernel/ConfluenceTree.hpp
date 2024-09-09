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

  void add(const VarOrder* vo) {
    // the location where we should add new nodes
    struct State {
      const VarOrder* toAdd;
      const VarOrder* prefix;
      Node* node;
      Node* prev;
      unsigned prevIndex;
    };

    Stack<State> todo;
    todo.push({ vo, VarOrder::get_empty(), root, nullptr, 0 });

    while (todo.isNonEmpty()) {
      auto st = todo.pop();

      if (!st.node) {
        // insert here
        DHSet<Edge> done;
        auto prevTr = st.prefix->transitive_reduction();
        while (prevTr) {
          done.insert(prevTr->head());
          prevTr = prevTr->tail();
        }
        auto tr = st.toAdd->transitive_reduction();
        while (tr) {
          auto edge = tr->head();
          if (done.contains(edge)) {
            tr = tr->tail();
            continue;
          }
          auto curr = new Node();
          curr->x = edge.x;
          curr->y = edge.y;
          st.prefix = VarOrder::add_edge(st.prefix,edge);

          if (st.prev) {
            st.prev->branches[st.prevIndex] = curr;
          } else {
            root = curr;
          }
          st.prev = curr;
          st.prevIndex = Node::branchIndex(edge.c);
          tr = tr->tail();
        }
        auto successNode = new Node();
        successNode->success = true;
        st.prev->branches[st.prevIndex] = successNode;
        continue;
      }

      if (st.node->success) {
        // this branch is covered, done
        continue;
      }
      auto c = st.toAdd->query(st.node->x, st.node->y);
      // check if we intersect with current node
      if (c != PoComp::INCOMPARABLE) {
        auto i = Node::branchIndex(c);
        auto prefix = VarOrder::add_edge(st.prefix,Edge{st.node->x,st.node->y,c});
        todo.push({ st.toAdd, prefix, st.node->branches[i], st.node, i });
      } else {
        { // GREATER
          auto ext = VarOrder::add_gt(st.toAdd, st.node->x, st.node->y);
          auto prefix = VarOrder::add_gt(st.prefix, st.node->x, st.node->y);
          if (ext) {
            todo.push({ ext, prefix, st.node->branches[0], st.node, 0 });
          }
        }
        { // LESS
          auto ext = VarOrder::add_gt(st.toAdd, st.node->y, st.node->x);
          auto prefix = VarOrder::add_gt(st.prefix, st.node->y, st.node->x);
          if (ext) {
            todo.push({ ext, prefix, st.node->branches[1], st.node, 1 });
          }
        }
        { // EQUAL
          auto ext = VarOrder::add_eq(st.toAdd, st.node->x, st.node->y);
          auto prefix = VarOrder::add_eq(st.prefix, st.node->x, st.node->y);
          if (ext) {
            todo.push({ ext, prefix, st.node->branches[2], st.node, 2 });
          }
        }
        { // INCOMPARABLE
          todo.push({ st.toAdd, st.prefix, st.node->branches[3], st.node, 3 });
        }
      }
    }
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
