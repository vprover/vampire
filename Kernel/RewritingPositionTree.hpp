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
 * @file RewritingPositionTree.hpp

 * Defines class RewritingPositionTree.
 */

#ifndef __RewritingPositionTree__
#define __RewritingPositionTree__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/STL.hpp"

#define DEBUG_PSBS 0

namespace Kernel {

class RewritingPositionTree
{
private:
  struct State {
    bool active;
    bool reversed;
  };
  using Path = Stack<pair<unsigned,State*>>;

  struct Node
  {
    CLASS_NAME(Node);
    USE_ALLOCATOR(Node);
    Node(State* s) : ref(s) {}
    // Node(unsigned m, State* s) : mains({m}), own(), ref(s) { /* state.ref = s; */ }
    unsigned main() const { ASS_EQ(mains.size(),1); return *mains.begin(); }
    bool hasMain() const { return mains.size()==1; }

    vset<unsigned> mains;
    DHMap<unsigned, Node*> indices;
    State& getOwn() { ASS(!ref); return own; }
    State* getRef() { ASS(ref); return ref; }
  private:
    //TODO turn these into a union once errors are eliminated
    State own;
    State* ref = nullptr;
    // union {
    //   State own;
    //   State* ref;
    //   unsigned debug;
    // } state;
  };

public:
  CLASS_NAME(RewritingPositionTree);
  USE_ALLOCATOR(RewritingPositionTree);

  RewritingPositionTree(Node* root) : _root(root), _active(false) {}

  static RewritingPositionTree* create(RewritingPositionTree* other);
  static RewritingPositionTree* createFromRewrite(RewritingPositionTree*& old, TermList term, TermList rwTerm, RewritingPositionTree* rhs);
  static RewritingPositionTree* createTruncated(RewritingPositionTree* old, TermList term, TermList rwTerm);
  static VirtualIterator<Term*> getSubtermIterator(RewritingPositionTree* tree, TermList term);
  static bool isExcluded(RewritingPositionTree* tree, TermList term, TermList rwTerm);
  static void activate(RewritingPositionTree* tree, TermList term);

  bool isValid(TermList t) const;
  vstring toString() const;

private:
  RewritingPositionTree* create();
  RewritingPositionTree* createTruncated(Term* term, Term* rwTerm);
  RewritingPositionTree* createFromRewrite(Term* term, Term* rwTerm, const Path& rhsPath);
  VirtualIterator<Term*> getSubtermIterator(Term* term);
  bool isExcluded(Term* term, Term* rwTerm);
  void activate(Term* term);
  static void buildTree(Node*& oldRoot, Node*& newRoot, Term* term, Term* rwTerm);
  static Path extractPath(RewritingPositionTree* tree);
  static void destroy(Node* n);

  Node* _root;
  bool _active;
};

};

#endif /* __RewritingPositionTree__ */
