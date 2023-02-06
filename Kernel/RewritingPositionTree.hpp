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

#define DEBUG_PSBS 0

namespace Kernel {

class RewritingPositionTree
{
private:
  struct Node
  {
    CLASS_NAME(Node);
    USE_ALLOCATOR(Node);
    Node() = default;
    Node(unsigned m, bool r) : main(m), reversed(r) {}

    int main = -1;
    DHMap<unsigned, Node*> indices;
    bool reversed = false;
  };

public:
  CLASS_NAME(RewritingPositionTree);
  USE_ALLOCATOR(RewritingPositionTree);

  RewritingPositionTree(Node* root) : _root(root) {}

  static RewritingPositionTree* create(RewritingPositionTree* other);
  static RewritingPositionTree* createFromRewrite(RewritingPositionTree*& old, TermList term, TermList rwTerm, RewritingPositionTree* rhs);
  static RewritingPositionTree* createTruncated(RewritingPositionTree* old, TermList term, TermList rwTerm);
  static TermIterator getSubtermIterator(RewritingPositionTree* old, TermList term, DHSet<TermList>& excluded);

  bool isValid(TermList t) const;
  vstring toString() const;

private:
  RewritingPositionTree* createTruncated(Term* term, Term* rwTerm);
  RewritingPositionTree* createFromRewrite(Term* term, Term* rwTerm, const Stack<pair<unsigned,bool>>& rhsPath);
  TermIterator getSubtermIterator(Term* term, DHSet<TermList>& excluded);
  static RewritingPositionTree* create(const Stack<pair<unsigned,bool>>& path);
  static void assignNewPath(Stack<pair<unsigned,bool>>& path, Node* n, Term* term, Term* rwTerm);
  static Stack<pair<unsigned,bool>> extractPath(RewritingPositionTree* tree);

  Node* _root;
};

};

#endif /* __RewritingPositionTree__ */
