#include "VariablePrenexOrderingTree.hpp"
#include <algorithm>
#include <string>
#include <sstream>

bool VariablePrenexOrderingTree::VariableOrderingTreeNode::percolate(VariablePrenexOrderingTree::VariableOrderingTreeNode::ParentDirection dir)
{
  bool changed = false;
  if (rightChild) {
    changed |= rightChild->percolate(dir);
  }
  if (leftChild) {
    changed |= leftChild->percolate(dir);
  }
  if (!parent) {
    return changed;
  }
  if (direction == dir) {
    for (auto x : containedVariablesOrder) {
      auto test = parent->containedVariables.find(x);
      if (test == parent->containedVariables.end()) {
        changed = true;
        parent->containedVariables.insert(x);
        parent->containedVariablesOrder.push_back(x);
      }
    }
  }
  return changed;
}

void VariablePrenexOrderingTree::VariableOrderingTreeNode::print(std::ostream &out)
{
  // Rotated tree printer: root at left, children to the right.
  std::function<void(const VariableOrderingTreeNode*, const std::string&, bool, bool)> printNode;

  printNode = [&](const VariableOrderingTreeNode* node, const std::string& prefix, bool isLeft, bool isRoot){
    if(!node) return;

    // build label
    std::ostringstream lbl;
    lbl << "[";
    for (size_t i = 0; i < node->containedVariablesOrder.size(); ++i) {
      if (i) lbl << " ";
      lbl << node->containedVariablesOrder[i];
    }
    lbl << "]";

    if (isRoot) {
      out << lbl.str() << "\n";
    } else {
      out << prefix << (isLeft ? "├── " : "└── ") << lbl.str() << "\n";
    }

    std::string childPrefix = prefix + (isLeft ? "│   " : "    ");

    // print left then right to have "top" = left child, "bottom" = right child
    if (node->leftChild) {
      printNode(node->leftChild.get(), childPrefix, true, false);
    }
    if (node->rightChild) {
      printNode(node->rightChild.get(), childPrefix, false, false);
    }
  };

  printNode(this, std::string(), true, true);
}

std::unique_ptr<VariablePrenexOrderingTree::VariableOrderingTreeNode> VariablePrenexOrderingTree::VariableOrderingTreeNode::buildTreeFromFormula(Formula *f, Connective recordedConnective)
{
  switch (f->connective()) {
    case AND:
    case OR: {
      auto args = f->args()->iter();
      std::vector<std::unique_ptr<VariableOrderingTreeNode>> trees;
      while (args.hasNext()) {
        trees.push_back(buildTreeFromFormula(args.next(), recordedConnective));
      }
      if (trees.empty()) {
        return std::unique_ptr<VariableOrderingTreeNode>(new VariableOrderingTreeNode());
      }
      if (trees.size() == 1) {
        return std::move(trees[0]);
      }
      // fold the argument trees into a binary tree
      std::unique_ptr<VariableOrderingTreeNode> node = std::move(trees[0]);
      for (size_t i = 1; i < trees.size(); ++i) {
        std::unique_ptr<VariableOrderingTreeNode> parent(new VariableOrderingTreeNode());
        parent->rightChild = std::move(node);
        parent->rightChild->parent = parent.get();
        parent->rightChild->direction = RIGHT;
        parent->leftChild = std::move(trees[i]);
        parent->leftChild->parent = parent.get();
        parent->leftChild->direction = LEFT;
        node = std::move(parent);
      }
      ASS(node->leftChild->parent == node.get())
      ASS(node->rightChild->parent == node.get())
      return node;
    }
    case IMP:
    case IFF:
    case XOR: {
      std::unique_ptr<VariableOrderingTreeNode> connectiveNode(new VariableOrderingTreeNode());
      auto left = buildTreeFromFormula(f->left(), recordedConnective);
      auto right = buildTreeFromFormula(f->right(), recordedConnective);
      left->direction = LEFT;
      right->direction = RIGHT;
      connectiveNode->leftChild = std::move(left);
      connectiveNode->leftChild->parent = connectiveNode.get();
      connectiveNode->rightChild = std::move(right);
      connectiveNode->rightChild->parent = connectiveNode.get();
      ASS(connectiveNode->leftChild->parent == connectiveNode.get())
      ASS(connectiveNode->rightChild->parent == connectiveNode.get())
      return connectiveNode;
      break;
    }
    case NOT: {
      return buildTreeFromFormula(f->uarg(), recordedConnective);
    }
    case FORALL:
    case EXISTS: {
      auto found = buildTreeFromFormula(f->qarg(), recordedConnective);
      if (f->connective() == recordedConnective) {
        VList::Iterator vs(f->vars());
        // SList::Iterator ss(f->sorts());
        while (vs.hasNext()) {
          unsigned var = vs.next();
          found->containedVariables.insert(var);
          found->containedVariablesOrder.push_back(var);
        }
        std::sort(found->containedVariablesOrder.begin(), found->containedVariablesOrder.end());
      }
      return found;
    }
    case LITERAL:
    case BOOL_TERM:
    case TRUE:
    case FALSE:
    default:
      return std::unique_ptr<VariableOrderingTreeNode>(new VariableOrderingTreeNode());
  }
  ASSERTION_VIOLATION;
}

void VariablePrenexOrderingTree::print(std::ostream &out)
{
  root->print(out);
}

void VariablePrenexOrderingTree::buildTreeFromFormula(Formula *f, Connective recordedConnective)
{
  root = VariableOrderingTreeNode::buildTreeFromFormula(f, recordedConnective);
}

std::vector<unsigned> *VariablePrenexOrderingTree::determineVariableOrdering()
{
  
  if (!treeHasBeenShaken) {
    //root->print(std::cout);
    //std::cout << "----\n\n";
    bool changing;
    do {
      changing = false;
      changing |= root->percolate(VariableOrderingTreeNode::LEFT);
      //root->print(std::cout);
      //std::cout << "----\n\n";
      changing |= root->percolate(VariableOrderingTreeNode::RIGHT);
      //root->print(std::cout);
      //std::cout << "----\n\n";
    } while (changing);
    treeHasBeenShaken = true;
  }
  return &root->containedVariablesOrder;
}
