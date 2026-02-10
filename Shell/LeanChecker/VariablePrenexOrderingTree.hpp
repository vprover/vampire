#include "Forwards.hpp"
#include "Forwards.hpp"
#include "Kernel/Formula.hpp"
#include <memory>
#include <set>
#include <vector>
#include <ostream>

/**
  * VariablePrenexOrderingTree.hpp
  *
  * When a formula is prenexed using simplification rules in lean checker,
  * the order of the variables in the quantifier prefix depends on the structure of the formula.
  * The rules applied are e.g.: ! [X] A(X) \/ B -> ! [X] (A(X) \/ B) or
  * A \/ ! [X] B -> ! [X] (A \/ B(X)) and 
  * where the order is important. This class builds a tree representing the structure of the formula
  * and then determines a variable ordering for the prenex quantifier prefix.
  * It assumes that the formula is always simplified first with a "left" rule until no more left rules apply,
  * and then with "right" rules until no more right rules apply. (Until fixpoint).
 */

class VariablePrenexOrderingTree {
  class VariableOrderingTreeNode {
  public:
    enum ParentDirection {
      LEFT = 0,
      RIGHT
    };

  private:
    VariableOrderingTreeNode* parent;
    ParentDirection direction;
    std::unique_ptr<VariableOrderingTreeNode> leftChild;
    std::unique_ptr<VariableOrderingTreeNode> rightChild;
    std::set<unsigned int> containedVariables;

  public:
    std::vector<unsigned int> containedVariablesOrder;

    bool percolate(ParentDirection dir);
    void print(std::ostream &out);
    static std::unique_ptr<VariableOrderingTreeNode> buildTreeFromFormula(Formula *f, Connective recordedConnective);
  };

  std::unique_ptr<VariableOrderingTreeNode> root;
  bool treeHasBeenShaken = false;

public:
  void print(std::ostream &out);
  void buildTreeFromFormula(Formula *f, Connective recordedConnective);
  std::vector<unsigned> *determineVariableOrdering();
};