/**
 * @file SimpleSMT.hpp
 * Defines class SimpleSMT.
 */

#ifndef __SimpleSMT__
#define __SimpleSMT__

//# We group includes by their namespace, inside the groups they may be alphabetically sorted
//# but this I often don't follow myself

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "SAT/SATLiteral.hpp"
#include "Lib/Numbering.hpp"


namespace VUtils {

//## we don't indent the inside of a namespace (doesn't make sense as almost everything is inside a namespace)

  using namespace Kernel;
  using namespace Shell;
  using namespace SAT;

  //## typedefs that are local to a class should be made as private inside
  //## the class, not outside
  typedef Numbering<Literal *, 1 > TwoWayMap;

  class SimpleSMT {
  public:
    int perform(int argc, char** argv);
  protected:
    //# redundant namespace, SATLiteral would be enough
    SAT::SATLiteral litTOSAT(Literal *l);
    void initializeSATSolver(ClauseIterator clite);
    //## Returning stack by value can get expensive as everything will be copied.
    //## Consider passing a stack as a reference argument.
    //## I realize it's not quite clear at the first glance which structures are expensive to
    //## pass by value, but generally it holds for datastructures (Stack, DHMap, Set, DHMultiset, DArray...).
    //## There are also some structures that should be always passed as pointers:
    //## List, SharedSet, Clause, Term, Unit, BDDNode,...
    //## Iterators generally can be passed by value, except if they are inherited from IteratorCore. But in
    //## this case the compiler will complain if you pass them by value.
    LiteralStack getLiteralAssignmentStack();
    void preprocessProblem(int argc, char** argv);
    //## Same as above, passing stacks by value can be expensive, so better avoided
    //## unless there is a reason for it (it might be a good idea to put the reason
    //## into the documentation then)
    bool getCClosureClauseStatus(LiteralStack litAsgn);
  private:
    //## comments to class members should be in the doxygen format /** ... */
     //keeps a map between the literals found in the clauses and the SAT literals
    TwoWayMap _map;
    //### (1) memory leak, one can deallocate in the destructor (as long as you assign to zero in constructor)
    //###     but the use of ScopedPtr would be even better
    //#	(2) I know it's perhaps not the most sensible practice, but in Vampire code we write the star in
    //#	    pointers as "SAT::SATSolver* _solver" rather than "SAT::SATSolver *_solver".
    //#	    It gets counter-intuitive when one wants to declare several variables of the same type
    //#	    on one line, since "int* a,b" doesn't make "b" a pointer, but that's simply the way it was
    //#	    all over the Vampire code already when I got to it:)
    SAT::SATSolver *_solver;
  };
}

#endif // __SimpleSMT__
