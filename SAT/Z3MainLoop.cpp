/**
 * @file Z3MainLoop.cpp
 * Defines class Z3MainLoop.
 */

#if VZ3

#include "Forwards.hpp"

#include "Z3MainLoop.hpp"

namespace SAT
{

using namespace Shell;
using namespace Lib;

Z3MainLoop::Z3MainLoop(Problem& prb, const Options& opt)
: MainLoop(prb,opt)
{
  CALL("Z3MainLoop::Z3MainLoop");

}

void Z3MainLoop::init()
{
  CALL("Z3MainLoop::init");

  
}

MainLoopResult Z3MainLoop::runImpl()
{
  CALL("Z3MainLoop::runImpl");

  SAT2FO s2f;
  Z3Interfacing solver(_opt,s2f);

 ClauseIterator cit(_prb.clauseIterator());
 while(cit.hasNext()){
   Clause* cl = cit.next();
   Clause::Iterator lit(*cl);
   unsigned len = cl->size();
   SATClause* sc = new(len) SATClause(len, true);
   unsigned i=0;
   while(lit.hasNext()){
     Literal* l = lit.next();
     SATLiteral sl = s2f.toSAT(l);
     (*sc)[i++] = sl;
   }
   solver.addClause(sc);
 }

 Status status = solver.solve();

 TerminationReason reason = 

 return MainLoopResult(reason);
}

}

#endif
