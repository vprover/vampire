/**
 * @file SATLiteral.cpp
 * Implements class SATLiteral.
 */

#include <ostream>


#include "Debug/RuntimeStatistics.hpp"

#include "Shell/Options.hpp"

#include "Lib/Int.hpp"

#include "Kernel/Term.hpp"

#include "SATLiteral.hpp"


namespace SAT
{

using namespace std;
using namespace Lib;
using namespace Shell;

string SATLiteral::toString() const
{
  if(isPositive()) {
    return Int::toString(var());
  } else {
    return "~"+Int::toString(var());
  }
}

/**
 * Uses _source to compute the niceness for this SATLiteral
 * Note - higher is better i.e. a larger niceness value should indicate
 *        that we want to select this literal
 *
 * The general notion used here is that it is 'nicer' to have variables
 * and constants deeper in the literal. 
 *
 * Three separate ways of computing niceness have been implemented. These
 * should be compared and other options explored. 
 * 
 * @author Giles
 */
unsigned SATLiteral::getNiceness(Options::NicenessOption niceness_option)
{
  CALL("SATLiteral::getNiceness");

  // use source literal to compute niceness weight

  // if it is null return 1 niceness
  // we assume that either all SATLiterals will have a niceness
  // score or none will
  if(!_source){
    return 1;
  }
  //We will do a Breadth-First search for variables or constants

  static Stack<const TermList*> _stack;
  _stack.reset();

  _stack.push(_source->args());

  unsigned level = 0;
  unsigned level_multiplier = 1;//change to make lower levels score more
  bool found = false;
  unsigned level_sum = 0; 
  unsigned count = 0;
  bool divide = false;
  switch(niceness_option){
    case Options::NICENESS_NONE:
      return 1; 
    case Options::NICENESS_TOP:
      // Search for highest variable/constant
      while(!_stack.isEmpty() && !found){
        level++;
        for(const TermList* t = _stack.pop(); !t->isEmpty(); t = t->next()){
          if(t->isVar()){
            found=true;
            break;
          }
          else{
            ASS(t->isTerm());
            const Term* trm = t->term();
            ASS(trm->shared());
            if(trm->ground()){
              found=true;
              break;
            }
            _stack.push(trm->args()); //breadth first, save args for later
          }
        }
      }  
      level = level*level_multiplier;
      RSTAT_MCTR_INC("nscore",level);
      return level; 
    case Options::NICENESS_AVERAGE:
      divide=true;
    case Options::NICENESS_SUM:
      //sum the levels of all variables/constants
      while(!_stack.isEmpty()){
        level++;
        for(const TermList* t = _stack.pop(); !t->isEmpty(); t = t->next()){
          if(t->isVar()){
            level_sum += (level*level_multiplier); 
          }
          else{
            ASS(t->isTerm());
            const Term* trm = t->term();
            ASS(trm->shared());
            if(trm->ground()){
              level_sum += (level*level_multiplier); 
              count += 1;
            }
            _stack.push(trm->args()); //breadth first, save args for later
          }
        }
      }
      RSTAT_MCTR_INC("nscore",level_sum);
      // if we want average, we set divid=true earlier
      if(divide){ level_sum = (level_sum/count);}//This division will truncate
      return level_sum;  
    //default: ASSERTION_VIOLATION(niceness_option);
  }

  return 1;
}
};

std::ostream& operator<< (std::ostream& out, const SAT::SATLiteral& lit )
{
  return out<<lit.toString();
}



