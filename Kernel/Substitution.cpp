
/*
 * File Substitution.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Substitution.cpp
 * Implements class Substitution.
 * @since 28/12/2007 Manchester, implemented from scratch
 */

#if VDEBUG
#  include "Lib/Int.hpp"
#  include "Term.hpp"
#endif

#include "Shell/BetaReductionEngine.hpp"

#include "Substitution.hpp"

using namespace Shell;

namespace Kernel
{

/**
 * Bind @b v to @b t.
 * @pre @b v must previously be unbound
 */
void Substitution::bind(unsigned v,Term* t)
{
  CALL("Substitution::bind(unsigned,Term*)");
  TermList ts;
  ts.setTerm(t);
  bind(v,ts);
}

void Substitution::rebind(unsigned v,Term* t)
{
  TermList ts;
  ts.setTerm(t);
  rebind(v,ts);
}

/**
 * Bind @b v to @b t.
 * @pre @b v must previously be unbound
 */
void Substitution::bind(unsigned v,TermList t)
{
  CALL("Substitution::bind(int,TermList)");

  if(v < Term::VARIABLE_HEAD_LOWER_BOUND){
    ALWAYS(_map.insert(v, t));
  } else {
    ALWAYS(_hoLambdaMap.insert(v - Term::VARIABLE_HEAD_LOWER_BOUND, t));
  }
} // Substitution::bind

void Substitution::bind(unsigned v, Prefix p)
{
  CALL("Substitution::bind(int,Prefix)");

  ALWAYS(_hoPrefixMap.insert((v - Term::VARIABLE_HEAD_LOWER_BOUND), p));

  //cout << "prefix " + p.toString() + " bound" << endl;
  //cout << "the substitution is now " + this->toString() << endl;
}

void Substitution::rebind(unsigned v,TermList t)
{
  if(v < Term::VARIABLE_HEAD_LOWER_BOUND){
    _map.set(v,t);
  } else {
    _hoLambdaMap.set(v - Term::VARIABLE_HEAD_LOWER_BOUND,t);
  }
}

void Substitution::rebind(unsigned v, Prefix p)
{
  CALL("Substitution::bind(int,Prefix)");

  _hoPrefixMap.set(v - Term::VARIABLE_HEAD_LOWER_BOUND,p);
}


/**
 * Remove the binding for @b v from the substitution.
 * @pre @b v must previously be bound
 * @since 04/05/2006 Bellevue
 * @since 30/12/2007 Manchester
 */
void Substitution::unbind(unsigned v)
{
  CALL("Substitution::unbind");
  
  if(v < Term::VARIABLE_HEAD_LOWER_BOUND){
    ALWAYS(_map.remove(v));
  } else { 
    if(!_hoLambdaMap.remove(v - Term::VARIABLE_HEAD_LOWER_BOUND)){
      ALWAYS(_hoPrefixMap.remove(v - Term::VARIABLE_HEAD_LOWER_BOUND));  
    }
  }
} // Substitution::unbind

void Substitution::reset()
{
  CALL("Substitution::reset");

  _map.reset();
  _hoLambdaMap.reset();
  _hoPrefixMap.reset();
}

/**
 * Return result of application of the substitution to variable @c var
 *
 * This function is to allow use of the @c Substitution class in the
 * methods of the @c SubstHelper class for applying substitutions.
 */
TermList Substitution::apply(unsigned var)
{
  ASS(var < Term::VARIABLE_HEAD_LOWER_BOUND);
  TermList res;
  if(!findBinding(var, res)) {
    res = TermList(var,false);
  }
  return res;
}

TermList Substitution::applyHigherOrder(Term* varHeadTerm){
   CALL("Substitution::applyHigherOrder");

   ASS(varHeadTerm->hasVarHead());
   TermList ts;
   Prefix p;
  
   unsigned var = varHeadTerm->functor();
   if(findBinding(var, ts)){
      //ts contains a lambda term. Carry out beta reduction and return result.

      BetaReductionEngine bre = BetaReductionEngine();
      TermList newTerm = ts;
      for(unsigned j = 0; j < varHeadTerm->arity(); j++){
        TermList tss = *(varHeadTerm->nthArgument(j));
        ASS(newTerm.isTerm());
        newTerm = bre.betaReduce(newTerm.term(), tss); 
      }

      return newTerm;      
   }
   if(findBinding(var, p)){
     //p contains a prefix. Return varHeadTerm with variable head replaced by p[refix
     Term* newTerm = Term::create(p.functor(), p.prefixLength(), varHeadTerm->arity(),
                                  p.prefixArgs(), varHeadTerm->args());
     return TermList(newTerm);
   }
   return TermList(varHeadTerm);

}

/**
 * If @c var is bound, assign binding into @c res and return true.
 * Otherwise return false and do nothing.
 */
bool Substitution::findBinding(unsigned var, TermList& res) const
{
  CALL("Substitution::findBinding");

  if(var < Term::VARIABLE_HEAD_LOWER_BOUND){
    return _map.find(var, res);
  } else {
    return _hoLambdaMap.find(var - Term::VARIABLE_HEAD_LOWER_BOUND, res);
  }
} // Substitution::bound


bool Substitution::findBinding(unsigned var, Prefix& res) const
{
  CALL("Substitution::findBinding(unsigned, Prefix)");

  return _hoPrefixMap.find((var - Term::VARIABLE_HEAD_LOWER_BOUND), res);
} // Substitution::findBinding



#if VDEBUG
 vstring Substitution::toString() const
 {
   vstring result("[");
   VirtualIterator<std::pair<unsigned,TermList>> items = _map.items();
   bool first=true;
   while(items.hasNext()){
     std::pair<unsigned,TermList> item = items.next();
     if(!first){result+=",";}
     first=false;
     result += Lib::Int::toString(item.first) + " -> " + item.second.toString(); 
   }
   
   result += "]\n High-order subsitutions: \n[";
   VirtualIterator<std::pair<unsigned,TermList>> items2 = _hoLambdaMap.items();
   first=true;
   while(items2.hasNext()){
     std::pair<unsigned,TermList> item = items2.next();
     if(!first){result+=",";}
     first=false;
     result += Lib::Int::toString(item.first + Term::VARIABLE_HEAD_LOWER_BOUND) + " -> " + item.second.toString(); 
   }
   result += "] \n [";

   VirtualIterator<std::pair<unsigned,Prefix>> items3 = _hoPrefixMap.items();
   first=true;
   while(items3.hasNext()){
     std::pair<unsigned,Prefix> item = items3.next();
     if(!first){result+=",";}
     first=false;
     result += Lib::Int::toString(item.first) + " -> " + item.second.toString(); 
   }
   result += ']';

   return result;
 } // Substitution::toString()
#endif

}

