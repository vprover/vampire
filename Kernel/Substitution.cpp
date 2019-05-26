
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

#include "Substitution.hpp"
#include "Kernel/SubstHelper.hpp"

namespace Kernel
{

/**
 * Bind @b v to @b t.
 * @pre @b v must previously be unbound
 */
void Substitution::bind(int v,Term* t)
{
  CALL("Substitution::bind(int,Term*)");
  TermList ts;
  ts.setTerm(t);
  bind(v,ts);
}
void Substitution::rebind(int v,Term* t)
{
  TermList ts;
  ts.setTerm(t);
  rebind(v,ts);
}

/**
 * Bind @b v to @b t.
 * @pre @b v must previously be unbound
 */
void Substitution::bind(int v,TermList t)
{
  CALL("Substitution::bind(int,TermList)");

  ALWAYS(_map.insert(v, t));
} // Substitution::bind

void Substitution::rebind(int v,TermList t)
{
  _map.set(v,t);
}

/**
 * Remove the binding for @b v from the substitution.
 * @pre @b v must previously be bound
 * @since 04/05/2006 Bellevue
 * @since 30/12/2007 Manchester
 */
void Substitution::unbind(int v)
{
  CALL("Substitution::unbind");

  ALWAYS(_map.remove(v));
} // Substitution::unbind

void Substitution::reset()
{
  CALL("Substitution::reset");

  _map.reset();
}

/**
 * Return result of application of the substitution to variable @c var
 *
 * This function is to allow use of the @c Substitution class in the
 * methods of the @c SubstHelper class for applying substitutions.
 */
TermList Substitution::apply(unsigned var)
{
  TermList res;
  if(!findBinding(var, res)) {
    res = TermList(var,false);
  }
  return res;
}

/**
 * If @c var is bound, assign bingind into @c res and return true.
 * Otherwise return false and do nothing.
 */
bool Substitution::findBinding(int var, TermList& res) const
{
  CALL("Substitution::findBinding");

  return _map.find(var, res);
} // Substitution::bound

void Substitution::compose(Substitution& other) {
  Substitution nsub;
  unsigned v;
  TermList t, temp;
  // apply other to every bound term
  for (DHMap<unsigned,TermList>::Iterator it(this->_map);
       it.hasNext();  ) {
    it.next(v,t);
    temp = SubstHelper::apply(t, other);
    //cerr << "substitution composition: rebind " << v << " to " << temp.toString() << endl;
    nsub.bind(v, temp);
  }
  // add all mappings not in domain of this substitution
  for (DHMap<unsigned,TermList>::Iterator it(other._map);
       it.hasNext();  ) {
    it.next(v,t);
    if (! this->_map.find(v,temp)) {
      //cerr << "substitution composition: bind new " << v << " to " << t.toString() << endl;
      nsub.bind(v, t);
    }
  }
  this->_map.reset();
  this->_map.loadFromMap(nsub._map);
} // Substitution::compose


  
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
   result += ']';
   return result;
 } // Substitution::toString()
#endif

}

