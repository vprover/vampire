/**
 * @file CombinationsIterator.hpp
 * Defines class CombinationsIterator.
 */

#ifndef __CombinationsIterator__
#define __CombinationsIterator__

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Lib/Environment.hpp"
#include "Lib/DArray.hpp"

#include "Forwards.hpp"

namespace FMB {

  using namespace Kernel;
  using namespace Lib;

  struct SubstCombination {
    SubstCombination(DArray<unsigned> ar) : _ar(ar) {}

    TermList apply(unsigned var){
      CALL("SubstCombination::apply");
      ASS_L(var,_ar.size());
      Term* t = getConstant(_ar[var]);
      ASS(t);
      return TermList(t);
    }
#if VDEBUG
    void print(){
      cout << "S ";
      for(unsigned i=0;i<_ar.size();i++) cout << _ar[i] << " ";
      cout << endl;
    }
#endif

//TODO - this should all be moved elsewhere!!
    static Term* getConstant(unsigned constant){
      CALL("SubstCombination::getConstant");
      while(constant >= created){
        vstring name; 
        bool found=false;
/*
        while(!found && fchecked<env.signature->functions()){
          fchecked++;
          Signature::Symbol* fun = env.signature->getFunction(fchecked); 
          if(fun->arity()==0){
            found=true;
            name=fun->name(); 
          }
        }
*/
        if(!found){
          name = "fmb_" + Lib::Int::toString(created);
        }
        constants[created] = Term::createConstant(name);
        created++;
      }
      return constants[constant];
    }
  private:
    DArray<unsigned> _ar;
    static Array<Term*> constants;
    static unsigned created;
    static unsigned fchecked; 
  };

  Array<Term*> SubstCombination::constants;
  unsigned SubstCombination::created = 0;
  unsigned SubstCombination::fchecked = 0;
  

  class CombinationsIterator {

  public:
    CombinationsIterator(unsigned k, unsigned n, bool all=false) : _ar(k), _K(k), _N(n),_hasN(0) { 
      CALL("CombinationsIterator::CombinationsIterator");
      ASS_G(k,0);
      for(unsigned i=0;i<k;i++) _ar[i]=1;
      _ar[k-1]=0;
      if(all) _hasN = 1;
    }
    
    bool hasNext(){
      CALL("CombinationsIterator::hasNext");

      start:
        for(unsigned i=_K-1;i+1!=0;i--){
          if(_ar[i]==_N){
            _ar[i]=1;
            _hasN--;
          }else{
            _ar[i]++;
            if(_ar[i]==_N){_hasN++;}
            if(_hasN) return true;
            else goto start;
          }
        }
      return false;
    }

    SubstCombination next(){
      CALL("CombinationsIterator::next");
      return SubstCombination(_ar); 
    }
   
    private:
      DArray<unsigned> _ar;
      unsigned _K, _N, _hasN;
  };

} // namespace FMB
#endif
