/**
 * @file CombinationsIterator.hpp
 * Defines class CombinationsIterator.
 */

#ifndef __CombinationsIterator__
#define __CombinationsIterator__

#include "Kernel/Term.hpp"

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
    static Term* getConstant(unsigned constant){
      CALL("SubstCombination::getConstant");
      while(constant >= created){
        vstring name = "fmb_" + Lib::Int::toString(created);
        constants[created] = Term::createConstant(name);
        created++;
      }
      return constants[constant];
    }
  private:
    DArray<unsigned> _ar;
    static Array<Term*> constants;
    static unsigned created;
  };

  Array<Term*> SubstCombination::constants;
  unsigned SubstCombination::created = 0;
  

  class CombinationsIterator {

  public:
    CombinationsIterator(unsigned k, unsigned n) : _ar(k), _K(k), _N(n),_hasN(0),_hadEmpty(false) { 
      CALL("CombinationsIterator::CombinationsIterator");
      if(k==0) return; // an empty substitution 

      for(unsigned i=0;i<k;i++) _ar[i]=1;
      _ar[k-1]=0;
    }
    
    bool hasNext(){
      CALL("CombinationsIterator::hasNext");

      if(_K==0 && !_hadEmpty){
        _hadEmpty=true;
        return true;
      }

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
      bool _hadEmpty;
  };

} // namespace FMB
#endif
