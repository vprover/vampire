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
#include "Lib/Array.hpp"

#include "FiniteModelBuilder.hpp"
#include "Forwards.hpp"

namespace FMB {

  using namespace Kernel;
  using namespace Lib;

  struct SubstCombination {
    SubstCombination(DArray<unsigned> ar) : _ar(ar) {}

    TermList apply(unsigned var){
      CALL("SubstCombination::apply");
      ASS_L(var,_ar.size());
      Term* t = FiniteModelBuilder::getConstant(_ar[var]);
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
  private:
    DArray<unsigned> _ar;
  };


  //TODO mark as an actual iterator?
  class CombinationsIterator {

  public:
    CombinationsIterator(unsigned k, unsigned n, bool all=false) : _ar(k), _k(k), _n(n),_hasN(0) { 
      CALL("CombinationsIterator::CombinationsIterator");
      ASS_G(k,0);
      for(unsigned i=0;i<k;i++) _ar[i]=1;
      _ar[k-1]=0;
      if(all) _hasN = 1;
    }
    
    bool hasNext(){
      CALL("CombinationsIterator::hasNext");

      start:
        for(unsigned i=_k-1;i+1!=0;i--){
          if(_ar[i]==_n){
            _ar[i]=1;
            _hasN--;
          }else{
            _ar[i]++;
            if(_ar[i]==_n){_hasN++;}
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
      unsigned _k, _n, _hasN;
  };

} // namespace FMB
#endif
