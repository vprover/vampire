#include <iostream>
#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Set.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID simGetMin 
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace Kernel;

// This actually emulates rather than uses stuff from DP/SimpleCongruenceClosure
// Just checking the idea works

struct ConstInfo{

  TermList normalForm;
  int normalFormWeight;
};

unsigned simGetMin(Set<unsigned>& terms,DArray<ConstInfo>& _cInfos)
{
  CALL("SimpleCongruenceClosure::getMin");

  Set<unsigned>* now = &terms;
  Set<unsigned>* next = new Set<unsigned>();

  unsigned min_weight = UINT_MAX;
  unsigned min_fsym = UINT_MAX;

  unsigned loop=0;
  while(true){
    cout << "=============== Loop " << loop << endl;
    Set<unsigned>::Iterator it(*now);
    while(it.hasNext()){
      unsigned i = it.next();
      ConstInfo& c = _cInfos[i];
      unsigned w = c.normalFormWeight;
      unsigned f = c.normalForm.term()->functor();
      cout << "proc " << i << " with w" << w << " and f" << f << endl;

      if((w < min_weight) || (w == min_weight && f < min_fsym)){
        delete next;
        next = new Set<unsigned>(); // cheaper than linear reset?
        cout << "reset next with " << i << endl;
        next->insert(i);
        min_weight=w; min_fsym=f;
      }
      else if(w == min_weight && f == min_fsym){
        cout << " add " << i << " to next" << endl;
        next->insert(i);
      }
    }
    cout << "end" << endl;
    // It is important that next is smaller than now
    ASS_G(now->size(),next->size());
    // Also next cannot be empty
    ASS_G(next->size(),0);

    if(next->size()==1){
      Set<unsigned>::Iterator ret(*next);
      ASS(ret.hasNext());
      return ret.next();
    }  
    if(loop>0) delete now;
    now=next;
    next = new Set<unsigned>();
    loop++;
  }
}

TEST_FUN(simGetMin1)
{
  cout << endl;
  
  TermList a = TermList(Term::createConstant(env.signature->addFunction("a",0)));
  TermList b = TermList(Term::createConstant(env.signature->addFunction("b",0)));
  unsigned f = env.signature->addFunction("f",1);
  unsigned g = env.signature->addFunction("g",1);

  DArray<ConstInfo> cInfos;
  cInfos.ensure(5);
  cInfos[0].normalForm = TermList(Term::create1(f,b));
  cInfos[0].normalFormWeight = cInfos[0].normalForm.term()->weight();
  cInfos[1].normalForm = TermList(Term::create1(g,TermList(Term::create1(f,b))));
  cInfos[1].normalFormWeight = cInfos[1].normalForm.term()->weight();
  cInfos[2].normalForm = TermList(Term::create1(f,a));
  cInfos[2].normalFormWeight = cInfos[0].normalForm.term()->weight();
  
  Set<unsigned> terms;
  terms.insert(0); 
  terms.insert(1);
  terms.insert(2);

  unsigned min = simGetMin(terms,cInfos);

  cout << min << endl;

}

