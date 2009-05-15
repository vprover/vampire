#include <iostream>

#include "Debug/Assertion.hpp"
#include "Kernel/BDD.hpp"

using namespace Kernel;
using namespace std;

BDD bdd;

int main()
{
  int v0=bdd.getNewVar();
  int v1=bdd.getNewVar();
  int v2=bdd.getNewVar();
  BDDNode* bn=bdd.getAtomic(v0, false);
  for(int i=0;i<10;i++) {
    int v=bdd.getNewVar();
    bn=bdd.disjunction(bn, bdd.getAtomic(v, false));
  }
  cout<<bdd.toString(bn)<<endl<<endl;
  BDDNode* bn2=bdd.getAtomic(v1, false);
  for(int i=0;i<10;i++) {
    int v=bdd.getNewVar();
    bn2=bdd.disjunction(bn2, bdd.getAtomic(v, false));
  }
  cout<<bdd.toString(bn2)<<endl<<endl;

  bn=bdd.conjunction(bn, bdd.getAtomic(v2, true));
  cout<<bdd.toString(bn)<<endl<<endl;
  bn=bdd.conjunction(bn, bn2);
  cout<<bdd.toString(bn)<<endl<<endl;
  bn=bdd.conjunction(bn, bdd.getAtomic(v2, false));
  cout<<bdd.toString(bn)<<endl<<endl;

  ASS(bdd.isFalse(bn));
  ASS(!bdd.isTrue(bn));
//  bn=bdd.disjunction(bn, bdd.getAtomic(v0, true));
//  ASS(!bdd.isFalse(bn));
//  ASS(!bdd.isTrue(bn));
//  bn=bdd.disjunction(bn, bdd.getAtomic(v1, true));
//  ASS(bdd.isTrue(bn));
//  ASS(!bdd.isFalse(bn));
  return 0;
}
