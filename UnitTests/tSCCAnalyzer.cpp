/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/Int.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/SCCAnalyzer.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Random.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;

typedef char Node;
typedef MapToLIFO<Node,Node> GMap;

void addEdges(GMap& map, char src, const char* tgts)
{
  while(*tgts) {
    map.pushToKey(src, *tgts);
    tgts++;
  }
}

TEST_FUN(scc1)
{
  GMap map;

  addEdges(map, 'a', "bcd");
  addEdges(map, 'b', "cd");
  addEdges(map, 'c', "a");
  addEdges(map, 'd', "e");
  addEdges(map, 'e', "d");

  MapToLIFOGraph<Node> gr(map);

  SCCAnalyzer<MapToLIFOGraph<Node> > anl(gr);

  ASS_EQ(anl.components().size(),2);

  cout<<"BR:";
  Stack<Node>::ConstIterator brit(anl.breakingNodes());
  while(brit.hasNext()) {
    cout<<brit.next();
  }
  cout<<endl;
}

TEST_FUN(scc2)
{
  GMap map;

  Random::setSeed(1);

  for(char c='a'; c<='z'; c++) {
    for(char d='a'; d<='z'; d++) {
      if(c==d || Random::getInteger(10)!=0) {
	continue;
      }
      map.pushToKey(c,d);
    }
  }

  MapToLIFOGraph<Node> gr1(map);

  SCCAnalyzer<MapToLIFOGraph<Node> > anl1(gr1);

  cout<<anl1.components().size()<<" "<<anl1.breakingNodes().size()<<endl;

  Subgraph<MapToLIFOGraph<Node> > gr2(gr1, Stack<Node>::ConstIterator(anl1.breakingNodes()));
  SCCAnalyzer<Subgraph<MapToLIFOGraph<Node> > > anl2(gr2);

  ASS_EQ(gr2.size(), anl2.components().size());
  ASS_EQ(anl2.breakingNodes().size(), 0);
}
