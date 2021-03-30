/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file CliqueFinder.hpp
 * Defines a heurstic for finding maximal cliques, the method is not complete 
 */

#ifndef __CliqueFinder__
#define __CliqueFinder__

#include "Lib/DHMap.hpp"

namespace FMB {

  class CliqueFinder {
  public:
    static unsigned findMaxCliqueSize(DHMap<unsigned,DHSet<unsigned>*>* Ngraph)
    {
      CALL("FMB::CliqueFinder::findMaxCliqueSize");

      //cout << "findMaxCliqueSize with " << Ngraph->size() << endl;

      // at least stores the number of nodes with at least index neighbours
      DArray<Stack<unsigned>> atleast;
      atleast.ensure(Ngraph->size()+1); // the +1 is to protect against a self-loop sneaking in

      DHMap<unsigned,DHSet<unsigned>*>::Iterator miter(*Ngraph);
      while(miter.hasNext()){
        unsigned c;
        DHSet<unsigned>* nbs;
        miter.next(c,nbs);
        unsigned size = nbs->size();
        //cout << ">> " << c << ": " << size << endl;

        //DHSet<unsigned>::Iterator dit(*nbs);
        //while(dit.hasNext()){ cout << dit.next() << endl; }

        for(;size>0;size--){
          atleast[size].push(c);
        }
      }
      //cout << "Searching" << endl;

      for(unsigned i=atleast.size()-1;i>1;i--){
        // in this case we would expect atleast[i] to be the clique
        if(atleast[i].size() == i+1){
          //cout << "CASE 1" << endl;
          if(checkClique(Ngraph,atleast[i])){
            //cout << "FIND(A) max clique of " << (i+1) << endl;
            //for(unsigned j=0;j<atleast[i].size();j++){ cout << atleast[i][j] << " ";}; cout << endl;
            return i+1;
          }
        }
        // in this case atleast[i] may contain a clique but cannot be a clique itself
        // we need to look at subsets
        else if (atleast[i].size() > i+1){
          //cout << "CASE 2" << endl;
          unsigned left = atleast[i].size();
          Stack<unsigned>::Iterator niter(atleast[i]);
          while(niter.hasNext() && left >= i+1){
            unsigned c = niter.next();
            //cout << ">> " << c << endl;
            auto ns = Ngraph->get(c);
            if(ns->size()==i){
              Stack<unsigned> clique;
              clique.loadFromIterator(ns->iterator());
              clique.push(c);
              if(checkClique(Ngraph,clique)){
                //cout << "FIND(B) max clique of " << (i+1) << endl;
                return i+1;
              }
              left--;
            }
          }
          //cout << "In this case with " << left << " left" << endl;
        }
      }

      //for(unsigned i=1;i<atleast.size();i++){
      //  cout << i << ":"<< atleast[i].size() << endl; 
      //}
      return 1;
    }
  private:

    // check if a clique is a clique
    static bool checkClique(DHMap<unsigned,DHSet<unsigned>*>* Ngraph, Stack<unsigned>& clique)
    {
      CALL("FMB::CliqueFinder::checkClique");
      
      //cout << "CHECK "; for(unsigned j=0;j<clique.size();j++){ cout << clique[j] << " ";}; cout << endl;

      for(unsigned i=0;i<clique.size()-1;i++){
        unsigned c1 = clique[i];
        auto ns = Ngraph->get(c1);
        //cout << c1 << " neighbours: "; 
        //DHSet<unsigned>::Iterator pit(*ns);while(pit.hasNext()){cout << pit.next() << " ";};cout<<endl;
        for(unsigned j=i+1;j<clique.size();j++){
          unsigned c2 = clique[j];
          //cout << "checking " << c2 << " is a neighbour of " << c1 << endl;
          if(!ns->find(c2)){ return false; }
        }
      }
      return true;
    }


  };



}

#endif
