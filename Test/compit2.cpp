
/*
 * File compit2.cpp.
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
 * @file compit2.cpp
 * Implements compit2 shell, that runs benchmark on interface
 * methods declared in compit2.hpp.
 */

#include "compit2.hpp"

#include <stddef.h>
#include <iostream>

#include "Lib/Timer.hpp"

using namespace Lib;


#define OP_BUFFER_CNT 50000


TermStruct terms[OP_BUFFER_CNT];     // terms
WORD oper[OP_BUFFER_CNT];        // operations
unsigned symCnt;
unsigned fnSymCnt;

bool readWord(FILE* f, WORD& val)
{
  char buf[sizeof(WORD)];
  for(unsigned i=0;i<sizeof(WORD);i++) {
    int c=getc(f);
    if(c==EOF) {
      return false;
    }
    buf[i]=c;
  }
  val=*reinterpret_cast<WORD*>(buf);
  return true;
}
WORD getWord(FILE* f)
{
  WORD res;
  if(!readWord(f,res)){
    printf("Invalid input\n"); exit(1);
  }
  return res;
}

bool readOp(FILE* f, int bufferIndex)
{
  bool available=readWord(f,oper[bufferIndex]);
  if(!available) {
    return false;
  }
  compitTermBegin();
  TermStruct res;
  WORD w=getWord(f);
  while(w!=TERM_SEPARATOR) {
    if(w<0) {
      res=compitTermVar(-w-1);
    } else {
      if(w>=symCnt) {
	printf("Invalid input\n"); exit(1);
      }
      res=compitTermFn(w);
    }
    w=getWord(f);
  }
  terms[bufferIndex]=res;

  return true;
}

void readSymbolTable(FILE* in)
{
  symCnt=getWord(in);
  fnSymCnt=getWord(in);
  compitInit(symCnt,fnSymCnt);

  for(unsigned fn=0;fn<symCnt;fn++) {
    compitAddSymbol(fn,getWord(in));
  }
}


int main( int argc, char *argv[] )
{
  FILE *in;

  if (argc != 2) {
    cout<<"Usage: "<<argv[0]<<" <benchmark file>\n";
    return(0);
  }
  if (!(in = fopen(argv[1], "r"))) {
    cout<<"\nUnable to open file\n\n";
    return(0);
  }

  Timer compitTimer;
  Timer totalTimer;
  totalTimer.start();

  readSymbolTable(in);

  int insertions=0;
  int deletions=0;
  int operations=0;

  int notfinished=1;
  while(notfinished)
    {
      /* ====== read new terms from disk ======== */
      int numops;
      for(numops=0; numops<OP_BUFFER_CNT; numops++)
      {
	bool res=readOp(in, numops);
	if (!res) {
	  notfinished=0;
	  break;
	}
      }

      /* ====== perform operations ============== */
#if VDEBUG
      printf("%d operations loaded.\n",numops);
#endif

      compitTimer.start();
      for (int i=0;i<numops;i++) {
	operations++;
	if(oper[i]==-1) {
	  compitInsert(terms[i]);
	  insertions++;
	} else if(oper[i]==-2) {
	  compitDelete(terms[i]);
	  deletions++;
	} else {
	  ASS_GE(oper[i],0);
	  unsigned cnt=compitQuery(terms[i]);
	  if(cnt!=(unsigned)oper[i]) {
	    printf("Found %d matches while there should be %d.\n",cnt,oper[i]);
	    printf("%d retrievals were ok.\n",operations-insertions-deletions);
	    exit(1);
	  }
	}
      }

      compitTimer.stop();
    }
  printf("%s,%d\n",
	  argv[1], compitTimer.elapsedMilliseconds());
//  printf("Total time:\t%d ms\nIndexing time:\t%d ms\n",
//	  totalTimer.elapsedMilliseconds(), compitTimer.elapsedMilliseconds());

//  printf("ops:%d, +:%d, -:%d.\n",operations,insertions,deletions);
  return 0;
}
