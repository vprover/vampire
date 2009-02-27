/**
 * @file compit2.cpp
 * Implements compit2 shell, that runs benchmark on interface
 * methods declared in compit2.hpp.
 */

#include "compit2.hpp"

#include <stddef.h>
#include <iostream>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Timer.hpp"
#include "Kernel/RobSubstitution.hpp"

using namespace Lib;
using namespace Kernel;

#define OP_BUFFER_CNT 50000


/* ======= Data structures for general driver: =================== */

TermStruct terms[OP_BUFFER_CNT];     // terms
WORD oper[OP_BUFFER_CNT];        // operations

int insertions=0;
int deletions=0;
int operations=0;
int numops;

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
    printf("Invalid input\n"); exit(0);
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
      res=compitTermFn(w);
    }
    w=getWord(f);
  }
  terms[bufferIndex]=res;

  return true;
}

void readSymbolTable(FILE* in)
{
  CALL("readSymbolTable");

  unsigned symCnt=getWord(in);
  unsigned fnSymCnt=getWord(in);
  compitInit(symCnt,fnSymCnt);

  for(unsigned fn=0;fn<symCnt;fn++) {
    compitAddSymbol(fn,getWord(in));
  }
}


int main( int argc, char *argv[] )
{
  CALL("main");
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


  int maxCnt=0;
  long totalIndexedWeight=0;
  long totalQueryWeight=0;
  long totalRetrievedTerms=0;
  int succQueryCnt=0;
  /* First of all, the queries from the benchmark are prepared as input for the application. */
  /* ====== MAIN LOOP ======== */
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
      operations = operations + numops;
#if VDEBUG
//      printf("%d operations loaded.\n",numops);
#endif

      compitTimer.start();
      for (int i=0;i<numops;i++) {
	if(oper[i]==-1) {
//	  cout<<"+\t"<<terms[i].toString()<<endl;
	  compitInsert(terms[i]);
	  insertions++;
	  if(terms[i].isVar()) {
	    totalIndexedWeight++;
	  } else {
	    totalIndexedWeight+=terms[i].term()->weight();
	  }
	} else if(oper[i]==-2) {
//	  cout<<"-\t"<<terms[i].toString()<<endl;
	  compitDelete(terms[i]);
	  deletions++;
	} else {
//	  cout<<"?"<<oper[i]<<"\t"<<terms[i].toString()<<endl;
	  ASS_GE(oper[i],0);
	  unsigned cnt=compitQuery(terms[i]);
//	  unsigned cnt=(unsigned)oper[i];
	  if(cnt!=(unsigned)oper[i]) {
	    printf("Found %d matches while there should be %d.\n",cnt,oper[i]);
	    exit(1);
	  }
	  if(cnt) {
	    succQueryCnt++;
	  }
	  totalRetrievedTerms+=cnt;
	  if(terms[i].isVar()) {
	    totalQueryWeight++;
	  } else {
	    totalQueryWeight+=terms[i].term()->weight();
	  }
	}
	if(insertions-deletions>maxCnt) {
	  maxCnt=insertions-deletions;
	}
      }

      compitTimer.stop();
    }
  int queries=operations-insertions-deletions;
  printf("%s,%d,%d,%d,%d,%f,%f,%f,%f,%d,%d,%d\n",argv[1],operations,insertions,deletions,
	  maxCnt,((float)totalIndexedWeight)/insertions,
	  ((float)totalQueryWeight)/queries,
	  ((float)totalRetrievedTerms)/queries,
	  ((float)succQueryCnt)/queries,
	  RobSubstitution::successes,
	  RobSubstitution::mismatchFailures,
	  RobSubstitution::ocFailures
	  );

//  printf("Total time:\t%d ms\nIndexing time:\t%d ms\n",
//	  totalTimer.elapsedMilliseconds(), compitTimer.elapsedMilliseconds());
//
//  printf("ops:%d, +:%d, -:%d.\n",operations,insertions,deletions);
  return 0;
}
