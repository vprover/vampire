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

using namespace Lib;

typedef unsigned char *stringterm;

#define IsVar(x)  ( (x>=48 && x<=57) || (x>=65 && x<=90) )
#define IsSym(x)  ( (x>=97 && x<=255) )

void ApplicationOp(unsigned char op, TermList t);
TermList MakeTerm(unsigned char* str);

#define OP_BUFFER_CNT 50000


/* ======= Data structures for general driver: =================== */

WORD buf[INPUTSIZE];

TermStruct terms[OP_BUFFER_CNT];     // terms
WORD oper[OP_BUFFER_CNT];        // operations

int insertions=0;
int deletions=0;
int operations=0;
int numops;

bool readWord(FILE* f, WORD& val)
{
  char buf[sizeof(WORD)];
  for(int i=0;i<sizeof(WORD);i++) {
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
  ALWAYS(readWord(f,res));
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
      res=compitTermVar(-w+1);
    } else {
      res=compitTermFn(w);
    }
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

  readSymbolTable(in);

  Timer totalTimer;
  Timer compitTimer;

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
	  buf[numops]='\0';
	  notfinished=0;
	  break;
	}
      }

      /* ====== perform operations ============== */
      operations = operations + numops;
#if VDEBUG
      printf("%d operations loaded.\n",numops);
#endif

      compitTimer.start();
      for (int i=0;i<numops;i++) {
	if(oper[i]==-1) {
	  compitInsert(terms[i]);
	} else if(oper[i]==-2) {
	  compitDelete(terms[i]);
	} else {
	  ASS_GE(oper[i],0);
	  unsigned cnt=compitQuery(terms[i]);
	  if(cnt!=oper[i]) {
	    if (!found) { printf("Found %d matches while there should be %d.\n",cnt,oper[i]); exit(1); }
	  }
	}
      }

      compitTimer.stop();
    }
  printf("Total time:\t%d ms\nIndexing time:\t%d ms\n",
	  timer.elapsedMilliseconds(), compitTimer.elapsedMilliseconds());

  printf("ops:%d, +:%d, -:%d.\n",operations,insertions,deletions);
  return 0;
}
