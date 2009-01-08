#include <stddef.h>

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Options.hpp"
#include "Shell/CommandLine.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Statistics.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

#define INPUTSIZE      524288    // 500Kb read from disk each time
#define MAXTERMSIZE    2000      // maximum number of chars of each term
                                 // in benchmarks
typedef char *stringterm;

#define IsVar(x)  ( (x>=48 && x<=57) || (x>=65 && x<=90) )
#define IsSym(x)  ( (x>=97 && x<=255) )

void ApplicationOp(char op, TermT t);
TermList MakeTerm(char* str);




/* ======= Data structures for general driver: =================== */

struct SymbolTableEntry
{
  SymbolTableEntry(): used(false) {}
  bool used;
  unsigned arity;
  unsigned num;
};
SymbolTableEntry symbolTable[256];


char buf[INPUTSIZE];
Term* terms[INPUTSIZE/2];     // terms
char oper[INPUTSIZE/2];        // operations

int insertions=0;
int deletions=0;
int operations=0;
int numops;


void readSymbolTable(FILE* in)
{
  CALL("readSymbolTable");

  int arity;
  char c=getc(in);
  while (c != EOF)
    {
      if (c=='$') break; // $ indicates end of symboltable

      ASS(!symbolTable[(int)c].used);

      fscanf(in,"/%d\n",&arity);
      symbolTable[(int)c].arity=arity;
      symbolTable[(int)c].used=true;
      symbolTable[(int)c].num=env.signature->addFunction(c,arity);
      c=getc(in);
    }
  c=getc(in); // read newline after $
}


int main( int argc, char *argv[] )
{
  CALL("main");
  FILE *in;

  if (argc != 2) {
    printf("Usage: vcompit <benchmark file>\n");
    return(0);
  }
  if (!(in = fopen(argv[1], "r"))) {
    printf("\n\nUnable to open file\n\n");
    return(0);
  }

  Lib::Random::resetSeed();
  Options options;
  //Shell::CommandLine cl(argc,argv);
  //cl.interpret(options);
  Allocator::setMemoryLimit(options.memoryLimit()*1000000);

  Timer timer;
  timer.start();
  env.timer = &timer;
  Indexing::TermSharing sharing;
  env.sharing = &sharing;
  env.options = &options;
  Shell::Statistics statistics;
  env.statistics = &statistics;


  readSymbolTable(in);

  Timer compitTimer;

  /* First of all, the queries from the benchmark are prepared as input for the application. */
  /* ====== MAIN LOOP ======== */
  int notfinished=1;
  while(notfinished)
    {
      /* ====== read new terms from disk ======== */
      int i=0;
      c=getc(in);
      while (1)
      {
	if (c==EOF) {
	  buf[i]='\0';
	  notfinished=0;
	  break;
	}
	if (c == '\n') {
	  buf[i]='\0';
	  if (i > INPUTSIZE-MAXTERMSIZE) {
	    break;
	  }
	}
	else {
	  buf[i]=c;
	}
	i++;
	c=getc(in);
      }

      /* ====== make application terms ===== */
      int j=0;
      numops=0;
      while ( j<i )
	{
	  oper[numops]=buf[j];
	  terms[numops++]=MakeTerm( buf+j+1 );

	  while (buf[j] != '\0') j++;
	  j++;
	}

      /* ====== perform operations ============== */
      operations = operations + numops;

      compitTimer.start();
      for (j=0;j<numops;j++) {
	/* The translated queries (terms and operations) are send to application. */
        ApplicationOp(oper[j], (terms[j]) );
      }

      compitTimer.stop();
    }
  printf("Total time:\t%d ms\nIndexing time:\t%d ms\n",
	  timer.elapsedMilliseconds(), compitTimer.elapsedMilliseconds());

  printf("ops:%d, +:%d, -:%d.\n",operations,insertions,deletions);
  return 0;
}

/* The actual queries are performed (send to Waldmeister). */
void ApplicationOp(char op, TermT t)
{
  int found;
  switch (op)
    {
    case '+':
      insertions++;
      w_insert(t);
      break;
    case '-':
      w_remove(t);
      deletions++;
      break;
    case '!':
      found = w_match(t);
      if (!found) { printf("match not found!\n"); exit(1); }
      break;
    case '?':
      found = w_match(t);
      if (found)  { printf("wrong match found! (w/ %d).\n",found); exit(1); }
      break;
    }
}

/* ========== translation form stringterm to flatterm ==== */
/* This is: From Benchmark to Waldmeister */

TermList MakeTerm(char* str)
{
  static Stack<char> chars(MAXTERMSIZE);
  static Stack<char> terms(64);
  static Stack<TermList> args(64);
  ASS(chars.isEmpty());
  ASS(terms.isEmpty());
  ASS(args.isEmpty());
  while(str) {
    chars.push(*(str++));
  }

  while(!chars.isEmpty()) {
    char ch=chars.pop();
    if(IsVar(ch)) {
      TermList aux;
      aux.makeVar(ch);
      args.push(aux);
    } else {
      ASS(IsSym(ch));
      ASS(symbolTable[ch].used);

      unsigned functor=symbolTable[ch].num;
      unsigned arity=symbolTable[ch].arity;
      ASS(arity<=args.length());

      Term* trm=new(arity) Term();
      trm->makeSymbol(functor, arity);

      TermList* arg=trm->args();
      while(arg->isNonEmpty()) {
	*arg=args.pop();
	arg=arg->next();
      }

      TermList aux;
      aux.setTerm(env.sharing->insert(trm));
      args.push(aux);
    }
  }
  ASS(chars.isEmpty() && terms.isEmpty() && args.length()==1);
  return args.pop();
}
