#ifndef lglopts_h_INCLUDED
#define lglopts_h_INCLUDED

#include "lglconst.h"

/*------------------------------------------------------------------------*/

typedef struct Opt {
  const char * lng, * descrp;
  int val, min, max, dflt;
} Opt;

/*------------------------------------------------------------------------*/

#ifdef OPT
#undef OPT
#endif
#define OPT(LNG,VAL,MIN,MAX,DESCRP) Opt LNG

typedef struct Opts {
  Opt beforefirst;
#include "lgloptl.h"
  Opt afterlast;
} Opts;

struct LGL;

/*------------------------------------------------------------------------*/

#define FIRSTOPT(lgl) (&(lgl)->opts->beforefirst + 1)
#define LASTOPT(lgl) (&(lgl)->opts->afterlast - 1)

/*------------------------------------------------------------------------*/

void lglinitopts (struct LGL *, Opts *);

/*------------------------------------------------------------------------*/

#endif
