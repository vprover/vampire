#include "lglopts.h"

#include <stdlib.h>
#include <limits.h>
#include <assert.h>

void lglgetenv (struct LGL * lgl, Opt * opt, const char * lname);

void lglinitopts (struct LGL * lgl, Opts * opts) {
  const int K = 1000, M = K*K, I = INT_MAX;
  const int MG = MAXGLUE;
#ifdef OPT
#undef OPT
#endif
#define OPT(LNG,VAL,MIN,MAX,DESCRP) \
do { \
  Opt * opt = &opts->LNG; \
  opt->lng = #LNG; \
  opt->dflt = opt->val = VAL; \
  assert (MIN <= VAL); \
  opt->min = MIN; \
  assert (VAL <= MAX); \
  opt->max = MAX; \
  opt->descrp = DESCRP; \
  lglgetenv (lgl, opt, #LNG); \
} while (0)

#include "lgloptl.h"
}

