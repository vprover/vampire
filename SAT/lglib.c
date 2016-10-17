/*-------------------------------------------------------------------------*/
/* Copyright 2010-2015 Armin Biere Johannes Kepler University Linz Austria */
/*-------------------------------------------------------------------------*/

#include "lglib.h"

/*------------------------------------------------------------------------*/

#include "lglconst.h"
#include "lglopts.h"

/*-------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

/*-------------------------------------------------------------------------*/

#define NLGLYALSAT // MS: what the hack is yals?

#ifndef NLGLYALSAT
#include "yals.h"
#endif

#define NLGLDRUPLIG // MS: what the hack is druplig?

#ifndef NLGLDRUPLIG
#include "druplig.h"
#endif

/*------------------------------------------------------------------------*/
#ifndef NLGLOG
/*------------------------------------------------------------------------*/

#define MAPLOGLEVEL(LEVEL) (LEVEL)

#define LOG(LEVEL,FMT,ARGS...) \
do { \
  if (MAPLOGLEVEL(LEVEL) > lgl->opts->log.val) break; \
  lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
  lglogend (lgl); \
} while (0)

#define LOGCLS(LEVEL,CLS,FMT,ARGS...) \
do { \
  const int * P; \
  if (MAPLOGLEVEL(LEVEL) > lgl->opts->log.val) break; \
  lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
  for (P = (CLS); *P; P++) fprintf (lgl->out, " %d", *P); \
  lglogend (lgl); \
} while (0)

#define LOGMCLS(LEVEL,CLS,FMT,ARGS...) \
do { \
  const int * P; \
  if (MAPLOGLEVEL(LEVEL) > lgl->opts->log.val) break; \
  lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
  for (P = (CLS); *P; P++) fprintf (lgl->out, " %d", lglm2i (lgl, *P)); \
  lglogend (lgl); \
} while (0)

#define LOGRESOLVENT(LEVEL,FMT,ARGS...) \
do { \
  const int * P; \
  if (MAPLOGLEVEL(LEVEL) > lgl->opts->log.val) break; \
  lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
  for (P = lgl->resolvent.start; P < lgl->resolvent.top; P++) \
    fprintf (lgl->out, " %d", *P); \
  lglogend (lgl); \
} while (0)

#define LOGREASON(LEVEL,LIT,REASON0,REASON1,FMT,ARGS...) \
do { \
  int TAG, TMP, RED, G; \
  const int * C, * P; \
  if (MAPLOGLEVEL(LEVEL) > lgl->opts->log.val) break; \
  lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
  TMP = ((REASON0) >> RMSHFT); \
  RED = ((REASON0) & REDCS); \
  TAG = ((REASON0) & MASKCS); \
  if (TAG == DECISION) fputs (" decision", lgl->out); \
  else if (TAG == UNITCS) fprintf (lgl->out, " unit %d", (LIT)); \
  else if (TAG == BINCS) { \
    fprintf (lgl->out, \
       " %s binary clause %d %d", lglred2str (RED), (LIT), TMP); \
  } else if (TAG == TRNCS) { \
    fprintf (lgl->out, " %s ternary clause %d %d %d", \
	    lglred2str (RED), (LIT), TMP, (REASON1)); \
  } else { \
    assert (TAG == LRGCS); \
    C = lglidx2lits (lgl, RED, (REASON1)); \
    for (P = C; *P; P++) \
      ; \
    fprintf (lgl->out, " size %ld", (long)(P - C)); \
    if (RED) { \
      G = ((REASON1) & GLUEMASK); \
      fprintf (lgl->out, " glue %d redundant", G); \
    } else fputs (" irredundant", lgl->out); \
    fputs (" clause", lgl->out); \
    for (P = C; *P; P++) { \
      fprintf (lgl->out, " %d", *P); \
    } \
  } \
  lglogend (lgl); \
} while (0)

#define LOGDSCHED(LEVEL,LIT,FMT,ARGS...) \
  do { \
    int POS; \
    if (MAPLOGLEVEL(LEVEL) > lgl->opts->log.val) break; \
    POS = *lgldpos (lgl, LIT); \
    lglogstart (lgl, MAPLOGLEVEL(LEVEL), "dsched[%d] = %d ", POS, LIT); \
    fprintf (lgl->out, FMT, ##ARGS); \
    fprintf (lgl->out, \
      " score %s", lglscr2str (lgl, lglqvar (lgl, LIT)->score)); \
    lglogend (lgl); \
  } while (0)

#define LOGESCHED(LEVEL,LIT,FMT,ARGS...) \
do { \
  int POS; \
  EVar * EV; \
  if (MAPLOGLEVEL(LEVEL) > lgl->opts->log.val) break; \
  POS = *lglepos (lgl, LIT); \
  EV = lglevar (lgl, LIT); \
  lglogstart (lgl, MAPLOGLEVEL(LEVEL), "esched[%d] = %d ", POS, LIT); \
  fprintf (lgl->out, FMT, ##ARGS); \
  fprintf (lgl->out, " score"); \
  fprintf (lgl->out, " occ %d %d", EV->occ[0], EV->occ[1]); \
  lglogend (lgl); \
} while (0)

#define LOGEQN(LEVEL,EQN,FMT,ARGS...) \
do { \
  const int * P, * START; \
  if (MAPLOGLEVEL(LEVEL) > lgl->opts->log.val) break; \
  lglogstart (lgl, MAPLOGLEVEL(LEVEL), FMT, ##ARGS); \
  START = lgl->gauss->xors.start + (EQN); \
  assert (START < lgl->gauss->xors.top); \
  for (P = START; *P > 1; P++) fprintf (lgl->out, " %d", *P); \
  fprintf (lgl->out, " = %d", *P); \
  lglogend (lgl); \
} while (0)

/*------------------------------------------------------------------------*/
#else /* end of then start of else part of 'ifndef NLGLOG' */
/*------------------------------------------------------------------------*/

#define LOG(ARGS...) do { } while (0)
#define LOGCLS(ARGS...) do { } while (0)
#define LOGMCLS(ARGS...) do { } while (0)
#define LOGRESOLVENT(ARGS...) do { } while (0)
#define LOGREASON(ARGS...) do { } while (0)
#define LOGDSCHED(ARGS...) do { } while (0)
#define LOGESCHED(ARGS...) do { } while (0)
#define LOGEQN(ARGS...) do { } while (0)

/*------------------------------------------------------------------------*/
#endif /* end of else part of 'ifndef NLGLOG' */
/*------------------------------------------------------------------------*/

#define ABORTIF(COND,FMT,ARGS...) \
do { \
  if (!(COND)) break; \
  fprintf (stderr, "*** API usage error of '%s' in '%s'", \
	   __FILE__, __FUNCTION__); \
  if (lgl && lgl->tid >= 0) fprintf (stderr, " (tid %d)", lgl->tid); \
  fputs (": ", stderr); \
  fprintf (stderr, FMT, ##ARGS); \
  fputc ('\n', stderr); \
  fflush (stderr); \
  lglabort (lgl); \
  exit (1); \
} while (0)

// Useful for using our 'sleeponabort' and other hooks 'on abort' ...

#ifndef NDEBUG
#define ASSERT(COND) \
do { \
  if ((COND)) break; \
  fprintf (stderr, \
    "liblgl.a: %s:%d: %s: Lingeling Assertion `%s' failed.", \
    __FUNCTION__, __LINE__, __FILE__, # COND); \
  if (lgl && lgl->tid >= 0) fprintf (stderr, " (tid %d)", lgl->tid); \
  fputc ('\n', stderr); \
  fflush (stderr); \
  lglabort (lgl); \
  exit (1); \
} while (0)
#else
#define ASSERT(COND) do { } while (0)
#endif

#define COVER(COND) \
do { \
  if (!(COND)) break; \
  fprintf (stderr, \
    "liblgl.a: %s:%d: %s: Coverage target `%s' reached.", \
    __FUNCTION__, __LINE__, __FILE__, # COND); \
  if (lgl && lgl->tid >= 0) fprintf (stderr, " (tid %d)", lgl->tid); \
  fputc ('\n', stderr); \
  fflush (stderr); \
  abort (); /* TODO: why not 'lglabort'? */ \
} while (0)

#define REQINIT() \
do { \
  ABORTIF (!lgl, "uninitialized manager"); \
} while (0)

#define REQINITNOTFORKED() \
do { \
  REQINIT (); \
  ABORTIF (lgl->forked, "forked manager"); \
} while (0)

#define REQUIRE(STATE) \
do { \
  REQINIT (); \
  ABORTIF(!(lgl->state & (STATE)), "!(%s)", #STATE); \
} while (0)

#define TRANS(STATE) \
do { \
  assert (lgl->state != STATE); \
  LOG (1, "transition to state " #STATE); \
  lgl->state = STATE; \
} while (0)

/*------------------------------------------------------------------------*/

#if !defined(NDEBUG) || !defined(NLGLOG)
#define RESOLVENT
#endif

/*------------------------------------------------------------------------*/

#define TRAPI(MSG,ARGS...) \
do { \
  if (!lgl->apitrace) break; \
  lgltrapi (lgl, MSG, ##ARGS); \
} while (0)

#define LGLCHKACT(ACT) \
do { assert (NOTALIT <= (ACT) && (ACT) < REMOVED - 1); } while (0)

/*------------------------------------------------------------------------*/

#define NEW(P,N) \
do { (P) = lglnew (lgl, (N) * sizeof *(P)); } while (0)

#define DEL(P,N) \
do { lgldel (lgl, (P), (N) * sizeof *(P)); (P) = 0; } while (0)

#define RSZ(P,O,N) \
do { (P) = lglrsz (lgl, (P), (O)*sizeof*(P), (N)*sizeof*(P)); } while (0)

#define CLN(P,N) \
do { memset ((P), 0, (N) * sizeof *(P)); } while (0)

#define CLRPTR(P) \
do { memset ((P), 0, sizeof *(P)); } while (0)

#define CLR(P) \
do { memset (&(P), 0, sizeof (P)); } while (0)

/*------------------------------------------------------------------------*/

#define SWAP(TYPE,A,B) \
do { TYPE TMP = (A); (A) = (B); (B) = TMP; } while (0)

#define ISORTLIM 10

#define CMPSWAP(TYPE,CMP,P,Q) \
do { if (CMP (&(P), &(Q)) > 0) SWAP (TYPE, P, Q); } while(0)

#define QPART(TYPE,CMP,A,L,R) \
do { \
  TYPE PIVOT; \
  int J = (R); \
  I = (L) - 1; \
  PIVOT = (A)[J]; \
  for (;;) { \
    while (CMP (&(A)[++I], &PIVOT) < 0) \
      ; \
    while (CMP (&PIVOT, &(A)[--J]) < 0) \
      if (J == (L)) break; \
    if (I >= J) break; \
    SWAP (TYPE, (A)[I], (A)[J]); \
  } \
  SWAP (TYPE, (A)[I], (A)[R]); \
} while(0)

#define QSORT(TYPE,CMP,A,N) \
do { \
  int L = 0, R = (N) - 1, M, LL, RR, I; \
  assert (lglmtstk (&lgl->sortstk)); \
  if (R - L <= ISORTLIM) break; \
  for (;;) { \
    M = (L + R) / 2; \
    SWAP (TYPE, (A)[M], (A)[R - 1]); \
    CMPSWAP (TYPE, CMP, (A)[L], (A)[R - 1]); \
    CMPSWAP (TYPE, CMP, (A)[L], (A)[R]); \
    CMPSWAP (TYPE, CMP, (A)[R - 1], (A)[R]); \
    QPART (TYPE, CMP, (A), L + 1, R - 1); \
    if (I - L < R - I) { LL = I + 1; RR = R; R = I - 1; } \
    else { LL = L; RR = I - 1; L = I + 1; } \
    if (R - L > ISORTLIM) { \
      assert (RR - LL > ISORTLIM); \
      lglpushstk (lgl, &lgl->sortstk, LL); \
      lglpushstk (lgl, &lgl->sortstk, RR); \
    } else if (RR - LL > ISORTLIM) L = LL, R = RR; \
    else if (!lglmtstk (&lgl->sortstk)) { \
      R = lglpopstk (&lgl->sortstk); \
      L = lglpopstk (&lgl->sortstk); \
    } else break; \
  } \
} while (0)

#define ISORT(TYPE,CMP,A,N) \
do { \
  TYPE PIVOT; \
  int L = 0, R = (N) - 1, I, J; \
  for (I = R; I > L; I--) \
    CMPSWAP (TYPE, CMP, (A)[I - 1], (A)[I]); \
  for (I = L + 2; I <= R; I++) { \
    J = I; \
    PIVOT = (A)[I]; \
    while (CMP (&PIVOT, &(A)[J - 1]) < 0) { \
      (A)[J] = (A)[J - 1]; \
      J--; \
    } \
    (A)[J] = PIVOT; \
  } \
} while (0)

#ifdef NDEBUG
#define CHKSORT(CMP,A,N) do { } while(0)
#else
#define CHKSORT(CMP,A,N) \
do { \
  int I; \
  for (I = 0; I < (N) - 1; I++) \
    assert (CMP (&(A)[I], &(A)[I + 1]) <= 0); \
} while(0)
#endif

#define SORT(TYPE,A,N,CMP) \
do { \
  TYPE * AA = (A); \
  const int NN = (N); \
  QSORT (TYPE, CMP, AA, NN); \
  ISORT (TYPE, CMP, AA, NN); \
  CHKSORT (CMP, AA, NN); \
} while (0)

#define SORTSTK(TYPE,S,CMP) \
do { \
  TYPE * A = (S)->start; \
  const int N = lglcntstk (S); \
  SORT (TYPE, A, N, CMP); \
} while (0)

/*------------------------------------------------------------------------*/

#define LGLPOPWTK(WTK,WRAG,LIT,OTHER,RED,REMOVED) \
do { \
  assert (!lglmtwtk (WTK)); \
  (WTK)->top--; \
  (WRAG) = (WTK)->top->wrag; \
  (LIT) = (WTK)->top->lit; \
  (OTHER) = (WTK)->top->other; \
  (RED) = (WTK)->top->red ? REDCS : 0; \
  (REMOVED) = (WTK)->top->removed; \
} while (0)

/*------------------------------------------------------------------------*/

#define CLONE(FIELD,SIZE) \
do { \
  NEW (lgl->FIELD, (SIZE)); \
  memcpy (lgl->FIELD, orig->FIELD, (SIZE) * sizeof *(lgl->FIELD)); \
} while (0)

#define CLONESTK(NAME) \
do { \
  size_t COUNT = orig->NAME.top - orig->NAME.start; \
  size_t SIZE = orig->NAME.end - orig->NAME.start; \
  size_t BYTES = SIZE * sizeof *lgl->NAME.start; \
  NEW (lgl->NAME.start, SIZE); \
  memcpy (lgl->NAME.start, orig->NAME.start, BYTES); \
  lgl->NAME.top = lgl->NAME.start + COUNT; \
  lgl->NAME.end = lgl->NAME.start + SIZE; \
} while (0)

/*------------------------------------------------------------------------*/

#define INCSTEPS(NAME) \
 ((lgl->stats->steps++), (lgl->stats->NAME++))

#define ADDSTEPS(NAME,INC) \
 ((lgl->stats->steps += INC), (lgl->stats->NAME += INC))

/*------------------------------------------------------------------------*/

#define LGLUPDPEN(NAME,SUCCESS) \
do { \
  assert (!lgl->limits->NAME.del.rem); \
  if ((SUCCESS) && lgl->limits->NAME.pen) \
    lgl->limits->NAME.pen--; \
  if (!(SUCCESS) && lgl->limits->NAME.pen < lgl->opts->penmax.val) \
    lgl->limits->NAME.pen++; \
  if ((SUCCESS) && lgl->limits->NAME.del.cur) \
    lgl->limits->NAME.del.cur /= 2; \
  if (!(SUCCESS) && lgl->limits->NAME.del.cur < lgl->opts->delmax.val) \
    lgl->limits->NAME.del.cur++; \
  lgl->limits->NAME.del.rem = lgl->limits->NAME.del.cur; \
} while (0)

/*-------------------------------------------------------------------------*/

#define RMSHFTLIT(LIT)		((int)(((unsigned)LIT)<<RMSHFT))

/*-------------------------------------------------------------------------*/

#define LGLL long long

/*-------------------------------------------------------------------------*/

typedef enum Tag {
  FREEVAR = 0,
  FIXEDVAR = 1,
  EQUIVAR = 2,
  ELIMVAR = 3,

  DECISION = 0,
  UNITCS = 1,
  OCCS = 1,
  BINCS = 2,
  TRNCS = 3,
  LRGCS = 4,
  MASKCS = 7,

  REDCS = 8,
  RMSHFT = 4,
} Tag;

typedef enum State {
  UNUSED 	= (1<<0),
  OPTSET 	= (1<<1),
  USED 		= (1<<2),
  READY		= (1<<3),
  UNKNOWN	= (1<<4),
  SATISFIED	= (1<<5),
  EXTENDED      = (1<<6),
  UNSATISFIED	= (1<<7),
  FAILED        = (1<<8),
  LOOKED        = (1<<9),
  RESET		= (1<<10),
} State;

typedef enum Wrag {
  PREFIX = 0,
  BEFORE = 1,
  AFTER = 2,
  POSTFIX = 3,
} Wrag;

typedef enum GTag { ANDTAG, ITETAG, XORTAG } GTag;

/*------------------------------------------------------------------------*/

typedef int Exp;
typedef uint64_t Mnt;
typedef int64_t Flt;
typedef int64_t Cnf;
typedef uint64_t Fun[FUNQUADS];
typedef signed char Val;
typedef Flt LKHD;

/*------------------------------------------------------------------------*/

typedef struct Conf { int lit, rsn[2]; } Conf;
typedef struct Ctk { struct Ctr * start, * top, * end; } Ctk;
typedef struct DFOPF { int observed, pushed, flag; } DFOPF;
typedef struct DFPR { int discovered, finished, parent, root; } DFPR;
typedef struct EVar { int occ[2], pos, score; } EVar;
typedef struct Ftk { Flt * start, * top, * end; } Ftk;
typedef struct HTS { int offset, count; }  HTS;
typedef struct Lim { int64_t confs, decs, props; } Lim;
typedef struct PAGSL { int psm, act, glue, size, lidx; } PAGSL;
typedef struct PSz { int pos, size; } PSz;
typedef struct RNG { unsigned z, w; } RNG;
typedef struct Stk { int * start, * top, * end; } Stk;
typedef struct Timer { double start; int idx, ign; } Timer;
typedef struct Timers { Timer stk[MAXPHN]; int nest; } Timers;
typedef struct Trv { void * state; void (*trav)(void *, int); } Trv;
typedef struct TVar { signed int val : 30; unsigned mark : 2; } TVar;
typedef struct Wtk { struct Work * start, * top, * end; } Wtk;

/*------------------------------------------------------------------------*/

typedef struct EMA {
  int shift, count;
  int64_t val;
} EMA;

typedef struct AVG {
  int64_t val, count;
} AVG;

#ifndef NLGLDEMA

typedef struct DEMA {
  EMA ema[2];
  int64_t val;
} DEMA;

#define MACDEMA DEMA
#define lglinitmacdema lglinitdema
#define lglupdatemacdema lglupdatedema

#else

#define MACDEMA EMA
#define lglinitmacdema lglinitema
#define lglupdatemacdema(A,B,C) lglupdatema(A,B,C,1)

#endif

typedef struct MACD {
  MACDEMA fast, slow;
  struct { int64_t actual; EMA smoothed; } diff;
} MACD;

/*------------------------------------------------------------------------*/

typedef struct Ctr { 
  signed int decision : 28; 
  unsigned used : 2;
  unsigned used2 : 2;
} Ctr;

typedef struct DVar { HTS hts[2]; } DVar;

#define GLAGBITS 31
#define MAXGLAG ((1<<(GLAGBITS-1)) - 1)

typedef struct QVar {
  Flt score;
  unsigned enqueued:1;
  signed int glag:GLAGBITS;
  int pos;
} QVar;

typedef struct TD {
  signed int level:30;
  unsigned lrglue:1, irr:1; 
  int rsn[2];
} TD;

typedef struct AVar {
  unsigned type : 4;
#ifndef NDEBUG
  unsigned simp:1, wasfalse:1;
#endif
  unsigned equiv:1, lcamark:4;
  signed int phase:2, bias:2, fase:2;
  unsigned inred:2, poisoned:1, assumed:2, failed:2;
  unsigned donotelm:1, donotblk:1, donoternres:1;
  unsigned donotbasicprobe:1, donotsimpleprobe:1, donotreelook:1, donotsweep:1;
#ifndef NLGLYALSAT
  signed int locsval:2;
#endif
  int mark, trail;
} AVar;

typedef struct Ext {
  unsigned equiv:1,melted:1,blocking:2,eliminated:1,tmpfrozen:1,imported:1;
  unsigned assumed:2,failed:2,aliased:1;
  signed int val:2, oldval:2;
  int repr, frozen;
} Ext;

typedef struct Work {
  unsigned wrag : 2;
  signed int lit : 30, other : 30;
  unsigned red : 1, removed : 1;
} Work;

typedef struct DFL {
  int discovered, finished;
  union { int lit, sign; };
#ifndef NLGLOG
  int lit4logging;
#endif
} DFL;

/*------------------------------------------------------------------------*/

#define FEATURES \
FEATURE(n) \
FEATURE(s) \
FEATURE(vo) \
FEATURE(vc) \
FEATURE(co) \
FEATURE(cc) \
FEATURE(b) \
FEATURE(t) \
FEATURE(q) \
FEATURE(c1) \
FEATURE(c2) \
FEATURE(c3) \
FEATURE(c4) \
FEATURE(x) \
FEATURE(a1) \
FEATURE(a2) \
FEATURE(g) \
FEATURE(j) \
FEATURE(c) \
FEATURE(o)

typedef struct Features {
#define FEATURE(NAME) int NAME;
FEATURES
} Features;

#define NFEATURES (sizeof (Features) / sizeof (int))

#undef FEATURE
#define FEATURE(NAME) #NAME,

static const char * featurenames[] = {
  FEATURES
};

/*------------------------------------------------------------------------*/

typedef struct Stats {
  int64_t agility;
  int64_t steps, trims, bins, trns, times;
  int defrags, reported, features, repcntdown, gcs, decomps;
  struct { int clauses, vars; } rescored;
  struct { int64_t count, checked, skipped, forced;
	   int64_t agile, delayed, blocked, notforced, reused;
	   struct { int64_t count, pen, delta; } delta;
	   struct { int64_t count, sum; } kept; } restarts;
  struct { int count, arith, memlim;
           int64_t collected, retired; } reduced;
  int64_t prgss, irrprgss, enlwchs, pshwchs, dense, sparse;
  int64_t confs, decisions, hdecs, qdecs, randecs, uips, decflipped;
  MACD glue, jlevel;
  EMA tlevel;
  AVG avglue;
  struct { MACD avg; int count; } its;
  struct {
    struct { int cur, max; int64_t add; } clauses, lits;
    int64_t maxbytes;
  } irr;
  struct { int64_t sat, mosat, simp, deref, fixed, freeze, lkhd;
	   int64_t melt, add, assume, cassume, failed, repr; } calls;
  struct { int64_t search, simp, lkhd; } props, visits;
  struct { size_t current, max; } bytes;
  struct { int bin, trn, lrg; } red;
  struct { int cnt, simple, trn, lrg, sub; } hbr;
  struct { int current, sum; } fixed, equiv;
  struct { int count, bin, trn; int64_t steps; } ternres;
  struct { int count, clauses, lits, pure; int64_t res, steps; } blk;
  struct {
    struct { int count, failed, eqs; int64_t probed, steps; } simple;
    struct { int count, failed, lifted; 
             int64_t probed, steps, lastate;
	     struct { int trnr, lrg, count; } ate; } basic;
    struct { int count, failed, lifted; int64_t probed, steps; } treelook;
  } prb;
  struct { int count, red, failed; int64_t lits, bins, steps; } trd;
  struct { int removed, red; } bindup;
  struct { int count, rounds;
	   struct { int trds, failed, sccs; int64_t sumsccsizes; } stamp;
	   struct { int lits, bin, trn, lrg; } failed;
	   struct { int bin, trn, lrg, red; } tauts;
	   struct { int bin, trn, lrg; } units;
	   struct { int trn, lrg, red; } hbrs, str;
	   int64_t steps; } unhd;
  struct {
    int count, elmd, pure, large, sub, str, blkd, rounds;
    struct { int elm, tried, failed; } small;
    int64_t resolutions, copies, subchks, strchks, ipos, steps; } elm;
  struct {
    int sub2, sub3, subl, str2, str3, str3self, strl, strlself;
    struct { int64_t lits, clauses, occs; } tried;
    int64_t steps;
  } bkwd;
  struct {
    struct { int64_t irr, red, bin, trn, lrg; } sub, str;
    int64_t driving, restarting, total; } otfs;
  struct { int64_t nonmin, learned; } lits;
  struct { 
    int64_t learned, glue, realglue, nonmaxglue, scglue;
    struct { int64_t count, kept; } maxglue;
  } clauses;
  struct {
    int clauses;
    int64_t added, reduced, retired, resolved, forcing, conflicts;
    int64_t maxbytes;
  } lir[POW2GLUE];
  struct { int count; int64_t set, pos, neg; } phase;
  struct {
    int count;
    struct { int confs, irr, vars, its, bin, trn; } limhit;
  } simp;
  struct { int count, gcs, units, equivs, trneqs; 
           struct { struct { int total, last; } max; int64_t sum; } arity; 
	   struct { int64_t extr, elim; } steps;
	   struct { int64_t total, last; } extracted; } gauss;
  struct { int count, eliminated, ate, abce, failed, lifted;
           int64_t steps, probed;
	   struct { int64_t search, hits, cols, ins, rsz; } cache; } cce;
  struct { 
    int count, units, expam1, resched;
    int64_t steps, eliminated, resolved, subsumed;
    struct {
      struct {
	struct { int64_t sum, cnt; int max; } total;
	struct { int cnt, max; } last;
      } am1, am2;
    } found;
    struct { struct { int64_t sum, cnt; } am1, am2; } used;
    } card;
  struct { int64_t bin, trn; } moved;
  struct { int count; int64_t added, skipped, steps; } bca;
  struct { 
    struct {
      int64_t produced; 
      struct { int64_t actual, tried, calls; } consumed;
    } cls, units;
  } sync;
  struct { struct { int64_t orig, red; } sum; } deco;
  struct {
    int64_t min, bin, size, deco;
    struct { int64_t search, hits; } poison;
    struct { int64_t search, hits; } usedtwice;
  } mincls;
  struct {
     struct { int64_t tried, red, sat; } cls, lits;
     struct { int64_t red, sum; } jlevel; } redcls;
  int64_t drupped, druplig;
  struct { int64_t count, tried, cands, sub; } subl;
  struct { int count; int64_t flips, mems; int min; } locs;
  struct {
    int count, failed, impls, equivs;
    int64_t rounds, steps, cached, sat, unsat, decs, confs;
    struct { int64_t classes, envs; } sumsize;
    struct { int64_t total;
	     struct { int64_t count, sat, unsat; } type[3]; } queries;
  } sweep;
  struct { int64_t count; int max, min; } setscincf;
  struct { int64_t tried, locked; } promote;
  struct { int count; int64_t quat, self1, self2, dup; } quatres;
  struct { int64_t flushed, sorted; } queue;
  struct { int64_t count, lits; } bump;
  struct { int64_t count; EMA avg; int changed, level; } stability;
} Stats;

/*------------------------------------------------------------------------*/

typedef struct Times {
    double all, search, preprocessing, inprocessing;            // level 0
    double lookahead;///PUT NOTHING HERE!                       // level 0
#define TIMESLEVEL0     lookahead
    double elim, transred, block, unhide, ternres;              // level 1
    double gauss, quatres, card, cce, bca, locs, sweep;         // level 1
    double showscoredist, showfeatures;                         // level 1
    double probe;///////PUT NOTHING HERE!                       // level 1
#define TIMESLEVEL1     probe
    struct { double simple, basic, treelook; } prb;             // level 2
    double quatres1, quatres2;                                  // level 2
    double gc, decompose, queuesort, phase;                     // level 2
    double backward;////PUT NOTHING HERE!                       // level 2
#define TIMESLEVEL2     backward
    double restart, defrag;                                     // level 3
    double reduce;//////PUT NOTHING HERE!                       // level 3
#define TIMESLEVEL3     reduce
    double analysis, decide, bump, mincls, druplig;             // level 4
    double redcls, queuedecision, heapdecision, subl;           // level 4
} Times;

#define TIMESLEVEL0IDX (&(((Times*)0)->TIMESLEVEL0)- &((Times*)0)->all)
#define TIMESLEVEL1IDX (&(((Times*)0)->TIMESLEVEL1)- &((Times*)0)->all)
#define TIMESLEVEL2IDX (&(((Times*)0)->TIMESLEVEL2)- &((Times*)0)->all)
#define TIMESLEVEL3IDX (&(((Times*)0)->TIMESLEVEL3)- &((Times*)0)->all)

/*------------------------------------------------------------------------*/

typedef struct Del { int cur, rem; } Del;

typedef struct Limits {
  int lkhdpen;
  int64_t randec, dfg;
  struct {
    int64_t visits;
    struct { int64_t add; int start; } clauses;
    struct { int start; } vars;
  } inc;
  struct { struct { int64_t otfs, confs; } vars; } rescore;
  struct { int pen; Del del; int64_t steps, irrprgss; } elm, blk;
  struct { int pen; Del del; int64_t steps; }
    trd, unhd, ternres, quatres, cce, card, sweep;
  struct { int pen; Del del; struct { int64_t extr, elim; } steps; } gauss;
  struct { int64_t confs; } restart;
  struct { int64_t steps; 
           struct { int pen; Del del; } simple, basic, treelook; } prb;
  struct {
    int64_t confs, hard, vars, its, bin, trn;
    int cinc, itinc, binc, tinc; } simp;
  struct { int64_t steps, confs; } sync;
  struct { int64_t steps; } term;
  struct { int64_t fixed; } gc;
  struct { Del del; int64_t steps, added; } bca;
  struct { int64_t steps, time; } trep;
  struct { int64_t confs, inc; int vars; } locs;
  struct { int redlarge; } reduce;
} Limits;

/*------------------------------------------------------------------------*/

typedef struct Cbs {
  struct { int (*fun)(void*); void * state; int done; } term;
  struct {
    struct { void (*fun)(void*,int); void * state; } produce, consumed;
    struct { void(*fun)(void*,int**,int**); void*state; } consume;
  } units;
  struct {
    struct { void (*fun)(void*,int*,int); void * state; } produce;
    struct { void(*fun)(void*,int**,int*); void*state; } consume;
    struct { void (*fun)(void*,int); void * state; } consumed;
  } cls;
  struct {
    struct { int * (*fun)(void*); void * state; } lock;
    struct { void (*fun)(void*,int,int); void * state; } unlock;
  } eqs;
  struct { void(*lock)(void*); void (*unlock)(void*); void*state; } msglock;
  double (*getime)(void);
  void (*onabort)(void *); void * abortstate;
} Cbs;

typedef struct BCA { Stk covered; } BCA;

typedef struct Dis { struct { Stk bin, trn; } red, irr; } Dis;

typedef struct Elm {
  int64_t oldsteps;
  int pivot, negcls, necls, neglidx, round, oldelmd;
  Stk lits, next, clv, csigs, sizes, occs, noccs, mark, m2i;
  struct { Stk stk; int * pos, mt, nvars; } touched;
  int bkwdocclim;
} Elm;

typedef struct Card {
  Stk atmost1, atmost2, cards, elim, * occs, units, expam1;
  char * eliminated, * lit2used, * marked;
  signed char * count;
  int * lit2count;
} Card;

typedef struct FltStr { int current; char str[MAXFLTSTR][100]; } FltStr;

typedef struct SPE { signed int count : 31; unsigned mark : 1, sum; } SPE;

typedef struct SPrb { 
  Stk units, impls, eqs, counted, marked;
  SPE * spes;
} SPrb;

typedef struct Gauss { 
  Stk xors, order, * occs; 
  signed char * eliminated;
  int garbage, next; 
} Gauss;

typedef struct CCE {
  Stk cla, extend, clauses;
  int * rem, bin, trn;
} CCE;

typedef struct SWP {
  int partitions, round, query, sat, type;
  Stk partition;
  struct { int64_t classes, envs; } sumsize;
  struct { int count; struct { int a, b; } cached; Stk stk; } decision;
} SWP;

typedef struct Tlk { Stk stk, seen; TVar * tvars; LKHD * lkhd; } Tlk;

typedef struct Mem {
  void * state;
  lglalloc alloc; lglrealloc realloc; lgldealloc dealloc;
} Mem;

typedef struct Wchs { Stk stk; int start[MAXLDFW], free; } Wchs;

typedef struct Wrk {
  Stk queue;
  int count, head, size, posonly, fifo, * pos;
} Wrk;

typedef struct Queue { Stk stk; int mt, next, sorted; } Queue;

/*------------------------------------------------------------------------*/

struct LGL {
  State state;

  int probing, tid, tids;
  int nvars, szvars, maxext, szext, changed, mt, repcntdown;
  int szdrail, next, next2, flushed, level, alevel, wait, glag;
  int unassigned, lrgluereasons, failed, assumed;

  Flt scinc, scincf, maxscore, minscore;
  int scincinc;

  char cceing, gaussing, bcaing, repforcehead, quatres, notrim;
  char searching, simp, allphaseset, flushphases, occs;
  char unhiding, basicprobing, simpleprobing, treelooking, setuponce;
  char eliminating, donotsched, blocking, ternresing, lkhd, allfrozen;
  char blkall, blkrem, blkrtc, elmall, elmrem, elmrtc, sweeprtc, decomposing;
  char frozen, dense, rmredbintrn, notfullyconnected, forcegc, allowforce;
  char ccertc, touching, sweeping;

  int64_t confatlastit;

  LGL * parent;
  int forked;

  Conf conf;
  RNG rng;

  // the state above this line is copied during 'clone' with 'memcpy'

  Mem * mem;
  Opts * opts;
  Stats * stats;
  Times * times;
  Timers * timers;
  Limits * limits;
  Ext * ext;
  int * i2e;
  int * doms;
  DVar * dvars;
  QVar * qvars;
  AVar * avars;
  Val * vals;
  Flt * jwh;
  TD * drail;
  Stk * red;
  Wchs * wchs;

  Ctk control;
#ifndef NDEBUG
  Stk prevclause;
  int prevglue;
#endif
  Stk clause, eclause, extend, irr, trail, frames, promote;
  Stk eassume, assume, learned;
  Stk dsched;
#ifndef NCHKSOL
  Stk orig;
#endif
  Queue queue;

  union {
    Elm * elm; SPrb * sprb; Tlk * tlk; Gauss * gauss;
    CCE * cce; BCA * bca; Card * card; SWP * swp;
  };
  union { Stk lcaseen, sortstk; };
  Stk poisoned, seen, esched, minstk, resolvent;
  struct { Stk bin, trn; } saved;
  EVar * evars;
  Dis * dis;
  Wrk * wrk;
  int * repr;

  char closeapitrace;
  FILE * out, * apitrace;
  char * prefix;
  Cbs * cbs;

  LGL * clone;

  FltStr * fltstr;
#if !defined(NLGLDRUPLIG)
  Druplig * druplig;
  int drupligunit;
#endif
};

/*-------------------------------------------------------------------------*/

#define LT(n) n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n

static const char lglfloorldtab[256] =
{
// 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
  -1, 0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3,
  LT(4), LT(5), LT(5), LT(6), LT(6), LT(6), LT(6),
  LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7)
};

static const uint64_t lglbasevar2funtab[6] = {
  0xaaaaaaaaaaaaaaaaull, 0xccccccccccccccccull, 0xf0f0f0f0f0f0f0f0ull,
  0xff00ff00ff00ff00ull, 0xffff0000ffff0000ull, 0xffffffff00000000ull,
};

/*-------------------------------------------------------------------------*/

static int lglfloorld (int n) {
  assert (n >= 0);
  if (n < (1<<8)) return lglfloorldtab[n];
  if (n < (1<<16)) return 8 + lglfloorldtab[n>>8];
  if (n < (1<<24)) return 16 + lglfloorldtab[n>>16];
  return 24 + lglfloorldtab[n>>24];
}

static int lglispow2 (int n) {
  assert (0 <= n && n <= INT_MAX);
  return !(n & (n - 1));
}

static int lglceild (int n) {
  int res = lglfloorld (n);
  if (!lglispow2 (n)) res++;
  return res;
}

static void lglchkflt (Flt a) {
#ifndef NDEBUG
  assert (a >= 0);
  assert (FLTMAX >= (uint64_t) a);
#else
  (void) a;
#endif
}

static Exp lglexp (Flt a) {
  Flt tmp = a >> FLTPRC;
  Exp res = tmp;
  assert (0 <= res && res <= EXPMAX);
  res -= EXPZRO;
  return res;
}

static Mnt lglmnt (Flt a) {
  Mnt res = a & MNTMAX;
  res |= MNTBIT;
  assert (res <= MNTMAX);
  return res;
}

static Flt lglflt (Exp e, Mnt m) {
  Flt res;
  if (!m) return FLTMIN;
  if (m < MNTBIT) {
    while (!(m & MNTBIT)) {
      m <<= 1;
      if (e > INT_MIN) e--;
      else break;
    }
  } else {
    while (m > MNTMAX) {
       m >>= 1;
       if (e > INT_MIN) e++;
       else break;
    }
  }
  if (e < -EXPZRO) return FLTMIN;
  if (e > EXPMAX - EXPZRO) return FLTMAX;
  e += EXPZRO;
  assert (0 <= e && e <= EXPMAX);
  assert (m <= MNTMAX);
  assert (m & MNTBIT);
  res = m & ~MNTBIT;
  res |= ((Flt)e) << FLTPRC;
  return res;
}

static Flt lglrat (unsigned n, unsigned d) {
  Mnt m;
  Exp e;
  if (!n) return FLTMIN;
  if (!d) return FLTMAX;
  m = n;
  e = 0;
  while (!(m & (1ull << 63))) m <<= 1, e--;
  m /= d;
  return lglflt (e, m);
}

#ifndef NDEBUG
double lglflt2dbl (Flt a) {
  return lglmnt (a) * pow (2.0, lglexp (a));
}
#endif

static const char * lglflt2str (LGL * lgl, Flt a) {
  double d, e;
  assert (lgl->fltstr);
  if (a == FLTMIN) return "0";
  if (a == FLTMAX) return "inf";
  d = lglmnt (a);
  d /= 4294967296ll;
  e = lglexp (a);
  e += 32;
  lgl->fltstr->current++;
  if (lgl->fltstr->current == MAXFLTSTR) lgl->fltstr->current = 0;
  sprintf (lgl->fltstr->str[lgl->fltstr->current], "%.6fd%+03.0f", d, e);
  return lgl->fltstr->str[lgl->fltstr->current];
}

static Flt lgladdflt (Flt a, Flt b) {
  Exp e, f, g;
  Mnt m, n, o;
  lglchkflt (a);
  lglchkflt (b);
  if (a == FLTMAX) return FLTMAX;
  if (b == FLTMAX) return FLTMAX;
  if (a == FLTMIN) return b;
  if (b == FLTMIN) return a;
  e = lglexp (a);
  f = lglexp (b);
  if (e < f) g = e, e = f, f = g, o = a, a = b, b = o;
  m = lglmnt (a);
  n = lglmnt (b);
  if (e - f < sizeof (m) * 8) m += n >> (e - f);
  return lglflt (e, m);
}

static Flt lglmulflt (Flt a, Flt b) {
  Exp e, ea, eb;
  Mnt m, ma, mb;
  lglchkflt (a);
  lglchkflt (b);
  if (a == FLTMAX) return FLTMAX;
  if (b == FLTMAX) return FLTMAX;
  if (a == FLTMIN) return FLTMIN;
  if (b == FLTMIN) return FLTMIN;
  ea = lglexp (a); eb = lglexp (b);
  if (ea > 0 && eb > 0 && (INT_MAX - ea < eb)) return FLTMAX;
  e = ea + eb;
  if (e > EXPMAX - EXPZRO - 32) return FLTMAX;
  e += 32;
  ma = lglmnt (a); mb = lglmnt (b);
  ma >>= 1; mb >>= 1;
  m = ma * mb;
  assert (3ull << 62);
  m >>= 30;
  return lglflt (e, m);
}

static Flt lglshflt (Flt a, int s) {
  Exp e;
  Mnt m;
  if (a == FLTMAX) return FLTMAX;
  if (a == FLTMIN) return FLTMIN;
  assert (0 <= s);
  e = lglexp (a);
  if (e < INT_MIN + s) return FLTMIN;
  e -= s;
  m = lglmnt (a);
  return lglflt (e, m);
}

static const char * lglscr2str (LGL * lgl, Flt scr) {
  return lglflt2str (lgl, scr);
}

static void lglwrn (LGL * lgl, const char * msg, ...) {
  va_list ap;
  fprintf (lgl->out, "*** warning in '%s': ", __FILE__);
  va_start (ap, msg);
  vfprintf (lgl->out, msg, ap);
  va_end (ap);
  fputc ('\n', lgl->out);
  fflush (lgl->out);
}

static void lgldie (LGL * lgl, const char * msg, ...) {
  va_list ap;
  fprintf (lgl->out, "*** internal error in '%s': ", __FILE__);
  va_start (ap, msg);
  vfprintf (lgl->out, msg, ap);
  va_end (ap);
  fputc ('\n', lgl->out);
  fflush (lgl->out);
  exit (0);
}

static void lglabort (LGL * lgl) {
  if (!lgl) exit (1);
  if (lgl->opts && lgl->opts->sleeponabort.val) {
    fprintf (stderr,
"liblgl.a: Process %d will sleep for %d seconds "
" before continuing with 'lglabort' procedure.\n",
      getpid (), lgl->opts->sleeponabort.val);
    fflush (stderr);
    sleep (lgl->opts->sleeponabort.val);
  }
  if (lgl->cbs && lgl->cbs->onabort)
    lgl->cbs->onabort (lgl->cbs->abortstate);
  if (lgl->opts && lgl->opts->exitonabort.val) exit (1);
  abort ();
}

static const char * lglprefix (LGL * lgl) {
  return lgl && lgl->prefix ? lgl->prefix : "c (LGL HAS NO PREFIX YET) ";
}

static int lglmsgstart (LGL * lgl, int level) {
#ifndef NLGLOG
  if (lgl->opts->log.val <= 0)
#endif
  if (lgl->opts->verbose.val < level) return 0;
  if (lgl->cbs && lgl->cbs->msglock.lock)
    lgl->cbs->msglock.lock (lgl->cbs->msglock.state);
  fputs (lglprefix (lgl), lgl->out);
  if (lgl->tid >= 0) fprintf (lgl->out, "%d ", lgl->tid);
  return 1;
}

static void lglmsgend (LGL * lgl) {
  fputc ('\n', lgl->out);
  fflush (lgl->out);
  if (lgl->cbs && lgl->cbs->msglock.unlock)
    lgl->cbs->msglock.unlock (lgl->cbs->msglock.state);
}

static void lglprt (LGL * lgl, int level, const char * msg, ...) {
  va_list ap;
#ifndef NLGLOG
  if (lgl->opts->log.val <= 0)
#endif
  if (lgl->opts->verbose.val < level) return;
  lglmsgstart (lgl, level);
  va_start (ap, msg);
  vfprintf (lgl->out, msg, ap);
  va_end (ap);
  lglmsgend (lgl);
}

#ifndef NLGLOG
static void lglogstart (LGL * lgl, int level, const char * msg, ...) {
  va_list ap;
  assert (lgl->opts->log.val >= level);
  if (lgl->cbs && lgl->cbs->msglock.lock)
    lgl->cbs->msglock.lock (lgl->cbs->msglock.state);
  fputs (lglprefix (lgl), lgl->out);
  if (lgl->tid >= 0) fprintf (lgl->out, "%d ", lgl->tid);
  fprintf (lgl->out, "LOG%d %d ", level, lgl->level);
  va_start (ap, msg);
  vfprintf (lgl->out, msg, ap);
  va_end (ap);
}

#define lglogend lglmsgend
#endif

/*------------------------------------------------------------------------*/

double lglprocesstime (void) {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

static double lglgetime (LGL * lgl) {
  lgl->stats->times++;
  if (lgl->cbs && lgl->cbs->getime) return lgl->cbs->getime ();
  else return lglprocesstime ();
}

static int lglprofidx (LGL * lgl, double * timestatsptr) {
  int res;
  assert ((double*) lgl->times <= timestatsptr);
  assert (timestatsptr < (double*)(sizeof *lgl->times + (char*) lgl->times));
  res = timestatsptr - (double*) lgl->times;
  return res;
}

static int lglignprofidx (LGL * lgl, int idx) {
  int res;
  assert (0 <= idx);
  assert (idx < sizeof (Times)/sizeof(double));
  switch (lgl->opts->profile.val) {
    case 0:  res = (TIMESLEVEL0IDX < idx); break;
    case 1:  res = (TIMESLEVEL1IDX < idx); break;
    case 2:  res = (TIMESLEVEL2IDX < idx); break;
    case 3:  res = (TIMESLEVEL3IDX < idx); break;
    default: res = 0;                      break;
  }
  return res;
}

static int lglignprofptr (LGL * lgl, double * timestatsptr) {
  return lglignprofidx (lgl, lglprofidx (lgl, timestatsptr));
}

static void lglstart (LGL * lgl, double * timestatsptr) {
  Timer * timer;
  int ign, idx;
  idx = lglprofidx (lgl, timestatsptr);
  ign = lglignprofidx (lgl, idx);
  assert (lgl->timers->nest < MAXPHN);
  timer = lgl->timers->stk + lgl->timers->nest++;
  timer->idx = idx;
  if ((timer->ign = ign)) timer->start = 0;
  else timer->start = lglgetime (lgl);
}

void lglflushtimers (LGL * lgl) {
  double time = lglgetime (lgl), delta, entered, * ptr;
  Timer * timer;
  int nest;
  for (nest = 0; nest < lgl->timers->nest; nest++) {
    timer = lgl->timers->stk + nest;
    if (timer->ign) continue;
    entered = timer->start;
    timer->start = time;
    delta = time - entered;
    if (delta < 0) delta = 0;
    ptr = timer->idx + (double*)lgl->times;
    *ptr += delta;
  }
}

double lglsec (LGL * lgl) {
  REQINIT ();
  lglflushtimers (lgl);
  return lgl->times->all;
}

static void lglstop (LGL * lgl) {
  Timer * timer;
  assert (lgl->timers->nest > 0);
  timer = lgl->timers->stk + lgl->timers->nest - 1;
  if (!timer->ign) lglflushtimers (lgl);
  lgl->timers->nest--;
  assert (lgl->timers->nest >= 0);
}

/*------------------------------------------------------------------------*/

void lglsetid (LGL * lgl, int tid, int tids) {
  REQINITNOTFORKED ();
  ABORTIF (tid < 0, "negative id");
  ABORTIF (tid >= tids, "id exceed number of ids");
  lgl->tid = tid;
  lgl->tids = tids;
}

/*------------------------------------------------------------------------*/

static void lglinc (LGL * lgl, size_t bytes) {
  lgl->stats->bytes.current += bytes;
  if (lgl->stats->bytes.max < lgl->stats->bytes.current) {
    lgl->stats->bytes.max = lgl->stats->bytes.current;
    LOG (5, "maximum allocated %ld bytes", lgl->stats->bytes.max);
  }
}

static void lgldec (LGL * lgl, size_t bytes) {
  assert (lgl->stats->bytes.current >= bytes);
  lgl->stats->bytes.current -= bytes;
}

static void * lglnew (LGL * lgl, size_t bytes) {
  void * res;
  if (!bytes) return 0;
  if (lgl->mem->alloc) res = lgl->mem->alloc (lgl->mem->state, bytes);
  else res = malloc (bytes);
  if (!res) lgldie (lgl, "out of memory allocating %ld bytes", bytes);
  assert (res);
  LOG (5, "allocating %p with %ld bytes", res, bytes);
  lglinc (lgl, bytes);
  if (res) memset (res, 0, bytes);
  return res;
}

static void lgldel (LGL * lgl, void * ptr, size_t bytes) {
  if (!ptr) { assert (!bytes); return; }
  lgldec (lgl, bytes);
  LOG (5, "freeing %p with %ld bytes", ptr, bytes);
  if (lgl->mem->dealloc) lgl->mem->dealloc (lgl->mem->state, ptr, bytes);
  else free (ptr);
}

static void * lglrsz (LGL * lgl, void * ptr, size_t old, size_t new) {
  void * res;
  assert (!ptr == !old);
  if (!ptr) return lglnew (lgl, new);
  if (!new) { lgldel (lgl, ptr, old); return 0; }
  if (old == new) return ptr;
  lgldec (lgl, old);
  if (lgl->mem->realloc)
    res = lgl->mem->realloc (lgl->mem->state, ptr, old, new);
  else res = realloc (ptr, new);
  if (!res)
    lgldie (lgl, "out of memory reallocating %ld to %ld bytes", old, new);
  assert (res);
  LOG (5, "reallocating %p to %p from %ld to %ld bytes", ptr, res, old, new);
  lglinc (lgl, new);
  if (new > old) memset (res + old, 0, new - old);
  return res;
}

/*------------------------------------------------------------------------*/

static char * lglstrdup (LGL * lgl, const char * str) {
  char * res;
  NEW (res, strlen (str) + 1);
  return strcpy (res, str);
}

static void lgldelstr (LGL * lgl, char * str) {
  DEL (str, strlen (str) + 1);
}

/*------------------------------------------------------------------------*/

static void lglinitcbs (LGL * lgl) {
  if (!lgl->cbs) NEW (lgl->cbs, 1);
}

void lglonabort (LGL * lgl, void * abortstate, void (*onabort)(void*)) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->abortstate = abortstate;
  lgl->cbs->onabort = onabort;
}

void lglseterm (LGL * lgl, int (*fun)(void*), void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->term.fun = fun;
  lgl->cbs->term.state = state;
}

void lglsetproduceunit (LGL * lgl, void (*fun) (void*, int), void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->units.produce.fun = fun;
  lgl->cbs->units.produce.state = state;
}

void lglsetconsumeunits (LGL * lgl,
			 void (*fun) (void*, int **, int **),
			 void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->units.consume.fun =  fun;
  lgl->cbs->units.consume.state = state;
}

void lglsetconsumedunits (LGL * lgl,
			  void (*fun) (void*, int), void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->units.consumed.fun = fun;
  lgl->cbs->units.consumed.state = state;
}

void lglsetproducecls (LGL * lgl, 
                       void (*fun) (void*, int *, int), void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->cls.produce.fun = fun;
  lgl->cbs->cls.produce.state = state;
}

void lglsetconsumecls (LGL * lgl,
		       void (*fun) (void*, int **, int *),
		       void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->cls.consume.fun =  fun;
  lgl->cbs->cls.consume.state = state;
}

void lglsetconsumedcls (LGL * lgl,
			void (*fun) (void*, int), void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->cls.consumed.fun = fun;
  lgl->cbs->cls.consumed.state = state;
}

void lglsetlockeq (LGL * lgl, int * (*fun)(void*), void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->eqs.lock.fun = fun;
  lgl->cbs->eqs.lock.state = state;
}

void lglsetunlockeq (LGL * lgl, void (*fun)(void*,int,int), void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->eqs.unlock.fun = fun;
  lgl->cbs->eqs.unlock.state = state;
}

void lglsetmsglock (LGL * lgl,
		    void (*lock)(void*), void (*unlock)(void*),
		    void * state) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->msglock.lock = lock;
  lgl->cbs->msglock.unlock = unlock;
  lgl->cbs->msglock.state = state;
}

void lglsetime (LGL * lgl, double (*time)(void)) {
  REQINITNOTFORKED ();
  lglinitcbs (lgl);
  lgl->cbs->getime = time;
}

/*------------------------------------------------------------------------*/

static int lglfullstk (Stk * s) { return s->top == s->end; }
static int lglmtstk (Stk * s) { return s->top == s->start; }
static size_t lglcntstk (Stk * s) { return s->top - s->start; }
static size_t lglszstk (Stk * s) { return s->end - s->start; }

static int lglpeek (Stk * s, int pos) {
  assert (0 <= pos && pos < lglszstk (s));
  return s->start[pos];
}

static void lglpoke (Stk * s, int pos, int val) {
  assert (0 <= pos && pos <= lglszstk (s));
  s->start[pos] = val;
}

static void lglenlstk (LGL * lgl, Stk * s) {
  size_t old_size = lglszstk (s);
  size_t new_size = old_size ? 2 * old_size : 1;
  size_t count = lglcntstk (s);
  RSZ (s->start, old_size, new_size);
  s->top = s->start + count;
  s->end = s->start + new_size;
}

static void lglrelstk (LGL * lgl, Stk * s) {
  DEL (s->start, lglszstk (s));
  CLRPTR (s);
}

static void lglshrstk (LGL * lgl, Stk * s, int new_size) {
  size_t old_size, count = lglcntstk (s);
  assert (new_size >= 0);
  assert (count <= new_size);
  if (new_size > 0) {
    old_size = lglszstk (s);
    RSZ (s->start, old_size, new_size);
    s->top = s->start + count;
    s->end = s->start + new_size;
  } else lglrelstk (lgl, s);
}

static void lglfitstk (LGL * lgl, Stk * s) {
  lglshrstk (lgl, s, lglcntstk (s));
}

static void lglpushstk (LGL * lgl, Stk * s, int elem) {
  if (lglfullstk (s)) lglenlstk (lgl, s);
  *s->top++ = elem;
}

static void lglrmstk (Stk * s, int elem) {
  int * p, * q;
  for (p = s->start; p < s->top; p++)
    if (*p == elem) break;
  assert (p < s->top);
  q = p++;
  while (p < s->top)
    *q++ = *p++;
  s->top = q;
}

static int lglpopstk (Stk * s) { assert (!lglmtstk (s)); return *--s->top; }

static int lgltopstk (Stk * s) { assert (!lglmtstk (s)); return s->top[-1]; }

static void lglrststk (Stk * s, int newsz) {
  assert (0 <= newsz && newsz <= lglcntstk (s));
  s->top = s->start + newsz;
}

static void lglclnstk (Stk * s) { lglrststk (s, 0); }

/*------------------------------------------------------------------------*/

static void lgltrapi (LGL * lgl, const char * msg, ...) {
  va_list ap;
  assert (lgl->apitrace);
  va_start (ap, msg);
  vfprintf (lgl->apitrace, msg, ap);
  va_end (ap);
  fputc ('\n', lgl->apitrace);
  if (lgl->opts->trapiflush.val) fflush (lgl->apitrace);
}

static void lglopenapitrace (LGL * lgl, const char * name) {
  FILE * file;
  char * cmd;
  int len;
  len = strlen (name);
  if (len >= 3 && !strcmp (name + len - 3, ".gz")) {
    len += 20;
    NEW (cmd, len);
    sprintf (cmd, "gzip -c > %s", name);
    file = popen (cmd, "w");
    DEL (cmd, len);
    if (file) lgl->closeapitrace = 2;
  } else {
    file = fopen (name, "w");
    if (file) lgl->closeapitrace = 1;
  }
  if (file) lgl->apitrace = file;
  else lglwrn (lgl, "can not write API trace to '%s'", name);
  TRAPI ("init");
}

void lglwtrapi (LGL * lgl, FILE * apitrace) {
  REQUIRE (UNUSED);
  ABORTIF (lgl->apitrace, "can only write one API trace");
  lgl->apitrace = apitrace;
  TRAPI ("init");
}

/*------------------------------------------------------------------------*/

static unsigned lglrand (LGL * lgl) {
  unsigned res;
  lgl->rng.z = 36969 * (lgl->rng.z & 65535) + (lgl->rng.z >> 16);
  lgl->rng.w = 18000 * (lgl->rng.w & 65535) + (lgl->rng.w >> 16);
  res = (lgl->rng.z << 16) + lgl->rng.w;
  LOG (5, "rng %u", res);
  return res;
}

/*------------------------------------------------------------------------*/

static int lglmtftk (Ftk * ftk) { return ftk->top == ftk->start; }

static int lglfullftk (Ftk * ftk) { return ftk->top == ftk->end; }

static int lglsizeftk (Ftk * ftk) { return ftk->end - ftk->start; }

static int lglcntftk (Ftk * ftk) { return ftk->top - ftk->start; }

static void lglrelftk (LGL * lgl, Ftk * ftk) {
  DEL (ftk->start, lglsizeftk (ftk));
  memset (ftk, 0, sizeof *ftk);
}

static void lglenlftk (LGL * lgl, Ftk * ftk) {
  int oldsize = lglsizeftk (ftk);
  int newsize = oldsize ? 2*oldsize : 1;
  int count = lglcntftk (ftk);
  RSZ (ftk->start, oldsize, newsize);
  ftk->top = ftk->start + count;
  ftk->end = ftk->start + newsize;
}

static void lglpushftk (LGL * lgl, Ftk * ftk, Flt f) {
  if (lglfullftk (ftk)) lglenlftk (lgl, ftk);
  *ftk->top++ = f;
}

static Flt lgltopftk (Ftk * ftk) {
  assert (!lglmtftk (ftk));
  return ftk->top[-1];
}

static Flt lglpopftk (Ftk * ftk) {
  assert (!lglmtftk (ftk));
  return *--ftk->top;
}

/*------------------------------------------------------------------------*/

static int lglfullctk (Ctk * ctk) { return ctk->top == ctk->end; }

static int lglsizectk (Ctk * ctk) { return ctk->end - ctk->start; }

static int lglcntctk (Ctk * ctk) { return ctk->top - ctk->start; }

static void lglrelctk (LGL * lgl, Ctk * ctk) {
  DEL (ctk->start, lglsizectk (ctk));
  memset (ctk, 0, sizeof *ctk);
}

static void lglenlctk (LGL * lgl, Ctk * ctk) {
  int oldsize = lglsizectk (ctk);
  int newsize = oldsize ? 2*oldsize : 1;
  int count = lglcntctk (ctk);
  RSZ (ctk->start, oldsize, newsize);
  ctk->top = ctk->start + count;
  ctk->end = ctk->start + newsize;
}

static void lglpushcontrol (LGL * lgl, int decision) {
  Ctk * ctk = &lgl->control;
  Ctr * ctr;
  if (lglfullctk (ctk)) lglenlctk (lgl, ctk);
  ctr = ctk->top++;
  ctr->decision = decision;
  ctr->used = 0;
  ctr->used2 = 0;
}

static void lglpopcontrol (LGL * lgl) {
  assert (lgl->control.top > lgl->control.start);
  --lgl->control.top;
}

static void lglrstcontrol (LGL * lgl, int count) {
  while (lglcntctk (&lgl->control) > count)
    lglpopcontrol (lgl);
}

static Ctr * lglctr (LGL * lgl, int level) {
  Ctk * ctk = &lgl->control;
  Ctr * res;
  assert (0 < level && level < lglsizectk (ctk));
  res = ctk->start + level;
  return res;
}

static unsigned lglevelused (LGL * lgl, int level) {
  return lglctr (lgl, level)->used;
}

static void lgluselevel (LGL * lgl, int level) {
  Ctk * ctk = &lgl->control;
  Ctr * ctr;
  assert (0 < level && level < lglsizectk (ctk));
  ctr = ctk->start + level;
  if (!ctr->used) {
    lglpushstk (lgl, &lgl->frames, level);
    LOG (2, "pulled in decision level %d", level);
    ctr->used = 1;
  } else if (ctr->used == 1) {
    LOG (2, "pulled in decision level %d a second time", level);
    ctr->used = 2;
  }
}

static void lglunuselevel (LGL * lgl, int level) {
  Ctk * ctk = &lgl->control;
  Ctr * ctr;
  assert (0 < level);
  if (level >= lglcntctk (ctk)) return;
  ctr = ctk->start + level;
  assert (ctr->used > 0);
  ctr->used = 0;
}

/*------------------------------------------------------------------------*/

void lglgetenv (LGL * lgl, Opt * opt, const char * lname) {
  const char * q, * valstr;
  char uname[40], * p;
  int newval, oldval;
  assert (strlen (lname) + 3 + 1 < sizeof (uname));
  uname[0] = 'L'; uname[1] = 'G'; uname[2] = 'L';
  p = uname + 3;
  for (q = lname; *q; q++) {
    assert (p < uname + sizeof uname);
    *p++ = toupper (*q);
  }
  assert (p < uname + sizeof uname);
  *p = 0;
  valstr = getenv (uname);
  if (!valstr) return;
  oldval = opt->val;
  newval = atoi (valstr);
  if (newval < opt->min) newval = opt->min;
  if (newval > opt->max) newval = opt->max;
  if (newval == oldval) return;
  opt->val = newval;
  TRAPI ("option %s %d", lname, newval);
  COVER (lgl->clone);
  if (lgl->clone) lglsetopt (lgl->clone, lname, newval);
}

static void lglchkenv (LGL * lgl) {
  extern char ** environ;
  char * src, *eos, * dst;
  char ** p, * s, * d;
  int len;
  for (p = environ; (src = *p); p++) {
    if (src[0] != 'L' || src[1] != 'G' || src[2] != 'L') continue;
    for (eos = src; *eos && *eos != '='; eos++)
      ;
    len = eos - (src + 3);
    NEW (dst, len + 1);
    d = dst;
    for (s = src + 3; s < eos; s++) *d++ = tolower (*s);
    *d = 0;
    if (!lglhasopt (lgl, dst) && strcmp (dst, "apitrace"))
      lglwrn (lgl, "invalid 'LGL...' environment '%s'", src);
    DEL (dst, len + 1);
  }
}

#define SETPLAIN(NAME) \
do { \
  if (val) lgl->opts->NAME.val = 0; \
  else lgl->opts->NAME.val = lgl->opts->NAME.dflt; \
} while (0)

#define SETDRUP SETPLAIN

static void lglforcedruplig (LGL * lgl, int val) {
  SETDRUP (bca);
  SETDRUP (card);
  SETDRUP (gauss);
  SETDRUP (smallve);
  SETDRUP (unhide);
}

static void lglsetdruplig (LGL * lgl, int val) {
  lglforcedruplig (lgl, val);
  lglprt (lgl, 1,
    "[druplig] druplig checking switched %s",
    val ? "on" : "off");
}

static void lglsetplain (LGL * lgl, int val) {
  SETPLAIN (bca);
  SETPLAIN (block);
  SETPLAIN (card);
  SETPLAIN (cce);
  SETPLAIN (decompose);
  SETPLAIN (elim);
  SETPLAIN (gauss);
  SETPLAIN (locs);
  SETPLAIN (probe);
  SETPLAIN (quatres);
  SETPLAIN (sweep);
  SETPLAIN (ternres);
  SETPLAIN (transred);
  SETPLAIN (unhide);
  lglprt (lgl, 1, "[plain] plain solving switched %s", val ? "on" : "off");
}

#define SETWAIT(NAME) \
do { \
  if (val) lgl->opts->NAME.val = lgl->opts->NAME.dflt; \
  else lgl->opts->NAME.val = 0; \
} while (0)

static void lglsetwait (LGL * lgl, int val) {
  SETWAIT (batewait);
  SETWAIT (bcawait);
  SETWAIT (blockwait);
  SETWAIT (ccewait);
  SETWAIT (elmblkwait);
  SETWAIT (gausswait);
  SETWAIT (smallvewait);
  SETWAIT (sweepwait);
  SETWAIT (ternreswait);
  SETWAIT (transredwait);
  SETWAIT (unhidewait);
  lglprt (lgl, 1, "[wait] waiting %s", val ? "enabled" : "disabled");
}

static LGL * lglnewlgl (void * mem,
			lglalloc alloc,
			lglrealloc realloc,
			lgldealloc dealloc) {
  LGL * lgl = alloc ? alloc (mem, sizeof *lgl) : malloc (sizeof *lgl);
  ABORTIF (!lgl, "out of memory allocating main solver object");
  CLRPTR (lgl);

  lgl->mem = alloc ? alloc (mem, sizeof *lgl->mem) : malloc (sizeof *lgl->mem);
  ABORTIF (!lgl->mem, "out of memory allocating memory manager object");

  lgl->mem->state = mem;
  lgl->mem->alloc = alloc;
  lgl->mem->realloc = realloc;
  lgl->mem->dealloc = dealloc;

  lgl->opts = alloc ? alloc (mem, sizeof (Opts)) : malloc (sizeof (Opts));
  ABORTIF (!lgl->opts, "out of memory allocating option manager object");
  CLRPTR (lgl->opts);

  lgl->stats = alloc ? alloc (mem, sizeof (Stats)) : malloc (sizeof (Stats));
  ABORTIF (!lgl->stats, "out of memory allocating statistic counters");
  CLRPTR (lgl->stats);

  lglinc (lgl, sizeof *lgl);
  lglinc (lgl, sizeof *lgl->mem);
  lglinc (lgl, sizeof *lgl->opts);
  lglinc (lgl, sizeof *lgl->stats);

  return lgl;
}

static void lglsetmaxminscore (LGL * lgl) {
  Flt oldmaxscore = lgl->maxscore, oldminscore = lgl->minscore;
  lgl->maxscore = lglflt (DEFSCOREXP, 1);
  lgl->minscore = lglflt (-DEFSCOREXP, 1);
  if (oldmaxscore != lgl->maxscore)
    lglprt (lgl, 1,
      "[set-maximum-score] maximum score limit %s",
      lglscr2str (lgl, lgl->maxscore));
  if (oldminscore != lgl->minscore)
    lglprt (lgl, 1,
      "[set-minimum-score] minimum score limit %s",
      lglscr2str (lgl, lgl->minscore));
}

static void lglsetscincf (LGL * lgl, int scincinc) {
  if (scincinc == lgl->scincinc) return;
  lgl->scincf = lglrat (1000 + scincinc, 1000);
  if (!lgl->stats->setscincf.count++)
    lgl->stats->setscincf.min = lgl->stats->setscincf.max = scincinc;
  else {
    if (scincinc < lgl->stats->setscincf.min)
      lgl->stats->setscincf.min = scincinc;
    if (scincinc > lgl->stats->setscincf.max)
      lgl->stats->setscincf.max = scincinc;
  }
  lglprt (lgl, 2,
    "[set-score-increment-%d] factor %s (%d/1000) after %lld conflicts",
    lgl->stats->setscincf.count,
    lglscr2str (lgl, lgl->scincf), scincinc, (LGLL) lgl->stats->confs);
  lgl->scincinc = scincinc;
}

static void lglinitscores (LGL * lgl) {
  lglsetmaxminscore (lgl);
  lglsetscincf (lgl, lgl->opts->scincinc.val);
}

LGL * lglminit (void * mem,
		lglalloc alloc,
		lglrealloc realloc,
		lgldealloc dealloc) {
  const char * apitracename;
  LGL * lgl;
  int i;

  lgl = 0;
  ABORTIF (!alloc+!realloc+!dealloc != 0 && !alloc+!realloc+!dealloc != 3,
	   "inconsistent set of external memory handlers");

  assert (sizeof (long) == sizeof (void*));

  assert (REMOVED > (RMSHFTLIT (MAXVAR) | MASKCS | REDCS));
  assert (REMOVED > MAXREDLIDX);
  assert (REMOVED > MAXIRRLIDX);

  assert (MAXREDLIDX == MAXIRRLIDX);
  assert (GLUESHFT == RMSHFT);

  assert (INT_MAX > ((MAXREDLIDX << GLUESHFT) | GLUEMASK));
  assert (INT_MAX > ((MAXIRRLIDX << RMSHFT) | MASKCS | REDCS));

  assert (MAXGLUE < POW2GLUE);

  lgl = lglnewlgl (mem, alloc, realloc, dealloc);
  lgl->tid = -1;

  lglpushcontrol (lgl, 0);
  assert (lglcntctk (&lgl->control) == lgl->level + 1);

  lgl->out = stdout;
  lgl->prefix = lglstrdup (lgl, "c ");

  apitracename = getenv ("LGLAPITRACE");
  if (apitracename) lglopenapitrace (lgl, apitracename);

  lglinitopts (lgl, lgl->opts);

  if (lgl->opts->plain.val) lglsetplain (lgl, 1);
  if (lgl->opts->druplig.val) lglsetdruplig (lgl, 1);
  if (!lgl->opts->wait.val) lglsetwait (lgl, 0);

  NEW (lgl->times, 1);
  NEW (lgl->timers, 1);
  NEW (lgl->limits, 1);
  NEW (lgl->fltstr, 1);
  NEW (lgl->red, MAXGLUE+1);
  NEW (lgl->wchs, 1);
  for (i = 0; i < MAXLDFW; i++) lgl->wchs->start[i] = INT_MAX;
  lglpushstk (lgl, &lgl->wchs->stk, INT_MAX);
  lglpushstk (lgl, &lgl->wchs->stk, INT_MAX);

  lgl->scinc = lglflt (0, 1);

  TRANS (UNUSED);

  return lgl;
}

static void lglcopyclonenfork (LGL * dst, LGL * src) {
  memcpy (dst->opts, src->opts, sizeof *src->opts);
  dst->out = src->out;
  if (dst->prefix) lgldelstr (dst, dst->prefix);
  dst->prefix = lglstrdup (dst, src->prefix);
  if (src->cbs) {
    lglinitcbs (dst);
    if (src->cbs->onabort) {
      dst->cbs->abortstate = src->cbs->abortstate;
      dst->cbs->onabort = src->cbs->onabort;
    }
    if (src->cbs->getime) dst->cbs->getime = src->cbs->getime;
  }
}

static void lglcompact (LGL *);

LGL * lglmclone (LGL * orig,
		 void * mem,
		 lglalloc alloc,
		 lglrealloc realloc,
		 lgldealloc dealloc) {
  size_t max_bytes, current_bytes;
  LGL * lgl = orig;
  int glue;

  if (!orig) return 0;
  lglcompact (orig);
  LOG (1, "cloning");
  lgl = lglnewlgl (mem, alloc, realloc, dealloc);
  memcpy (lgl, orig, ((char*)&orig->mem) - (char*) orig);
  max_bytes = lgl->stats->bytes.max;
  current_bytes = lgl->stats->bytes.current;
  memcpy (lgl->stats, orig->stats, sizeof *orig->stats);
  lgl->stats->bytes.current = current_bytes;
  lgl->stats->bytes.max = max_bytes;

  lglcopyclonenfork (lgl, orig);

  CLONE (limits, 1);
  CLONE (times, 1);
  CLONE (timers, 1);		assert (!lgl->timers->nest);
  CLONE (fltstr, 1);
  CLONE (ext, orig->szext);
  CLONE (i2e, orig->szvars);
  CLONE (doms, 2*orig->szvars);
  CLONE (dvars, orig->szvars);
  CLONE (qvars, orig->szvars);
  CLONE (avars, orig->szvars);
  CLONE (vals, orig->szvars);
  CLONE (jwh, 2*orig->szvars);
  CLONE (drail, orig->szdrail);

  NEW (lgl->red, MAXGLUE+1);
  for (glue = 0; glue <= MAXGLUE; glue++) CLONESTK (red[glue]);

  NEW (lgl->wchs, 1);
  memcpy (lgl->wchs, orig->wchs, sizeof *orig->wchs);
  CLONESTK (wchs->stk);

  CLONESTK (control);
#ifndef NDEBUG
  CLONESTK (prevclause);
  lgl->prevglue = orig->prevglue;
#endif
  CLONESTK (clause);
  CLONESTK (eclause);
  CLONESTK (extend);
  CLONESTK (irr);
  CLONESTK (trail);
  CLONESTK (frames);
  CLONESTK (promote);
  CLONESTK (eassume);
  CLONESTK (assume);
  CLONESTK (learned);
  CLONESTK (dsched);

  CLONESTK (queue.stk);
  lgl->queue.mt = orig->queue.mt;
  lgl->queue.next = orig->queue.next;

#ifndef NCHKSOL
  CLONESTK (orig);
#endif
#ifndef NDEBUG
  {
    const char * p;
    for (p = (char*)&orig->elm; p < (char*)(&orig->repr+1); p++) assert (!*p);
  }
#endif
  assert (lgl->stats->bytes.current == orig->stats->bytes.current);
  assert (lgl->stats->bytes.max <= orig->stats->bytes.max);
  lgl->stats->bytes.max = orig->stats->bytes.max;
  return lgl;
}

LGL * lglclone (LGL * lgl) {
  REQINIT ();
  ABORTIF (lgl->opts->druplig.val,
    "can not clone if Druplig checking is enabled");
  return lglmclone (lgl,
                    lgl->mem->state,
                    lgl->mem->alloc,
                    lgl->mem->realloc,
                    lgl->mem->dealloc);
}

void lglchkclone (LGL * lgl) {
  REQINITNOTFORKED ();
  TRAPI ("chkclone");
}

LGL * lglinit (void) { return lglminit (0, 0, 0, 0); }

static int lglmaxoptnamelen (LGL * lgl) {
  int res = 0, len;
  Opt * o;
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++)
    if ((len = strlen (o->lng)) > res)
      res = len;
  return res;
}

void lglusage (LGL * lgl) {
  char fmt[20];
  int len;
  Opt * o;
  REQINITNOTFORKED ();
  len = lglmaxoptnamelen (lgl);
  sprintf (fmt, "--%%-%ds", len);
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++) {
    fprintf (lgl->out, "   ");
    fprintf (lgl->out, fmt, o->lng);
    fprintf (lgl->out, " %s [%d]\n", o->descrp, o->val);
  }
}

static int lglstrhasprefix (const char * str, const char * prefix) {
  const char * p, * q;
  for (p = str, q = prefix; *q && *p == *q; p++, q++)
    ;
  return !*q;
}

static int lglignopt (const char * name) {
  if (!strcmp (name, "abstime")) return 1;
  if (!strcmp (name, "check")) return 1;
  if (lglstrhasprefix (name, "drup")) return 1;
  if (!strcmp (name, "exitonabort")) return 1;
  if (!strcmp (name, "log")) return 1;
  if (!strcmp (name, "sleeponabort")) return 1;
  if (!strcmp (name, "verbose")) return 1;
  if (!strcmp (name, "witness")) return 1;
  return 0;
}

void lglopts (LGL * lgl, const char * prefix, int ignsome) {
  Opt * o;
  REQINITNOTFORKED ();
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++) {
    if (ignsome && lglignopt (o->lng)) continue;
    fprintf (lgl->out, "%s--%s=%d\n", prefix, o->lng, o->val);
  }
}

void lglrgopts (LGL * lgl) {
  Opt * o;
  REQINITNOTFORKED ();
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++)
    fprintf (lgl->out, "%s %d %d %d\n", o->lng, o->val, o->min, o->max);
}

void lglpcs (LGL * lgl, int mixed) {
  int i, printi, printl;
  int64_t range;
  Opt * o;
  REQINITNOTFORKED ();
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++) {
    if (lglignopt (o->lng)) continue;
    range = o->max; range -= o->min;
    if (range >= 7 && mixed < 0) continue;
    printi = printl = 0;
    printf ("%s ", o->lng);
    if (range < 7) {
      printf ("{%d", o->min);
      for (i = o->min + 1; i <= o->max; i++) printf (",%d", i);
      printf ("}");
    } else if (!mixed) {
      printf ("[%d,%d]", o->min, o->max);
      printi = 1;
      printl = (o->min > 0 && range >= 100);
    } else if (o->dflt == o->min || o->dflt == o->max) {
      printf ("{%d,%d,%d,%d,%d}",
        o->min,
        (int)(o->min + (1*range + 3)/4),
        (int)(o->min + (2*range + 3)/4),
        (int)(o->min + (3*range + 3)/4),
        o->max);
    } else if (o->dflt == o->min + 1) {
      printf ("{%d,%d,%d,%d}",
        o->min,
	o->dflt,
	(int)(o->dflt + (o->max - (int64_t) o->dflt)/2),
	o->max);
    } else if (o->dflt + 1 == o->max) {
      printf ("{%d,%d,%d,%d}",
        o->min,
	(int)(o->min + (o->dflt - (int64_t) o->min)/2),
	o->dflt,
	o->max);
    } else {
      assert (o->dflt - o->min >= 2);
      assert (o->max - o->dflt >= 2);
      printf ("{%d,%d,%d,%d,%d}",
        o->min,
	(int)(o->min + (o->dflt - (int64_t) o->min)/2),
        o->dflt,
        (int)(o->dflt + (o->max - (int64_t) o->min)/2),
	o->max);
    }
    printf ("[%d]", o->dflt);
    if (printi) printf ("i"); 
    if (printl) printf ("l"); 
    printf (" # %s\n",o->descrp);
  }
}

int lglhasopt (LGL * lgl, const char * opt) {
  Opt * o;
  REQINITNOTFORKED ();
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++)
    if (!strcmp (o->lng, opt)) return 1;
  return 0;
}

void * lglfirstopt (LGL * lgl) { return FIRSTOPT (lgl); }

void * lglnextopt (LGL * lgl,
		   void * current,
		   const char **nameptr,
		   int *valptr, int *minptr, int *maxptr) {
  Opt * opt = current, * res = opt + 1;
  if (res > LASTOPT (lgl)) return 0;
  if (nameptr) *nameptr = opt->lng;
  if (valptr) *valptr = opt->val;
  if (minptr) *minptr = opt->min;
  if (maxptr) *maxptr = opt->max;
  return res;
}

void lglsetopt (LGL * lgl, const char * opt, int val) {
  int oldval;
  Opt * o;
  REQINITNOTFORKED ();
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++)
    if (!strcmp (o->lng, opt)) break;
  if (o > LASTOPT (lgl)) return;
  if (val < o->min) val = o->min;
  if (o->max < val) val = o->max;
  oldval = o->val;
  o->val = val;
  if (o == &lgl->opts->plain) {
    if (val > 0 && !oldval) lglsetplain (lgl, 1);
    if (!val && oldval) lglsetplain (lgl, 0);
  }
  if (o == &lgl->opts->druplig) {
    if (val > 0 && !oldval) lglsetdruplig (lgl, 1);
    if (!val && oldval) lglsetdruplig (lgl, 0);
  }
  if (o == &lgl->opts->wait) {
    if (val > 0 && !oldval) lglsetwait (lgl, 1);
    if (!val && oldval) lglsetwait (lgl, 0);
  }
  if (o == &lgl->opts->phase && val != oldval) lgl->flushphases = 1;
  if (lgl->state == UNUSED) TRANS (OPTSET);
  TRAPI ("option %s %d", opt, val);

  if (lgl->opts->druplig.val)
    lglforcedruplig (lgl, 1);
}

static int lglws (int ch) {
  return ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r';
}

int lglreadopts (LGL * lgl, FILE * file) {
  int res, ch, val, nvalbuf, noptbuf;
  char optbuf[40], valbuf[40];
  const char * opt;
  res = 0;
  for (;;) {
    while (lglws (ch = getc (file)))
      ;
    if (ch == EOF) break;
    noptbuf = 0;
    optbuf[noptbuf++] = ch;
    while ((ch = getc (file)) != EOF && !lglws (ch)) {
      if (noptbuf + 1 >= sizeof optbuf) { ch = EOF; break; }
      optbuf[noptbuf++] = ch;
    }
    if (ch == EOF) break;
    assert (noptbuf < sizeof optbuf);
    optbuf[noptbuf++] = 0;
    assert (lglws (ch));
    while (lglws (ch = getc (file)))
      ;
    if (ch == EOF) break;
    nvalbuf = 0;
    valbuf[nvalbuf++] = ch;
    while ((ch = getc (file)) != EOF && !lglws (ch)) {
      if (nvalbuf + 1 >= sizeof valbuf) break;
      valbuf[nvalbuf++] = ch;
    }
    assert (nvalbuf < sizeof valbuf);
    valbuf[nvalbuf++] = 0;
    opt = optbuf;
    val = atoi (valbuf);
    lglprt (lgl, 1, "read option --%s=%d", opt, val);
    lglsetopt (lgl, opt, val);
    res++;
  }
  return res;
}

void lglsetout (LGL * lgl, FILE * out) { lgl->out = out; }

FILE * lglgetout (LGL * lgl) { return lgl->out; }

void lglsetprefix (LGL * lgl, const char * prefix) {
  lgldelstr (lgl, lgl->prefix);
  lgl->prefix = lglstrdup (lgl, prefix);
}

const char * lglgetprefix (LGL * lgl) { return lgl->prefix; }

static Opt * lgligetopt (LGL * lgl, const char * opt) {
  Opt * o;
  REQINITNOTFORKED ();
  for (o = FIRSTOPT (lgl); o <= LASTOPT (lgl); o++)
    if (!strcmp (o->lng, opt)) return o;
  return 0;
}

int lglgetopt (LGL * lgl, const char * opt) {
  Opt * o = lgligetopt (lgl, opt);
  return o ? o->val : 0;
}

int lgldefopt (LGL * lgl, const char * opt) {
  Opt * o = lgligetopt (lgl, opt);
  return o ? o->dflt : 0;
}

int lglgetoptminmax (LGL * lgl, const char * opt,
                     int * min_ptr, int * max_ptr) {
  Opt * o = lgligetopt (lgl, opt);
  if (!o) return 0;
  if (min_ptr) *min_ptr = o->min;
  if (max_ptr) *max_ptr = o->max;
  return o->val;
}

/*------------------------------------------------------------------------*/

static void lglrszvars (LGL * lgl, int new_size) {
  int old_size = lgl->szvars;
  assert (lgl->nvars <= new_size);
  RSZ (lgl->vals, old_size, new_size);
  RSZ (lgl->i2e, old_size, new_size);
  RSZ (lgl->doms, 2*old_size, 2*new_size);
  RSZ (lgl->dvars, old_size, new_size);
  RSZ (lgl->avars, old_size, new_size);
  RSZ (lgl->qvars, old_size, new_size);
  RSZ (lgl->jwh, 2*old_size, 2*new_size);
  lgl->szvars = new_size;
}

static void lglenlvars (LGL * lgl) {
  size_t old_size, new_size;
  old_size = lgl->szvars;
  new_size = old_size ? 2 * old_size : 4;
  LOG (3, "enlarging internal variables from %ld to %ld", old_size, new_size);
  lglrszvars (lgl, new_size);
}

static void lglredvars (LGL * lgl) {
  size_t old_size, new_size;
  old_size = lgl->szvars;
  new_size = lgl->nvars;
  if (new_size == old_size) return;
  LOG (3, "reducing variables from %ld to %ld", old_size, new_size);
  lglrszvars (lgl, new_size);
}

static int lglmax (int a, int b) { return a > b ? a : b; }

/*------------------------------------------------------------------------*/

static DVar * lgldvar (LGL * lgl, int lit) {
  assert (2 <= abs (lit) && abs (lit) < lgl->nvars);
  return lgl->dvars + abs (lit);
}

/*------------------------------------------------------------------------*/

static AVar * lglavar (LGL * lgl, int lit) {
  assert (2 <= abs (lit) && abs (lit) < lgl->nvars);
  return lgl->avars + abs (lit);
}

static Val lglval (LGL * lgl, int lit) {
  int idx = abs (lit);
  Val res;
  ASSERT (2 <= idx && idx < lgl->nvars);
  res = lgl->vals[idx];
  if (lit < 0) res = -res;
  return res;
}

static int lgltrail (LGL * lgl, int lit) { return lglavar (lgl, lit)->trail; }

static int lglevel2trail (LGL * lgl, int level) {
  return lgltrail (lgl, lglctr (lgl, level)->decision);
}


static TD * lgltd (LGL * lgl, int lit) {
  int pos = lgltrail (lgl, lit);
  assert (0 <= pos && pos < lgl->szdrail);
  return lgl->drail + pos;
}

static int lglevel (LGL * lgl, int lit) { return lgltd (lgl, lit)->level; }

static int lglisfree (LGL * lgl, int lit) {
  return lglavar (lgl, lit)->type == FREEVAR;
}

/*------------------------------------------------------------------------*/

static QVar * lglqvar (LGL * lgl, int lit) {
  assert (2 <= abs (lit) && abs (lit) < lgl->nvars);
  return lgl->qvars + abs (lit);
}

static int * lgldpos (LGL * lgl, int lit) {
  QVar * qv;
  int * res;
  qv = lglqvar (lgl, lit);
  res = &qv->pos;
  return res;
}

static int lglscrcmp (LGL * lgl, Flt a, Flt b) {
  const int shift = lgl->opts->scoreshift.val;
  a >>= shift; assert (a >= 0);
  b >>= shift; assert (b >= 0);
  if (a < b) return -1;
  if (a > b) return 1;
  return 0;
}

static int lgldcmp (LGL * lgl, int l, int k) {
  QVar * pv = lglqvar (lgl, l);
  QVar * qv = lglqvar (lgl, k);
  int res;
  if ((res = lglscrcmp (lgl, pv->score, qv->score))) return res;
  return 0;
}

#ifndef NDEBUG
static void lglchkdsched (LGL * lgl) {
  int * p, parent, child, ppos, cpos, size, i, tmp;
  Stk * s = &lgl->dsched;
  size = lglcntstk (s);
  p = s->start;
  for (ppos = 0; ppos < size; ppos++) {
    parent = p[ppos];
    assert (parent > 1);
    tmp = *lgldpos (lgl, parent);
    assert (ppos == tmp);
    for (i = 0; i <= 1; i++) {
      cpos = 2*ppos + 1 + i;
      if (cpos >= size) continue;
      child = p[cpos];
      assert (child > 1);
      tmp = *lgldpos (lgl, child);
      assert (cpos == tmp);
      assert (lgldcmp (lgl, parent, child) >= 0);
    }
  }
}
#endif

static void lgldup (LGL * lgl, int lit) {
  int child = lit, parent, cpos, ppos, * p, * cposptr, * pposptr;
  Stk * s = &lgl->dsched;
  assert (lit > 1);
  p = s->start;
  cposptr = lgldpos (lgl, child);
  cpos = *cposptr;
  assert (cpos >= 0);
  while (cpos > 0) {
    ppos = (cpos - 1)/2;
    parent = p[ppos];
    if (lgldcmp (lgl, parent, lit) >= 0) break;
    pposptr = lgldpos (lgl, parent);
    assert (*pposptr == ppos);
    p[cpos] = parent;
    *pposptr = cpos;
    LOGDSCHED (5, parent, "down from %d", ppos);
    cpos = ppos;
  }
  if (*cposptr == cpos) return;
#ifndef NLGLOG
  ppos = *cposptr;
#endif
  *cposptr = cpos;
  p[cpos] = lit;
  LOGDSCHED (5, lit, "up from %d", ppos);
#ifndef NDEBUG
  if (lgl->opts->check.val >= 2) lglchkdsched (lgl);
#endif
}

static void lglddown (LGL * lgl, int lit) {
  int parent = lit, child, right, ppos, cpos;
  int * p, * pposptr, * cposptr, size;
  Stk * s = &lgl->dsched;
  assert (lit > 1);
  size = lglcntstk (s);
  p = s->start;
  pposptr = lgldpos (lgl, parent);
  ppos = *pposptr;
  assert (0 <= ppos);
  for (;;) {
    cpos = 2*ppos + 1;
    if (cpos >= size) break;
    child = p[cpos];
    if (cpos + 1 < size) {
      right = p[cpos + 1];
      if (lgldcmp (lgl, child, right) < 0) cpos++, child = right;
    }
    if (lgldcmp (lgl, child, lit) <= 0) break;
    cposptr = lgldpos (lgl, child);
    assert (*cposptr = cpos);
    p[ppos] = child;
    *cposptr = ppos;
    LOGDSCHED (5, child, "up from %d", cpos);
    ppos = cpos;
  }
  if (*pposptr == ppos) return;
#ifndef NLGLOG
  cpos = *pposptr;
#endif
  *pposptr = ppos;
  p[ppos] = lit;
  LOGDSCHED (5, lit, "down from %d", cpos);
#ifndef NDEBUG
  if (lgl->opts->check.val >= 2) lglchkdsched (lgl);
#endif
}

static void lgldsched (LGL * lgl, int lit) {
  int * p = lgldpos (lgl, lit);
  Stk * s = &lgl->dsched;
  assert (lit > 1);
  assert (!lglqvar (lgl, lit)->enqueued);
  assert (*p < 0);
  *p = lglcntstk (s);
  lglpushstk (lgl, s, lit);
  lgldup (lgl, lit);
  lglddown (lgl, lit);
  LOGDSCHED (4, lit, "pushed");
}

static int lgltopdsched (LGL * lgl) {
  assert (!lglmtstk (&lgl->dsched));
  return lgl->dsched.start[0];
}

static int lglpopdsched (LGL * lgl) {
  Stk * s = &lgl->dsched;
  int res, last, cnt, * p;
  QVar * qv;
  assert (!lglmtstk (s));
  res = *s->start;
  LOGDSCHED (4, res, "popped");
  qv = lglqvar (lgl, res);
  assert (!qv->pos);
  qv->pos = -1;
  last = lglpopstk (s);
  cnt = lglcntstk (s);
  if (!cnt) { assert (last == res); return res; }
  p = lgldpos (lgl, last);
  assert (*p == cnt);
  *p = 0;
  *s->start = last;
  lglddown (lgl, last);
  return res;
}

#if 0
static void lgldunsched (LGL * lgl, int lit) {
  Stk * s = &lgl->dsched;
  int last, cnt, * p, pos;
  QVar * qv;
  if (lit < 0) lit = -lit;
  assert (!lglmtstk (s));
  LOGDSCHED (4, lit, "unschedule");
  qv = lglqvar (lgl, lit);
  pos = qv->pos;
  qv->pos = -1;
  assert (lglpeek (s, pos) == lit);
  last = lglpopstk (s);
  cnt = lglcntstk (s);
  if (cnt == pos) { assert (last == lit); return; }
  p = lgldpos (lgl, last);
  assert (*p == cnt);
  lglpoke (s, pos, last);
  *p = pos;
  lgldup (lgl, last);
  lglddown (lgl, last);
}
#endif

static void lgldreschedule (LGL * lgl) {
  Stk * s = &lgl->dsched;
  int idx, i, pos, cnt = lglcntstk (s);
  QVar * qv;
  LOG (1, "rescheduling %d variables", cnt);
  for (idx = 2; idx < lgl->nvars; idx++) {
    qv= lglqvar (lgl, idx);
    if (qv->enqueued) continue;
    qv->pos = -1;
  }
  pos = 0;
  s->top = s->start;
  for (i = 0; i < cnt; i++) {
    assert (pos <= i);
    assert (s->start + pos == s->top);
    idx = s->start[i];
    if (abs (idx) <= 1) continue;
    qv = lglqvar (lgl, idx);
    assert (!qv->enqueued);
    if (!lglisfree (lgl, idx)) { qv->pos = -1; continue; }
    assert (qv->pos == -1);
    s->start[pos] = idx;
    qv->pos = pos++;
    s->top++;
    lgldup (lgl, idx);
    lglddown (lgl, idx);
  }
  LOG (1, "new schedule with %d variables", lglcntstk (s));
  lglfitstk (lgl, s);
#ifndef NDEBUG
  if (lgl->opts->check.val >= 1) lglchkdsched (lgl);
#endif
}

static void lglenq (LGL * lgl, int idx, int updatequeuenext) {
  QVar * qv = lglqvar (lgl, idx);
  assert (!qv->enqueued);
  assert (qv->pos < 0);
  qv->enqueued = 1;
  qv->pos = lglcntstk (&lgl->queue.stk);
  lglpushstk (lgl, &lgl->queue.stk, idx);
  if (updatequeuenext || lgl->queue.next < 0) lgl->queue.next = qv->pos;
}
static void lglrescorevars (LGL * lgl) {
  Flt oldscinc, oldscore, newscore, oldmaxscore = 0, newmaxscore = 0;
  int64_t newotfs;
  QVar * qv;
  int idx;
  lgl->stats->rescored.vars++;
  for (idx = 2; idx < lgl->nvars; idx++) {
    qv = lglqvar (lgl, idx);
    if (qv->enqueued) continue;
    oldscore = qv->score;
    if (oldscore > oldmaxscore) oldmaxscore = oldscore;
    if (oldscore == FLTMIN) newscore = oldscore;
    else if (oldscore <= lgl->minscore) newscore = lgl->minscore;
    else {
      newscore = lglshflt (oldscore, DEFSCOREXP);
      if (newscore < lgl->minscore) newscore = lgl->minscore;
    }
    if (newscore <= lgl->minscore) {
      assert (newscore == FLTMIN || newscore == lgl->minscore);
      assert (!qv->enqueued);
    } else newscore = (oldscore >> 32);
    qv->score = newscore;
    if (qv->score > newmaxscore) newmaxscore = qv->score;
    LOG (3, "rescored variable %d from %s to %s",
	 idx, lglscr2str (lgl, oldscore), lglscr2str (lgl, qv->score));
  }
  lgldreschedule (lgl);
  newotfs = lgl->stats->otfs.driving + lgl->stats->otfs.restarting;
  assert (newotfs >= lgl->limits->rescore.vars.otfs);
  assert (lgl->stats->confs >= lgl->limits->rescore.vars.confs);
  lglprt (lgl, 3,
    "[rescored-vars-%d] after %lld conflicts and %lld OTFS",
    lgl->stats->rescored.vars,
    lgl->stats->confs - lgl->limits->rescore.vars.confs,
    newotfs - lgl->limits->rescore.vars.otfs);
  lgl->limits->rescore.vars.confs = lgl->stats->confs;
  lgl->limits->rescore.vars.otfs = newotfs;
  lglprt (lgl, 3,
    "[rescored-vars-%d] old maximum score %s",
    lgl->stats->rescored.vars, lglscr2str (lgl, oldmaxscore));
  lglprt (lgl, 3,
    "[rescored-vars-%d] new maximum score %s",
    lgl->stats->rescored.vars, lglscr2str (lgl, newmaxscore));
  oldscinc = lgl->scinc;
  lgl->scinc = lglshflt (oldscinc, DEFSCOREXP);
  assert (lgl->scinc > 0);
  lglprt (lgl, 3,
    "[rescored-vars-%d] old score increment %s",
    lgl->stats->rescored.vars, lglscr2str (lgl, oldscinc));
  lglprt (lgl, 3,
    "[rescored-vars-%d] new score increment %s",
    lgl->stats->rescored.vars, lglscr2str (lgl, lgl->scinc));
}

static void lglbumpscinc (LGL * lgl) {
  Flt oldscinc;
  if (lgl->simp && !lgl->opts->bumpsimp.val) return;
  oldscinc = lgl->scinc;
  lgl->scinc = lglmulflt (oldscinc, lgl->scincf);
  LOG (3, "bumped variable score increment from %s to %s",
       lglscr2str (lgl, oldscinc), lglscr2str (lgl, lgl->scinc));
  if (lgl->scinc >= lgl->maxscore) {
    LOG (2, "variable max score %s hit", lglscr2str (lgl, lgl->maxscore));
    lglrescorevars (lgl);
  }
  if (!lgl->simp &&
      !(lgl->stats->confs % lgl->opts->scincincincint.val)) {
    int newscincinc = lgl->scincinc;
    if (lgl->opts->scincincmode.val == 1)
      newscincinc -= lgl->opts->scincincdelta.val;
    else if (lgl->opts->scincincmode.val == 2)
      newscincinc = (lgl->opts->scincincmin.val + newscincinc)/2;
    if (newscincinc < lgl->opts->scincincmin.val)
      newscincinc = lgl->opts->scincincmin.val;
    if (newscincinc != lgl->scincinc) lglsetscincf (lgl, newscincinc);
  }
}

/*------------------------------------------------------------------------*/

static int lglnewvar (LGL * lgl) {
  AVar * av;
  DVar * dv;
  QVar * qv;
  int res;
  assert (!lgl->dense);
  if (lgl->nvars == lgl->szvars) lglenlvars (lgl);
  if (lgl->nvars) res = lgl->nvars++;
  else res = 2, lgl->nvars = 3;
  assert (res < lgl->szvars);
  if (res > MAXVAR) lgldie (lgl, "more than %d variables", MAXVAR - 1);
  assert (res <= MAXVAR);
  assert ((RMSHFTLIT(res) >> RMSHFT) == res);
  assert ((RMSHFTLIT(-res) >> RMSHFT) == -res);
  LOG (3, "new internal variable %d", res);
  dv = lgl->dvars + res;
  CLRPTR (dv);
  av = lgl->avars + res;
  CLRPTR (av);
  qv = lgl->qvars + res;
  CLRPTR (qv);
  qv->glag = -1;
  qv->pos = -1;
  lglenq (lgl, res, 1);
  lgl->unassigned++;
  lgl->allphaseset = 0;
  return res;
}

static int lglsgn (int lit) { return (lit < 0) ? -1 : 1; }

static Ext * lglelit2ext (LGL * lgl, int elit) {
  int idx = abs (elit);
  assert (0 < idx), assert (idx <= lgl->maxext);
  return lgl->ext + idx;
}

static int lglerepr (LGL * lgl, int elit) {
  int res, next, tmp;
  Ext * ext;
  assert (0 < abs (elit)), assert (abs (elit) <= lgl->maxext);
  res = elit;
  for (;;) {
    ext = lglelit2ext (lgl, res);
    if (!ext->equiv) break;
    next = ext->repr;
    if (res < 0) next = -next;
    res = next;
  }
  tmp = elit;
  for (;;) {
    ext = lglelit2ext (lgl, tmp);
    if (!ext->equiv) { assert (tmp == res); break; }
    next = ext->repr;
    ext->repr = (tmp < 0) ? -res : res;
    if (tmp < 0) next = -next;
    tmp = next;
  }
  return res;
}

static void lgladjext (LGL * lgl, int eidx) {
  size_t old, new;
  assert (eidx >= lgl->szext);
  assert (eidx > lgl->maxext);
  assert (lgl->szext >= lgl->maxext);
  old = lgl->szext;
  new = old ? 2*old : 2;
  while (eidx >= new) new *= 2;
  assert (eidx < new), assert (new >= lgl->szext);
  LOG (3, "enlarging external variables from %ld to %ld", old, new);
  RSZ (lgl->ext, old, new);
  lgl->szext = new;
}

static void lglmelter (LGL * lgl) {
  if (lgl->allfrozen) {
    lglprt (lgl, 1,
      "[melter] not all literals assumed to be frozen anymore");
    lgl->allfrozen = 0;
  }
  if (lgl->limits->elm.pen || lgl->limits->blk.pen || lgl->limits->cce.pen) {
    lglprt (lgl, 1,
      "[melter] reset penalties: %d elm, %d blk, %d cce",
      lgl->limits->elm.pen, lgl->limits->blk.pen, lgl->limits->cce.pen);
    lgl->limits->elm.pen = lgl->limits->blk.pen = lgl->limits->cce.pen = 0;
  }
  lgl->frozen = lgl->allfrozen = 0;
  LOG (2, "melted solver");
}

static int lglimportaux (LGL * lgl, int elit) {
  int res, repr, eidx = abs (elit);
  Ext * ext;
  assert (elit);
  if (eidx >= lgl->szext) lgladjext (lgl, eidx);
  if (eidx > lgl->maxext) {
    lgl->maxext = eidx;
    lglmelter (lgl);
  }
  repr = lglerepr (lgl, elit);
  ext = lglelit2ext (lgl, repr);
  assert (!ext->equiv);
  res = ext->repr;
  if (!ext->imported) {
    res = lglnewvar (lgl);
    assert (!ext->equiv);
    ext->repr = res;
    ext->imported = 1;
    assert (eidx <= INT_MAX/2);
    lgl->i2e[res] = 2*eidx;
    LOG (3, "mapping external variable %d to %d", eidx, res);
    lglmelter (lgl);
  }
  if (repr < 0) res = -res;
  LOG (2, "importing %d as %d", elit, res);
  return res;
}

static int lglimport (LGL * lgl, int elit) {
  assert (elit);
  if (!lgl->opts->import.val) {
    if (!lgl->maxext) (void) lglimportaux (lgl, 1);
    while (lgl->maxext < abs (elit))
      (void) lglimportaux (lgl, lgl->maxext + 1);
  }
  return lglimportaux (lgl, elit);
}

static Stk * lglidx2stk (LGL * lgl, int red, int lidx) {
  int glue = 0;
  Stk * s;
  assert (red == 0 || red == REDCS);
  assert (0 <= lidx);
  if (!red) s = &lgl->irr;
  else {
    glue = lidx & GLUEMASK;
    lidx >>= GLUESHFT;
    assert (lidx <= MAXREDLIDX);
    s = &lgl->red[glue];
  }
  return s;
}

static int * lglidx2lits (LGL * lgl, int red, int lidx) {
  Stk * s = lglidx2stk (lgl, red, lidx);
  int * res;
  assert (red == 0 || red == REDCS);
  assert (0 <= lidx);
  res = s->start + (red ? (lidx >> GLUESHFT) : lidx);
#ifndef NDEBUG
  if (red && (lidx & GLUEMASK) == MAXGLUE) assert (res < s->end);
  else assert (res < s->top);
#endif
  return res;
}

#ifndef NLGLOG
static const char * lglred2str (int red) {
  assert (!red || red == REDCS);
  return red ? "redundant" : "irredundant";
}
#endif

static int lgliselim (LGL * lgl, int lit) {
  Tag tag = lglavar (lgl, lit)->type;
  return tag == ELIMVAR;
}

static int lglexport (LGL * lgl, int ilit) {
  int iidx, tidx, eidx, def, res;
  iidx = abs (ilit);
  assert (2 <= iidx), assert (iidx < lgl->nvars);
  tidx = lgl->i2e[iidx];
  def = tidx & 1;
  tidx >>= 1;
  assert (tidx);
  eidx = tidx;
  if (def) eidx += lgl->maxext;
  res = eidx;
  if (ilit < 0) res = -res;
  return res;
}

static int * lglrsn (LGL * lgl, int lit) { return lgltd (lgl, lit)->rsn; }

static int lglulit (int lit) { return 2*abs (lit) + (lit < 0); }

static void lglsetdom (LGL * lgl, int lit, int dom) {
  assert (2 <= abs (lit)  && abs (lit) < lgl->nvars);
  assert (2 <= abs (dom)  && abs (dom) < lgl->nvars);
  ASSERT (lglval (lgl, lit) >= 0);
  ASSERT (lglval (lgl, dom) >= 0);
  lgl->doms[lglulit (lit)] = dom;
  LOG (3, "literal %d dominated by %d", lit, dom);
}

static int lglgetdom (LGL * lgl, int lit) {
  int res;
  assert (2 <= abs (lit)  && abs (lit) < lgl->nvars);
  assert (lglval (lgl, lit) >= 0);
  res = lgl->doms[lglulit (lit)];
  return res;
}

static HTS * lglhts (LGL * lgl, int lit) {
  return lgldvar (lgl, lit)->hts + (lit < 0);
}

static int * lglhts2wchs (LGL * lgl, HTS * hts) {
  int * res = lgl->wchs->stk.start + hts->offset;
  assert (res < lgl->wchs->stk.top);
  assert (res + hts->count < lgl->wchs->stk.top);
  assert (res + hts->count < lgl->wchs->stk.top);
  return res;
}

/*------------------------------------------------------------------------*/

#ifndef NLGLDRUPLIG

static int lgldruplig (LGL * lgl) {
  if (!lgl->opts->druplig.val) return 0;
  if (!lgl->druplig) {
    lgl->druplig = druplig_minit (lgl,
		     (druplig_malloc) lglnew,
		     (druplig_realloc) lglrsz,
		     (druplig_free) lgldel);
    druplig_set_check (lgl->druplig, lgl->opts->drupligcheck.val);
    if (lgl->opts->drupligtrace.val)
      druplig_set_trace (lgl->druplig, lgl->out);
    else druplig_set_trace (lgl->druplig, 0);
    druplig_set_traceorig (lgl->druplig, lgl->opts->drupligtraceorig.val);
    if (lgl->opts->verbose.val > 0) {
      druplig_banner (lgl->out);
      druplig_options (lgl->druplig, lgl->out);
    }
  }
  return 1;
}

static void lgldrupligreallyadd (LGL * lgl, int red) {
  assert (!red || red == REDCS);
  assert (lgl->opts->druplig.val);
  assert (lgl->druplig);
  lglstart (lgl, &lgl->times->druplig);
  if (red) druplig_check_and_add_redundant_clause (lgl->druplig);
  else druplig_add_original_clause (lgl->druplig);
  lglstop (lgl);
}

static void lgldrupligreallydel (LGL * lgl) {
  assert (lgl->opts->druplig.val);
  assert (lgl->druplig);
  lglstart (lgl, &lgl->times->druplig);
  druplig_forget_clause (lgl->druplig);
  lglstop (lgl);
}

static int lglialiased (LGL * lgl, int ilit) {
  int elit = lglexport (lgl, ilit);
  Ext * ext = lglelit2ext (lgl, elit);
  return ext->aliased;
}

#endif

static void lgldrupligaddclsaux (LGL * lgl, int red, const int * c) {
#ifndef NLGLDRUPLIG
  assert (!red || red == REDCS);
  if (lgldruplig (lgl)) {
    const int * p;
    int lit;
    for (p = c; (lit = *p); p++)
      druplig_add_literal (lgl->druplig, lglexport (lgl, lit));
    lgldrupligreallyadd (lgl, red);
  }
#else
  (void) lgl, (void) c;
#endif
}

static void lgldrupligaddclsarg (LGL * lgl, int red, ...) {
#ifndef NLGLDRUPLIG
  assert (!red || red == REDCS);
  if (lgldruplig (lgl)) {
    va_list ap;
    int unit = 0;
#ifndef NLGLOG
    int logging = (lgl->opts->log.val > 1);
    if (logging) lglogstart (lgl, 2, "druplig adding internal clause");
#endif
    va_start (ap, red);
    for (;;) {
      int lit = va_arg (ap, int);
      if (!lit) break;
      if (unit) unit = INT_MAX; else unit = lit;
      druplig_add_literal (lgl->druplig, lglexport (lgl, lit));
#ifndef NLGLOG
      if (logging) fprintf (lgl->out, " %d", lit);
#endif
    }
    va_end (ap);
#ifndef NLGLOG
    if (logging) lglogend (lgl);
#endif
    lgldrupligreallyadd (lgl, red);
    if (unit && unit != INT_MAX) lgl->drupligunit = unit;
    else lgl->drupligunit = 0;
  }
#else
  (void) lgl, (void) red;
#endif
}

static void lgldrupligaddcls (LGL * lgl, int red) {
#ifndef NLGLDRUPLIG
  assert (!red || red == REDCS);
  if (lgldruplig (lgl)) {
    int lit, size = 0;
    const int * p;
    for (p = lgl->clause.start; p < lgl->clause.top; p++)
      if ((lit = *p)) {
	druplig_add_literal (lgl->druplig, lglexport (lgl, lit));
	size++;
      }
    lgldrupligreallyadd (lgl, red);
    if (size == 1) lgl->drupligunit = lgl->clause.start[0];
    else lgl->drupligunit = 0;
  }
#else
  (void) lgl, (void) red;
#endif
}

static void lgldrupligdelclsarg (LGL * lgl, ...) {
#ifndef NLGLDRUPLIG
  if (lgldruplig (lgl)) {
    int aliased = 0;
    va_list ap;
#ifndef NDEBUG
    int size = 0;
#endif
#ifndef NLGLOG
    int logging = (lgl->opts->log.val > 1);
    if (logging) lglogstart (lgl, 2, "druplig forgetting internal clause");
#endif
    va_start (ap, lgl);
    for (;;) {
      int lit = va_arg (ap, int);
      if (!lit) break;
      if (lglialiased (lgl, lit)) aliased = 1;
#ifndef NDEBUG
      size++;
#endif
#ifndef NLGLOG
      if (logging) fprintf (lgl->out, " %d", lit);
#endif
    }
    va_end (ap);
#ifndef NLGLOG
    if (logging) {
      if (aliased) fprintf (lgl->out, " (but aliased)");
      lglogend (lgl);
    }
#endif
    assert (size > 1);
    if (aliased) return;
    va_start (ap, lgl);
    for (;;) {
      int lit = va_arg (ap, int);
      if (!lit) break;
      druplig_add_literal (lgl->druplig, lglexport (lgl, lit));
    }
    va_end (ap);
    lgldrupligreallydel (lgl);
  }
#else
  (void) lgl;
#endif
}

static void lgldrupligdelclsaux (LGL * lgl, const int * c) {
#ifndef NLGLDRUPLIG
  if (lgldruplig (lgl)) {
    const int * p;
    int lit;
    for (p = c; (lit = *p); p++)
      if (lglialiased (lgl, lit)) return;
    for (p = c; (lit = *p); p++)
      druplig_add_literal (lgl->druplig, lglexport (lgl, lit));
    lgldrupligreallydel (lgl);
    assert (p - c > 1);
  }
#else
  (void) lgl, (void) c;
#endif
}

static void lgldrupligunit (LGL * lgl, int lit) {
#ifndef NLGLDRUPLIG
  if (!lgldruplig (lgl)) return;
  if (lit == lgl->drupligunit) return;
  druplig_add_literal (lgl->druplig, lglexport (lgl, lit));
  druplig_check_and_add_redundant_clause (lgl->druplig);
  lgl->drupligunit = lit;
#else
  (void) lgl, (void) lit;
#endif
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
static int lglrgforcing (LGL * lgl, int red, int lidx) {
  int lit, val, level, truelevel, unit;
  const int * p, * c;
  int * rsn, r0, r1;
  assert (!red || red == REDCS);
  c = lglidx2lits (lgl, red, lidx);
  truelevel = INT_MAX;
  unit = 0;
  for (p = c; (lit = *p); p++) {
    assert (abs (lit) < NOTALIT);
    val = lglval (lgl, lit);
    if (!val) return 0;
    level = lglevel (lgl, lit);
    if (val > 0) {
      if (unit) return 0;
      truelevel = level;
      unit = lit;
    } else if (level > truelevel) return 0;
  }
  if (!unit) return 0;
  rsn = lglrsn (lgl, unit);
  r0 = rsn[0];
  if ((r0 & MASKCS) != LRGCS) return 0;
  if ((r0 & REDCS) != red) return 0;
  r1 = rsn[1];
  if (r1 != lidx) return 0;
  return 1;
}
#endif

static void lglassign (LGL * lgl, int lit, int r0, int r1) {
  int * p, other, other2, * c, lidx, found;
  int idx, phase, glue, tag, dom, red, irr;
  AVar * av = lglavar (lgl, lit);
  TD * td;
  LOGREASON (2, lit, r0, r1, "assign %d through", lit);
  av->trail = lglcntstk (&lgl->trail);
  if (av->trail >= lgl->szdrail) {
    int newszdrail = lgl->szdrail ? 2*lgl->szdrail : 1;
    RSZ (lgl->drail, lgl->szdrail, newszdrail);
    lgl->szdrail = newszdrail;
  }
  td = lgltd (lgl, lit);
  tag = r0 & MASKCS;
  dom = (tag == BINCS) ? lglgetdom (lgl, -(r0 >> RMSHFT)) : lit;
  lglsetdom (lgl, lit, dom);
#ifndef NDEBUG
  {
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      assert (lglval (lgl, other) < 0);
      if (tag == TRNCS) {
	other2 = r1;
	assert (lglval (lgl, other2) < 0);
      }
    } else if (tag == LRGCS) {
      red = r0 & REDCS;
      lidx = r1;
      c = lglidx2lits (lgl, red, lidx);
      found = 0;
      for (p = c; (other = *p); p++)
	if (other == lit) found++;
	else assert (lglval (lgl, other) < 0);
      assert (found == 1);
    } else assert (tag == DECISION || tag == UNITCS);
  }
  assert (!lglval (lgl, lit));
  assert (lgl->unassigned > 0);
  assert (!lgliselim (lgl, lit));
#endif
  idx = abs (lit);
  phase = lglsgn (lit);
  lgl->vals[idx] = phase;
  if (!lgl->simp) {
    lgl->stats->agility -= lgl->stats->agility >> 13;
    if (av->phase != phase) {
      av->phase = phase;
      lgl->stats->agility += ((int64_t)1) << 19;
      lgl->stats->stability.changed++;
    }
  }
#ifndef NDEBUG
  if (phase < 0) av->wasfalse = 1; else av->wasfalse = 0;
#endif
  td->level = lgl->level;
  if (!lgl->level) {
    lgldrupligunit (lgl, lit);
    td->irr = 1;
    if (av->type == EQUIVAR) {
      assert (lgl->stats->equiv.current > 0);
      lgl->stats->equiv.current--;
      assert (lgl->stats->equiv.sum > 0);
      lgl->stats->equiv.sum--;
    } else {
      assert (av->type == FREEVAR);
      av->type = FIXEDVAR;
    }
    lgl->stats->fixed.sum++;
    lgl->stats->fixed.current++;
    lgl->stats->prgss++;
    lgl->stats->irrprgss++;
    td->rsn[0] = UNITCS | RMSHFTLIT (lit);
    td->rsn[1] = 0;
    if (lgl->cbs && lgl->cbs->units.produce.fun) {
      LOG (2, "trying to export internal unit %d external %d\n",
	   lgl->tid, lit, lglexport (lgl, lit));
      lgl->stats->sync.units.produced++;
      lgl->cbs->units.produce.fun (lgl->cbs->units.produce.state,
                                  lglexport (lgl, lit));
      LOG (2, "exporting internal unit %d external %d\n",
	      lgl->tid, lit, lglexport (lgl, lit));
    }
  } else {
    td->rsn[0] = r0;
    td->rsn[1] = r1;
    if (lgl->level == 1) {
      assert (tag != UNITCS);
      if (tag == DECISION) irr = 1;
      else if ((irr = !(red = (r0 & REDCS)))) {
	if (tag == BINCS) {
	  other = r0 >> RMSHFT;
	  irr = lgltd (lgl, other)->irr;
	} else if (tag == TRNCS) {
	  other = r0 >> RMSHFT;
	  if ((irr = lgltd (lgl, other)->irr)) {
	    other2 = r1;
	    irr = lgltd (lgl, other2)->irr;
	  }
	} else {
	  assert (tag == LRGCS);
	  lidx = r1;
	  c = lglidx2lits (lgl, red, lidx);
	  found = 0;
	  for (p = c; irr && (other = *p); p++)
	    if (other == lit) found++;
	    else irr = lgltd (lgl, other)->irr;
	  assert (!irr || found == 1);
	}
      }
    } else irr = 0;
    td->irr = irr;
  }

  lglpushstk (lgl, &lgl->trail, lit);
  if (!lgl->simp && !lgl->failed && (av->assumed & (1u << (lit > 0)))) {
    LOG (2, "failed assumption %d", -lit);
    lgl->failed = -lit;
  }
  lgl->unassigned--;
  td->lrglue = 0;
  if ((r0 & REDCS) && (r0 & MASKCS) == LRGCS) {
    glue = r1 & GLUEMASK;
    lgl->stats->lir[glue].forcing++;
    assert (lgl->stats->lir[glue].forcing > 0);
    if (lgl->level && 0 < glue && glue < MAXGLUE) {
      lgl->lrgluereasons++;
      assert (lgl->lrgluereasons > 0);
      td->lrglue = 1;
    }
#ifndef NDEBUG
    if (glue == MAXGLUE)
      assert ((r1 >> GLUESHFT) + 4 < lglcntstk (&lgl->red[MAXGLUE]));
#endif
  }
#ifndef NDEBUG
  if (tag == LRGCS) {
    lidx = r1;
    red = r0 & REDCS;
    if (lgl->level) assert (lglrgforcing (lgl, red, lidx));
    else assert (((*lglrsn (lgl, lit)) & MASKCS) == UNITCS);
  }
#endif
}

static void lglf2rce (LGL * lgl, int lit, int other, int red) {
  assert (lglval (lgl, other) < 0);
  assert (!red || red == REDCS);
  assert (!lgliselim (lgl, other));
  lglassign (lgl, lit, (RMSHFTLIT (other) | BINCS | red), 0);
}

static void lglf3rce (LGL * lgl, int lit, int other, int other2, int red) {
  assert (lglval (lgl, other) < 0);
  assert (lglval (lgl, other2) < 0);
  assert (!lgliselim (lgl, other));
  assert (!lgliselim (lgl, other2));
  assert (!red || red == REDCS);
  lglassign (lgl, lit, (RMSHFTLIT (other) | TRNCS | red), other2);
}

static void lglflrce (LGL * lgl, int lit, int red, int lidx) {
#ifndef NDEBUG
  int * p = lglidx2lits (lgl, red, lidx), other;
  while ((other = *p++)) {
    assert (!lgliselim (lgl, other));
    if (other != lit) assert (lglval (lgl, other) < 0);
  }
  assert (red == 0 || red == REDCS);
#endif
  lglassign (lgl, lit, red | LRGCS, lidx);
}

static int lgldscheduled (LGL * lgl, int lit) {
  QVar * qv = lglqvar (lgl, lit);
  if (qv->enqueued) return 1;
  return qv->pos >= 0;
}

static void lglunassign (LGL * lgl, int lit) {
  int idx = abs (lit), r0, r1, tag, lidx, glue;
  QVar * qv;
  TD *  td;
  LOG (2, "unassign %d", lit);
  assert (lglval (lgl, lit) > 0);
  assert (lgl->vals[idx] == lglsgn (lit));
  lgl->vals[idx] = 0;
  lgl->unassigned++;
  assert (lgl->unassigned > 0);
  qv = lglqvar (lgl, idx);
  if (qv->enqueued) assert (qv->pos >= 0);
  else if (qv->pos < 0) lgldsched (lgl, idx);
  td = lgltd (lgl, idx);
  r0 = td->rsn[0];
  if (!(r0 & REDCS)) return;
  tag = r0 & MASKCS;
  if (tag != LRGCS) return;
  r1 = td->rsn[1];
  glue = r1 & GLUEMASK;
  if (td->lrglue) {
    assert (lgl->lrgluereasons > 0);
    lgl->lrgluereasons--;
  }
  if (glue < MAXGLUE) return;
  lidx = r1 >> GLUESHFT;
  LOG (2, "eagerly deleting maximum glue clause at %d", lidx);
  lglrststk (&lgl->red[glue], lidx);
}

static Val lglifixed (LGL * lgl, int lit) {
  int res;
  if (!(res = lglval (lgl, lit))) return 0;
  if (lglevel (lgl, lit) > 0) return 0;
  return res;
}

static void lglbacktrack (LGL * lgl, int level) {
  int lit;
  assert (level >= 0);
  assert (lgl->level > level);
  if (lgl->stats->stability.level > 0) {
    LOG (2, "cancelling restart stability computation");
    lgl->stats->stability.level = 0;
  }
  LOG (2, "backtracking to level %d", level);
  assert (level <= lgl->level);
  assert (abs (lgl->failed) != 1 || lgl->failed == -1);
  if (lgl->failed &&
      lgl->failed != -1 &&
      lglevel (lgl, lgl->failed) > level) {
    LOG (2, "resetting failed assumption %d", lgl->failed);
    lgl->failed = 0;
  }
  while (!lglmtstk (&lgl->trail)) {
    lit = lgltopstk (&lgl->trail);
    assert (abs (lit) > 1);
    if (lglevel (lgl, lit) <= level) break;
    lglunassign (lgl, lit);
    lgl->trail.top--;
  }
  if (!level) {
    assert (!lgl->lrgluereasons);
    while (!lglmtstk (&lgl->red[MAXGLUE])) {
      int tmp = lglpopstk (&lgl->red[MAXGLUE]);
      assert (tmp >= NOTALIT);
      (void) tmp;
    }
  }
  if (lgl->alevel > level) {
    LOG (2,
	 "resetting assumption decision level to %d from %d",
	 level, lgl->alevel);
    lgl->alevel = level;
    if (lgl->assumed) {
      LOG (2,
	   "resetting assumption queue level to 0 from %d",
	   lgl->assumed);
      lgl->assumed = 0;
    }
  }
  lgl->level = level;
  lglrstcontrol (lgl, level + 1);
  assert (lglcntctk (&lgl->control) == lgl->level + 1);
  lgl->conf.lit = 0;
  lgl->conf.rsn[0] = lgl->conf.rsn[1] = 0;
  lgl->next2 = lgl->next = lglcntstk (&lgl->trail);
#ifndef NDEBUG
  if (lgl->prevglue == MAXGLUE) {
    lglclnstk (&lgl->prevclause);
    lgl->prevglue = -1;
  }
#endif
  LOG (2, "backtracked ");
}

static int lglmarked (LGL * lgl, int lit) {
  int res = lglavar (lgl, lit)->mark;
  if (lit < 0) res = -res;
  return res;
}

/*------------------------------------------------------------------------*/

static void lglunit (LGL * lgl, int lit) {
  ASSERT (!lgl->level);
  LOG (1, "unit %d", lit);
  lglassign (lgl, lit, RMSHFTLIT (lit) | UNITCS, 0);
}

static void lglmark (LGL * lgl, int lit) {
  lglavar (lgl, lit)->mark = lglsgn (lit);
}

static void lglmarkunmarked (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  assert (!av->mark);
  av->mark = lglsgn (lit);
}

static void lglunmark (LGL * lgl, int lit) { lglavar (lgl, lit)->mark = 0; }

static void lglchksimpcls (LGL * lgl) {
#ifndef NDEBUG
  int *p, tmp, lit;
  AVar * av;
  for (p = lgl->clause.start; (lit = *p); p++) {
    tmp = lglifixed (lgl, lit);
    assert (!tmp);
    av = lglavar (lgl, lit);
    assert (!av->simp);
    av->simp = 1;
  }
  while (p > lgl->clause.start)
    lglavar (lgl,  *--p)->simp = 0;
#endif
}

static int lglcval (LGL * lgl, int litorval) {
  assert (litorval);
  if (litorval == 1 || litorval == -1) return litorval;
  return lglval (lgl, litorval);
}

/*------------------------------------------------------------------------*/

static int lglisimpcls (LGL * lgl) {
  int * p, * q = lgl->clause.start, lit, satisfied, val, mark;
#ifndef NLGLOG
  int simplified;
#endif

  satisfied = 0;

#ifndef NDEBUG
  for (p = q; (lit = *p); p++) assert (!lglmarked (lgl, lit));
#endif

  for (p = q; (lit = *p); p++) {
    if (satisfied) continue;
    val = lglval (lgl, lit);
    if (val > 0) {
      LOG (4, "literal %d satisfies clauses", lit);
      satisfied = 1;
      continue;
    }
    if (val < 0) {
      LOG (4, "removing false literal %d", lit);
      continue;
    }
    mark = lglmarked (lgl, lit);
    if (mark > 0) {
      LOG (4, "removing duplicated literal %d", lit);
      continue;
    }
    if (mark < 0) {
      LOG (4, "literals %d and %d occur both", -lit, lit);
      satisfied = 1;
      continue;
    }
    *q++ = lit;
    lglmark (lgl, lit);
  }

  *q = 0;
  lgl->clause.top = q + 1;
#ifndef NLGLOG
  simplified = (lgl->clause.top != q + 1);
#endif

  if (satisfied) LOG (2, "simplified clause is trivial");
  else
    LOGCLS (2, lgl->clause.start,
      "%s simplified clause", simplified ? "changed" : "unchanged");

  while (q > lgl->clause.start) lglunmark (lgl, *--q);

  return satisfied;
}

static int lglesimpcls (LGL * lgl) {
  int * p, * q = lgl->clause.start, lit, satisfied, val, mark;
#if !defined(NLGLOG) || (!defined(NLGLDRUPLIG) && !defined(NDEBUG))
  int simplified;
#endif

  satisfied = 0;

#ifndef NDEBUG
  for (p = q; (lit = *p); p++)
    assert (abs (lit) == 1 || !lglmarked (lgl, lit));
#endif

  for (p = q; !satisfied && (lit = *p); p++) {
    val = lglcval (lgl, lit);
    if (val > 0) {
      LOG (4, "literal %d satisfies clauses", lit);
      satisfied = 1;
      continue;
    }
    if (val < 0) {
      LOG (4, "removing false literal %d", lit);
      continue;
    }
    mark = lglmarked (lgl, lit);
    if (mark > 0) {
      LOG (4, "removing duplicated literal %d", lit);
      continue;
    }
    if (mark < 0) {
      LOG (4, "literals %d and %d occur both", -lit, lit);
      satisfied = 1;
      continue;
    }
    *q++ = lit;
    lglmark (lgl, lit);
  }

  *q = 0;
  lgl->clause.top = q + 1;
#if !defined(NLGLOG) || (!defined(NLGLDRUPLIG) && !defined(NDEBUG))
  simplified = (lgl->clause.top != q + 1);
#endif

  if (satisfied) LOG (2, "simplified clause is trivial");
  else
    LOGCLS (2, lgl->clause.start,
      "%s simplified clause", simplified ? "changed" : "unchanged");

  while (q > lgl->clause.start) lglunmark (lgl, *--q);

#ifndef NLGLDRUPLIG
  if (lgldruplig (lgl)) {
    int different = (lglcntstk (&lgl->eclause) != lglcntstk (&lgl->clause));
    assert (!simplified || different);
    if (!satisfied && different) lgldrupligaddcls (lgl, REDCS);
    if (satisfied || different) {
      const int * p;
      int elit;
      for (p = lgl->eclause.start; (elit = *p); p++)
	druplig_add_literal (lgl->druplig, elit);
      lgldrupligreallydel (lgl);
    }
  }
#endif

  return satisfied;
}

static void lglorderclsaux (LGL * lgl, int * start) {
  int * p, max = 0, level, lit, val;
  for (p = start; (lit = *p); p++) {
    if ((val = lglval (lgl, lit)) < 0) level = lglevel (lgl, lit);
    else if (val > 0) level = INT_MAX - 1;
    else assert (!val), level = INT_MAX;
    if (level <= max) continue;
    max = level;
    *p = start[0];
    start[0] = lit;
  }
}

static void lglordercls (LGL * lgl) {
  assert (lglcntstk (&lgl->clause) > 2);
  lglorderclsaux (lgl, lgl->clause.start);
  LOG (3, "head literal %d", lgl->clause.start[0]);
  lglorderclsaux (lgl, lgl->clause.start  + 1);
  LOG (3, "tail literal %d", lgl->clause.start[1]);
  LOGCLS (3, lgl->clause.start, "ordered clause");
}
/*------------------------------------------------------------------------*/


static void lglfreewch (LGL * lgl, int oldoffset, int oldhcount) {
  int ldoldhcount = lglceild (oldhcount);
  lgl->wchs->stk.start[oldoffset] = lgl->wchs->start[ldoldhcount];
  assert (oldoffset);
  lgl->wchs->start[ldoldhcount] = oldoffset;
  lgl->wchs->free++;
  assert (lgl->wchs->free > 0);
  LOG (5, "saving watch stack at %d of size %d on free list %d",
       oldoffset, oldhcount, ldoldhcount);
}

static void lglshrinkhts (LGL * lgl, HTS * hts, int newcount) {
  int * p, i, oldcount = hts->count;
  assert (newcount <= oldcount);
  if (newcount == oldcount) return;
  p = lglhts2wchs (lgl, hts);
  for (i = newcount; i < oldcount; i++) p[i] = 0;
  hts->count = newcount;
  if (newcount) return;
  lglfreewch (lgl, hts->offset, oldcount);
  hts->offset = 0;
}

static long lglenlwchs (LGL * lgl, HTS * hts) {
  int oldhcount = hts->count, oldoffset = hts->offset, newoffset;
  int oldwcount, newwcount, oldwsize, newwsize, i, j;
  int newhcount = oldhcount ? 2*oldhcount : 1;
  int * oldwstart, * newwstart, * start;
  int ldnewhcount = lglfloorld (newhcount);
  long res = 0;

  newhcount = (1<<ldnewhcount);
  assert (newhcount > oldhcount);

  LOG (5, "increasing watch stack at %d from %d to %d",
       oldoffset, oldhcount, newhcount);

  assert (!oldoffset == !oldhcount);

  lgl->stats->enlwchs++;

  newoffset = lgl->wchs->start[ldnewhcount];
  start = lgl->wchs->stk.start;
  if (newoffset != INT_MAX) {
    lgl->wchs->start[ldnewhcount] = start[newoffset];
    start[newoffset] = 0;
    assert (lgl->wchs->free > 0);
    lgl->wchs->free--;
    LOG (5, "reusing free watch stack at %d of size %d",
	 newoffset, (1 << ldnewhcount));
  } else {
    assert (lgl->wchs->stk.start[hts->offset]);
    assert (lgl->wchs->stk.top[-1] == INT_MAX);

    oldwcount = lglcntstk (&lgl->wchs->stk);
    newwcount = oldwcount + newhcount;
    oldwsize = lglszstk (&lgl->wchs->stk);
    newwsize = oldwsize;

    assert (lgl->wchs->stk.top == lgl->wchs->stk.start + oldwcount);
    assert (oldwcount > 0);

    while (newwsize < newwcount) newwsize *= 2;
    if (newwsize > oldwsize) {
      newwstart = oldwstart = lgl->wchs->stk.start;
      RSZ (newwstart, oldwsize, newwsize);
      LOG (3, "resized global watcher stack from %d to %d",
	   oldwsize, newwsize);
      res = newwstart - oldwstart;
      if (res) {
	LOG (3, "moved global watcher stack by %ld", res);
	start = lgl->wchs->stk.start = newwstart;
      }
      lgl->wchs->stk.end = start + newwsize;
    }
    lgl->wchs->stk.top = start + newwcount;
    lgl->wchs->stk.top[-1] = INT_MAX;
    newoffset = oldwcount - 1;
    LOG (5,
	 "new watch stack of size %d at end of global watcher stack at %d",
	 newhcount, newoffset);
  }
  assert (start == lgl->wchs->stk.start);
  assert (start[0]);
  j = newoffset;
  for (i = oldoffset; i < oldoffset + oldhcount; i++) {
    start[j++] = start[i];
    start[i] = 0;
  }
  while (j < newoffset + newhcount)
    start[j++] = 0;
  assert (start + j <= lgl->wchs->stk.top);
  hts->offset = newoffset;
  if (oldhcount > 0) lglfreewch (lgl, oldoffset, oldhcount);
  return res;
}

static long lglpushwch (LGL * lgl, HTS * hts, int wch) {
  long res = 0;
  int * wchs = lglhts2wchs (lgl, hts);
  assert (sizeof (res) == sizeof (void*));
  assert (hts->count >= 0);
  if (wchs[hts->count]) {
    res = lglenlwchs (lgl, hts);
    wchs = lglhts2wchs (lgl, hts);
  }
  assert (!wchs[hts->count]);
  assert (wch != INT_MAX);
  wchs[hts->count++] = wch;
  lgl->stats->pshwchs++;
  assert (lgl->stats->pshwchs > 0);
  return res;
}

static long lglwchbin (LGL * lgl, int lit, int other, int red) {
  HTS * hts = lglhts (lgl, lit);
  int cs = (RMSHFTLIT (other) | BINCS | red);
  long res;
  assert (red == 0 || red == REDCS);
  res = lglpushwch (lgl, hts, cs);
  LOG (3, "new %s binary watch %d blit %d", lglred2str (red), lit, other);
  return res;
}

static long lglwchtrn (LGL * lgl, int a, int b, int c, int red) {
  HTS * hts = lglhts (lgl, a);
  int cs = (RMSHFTLIT (b) | TRNCS | red);
  long res;
  assert (red == 0 || red == REDCS);
  res = lglpushwch (lgl, hts, cs);
  res += lglpushwch (lgl, hts, c);
  LOG (3, "new %s ternary watch %d blits %d %d", lglred2str (red), a, b, c);
  return res;
}

static long lglwchlrg (LGL * lgl, int lit, int other, int red, int lidx) {
  HTS * hts = lglhts (lgl, lit);
  int blit = (RMSHFTLIT (other) | LRGCS | red);
  long res = 0;
  assert (red == 0 || red == REDCS);
  res += lglpushwch (lgl, hts, blit);
  res += lglpushwch (lgl, hts, lidx);
#ifndef NLGLOG
  {
    int * p = lglidx2lits (lgl, red, lidx);
    if (red)
      LOG (3,
	   "watching %d with blit %d in red[%d][%d] %d %d %d %d%s",
	   lit, other, (lidx & GLUEMASK), (lidx >> GLUESHFT),
	   p[0], p[1], p[2], p[3], (p[4] ? " ..." : ""));
    else
      LOG (3,
       "watching %d with blit %d in irr[%d] %d %d %d %d%s",
       lit, other, lidx, p[0], p[1], p[2], p[3], (p[4] ? " ..." : ""));
  }
#endif
  assert (sizeof (res) == sizeof (void*));
  return res;
}

/*------------------------------------------------------------------------*/

static EVar * lglevar (LGL * lgl, int lit) {
  int idx = abs (lit);
  assert (1 <= idx && idx < lgl->nvars);
  return lgl->evars + idx;
}

static int * lglepos (LGL * lgl, int lit) {
  EVar * ev;
  int * res;
  ev = lglevar (lgl, lit);
  res = &ev->pos;
  return res;
}

static int lglecmp (LGL * lgl, int l, int k) {
  return lglevar (lgl,k)->score - lglevar (lgl,l)->score;
}

#ifndef NDEBUG
static void lglchkesched (LGL * lgl) {
  int * p, parent, child, ppos, cpos, size, i, tmp;
  Stk * s = &lgl->esched;
  size = lglcntstk (s);
  p = s->start;
  for (ppos = 0; ppos < size; ppos++) {
    parent = p[ppos];
    tmp = *lglepos (lgl, parent);
    assert (ppos == tmp);
    for (i = 0; i <= 1; i++) {
      cpos = 2*ppos + 1 + i;
      if (cpos >= size) continue;
      child = p[cpos];
      tmp = *lglepos (lgl, child);
      assert (cpos == tmp);
      assert (lglecmp (lgl, parent, child) >= 0);
    }
  }
}
#endif

static void lgleup (LGL * lgl, int lit) {
  int child = lit, parent, cpos, ppos, * p, * cposptr, * pposptr;
  Stk * s = &lgl->esched;
  p = s->start;
  cposptr = lglepos (lgl, child);
  cpos = *cposptr;
  assert (cpos >= 0);
  while (cpos > 0) {
    ppos = (cpos - 1)/2;
    parent = p[ppos];
    if (lglecmp (lgl, parent, lit) >= 0) break;
    pposptr = lglepos (lgl, parent);
    assert (*pposptr == ppos);
    p[cpos] = parent;
    *pposptr = cpos;
    LOGESCHED (5, parent, "down from %d", ppos);
    cpos = ppos;
  }
  if (*cposptr == cpos) return;
#ifndef NLGLOG
  ppos = *cposptr;
#endif
  *cposptr = cpos;
  p[cpos] = lit;
  LOGESCHED (5, lit, "up from %d", ppos);
#ifndef NDEBUG
  if (lgl->opts->check.val >= 2) lglchkesched (lgl);
#endif
}

static void lgledown (LGL * lgl, int lit) {
  int parent = lit, child, right, ppos, cpos;
  int * p, * pposptr, * cposptr, size;
  Stk * s = &lgl->esched;
  size = lglcntstk (s);
  p = s->start;
  pposptr = lglepos (lgl, parent);
  ppos = *pposptr;
  assert (0 <= ppos);
  for (;;) {
    cpos = 2*ppos + 1;
    if (cpos >= size) break;
    child = p[cpos];
    if (cpos + 1 < size) {
      right = p[cpos + 1];
      if (lglecmp (lgl, child, right) < 0)
	cpos++, child = right;
    }
    if (lglecmp (lgl, child, lit) <= 0) break;
    cposptr = lglepos (lgl, child);
    assert (*cposptr = cpos);
    p[ppos] = child;
    *cposptr = ppos;
    LOGESCHED (5, child, "up from %d", cpos);
    ppos = cpos;
  }
  if (*pposptr == ppos) return;
#ifndef NLGLOG
  cpos = *pposptr;
#endif
  *pposptr = ppos;
  p[ppos] = lit;
  LOGESCHED (5, lit, "down from %d", cpos);
#ifndef NDEBUG
  if (lgl->opts->check.val >= 2) lglchkesched (lgl);
#endif
}

static int lglifrozen (LGL * lgl, int ilit) {
  int elit = lglexport (lgl, ilit);
  Ext * ext = lglelit2ext (lgl, elit);
  return ext->frozen || ext->tmpfrozen;
}

static void lglesched (LGL * lgl, int lit) {
  AVar * av;
  int * p;
  Stk * s;
  if (lgl->cceing) return;
  if (lglifrozen (lgl, lit)) return;
  if (!lglisfree (lgl, lit)) return;
  if (lgl->donotsched) {
    av = lglavar (lgl, lit);
    if (lgl->eliminating && av->donotelm) return;
    if (lgl->blocking && av->donotblk) return;
  }
  p = lglepos (lgl, lit);
  s = &lgl->esched;
  if (*p >= 0) return;
  *p = lglcntstk (s);
  lglpushstk (lgl, s, lit);
  lgleup (lgl, lit);
  lgledown (lgl, lit);
  LOGESCHED (4, lit, "pushed");
}

/*------------------------------------------------------------------------*/

static unsigned lglgcd (unsigned a, unsigned b) {
  unsigned tmp;
  assert (a), assert (b);
  if (a < b) SWAP (unsigned, a, b);
  while (b) tmp = b, b = a % b, a = tmp;
  return a;
}

static int lglrandidxtrav (LGL * lgl, int (*fun)(LGL*,int idx)) {
  int idx, delta, mod, prev, first, res;
  first = mod = lglmax (lgl->nvars, 2);
  idx = lglrand (lgl) % mod;
  delta = lglrand (lgl) % mod;
  if (!delta) delta++;
  while (lglgcd (delta, mod) > 1)
    if (++delta == mod) delta = 1;
  res = 1;
  LOG (2,
    "random index traversal start %d delta %d mod %d",
     idx, delta, mod);
  while (res) {
    if (idx >= 2 && !fun (lgl, idx)) res = 0;
    else {
      prev = idx;
      idx += delta;
      if (idx >= mod) idx -= mod;
      if (idx == first) break;
      if (first == mod) first = prev;
    }
  }
  return res;
}

static int lglrem (LGL * lgl) {
  int res = lgl->nvars;
  if (!res) return 0;
  assert (res >= 2);
  res -= lgl->stats->fixed.current + 2;
  assert (res >= 0);
  return res;
}

static double lglpcnt (double n, double d) {
  if (d <= 0 || !n) return 0.0;
  return 100.0 * n / d;
}

static int lglecalc (LGL * lgl, EVar * ev) {
  int oldscore = ev->score, o0 = ev->occ[0], o1 = ev->occ[1], newscore;
  if (!o0 || !o1) newscore = 0;
  else newscore = o0 + o1;
  ev->score = newscore;
  return newscore - oldscore;
}

static int lglocc (LGL * lgl, int lit) {
  if (!lgl->occs) return lglhts (lgl, lit)->count;
  return lglevar (lgl, lit)->occ[lit < 0];
}

static void lglflushtouched (LGL * lgl) {
  int * q, idx, mt = 0, * pos = lgl->elm->touched.pos, newpos = 0;
  Stk * touched = &lgl->elm->touched.stk;
  const int * p;
  for (p = q = touched->start; p < touched->top; p++) {
    if ((idx = *p)) {
      assert (1 < idx), assert (idx < lgl->elm->touched.nvars);
      pos[idx] = newpos++;
      *q++ = idx; 
    } else mt++;
  }
  LOG (2, "flushed %d empty entries on touched stack kept %d", mt, newpos);
  assert (lgl->elm->touched.mt == mt);
  lgl->elm->touched.mt = 0;
  touched->top = q;
}

static void lgltouch (LGL * lgl, int lit) {
  int idx = abs (lit), * posptr, oldpos, newpos;
  assert (lgl->elm);
  posptr = lgl->elm->touched.pos + idx;
  newpos = lglcntstk (&lgl->elm->touched.stk);
  oldpos = *posptr;
  assert (oldpos < 0 || lglpeek (&lgl->elm->touched.stk, oldpos) == idx);
  LOG (4, "touching %d (moved to %d from %d)", idx, newpos, oldpos);
  lglpushstk (lgl, &lgl->elm->touched.stk, idx);
  *posptr = newpos;
  if (oldpos >= 0) {
    lglpoke (&lgl->elm->touched.stk, oldpos, 0);
    lgl->elm->touched.mt++;
    if (lgl->elm->touched.mt > lgl->elm->touched.nvars)
      lglflushtouched (lgl);
  }
}

static int lglpoptouched (LGL * lgl) {
#if !defined(NDEBUG) || !defined(NLGLOG)
  int pos;
#endif
  int res, * posptr;
  assert (lgl->elm);
  for (;;) {
    if (lglmtstk (&lgl->elm->touched.stk)) return 0;
    if ((res = lglpopstk (&lgl->elm->touched.stk))) break;
    assert (lgl->elm->touched.mt > 0);
    lgl->elm->touched.mt--;
  }
#if !defined(NDEBUG) || !defined(NLGLOG)
  pos = lglcntstk (&lgl->elm->touched.stk);
#endif
  assert (1 < res), assert (res < lgl->elm->touched.nvars);
  posptr = lgl->elm->touched.pos + res;
  assert (*posptr >= 0), assert (*posptr == pos);
  *posptr = -1;
  LOG (4, "popped touched %d at position %d", res, pos);
  return res;
}

static int lgltouched (LGL * lgl, int lit) {
  int idx = abs (lit);
  assert (1 < idx), assert (idx < lgl->elm->touched.nvars);
  return lgl->elm->touched.pos[idx] >= 0;
}

static void lglincocc (LGL * lgl, int lit) {
  int idx, sign, change;
  EVar * ev;
  if (!lgl->occs) return;
  idx = abs (lit), sign = (lit < 0);
  ev = lglevar (lgl, lit);
  assert (lglisfree (lgl, lit));
  ev->occ[sign] += 1;
  assert (ev->occ[sign] > 0);
  change = lglecalc (lgl, ev);
  LOG (3,
    "inc occ of %d now occs[%d] = %d %d",
    lit, idx, ev->occ[0], ev->occ[1]);
  if (ev->pos < 0) lglesched (lgl, idx);
  else if (change > 0) lgledown (lgl, idx);
  else if (change < 0) lgleup (lgl, idx);
  if (lgl->touching) lgltouch (lgl, lit);
}

static int lglisact (int act) { return NOTALIT <= act && act < REMOVED-1; }

static int lglrescoreglue (LGL * lgl, int glue) {
  int * c, * p, oldact, newact, count = 0;
  const int retireint = lgl->opts->retireint.val;
  Stk * lir = lgl->red + glue;
  for (c = lir->start; c < lir->top; c = p + 1) {
    oldact = *c;
    if (oldact == REMOVED) {
      for (p = c + 1; p < lir->top && *p == REMOVED; p++)
	;
      assert (p >= lir->top || *p < NOTALIT || lglisact (*p));
      p--;
    } else if (NOTALIT + retireint < oldact) {
      assert (NOTALIT + retireint <= oldact && oldact <= REMOVED - 1);
      newact = (oldact - NOTALIT - retireint + 1) / 2;
      newact += NOTALIT + retireint;
      assert (newact < REMOVED);
      *c++ = newact;
      LOGCLS (5, c,
        "rescoring activity from %d to %d of clause",
	oldact - NOTALIT, newact - NOTALIT);
      for (p = c; *p; p++)
	;
      count++;
    } else {
      for (p = c + 1; *p; p++)
	;
    }
  }
  return count;
}

static void lglrescoreclauses (LGL * lgl) {
  int glue, count = 0;
  lgl->stats->rescored.clauses++;
  for (glue = 0; glue < MAXGLUE; glue++)
    count += lglrescoreglue (lgl, glue);
  lglprt (lgl, 3,
    "[rescored-clauses-%d] rescored activity of %d clauses",
    lgl->stats->rescored.clauses, count);
}

static void lglchkirrstats (LGL * lgl) {
#if  0
  int idx, sign, lit, blit, tag, red, other, other2, clauses, lits;
  const int * p, * w, * eow, * c, * top;
  HTS * hts;
  clauses = lits = 0;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	red = blit & REDCS;
	if (red) continue;
	if (tag == BINCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  lits += 2;
	} else if (tag == TRNCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  lits += 3;
	} else continue;
	clauses++;
      }
    }
  top = lgl->irr.top;
  for (c = lgl->irr.start; c < top; c = p + 1) {
    if (*(p = c) >= NOTALIT) continue;
    while (*++p)
      ;
    lits += p - c;
    clauses++;
  }
  assert (clauses == lgl->stats->irr.clauses.cur);
  assert (lits == lgl->stats->irr.lits.cur);
#else
  (void) lgl;
#endif
}

static void lglincirr (LGL * lgl, int size) {
  if (size < 2) return;
  lgl->stats->irr.clauses.cur++;
  assert (lgl->stats->irr.clauses.cur > 0);
  if (lgl->stats->irr.clauses.cur > lgl->stats->irr.clauses.max)
    lgl->stats->irr.clauses.max = lgl->stats->irr.clauses.cur;
  lgl->stats->irr.lits.cur += size;
  assert (lgl->stats->irr.lits.cur >= size);
  if (lgl->stats->irr.lits.cur > lgl->stats->irr.lits.max)
    lgl->stats->irr.lits.max = lgl->stats->irr.lits.cur;
  lgl->stats->irrprgss++;
}

static void lgldecirr (LGL * lgl, int size) {
  assert (size >= 2);
  assert (lgl->stats->irr.clauses.cur > 0);
  lgl->stats->irr.clauses.cur--;
  assert (lgl->stats->irr.lits.cur >= size);
  lgl->stats->irr.lits.cur -= size;
  assert (!lgl->stats->irr.clauses.cur == !lgl->stats->irr.lits.cur);
  lgl->stats->irrprgss++;
}

static void lglincglag (LGL * lgl) {
  if (lgl->glag == MAXGLAG) {
    int idx;
    for (idx = 2; idx < lgl->nvars; idx++)
      lglqvar (lgl, idx)->glag = -1;
    lgl->glag = 0;
  } else lgl->glag++;
  LOG (4, "new glue flag %d", lgl->glag);
}

static int lglaged (LGL * lgl, int lit) {
  int level = lglevel (lgl, lit);
  QVar * qv;
  if (!level++) return 1;
  assert (2 <= level), assert (level < lgl->nvars);
  qv = lglqvar (lgl, level);
  assert (qv->glag <= lgl->glag);
  if (qv->glag >= lgl->glag) return 1;
  assert (0 <= lgl->glag), assert (lgl->glag <= MAXGLAG);
  qv->glag = lgl->glag;
  assert (0 <= qv->glag);
  return 0;
}

static const int lglar1scalegluetab[POW2GLUE] =
{
// 0  1  2  3  4  5  6  7  8  9  10  11  12  13  14  15
   0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
};

static const int lglar2scalegluetab[POW2GLUE] =
{
// 0  1  2  3   4   5   6   7   8   9  10  11  12  13   14   15
   0, 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120
};

static const int lglsqrtscalegluetab[POW2GLUE] = 
{
// 0  1  2  3   4   5   6   7   8   9  10  11    12   13   14   15
   0, 1, 2, 5, 10, 17, 26, 37, 50, 65, 82, 101, 122, 145, 170, 197
};

static const int lglsqrtldscalegluetab[POW2GLUE] =
{
// 0  1  2  3   4   5   6   7   8   9  10   11   12   13    14    15
   0, 1, 2, 5, 10, 17, 26, 37, 50, 65, 82, 122, 226, 530, 1522, 5042
};

static const int lglldscalegluetab[POW2GLUE] =
{
// 0  1  2  3   4   5   6    7    8    9    10    11    12    13     14     15
   0, 1, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768
};


static int lglsearchscaleglue (int unscaled, const int * tab) {
  int res;
  for (res = 0; res < POW2GLUE && tab[res + 1] <= unscaled; res++)
    ;
  return res;
}

#define LGLSEARCHSCALEGLUE(NAME,GLUE) \
  lglsearchscaleglue (GLUE, lgl ## NAME ## scalegluetab)

static int lglunboundedscaleglue (LGL * lgl, int origlue) {
  int res, red;
  assert (0 <= origlue);
  if (origlue <= lgl->opts->gluekeep.val) res = 0;
  else {
    red = origlue - lgl->opts->gluekeep.val;
    assert (red >= 1);
    switch (lgl->opts->gluescale.val) {
      default:
      case 1: res = LGLSEARCHSCALEGLUE (ar1, red); break;
      case 2: res = LGLSEARCHSCALEGLUE (ar2, red); break;
      case 3: res = LGLSEARCHSCALEGLUE (sqrt, red); break;
      case 4: res = LGLSEARCHSCALEGLUE (sqrtld, red); break;
      case 5: res = LGLSEARCHSCALEGLUE (ld, red); break;
    }
    assert (res > 0);
    if (res > MAXGLUE) res = MAXGLUE;
  }
  assert (0 <= res), assert (res <= MAXGLUE);
  return res;
}

static int lglscaleglue (LGL * lgl, int origlue) {
  int res = lglunboundedscaleglue (lgl, origlue);
  if (lgl->opts->maxscaledglue.val <= res)
    res = MAXGLUE;
  assert (0 <= res), assert (res <= MAXGLUE);
  return res;
}

static int lglunscaleglue (LGL * lgl, int scaledglue) {
  int res = 0;
  assert (0 <= scaledglue), assert (scaledglue <= MAXGLUE);
  if (!scaledglue) res = 0;
  else {
    switch (lgl->opts->gluescale.val) {
      default:
      case 1: res = lglar1scalegluetab[scaledglue]; break;
      case 2: res = lglar2scalegluetab[scaledglue]; break;
      case 3: res = lglsqrtldscalegluetab[scaledglue]; break;
      case 4: res = lglsqrtldscalegluetab[scaledglue]; break;
      case 5: res = lglldscalegluetab[scaledglue]; break;
    }
    res += lgl->opts->gluekeep.val;
  }
  assert (lglunboundedscaleglue (lgl, res) == scaledglue);
  assert (!res || lglunboundedscaleglue (lgl, res - 1) == scaledglue - 1);
  return res;
}

static int lglcheckgluereduced (LGL * lgl, int lidx,
                               int gluelim, int sizelim,
			       int * newunscaledglueptr) {
  int oldscaledglue, newunscaledglue, newscaledglue, lit, pos, size;
  const int * c;
  Stk * lir;
  oldscaledglue = (lidx & GLUEMASK);
  if (!oldscaledglue) return 0;
  if (oldscaledglue >= MAXGLUE) return 0;
  lglincglag (lgl);
  lir = lgl->red + oldscaledglue;
  pos = lidx >> GLUESHFT;
  assert (pos > 0);
  c = lir->start + pos;
  if (c > lir->top) return 0;
  if (c[0] >= REMOVED) return 0;
  assert (lir->start < c && c < lir->end);
  size = newunscaledglue = 0;
  while ((lit = c[size])) {
    if (++size > sizelim) return 0;
    if (lglaged (lgl, lit)) continue;
    if (++newunscaledglue > gluelim) return 0;
  }
  newscaledglue = lglscaleglue (lgl, newunscaledglue);
  if (oldscaledglue <= newscaledglue) return 0;
  LOG (4,
    "old scaled glue %d size %d clause at %d has new scaled glue %d"
    " (unscaled %d)",
    oldscaledglue, size, pos, newscaledglue, newunscaledglue);
  if (newunscaledglueptr) *newunscaledglueptr = newunscaledglue;
  return 1;
}

static void lglcheckpromotion (LGL * lgl, int lidx) {
  const int gluelim = lgl->opts->promotegluelim.val;
  int glue;
  if (!lgl->opts->promote.val) return;
  glue = lidx & GLUEMASK;
  if (!glue) return;
  if (glue >= MAXGLUE) return;
  if (!lglcheckgluereduced (lgl, lidx, gluelim, INT_MAX, 0)) return;
  LOG (4,
    "saving clause idx red[%d][%d] on promotion stack",
    glue, (lidx >> GLUESHFT));
  lglpushstk (lgl, &lgl->promote, lidx);
  lgl->stats->promote.tried++;
}

static void lglbumplidx (LGL * lgl, int lidx) {
  int glue = (lidx & GLUEMASK), * c, *ap, act, pos;
  const int retirenb = lgl->opts->retirenb.val;
  const int retireint = lgl->opts->retireint.val;
  Stk * lir = lgl->red + glue;
  if (lgl->simp && !lgl->opts->bumpsimp.val) return;
  if (glue >= MAXGLUE) return;
  pos = lidx >> GLUESHFT;
  c = lir->start + pos;
  assert (lir->start < c && c < lir->end);
  ap = c - 1;
  act = *ap;
  if (act < REMOVED - 1) {
    LGLCHKACT (act);
    act += 1;
    if (retirenb && act < NOTALIT + retireint) act = NOTALIT + retireint;
    LGLCHKACT (act);
    *ap = act;
  }
  LOGCLS (4, c, "bumped activity to %d of glue %d clause", act-NOTALIT, glue);
  lgl->stats->lir[glue].resolved++;
  assert (lgl->stats->lir[glue].resolved > 0);
  if (act >= REMOVED - 1) lglrescoreclauses (lgl);
}

static void lglbumpnupdatelidx (LGL * lgl, int lidx) {
  lglbumplidx (lgl, lidx);
  lglcheckpromotion (lgl, lidx);
}

static void lglincjwh (LGL * lgl, int lit, Flt inc) {
  int ulit = lglulit (lit);
  Flt old = lgl->jwh[ulit];
  Flt new = lgladdflt (old, inc);
  lgl->jwh[ulit] = new;
}

static void lglmtaux (LGL * lgl, int red) {
  assert (!red || red == REDCS);
  if (lgl->mt) return;
  LOG (1, "adding empty clause");
  lgl->mt = 1;
  lgldrupligaddclsarg (lgl, red, 0);
}

static void lglmt (LGL * lgl) { lglmtaux (lgl, REDCS); }

static int lgladdcls (LGL * lgl, int red, int origlue, int force) {
  int size, lit, other, other2, * p, lidx, unit, blit;
  int64_t * maxbytesptr, bytes;
  int scaledglue, prevglue;
  Flt inc;
  Val val;
  Stk * w;
  lgl->stats->prgss++;
  if (lgl->eliminating) {
    size = lglcntstk (&lgl->clause);
    ADDSTEPS (elm.steps, size);
  }
  if (!red) lgl->stats->irrprgss++;
  assert (!lglmtstk (&lgl->clause));
  assert (!lgl->clause.top[-1]);
  if (force) lglchksimpcls (lgl);
  size = lglcntstk (&lgl->clause) - 1;
  if (!red) lglincirr (lgl, size);
  else if (size == 2) lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
  else if (size == 3) lgl->stats->red.trn++, assert (lgl->stats->red.trn > 0);
  assert (size >= 0);
  if (!size) {
    lglmtaux (lgl, red);
    return 0;
  }
  lit = lgl->clause.start[0];
  if (size == 1) {
    assert (lglval (lgl, lit) >= 0);
    if (!lglval (lgl, lit)) lglunit (lgl, lit);
    return 0;
  }
  inc = lglflt (-size, 1);
  other = lgl->clause.start[1];
  if (size == 2) {
    lglwchbin (lgl, lit, other, red);
    lglwchbin (lgl, other, lit, red);
    if (red) {
      if (force && lglval (lgl, lit) < 0) lglf2rce (lgl, other, lit, REDCS);
      if (force && lglval (lgl, other) < 0) lglf2rce (lgl, lit, other, REDCS);
    } else if (lgl->dense) {
      assert (!red);
      lglincocc (lgl, lit);
      lglincocc (lgl, other);
    }
    if (!red) lglincjwh (lgl, lit, inc), lglincjwh (lgl, other, inc);
    return 0;
  }
  lglordercls (lgl);
  lit = lgl->clause.start[0];
  other = lgl->clause.start[1];
  if (size == 3) {
    other2 = lgl->clause.start[2];
    lglwchtrn (lgl, lit, other, other2, red);
    lglwchtrn (lgl, other, lit, other2, red);
    lglwchtrn (lgl, other2, lit, other, red);
    if (red) {
      if (force && lglval (lgl, lit) < 0 && lglval (lgl, other) < 0)
	lglf3rce (lgl, other2, lit, other, REDCS);
      if (force && lglval (lgl, lit) < 0 && lglval (lgl, other2) < 0)
	lglf3rce (lgl, other, lit, other2, REDCS);
      if (force && lglval (lgl, other) < 0 && lglval (lgl, other2) < 0)
	lglf3rce (lgl, lit, other, other2, REDCS);
    } else if (lgl->dense) {
      assert (!red);
      lglincocc (lgl, lit);
      lglincocc (lgl, other);
      lglincocc (lgl, other2);
    }
    if (!red) lglincjwh (lgl, lit, inc),
              lglincjwh (lgl, other, inc),
	      lglincjwh (lgl, other2, inc);
    return 0;
  }
  assert (size > 3);
  if (red) {
    scaledglue = lglscaleglue (lgl, origlue);
    if (scaledglue == MAXGLUE &&
	lgl->opts->keepmaxglue.val &&
  !(lgl->stats->clauses.maxglue.count % lgl->opts->keepmaxglueint.val)) {
      lgl->stats->clauses.maxglue.count++;
      lgl->stats->clauses.maxglue.kept++;
      scaledglue = MAXGLUE-1;
      LOG (2,
        "reducing maximum glue %d to %d to keep clause", 
	MAXGLUE, scaledglue);
    }
    lgl->stats->clauses.scglue += scaledglue;
    if (scaledglue == MAXGLUE) {
      lgl->stats->clauses.maxglue.count++;
#ifndef NDEBUG
      lglclnstk (&lgl->prevclause);
      lgl->prevglue = -1;
#endif
    } else lgl->stats->clauses.nonmaxglue++;
    w = lgl->red + scaledglue;
    lidx = lglcntstk (w) + 1;
    if (lidx > MAXREDLIDX) {
      prevglue = scaledglue;
      if (lidx > MAXREDLIDX) {
	scaledglue = prevglue;
	while (scaledglue + 1 < MAXGLUE && lidx > MAXREDLIDX) {
	  w = lgl->red + ++scaledglue;
	  lidx = lglcntstk (w) + 1;
	}
      }
      if (lidx > MAXREDLIDX) {
	scaledglue = prevglue;
	while (scaledglue > 0 && lidx > MAXREDLIDX) {
	  w = lgl->red + --scaledglue;
	  lidx = lglcntstk (w) + 1;
	}
      }
      if (lidx > MAXREDLIDX && scaledglue < MAXGLUE) {
	w = lgl->red + (scaledglue = MAXGLUE);
	lidx = lglcntstk (w) + 1;
      }
      if (lidx > MAXREDLIDX && scaledglue == MAXGLUE) {
	lglbacktrack (lgl, 0);
	lidx = lglcntstk (w);
	assert (!lidx);
      }
      if (lidx > MAXREDLIDX)
	lgldie (lgl, "number of redundant large clause literals exhausted");
    }
    assert (w == lgl->red + scaledglue);
    maxbytesptr = &lgl->stats->lir[scaledglue].maxbytes;
    lglpushstk (lgl, w, NOTALIT);
    assert (lidx == lglcntstk (w));
    lidx <<= GLUESHFT;
    assert (0 <= lidx);
    lidx |= scaledglue;
    if (scaledglue < MAXGLUE) {
      lgl->stats->lir[scaledglue].clauses++;
      assert (lgl->stats->lir[scaledglue].clauses > 0);
    }
    lgl->stats->lir[scaledglue].added++;
    assert (lgl->stats->lir[scaledglue].added > 0);
  } else {
    w = &lgl->irr;
    maxbytesptr = &lgl->stats->irr.maxbytes;
    lidx = lglcntstk (w);
    scaledglue = 0;
    if (lidx <= 0 && !lglmtstk (w))
      lgldie (lgl, "number of irredundant large clause literals exhausted");
  }
  for (p = lgl->clause.start; (other2 = *p); p++)
    lglpushstk (lgl, w, other2), lglincjwh (lgl, other2, inc);
  lglpushstk (lgl, w, 0);
  bytes = sizeof (int) * (int64_t) lglcntstk (w);
  if (bytes > *maxbytesptr) *maxbytesptr = bytes;
  if (red) {
    unit = 0;
    for (p = lgl->clause.start; (other2 = *p); p++) {
      val = lglval (lgl, other2);
      assert (!force || val <= 0);
      if (val < 0) continue;
      if (unit) unit = INT_MAX;
      else unit = other2;
    }
    if (force && unit && unit != INT_MAX) lglflrce (lgl, unit, red, lidx);
  }
  assert (red == 0 || red == REDCS);
  if (!red || (red && scaledglue < MAXGLUE)) {
    (void) lglwchlrg (lgl, lit, other, red, lidx);
    (void) lglwchlrg (lgl, other, lit, red, lidx);
  }
  if (red && scaledglue != MAXGLUE) {
    // lglbumplidx (lgl, lidx); 		// TODO why was this here?
    lgl->stats->red.lrg++;
  }
  if (!red && lgl->dense) {
    if (lidx > MAXIRRLIDX)
      lgldie (lgl, "number of irredundant large clause literals exhausted");
    blit = (lidx << RMSHFT) | OCCS;
    for (p = lgl->clause.start; (other2 = *p); p++) {
      lglincocc (lgl, other2);
      lglpushwch (lgl, lglhts (lgl, other2), blit);
    }
  }
  lglchkirrstats (lgl);
  return lidx;
}

static void lgliadd (LGL * lgl, int ilit) {
  int size;
#ifndef NLGLOG
  if (lglmtstk (&lgl->clause)) LOG (4, "opening irredundant clause");
#endif
  assert (abs (ilit) < 2 || abs (ilit) < lgl->nvars);
  lglpushstk (lgl, &lgl->clause, ilit);
  if (ilit) {
    LOG (4, "added literal %d", ilit);
  } else {
    LOG (4, "closing irredundant clause");
    LOGCLS (3, lgl->eclause.start, "external irredundant clause");
    LOGCLS (3, lgl->clause.start, "internal unsimplified irredundant clause");
#ifndef NLGLDRUPLIG
    if (lgldruplig (lgl)) {
      const int * p;
      int other;
      for (p = lgl->eclause.start; (other = *p); p++)
	druplig_add_literal (lgl->druplig, other);
      lgldrupligreallyadd (lgl, 0);
    }
#endif
    if (!lglesimpcls (lgl)) {
      lgladdcls (lgl, 0, 0, 1);
      lgl->stats->irr.clauses.add++;
      size = lglcntstk (&lgl->clause) - 1;
      assert (size >= 0);
      lgl->stats->irr.lits.add += size;
    }
    lglclnstk (&lgl->clause);
    lglclnstk (&lgl->eclause);
  }
}

static void lgleunassignall (LGL * lgl) {
  int eidx;
  for (eidx = 1; eidx <= lgl->maxext; eidx++)
    lglelit2ext (lgl, eidx)->val = 0;
}

static void lglchkeassumeclean (LGL * lgl) {
  assert (lglmtstk (&lgl->eassume));
#ifndef NDEBUG
  int eidx;
  for (eidx = 1; eidx <= lgl->maxext; eidx++) {
    Ext * ext = lglelit2ext (lgl, eidx);
    assert (!ext->assumed);
    assert (!ext->failed);
  }
#endif
}

static void lglchkassumeclean (LGL * lgl) {
  assert (!lgl->failed);
  assert (!lgl->assumed);
  assert (lglmtstk (&lgl->assume));
#ifndef NDEBUG
  if (lgl->opts->check.val >= 1) {
    int idx;
    for (idx = 2; idx < lgl->nvars; idx++) {
      AVar * av = lglavar (lgl, idx);
      assert (!av->assumed);
      assert (!av->failed);
    }
  }
#endif
}

static void lglreset (LGL * lgl) {
  int elit, ilit, erepr;
  Ext * ext, * rext;
  unsigned bit;
  AVar * av;
  if (lgl->state == RESET) return;
  if (lgl->state <= USED) return;
  assert (lgl->state & (UNKNOWN|SATISFIED|EXTENDED|UNSATISFIED|FAILED|LOOKED));
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  if (!lglmtstk (&lgl->eassume)) {
    LOG (2, "resetting %d external assumptions", lglcntstk (&lgl->eassume));
    while (!lglmtstk (&lgl->eassume)) {
      elit = lglpopstk (&lgl->eassume);
      ext = lglelit2ext (lgl, elit);
      ext->assumed = 0;
      if (ext->failed) {
	ext->failed = 0;
	erepr = lglerepr (lgl, elit);
	if (erepr != elit) {
	  rext = lglelit2ext (lgl, erepr);
	  rext->failed = 0;
	}
      }
    }
  }
  lglchkeassumeclean (lgl);
  if (!lglmtstk (&lgl->assume)) {
    LOG (2, "resetting %d internal assumptions", lglcntstk (&lgl->assume));
    while (!lglmtstk (&lgl->assume)) {
      ilit = lglpopstk (&lgl->assume);
      av = lglavar (lgl, ilit);
      bit = (1u << (ilit < 0));
      assert (av->assumed & bit);
      av->assumed &= ~bit;
      av->failed &= ~bit;
    }
  }
  if (lgl->failed) {
    LOG (2, "resetting internal failed assumption %d", lgl->failed);
    lgl->failed = 0;
  }
  if (lgl->assumed) {
    LOG (2, "resetting assumption queue level to 0 from %d", lgl->assumed);
    lgl->assumed = 0;
  }
  lglchkassumeclean (lgl);
  lgleunassignall (lgl);
  if (lgl->cbs && lgl->cbs->term.done) {
    LOG (2, "resetting forced termination done flag");
    lgl->cbs->term.done = 0;
  }
  TRANS (RESET);
}

static void lgluse (LGL * lgl) {
  if (lgl->state >= USED) return;
  assert (lgl->state == UNUSED || lgl->state == OPTSET);
  TRANS (USED);
}

static void lglupdatealiased (LGL * lgl, int elit) {
  Ext * ext;
  int erepr;
  assert (elit), assert (elit != INT_MIN);
  if (abs (elit) > lgl->maxext) return;
  erepr = lglerepr (lgl, elit);
  if (erepr == elit) return;
  ext = lglelit2ext (lgl, erepr);
  if (ext->aliased) return;
  LOG (4,
    "external literal %d aliased by external literal %d",
    erepr, elit);
  ext->aliased = 1;
}

static void lgleadd (LGL * lgl, int elit) {
  int ilit;
  lglreset (lgl);
  if (elit) {
    lglupdatealiased (lgl, elit);
    ilit = lglimport (lgl, elit);
    LOG (4, "adding external literal %d as %d", elit, ilit);
  } else {
    ilit = 0;
    LOG (4, "closing external clause");
  }
  lglpushstk (lgl, &lgl->eclause, elit);
  lgliadd (lgl, ilit);
#ifndef NCHKSOL
  lglpushstk (lgl, &lgl->orig, elit);
#endif
}

void lgladd (LGL * lgl, int elit) {
  int eidx = abs (elit);
  Ext * ext;
  REQINITNOTFORKED ();
  TRAPI ("add %d", elit);
  if (0 < eidx && eidx <= lgl->maxext) {
    ext = lglelit2ext (lgl, elit);
    ABORTIF (ext->melted, "adding melted literal %d", elit);
  }
  lgl->stats->calls.add++;
  lgleadd (lgl, elit);
  lgluse (lgl);
  if (lgl->clone) lgladd (lgl->clone, elit);
}

static void lglisetphase (LGL * lgl, int lit, int phase) {
  AVar * av;
  if (lit < 0) lit = -lit, phase = -phase;
  av = lglavar (lgl, lit);
  av->fase = phase;
  LOG (2, "setting phase of internal literal %d to %d", lit, phase);
}

static void lglesetphase (LGL * lgl, int elit, int phase) {
  int ilit = lglimport (lgl, elit);
  if (abs (ilit) >= 2) {
    LOG (2, "setting phase of external literal %d to %d", elit, phase);
    lglisetphase (lgl, ilit, phase);
  } else LOG (2, "setting phase of external literal %d skipped", elit);
}

void lglsetphase (LGL * lgl, int elit) {
  REQINITNOTFORKED ();
  TRAPI ("setphase %d", elit);
  ABORTIF (!elit, "invalid literal argument");
  if (elit < 0) lglesetphase (lgl, -elit, -1);
  else lglesetphase (lgl, elit, 1);
  if (lgl->clone) lglsetphase (lgl->clone, elit);
}

void lglresetphase (LGL * lgl, int elit) {
  REQINITNOTFORKED ();
  TRAPI ("resetphase %d", elit);
  ABORTIF (!elit, "invalid literal argument");
  lglesetphase (lgl, elit, 0);
  if (lgl->clone) lglresetphase (lgl->clone, elit);
}

static void lgleassume (LGL * lgl, int elit) {
  int ilit, val;
  unsigned bit;
  AVar * av;
  Ext * ext;
  lglreset (lgl);
  ilit = lglimport (lgl, elit);
  LOG (2, "assuming external literal %d", elit);
  bit = 1u << (elit < 0);
  ext = lglelit2ext (lgl, elit);
  if (!(ext->assumed & bit)) {
    ext->assumed |= bit;
    lglpushstk (lgl, &lgl->eassume, elit);
  }
  assert (!lgl->level);
  if (!(val = lglcval (lgl, ilit))) {
    av = lglavar (lgl, ilit);
    bit = (1u << (ilit < 0));
    if (av->assumed & bit) {
      LOG (2, "internal literal %d already assumed", ilit);
    } else {
      av->assumed |= bit;
      if (av->assumed & (bit^3))
	LOG (2, "negation %d was also already assumed", -ilit);
      lglpushstk (lgl, &lgl->assume, ilit);
    }
  } else if (val > 0) {
    LOG (2, "externally assumed literal %d already fixed to true", elit);
  } else {
    assert (val < 0);
    LOG (2, "externally assumed literal %d already fixed to false", elit);
    if (ilit != -1) {
      av = lglavar (lgl, ilit);
      bit = (1u << (ilit < 0));
      if (!(av->assumed & bit)) {
	av->assumed |= bit;
	lglpushstk (lgl, &lgl->assume, ilit);
      }
    }
    if (!lgl->failed) lgl->failed = ilit;
  }
}

static void lglecassume (LGL * lgl, int elit) {
  LOG (2, "adding external literal %d to assumed clause", elit);
}

void lglassume (LGL * lgl, int elit) {
  int eidx = abs (elit);
  Ext * ext;
  REQINITNOTFORKED ();
  TRAPI ("assume %d", elit);
  lgl->stats->calls.assume++;
  ABORTIF (!elit, "can not assume invalid literal 0");
  if (0 < eidx && eidx <= lgl->maxext) {
    ext = lglelit2ext (lgl, elit);
    ABORTIF (ext->melted, "assuming melted literal %d", elit);
  }
  lgleassume (lgl, elit);
  lgluse (lgl);
  lglmelter (lgl);
  if (lgl->clone) lglassume (lgl->clone, elit);
}

void lglcassume (LGL * lgl, int elit) {
  int eidx = abs (elit);
  Ext * ext;
  REQINITNOTFORKED ();
  TRAPI ("cassume %d", elit);
  lgl->stats->calls.cassume++;
  if (0 < eidx && eidx <= lgl->maxext) {
    ext = lglelit2ext (lgl, elit);
    ABORTIF (ext->melted, "assuming melted literal %d", elit);
  }
  lglecassume (lgl, elit);
  lgluse (lgl);
  if (lgl->clone) lglcassume (lgl->clone, elit);
}

void lglfixate (LGL * lgl) {
  const int  * p;
  Stk eassume;
  REQINITNOTFORKED ();
  TRAPI ("fixate");
  if (lgl->mt) return;
  CLR (eassume);
  for (p = lgl->eassume.start; p < lgl->eassume.top; p++)
    lglpushstk (lgl, &eassume, *p);
  for (p = eassume.start; p < eassume.top; p++)
    lgleadd (lgl, *p), lgleadd (lgl, 0);
  lglrelstk (lgl, &eassume);
  lgluse (lgl);
  if (lgl->clone) lglfixate (lgl->clone);
}

static void lglbonflict (LGL * lgl, int lit, int blit) {
  assert (lglevel (lgl, lit) >= lglevel (lgl, blit >> RMSHFT));
  assert (!lgliselim (lgl, blit >> RMSHFT));
  assert (!lgliselim (lgl, lit));
  lgl->conf.lit = lit;
  lgl->conf.rsn[0] = blit;
  LOG (2, "inconsistent %s binary clause %d %d",
       lglred2str (blit & REDCS), lit, (blit >> RMSHFT));
}

static void lgltonflict (LGL * lgl, int lit, int blit, int other2) {
  assert ((blit & MASKCS) == TRNCS);
  assert (lglevel (lgl, lit) >= lglevel (lgl, blit >> RMSHFT));
  assert (lglevel (lgl, lit) >= lglevel (lgl, other2));
  assert (!lgliselim (lgl, blit >> RMSHFT));
  assert (!lgliselim (lgl, other2));
  assert (!lgliselim (lgl, lit));
  lgl->conf.lit = lit;
  lgl->conf.rsn[0] = blit;
  lgl->conf.rsn[1] = other2;
  LOG (2, "inconsistent %s ternary clause %d %d %d",
       lglred2str (blit & REDCS), lit, (blit>>RMSHFT), other2);
}

static void lglonflict (LGL * lgl, int check, int lit, int red, int lidx) {
  int glue;
#if !defined (NLGLOG) || !defined (NDEBUG)
  int * p, * c = lglidx2lits (lgl, red, lidx);
#endif
  assert (red == REDCS || !red);
#ifndef NDEBUG
  {
    int found = 0;
    for (p = c; *p; p++) {
      if(*p == lit) found++;
      assert (lglval (lgl, *p) <= -check);
      assert (lglevel (lgl, lit) >= lglevel (lgl, *p));
      assert (!lgliselim (lgl, lit));
    }
    assert (found == 1);
  }
#endif
  lgl->conf.lit = lit;
  lgl->conf.rsn[0] = red | LRGCS;
  lgl->conf.rsn[1] = lidx;
#ifndef NLGLOG
  if (lgl->opts->log.val >= 2) {
    lglogstart (lgl, 2, "inconsistent %s large clause", lglred2str (red));
    for (p = c ; *p; p++)
      fprintf (lgl->out, " %d", *p);
    lglogend (lgl);
  }
#endif
  if (red) {
    glue = lidx & GLUEMASK;
    lgl->stats->lir[glue].conflicts++;
    assert (lgl->stats->lir[glue].conflicts > 0);
  }
}

static void lgldeclscnt (LGL * lgl, int size, int red, int glue) {
  assert (!red || red == REDCS);
  if (!red) lgldecirr (lgl, size);
  else if (size == 2) assert (lgl->stats->red.bin), lgl->stats->red.bin--;
  else if (size == 3) assert (lgl->stats->red.trn), lgl->stats->red.trn--;
  else {
    assert (lgl->stats->red.lrg > 0);
    lgl->stats->red.lrg--;
    assert (lgl->stats->lir[glue].clauses > 0);
    lgl->stats->lir[glue].clauses--;
  }
}

static void lglrminc (LGL * lgl, const int * w, const int * eow) {
  int inc;
  assert (w <= eow);
  assert (sizeof w < 8 || eow <= w + INT_MAX);
  inc = eow - w;
  assert (inc >= 0);
  inc >>= lgl->opts->rmincpen.val;
  inc++;
  assert (lgl->blocking + lgl->eliminating + lgl->simpleprobing <= 1);
  if (lgl->blocking) ADDSTEPS (blk.steps, inc);
  else if (lgl->eliminating) ADDSTEPS (elm.steps, inc);
  else if (lgl->simpleprobing) ADDSTEPS (prb.simple.steps, inc);
}

static void lglrmtwch (LGL * lgl, int lit, int other1, int other2, int red) {
  int * p, blit, other, blit1, blit2, * w, * eow, tag;
  HTS * hts;
  assert (!red || red == REDCS);
  LOG (3, "removing %s ternary watch %d blits %d %d",
       lglred2str (red), lit, other1, other2);
  hts = lglhts (lgl, lit);
  assert (hts->count >= 2);
  p = w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  lglrminc (lgl, w, eow);
  blit1 = RMSHFTLIT (other1) | red | TRNCS;
  blit2 = RMSHFTLIT (other2) | red | TRNCS;
  for (;;) {
    assert (p < eow);
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == BINCS || tag == OCCS) continue;
    other = *p++;
    if (tag == LRGCS) continue;
    assert (tag == TRNCS);
    if (blit == blit1 && other == other2) break;
    if (blit == blit2 && other == other1) break;
  }
  while (p < eow) p[-2] = p[0], p++;
  lglshrinkhts (lgl, hts, p - w - 2);
}

static void lglpopnunmarkstk (LGL * lgl, Stk * stk) {
  while (!lglmtstk (stk)) {
    int lit = lglpopstk (stk);
    if (!lit) continue;
    lglavar (lgl, lit)->mark = 0;
  }
}

static void lglpopnunlcamarkstk (LGL * lgl, Stk * stk) {
  while (!lglmtstk (stk))
    lglavar (lgl, lglpopstk (stk))->lcamark = 0;
}

static int lglcamarked (LGL * lgl, int lit) {
  switch (lglavar (lgl, lit)->lcamark) {
    case 1: return (lit < 0) ? -1 : 1;
    case 2: return (lit < 0) ? -2 : 2;
    case 4: return (lit < 0) ? 1 : -1;
    case 8: return (lit < 0) ? 2 : -2;
    default: assert (!lglavar (lgl, lit)->lcamark); return 0;
  }
}

static void lglcamark (LGL * lgl, int lit, int mark) {
  int newmark;
  AVar * av;
  assert (mark == 1 || mark == 2);
  av = lglavar (lgl, lit);
  assert (!av->lcamark);
  newmark = mark;
  if (lit < 0) newmark <<= 2;
  av->lcamark = newmark;
  lglpushstk (lgl, &lgl->lcaseen, lit);
  assert (lglcamarked (lgl, lit) == mark);
  assert (lglcamarked (lgl, -lit) == -mark);
}

static int lgbiglca (LGL * lgl, int a, int b, int64_t * stepsptr) {
  int blit, tag, mark, negmark, prevmark, c, res, prev, next;
  const int * p, * w, * eow;
  int64_t steps;
  HTS * hts;
  assert (a), assert (b);
  assert (abs (a) != abs (b));
  assert (lglevel (lgl, a));
  assert (lglevel (lgl, b));
  assert (lglval (lgl, a) > 0);
  assert (lglval (lgl, b) > 0);
  assert (lglgetdom (lgl, a) == lglgetdom (lgl, b));
  assert (lglmtstk (&lgl->lcaseen));
  lglcamark (lgl, a, 1);
  lglcamark (lgl, b, 2);
  res = next = 0;
  steps = 0;
  while (next < lglcntstk (&lgl->lcaseen)) {
    c = lglpeek (&lgl->lcaseen, next++);
    assert (lglval (lgl, c) > 0);
    assert (lglevel (lgl, c) > 0);
    mark = lglcamarked (lgl, c);
    assert (mark == 1 || mark == 2);
    negmark = mark ^ 3;
    hts = lglhts (lgl, c);
    if (!hts->count) continue;
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    steps++;
    for (p = w; p < eow; p++) {
      blit = *p;
      tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) p++;
      if (tag != BINCS) continue;
      prev = -(blit >> RMSHFT);
      if (!lglevel (lgl, prev)) continue;
      if (lglval (lgl, prev) <= 0) continue;
      if ((prevmark = lglcamarked (lgl, prev)) < 0) continue;
      if (mark == prevmark) continue;
      if (prevmark == negmark) { res = prev; goto DONE; }
      lglcamark (lgl, prev, mark);
    }
  }
DONE:
  lglpopnunlcamarkstk (lgl, &lgl->lcaseen);
  LOG (3, "least common ancestor of %d and %d is %d", a, b, res);
  *stepsptr += steps;
  return res;
}

static int lglimplca (LGL * lgl, int a, int b, int64_t * stepsptr) {
  int r0, tag, mark, negmark, prevmark, c, res, prev, next;
  int64_t steps;
  assert (a), assert (b);
  assert (abs (a) != abs (b));
  assert (lglevel (lgl, a));
  assert (lglevel (lgl, b));
  assert (lglval (lgl, a) > 0);
  assert (lglval (lgl, b) > 0);
  assert (lglgetdom (lgl, a) == lglgetdom (lgl, b));
  assert (lglmtstk (&lgl->lcaseen));
  lglcamark (lgl, a, 1);
  lglcamark (lgl, b, 2);
  res = next = 0;
  steps = 0;
  while (next < lglcntstk (&lgl->lcaseen)) {
    c = lglpeek (&lgl->lcaseen, next++);
    assert (lglval (lgl, c) > 0);
    assert (lglevel (lgl, c) > 0);
    mark = lglcamarked (lgl, c);
    assert (mark == 1 || mark == 2);
    negmark = mark ^ 3;
    steps++;
    r0 = *lglrsn (lgl, c);
    tag = r0 & MASKCS;
    if (tag != BINCS) continue;
    prev = -(r0 >> RMSHFT);
    if (!lglevel (lgl, prev)) continue;
    if (lglval (lgl, prev) <= 0) continue;
    if ((prevmark = lglcamarked (lgl, prev)) < 0) continue;
    if (mark == prevmark) continue;
    if (prevmark == negmark) { res = prev; goto DONE; }
    lglcamark (lgl, prev, mark);
  }
DONE:
  lglpopnunlcamarkstk (lgl, &lgl->lcaseen);
  LOG (3, "least common ancestor of %d and %d is %d", a, b, res);
  *stepsptr += steps;
  return res;
}


static int lglhbrdom (LGL * lgl, int a, int b, int64_t * stepsptr) {
  assert (lglgetdom (lgl, a) == lglgetdom (lgl, b));
  switch (lgl->opts->hbrdom.val) {
    case 2: return lgbiglca (lgl, a, b, stepsptr);
    case 1: return lglimplca (lgl, a, b, stepsptr);
    default: return lglgetdom (lgl, a);
  }
}

static void lglrmlwch (LGL * lgl, int lit, int red, int lidx) {
  int blit, tag, * p, * q, * w, * eow, ored, olidx;
  HTS * hts;
#ifndef NLGLOG
  p = lglidx2lits (lgl, red, lidx);
  if (red)
    LOG (3, "removing watch %d in red[%d][%d] %d %d %d %d%s",
	 lit, (lidx & GLUEMASK), (lidx >> GLUESHFT), p[0], p[1], p[2], p[3],
	 (p[4] ? " ..." : ""));
  else
    LOG (3, "removing watch %d in irr[%d] %d %d %d %d%s",
	 lit, lidx, p[0], p[1], p[2], p[3], (p[4] ? " ..." : ""));
#endif
  hts = lglhts (lgl, lit);
  assert (hts->count >= 2);
  p = w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  lglrminc (lgl, w, eow);
  for (;;) {
    assert (p < eow);
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == BINCS) continue;
    if (tag == OCCS) { assert (lgl->dense); continue; }
    olidx = *p++;
    if (tag == TRNCS) continue;
    assert (tag == LRGCS);
    ored = blit & REDCS;
    if (ored != red) continue;
    if (olidx == lidx) break;
  }
  assert ((p[-2] & REDCS) == red);
  assert (p[-1] == lidx);
  for (q = p; q < eow; q++)
    q[-2] = q[0];
  lglshrinkhts (lgl, hts, q - w - 2);
}

static void lglpropsearch (LGL * lgl, int lit) {
  int * q, * eos, blit, other, other2, other3, red, prev;
  int tag, val, val2, lidx, * c, * l;
  const int * p;
  int visits;
  long delta;
  HTS * hts;

  LOG (3, "propagating %d in search", lit);

  assert (!lgl->simp);
  assert (!lgl->lkhd);
  assert (!lgl->probing);
  assert (!lgl->dense);
  assert (!lgliselim (lgl, lit));
  assert (lglval (lgl, lit) == 1);

  hts = lglhts (lgl, -lit);
  if (!hts->offset) return;
  q = lglhts2wchs (lgl, hts);
  assert (hts->count >= 0);
  eos = q + hts->count;
  visits = 0;
  for (p = q; p < eos; p++) {
    visits++;
    *q++ = blit = *p;
    tag = blit & MASKCS;
    if (tag != BINCS) {
      assert (tag == TRNCS || tag == LRGCS);
      *q++ = *++p;
    }
    other = (blit >> RMSHFT);
    assert (abs (other) != abs (lit));
    val = lglval (lgl, other);
    if (val > 0) continue;
    red = blit & REDCS;
    if (tag == BINCS) {
      if (val < 0) { lglbonflict (lgl, -lit, blit); p++; break; }
      lglf2rce (lgl, other, -lit, red);
    } else if (tag == TRNCS) {
      other2 = *p;
      val2 = lglval (lgl, other2);
      if (val2 > 0) continue;
      if (!val && !val2) continue;
      if (val < 0 && val2 < 0) {
	lgltonflict (lgl, -lit, blit, other2);
	p++;
	break;
      }
      if (!val) SWAP (int, other, other2);
      else assert (val < 0);
      lglf3rce (lgl, other2, -lit, other, red);
    } else {
      assert (tag == LRGCS);
      assert (val <= 0);
      lidx = *p;
      c = lglidx2lits (lgl, red, lidx);
      other2 = c[0];
      if (other2 == -lit) other2 = c[0] = c[1], c[1] = -lit;
      else assert (c[1] == -lit);
      if (other2 != other) {
	other = other2;
	val = lglval (lgl, other);
	if (val > 0) {
	  q[-2] = LRGCS | RMSHFTLIT (other2) | red;
	  continue;
	}
      }
      assert (!red || !lgliselim (lgl, other));
      val2 = 0;
      prev = -lit;
      for (l = c + 2; (other2 = *l); l++) {
	*l = prev;
	val2 = lglval (lgl, other2);
	if (val2 >= 0) break;
	assert (!red || !lgliselim (lgl, other2));
	prev = other2;
      }
      assert (!other2 || val2 >= 0);
      if (other2) {
	c[1] = other2;
	assert (other == c[0]);
	delta = lglwchlrg (lgl, other2, other, red, lidx);
	if (delta) p += delta, q += delta, eos += delta;
	q -= 2;
	continue;
      }
      while (l > c + 2) {
	other3 = *--l;
	*l = prev;
	prev = other3;
      }
      if (val < 0) {
	lglonflict (lgl, 1, -lit, red, lidx);
	p++;
	break;
      }
      assert (!val);
      lglflrce (lgl, other, red, lidx);
    }
  }
  while (p < eos) *q++ = *p++;
  lglshrinkhts (lgl, hts, hts->count - (p - q));
  assert (!lgl->simp);

  lgl->stats->visits.search += visits;
}

static int lglhbred (LGL * lgl, int subsumed, int red) {
  int res = subsumed ? red : REDCS;
  LOG (3, "hyber binary learned clause becomes %s", lglred2str (res));
  return res;
}

static void lgldecocc (LGL *, int);	//TODO move scheduling ...

static void lglrmlocc (LGL * lgl, int lit, int red, int lidx) {
  int search, blit, tag, * p, * q, * w, * eow;
  HTS * hts;
#ifndef NLGLOG
  if (red) LOG (3, "removing occurrence %d in red[0][%d]", lit, lidx);
  else LOG (3, "removing occurrence %d in irr[%d]", lit, lidx);
#endif
  assert (!red || red == REDCS);
  hts = lglhts (lgl, lit);
  assert (hts->count >= 1);
  assert (lidx <= MAXIRRLIDX);
  search = (lidx << RMSHFT) | OCCS | red;
  assert (search >= 0);
  p = w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  lglrminc (lgl, w, eow);
  do {
    assert (p < eow);
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
  } while (blit != search);
  assert (p[-1] == search);
  for (q = p ; q < eow; q++)
    q[-1] = q[0];
  lglshrinkhts (lgl, hts, q - w - 1);
}

static void lglflushremovedoccs (LGL * lgl, int lit) {
  HTS * hts = lglhts (lgl, lit);
  int * w = lglhts2wchs (lgl, hts);
  int * eow = w + hts->count;
  int blit, tag, red, lidx;
  int * p, * q, * c;
  lglrminc (lgl, w, eow);
  for (p = q = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == BINCS) *q++ = blit;
    else if (tag == TRNCS) *q++ = blit, *q++ = *p;
    else {
      assert (tag == LRGCS || tag == OCCS);
      if (!red) {
	lidx = (tag == LRGCS) ? *p : (blit >> RMSHFT);
	c = lglidx2lits (lgl, red, lidx);
	if (c[0] == REMOVED) continue;
      }
      *q++ = blit;
      if (tag == LRGCS) *q++ = *p;
    }
  }
  lglshrinkhts (lgl, hts, q - w);
}

static void lglpropupdvisits (LGL * lgl, int visits, int64_t steps) {
  if (lgl->lkhd) lgl->stats->visits.lkhd += visits;
  else if (lgl->simp) lgl->stats->visits.simp += visits;
  else lgl->stats->visits.search += visits;

  if (lgl->simp) {
         if (lgl->basicprobing) ADDSTEPS (prb.basic.steps, visits + steps);
    else if (lgl->simpleprobing) ADDSTEPS (prb.simple.steps, visits + steps);
    else if (lgl->treelooking) ADDSTEPS (prb.treelook.steps, visits + steps);
    else if (lgl->sweeping) ADDSTEPS (sweep.steps, visits + steps);
  } else {
    assert (!lgl->basicprobing);
    assert (!lgl->simpleprobing);
    assert (!lgl->treelooking);
    assert (!lgl->sweeping);
  }
}

static void lglprop (LGL * lgl, int lit) {
  int * p, * q, * eos, blit, other, other2, other3, red, prev;
  int tag, val, val2, lidx, * c, * l, dom, hbred, subsumed;
  int glue, flushoccs, visits;
  int64_t steps;
  long delta;
  HTS * hts;
  LOG (3, "propagating %d over ternary and large clauses", lit);
  assert (!lgliselim (lgl, lit));
  assert (lglval (lgl, lit) == 1);
  hts = lglhts (lgl, -lit);
  if (!hts->offset) return;
  flushoccs = 0;
  q = lglhts2wchs (lgl, hts);
  assert (hts->count >= 0);
  eos = q + hts->count;
  visits = 0;
  steps = 0;
  for (p = q; p < eos; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    if (tag == OCCS) {
      assert (lgl->dense);
      assert (!red);
      *q++ = blit;
      continue;
    }
    visits++;
    other = (blit >> RMSHFT);
    val = lglval (lgl, other);
    if (tag == BINCS) {
      *q++ = blit;
      if (val > 0) continue;
      if (red && lgliselim (lgl, other)) continue;
      if (val < 0) {
	lglbonflict (lgl, -lit, blit);
	p++;
	break;
      }
      assert (!val);
      lglf2rce (lgl, other, -lit, red);
    } else if (tag == TRNCS) {
      *q++ = blit;
      other2 = *++p;
      *q++ = other2;
      if (val > 0) continue;
      if (red && lgliselim (lgl, other)) continue;
      val2 = lglval (lgl, other2);
      if (val2 > 0) continue;
      if (!val && !val2) continue;
      if (red && lgliselim (lgl, other2)) continue;
      if (val < 0 && val2 < 0) {
	lgltonflict (lgl, -lit, blit, other2);
	p++;
	break;
      }
      if (!val) SWAP (int, other, other2); else assert (val < 0);
      if (lgl->level &&
	  lgl->simp &&
	  lgl->opts->lhbr.val) {
	assert (lgl->simp);
	dom = lglgetdom (lgl, lit);
	if (lglgetdom (lgl, -other) != dom) goto NO_HBR_JUST_F3RCE;
	dom = lglhbrdom (lgl, lit, -other, &steps);
	if (!dom) goto NO_HBR_JUST_F3RCE;
	subsumed = (dom == lit || dom == -other);
	hbred = lglhbred (lgl, subsumed, red);
	LOG (2, "hyper binary resolved %s clause %d %d",
	     lglred2str (hbred), -dom, other2);
        lgldrupligaddclsarg (lgl, REDCS, -dom, other2, 0);
	if (subsumed) {
	  LOG (2, "subsumes %s ternary clause %d %d %d",
	       lglred2str (red), -lit, other, other2);
	  lglrmtwch (lgl, other2, other, -lit, red);
	  lglrmtwch (lgl, other, other2, -lit, red);
	  lgl->stats->hbr.sub++;
	  if (red) assert (lgl->stats->red.trn), lgl->stats->red.trn--;
	  else {
	    lgldecirr (lgl, 3);
	    if (lgl->dense) {
	      if (-dom == -lit) lgldecocc (lgl, other);
	      else { assert (-dom == other); lgldecocc (lgl, -lit); }
	    }
	  }
	  lgldrupligdelclsarg (lgl, -lit, other, other2, 0);
	}
	delta = 0;
	if (dom == lit) {
	  LOG (3,
    "replacing %s ternary watch %d blits %d %d with binary %d blit %d",
	  lglred2str (red), -lit, other, other2, -dom, other2);
	  assert (subsumed);
	  blit = RMSHFTLIT (other2) | BINCS | hbred;
	  q[-2] = blit;
	  q--;
	} else {
	  if (dom == -other) {
	    LOG (3, "removing %s ternary watch %d blits %d %d",
		 lglred2str (red), -lit, other, other2);
	    assert (subsumed);
	    q -= 2;
	  } else {
	    LOG (2, "replaces %s ternary clause %d %d %d as reason for %d",
		 lglred2str (red), -lit, other, other2, other2);
	    assert (!subsumed);
	    assert (abs (dom) != abs (lit));
	    assert (abs (other2) != abs (lit));
	  }
	  delta += lglwchbin (lgl, -dom, other2, hbred);
	}
	delta += lglwchbin (lgl, other2, -dom, hbred);
	if (delta) p += delta, q += delta, eos += delta;
	if (hbred) lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
	else lglincirr (lgl, 2);
	lglf2rce (lgl, other2, -dom, hbred);
	lgl->stats->hbr.trn++;
	lgl->stats->hbr.cnt++;
	lgl->stats->prgss++;
      } else {
NO_HBR_JUST_F3RCE:
       lglf3rce (lgl, other2, -lit, other, red);
      }
    } else {
      assert (tag == LRGCS);
      if (val > 0) goto COPYL;
      lidx = p[1];
      c = lglidx2lits (lgl, red, lidx);
      other2 = c[0];
      if (other2 >= NOTALIT) {
	p++;
	continue;
      }
      if (other2 == -lit) other2 = c[0] = c[1], c[1] = -lit;
      if (other2 != other) {
	other = other2;
	val = lglval (lgl, other);
	blit = red;
	blit |= LRGCS;
	blit |= RMSHFTLIT (other2);
	if (val > 0) goto COPYL;
      }
      if (red && lgliselim (lgl, other)) goto COPYL;
      val2 = INT_MAX;
      prev = -lit;
      for (l = c + 2; (other2 = *l); l++) {
	*l = prev;
	val2 = lglval (lgl, other2);
	if (val2 >= 0) break;
	if (red && lgliselim (lgl, other2)) break;
	prev = other2;
      }
      assert (val2 != INT_MAX);
      if (other2 && val2 >= 0) {
	c[1] = other2;
	assert (other == c[0]);
	delta = lglwchlrg (lgl, other2, other, red, lidx);
	if (delta) p += delta, q += delta, eos += delta;
	p++;
	continue;
      }

      while (l > c + 2) {
	other3 = *--l;
	*l = prev;
	prev = other3;
      }

      if (other2 && val2 < 0) goto COPYL;

      if (val < 0) {
	lglonflict (lgl, 1, -lit, red, lidx);
	break;
      }

      assert (!val);
      if (lgl->level &&
	  lgl->simp &&
	  lgl->opts->lhbr.val) {
	assert (lgl->simp);
	dom = 0;
	for (l = c; (other2 = *l); l++) {
	  if (other2 == other) continue;
	  if (!lglevel (lgl, other2)) continue;
	  assert (lglval (lgl, other2) < 0);
	  if (!dom) dom = lglgetdom (lgl, -other);
	  if (dom != lglgetdom (lgl, -other2)) goto NO_HBR_JUST_FLRCE;
	}
	LOGCLS (2, c, "dominator %d for %s clause", dom, lglred2str (red));
	dom = 0;
	for (l = c; (other2 = *l); l++) {
	  if (other2 == other) continue;
	  if (!lglevel (lgl, other2)) continue;
	  dom = lglhbrdom (lgl, dom, -other2, &steps);
	}
	if (!dom) goto NO_HBR_JUST_FLRCE;
	LOGCLS (2, c, "closest dominator %d", dom);
	subsumed = 0;
	for (l = c; !subsumed && (other2 = *l); l++)
	  subsumed = (dom == -other2);
	assert (lit != dom || subsumed);
	hbred = lglhbred (lgl, subsumed, red);
	LOG (2, "hyper binary resolved %s clause %d %d",
	     lglred2str (hbred), -dom, other);
        lgldrupligaddclsarg (lgl, REDCS, -dom, other, 0);
	if (subsumed) {
	  LOGCLS (2, c, "subsumes %s large clause", lglred2str (red));
	  lglrmlwch (lgl, other, red, lidx);
	  lgl->stats->hbr.sub++;
	  if (red) {
	    glue = lidx & GLUEMASK;
	    if (glue != MAXGLUE) {
	      assert (lgl->stats->red.lrg);
	      lgl->stats->red.lrg--;
	      assert (lgl->stats->lir[glue].clauses > 0);
	      lgl->stats->lir[glue].clauses--;
	    }
	  }
	  if (!red && lgl->dense) {
	    for (l = c; (other2 = *l); l++) {
	      if (other2 != -lit) lglrmlocc (lgl, other2, 0, lidx);
	      if (other2 == -dom) continue;
	      if (other2 == other) continue;
	      lgldecocc (lgl, other2);
	    }
	    flushoccs++;
	  }
	  if (red && glue < MAXGLUE) { LGLCHKACT (c[-1]); c[-1] = REMOVED; }
	  lgldrupligdelclsaux (lgl, c);
	  for (l = c; *l; l++) *l = REMOVED;
	  if (!red) lgldecirr (lgl, l - c);
	  *l = REMOVED;
	}
	delta = 0;
	if (dom == lit) {
	  assert (subsumed);
	  LOG (3,
	       "replacing %s large watch %d with binary watch %d blit %d",
	       lglred2str (red), -lit, -lit, -dom);
	  blit = RMSHFTLIT (other) | BINCS | hbred;
	  *q++ = blit, p++;
	} else {
	  if (subsumed) {
	    LOG (3, "removing %s large watch %d", lglred2str (red), -lit);
	    p++;
	  } else {
	    LOGCLS (2, c,
		    "%s binary clause %d %d becomes reasons "
		    "for %d instead of %s large clause",
		    lglred2str (hbred), -dom, other, other, lglred2str (red));
	    assert (hbred == REDCS);
	  }
	  delta += lglwchbin (lgl, -dom, other, hbred);
	}
	delta += lglwchbin (lgl, other, -dom, hbred);
	if (delta) p += delta, q += delta, eos += delta;
	if (hbred) lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
	else lglincirr (lgl, 2);
	lglf2rce (lgl, other, -dom, hbred);
	lgl->stats->hbr.lrg++;
	lgl->stats->hbr.cnt++;
	lgl->stats->prgss++;
	if (subsumed) continue;
      } else {
NO_HBR_JUST_FLRCE:
	lglflrce (lgl, other, red, lidx);
      }
COPYL:
      *q++ = blit;
      *q++ = *++p;
    }
  }
  while (p < eos) *q++ = *p++;
  lglshrinkhts (lgl, hts, hts->count - (p - q));
  if (flushoccs) lglflushremovedoccs (lgl, -lit);
  lglpropupdvisits (lgl, visits, steps);
}

static void lglprop2 (LGL * lgl, int lit) {
  int other, blit, tag, val, red, visits;
  const int * p, * w, * eow;
  int64_t travs;
  HTS * hts;
  LOG (3, "propagating %d over binary clauses", lit);
  assert (!lgliselim (lgl, lit));
  assert (lglval (lgl, lit) == 1);
  visits = 0;
  travs = 0;
  hts = lglhts (lgl, -lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    visits++;
    red = blit & REDCS;
    other = blit >> RMSHFT;
    travs++;
    if (lgliselim (lgl, other)) { assert (red); continue; }
    val = lglval (lgl, other);
    if (val > 0) continue;
    if (val < 0) { lglbonflict (lgl, -lit, blit); break; }
    lglf2rce (lgl, other, -lit, red);
  }

  lglpropupdvisits (lgl, visits, travs);
}

static int lglhasconflict (LGL * lgl) {
  return lgl->conf.lit != 0;
}

static int lglbcpcomplete (LGL * lgl) {
  assert (lgl->next2 <= lgl->next);
  assert (lgl->next <= lglcntstk (&lgl->trail));
  if (lgl->next2 < lgl->next) return 0;
  if (lgl->next < lglcntstk (&lgl->trail)) return 0;
  return 1;
}

static void lglchkbcpclean (LGL * lgl, const char * where) {
  ASSERT (lglbcpcomplete (lgl));
  ASSERT (!lgl->conf.lit);
  ASSERT (!lgl->mt);
}

static int lglbcp (LGL * lgl) {
  int lit, trail, count;
  assert (!lgl->mt);
  assert (!lgl->conf.lit);
  assert (!lgl->notfullyconnected);
  count = 0;
  while (!lgl->conf.lit) {
    trail = lglcntstk (&lgl->trail);
    if (lgl->next2 < trail) {
      lit = lglpeek (&lgl->trail, lgl->next2++);
      lglprop2 (lgl, lit);
      continue;			// TODO try to optionally uncomment
    }
    if (lgl->next >= trail) break;
    count++;
    lit = lglpeek (&lgl->trail, lgl->next++);
    lglprop (lgl, lit);
  }
  if (lgl->lkhd) ADDSTEPS (props.lkhd, count);
  else if (lgl->simp) ADDSTEPS (props.simp, count);
  else ADDSTEPS (props.search, count);
  assert (lglhasconflict (lgl) || lglbcpcomplete (lgl));
  return !lglhasconflict (lgl);
}

static int lglbcpsearch (LGL * lgl) {
  int lit, count = 0;
  assert (!lgl->simp);
  assert (!lgl->notfullyconnected);
  while ((!lgl->failed || !lgl->level) &&
	 !lgl->conf.lit &&
	 lgl->next < lglcntstk (&lgl->trail)) {
    lit = lglpeek (&lgl->trail, lgl->next++);
    lglpropsearch (lgl, lit);
    count++;
  }
  ADDSTEPS (props.search, count);
  lgl->next2 = lgl->next;
  if (lgl->conf.lit && lgl->failed) {
    LOG (2, "inconsistency overwrites failed assumption %d", lgl->failed);
    lgl->failed = 0;
  }
  assert (lglhasconflict (lgl) || lgl->failed || lglbcpcomplete (lgl));
  return !lgl->conf.lit && !lgl->failed;
}

#ifndef NDEBUG
static void lglchkclnvar (LGL * lgl) {
  AVar * av;
  int i;
  for (i = 2; i < lgl->nvars; i++) {
    av = lglavar (lgl, i);
    assert (!av->mark);
  }
}
#endif

#ifdef RESOLVENT
static int lglmaintainresolvent (LGL * lgl) {
#ifndef NDEBUG
  if (lgl->opts->check.val >= 1) return 1;
#endif
#ifndef NLGLOG
  if (lgl->opts->log.val >= 2) return 1;
#endif
  return 0;
}
#endif

static int lgldecision (LGL * lgl, int lit) {
  int * rsn = lglrsn (lgl, lit);
  int tag = rsn[0] & MASKCS;
  return tag == DECISION;
}

static int lglassumption (LGL * lgl, int lit) {
  return lglavar (lgl, lit)->assumed;
}

static int lglpull (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int level, res;
  level = lglevel (lgl, lit);
  if (!level) return 0;
  if (av->mark) return 0;
  av->mark = 1;
  lglpushstk (lgl, &lgl->seen, lit);
#ifdef RESOLVENT
  if (lglmaintainresolvent (lgl)) {
    lglpushstk (lgl, &lgl->resolvent, lit);
    LOG (2, "adding %d to resolvent", lit);
    LOGRESOLVENT (3, "resolvent after adding %d is", lit);
  }
#endif
  if (level == lgl->level) {
    LOG (2, "reason literal %d at same level %d", lit, lgl->level);
    res = 1;
  } else {
    lglpushstk (lgl, &lgl->clause, lit);
    LOG (2, "adding literal %d at upper level %d to 1st UIP clause",
	 lit, lglevel (lgl, lit));
    lgluselevel (lgl, level);
    res = 0;
  }
  return res;
}

static int lglusedtwice (LGL * lgl, int lit) {
  int level;
  if (!lgl->opts->usedtwice.val) return 1;
  level = lglevel (lgl, lit);
  lgl->stats->mincls.usedtwice.search++;
  if (lglevelused (lgl, level) >= 2) return 1;
  lgl->stats->mincls.usedtwice.hits++;
  return 0;
}

static int lglpoison (LGL * lgl, int lit, Stk * stk, int local) {
  AVar * av = lglavar (lgl, lit);
  int level, res;
  if (av->mark) res = 0;
  else {
    level = lglevel (lgl, lit);
    if (!level) res = 0;
    else {
      assert (level < lgl->level);
      if (lgldecision (lgl, lit)) res = 1;
      else if (lglevelused (lgl, level) < 2) res = 1;
      else {
	if (lgl->opts->poison.val) lgl->stats->mincls.poison.search++;
	if (av->poisoned) {
	  assert (lgl->opts->poison.val);
	  lgl->stats->mincls.poison.hits++;
	  res = 1;
	} else if (local) res = 1;
	else if (lglusedtwice (lgl, lit)) {
	  av->mark = 1;
	  lglpushstk (lgl, &lgl->seen, lit);
	  lglpushstk (lgl, stk, lit);
	  res = 0;
	} else res = 1;
      }
    }
  }
  if (res && lgl->opts->poison.val && !av->poisoned) {
    av->poisoned = 1;
    lglpushstk (lgl, &lgl->poisoned, lit);
  }
  return res;
}

static int lglminclslit (LGL * lgl, int start, int local) {
  int lit, tag, r0, r1, other, * p, * q, *top, old, level;
  int poisoned, * rsn, found;
  AVar * av, * bv;
  assert (lglmarked (lgl, start));
  lit = start;
  level = lglevel (lgl, lit);
  assert (level > 0);
  if (level == lgl->level) return 0;
  if (!lglusedtwice (lgl, lit)) return 0;
  rsn = lglrsn (lgl, lit);
  r0 = rsn[0];
  tag = (r0 & MASKCS);
  if (tag == DECISION) return 0;
  old = lglcntstk (&lgl->seen);
  assert (lglmtstk (&lgl->minstk));
  for (;;) {
    r1 = rsn[1];
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      if (lglpoison (lgl, other, &lgl->minstk, local)) goto FAILED;
      if (tag == TRNCS && lglpoison (lgl, r1, &lgl->minstk, local))
	goto FAILED;
    } else {
      assert (tag == LRGCS);
      p = lglidx2lits (lgl, (r0 & REDCS), r1);
      found = 0;
      while ((other = *p++)) {
	if (other == -lit) found++;
	else if (lglpoison (lgl, other, &lgl->minstk, local)) goto FAILED;
      }
      assert (found == 1);
    }
    if (lglmtstk (&lgl->minstk)) { lglrelstk (lgl, &lgl->minstk); return 1; }
    lit = lglpopstk (&lgl->minstk);
    assert (lglavar (lgl, lit)->mark);
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0];
    tag = (r0 & MASKCS);
  }
FAILED:
  lglclnstk (&lgl->minstk);
  p = lgl->seen.top;
  top = lgl->seen.top = lgl->seen.start + old;
  while (p > top) {
    lit = *--p;
    av = lglavar (lgl, lit);
    assert (av->mark);
    av->mark = 0;
    if (!lgl->opts->poison.val) continue;
    poisoned = av->poisoned;
    if (poisoned) continue;
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0];
    tag = (r0 & MASKCS);
    assert (tag != DECISION);
    r1 = rsn[1];
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      bv = lglavar (lgl, other);
      if (bv->poisoned) poisoned = 1;
      else if (tag == TRNCS) {
	bv = lglavar (lgl, r1);
	if (bv->poisoned) poisoned = 1;
      }
    } else {
      assert (tag == LRGCS);
      q = lglidx2lits (lgl, (r0 & REDCS), r1);
      while (!poisoned && (other = *q++))
	poisoned = lglavar (lgl, other)->poisoned;
    }
    if (!poisoned) continue;
    assert (!av->poisoned);
    av->poisoned = 1;
    lglpushstk (lgl, &lgl->poisoned, lit);
  }
  return 0;
}

double lglmaxmb (LGL * lgl) {
  REQINIT ();
  return (lgl->stats->bytes.max + sizeof *lgl) / (double)(1<<20);
}

size_t lglbytes (LGL * lgl) {
  REQINIT ();
  return lgl->stats->bytes.current;
}

double lglmb (LGL * lgl) {
  REQINIT ();
  return (lgl->stats->bytes.current + sizeof *lgl) / (double)(1<<20);
}

static double lglavg (double n, double d) {
  return d != 0 ? n / d : 0.0;
}

static double lglheight (LGL * lgl) {
  return lgl->stats->jlevel.slow.val / (double)(1ull<<32);
}

static double lgltlevel (LGL * lgl) {
  return lgl->stats->tlevel.val / (double)(1ull<<32);
}

static double lglglue (LGL * lgl) {
  return lgl->stats->glue.slow.val / (double)(1ull<<32);
}

static void lglrephead (LGL * lgl) {
  if (lgl->tid > 0) return;
  lgl->repforcehead = 0;
  lgl->repcntdown = REPMOD;
  if (lgl->tid > 0) return;
  if (lgl->cbs && lgl->cbs->msglock.lock)
    lgl->cbs->msglock.lock (lgl->cbs->msglock.state);
  assert (lgl->prefix);
  fprintf (lgl->out, "%s\n", lgl->prefix);
  fprintf (lgl->out, "%s%s"
" seconds         irredundant            redundant clauses   glue"
"   iterations\"      MB    stability\n",
    lgl->prefix, !lgl->tid ? "  " : "");
  fprintf (lgl->out, "%s%s"
"         variables clauses conflicts  large ternary binary "
"    jlevel       jlevel'  agility     tlevel\n",
    lgl->prefix, !lgl->tid ? "  " : "");
  fprintf (lgl->out, "%s\n", lgl->prefix);
  fflush (lgl->out);
  if (lgl->cbs && lgl->cbs->msglock.unlock)
    lgl->cbs->msglock.unlock (lgl->cbs->msglock.state);
}

#ifndef NLGLOG
static double lglitavg (LGL * lgl) {
  return lgl->stats->its.avg.slow.val / (double)(1ull<<32);
}
#endif

static double lglitder (LGL * lgl) {
  return 10000.0 * lglavg (lgl->stats->its.avg.diff.smoothed.val / (double)(1ull<<32), lgl->stats->confs);
}

static double lgljlevelder (LGL * lgl) {
  return lgl->stats->jlevel.diff.smoothed.val / (double)(1ll<<32);
}

static void lglrep (LGL * lgl, int level, char type) {
  if (lgl->opts->verbose.val < level) return;
  if ((level > 0 && lgl->repforcehead) || !lgl->repcntdown--)
    lglrephead (lgl);
  lglprt (lgl, level,
    " %c"	// type
    " %6.1f"	// time
    " %7d"	// rem
    " %8d"	// irr
    " %9lld"	// confs
    " %7d"	// lrg
    " %6d"	// trn
    " %5d"	// bin
    " %4.0f"	// glue
    " %5.0f"	// height
    " %6.0f"	// it"
    " %5.0f"	// jl'
    " %4.0f"	// mb
    " %3.0f"	// agility
    " %5.0f"	// stability
    " %6.0f"	// trail
    ,
    type,
    lgl->opts->abstime.val ? lglgetime (lgl) : lglsec (lgl),
    lglrem (lgl),
    lgl->stats->irr.clauses.cur,
    (LGLL) lgl->stats->confs,
    lgl->stats->red.lrg,
    lgl->stats->red.trn,
    lgl->stats->red.bin,
    lglglue (lgl),
    lglheight (lgl),
    lglitder (lgl),
    lgljlevelder (lgl),
    lglmb (lgl),
    100.0*(lgl->stats->agility/(double)(1ll<<32)),
    1000.0*(lgl->stats->stability.avg.val/(double)(1ll<<32)),
    lgltlevel (lgl)
    );
  lgl->stats->reported++;
}

static void lglflshrep (LGL * lgl) {
  if (!lgl->stats->reported) return;
  if (lgl->stats->reported % REPMOD) lglrephead (lgl);
  else lglprt (lgl, 1, "");
}

static void lglfitlir (LGL * lgl, Stk * lir) {
  lglfitstk (lgl, lir);
}

static void lglchkred (LGL * lgl) {
#ifndef NDEBUG
  int glue, idx, sign, lit, thisum, sum, sum2, sum3;
  int blit, tag, red, other, other2;
  int * p, * c, * w, * eow;
  HTS * hts;
  Stk * lir;
  if (lgl->mt) return;
  sum = 0;
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    thisum = 0;
    for (c = lir->start; c < lir->top; c = p + 1) {
      p = c;
      if (*p >= NOTALIT) continue;
      while (*p) p++;
      assert (p - c >= 4);
      thisum++;
    }
    assert (thisum == lgl->stats->lir[glue].clauses);
    sum += thisum;
  }
  assert (sum == lgl->stats->red.lrg);
  sum2 = sum3 = 0;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (!red || tag == LRGCS || tag == OCCS) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	if (tag == BINCS) sum2++;
	else {
	  assert (tag == TRNCS);
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  sum3++;
	}
      }
    }
  assert (sum2 == lgl->stats->red.bin);
  assert (sum3 == lgl->stats->red.trn);
#endif
}

static void lglinitredl (LGL * lgl) {
  lgl->limits->reduce.redlarge = lgl->opts->reduceinit.val;
  lglprt (lgl, 2,
    "[set-reduce-limit] initial reduce limit of %lld after %lld conflicts",
    (LGLL) lgl->limits->reduce.redlarge, (LGLL) lgl->stats->confs);
}

static int lglmemout (LGL * lgl) {
  size_t cur;
  int res;
  if (lgl->opts->memlim.val < 0) return 0;
  cur = lgl->stats->bytes.current;
  cur >>= 20;
  res = (cur >= lgl->opts->memlim.val);
  if (res)
    lglprt (lgl, 2, "memory limit of %d MB hit after allocating %lld MB",
      lgl->opts->memlim.val, (LGLL) cur);
  return res;
}

static Val lgliphase (LGL * lgl, int lit) {
  Val res = lglavar (lgl, lit)->phase;
  if (lit < 0) res = -res;
  return res;
}

static void lglretire (LGL * lgl) {
  int count, ready, inactive, glue, * p, * c, act;
  const int retireint = lgl->opts->retireint.val;
  Stk * s;
  assert (lgl->opts->retirenb.val);
  count = ready = inactive = 0;
  for (glue = 0; glue < MAXGLUE; glue++) {
    s = lgl->red + glue;
    for (c = s->start; c < s->top; c = p + 1) {
      act = *(p = c);
      if (act <= NOTALIT + retireint) {
	count++;
	inactive++;
	assert (lglisact (act));
	if (act <= NOTALIT + 1) { act = NOTALIT; ready++; } else act--;
	assert (lglisact (act));
	*p++ = act;
      } 
      else if (act < REMOVED) {
	count++;
	act = NOTALIT + retireint + (act - NOTALIT - retireint)/2;
	assert (lglisact (act));
	*p++ = act;
      } 
      while (*p) p++;
    }
  }
  lglprt (lgl, 2,
    "[reduce-%d] %d ready to retire %.0f%%, %d inactive %.0f%%",
    lgl->stats->reduced.count,
    ready, lglpcnt (ready, count),
    inactive, lglpcnt (inactive, count));
}

static int lglcmpagsl (LGL * lgl, PAGSL * a, PAGSL * b) {
  int res;
  if ((res = b->psm - a->psm)) return res;
  if ((res = b->glue - a->glue)) return res;
  if ((res = a->act - b->act)) return res;
  if ((res = b->size - a->size)) return res;
  if ((res = a->lidx - b->lidx)) return res;
  return 0;
}

#define LGLCMPAGSL(A,B) lglcmpagsl (lgl, (A), (B))

static void lglreduce (LGL * lgl, int forced) {
  int * p, * q, * start, * c, ** maps, * sizes, * map, * eow, * rsn;
  int nlocked, collected, sumcollected, nunlocked, moved, act, psm;
  int glue, target, nkeep, retired, sumretired;
  PAGSL * pagsls, * pagsl; int npagsls, szpagsls;
  const int retirenb = lgl->opts->retirenb.val;
  const int retiremin = lgl->opts->retiremin.val;
  int size, idx, tag, red, i, blit;
  int r0, lidx, src, dst, lit;
  int inc, delta, npromoted;
  char type = '-';
  HTS * hts;
  DVar * dv;
  Stk * lir;
  lglchkred (lgl);
  lglstart (lgl, &lgl->times->reduce);
  lgl->stats->reduced.count++;
  if (retirenb) lglretire (lgl);
  LOG (1, "starting reduction %d", lgl->stats->reduced.count);
  delta = lgl->stats->red.lrg;
  delta -= lgl->lrgluereasons;
  delta -= lgl->stats->lir[0].clauses;
  assert (delta >= 0);
  if (delta > 3*lgl->limits->reduce.redlarge/2)
    target = delta - lgl->limits->reduce.redlarge/2;
  else target = delta/2;
  if (target < 0) target = 0;
  lglprt (lgl, 2,
    "[reduce-%d] target is to collect %d clauses %.0f%%",
    lgl->stats->reduced.count, target,
    lglpcnt (target, lgl->stats->red.lrg));
  NEW (maps, MAXGLUE);
  NEW (sizes, MAXGLUE);
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    size = lglcntstk (lir);
    assert (!size || size >= 6);
    size = (size + 5)/6;
    sizes[glue] = size;
    lglfitstk (lgl, lir);
    NEW (maps[glue], size);
    map = maps[glue];
    for (i = 0; i < size; i++) map[i] = -2;
  }
  nlocked = 0;
  for (i = 0; i < lglcntstk (&lgl->trail); i++) {
    lit = lglpeek (&lgl->trail, i);
    idx = abs (lit);
    rsn = lglrsn (lgl, idx);
    r0 = rsn[0];
    red = r0 & REDCS;
    if (!red) continue;
    tag = r0 & MASKCS;
    if (tag != LRGCS) continue;
    lidx = rsn[1];
    glue = lidx & GLUEMASK;
    if (glue == MAXGLUE) continue;
    lidx >>= GLUESHFT;
#ifndef NLGLOG
    lir = lgl->red + glue;
    assert (lglpeek (lir, lidx) < REMOVED);
    LOGCLS (5, lir->start + lidx,
      "locking reason of literal %d glue %d clause",
      lit, glue);
#endif
    lidx /= 6;
    assert (maps);
    assert (maps[glue]);
    assert (lidx < sizes[glue]);
    assert (maps[glue][lidx] == -2);
    maps[glue][lidx] = -1;
    nlocked++;
  }
  lglprt (lgl, 2,
    "[reduce-%d] locked %d learned reason clauses %.0f%%",
     lgl->stats->reduced.count,
     nlocked, lglpcnt (nlocked, lgl->stats->red.lrg));
  npromoted = 0;
  while (!lglmtstk (&lgl->promote)) {
    lidx = lglpopstk (&lgl->promote);
    glue = lidx & GLUEMASK;
    assert (glue < MAXGLUE);
    if (!maps[glue]) { assert (!sizes[glue]); continue; }
    assert (0 < glue), assert (glue < MAXGLUE);
    lidx >>= GLUESHFT;
    assert (lidx > 0);
    lir = lgl->red + glue;
    p = lir->start + lidx;
    if (p >= lir->top) continue;
    if (*p >= NOTALIT) continue;
    if (!lglisact (p[-1])) continue;
    if (maps[glue][lidx/6] == -1) continue;
#ifndef NLGLOG
    LOGCLS (5, lir->start + lidx,
      "locking promoted glue %d clause",
      glue);
#endif
    assert (lidx/6 < sizes[glue]);
    maps[glue][lidx/6] = -1;
    lgl->stats->promote.locked++;
    npromoted++;
  }
  lglprt (lgl, 2,
    "[reduce-%d] locked %d promoted learned clauses %.0f%%",
    lgl->stats->reduced.count,
    npromoted, lglpcnt (npromoted, lgl->stats->red.lrg));

  szpagsls = lgl->stats->red.lrg;
  NEW (pagsls, szpagsls);
  retired = npagsls = 0;
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    start = lir->start;
    for (c = start; c < lir->top; c = p + 1) {
      if ((act = *c++) == REMOVED) {
	for (p = c; p < lir->top && *p == REMOVED; p++)
	  ;
	p--;
	continue;
      }
      LGLCHKACT (act);
      lidx = c - start;
      act -= NOTALIT;
      psm = 0;
      for (p = c; (lit = *p); p++)
	if (lgliphase (lgl, lit) >= 0) psm++;
      size = p - c;
      LOG (5, 
         "clause red[%d][%d] has: psm %d, act %d, size %d",
	 glue, lidx, psm, act, size);

      if (maps[glue][lidx/6] == -1) continue;
      assert (maps[glue][lidx/6] == -2);

      if (retirenb && !act && glue >= retiremin) {
	retired++;
	maps[glue][lidx/6] = -3;
	LOG (5, "retiring this inactive clause");
	continue;
      }

      if (!glue && size <= lgl->opts->gluekeepsize.val) {
        LOG (5, "keeping this glue 0 size %d clause", size);
        maps[glue][lidx/6] = -1;
        continue;
      }

      assert (npagsls < szpagsls);
      pagsl = pagsls + npagsls++;
      pagsl->psm = psm;
      pagsl->act = act;
      pagsl->glue = glue;
      pagsl->size = size;
      pagsl->lidx = lidx;
    }
  }
  assert (npagsls <= szpagsls);
  LOG (2,
    "retiring %d learned clauses %.0f%%",
    retired, lglpcnt (retired, lgl->stats->red.lrg));

  SORT (PAGSL, pagsls, npagsls, LGLCMPAGSL);
  LOG (1, "copied and sorted %d activities", npagsls);

  nkeep = 0;
  for (idx = target; idx < npagsls; idx++) {
    pagsl = pagsls + idx;
    lidx = pagsl->lidx;
    glue = pagsl->glue;
    assert (lidx/6 < sizes[glue]);
    maps[glue][lidx/6] = -1;
    nkeep++;
    LOG (5, 
      "marked clause red[%d][%d] to keep with psm %d, act %d, size %d",
      glue, lidx, pagsl->psm, pagsl->act, pagsl->size);
  }
  DEL (pagsls, szpagsls);
  LOG (1, "explicity marked %d additional clauses to keep", nkeep);
  sumcollected = sumretired = 0;
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    map = maps[glue];
#ifndef NDEBUG
    size = sizes[glue];
#endif
    q = start = lir->start;
    collected = retired = 0;
    for (c = start; c < lir->top; c = p + 1) {
      act = *c++;
      if (act == REMOVED) {
	for (p = c; p < lir->top && *p == REMOVED; p++)
	  ;
	assert (p >= lir->top || *p < NOTALIT || lglisact (*p));
	p--;
	continue;
      }
      p = c;
      LGLCHKACT (act);
      src = (c - start)/6;
      assert (src < size);
      if (map[src] <= -2) {
	assert (collected + retired < lgl->stats->lir[glue].clauses);
	if (map[src] == -2) {
	  collected++;
	  LOGCLS (5, c, "collecting glue %d clause", glue);
	} else {
	  assert (map[src] == -3);
	  retired++;
	  LOGCLS (5, c, "retiring glue %d clause", glue);
	}
	lgldrupligdelclsaux (lgl, c);
	while (*p) p++;
      } else {
	dst = q - start + 1;
	map[src] = dst;
	if (p == q) {
	  while (*p) p++;
	  q = p + 1;
	} else {
	  *q++ = act;
	  LOGCLS (5, c, "moving from %d to %d glue %d clause",
		  (c - start), dst, glue);
	  while (*p) *q++ = *p++;
	  *q++ = 0;
	}
      }
    }
    LOG (2, "collected %d glue %d clauses", collected, glue);
    assert (sumcollected + sumretired <= lgl->stats->red.lrg);
    assert (lgl->stats->lir[glue].clauses >= collected + retired);
    lgl->stats->lir[glue].clauses -= collected + retired;
    lgl->stats->lir[glue].reduced += collected;
    lgl->stats->lir[glue].retired += retired;
    sumcollected += collected;
    sumretired += retired;
    lir->top = q;
    lglfitlir  (lgl, lir);
  }
  lglprt (lgl, 2,
    "[reduce-%d] collected %d clauses %.0f%%, retired %d clauses %.0f%%", 
    lgl->stats->reduced.count,
    sumcollected, lglpcnt (sumcollected, lgl->stats->red.lrg),
    sumretired, lglpcnt (sumretired, lgl->stats->red.lrg));
  assert (sumcollected + sumretired <= lgl->stats->red.lrg);
  lgl->stats->red.lrg -= sumcollected + sumretired;
  lgl->stats->reduced.collected += sumcollected;
  lgl->stats->reduced.retired += sumretired;
  nunlocked = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglval (lgl, idx)) continue;
    rsn = lglrsn (lgl, idx);
    r0 = rsn[0];
    red = r0 & REDCS;
    if (!red) continue;
    tag = r0 & MASKCS;
    if (tag != LRGCS) continue;
    lidx = rsn[1];
    glue = lidx & GLUEMASK;
    if (glue == MAXGLUE) continue;
    src = (lidx >> GLUESHFT);
    assert (src/6 < sizes[glue]);
    dst = maps[glue][src/6];
    assert (dst >= 0);
    dst <<= GLUESHFT;
    dst |= lidx & GLUEMASK;
    rsn[1] = dst;
    nunlocked++;
  }
  LOG (2, "unlocked %d reasons", nunlocked);
  assert (nlocked == nunlocked);
  collected = moved = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    dv = lgldvar (lgl, idx);
    for (i = 0; i <= 1; i++) {
      hts = dv->hts + i;
      if (!hts->offset) continue;
      q = lglhts2wchs (lgl, hts);
      assert (hts->count >= 0);
      eow = q + hts->count;
      for (p = q; p < eow; p++) {
	blit = *p;
	red = blit & REDCS;
	tag = blit & MASKCS;
	if (red && tag == LRGCS) {
	  lidx = *++p;
	  glue = lidx & GLUEMASK;
	  if (glue == MAXGLUE) {
	    dst = lidx >> GLUESHFT;
	  } else {
	    src = lidx >> GLUESHFT;
	    assert (src/6 < sizes[glue]);
	    dst = maps[glue][src/6];
	  }
	  if (dst >= 0) {
	    moved++;
	    *q++ = blit;
	    *q++ = (dst << GLUESHFT) | (lidx & GLUEMASK);
	  } else collected++;
	} else {
	  *q++ = blit;
	  if (tag != BINCS) {
	    assert (tag == TRNCS || tag == LRGCS);
	    *q++ = *++p;
	  }
	}
      }
      lglshrinkhts (lgl, hts, hts->count - (p - q));
    }
  }
  LOG (1, "moved %d and collected %d occurrences", moved, collected);
  for (glue = 0; glue < MAXGLUE; glue++)
    DEL (maps[glue], sizes[glue]);
  DEL (sizes, MAXGLUE);
  DEL (maps, MAXGLUE);
  if (lgl->opts->reducefixed.val) goto NOINC;
  if (lglmemout (lgl)) {
    inc = 0;
    lglprt (lgl, 2,
      "[reduce-%d] no increase of reduce limit since memory limit was hit",
      lgl->stats->reduced.count);
    lgl->stats->reduced.memlim++;
  } else {
    inc = lgl->opts->reduceinc.val;
    lglprt (lgl, 2,
      "[reduce-%d] increase of reduce limit by %d to %d",
      lgl->stats->reduced.count, inc, lgl->limits->reduce.redlarge + inc);
    lgl->stats->reduced.arith++;
  }
  LOG (1, "reduce increment %d", inc);
  lgl->limits->reduce.redlarge += inc;
  assert (forced || lgl->opts->reduce.val);
NOINC:
  lglrelstk (lgl, &lgl->learned);
  lglrep (lgl, 1, type);
  lglchkred (lgl);
  lglstop (lgl);
#ifndef NDEBUG
  lglclnstk (&lgl->prevclause);
  lgl->prevglue = -1;
#endif
}

void lglreducecache (LGL * lgl) {
  REQINITNOTFORKED ();
  TRAPI ("reduce");
  if (lgl->mt) return;
  lglinitredl (lgl);
  lglreduce (lgl, 1);
  lglinitredl (lgl);
  lglprt (lgl, 1, "[reduce-cache] new limit %d", lgl->limits->reduce.redlarge);
  if (lgl->clone) lglreducecache (lgl->clone);
}

static void lgliflushcache (LGL * lgl, int keep) {
  int idx, sign, lit, blit, tag, red, * w, * q, lidx, glue;
  const int druplig = lgl->opts->druplig.val;
  int bin, trn, lrg, start;
  const int * p, * eow;
  HTS * hts;
  assert (1 <= keep), assert (keep <= 4);
  if (lgl->level) lglbacktrack (lgl, 0);
  bin = trn = lrg = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      q = w;
      for (p = q; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	red = blit & REDCS;
	if (red) {
	  if (tag == BINCS) {
	    if (keep < 2) {
	      if (druplig) {
		int other = blit >> RMSHFT;
		if (idx < abs (other))
		  lgldrupligdelclsarg (lgl, lit, other, 0);
	      }
	      continue;
	    }
	  } else if (tag == TRNCS) {
	    if (keep < 3) {
	      if (druplig) {
		int other = blit >> RMSHFT;
		if (idx < abs (other)) {
		  int other2 = *p;
		  if (idx < abs (other2))
		    lgldrupligdelclsarg (lgl, lit, other, other2, 0);
		}
	      }
	      continue;
	    }
	  } else {
	    assert (tag == LRGCS);
	    lidx = *p;
	    glue = lidx & GLUEMASK;
	    if (keep < 4 || glue > 0) {
	      if (druplig) {
                const int * c = lglidx2lits (lgl, red, lidx);
		if (*c == lit)
		  lgldrupligdelclsaux (lgl, c);
	      }
	      continue;
	    }
	  }
	}
	*q++ = blit;
	if (tag == TRNCS || tag == LRGCS) *q++ = *p;
      }
      lglshrinkhts (lgl, hts, q - w);
    }
  }
  if (keep < 2) bin = lgl->stats->red.bin, lgl->stats->red.bin = 0;
  if (keep < 3) trn = lgl->stats->red.trn, lgl->stats->red.trn = 0;
  start = (keep >= 4);
  for (glue = start; glue < MAXGLUE; glue++) {
    lrg += lgl->stats->lir[glue].clauses;
    lgl->stats->lir[glue].clauses = 0;
  }
  assert (lrg <= lgl->stats->red.lrg), lgl->stats->red.lrg -= lrg;
  lglrelstk (lgl, &lgl->learned);
  for (glue = start; glue < MAXGLUE; glue++)
    lglrelstk (lgl, lgl->red + glue);
  lglprt (lgl, 1,
    "[flush-cache] %d binary, %d ternary, %d large",
    bin, trn, lrg);
#ifndef NDEBUG
  lglclnstk (&lgl->prevclause);
  lgl->prevglue = -1;
#endif
}

void lglflushcache (LGL * lgl) {
  REQINITNOTFORKED ();
  TRAPI ("flush");
  if (lgl->mt) return;
  lglinitredl (lgl);
  lgliflushcache (lgl, 3);
  lglinitscores (lgl);
  lglinitredl (lgl);
  lglprt (lgl, 1, "[flush-cache] new limit %d", lgl->limits->reduce.redlarge);
  if (lgl->clone) lglflushcache (lgl->clone);
}


static void lglrmbwch (LGL * lgl, int lit, int other, int red) {
  int * p, blit, blit1, * w, * eow, tag;
  HTS * hts;
  assert (!red || red == REDCS);
  LOG (3, "removing %s binary watch %d blit %d",
       lglred2str (red), lit, other);
  hts = lglhts (lgl, lit);
  assert (hts->count >= 1);
  p = w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  lglrminc (lgl, w, eow);
  blit1 = RMSHFTLIT (other) | red | BINCS;
  for (;;) {
    assert (p < eow);
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) { p++; continue; }
    if (tag == OCCS) { assert (lgl->dense); continue; }
    assert (tag == BINCS);
    if (blit == blit1) break;
  }
  while (p < eow) p[-1] = p[0], p++;
  lglshrinkhts (lgl, hts, p - w - 1);
}

static int lglpopesched (LGL * lgl) {
  Stk * s = &lgl->esched;
  int res, last, cnt, * p;
  EVar * ev;
  assert (!lglmtstk (s));
  res = *s->start;
  assert (!lglifrozen (lgl, res));
  LOGESCHED (4, res, "popped");
  ev = lglevar (lgl, res);
  assert (!ev->pos);
  ev->pos = -1;
  last = lglpopstk (s);
  cnt = lglcntstk (s);
  if (!cnt) { assert (last == res); return res; }
  p = lglepos (lgl, last);
  assert (*p == cnt);
  *p = 0;
  *s->start = last;
  lgledown (lgl, last);
  return res;
}

static void lgldecocc (LGL * lgl, int lit) {
  int idx, sign, change;
  EVar * ev;
  if (!lgl->occs) return;
  idx = abs (lit), sign = (lit < 0);
  ev = lglevar (lgl, lit);
  assert (ev->occ[sign] > 0);
  ev->occ[sign] -= 1;
  if (!lglisfree (lgl, lit)) return;
  change = lglecalc (lgl, ev);
  LOG (3, "dec occ of %d now occs[%d] = %d %d",
       lit, idx,  ev->occ[0], ev->occ[1]);
  if (ev->pos < 0) lglesched (lgl, idx);
  else if (change < 0) lgleup (lgl, idx);
  else if (change > 0) lgledown (lgl, idx);
}

static void lglrmbcls (LGL * lgl, int a, int b, int red) {
  lglrmbwch (lgl, a, b, red);
  lglrmbwch (lgl, b, a, red);
  LOG (2, "removed %s binary clause %d %d", lglred2str (red), a, b);
  lgldeclscnt (lgl, 2, red, 0);
  if (!red && lgl->dense) lgldecocc (lgl, a), lgldecocc (lgl, b);
}

static void lglrmtcls (LGL * lgl, int a, int b, int c, int red) {
  lglrmtwch (lgl, a, b, c, red);
  lglrmtwch (lgl, b, a, c, red);
  lglrmtwch (lgl, c, a, b, red);
  LOG (2, "removed %s ternary clause %d %d %d", lglred2str (red), a, b, c);
  lgldeclscnt (lgl, 3, red, 0);
  if (!red && lgl->dense)
    lgldecocc (lgl, a), lgldecocc (lgl, b), lgldecocc (lgl, c);
}

static void lgltrimlitstk (LGL * lgl, int red, int lidx) {
  Stk * s;
  int * p;
  if (lgl->notrim) return;
  s = lglidx2stk (lgl, red, lidx);
  p = s->top;
  while (p > s->start && p[-1] == REMOVED)
    p--;
  if (p < s->top) {
    int64_t trimmed = s->top - p;
#ifndef NLGLOG
    if (red)
       LOG (4,
         "trimmed 'red[%d]' by %lld", 
         (lidx & GLUEMASK), (LGLL) trimmed);
    else LOG (4, "trimmed 'irr' by %lld", (LGLL) trimmed);
#endif
    lgl->stats->trims += trimmed;
    s->top = p;
    if (red) {
      int glue = (lidx & GLUEMASK), maxlidx;
      assert (s == &lgl->red[glue]);
      maxlidx = (lglcntstk (s) << GLUESHFT) | glue;
      for (p = lgl->learned.start; p < lgl->learned.top; p += 3) {
       int olidx = *p, oglue = (olidx & GLUEMASK);
       if (oglue == glue && olidx >= maxlidx) *p = INT_MIN;
      }
    }
  }
}

static void lglrmlcls (LGL * lgl, int lidx, int red) {
  int * c, * p, glue, lit;
  assert (!red || red == REDCS);
  glue = red ? (lidx & GLUEMASK) : 0;
  c = lglidx2lits (lgl, red, lidx);
  if (!red || glue < MAXGLUE) {
    lglrmlwch (lgl, c[0], red, lidx);
    lglrmlwch (lgl, c[1], red, lidx);
  }
  if (!red && lgl->dense) {
    for (p = c; (lit = *p); p++) {
      lglrmlocc (lgl, lit, red, lidx);
      lgldecocc (lgl, lit);
    }
  }
  if (red && glue < MAXGLUE) { LGLCHKACT (c[-1]); c[-1] = REMOVED; }
  for (p = c; *p; p++) *p = REMOVED;
  *p = REMOVED;
  if (glue != MAXGLUE) lgldeclscnt (lgl, p - c, red, glue);
  lgltrimlitstk (lgl, red, lidx);
}

static void lgldynsub (LGL * lgl, int lit, int r0, int r1) {
  int red, tag, other, other2;
  const int * c;
  tag = r0 & MASKCS;
  LOGREASON (2, lit, r0, r1, "removing on-the-fly subsumed");
  red = r0 & REDCS;
  if (red) lgl->stats->otfs.sub.red++;
  else lgl->stats->otfs.sub.irr++;
  if (tag == BINCS) {
    lgl->stats->otfs.sub.bin++;
    other = (r0 >> RMSHFT);
    lgldrupligdelclsarg (lgl, lit, other, 0);
    lglrmbcls (lgl, lit, other, red);
  } else if (tag == TRNCS) {
    lgl->stats->otfs.sub.trn++;
    other = (r0 >> RMSHFT), other2 = r1;
    lgldrupligdelclsarg (lgl, lit, other, other2, 0);
    lglrmtcls (lgl, lit, other, other2, red);
  } else { 
    assert (tag == LRGCS);
    lgl->stats->otfs.sub.lrg++;
    c = lglidx2lits (lgl, red, r1);
    lgldrupligdelclsaux (lgl, c);
    lglrmlcls (lgl, r1, red);
  }
}


static void lglunflict (LGL * lgl, int lit) {
  lgl->conf.lit = lit;
  lgl->conf.rsn[0] = RMSHFTLIT (lit) | UNITCS;
  LOG (1, "inconsistent unary clause %d", lit);
}

static void lgldynstr (LGL * lgl, int del, int lit, int r0, int r1) {
  int * p, * c, lidx, other, red, tag, glue, other2, other3, blit;
  tag = r0 & MASKCS;
  LOGREASON (2, lit, r0, r1,
    "on-the-fly strengthening by removing %d from", del);
  red = r0 & REDCS;
  if (red) lgl->stats->otfs.str.red++;
  else lgl->stats->otfs.str.irr++;
  lgl->stats->otfs.total++;
  lgl->stats->prgss++;
  if (!red) lgl->stats->irrprgss++;
  if (tag == BINCS) {
    lgl->stats->otfs.str.bin++;
    other = (del == lit) ? (r0 >> RMSHFT) : lit;
    assert (other != del);
    lgldrupligaddclsarg (lgl, REDCS, other, 0);
    lgldrupligdelclsarg (lgl, del, other, 0);
    lglrmbcls (lgl, del, other, red);
    lglunflict (lgl, other);
    return;
  }
  if (tag == TRNCS) {
    lgl->stats->otfs.str.trn++;
    if (lit == del) other = (r0 >> RMSHFT), other2 = r1;
    else if (del == r1) other = lit, other2 = (r0 >> RMSHFT);
    else other = lit, other2 = r1;
    assert (del != other && del != other2);
    lgldrupligaddclsarg (lgl, REDCS, other, other2, 0);
    lgldrupligdelclsarg (lgl, del, other, other2, 0);
    lglrmtcls (lgl, del, other, other2, red);
    if (!red) lglincirr (lgl, 2);
    else lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
    lglwchbin (lgl, other, other2, red);
    lglwchbin (lgl, other2, other, red);
    if (lglevel (lgl, other) < lglevel (lgl, other2)) SWAP (int, other, other2);
    blit = RMSHFTLIT (other2) | BINCS | red;
    lglbonflict (lgl, other, blit);
    return;
  }
  assert (tag == LRGCS);
  lgl->stats->otfs.str.lrg++;
  lidx = r1;
  glue = red ? (lidx & GLUEMASK) : 0;
  c = lglidx2lits (lgl, red, lidx);
  for (p = c; *p != del; p++)
    assert (*p);
  if (glue < MAXGLUE) {
    lglrmlwch (lgl, c[0], red, lidx);
    lglrmlwch (lgl, c[1], red, lidx);
  }
  while ((other = *++p)) p[-1] = other;
  p[-1] = 0, *p = REMOVED;
  lgltrimlitstk (lgl, red, lidx);
  if (!red) assert (lgl->stats->irr.lits.cur), lgl->stats->irr.lits.cur--;
  lglorderclsaux (lgl, c + 0);
  lglorderclsaux (lgl, c + 1);
  lgldrupligaddclsaux (lgl, REDCS, c);
  assert (p - c > 3);
  if (p - c == 4) {
    assert (!c[3] && c[4] >= NOTALIT);
    other = c[0], other2 = c[1], other3 = c[2];
    if (red && glue < MAXGLUE) { LGLCHKACT (c[-1]); c[-1] = REMOVED; }
    c[0] = c[1] = c[2] = c[3] = REMOVED;
    lgltrimlitstk (lgl, red, lidx);
    if (lglevel (lgl, other2) < lglevel (lgl, other3))
      SWAP (int, other2, other3);
    if (lglevel (lgl, other) < lglevel (lgl, other2))
      SWAP (int, other, other2);
    lglwchtrn (lgl, other, other2, other3, red);
    lglwchtrn (lgl, other2, other, other3, red);
    lglwchtrn (lgl, other3, other, other2, red);
    if (red) {
      if (glue < MAXGLUE) {
	assert (lgl->stats->red.lrg > 0);
	lgl->stats->red.lrg--;
	assert (lgl->stats->lir[glue].clauses > 0);
	lgl->stats->lir[glue].clauses--;
      }
      lgl->stats->red.trn++;
      assert (lgl->stats->red.trn > 0);
    }
    lgltonflict (lgl, other, RMSHFTLIT (other2) | red | TRNCS, other3);
  } else {
    if (glue < MAXGLUE) {
      LOG (3, "new head literal %d", c[0]);
      (void) lglwchlrg (lgl, c[0], c[1], red, lidx);
      LOG (3, "new tail literal %d", c[1]);
      (void) lglwchlrg (lgl, c[1], c[0], red, lidx);
    }
    lglonflict (lgl, 0, c[0], red, lidx);
  }
}

static void lglclnframes (LGL * lgl) {
  while (!lglmtstk (&lgl->frames))
    lglunuselevel (lgl, lglpopstk (&lgl->frames));
}

static void lglclnpoisoned (LGL * lgl) {
  while (!lglmtstk (&lgl->poisoned)) {
    int lit = lglpopstk (&lgl->poisoned);
    AVar * av = lglavar (lgl, lit);
    assert (!av->mark);
    assert (av->poisoned);
    av->poisoned = 0;
  }
}

static void lglclnana (LGL * lgl) {
#ifdef RESOLVENT
  if (lglmaintainresolvent (lgl)) lglclnstk (&lgl->resolvent);
#endif
  lglclnstk (&lgl->clause);
  lglpopnunmarkstk (lgl, &lgl->seen);
  lglclnframes (lgl);
}

static void lglbumpdlit (LGL * lgl, int lit) {
  int idx = abs (lit), mightneedtorescore = 0;
  QVar * qv = lglqvar (lgl, idx);
  Flt oldscore, newscore;
  if (lgl->simp && !lgl->opts->bumpsimp.val) return;
  if (qv->enqueued) {
    assert (lglpeek (&lgl->queue.stk, qv->pos) == abs (lit));
    lglpoke (&lgl->queue.stk, qv->pos, 0);
    lgl->queue.mt++;
    qv->enqueued = 0;
    qv->pos = -1;
    if (!lglval (lgl, lit)) lgldsched (lgl, idx);
  }
  oldscore = qv->score;
  newscore = lgladdflt (oldscore, lgl->scinc);
  LOG (3,
    "bumping EVSIDS score of variable %d from %s to %s",
    idx, lglscr2str (lgl, oldscore), lglscr2str (lgl, newscore));
  assert (newscore > oldscore);
  mightneedtorescore = 1;
  qv->score = newscore;
  if (lgldscheduled (lgl, idx)) lgldup (lgl, idx);
  if (mightneedtorescore && newscore >= lgl->maxscore) lglrescorevars (lgl);
}

static int lglcmpbump (LGL * lgl, int a, int b) {
  return lgltrail (lgl, b) - lgltrail (lgl, a);
}

#define LGLCMPBUMP(P,Q) lglcmpbump (lgl, *(P), *(Q))

static void lglbumpseenlits (LGL * lgl) {
  const int * p;
  if (lgl->simp && !lgl->opts->bumpsimp.val) return;
  lglstart (lgl, &lgl->times->bump);
  lgl->stats->bump.count++;
  SORT (int, lgl->seen.start, lglcntstk (&lgl->seen), LGLCMPBUMP);
  for (p = lgl->seen.start; p < lgl->seen.top; p++)
    lglbumpdlit (lgl, *p);
  LOG (2, "bumped %d literals", lglcntstk (&lgl->seen));
  lgl->stats->bump.lits += lglcntstk (&lgl->seen);
  lglstop (lgl);
}

static void lglmincls (LGL * lgl, int uip, int glue) {
  int origsize = lglcntstk (&lgl->clause) - 1;
  int * p, * q, other, minimized, local;
  if (!lgl->opts->minimize.val) return;
  if (glue > lgl->opts->minlocalgluelim.val) return;
  if (origsize > lgl->opts->minlocalsizelim.val) return;
  lglstart (lgl, &lgl->times->mincls);
  lgl->stats->mincls.min++;
  q = lgl->clause.start;
  minimized = 0;
  local = lgl->opts->minimize.val <= 1 || 
          glue > lgl->opts->minrecgluelim.val ||
          origsize > lgl->opts->minrecsizelim.val;
  assert (lglmtstk (&lgl->poisoned));
  for (p = q; (other = *p); p++)
    if (other != uip && lglminclslit (lgl, other, local)) {
      LOG (2, "minimized literal %d", other);
      minimized++;
    } else *q++ = other;
  *q++ = 0;
  lglclnpoisoned (lgl);
  assert (lgl->clause.top - q == minimized);
  COVER (glue + 1 >= origsize && minimized > 0);	// unreachable ...
  LOG (2, "clause minimized by %d literals", minimized);
  LOGCLS (2, lgl->clause.start, "minimized clause");
  lgl->clause.top = q;
  lglstop (lgl);
}

static void lglsignedmarknpushseen (LGL *, int);
static int lglsignedmarked (LGL *, int);

static int lglcmpuiplitrail (LGL * lgl, int uip, int a, int b) {
  if (a == uip) return -1;
  if (b == uip) return 1;
  return lgltrail (lgl, a) - lgltrail (lgl, b);
}

#define LGLCMPUIPLITRAIL(P,Q) lglcmpuiplitrail (lgl, uip, *(P), *(Q))

static void lglredclsassign (LGL * lgl, int lit) {
  assert (!lglmarked (lgl, lit)), assert (!lglifixed (lgl, lit));
  lglmark (lgl, lit);
  lglpushstk (lgl, &lgl->seen, lit);
  LOG (3, "assigning literal %d for clause reduction", lit);
}

static int lglredclsmarked (LGL * lgl, int lit) {
  int mark, val;
  mark = lglmarked (lgl, lit);
  if (mark) return mark;
  val = lglifixed (lgl, lit);
  if (val) return val;
  return 0;
}

static void lglredcls (LGL * lgl, int uip, int glue, int * jlevelptr) {
  int lit, cand, blit, tag, other, other2, count, size, reduced;
  int * q, newjlevel, oldjlevel, level, sat, red, lidx, unit;
  int dec, depth, props, mark, mark2, markcand, lrg;
  const int * p, * w, * eow, * r, * l, * c;
  HTS * hts;
  const int maxdepth = lgl->opts->redclsmaxdepth.val;
  const int maxprops = lgl->opts->redclsmaxprops.val;
  const int maxlrg = lgl->opts->redclsmaxlrg.val;
  const int maxdec = lgl->opts->redclsmaxdec.val;
  const int type = lgl->opts->redclstype.val;
  if (!lgl->opts->redcls.val) return;
  if (glue > lgl->opts->redclsglue.val) return;
  if (lglcntstk (&lgl->clause) >= lgl->opts->redclsize.val) return;
  lglstart (lgl, &lgl->times->redcls);
  lgl->stats->redcls.cls.tried++;
  lglpopnunmarkstk (lgl, &lgl->seen);
  size = lglcntstk (&lgl->clause) - 1;
  assert (size >= 1);
  SORT (int, lgl->clause.start, size, LGLCMPUIPLITRAIL);
  assert (lglpeek (&lgl->clause, 0) == uip);
#ifndef NLGLOG
  if (lgl->opts->log.val >= 2) {
    lglogstart (lgl, 2, "sorted clause before reducing");
    for (p = lgl->clause.start; p < lgl->clause.top; p++) {
      if (!(lit = *p)) continue;
      fprintf (lgl->out, " %d (l%d,t%d)",
        lit, lglevel (lgl, lit), lgltrail (lgl, lit));
    }
    lglogend (lgl);
  }
#endif
  sat = reduced = 0;
  assert (lgl->clause.start < lgl->clause.top);
  assert (!lgl->clause.top[-1]);
  dec = 0;
  for (p = q = lgl->clause.start; p < lgl->clause.top; p++) {
    if (!(cand = *p)) *q++ = cand;
    else {
      lgl->stats->redcls.lits.tried++;
      markcand = lglredclsmarked (lgl, cand);
      if (markcand > 0) {
	LOG (3, "skipping true literal %d for clause reduction", cand);
	lgl->stats->redcls.lits.sat++;
	*q++ = cand;
	sat = 1;
      } else if (markcand < 0) {
	LOG (3, "reducing clause by removing literal %d", cand);
	lgl->stats->redcls.lits.red++;
	reduced++;
      } else {
	assert (!markcand);
	*q++ = cand;
	assert (p + 1 < lgl->clause.top);
	if (!p[1]) continue;
	if (++dec > maxdec) continue;
	LOG (3, "decision literal %d for clause reduction", -cand);
	depth = props = lrg = 0;
	count = lglcntstk (&lgl->seen);
	lglredclsassign (lgl, -cand);
	while (count < lglcntstk (&lgl->seen)) {
	  if (props >= maxprops) break;
	  if (depth >= maxdepth) break;
	  lit = lglpeek (&lgl->seen, count++);
	  if (lit) props++; else { depth++; continue; }
	  assert (lglredclsmarked (lgl, lit) > 0);
	  LOG (4, "propagating literal %d for clause reduction", lit);
	  hts = lglhts (lgl, -lit);
	  w = lglhts2wchs (lgl, hts);
	  eow = w + hts->count;
	  for (r = w; r < eow; r++) {
	    blit = *r;
	    tag = blit & MASKCS;
	    if (tag == TRNCS || tag == LRGCS) r++;
	    if (tag == BINCS) {
	      other = blit >> RMSHFT;
	      if (lglredclsmarked (lgl, other)) continue;
	      lglredclsassign (lgl, other);
	    } else if (tag == TRNCS) {
	      if (cand != uip || type < 3) continue;
	      other = blit >> RMSHFT;
	      mark = lglredclsmarked (lgl, (other));
	      if (mark > 0) continue;
	      other2 = *r;
	      mark2 = lglredclsmarked (lgl, other2);
	      if (mark2 > 0) continue;
	      if (mark2 < 0 && !mark) lglredclsassign (lgl, other);
	      if (mark < 0 && !mark2) lglredclsassign (lgl, other2);
	    } else {
	      assert (tag == LRGCS);
	      if (type < 4 || cand != uip) continue;
	      if (++lrg >= maxlrg) continue;
	      other = blit >> RMSHFT;
	      mark = lglredclsmarked (lgl, other);
	      if (mark > 0) continue;
	      red = blit & REDCS;
	      lidx = *r;
	      c = lglidx2lits (lgl, red, lidx);
	      unit = 0;
	      for (l = c; (other = *l); l++) {
		if (other == -lit) continue;
		mark = lglredclsmarked (lgl, other);
		if (mark > 0) break;
		if (mark < 0) continue;
		if (unit) break;
		unit = other;
	      }
	      if (other || !unit) continue;
	      lglredclsassign (lgl, unit);
	    }
	  }
	  lglpushstk (lgl, &lgl->seen, 0);
	}
      }
    }
  }
  if (sat) lgl->stats->redcls.cls.sat++;
  lgl->clause.top = q;
  LOG (2, "reduced clause by %d literals", reduced);
  LOGCLS (2, lgl->clause.start, "reduced clause");
  if (reduced) lgl->stats->redcls.cls.red++;
  oldjlevel = *jlevelptr;
  newjlevel = 0;
  for (p = lgl->clause.start; p < lgl->clause.top; p++) {
    if (!(lit = *p) || lit == uip) continue;
    level = lglevel (lgl, lit);
    assert (level != lgl->level);
    if (level > newjlevel) newjlevel = level;
  }
  assert (newjlevel <= oldjlevel);
  if (oldjlevel == newjlevel)
    LOG (2, "jump level %d does not change", newjlevel);
  else {
    LOG (2, "jump level reduced to %d from %d", newjlevel, oldjlevel);
    *jlevelptr = newjlevel;
    lgl->stats->redcls.jlevel.red++;
    lgl->stats->redcls.jlevel.sum += oldjlevel - newjlevel;
  }
  lglstop (lgl);
}

static void lgliassume (LGL * lgl, int lit) {
  lgl->level++;
  lglpushcontrol (lgl, lit);
  assert (lglcntctk (&lgl->control) == lgl->level + 1);
  LOG (2, "internally assuming %d", lit);
  lglassign (lgl, lit, DECISION, 0);
}

static void lgldassume (LGL * lgl, int lit) {
  LOG (1, "next assumed decision %d external %d", lit, lglexport (lgl, lit));
  lgl->stats->decisions++;
  lgliassume (lgl, lit);
  assert (lgldecision (lgl, lit));
}

static int lglsubl (LGL * lgl, int lidx, int size, int glue) {
  const int * c, * p;
  int count, lit;
  assert (lidx);
  assert ((lidx & GLUEMASK) < MAXGLUE);
  c = lglidx2lits (lgl, REDCS, lidx);
  count = 0;
  for (p = c; count < size && (lit = *p); p++) {
    if (lit == REMOVED) return 1;
    if (lglmarked (lgl, lit) > 0) count++;
  }
  lgl->stats->subl.tried++;
  if (count < size) {
    LOGCLS (4, c, "only %d literals shared in clause", count);
    return 0;
  }
  assert (!lglrgforcing (lgl, REDCS, lidx));
  LOGCLS (2, c,
    "subsumed learned (scaled) glue %d clause",
    (int)(lidx & GLUEMASK));
  LOGCLS (2, lgl->clause.start,
    "subsumed by new size %d glue %d scaled glue %d clause",
    size, glue, lglscaleglue (lgl, glue));
  lgl->stats->subl.sub++;
  lgldrupligdelclsaux (lgl, c);
  lglrmlcls (lgl, lidx, REDCS);
  return 1;
}

static void lgldrive (
  LGL * lgl, const char * type, int * forcedptr, 
  int * glueptr, int * realglueptr, int * jlevelptr) {
  int lit, jlevel, level, minlevel, maxlevel, glue, realglue, forced;
  const int * p, * soc = lgl->clause.start, * eoc = lgl->clause.top - 1;
  Ctr * c;
  assert (soc <= eoc), assert (!*eoc);
  forced = forcedptr ? *forcedptr : 0;
#ifndef NDEBUG
  for (p = soc; p < eoc; p++) {
    level = lglevel (lgl, lit = *p);
    assert (0 < level), assert (level <= lgl->level);
    c = lgl->control.start + level;
    assert (!c->used2);
  }
#endif
#ifndef NLGLOG
  if (lgl->opts->log.val >= 4) {
    lglogstart (lgl, 2, "driving using clause");
    for (p = soc; p < eoc; p++) {
      lit = *p;
      fprintf (lgl->out, " %d (l%d,t%d)",
        lit, lglevel (lgl, lit), lgltrail (lgl, lit));
    }
    lglogend (lgl);
  }
#endif
  maxlevel = -1, minlevel = lgl->level + 1;
  for (p = soc; p < eoc; p++) {
    level = lglevel (lgl, *p);
    c = lgl->control.start + level;
    if (!c->used2) {
      if (level < minlevel) minlevel = level;
      if (level > maxlevel) maxlevel = level;
      c->used2 = 1;
      LOG (4, "level %d used in clause", level);
    } else if (c->used2 == 1) {
      c->used2 = 2;
      LOG (4, "level %d actually used (at least) twice in clause", level);
    }
  }
  if (maxlevel >= 0) {
    c = lgl->control.start + maxlevel;
    assert (c->used2);
    if (c->used2 > 1) {
      assert (c->used2 == 2);
      LOG (4, "maximum level %d used twice so no forced literal", maxlevel);
      jlevel = maxlevel;
      realglue = glue = -1;
      for (p = soc; p < eoc; p++) {
       level = lglevel (lgl, lit = *p);
       c = lgl->control.start + level;
       if (c->used2 || level == jlevel) {
         if (level >= lgl->alevel) realglue++;
         glue++;
       }
       c->used2 = 0;
      } 
      assert (realglue >= 0);
      assert (glue >= 0);
    } else {
      assert (c->used2 == 1);
      LOG (4, "maximum level %d used only once", maxlevel);
      realglue = glue = jlevel = level = forced = 0;
      for (p = soc; p < eoc; p++) {
       level = lglevel (lgl, lit = *p);
       c = lgl->control.start + level;
       if (level == maxlevel) {
         assert (c->used2 == 1);
         forced = lit;
       } else if (c->used2) {
         if (level > jlevel) jlevel = level;
         if (level >= lgl->alevel) realglue++;
         glue++;
       }
       c->used2 = 0;
      }
      assert (!jlevel || minlevel <= jlevel);
      assert (jlevel < maxlevel);
      assert (forced);
    }
  } else glue = realglue = jlevel = forced = minlevel = maxlevel = 0;

  for (p = soc; p < eoc; p++) {
    level = lglevel (lgl, lit = *p);
    assert (0 < level), assert (level <= lgl->level);
    c = lgl->control.start + level;
    if (c->used2) c->used2 = 0;
  }

  LOG (2, "%s minimum level %d", type, minlevel);
  LOG (2, "%s maximum level %d", type, maxlevel);
  LOG (2, "%s glue %d (real %d) covers %.0f%%", type, glue, realglue,
       (float)(jlevel ? lglpcnt (glue, (jlevel - minlevel) + 1) : 100.0));
  LOG (2, "%s jump level %d", type, jlevel);
  LOG (2, "%s forced %d", type, forced);

  if (glueptr) *glueptr = glue;
  if (realglueptr) *realglueptr = realglue;
  if (jlevelptr) *jlevelptr = jlevel;
  if (forcedptr) *forcedptr = forced;
}

static void lgldeco (LGL * lgl, int jlevel, int uip) {
  int * q, * r, lit, level, limlevel;
#ifndef NDEBUG
  int countabovejlevel = 0;
#endif
  Ctr * p;
  assert (lgl->opts->deco.val == 1);
  if (lgl->opts->deco1opt.val) {
    for (limlevel = jlevel; limlevel > 1; limlevel--) {
      p = lgl->control.start + limlevel;
      if (p->used > 1) break;
    }
  } else limlevel = jlevel;
  LOG (4,
    "singly-used level limit %d for deco clause",
    limlevel);
  for (q = r = lgl->clause.start; q < lgl->clause.top; q++) {
    if (!(lit = *q)) continue;
    level = lglevel (lgl, lit);
    assert (0 < level);
    if (level > jlevel) {
#ifndef NDEBUG
      assert (!countabovejlevel);      // only for UIP
      assert (lit == uip);
      countabovejlevel++;
#else
      (void) uip;
#endif
      continue;
    }
    p = lgl->control.start + level;
    assert (p->used >= 1);
    if (level > limlevel && p->used == 1) {
      LOG (4,
        "keep singly-used level %d literal %d in deco clause",
       level, lit);
      *r++ = lit;
    } else if (p->decision != -lit)
      LOG (4,
        "drop non-decision multi-used level %d literal %d in deco clause",
       level, lit);
  }
  lgl->clause.top = r;
  for (level = 1; level <= jlevel; level++) {
    p = lgl->control.start + level;
    assert (p < lgl->control.top);
    if (level > limlevel && p->used == 1) continue;
    lit = -p->decision;
    assert (lgldecision (lgl, lit));
    assert (lglevel (lgl, lit));
    assert (lglevel (lgl, lit) <= jlevel);
    lglpushstk (lgl, &lgl->clause, lit);
    LOG (4,
      "add level %d decision literal %d to deco clause",
      level, lit);
  }
}

/*------------------------------------------------------------------------*/

static const int64_t INT64MIN = LLONG_MIN;
static const int64_t INT64MAX = LLONG_MAX;

static int64_t lgleftshiftint64 (int64_t val, int shift) {
  int64_t res;
  assert (shift >= 0);
       if (val == INT64MIN) res = INT64MIN;
  else if (val == INT64MAX) res = INT64MAX;
  else if (val > (INT64MAX >> shift)) res = INT64MAX;
  else if (val < (INT64MIN >> shift)) res = INT64MIN;
  else res = (int64_t)(((uint64_t) val) << shift);
  assert (val < 0 || res >= val);
  assert (val > 0 || res <= val);
  return res;
}

static int64_t lglrightshiftint64 (int64_t val, int shift) {
  int64_t res;
  assert (shift >= 0);
       if (val == INT64MIN) res = INT64MIN;
  else if (val == INT64MAX) res = INT64MAX;
  else res = val >> shift;
  assert (val > 0 || res >= val);
  assert (val < 0 || res <= val);
  return res;
}

static int64_t lgladdint64 (int64_t a, int64_t b) {
  int64_t res;
       if (a == INT64MIN) res = INT64MIN;
  else if (b == INT64MIN) res = INT64MIN;
  else if (a == INT64MAX) res = INT64MAX;
  else if (b == INT64MAX) res = INT64MAX;
  else if (a >= 0 && b <= 0) res = a + b;
  else if (a <= 0 && b >= 0) res = a + b;
  else if (a < 0) {
    assert (b < 0);
    if (b < (INT64MIN - a)) res = INT64MIN;
    else res = a + b;
    assert (res <= a), assert (res <= b);
  } else {
    assert (a > 0), assert (b > 0);
    if (b > (INT64MAX - a)) res = INT64MAX;
    else res = a + b;
    assert (res >= a), assert (res >= b);
  }
  return res;
}

static int64_t lglsubint64 (int64_t a, int64_t b) {
  int64_t res;
  if (b == INT64MIN) res = INT64MIN;
  else res = lgladdint64 (a, -b);
  return res;
}

static int lglvalidint64 (int64_t a) {
  return a != INT64MIN && a != INT64MAX;
}

/*------------------------------------------------------------------------*/

static void lglinitema (LGL * lgl, EMA * ema, int shift) {
  assert (0 <= shift), assert (shift <= 32);
  ema->shift = shift;
  ema->count = 0;
  LOG (2, "initialized EMA shift %d", shift);
}

static void lglupdatema (LGL * lgl, EMA * ema, int64_t input, int left) {
  int64_t oldval, tmpval, newval, add, sub;
  const int shift = ema->count;
  oldval = ema->val;
  if (shift < ema->shift) ema->count++;
  assert (lglvalidint64 (oldval));
  if (!lglvalidint64 (input)) goto DONE;
  sub = lglrightshiftint64 (oldval, shift);
  if (!lglvalidint64 (sub)) goto DONE;
  tmpval = lglsubint64 (oldval, sub);
  if (!lglvalidint64 (tmpval)) goto DONE;
  if (left) add = lgleftshiftint64 (input, 32 - shift);
  else add = lglrightshiftint64 (input, shift);
  if (!lglvalidint64 (add)) goto DONE;
  newval = lgladdint64 (tmpval, add);
  if (!lglvalidint64 (newval)) goto DONE;
  ema->val = newval;
DONE:
#ifndef NLGLOG
  if (left)
    LOG (2,
      "EMA (left) input %lld old %g shift %d new %g",
      (LGLL) input,
      oldval/(double)(1ll<<32),
      ema->shift,
      ema->val/(double)(1ll<<32));
  else
    LOG (2,
      "EMA (right) input %g old %g shift %d new %g",
      input/(double)(1ll<<32),
      oldval/(double)(1ll<<32),
      ema->shift,
      ema->val/(double)(1ll<<32));
#else
  ;
#endif
}

#ifndef NLGLDEMA

static void lglinitdema (LGL * lgl, DEMA * dema, int shift) {
  lglinitema (lgl, &dema->ema[0], shift);
  lglinitema (lgl, &dema->ema[1], shift);
  LOG (2, "initialized DEMA shift %d", shift);
}

static void lglupdatedema (LGL * lgl, DEMA * dema, int input) {
#ifndef NLGLOG
  int64_t oldval = dema->val;
#endif
  int64_t newval, val0, val1;
  lglupdatema (lgl, &dema->ema[0], input, 1);
  if (!lglvalidint64 (val0 = dema->ema[0].val)) goto DONE;
  lglupdatema (lgl, &dema->ema[1], val0, 0);
  if (!lglvalidint64 (val1 = dema->ema[1].val)) goto DONE;
  newval = lglsubint64 (lgleftshiftint64 (val0, 1), val1);
  if (!newval) goto DONE;
  dema->val = newval;
DONE:
  LOG (2,
    "DEMA input %lld old %g shift %d new %g",
    (LGLL) input,
    oldval/(double)(1ll<<32),
    dema->ema[0].shift,
    dema->val/(double)(1ll<<32));
}

#endif

static void lglinitmacd (LGL * lgl, MACD * macd,
                         int fast, int slow, int smooth) {
  assert (0 <= fast), assert (fast <= 32);
  assert (0 <= slow), assert (slow <= 32);
  assert (0 <= smooth), assert (smooth <= 32);
  lglinitmacdema (lgl, &macd->fast, fast);
  lglinitmacdema (lgl, &macd->slow, slow);
  lglinitema (lgl, &macd->diff.smoothed, smooth);
  LOG (2, "initialized MACD fast %d slow %d smooth %d", fast, slow, smooth);
}

static void lglupdatemacd (LGL * lgl, MACD * macd, int64_t input) {
#if !defined(NDEBUG) || !defined(NLGLOG)
  int64_t oldactual = macd->diff.actual;
  int64_t oldsmoothed = macd->diff.smoothed.val;
#endif
  int64_t newactual;
  assert (lglvalidint64 (oldsmoothed));
  assert (lglvalidint64 (oldactual));
  lglupdatemacdema (lgl, &macd->fast, input);
  lglupdatemacdema (lgl, &macd->slow, input);
  newactual = lglsubint64 (macd->fast.val, macd->slow.val);
  if (!lglvalidint64 (newactual)) goto DONE;
  macd->diff.actual = newactual;
  lglupdatema (lgl, &macd->diff.smoothed, newactual, 0);
DONE:
  LOG (2,
"updated MACD input %lld actual/smoothed: old %g/%g, new %g/%g",
    (LGLL) input,
    oldactual/(double)(1ll<<32),
    oldsmoothed/(double)(1ll<<32),
    macd->diff.actual/(double)(1ll<<32),
    macd->diff.smoothed.val/(double)(1ll<<32));
}

static void lglupdstab (LGL * lgl) {
  int assigned = lglcntstk (&lgl->trail);
  int changed = lgl->stats->stability.changed;
  int topassigned = lglevel2trail (lgl, 1);
  int nontopassigned = assigned - topassigned;
  int64_t difference, shifted, fraction;
  lgl->stats->stability.count++;
  lglprt (lgl, 2,
    "[stability-%lld] %d assigned, %d non-top %.1f%%, %d changed %.2f%%",
    (LGLL) lgl->stats->stability.count,
    assigned,
    nontopassigned, lglpcnt (nontopassigned, assigned),
    changed, lglpcnt (changed, nontopassigned));
  assert (lgl->level > 0);
  assert (lgl->stats->stability.level > 0);
  assert (lgl->stats->stability.level <= lgl->level);
  assert (nontopassigned >= 0);
  if (!nontopassigned) fraction = 0;
  else {
    assert (nontopassigned >= changed);
    difference = nontopassigned - changed;
    shifted = difference << 32;
    fraction = shifted / nontopassigned;
  }
  lglupdatema (lgl, &lgl->stats->stability.avg, fraction, 0);
  lgl->stats->stability.level = 0;
  lglprt (lgl, 2,
    "[stability-%lld] unchanged fraction %.3f%% new stability %.3f%%",
    (LGLL) lgl->stats->stability.count,
    100.0 * fraction/(double)(1ll<<32),
    100.0 * lgl->stats->stability.avg.val / (double)(1ll<<32));
}

static void lglinitavg (AVG * avg) {
  avg->val = avg->count = 0;
}

static void lglupdateavg (LGL * lgl, AVG * avg, int input) {
  int64_t oldval = avg->val, newval = oldval, shifted, diff;
  shifted = lgleftshiftint64 (input, 32);
  if (!lglvalidint64 (shifted)) goto DONE;
  diff = lglsubint64 (shifted, oldval);
  if (!lglvalidint64 (diff)) goto DONE;
  diff /= ++avg->count;
  newval = lgladdint64 (oldval, diff);
  if (!lglvalidint64 (newval)) goto DONE;
  avg->val = newval;
DONE:
  LOG (2,
    "AVG input %d old %g new %g count %lld",
    input,
    oldval/(double)(1ll<<32),
    newval/(double)(1ll<<32),
    avg->count);
}

/*------------------------------------------------------------------------*/

static int lglblockrestart (LGL * lgl) {
  const int64_t   actual = ((int64_t)lglcntstk (&lgl->trail)) << 32;
  const int64_t smoothed = lgl->stats->tlevel.val;
  const int64_t  percent = lgl->opts->restartblocklim.val;
  int64_t limit;
  int blocking;
  if (lgl->stats->confs < lgl->limits->restart.confs) return 0;
  if (lgl->stats->confs < lgl->opts->restartblockbound.val) return 0;
  assert (percent);
  assert (lglvalidint64 (smoothed));
  limit = (smoothed < 0 ? -smoothed : smoothed);
  assert (limit >= 0);
  if (!lglvalidint64 (limit)) return 0;
  limit /= 100;
  if (INT64MAX/percent < limit) return 0;
  limit *= percent;
  blocking = (limit < actual);
  LOG (2,
    "%s restart MACD %g * %.2f = %g %s %g at %lld conflicts",
    (blocking ? "blocking" : "not blocking"),
    smoothed/(double)(1ll<<32),
    lgl->opts->restartblocklim.val/100.0,
    limit/(double)(1ll<<32),
    blocking ? "<" : ">=",
    actual/(double)(1ll<<32),
    (LGLL) lgl->stats->confs);
  return blocking;
}

static int lglana (LGL * lgl) {
  int open, resolved, tag, lit, uip, r0, r1, other, other2, * p, * q, lidx;
  int size, savedsize, resolventsize, level, red, glue, realglue;
  int jlevel, mlevel, nmlevel, origsize, redsize, tlevel;
  int64_t delta;
  int len, * rsn;
#ifdef RESOLVENT
  AVar * av;
#endif
  if (lgl->mt) return 0;
  if (lgl->failed) return 0;
  if (!lgl->conf.lit) return 1;
  if (!lgl->level) { lglmt (lgl); return 0; }
  lglstart (lgl, &lgl->times->analysis);
  if (lgl->sweeping) lgl->stats->sweep.confs++;
  else assert (!lgl->simp), lgl->stats->confs++;
RESTART:
  tlevel = lglcntstk (&lgl->trail);
  assert (lgl->conf.lit);
  assert (lglmtstk (&lgl->seen));
  assert (lglmtstk (&lgl->clause));
  assert (lglmtstk (&lgl->resolvent));
#ifndef NDEBUG
  if (lgl->opts->check.val > 0) lglchkclnvar (lgl);
#endif
  open = 0;
  lit = lgl->conf.lit, r0 = lgl->conf.rsn[0], r1 = lgl->conf.rsn[1];
  savedsize = resolved = 0;
  open += lglpull (lgl, lit);
  LOG (2, "starting analysis with reason of literal %d", lit);
  for (;;) {
    LOGREASON (2, lit, r0, r1, "analyzing");
    if (resolved++) {
#ifdef RESOLVENT
      if (lglmaintainresolvent (lgl)) {
	LOG (2, "removing %d from resolvent", -lit);
	lglrmstk (&lgl->resolvent, -lit);
	LOGRESOLVENT (3, "resolvent after removing %d is", -lit);
      }
#endif
    }
    assert (lglevel (lgl, lit) == lgl->level);
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      size = lglevel (lgl, other) ? 2 : 1;
      if (lglpull (lgl, other)) open++;
      if (tag == TRNCS) {
	if (lglevel (lgl, r1)) size++;
	if (lglpull (lgl, r1)) open++;
      }
    } else {
      assert (tag == LRGCS);
      red = r0 & REDCS;
      p = lglidx2lits (lgl, red, r1);
      size = 0;
      while ((other = *p++)) {
	if (lglevel (lgl, other)) size++;
	if (lglpull (lgl, other)) open++;
      }
      if (red) lglbumpnupdatelidx (lgl, r1);
    }
    LOG (3, "open %d antecendents %d learned %d resolved %d",
	 open-1, size, lglcntstk (&lgl->clause), lglcntstk (&lgl->resolvent));
    assert (open > 0);
    resolventsize = open + lglcntstk (&lgl->clause);
#ifdef RESOLVENT
    LOGRESOLVENT (2, "resolvent");
    if (lglmaintainresolvent (lgl))
      assert (lglcntstk (&lgl->resolvent) == resolventsize);
#endif
    if (lgl->opts->otfs.val &&
	(resolved >= 2) &&
	resolventsize > 1 &&
	(resolventsize < size || (resolved==2 && resolventsize<savedsize))) {
      int sl = 0, s0 = 0, s1 = 0, del;
      int cl = lgl->conf.lit;
      int c0 = lgl->conf.rsn[0];
      int c1 = lgl->conf.rsn[1];
      assert (resolved >= 2);
      del = lit;
      if (resolved > 2) ;
      else if (resolventsize >= size) del = -lit, lit = cl, r0 = c0, r1 = c1;
      else if (resolventsize >= savedsize) ;
      else {
	if (r0 & REDCS) {
	  sl = lit, s0 = r0, s1 = r1;
	  del = -lit, lit = cl, r0 = c0, r1 = c1;
	} else sl = cl, s0 = c0, s1 = c1;
      }
      lgldynstr (lgl, del, lit, r0, r1);
      if (sl) lgldynsub (lgl, sl, s0, s1);
      lit = lgl->conf.lit;
      r0 = lgl->conf.rsn[0];
      r1 = lgl->conf.rsn[1];
      assert (lglevel (lgl, lit) == lgl->level);
      tag = r0 & MASKCS;
      if (tag == UNITCS) {
	mlevel = lglevel (lgl, lit);
	nmlevel = 1;
	jlevel = 0;
      } else if (tag == BINCS) {
	jlevel = lglevel (lgl, lit);
	other = r0 >> RMSHFT;
	mlevel = lglevel (lgl, other);
	if (jlevel > mlevel) { nmlevel = 1; SWAP (int, mlevel, jlevel); }
	else if (jlevel == mlevel) nmlevel = 2;
	else assert (jlevel < mlevel), nmlevel = 1;
      } else if (tag== TRNCS) {
	jlevel = lglevel (lgl, lit);
	other = r0 >> RMSHFT;
	level = lglevel (lgl, other);
	other2 = r1;
	mlevel = lglevel (lgl, other2);
	if (jlevel > mlevel) SWAP (int, jlevel, mlevel);
	if (level > mlevel) SWAP (int, level, mlevel);
	if (level > jlevel) SWAP (int, level, jlevel);
	assert (mlevel >= jlevel);
	assert (jlevel >= level);
	if (mlevel == jlevel) nmlevel = 2 + (jlevel == level);
	else assert (mlevel > jlevel), nmlevel = 1;
	assert (nmlevel == 1 + (mlevel == jlevel) + (mlevel == level));
      } else {
	mlevel = lglevel (lgl, lit), nmlevel = 1, jlevel = 0;
	assert (tag == LRGCS);
	red = r0 & REDCS;
	p = lglidx2lits (lgl, red, r1);
	while (jlevel < lgl->level && (other = *p++)) {
	  if (other == lit) continue;
	  assert (other != -lit);
	  level = lglevel (lgl, other);
	  if (level < mlevel) {
	    if (level > jlevel) jlevel = level;
	    continue;
	  }
	  if (level == mlevel) nmlevel++;
	  else {
	    assert (level > mlevel);
	    jlevel = mlevel;
	    mlevel = level;
	    nmlevel = 1;
	  }
	}
	if (red) lglbumpnupdatelidx (lgl, r1);
      }
      if (nmlevel >= 2) {
	LOG (2, "restarting analysis after on-the-fly strengthening");
	lgl->stats->otfs.restarting++;
	lglclnana (lgl);
	if (lgl->level > mlevel) lglbacktrack (lgl, mlevel);
	goto RESTART;
      }
      assert (nmlevel == 1);
      assert (mlevel > jlevel);
      assert (lglevel (lgl, lit) == mlevel);
      LOGREASON (2, lit, r0, r1,
	"driving %d at level %d through strengthened", lit, jlevel);
      lgl->stats->otfs.driving++;
      lglbacktrack (lgl, jlevel);
      if (tag == LRGCS && (r0 & REDCS) && (r1 & GLUEMASK) == MAXGLUE) {
	// Note, that 'lit' is unassigned by 'backtrack' above and thus if
	// it's reason is at the end of the MAXGLUE stack, then the reason
	// becomes invalid.  See the corresponding 'assert' in 'lglassign'.
	// Our original incorrect fix to this problem was to simply increase
	// the size of the stack to point after the zero sentinel, which
	// however produces garbage on the MAXGLUE stack and thus we only
	// follow this idea if the reason of 'lit' is exactly after the
	// current end of the MAXGLUE stack. If it starts before the end
	// nothing has to be done.  Otherwise we have to move the reason
	// literals and update the reason.
	p = lglidx2lits (lgl, REDCS, r1);
	if (p > lgl->red[MAXGLUE].top) {
	  rsn = lglrsn (lgl, lit);
	  r1 = lglcntstk (&lgl->red[MAXGLUE]);
	  r1 <<= GLUESHFT;
	  r1 |= MAXGLUE;
	  rsn[1] = r1;
	  for (q = lgl->red[MAXGLUE].top; *p; p++) {
	    assert (q < p);
	    *q++ = *p;
	  }
	  *q++ = 0;
	  lgl->red[MAXGLUE].top = q;
	} else if (p == lgl->red[MAXGLUE].top) {
	  while (*p) { assert (*p < NOTALIT); p++; }
	  if (++p > lgl->red[MAXGLUE].top) lgl->red[MAXGLUE].top = p;
	}
      }
      lglassign (lgl, lit, r0, r1);
      len = INT_MAX;
      goto DONE;
    }
    savedsize = size;
    while (!lglmarked (lgl, lit = lglpopstk (&lgl->trail)))
      lglunassign (lgl, lit);
    lglunassign (lgl, lit);
    if (!--open) { uip = -lit; break; }
    LOG (2, "analyzing reason of literal %d next", lit);
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0], r1 = rsn[1];
  }
  assert (uip);
  LOG (2, "adding UIP %d at same level %d to 1st UIP clause",
       uip, lgl->level);
  lglpushstk (lgl, &lgl->clause, uip);
  assert (lglmarked (lgl, uip));
#ifdef RESOLVENT
  LOGRESOLVENT (3, "final resolvent before flushing fixed literals");
  if (lglmaintainresolvent  (lgl)) {
    int * q = lgl->resolvent.start;
    for (p = q; p < lgl->resolvent.top; p++)
      if (lglevel (lgl, (other = *p)))
	*q++ = other;
    lgl->resolvent.top = q;
    LOGRESOLVENT (2, "final resolvent after flushing fixed literals");
    assert (lglcntstk (&lgl->resolvent) == lglcntstk (&lgl->clause));
    for (p = lgl->clause.start; p < lgl->clause.top; p++)
      assert (lglavar (lgl, *p)->mark > 0);
    for (p = lgl->resolvent.start; p < lgl->resolvent.top; p++) {
      av = lglavar (lgl, *p); assert (av->mark > 0); av->mark = -av->mark;
    }
    for (p = lgl->clause.start; p < lgl->clause.top; p++)
      assert (lglavar (lgl, *p)->mark < 0);
    for (p = lgl->resolvent.start; p < lgl->resolvent.top; p++) {
      av = lglavar (lgl, *p); assert (av->mark < 0); av->mark = -av->mark;
    }
    lglclnstk (&lgl->resolvent);
  }
#endif
  lglpushstk (lgl, &lgl->clause, 0);
  LOGCLS (2, lgl->clause.start, "1st UIP clause");

  lgldrive (lgl, "preliminary", 0, &glue, 0, &jlevel);
  assert (glue == lglcntstk (&lgl->frames));

  origsize = lglcntstk (&lgl->clause) - 1;
  assert (glue + 1 <= origsize);
  lglbumpseenlits (lgl);
  lgl->stats->lits.nonmin += origsize;
  redsize = jlevel + 1;
  if (origsize == 2) {
    lgl->stats->mincls.bin++;
    LOGCLS (2, lgl->clause.start, "binary 1st UIP clause not minimized");
  } else if (glue + 1 == origsize) {
    lgl->stats->mincls.size++;
    LOGCLS (2, lgl->clause.start,
      "size %d 1st UIP clause with glue %d can not be minimized",
      origsize, glue);
  } else if (jlevel > 1 &&
      lgl->opts->deco.val &&
      redsize < 2*origsize/3 &&
      glue > lgl->opts->decolim.val) {
    assert (origsize > 2);
    lgl->stats->mincls.deco++;
    lgl->stats->deco.sum.orig += origsize;
    lgldeco (lgl, jlevel, uip);
    lglpushstk (lgl, &lgl->clause, uip);
    lgl->stats->deco.sum.red += lglcntstk (&lgl->clause);
    lglpushstk (lgl, &lgl->clause, 0);
    LOGCLS (2, lgl->clause.start,
      "size %d 1st UIP clause discarded for size %d decision-only clause",
      origsize, redsize);
  } else {
    lglmincls (lgl, uip, glue);
    lglredcls (lgl, uip, glue, &jlevel);
  }

  lgldrive (lgl, "final", &uip, &glue, &realglue, &jlevel);

  if (uip && lglrsn (lgl, uip)[0]) lgl->stats->uips++;
  else if (jlevel + 1 == lgl->level) lgl->stats->decflipped++;

  lglbumpscinc (lgl);

  lglbacktrack (lgl, jlevel);

  len = lglcntstk (&lgl->clause) - 1;
  lgl->stats->clauses.glue += glue;
  lgl->stats->clauses.realglue += realglue;
  lgl->stats->lits.learned += len;
  lgl->stats->clauses.learned++;

  if (!lgl->simp) {
    LOG (2, "updating AVG glue");
    lglupdateavg (lgl, &lgl->stats->avglue, realglue);
    LOG (2, "updating MACD restart glue");
    lglupdatemacd (lgl, &lgl->stats->glue, realglue);
    LOG (2, "updating MACD jump level");
    lglupdatemacd (lgl, &lgl->stats->jlevel, jlevel);
    LOG (2, "updating EMA trail level");
    lglupdatema (lgl, &lgl->stats->tlevel, tlevel, 1);
    if (lgl->opts->restartblock.val == 1 && lglblockrestart (lgl)) {
      lgl->limits->restart.confs =
        lgl->stats->confs + lgl->opts->restartint.val;
      lgl->stats->restarts.blocked++;
    }
#ifndef NLGLFILES
    {
      static FILE * macdfile = 0;
      if (!macdfile) macdfile = fopen ("/tmp/macd", "w");
      fprintf (macdfile,
       "%lld %d"
       " %g %g %g %g"
       " %g %g %g %g"
       " %g %g"
       " %d %d"
       " %g"
       "\n",
       (LGLL) lgl->stats->confs,
       realglue,

       lgl->stats->glue.fast.val/(double)(1ll<<32),
       (!lgl->opts->restartforcemode.val ?
	 lgl->stats->avglue.val :
	 lgl->stats->glue.slow.val) /(double)(1ll<<32),
       lgl->stats->glue.diff.actual/(double)(1ll<<32),
       lgl->stats->glue.diff.smoothed.val/(double)(1ll<<32),

       lgl->stats->jlevel.fast.val/(double)(1ll<<32),
       lgl->stats->jlevel.slow.val/(double)(1ll<<32),
       lgl->stats->jlevel.diff.actual/(double)(1ll<<32),
       lgl->stats->jlevel.diff.smoothed.val/(double)(1ll<<32),

       100.0 * (lgl->stats->agility/(double)(1ll<<32)),
       100.0 * lgl->stats->stability.avg.val/(double)(1ll<<32),

       jlevel,
       tlevel,

       lgl->stats->tlevel.val/(double)(1ll<<32)

       );

      fflush (macdfile);
    }
#endif
  }

  lgldrupligaddcls (lgl, REDCS);
  lidx = lgladdcls (lgl, REDCS, realglue, 1);

#ifndef NDEBUG
  if (!lglmtstk (&lgl->prevclause)) {
    for (p = lgl->prevclause.start, q = lgl->clause.start; *p; p++, q++)
      if (*p != *q) break;
    assert (*q != *p);
  }
  lglclnstk (&lgl->prevclause);
  for (p = lgl->clause.start; *p; p++)
    lglpushstk (lgl, &lgl->prevclause, *p);
  lglpushstk (lgl, &lgl->prevclause, 0);
  lgl->prevglue = lglscaleglue (lgl, realglue);
#endif
  if (lgl->opts->subl.val) {
    lglstart (lgl, &lgl->times->subl);
    lgl->stats->subl.count++;
    lglpopnunmarkstk (lgl, &lgl->seen);
    size = lglcntstk (&lgl->clause) - 1;
    if (size > 1) {
      unsigned sig = 0;
      p = lgl->clause.start;
      while ((lit = *p++)) {
       sig |= (1u << (lglulit (lit) & 31));
       lglmark (lgl, lit);
      }
      q = lgl->learned.start;
      for (p = q; p < lgl->learned.top; p += 3) {
       int olidx = p[0], osize = p[1];
       unsigned osig = (unsigned) p[2];
       if (olidx < 0) continue;
       if (osize <= size ||
           (sig & ~osig) ||
           !lglsubl (lgl, olidx, size, glue))
         *q++ = olidx, *q++ = osize, *q++ = (int) osig;
      }
      lgl->learned.top = q;
      if (lidx && (lidx & GLUEMASK) < MAXGLUE) {
       lgl->stats->subl.cands++;
       lglpushstk (lgl, &lgl->learned, lidx);
       lglpushstk (lgl, &lgl->learned, size);
       lglpushstk (lgl, &lgl->learned, (int) sig);
       if (lglcntstk (&lgl->learned) / 3 > lgl->opts->subl.val) {
         q = lgl->learned.start;
         for (p = q + 3; p < lgl->learned.top; p++) *q++ = *p;
         lgl->learned.top = q;
       }
      } 
      p = lgl->clause.start;
      while ((lit = *p++)) lglunmark (lgl, lit);
    }
    lglstop (lgl);
  }

  if (lgl->cbs &&
      lgl->cbs->cls.produce.fun &&
      glue <= lgl->opts->synclsglue.val &&
      lglcntstk (&lgl->clause) - 1 <= lgl->opts->synclslen.val) {
    assert (lglmtstk (&lgl->eclause));
    for (p = lgl->clause.start; *p; p++)
      lglpushstk (lgl, &lgl->eclause, lglexport (lgl, *p));
    lglpushstk (lgl, &lgl->eclause, 0);
    LOGCLS (2, lgl->eclause.start,
      "exporting external redundant glue %d length %d clause", 
      glue, lglcntstk (&lgl->clause) -1);
    lgl->stats->sync.cls.produced++;
    lgl->cbs->cls.produce.fun (lgl->cbs->cls.produce.state,
                               lgl->eclause.start, glue);
    lglclnstk (&lgl->eclause);
  }

DONE:

  if (lgl->simp) goto SKIPNOSIMP;

  if (len == 2) {
    lglrep (lgl, 2, 'b');
    lgl->stats->bins++;
  }

  if (len == 3) {
    lglrep (lgl, 2, 't');
    lgl->stats->trns++;
  }

  delta = lgl->stats->confs - lgl->confatlastit;
  LOG (1, "iteration delta %d", delta);
  lglupdatemacd (lgl, &lgl->stats->its.avg, delta);
  if (len == 1) {
    int delay = lgl->opts->simpitdelay.val;
    lgl->confatlastit = lgl->stats->confs;
    lgl->stats->its.count++;
    lglrep (lgl, 1, 'i');
    if (delta > 0) delay /= delta;
    if (delay > 0) {
      lgl->limits->simp.confs += delay;
      LOG (1, "delaying simplification by %d conflicts", delay);
    }
  }
  LOG (1, "iteration interval average %.0f", lglitavg (lgl));

SKIPNOSIMP:

  lglclnana (lgl);
  lglstop (lgl);

  return 1;
}

static void lglincrestart (LGL * lgl) {
  Stats * s = lgl->stats;
  int64_t delta;
  int pen = 0;
  delta = lgl->opts->restartint.val;
  if (lgl->opts->restartfixed.val) goto NOPEN;
  LOG (2, "initial next restarting delta %lld", (LGLL) delta);
  if (lgl->opts->restartpen1.val && s->confs > 500000 &&
      (!s->its.count || s->confs/s->its.count > 100000)) {
    lglprt (lgl, 2,
      "[restart-%lld] few iterations after 500000 conflicts",
      (LGLL) lgl->stats->restarts.count);
    pen++;
  }
  if (lgl->opts->restartpen2.val && s->confs > 50000 &&
      (!s->bins || s->confs/s->bins > 10000)) {
    lglprt (lgl, 2,
      "[restart-%lld] few binaries after 50000 conflicts",
      (LGLL) lgl->stats->restarts.count);
    pen++;
  }
  if (lgl->opts->restartpen3.val && s->confs > 5000 &&
      (!s->trns || s->confs/s->trns > 1000)) {
    lglprt (lgl, 2,
      "[restart-%lld] few ternaries after 5000 conflicts",
      (LGLL) lgl->stats->restarts.count);
    pen++;
  }
  if (lgl->opts->restartpenstab.val && s->confs > 50000) {
    int64_t glue = (s->glue.slow.val >> 32);
    if (glue < 20) {
      int64_t stab = s->stability.avg.val;
      int peninc = 0;
      assert (stab <= (1ll << 32));
      stab *= 100000;
      stab >>= 32;
      if (stab > 98000) peninc++;
      if (stab > 99000) peninc++;
      if (stab > 99500) peninc++;
      if (stab > 99750) peninc++;
      if (stab > 99875) peninc++;
      pen += peninc;
      lglprt (lgl, 2,
	"[restart-%lld] "
	"stability %lld glue %d after 50000 conflicts (penalty increase %d)",
	(LGLL) lgl->stats->restarts.count, stab, glue, peninc);
    }
  }
NOPEN:
  delta <<= pen;
  lgl->stats->restarts.delta.pen += pen;
  lgl->stats->restarts.delta.delta += delta;
  lgl->stats->restarts.delta.count++;
  lgl->limits->restart.confs = lgl->stats->confs + delta;
  lglprt (lgl, 2,
    "[restart-%lld] next restart %lld delta %lld (penalty %d)",
    (LGLL) lgl->stats->restarts.count,
    (LGLL) lgl->limits->restart.confs, (LGLL) delta, pen);
  lglrep (lgl, 2, 'R');
}

static void lglqueueflush (LGL * lgl) {
  int before, mt, after, nonfree;
  const int * p, * start;
  int * q, lit, found;
  QVar * qv;
  lgl->stats->queue.flushed++;
  found = nonfree = mt = 0;
  before = lglcntstk (&lgl->queue.stk);
  assert (lgl->mt <= before);
  start = q = lgl->queue.stk.start;
  for (p = q; p < lgl->queue.stk.top; p++) {
    if (!(lit = *p)) {
      mt++;
      continue;
    }
    qv = lglqvar (lgl, lit);
    assert (qv->enqueued);
    assert (qv->pos == (p - start));
    if (!lglisfree (lgl, lit)) {
      qv->enqueued = 0;
      qv->pos = -1;
      nonfree++;
    } else {
      qv->pos = (q - start);
      if (!found && lgl->queue.next >= (p - start))
	found = 1, lgl->queue.next = qv->pos;
      *q++ = lit;
    }
  }
  lgl->queue.stk.top = q;
  if (!found) lgl->queue.next = lglcntstk (&lgl->queue.stk) - 1;
  assert (mt == lgl->queue.mt);
  lgl->queue.mt = 0;
  after = lglcntstk (&lgl->queue.stk);
  assert (before == after + nonfree + mt);
  lglprt (lgl, 2,
    "[flush-queue-%d] flushed %d = %d mt + %d nonfree (resized %d to %d)",
    lgl->stats->queue.flushed, mt + nonfree, mt, nonfree, before, after);
}

static int lglnextdecision (LGL * lgl, int updatestats) {
  int res = 0;
#ifndef NDEBUG
  int start;
#endif
  QVar * qv;
  if (!lgl->unassigned) return 0;
  lglstart (lgl, &lgl->times->decide);
  lglstart (lgl, &lgl->times->heapdecision);
  while (!res && !lglmtstk (&lgl->dsched)) {
    int next = lgltopdsched (lgl);
    if (!lglval (lgl, next) && lglisfree (lgl, next)) res = next;
    else lglpopdsched (lgl);
  }
  lglstop (lgl);
  if (!res) {
    lglstart (lgl, &lgl->times->queuedecision);
    assert (!lglmtstk (&lgl->queue.stk));
    if (lglcntstk (&lgl->queue.stk) < 2*lgl->queue.mt) lglqueueflush (lgl);
#ifndef NDEBUG
    start = lgl->queue.next;
#endif
    for (;;) {
      res = lglpeek (&lgl->queue.stk, lgl->queue.next);
      if (res) {
	qv = lglqvar (lgl, res);
	assert (qv->enqueued);
	assert (qv->pos == lgl->queue.next);
	if (!lglisfree (lgl, res)) {
	  lglpoke (&lgl->queue.stk, lgl->queue.next, 0);
	  lgl->queue.mt++;
	  qv->enqueued = 0;
	  qv->pos = -1;
	} else if (!lglval (lgl, res)) {
	  if (updatestats) lgl->stats->qdecs++;
	  break;
	}
      }
      lgl->queue.next--;
      if (lgl->queue.next < 0)
	lgl->queue.next = lglcntstk (&lgl->queue.stk) - 1;
      ASSERT (lgl->queue.next != start);
    }
    lglstop (lgl);
  } else if (updatestats) lgl->stats->hdecs++;
  assert (res);
  lglstop (lgl);
  LOG (2, "next decision would be %d", res);
  return res;
}

static int lglreusetrail (LGL * lgl) {
  int next = 0, res = 0, prev, level;
  const Ctr * p;
  if (!lgl->opts->reusetrail.val) return 0;
  if (!(next = lglnextdecision (lgl, 0))) return 0;
  for (p = lgl->control.start + 1; p < lgl->control.top; p++) {
    prev = p->decision;
    assert (lgldecision (lgl, prev));
    if (!lglassumption (lgl, prev) && lgldcmp (lgl, prev, next) < 0) break;
    level = lglevel (lgl, prev);
    assert (level == p - lgl->control.start);
    assert (res + 1 == level);
    res = level;
  }
  if (res)
    lglprt (lgl, 3,
      "[reuse-trail] reusing level %d from current level %d",
      res, lgl->level);
  else
    lglprt (lgl, 3,
      "[reuse-trail] can not reuse any level from current level %d",
      lgl->level);
  return res;
}

static void lglrestart (LGL * lgl) {
  int level, kept;
  assert (lgl->opts->restart.val);
  lglstart (lgl, &lgl->times->restart);
  level = lglreusetrail (lgl);
  if (level < lgl->alevel) level = lgl->alevel;
  else if (level > lgl->alevel) {
    kept = (100*level) / lgl->level;
    lgl->stats->restarts.kept.sum += kept;
    lgl->stats->restarts.kept.count++;
  }
  if (level < lgl->level) {
    int oldlevel = lgl->level;
    lglbacktrack (lgl, level);
    LOG (2, "setting stability level to %d", oldlevel);
    lgl->stats->stability.level = oldlevel;
    assert (lgl->stats->stability.level > 0);
    lgl->stats->stability.changed = 0;
    lgl->stats->restarts.count++;
  } else {
    lgl->stats->restarts.reused++;
    lgl->stats->restarts.skipped++;
  }
  lglincrestart (lgl);
  lglstop (lgl);
}

static void lgldefrag (LGL * lgl) {
  int * wchs, nwchs, i, idx, bit, ldsize, size, offset, * start, * q, * end;
  const int * p, * eow, * w;
  HTS * hts;
  lglstart (lgl, &lgl->times->defrag);
  lgl->stats->defrags++;
  nwchs = lglcntstk (&lgl->wchs->stk);
  NEW (wchs, nwchs);
  memcpy (wchs, lgl->wchs->stk.start, nwchs * sizeof *wchs);
  for (i = 0; i < MAXLDFW; i++) lgl->wchs->start[i] = INT_MAX;
  lgl->wchs->free = 0;
  start = lgl->wchs->stk.start;
  assert (nwchs >= 1);
  assert (start[0] == INT_MAX);
  offset = 1;
  for (idx = 2; idx < lgl->nvars; idx++)
  for (bit = 0; bit <= 1; bit++) {
    hts = lgl->dvars[idx].hts + bit;
    if (!hts->offset) { assert (!hts->count); continue; }
    ldsize = lglceild (hts->count);
    size = (1 << ldsize);
    assert (size >= hts->count);
    w = wchs + hts->offset;
    hts->offset = offset;
    eow = w + hts->count;
    q = start + offset;
    for (p = w; p < eow; p++) *q++ = *p;
    offset += size;
    end = start + offset;
    while (q < end) *q++ = 0;
  }
  DEL (wchs, nwchs);
  q = start + offset;
  *q++ = INT_MAX;
  assert (q <= lgl->wchs->stk.top);
  lgl->wchs->stk.top = q;
  lglfitstk (lgl, &lgl->wchs->stk);
  lgl->limits->dfg = lgl->stats->pshwchs + lgl->opts->defragint.val;
  lglrep (lgl, 2, 'F');
  lglstop (lgl);
}

static void lgldis (LGL * lgl) {
  int blit, nblit, tag, red, * p, * q, * eow, * w;
  int idx, sign, lit, other, other2;
  Stk bins, trns;
  Val val, val2;
  HTS * hts;
  assert (!lgl->level);
  CLR (bins); CLR (trns);
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = idx * sign;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      val = lglval (lgl, lit);
      assert (hts->count > 0);
      if (lgl->mt || val || lgliselim (lgl, lit)) {
	lglshrinkhts (lgl, hts, 0);
	continue;
      }
      assert (lglisfree (lgl, lit));
      assert (lglmtstk (&bins));
      assert (lglmtstk (&trns));
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == OCCS) continue;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	other = blit >> RMSHFT;
	val = lglval (lgl, other);
	if (val > 0) continue;
	if (lgliselim (lgl, other)) continue;
	if (tag == BINCS) {
	  assert (!val);
	  lglpushstk (lgl, &bins, blit);
	  continue;
	}
	assert (tag == TRNCS);
	other2 = *p;
	val2 = lglval (lgl, other2);
	if (val2 > 0) continue;
	if (lgliselim (lgl, other2)) continue;
	if (val < 0) {
	  assert (val < 0 && !val2);
	  nblit = red | RMSHFTLIT (other2) | BINCS;
	  lglpushstk (lgl, &bins, nblit);
	  if (abs (lit) < abs (other2)) {
	    lgldrupligaddclsarg (lgl, REDCS, lit, other2, 0);
	    lgldrupligdelclsarg (lgl, lit, other, other2, 0);
	  }
	  continue;
	}
	if (val2 < 0) {
	  assert (!val && val2 < 0);
	  nblit = red | RMSHFTLIT (other) | BINCS;
	  lglpushstk (lgl, &bins, nblit);
	  if (abs (lit) < abs (other)) {
	    lgldrupligaddclsarg (lgl, REDCS, lit, other, 0);
	    lgldrupligdelclsarg (lgl, lit, other, other2, 0);
	  }
	  continue;
	}
	assert (!val && !val2);
	lglpushstk (lgl, &trns, blit);
	lglpushstk (lgl, &trns, other2);
      }
      q = w;
      for (p = bins.start; p != bins.top; p++) *q++ = *p;
      for (p = trns.start; p != trns.top; p++) *q++ = *p;
      lglshrinkhts (lgl, hts, q - w);
      lglclnstk (&bins);
      lglclnstk (&trns);
    }
  lglrelstk (lgl, &bins);
  lglrelstk (lgl, &trns);
  lglrelstk (lgl, &lgl->learned);
}

static int lglcmphase (LGL * lgl, int a, int b) {
  return lgliphase (lgl, b) - lgliphase (lgl, a);
}

#define LGLCMPHASE(A,B) lglcmphase (lgl, *(A), *(B))

static void lglconnaux (LGL * lgl, int glue) {
  int lit, collect, lidx, size, origsize, red, act;
  const int druplig = lgl->opts->druplig.val;
  const int * p, * c, * start, * top;
  Stk * stk, saved;
  int * q, * d;
  Val val;
  if (glue >= 0) {
    assert (glue < MAXGLUE);
    red = REDCS;
    stk = lgl->red + glue;
  } else red = 0, stk = &lgl->irr;
  start = q = stk->start;
  top = stk->top;
  CLR (saved);
  for (c = q; c < top; c = p + 1) {
    act = *c;
    if (act == REMOVED) {
      for (p = c + 1; p < top && *p == REMOVED; p++)
	;
      assert (p >= top || *p < NOTALIT || lglisact (*p));
      p--;
      continue;
    }
    if (lglisact (act)) assert (glue >= 0), *q++ = *c++;
    else assert (glue < 0), act = -1;
    d = q;
    collect = 0;
    lglclnstk (&saved);
    for (p = c; assert (p < top), (lit = *p); p++) {
      assert (lit < NOTALIT);
      if (druplig) lglpushstk (lgl, &saved, lit);
      if (collect) continue;
      val = lglval (lgl, lit);
      if (lgliselim (lgl, lit)) {
	assert (lgl->eliminating || lgl->blocking);
	collect = 1;
      } else if (val > 0) collect = 1;
      else if (!val) *q++ = lit;
    }

    size = q - d;
    origsize = p - c;
    assert (!druplig || origsize == lglcntstk (&saved));
    assert (size <= origsize);

    if (druplig && !collect && size > 1 && size < origsize)
      *q = 0, lgldrupligaddclsaux (lgl, REDCS, d);

    if (collect || p == c + 1) {
      q = d - (act >= 0);
    } else if (!size) {
      q = d - (act >= 0);
      if (!lgl->mt) {
	LOG (1, "empty clause during connection garbage collection phase");
	lglmt (lgl);
      }
    } else if (size == 1) {
      q = d - (act >= 0);
      LOG (1, "unit during garbage collection");
      lglunit (lgl, d[0]);
    } else if (size == 2) {
      q = d - (act >= 0);
      lglwchbin (lgl, d[0], d[1], red);
      lglwchbin (lgl, d[1], d[0], red);
    } else if (size == 3) {
      q = d - (act >= 0);
      lglwchtrn (lgl, d[0], d[1], d[2], red);
      lglwchtrn (lgl, d[1], d[0], d[2], red);
      lglwchtrn (lgl, d[2], d[0], d[1], red);
    } else {
      assert (size > 3);
      if (lgl->opts->sortlits.val) SORT (int, d, size, LGLCMPHASE);
      *q++ = 0;
      lidx = d - start;
      if (red) {
	assert (lidx <= MAXREDLIDX);
	lidx <<= GLUESHFT;
	assert (0 <= lidx);
	lidx |= glue;
      }
      (void) lglwchlrg (lgl, d[0], d[1], red, lidx);
      (void) lglwchlrg (lgl, d[1], d[0], red, lidx);
    }
    if (druplig && (collect || origsize != size)) {
      lglpushstk (lgl, &saved, 0);
      lgldrupligdelclsaux (lgl, saved.start);
    }
  }
  stk->top = q;
  lglrelstk (lgl, &saved);
}

static void lglconsavedbin (LGL * lgl) {
  int satisfied, eliminated, size, val0, val1, nunits = 0, nmt = 0;
  const int druplig = lgl->opts->druplig.val, * p;
  assert (lgl->rmredbintrn);
  for (p = lgl->saved.bin.start; p < lgl->saved.bin.top; p += 2) {
    assert (p + 1 < lgl->saved.bin.top);
    satisfied = eliminated = val0 = val1 = 0;
         if ((val0 = lglval (lgl, p[0])) > 0) satisfied = 1;
    else if ((val1 = lglval (lgl, p[1])) > 0) satisfied = 1;
    else if (lgliselim (lgl, p[0])) eliminated = 1;
    else if (lgliselim (lgl, p[1])) eliminated = 1;
    assert (!eliminated || lgl->eliminating || lgl->blocking);
    if (satisfied || eliminated) size = INT_MAX;
    else if (val0 < 0 && val1 < 0) {
      nmt++;
      size = 0;
      if (!lgl->mt) {
	LOG (1, "empty clause connecting saved binary clauses");
	lglmt (lgl);
      }
    } else if (!val0 && val1 < 0) {
      size = 1;
      LOG (1, "unit during connecting saved binary clauses");
      lglunit (lgl, p[0]);
      nunits++;
    } else if (val0 < 0 && !val1) {
      size = 1;
      LOG (1, "unit during connecting saved binary clauses");
      lglunit (lgl, p[1]);
      nunits++;
    } else {
      assert (!val0), assert (!val1);
      size = 2;
      lglwchbin (lgl, p[0], p[1], REDCS);
      lglwchbin (lgl, p[1], p[0], REDCS);
    }
    if (druplig && (satisfied || eliminated || size < 2))
      lgldrupligdelclsarg (lgl, p[0], p[1], 0);
  }
  lglprt (lgl, 
    2 - (nmt || nunits),
    "[gc-%d] reconnected %d binary clauses (produced %d empty %d units)",
    lgl->stats->gcs, lglcntstk (&lgl->saved.bin)/2, nmt, nunits);
  lglrelstk (lgl, &lgl->saved.bin);
}

static void lglconsavedtrn (LGL * lgl) {
  const int druplig = lgl->opts->druplig.val, * p;
  int satisfied, eliminated, size, val0, val1, val2;
  int nmt = 0, nunits = 0, nbins = 0;
  assert (lgl->rmredbintrn);
  for (p = lgl->saved.trn.start; p < lgl->saved.trn.top; p += 3) {
    assert (p + 1 < lgl->saved.trn.top);
    satisfied = eliminated = val0 = val1 = val2 = 0;
         if ((val0 = lglval (lgl, p[0])) > 0) satisfied = 1;
    else if ((val1 = lglval (lgl, p[1])) > 0) satisfied = 1;
    else if ((val2 = lglval (lgl, p[2])) > 0) satisfied = 1;
    else if (lgliselim (lgl, p[0])) eliminated = 1;
    else if (lgliselim (lgl, p[1])) eliminated = 1;
    else if (lgliselim (lgl, p[2])) eliminated = 1;
    assert (!eliminated || lgl->eliminating || lgl->blocking);
    if (satisfied || eliminated) size = INT_MAX;
    else if (val0 < 0 && val1 < 0 && val2 < 0) {
      nmt++;
      size = 0;
      if (!lgl->mt) {
	LOG (1, "empty clause connecting saved ternary clauses");
	lglmt (lgl);
      }
    } else if (!val0 && val1 < 0 && val2 < 0) {
      size = 1;
      LOG (1, "unit during connecing saved ternary clauses");
      lglunit (lgl, p[0]);
      nunits++;
    } else if (val0 < 0 && !val1 && val2 < 0) {
      size = 1;
      LOG (1, "unit during connecing saved ternary clauses");
      lglunit (lgl, p[1]);
      nunits++;
    } else if (val0 < 0 && val1 < 0 && !val2) {
      size = 1;
      LOG (1, "unit during connecing saved ternary clauses");
      lglunit (lgl, p[2]);
      nunits++;
    } else if (!val0 && !val1 && val2 < 0) {
      size = 2;
      nbins++;
      lglwchbin (lgl, p[0], p[1], REDCS);
      lglwchbin (lgl, p[1], p[0], REDCS);
      if (druplig) lgldrupligaddclsarg (lgl, REDCS, p[0], p[1], 0);
    } else if (!val0 && val1 < 0 && !val2) {
      size = 2;
      nbins++;
      lglwchbin (lgl, p[0], p[2], REDCS);
      lglwchbin (lgl, p[2], p[0], REDCS);
      if (druplig) lgldrupligaddclsarg (lgl, REDCS, p[0], p[2], 0);
    } else if (val0 < 0 && !val1 && !val2) {
      size = 2;
      nbins++;
      lglwchbin (lgl, p[1], p[2], REDCS);
      lglwchbin (lgl, p[2], p[1], REDCS);
      if (druplig) lgldrupligaddclsarg (lgl, REDCS, p[1], p[2], 0);
    } else {
      size = 3;
      assert (!val0), assert (!val1), assert (!val2);
      lglwchtrn (lgl, p[0], p[1], p[2], REDCS);
      lglwchtrn (lgl, p[1], p[0], p[2], REDCS);
      lglwchtrn (lgl, p[2], p[0], p[1], REDCS);
    }
    if (druplig && (satisfied || eliminated || size < 3))
      lgldrupligdelclsarg (lgl, p[0], p[1], p[2], 0);
  }
  lglprt (lgl, 
    2 - (nmt || nunits), // || nbins), // NOTE would be too verbose ...
    "[gc-%d] reconnected %d ternary clauses "
    " (produced %d empty %d units %d binary)",
    lgl->stats->gcs, lglcntstk (&lgl->saved.trn)/3, nmt, nunits, nbins);
  lglrelstk (lgl, &lgl->saved.trn);
}

static void lglfullyconnected (LGL * lgl) {
  if (!lgl->notfullyconnected) return;
  LOG (1, "switching to fully connected mode");
  lgl->notfullyconnected  = 0;
}

static void lglcon (LGL * lgl) {
  int glue;
  for (glue = -1; glue < MAXGLUE; glue++) lglconnaux (lgl, glue);
  lglfullyconnected (lgl);
}

static void lglconsaved (LGL * lgl) {
  if (lgl->rmredbintrn) {
    lglconsavedbin (lgl);
    lglconsavedtrn (lgl);
    lgl->rmredbintrn = 0;
    if (!lgl->mt && !lglbcpcomplete (lgl)) {
      lglfullyconnected (lgl);
      if (!lglbcp (lgl)) {
	LOG (1, "empty clause generated propagating reconnected unit");
	lglmt (lgl);
      }
    }
  } else
    assert (lglmtstk (&lgl->saved.bin)),
    assert (lglmtstk (&lgl->saved.trn));
}

static void lglcount (LGL * lgl) {
  int idx, sign, lit, tag, blit, red, other, other2, glue, count;
  const int * p, * w, * c, * eow;
  HTS * hts;
  Stk * lir;
  lgl->stats->irr.clauses.cur = 0;
  lgl->stats->irr.lits.cur = 0;
  lgl->stats->red.bin = 0;
  lgl->stats->red.trn = 0;
  lgl->stats->red.lrg = 0;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	red = blit & REDCS;
	tag = blit & MASKCS;
	if (tag == LRGCS || tag == TRNCS) p++;
	if (tag == LRGCS) continue;
	assert (tag == BINCS || tag == TRNCS);
	other = blit >> RMSHFT;
	assert (abs (other) != abs (lit));
	if (abs (lit) >= abs (other)) continue;
	assert (2 == BINCS && 3 == TRNCS);
	if (tag == TRNCS) {
	  other2 = *p;
	  assert (abs (other2) != abs (lit));
	  assert (abs (other2) != abs (other));
	  if (abs (lit) >= abs (other2)) continue;
	}
	if (!red) {
	  lgl->stats->irr.clauses.cur++;
	  if (tag == BINCS) lgl->stats->irr.lits.cur += 2;
	  else assert (tag == TRNCS), lgl->stats->irr.lits.cur += 3;
	} else if (tag == BINCS) lgl->stats->red.bin++;
	else assert (tag == TRNCS), lgl->stats->red.trn++;
      }
    }
  assert (lgl->stats->red.bin >= 0 && lgl->stats->red.trn >= 0);
  for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
    if (*(p = c) >= REMOVED) continue;
    while (*p) p++;
    lgl->stats->irr.lits.cur += p - c;
    lgl->stats->irr.clauses.cur++;
  }
  LOG (1, "counted %d irredundant clauses with %d literals",
       lgl->stats->irr.clauses.cur, lgl->stats->irr.lits.cur);
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    count = 0;
    for (c = lir->start; c < lir->top; c++)
      if (!*c) count++;
    if (count)
      LOG (1, "counted %d redundant clauses with glue %d", count, glue);
    lgl->stats->red.lrg += count;
    lgl->stats->lir[glue].clauses = count;
  }
  assert (lgl->stats->red.lrg >= 0);
  if (lgl->stats->red.bin)
    LOG (1, "counted %d binary redundant clauses altogether",
	 lgl->stats->red.bin);
  if (lgl->stats->red.trn)
    LOG (1, "counted %d ternary redundant clauses altogether",
	 lgl->stats->red.trn);
  if (lgl->stats->red.lrg)
    LOG (1, "counted %d large redundant clauses altogether",
	 lgl->stats->red.lrg);
}

static int lglilit (int ulit) {
  int res = ulit/2;
  assert (res >= 1);
  if (ulit & 1) res = -res;
  return res;
}

static void lgljwh (LGL * lgl) {
  int idx, sign, lit, tag, blit, other, other2, red, size, glue;
  const int *p, * w, * eow, * c;
  Val val, tmp, tmp2;
  HTS * hts;
  Stk * s;
  Flt inc;
  CLN (lgl->jwh, 2*lgl->nvars);
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      val = lglval (lgl, lit);
      if (val > 0) continue;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	if (!lgl->opts->jwhred.val && red) continue;
	if (lgl->opts->jwhred.val == 2 && !red) continue;
	other = blit >> RMSHFT;
	if (abs (other) < abs (lit)) continue;
	tmp = lglval (lgl, other);
	if (tmp > 0) continue;
	if (tag == BINCS) {
	  assert (!tmp);
	  inc = lglflt (-2, 1);
	  lglincjwh (lgl, lit, inc);
	  lglincjwh (lgl, other, inc);
	} else {
	  assert (tag == TRNCS);
	  other2 = *p;
	  if (abs (other2) < abs (lit)) continue;
	  tmp2 = lglval (lgl, other2);
	  if (tmp2 > 0) continue;
	  assert ((val > 0) + (tmp > 0) + (tmp2 > 0) == 0);
	  assert ((val < 0) + (tmp < 0) + (tmp2 < 0) <= 1);
	  size = 3 + val + tmp + tmp2;
	  assert (2 <= size && size <= 3);
	  inc = lglflt (-size, 1);
	  if (!val) lglincjwh (lgl, lit, inc);
	  if (!tmp) lglincjwh (lgl, other, inc);
	  if (!tmp2) lglincjwh (lgl, other2, inc);
	}
      }
    }
  for (glue = -1; glue < MAXGLUE; glue++) {
    if (!lgl->opts->jwhred.val && glue >= 0) continue;
    if (lgl->opts->jwhred.val == 2 && glue < 0) continue;
    if (glue < 0) s = &lgl->irr;
    else s = &lgl->red[glue];
    for (c = s->start; c < s->top; c = p + 1) {
      if (*(p = c) >= NOTALIT) continue;
      val = -1;
      size = 0;
      while ((other = *p)) {
	tmp = lglval (lgl, other);
	if (tmp > val) val = tmp;
	if (!tmp) size++;
	p++;
      }
      if (val > 0) continue;
      inc = lglflt (-size, 1);
      for (p = c; (other = *p); p++)
	if (!lglval (lgl, other))
	  lglincjwh (lgl, other, inc);
    }
  }
}

static int * lglis (LGL * lgl) {
  int idx, sign, lit, tag, blit, other, other2, red, * res;
  const int *p, * w, * eow, * c;
  Val val, tmp, tmp2;
  HTS * hts;
  Stk * s;
  NEW (res, 2*lgl->nvars);
  res += lgl->nvars;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      val = lglval (lgl, lit);
      if (val > 0) continue;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	if (red) continue;
	other = blit >> RMSHFT;
	if (abs (other) < abs (lit)) continue;
	tmp = lglval (lgl, other);
	if (tmp > 0) continue;
	if (tag == BINCS) {
	  assert (!tmp);
	  res[lit]++,
	  res[other]++;
	} else {
	  assert (tag == TRNCS);
	  other2 = *p;
	  if (abs (other2) < abs (lit)) continue;
	  tmp2 = lglval (lgl, other2);
	  if (tmp2 > 0) continue;
	  assert ((val > 0) + (tmp > 0) + (tmp2 > 0) == 0);
	  assert ((val < 0) + (tmp < 0) + (tmp2 < 0) <= 1);
	  if (!val) res[lit]++;
	  if (!tmp) res[other]++;
	  if (!tmp2) res[other2]++;
	}
      }
    }
  s = &lgl->irr;
  for (c = s->start; c < s->top; c = p + 1) {
    p = c;
    if (*p >= NOTALIT) continue;
    val = -1;
    while ((other = *p)) {
      tmp = lglval (lgl, other);
      if (tmp > val) val = tmp;
      p++;
    }
    if (val > 0) continue;
    for (p = c; (other = *p); p++)
      if (!lglval (lgl, other))
	res[other]++;
  }
  return res;
}

static int lglsetjwhbias (LGL * lgl, int idx) {
  AVar * av = lglavar (lgl, idx);
  Flt pos, neg;
  int bias;
  idx = abs (idx);
  pos = lgl->jwh[lglulit (idx)];
  neg = lgl->jwh[lglulit (-idx)];
  if (av->phase) return av->phase;
  bias = (pos > neg) ? 1 : -1;
  if (av->bias == bias) return bias;
  av->bias = bias;
  lgl->stats->phase.set++;
  if (bias > 0) lgl->stats->phase.pos++; else lgl->stats->phase.neg++;
  LOG (1, "JW bias %d (pos %s, neg %s)", 
       bias * idx, lglflt2str (lgl, pos), lglflt2str (lgl, neg));
  return bias;
}

static void lglsetbias (LGL * lgl, int idx, int bias) {
  AVar * av = lglavar (lgl, idx);
  assert (abs (bias) == 1);
  if (av->phase) return;
  av->bias = bias;
  lgl->stats->phase.set++;
  if (bias > 0) lgl->stats->phase.pos++; else lgl->stats->phase.neg++;
  LOG (1, "set bias %d explicitly", bias * idx);
}

static void lglsetallphases (LGL * lgl) {
  int res = 1, idx;
  for (idx = 2; res && idx < lgl->nvars; idx++)
    res = (!lglisfree (lgl, idx) || lglavar (lgl, idx)->phase);
  lgl->allphaseset = res;
}

static void lglflushphases (LGL * lgl) {
  int idx, flushed = 0;
  AVar * av;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    av = lglavar (lgl, idx);
    av->phase = 0;
    flushed++;
  }
  lglprt (lgl, 1, "[flushphases] %d phases reset", flushed);
  lgl->allphaseset = !flushed;
  lgl->flushphases = 0;
}

static int lgluckyphase (LGL * lgl) {
  int pos = 0, neg = 0, lit, idx, count = 0, res = 0;
  int negrest, posrest;
  const int * p, * c;
  for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
    int foundpos = 0, foundneg = 0;
    if (*(p = c) >= NOTALIT) continue;
    while ((lit = *p)) {
      if (lit > 0) foundpos = 1;
      if (lit < 0) foundneg = 1;
      p++;
    }
    if (foundpos) pos++;
    if (foundneg) neg++;
    count++;
  }
  for (idx = 2; idx < lgl->nvars; idx++) {
    HTS * hts = lglhts (lgl, idx);
    const int * p, * w, * eow;
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    for (p = w; p < eow; p++) {
      int blit = *p, red, other;
      int tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) p++;
      if (tag == LRGCS) continue;
      red = blit & REDCS;
      if (red) continue;
      other = blit >> RMSHFT;
      if (abs (other) < idx) continue;
      if (tag == TRNCS) {
	int other2 = *p;
	if (abs (other2) < idx) continue;
	if (other < 0 || other2 < 0) neg++;
      } else if (other < 0) neg++;
      count++;
      pos++;
    }
    hts = lglhts (lgl, -idx);
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    for (p = w; p < eow; p++) {
      int blit = *p, red, other;
      int tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) p++;
      if (tag == LRGCS) continue;
      red = blit & REDCS;
      if (red) continue;
      other = blit >> RMSHFT;
      if (abs (other) < idx) continue;
      if (tag == TRNCS) {
	int other2 = *p;
	if (abs (other2) < idx) continue;
	if (other > 0 || other2 > 0) pos++;
      } else if (other > 0) pos++;
      count++;
      neg++;
    }
  }
  assert (count >= neg);
  negrest = count - neg;
  assert (count >= pos);
  posrest = count - pos;
  assert (count == lgl->stats->irr.clauses.cur);
  lglprt (lgl, 1,
    "[phase-count-%d] %d negative %.1f%% of %d except %d %.1f%%",
    lgl->stats->phase.count,
    neg, lglpcnt (neg, count), count, negrest, lglpcnt (negrest, count));
  lglprt (lgl, 1,
    "[phase-count-%d] %d positive %.1f%% of %d except %d %.1f%%",
    lgl->stats->phase.count,
    pos, lglpcnt (pos, count), count, posrest, lglpcnt (posrest, count));
  if (neg >= count) {
    res = -1;
    lglprt (lgl, 1,
      "[phase-count-%d] all clauses contain a negative literal",
      lgl->stats->phase.count);
  } else if (pos >= count) {
    res = 1;
    lglprt (lgl, 1,
      "[phase-count-%d] all clauses contain a positive literal",
      lgl->stats->phase.count);
  } else if (lgl->stats->phase.count <= lgl->opts->phaseluckmaxround.val) {
    int lim = lgl->opts->phaselucklim.val * (count / 1000);
    int fac = lgl->opts->phaseluckfactor.val;
    if (negrest <= lim &&
	negrest <= posrest &&
	posrest/fac >= negrest/100) {
      res = -1;
      lglprt (lgl, 1,
	"[phase-count-%d] less non-negative clauses %d than limit %d (%.1f%%)",
	lgl->stats->phase.count,
	negrest, lim, lgl->opts->phaselucklim.val / 10.0);
      lglprt (lgl, 1,
	"[phase-count-%d] non-pos/non-neg = %d/%d = %.2f >= %.2f = %d/100",
	lgl->stats->phase.count,
	posrest, negrest, posrest/(double)negrest, fac/100.0, fac);
    } else if (posrest <= lim && 
               posrest <= negrest &&
               negrest/fac >= posrest/100) {
      res = 1;
      lglprt (lgl, 1,
	"[phase-count-%d] less non-positive clauses %d than limit %d (%.1f%%)",
	lgl->stats->phase.count,
	posrest, lim, lgl->opts->phaselucklim.val / 1000.0);
      lglprt (lgl, 1,
	"[phase-count-%d] non-neg/non-pos = %d/%d = %.2f >= %.2f = %d/100",
	lgl->stats->phase.count,
	negrest, posrest, negrest/(double)posrest, fac/100.0, fac);
    }
  } else
      lglprt (lgl, 1,
	"[phase-count-%d] skipping relative phase luck test",
        lgl->stats->phase.count);
  if (res)
    lglprt (lgl, 1,
      "[lucky-phase-%d] forcing lucky phase %d",
      lgl->stats->phase.count,
      res);
  return res;
}

static void lglphase (LGL * lgl) {
  int64_t set = lgl->stats->phase.set;
  int64_t pos = lgl->stats->phase.pos;
  int64_t neg = lgl->stats->phase.neg;
  int idx, lucky;
  lglstart (lgl, &lgl->times->phase);
  if (lgl->flushphases) lglflushphases (lgl);
  if (lgl->opts->phase.val) goto DONE;
  lglsetallphases (lgl);
  if (lgl->allphaseset) goto DONE;
  lgl->stats->phase.count++;
  lgljwh (lgl);
  if ((lucky = lgluckyphase (lgl)))
    for (idx = 2; idx < lgl->nvars; idx++)
      lglsetbias (lgl, idx, lucky);
  else
    for (idx = 2; idx < lgl->nvars; idx++)
      lglsetjwhbias (lgl, idx);
  set = lgl->stats->phase.set - set;
  pos = lgl->stats->phase.pos - pos;
  neg = lgl->stats->phase.neg - neg;
  lglprt (lgl, 1,
     "[phase-%d] phase bias: %lld positive %.0f%%, %lld negative %.0f%%",
     lgl->stats->phase.count,
     (LGLL) pos, lglpcnt (pos, set),
     (LGLL) neg, lglpcnt (neg, set));
DONE:
  lglstop (lgl);
}

static int lglmaplit (int * map, int lit) {
  return map [ abs (lit) ] * lglsgn (lit);
}

static void lglmapstk (LGL * lgl, int * map, Stk * lits) {
  int * p, * eol;
  eol = lits->top;
  for (p = lits->start; p < eol; p++)
    *p = lglmaplit (map, *p);
}

static void lglmapqueue (LGL * lgl, int * map) {
  int idx, found, * q, src, dst;
  const int * p, * start;
  QVar * qv;
  for (idx = 2; idx < lgl->nvars; idx++) {
    qv = lglqvar (lgl, idx);
    if (!qv->enqueued) continue;
    qv->pos = -1;
  }
  found = 0;
  start = q = lgl->queue.stk.start;
  for (p = q; p < lgl->queue.stk.top; p++) {
    if (!(src = *p)) continue;
    assert (1 < src);
    dst = lglmaplit (map, src);
    if (dst < 0) dst = -dst;
    if (dst <= 1) continue;
    qv = lglqvar (lgl, dst);
    if (!qv->enqueued) continue;
    if (qv->pos >= 0) continue;
    qv->pos = (q - start);
    assert (qv->pos >= 0);
    if (!found && lgl->queue.next >= (p - start))
      found = 1, lgl->queue.next = qv->pos;
    *q++ = dst;
  }
  for (idx = 2; idx < lgl->nvars; idx++) {
    qv = lglqvar (lgl, idx);
    if (!qv->enqueued) continue;
    if (qv->pos >= 0) continue;
    assert (q < lgl->queue.stk.top);
    qv->pos = (q - start);
    assert (qv->pos >= 0);
    *q++ = idx;
  }
  lgl->queue.stk.top = q;
  lglfitstk (lgl, &lgl->queue.stk);
  if (!found) lgl->queue.next = lglcntstk (&lgl->queue.stk) - 1;
  lgl->queue.mt = 0;
}

static void lglmapglue (LGL * lgl, int * map, Stk * lits) {
  int * p, * eol;
  eol = lits->top;
  for (p = lits->start; p < eol; p++)
    if (!lglisact (*p)) *p = lglmaplit (map, *p);
}

static void lglmaplits (LGL * lgl, int * map) {
  int glue;
  lglmapstk (lgl, map, &lgl->irr);
  for (glue = 0; glue < MAXGLUE; glue++)
    lglmapglue (lgl, map, &lgl->red[glue]);
}

static void lglmapvars (LGL * lgl, int * map, int nvars) {
  int i, oldnvars = lgl->nvars, sign, udst, idst, usrc, isrc;
  DVar * dvars;
  QVar * qvars;
  AVar * avars;
  Val * vals;
  int * i2e;
  Flt * jwh;

  if (nvars > 2) assert (nvars <= oldnvars);
  else nvars = 0;

  DEL (lgl->doms, 2*lgl->szvars);
  NEW (lgl->doms, 2*nvars);

  NEW (vals, nvars);
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      vals[map[i]] = lgl->vals[i];
  DEL (lgl->vals, lgl->szvars);
  lgl->vals = vals;

  NEW (i2e, nvars);
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      i2e[map[i]] = lgl->i2e[i];
  DEL (lgl->i2e, lgl->szvars);
  lgl->i2e = i2e;

  NEW (dvars, nvars);
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      dvars[map[i]] = lgl->dvars[i];
  DEL (lgl->dvars, lgl->szvars);
  lgl->dvars = dvars;

  NEW (qvars, nvars);
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      qvars[map[i]] = lgl->qvars[i];
  DEL (lgl->qvars, lgl->szvars);
  lgl->qvars = qvars;

  NEW (jwh, 2*nvars);
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      for (sign = -1; sign <= 1; sign += 2) {
	  isrc = sign * i;
	  idst = sign * map[i];
	  usrc = lglulit (isrc);
	  udst = lglulit (idst);
	  jwh[udst] = lgladdflt (jwh[udst], lgl->jwh[usrc]);
	}
  DEL (lgl->jwh, 2*lgl->szvars);
  lgl->jwh = jwh;

  NEW (avars, nvars);	  	
  for (i = 2; i < oldnvars; i++)
    if (lglisfree (lgl, i))
      avars[map[i]] = lgl->avars[i];
  DEL (lgl->avars, lgl->szvars);
  lgl->avars = avars;              // Last since 'lglisfree' depends on it !!!

  lgl->nvars = lgl->szvars = nvars;
  lgl->stats->fixed.current = 0;
}

static void lglmaphts (LGL * lgl, int * map) {
  int idx, sign, lit, * w, *eow, * p, other, other2, blit, tag, red;
  int newblit, newother, newother2;
  HTS * hts;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->count) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	assert (tag == BINCS || tag == TRNCS || tag == LRGCS);
	red = blit & REDCS;
	other = blit >> RMSHFT;
	newother = lglmaplit (map, other);
	newblit = RMSHFTLIT (newother) | tag | red;
	*p = newblit;
	if (tag == BINCS) continue;
	other2 = *++p;
	if (tag == LRGCS) continue;
	assert (tag == TRNCS);
	newother2 = lglmaplit (map, other2);
	*p = newother2;
      }
    }
}

static void lglmaptrail (LGL * lgl, int * map) {
  int * p, * q, src, dst;
  for (p = lgl->trail.start; p < lgl->trail.top; p++)
    if (lglevel (lgl, *p) > 0) break;
  for (q = lgl->trail.start; p < lgl->trail.top; p++) {
    src = *p;
    assert (lglevel (lgl, src) > 0);
    dst = lglmaplit (map, src);
    *q++ = dst;
  }
  lgl->trail.top = q;
  lgl->flushed = lgl->next2 = lgl->next = lglcntstk (&lgl->trail);
}

static int lglptrjmp (int * repr, int max, int start) {
#ifndef NDEBUG
  int prev = 0, count = 0;
#endif
  int next, idx, res, sgn, tmp;
  assert (repr);
  next = start;
  do {
    res = next;
    idx = abs (res);
    assert (idx <= max);
    sgn = lglsgn (res);
    next = repr[idx];
    next *= sgn;
#ifndef NDEBUG
    if (prev || next) assert (prev != next);
    prev = res;
    assert (count <= max);
#endif
  } while (next);
  tmp = start;
  while (tmp != res) {
    idx = abs (tmp), sgn = lglsgn (tmp);
    next = repr[idx] * sgn;
    repr[idx] = sgn * res;
    tmp = next;
  }
  return res;
}

static int lglirepr (LGL * lgl, int lit) {
  assert (lgl->repr);
  return lglptrjmp (lgl->repr, lgl->nvars - 1, lit);
}

static void lglmapext (LGL * lgl, int * map) {
  int eidx, ilit, mlit;
  Ext * ext;
  for (eidx = 1; eidx <= lgl->maxext; eidx++) (void) lglerepr (lgl, eidx);
  for (eidx = 1; eidx <= lgl->maxext; eidx++) {
    ext = lgl->ext + eidx;
    if (!ext->imported) continue;
    if (ext->equiv) {
      LOG (3, "mapping external %d to equivalent external %d",
	   eidx, ext->repr);
      continue;
    }
    ilit = ext->repr;
    mlit = lglmaplit (map, ilit);
    LOG (3, "mapping external %d to internal %d", eidx, mlit);
    ext->repr = mlit;
  }
}

static void lglsignedmark (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int bit = 1 << (lit < 0);
  if (av->mark & bit) return;
  av->mark |= bit;
}

static void lglsignedunmark (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int bit = 1 << (lit < 0);
  if (!(av->mark & bit)) return;
  av->mark &= ~bit;
}

static int lglsignedmarked (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int bit = 1 << (lit < 0);
  return av->mark & bit;
}

static void lglmapass (LGL * lgl, int * map) {
  int * p, * q, iass, mass, flushed;
  unsigned bit;
  AVar * av;
  if (abs (lgl->failed) != 1) lgl->failed = lglmaplit (map, lgl->failed);
  for (p = q = lgl->assume.start; p < lgl->assume.top; p++) {
    iass = *p;
    mass = lglmaplit (map, iass);
    if (mass == 1) continue;
    if (mass == -1) {
      if (lgl->failed != -1) {
#ifndef NDEBUG
	int * r;
	for (r = lgl->eassume.start; r < lgl->eassume.top; r++)
	  if (lglimport (lgl, *r) == -1) break;
	assert (r < lgl->eassume.top);
#endif
	LOG (2, "enforcing a failed assumption");
	lgl->failed = -1;
      }
      continue;
    }
    LOG (2, "mapping previous internal assumption %d to %d", iass, mass);
    av = lglavar (lgl, mass);
    bit = 1u << (mass < 0);
    if (!(av->assumed & bit)) {
      LOG (2, "assuming new representative %d instead of %d", mass, iass);
      av->assumed |= bit;
    }
    *q++ = mass;
  }
  lgl->assume.top = q;
  flushed = 0;
  for (p = q = lgl->assume.start; p < lgl->assume.top; p++) {
    iass = *p;
    if (lglsignedmarked (lgl, iass)) { flushed++; continue; }
    lglsignedmark (lgl, iass);
    *q++ = iass;
  }
  lgl->assume.top = q;
  for (p = lgl->assume.start; p < lgl->assume.top; p++) {
    iass = *p;
    assert (lglsignedmarked (lgl, iass));
    lglsignedunmark (lgl, iass);
  }
  if (flushed)
    LOG (2, "flushed %d duplicated internal assumptions", flushed);
}

static void lglmaplkhdscore (LGL * lgl, int * map, int oldnvars) {
  LKHD * oldlkhdscore = lgl->tlk->lkhd, score;
  int idx, src, sign, dst;
  NEW (lgl->tlk->lkhd, 2*lgl->nvars);
  lgl->tlk->lkhd += lgl->nvars;
  for (idx = oldnvars-1; idx >= 2; idx--) {
    for (sign = -1; sign <= 1; sign += 2) {
      src = sign * idx;
      dst = lglmaplit (map, src);
      if (abs (dst) <= 1) continue;
      score = oldlkhdscore[src];
      LOG (2, "mapping look-ahead score %s of %d as score of %d",
	   lglflt2str (lgl, score), src, dst);
      lgl->tlk->lkhd[dst] = score;
    }
  }
  oldlkhdscore -= oldnvars;
  DEL (oldlkhdscore, 2*oldnvars);
}

static int lglmapsize (LGL * lgl) {
  int size = 0, idx;
  for (idx = 2; idx < lgl->nvars; idx++) 
    if (lglisfree (lgl, idx)) size++;
  LOG (1, "mapping %d remaining variables", size);
  return size;
}

static void lglmapnonequiv (LGL * lgl, int * map, int size) {
  int count = 0, idx;
  AVar * av;
  Val val;
  map[0] = 0, map[1] = 1;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (map[idx]) continue;
    av = lglavar (lgl, idx);
    if (av->type == FREEVAR) {
      assert (idx > 0);
      if (map[idx]) { assert (map[idx] < idx); continue; }
      LOG (3, "mapping free %d to %d", idx, count + 2);
      map[idx] = count + 2;
      count++;
    } else if (av->type == EQUIVAR) {
      assert (lgl->repr);
      assert (!map[idx]);
    } else if (av->type == FIXEDVAR) {
      val = lgl->vals[idx];
      assert (val);
      LOG (3, "mapping assigned %d to %d", idx, (int) val);
      map[idx] = val;
    } else {
      assert (av->type == ELIMVAR);
      assert (!lglifrozen (lgl, idx));
      map[idx] = 0;
    }
  }
  assert (count == size);
}

static void lglmapequiv (LGL * lgl, int * map) {
  int idx, repr, dst;
  AVar * av;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (map[idx]) continue;
    av = lglavar (lgl, idx);
    if (av->type == ELIMVAR) continue;
    assert (av->type == EQUIVAR);
    assert (lgl->repr);
    assert (!map[idx]);
    repr = lglirepr (lgl, idx);
    assert (repr != idx);
    assert (map[abs (repr)]);
    dst = lglmaplit (map, repr);
    LOG (3, "mapping equivalent %d to %d", idx, dst);
    map[idx] = dst;
  }
}

static int64_t lglsteps (LGL * lgl) {
  int64_t res = lgl->stats->steps;
#ifndef NDEBUG
  // Note, this would be bulky and slow ...
  int64_t steps = 0;
  steps += lgl->stats->bca.steps;
  steps += lgl->stats->blk.steps;
  steps += lgl->stats->card.steps;
  steps += lgl->stats->cce.steps;
  steps += lgl->stats->elm.copies;
  steps += lgl->stats->elm.resolutions;
  steps += lgl->stats->elm.steps;
  steps += lgl->stats->gauss.steps.elim;
  steps += lgl->stats->gauss.steps.extr;
  steps += lgl->stats->prb.basic.steps;
  steps += lgl->stats->prb.simple.steps;
  steps += lgl->stats->prb.treelook.steps;
  steps += lgl->stats->props.lkhd;
  steps += lgl->stats->props.search;
  steps += lgl->stats->props.simp;
  steps += lgl->stats->sweep.steps;
  steps += lgl->stats->trd.steps;
  steps += lgl->stats->ternres.steps;
  steps += lgl->stats->unhd.steps;
  assert (steps == res);
#endif
  return res;
}

static void lgltrep (LGL * lgl) {
  int64_t steps, i;
  double t;
  if (!lgl->opts->trep.val) return;
  if (lgl->opts->verbose.val) return;
  steps = lglsteps (lgl);
  if (steps < lgl->limits->trep.steps) return;
  lgl->limits->trep.steps += lgl->opts->trepint.val;
  t = lgl->opts->abstime.val ? lglgetime (lgl) : lglsec (lgl);
  if (t < lgl->limits->trep.time) return;
  lglrep (lgl, 0, (lgl->simp ? 'P' : 'S'));
  i = lgl->limits->trep.time;
  do {
         if (!i)         i = 1;
    else if (i == 1)     i = 2;
    else if (i == 2)     i = 5;
    else if (i < 10)     i = 10;
    else if (i < 60)     i += 10;
    else if (i < 300)    i += 60;
    else if (i < 900)    i += 300;
    else if (i < 7200)   i += 900;
    else                 i += 3600;
  } while (i < t);
  lgl->limits->trep.time = i;
}

static int lglterminate (LGL * lgl) {
  int64_t steps;
  int res;
  lgltrep (lgl);
  if (!lgl->cbs) return 0;
  if (!lgl->cbs->term.fun) return 0;
  if (lgl->cbs->term.done) return 1;
  steps = lglsteps (lgl);
  if (steps < lgl->limits->term.steps) return 0;
  res = lgl->cbs->term.fun (lgl->cbs->term.state);
  if (res) lgl->cbs->term.done = res;
  else lgl->limits->term.steps = steps + lgl->opts->termint.val;
  return  res;
}

static void lglmap (LGL * lgl) {
  int size, * map, oldnvars, mapsize;
#ifndef NDEBUG
  lglrelstk (lgl, &lgl->prevclause);
#endif
  lglrelstk (lgl, &lgl->promote);
  assert (!lgl->level);
  lgldreschedule (lgl);
  size = lglmapsize (lgl);
  oldnvars = lgl->nvars;
  mapsize = lglmax (oldnvars, 2);
  NEW (map, mapsize);
  lglmapnonequiv (lgl, map, size);
  lglmapequiv (lgl, map);
  lglmaptrail (lgl, map);
  lglmapvars (lgl, map, size + 2);
  lglmaplits (lgl, map);
  lglmapstk (lgl, map, &lgl->dsched);
  lglmapqueue (lgl, map);
  lglmapext (lgl, map);
  lglmapass (lgl, map);
  if (lgl->treelooking && lgl->tlk && lgl->tlk->lkhd)
    lglmaplkhdscore (lgl, map, oldnvars);
  assert (lglmtstk (&lgl->clause));
  lglmaphts (lgl, map);
  DEL (map, mapsize);
  if (lgl->repr) DEL (lgl->repr, oldnvars);
  lgl->unassigned = size;
  lgldreschedule (lgl);
#ifndef NLGLDRUPLIG
  lgl->drupligunit = 0;
#endif
}

static int lglgcnotnecessary (LGL * lgl) {
  if (lgl->forcegc) return 0;
  if (lgl->notfullyconnected) return 0;
  return lgl->stats->fixed.sum <= lgl->limits->gc.fixed;
}

static void lglcompact (LGL * lgl) {
  int glue;
  lglfitstk (lgl, &lgl->assume);
#ifndef NDEBUG
  lglfitstk (lgl, &lgl->prevclause);
#endif
  lglfitstk (lgl, &lgl->clause);
  lglfitstk (lgl, &lgl->eclause);
  lglfitstk (lgl, &lgl->dsched);
  lglfitstk (lgl, &lgl->queue.stk);
  lglfitstk (lgl, &lgl->eassume);
  lglfitstk (lgl, &lgl->extend);
  lglfitstk (lgl, &lgl->learned);
  lglfitstk (lgl, &lgl->frames);
  lglfitstk (lgl, &lgl->promote);
#ifndef NCHKSOL
  lglfitstk (lgl, &lgl->orig);
#endif
  lglfitstk (lgl, &lgl->trail);
  lgldefrag (lgl);
  lglfitstk (lgl, &lgl->wchs->stk);

  lglfitstk (lgl, &lgl->irr);
  for (glue = 0; glue <= MAXGLUE; glue++)
    lglfitlir (lgl, lgl->red + glue);
  lglrelstk (lgl, &lgl->lcaseen);
  lglrelstk (lgl, &lgl->resolvent);
  lglrelstk (lgl, &lgl->minstk);
  lglrelstk (lgl, &lgl->poisoned);
  lglrelstk (lgl, &lgl->seen);
  lglrelstk (lgl, &lgl->esched);
  lglrelstk (lgl, &lgl->saved.bin);
  lglrelstk (lgl, &lgl->saved.trn);
}

static void lglgc (LGL * lgl) {
  if (lgl->mt) return;
  lglchkred (lgl);
  if (lglgcnotnecessary (lgl)) return;
  lglstart (lgl, &lgl->times->gc);
  lglchkbcpclean (lgl, "gc");
  lglrep (lgl, 2, 'g');
  lgl->stats->gcs++;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  lglconsaved (lgl);
  do {			// Note, need to go into loop even if 'lgl->mt'!
    lgldis (lgl);
    lglcon (lgl);
    if (lgl->mt) break;
    if (lglbcpcomplete (lgl)) break;
    if (lglbcp (lgl)) continue;
    assert (!lgl->mt);
    LOG (1, "empty clause after propagating garbage collection unit");
    lglmt (lgl);
  } while (!lgl->mt);
  lglcount (lgl);
  lglmap (lgl);

  lglcompact (lgl);

  lgl->limits->gc.fixed = lgl->stats->fixed.sum;

  lglchkred (lgl);
  lglrep (lgl, 2, 'c');
  lglstop (lgl);
}

static int lgltopgc (LGL * lgl) {
  if (lgl->mt) return 0;
  assert (!lgl->forcegc && !lgl->allowforce);
  lgl->forcegc = lgl->allowforce = 1;
  lglgc (lgl);
  assert (lgl->forcegc && lgl->allowforce);
  lgl->forcegc = lgl->allowforce = 0;
  return !lgl->mt;
}

static int lglrandec (LGL * lgl) {
  unsigned size, pos, start, delta;
  int lit;
  lgl->limits->randec = lgl->stats->decisions;
  lgl->limits->randec += lgl->opts->randecint.val/2;
  lgl->limits->randec += lglrand (lgl) % lgl->opts->randecint.val;
  assert (lgl->nvars > 2);
  size = lgl->nvars - 2;
  if (!size) return 0;
  pos = start = lglrand (lgl) % size;
  lit = 2 + pos;
  assert (2 <= lit && lit < lgl->nvars);
  if (lglval (lgl, lit)) {
    delta = lglrand (lgl) % size;
    if (size == 1) return 0;
    if (!delta) delta++;
    while (lglgcd (delta, size) != 1)
      if (++delta == size) delta = 1;
    do {
      pos += delta;
      if (pos >= size) pos -= size;
      if (pos == start) return 0;
      lit = pos + 2;
      assert (2 <= lit && lit < lgl->nvars);
    } while (lglval (lgl, lit));
  }
  lgl->stats->randecs++;
  return lit;
}

static int lgladecide (LGL * lgl) {
  int res, val;
  while (lgl->assumed < lglcntstk (&lgl->assume)) {
    res = lglpeek (&lgl->assume, lgl->assumed);
    val = lglcval (lgl, res);
    if (val > 0) LOG (3, "assumption %d already satisfied", res);
    lgl->assumed++;
    LOG (3, "new assumption queue level %d", lgl->assumed);
    assert (val >= 0);
    if (!val) return res;
  }
  return 0;
}

static int lgldefphase (LGL * lgl, int idx) {
  int bias, res;
  AVar * av;
  assert (idx > 0);
  av = lglavar (lgl, idx);
  bias = lgl->opts->phase.val;
  if (!bias) bias = av->bias;
  if (!bias) bias = lglsetjwhbias (lgl, idx);
  if (lgl->opts->phasesave.val) {
    if (!(res = av->phase)) res = av->phase = bias;
    else if (lgl->opts->phasesave.val < 0) res = -res;
  } else res = bias;
  return res;
}

static int lgldecidephase (LGL * lgl, int lit) {
  int res = abs (lit);
  AVar * av = lglavar (lgl, lit);
  if (av->fase) return av->fase * res;
  if (lgldefphase (lgl, res) <= 0) res = -res;
  return res;
}

static int lglhasbins (LGL * lgl, int lit) {
  int blit, tag, other, other2, val, val2, implied;
  const int * p, * w, * eos, * q;
  HTS * hts;
  assert (!lgl->level);
  assert (lglisfree (lgl, lit));
  hts = lglhts (lgl, lit);
  w = lglhts2wchs (lgl, hts);
  eos = w + hts->count;
  for (p = w; p < eos; p++) {
    if (lgl->treelooking) INCSTEPS (prb.treelook.steps);
    blit = *p;
    tag = blit & MASKCS;
    if (tag == BINCS) {
      other = blit >> RMSHFT;
      val = lglval (lgl, other);
      assert (val >= 0);
      if (!val) return 1;
    } else if (tag == TRNCS) {
      other = blit >> RMSHFT;
      other2= *++p;
      val = lglval (lgl, other);
      val2 = lglval (lgl, other2);
      assert (val >= 0 || val2 >= 0);
      if (val > 0 || val2 > 0) continue;
      if (!val && val2 < 0) return 1;
      if (val < 0 && !val2) return 1;
    } else {
      assert (tag == LRGCS);
      q = lglidx2lits (lgl, (blit & REDCS), *++p);
      implied = 0;
      while ((other = *q++)) {
	if (other == lit) continue;
	val = lglval (lgl, other);
	if (val > 0) break;
	if (val < 0) continue;
	if (implied) break;
	implied = other;
      }
      if (other) continue;
      if (implied) return 1;
    }
  }
  return 0;
}

static int lgldecide (LGL * lgl) {
  int lit;
  lglchkbcpclean (lgl, "decide");
  if (!lgl->unassigned) return 0;
  if ((lit = lgladecide (lgl))) {
    LOG (2, "using assumption %d as decision", lit);
    lgl->alevel = lgl->level + 1;
    LOG (2, "new assumption decision level %d", lgl->alevel);
  } else {
    if (lgl->stats->stability.level > 0 &&
        lgl->stats->stability.level <= lgl->level)
      lglupdstab (lgl);
    if (lgl->opts->randec.val &&
	lgl->limits->randec <= lgl->stats->decisions) {
      lit = lglrandec (lgl);
      lit = lgldecidephase (lgl, lit);
      LOG (2, "random decision %d", lit);
    } else {
      lit = lglnextdecision (lgl, 1);
      lit = lgldecidephase (lgl, lit);
    }
  }
  if (lit) lgldassume (lgl, lit);
  return 1;
}

static void lgldcpdis (LGL * lgl) {
  int idx, sign, lit, tag, blit, red, other, other2, i;
  const int * w, * p, * eow;
  Val val;
  HTS * hts;
  Stk * s;
  NEW (lgl->dis, 1);
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      assert (hts->count > 0);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      hts->count = hts->offset = 0;
      val = lglval (lgl, lit);
      if (val > 0) continue;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	val = lglval (lgl, other);
	if (val > 0) continue;
	red = blit & REDCS;
	if (red && !lglisfree (lgl, other)) continue;
	if (tag == BINCS) {
	  s = red ? &lgl->dis->red.bin : &lgl->dis->irr.bin;
	} else {
	  assert (tag == TRNCS);
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  val = lglval (lgl, other2);
	  if (val > 0) continue;
	  if (red && !lglisfree (lgl, other2)) continue;
	  s = red ? &lgl->dis->red.trn : &lgl->dis->irr.trn;
	  lglpushstk (lgl, s, other2);
	}
	lglpushstk (lgl, s, other);
	lglpushstk (lgl, s, lit);
	lglpushstk (lgl, s, 0);
      }
    }
  lglrststk (&lgl->wchs->stk, 2);
  lgl->wchs->stk.top[-1] = INT_MAX;
  for (i = 0; i < MAXLDFW; i++) lgl->wchs->start[i] = INT_MAX;
  lgl->wchs->free = 0;
  lglrelstk (lgl, &lgl->learned);
}

static void lgldcpclnstk (LGL * lgl, int red, Stk * s) {
  int oldsz, newsz, lit, mark, satisfied, repr, act, changed;
  const int druplig = lgl->opts->druplig.val;
  const int * p, * c, * eos = s->top;
  int * start, * q, * r, * d;
  Stk * t, saved;
  Val val;
  CLR (saved);
  q = start = s->start;
  for (c = q; c < eos; c = p + 1) {
    act = *c;
    if (act == REMOVED) {
      for (p = c + 1; p < eos && *p == REMOVED; p++)
	;
      assert (p >= eos || *p < NOTALIT || lglisact (*p));
      p--;
      continue;
    }
    if (lglisact (act)) *q++ = *c++; else act = -1;
    d = q;
    satisfied = changed = 0;
#ifndef NDEBUG
    for (p = c; assert (p < eos), (lit = *p); p++) {
      assert (!lglavar (lgl, lit)->mark);
      repr = lglirepr (lgl, lit);
      assert (abs (repr) == 1 || !lglavar (lgl, lit)->mark);
    }
#endif
    lglclnstk (&saved);
    for (p = c; assert (p < eos), (lit = *p); p++) {
      assert (lit < NOTALIT);
      if (druplig) lglpushstk (lgl, &saved, lit);
      if (satisfied) continue;
      repr = lglirepr (lgl, lit);
      val = lglcval (lgl, repr);
      if (val > 0) { satisfied = 1; continue; }
      if (val < 0) { changed = 1; continue; }
      mark = lglmarked (lgl, repr);
      if (mark < 0) { satisfied = 1; continue; }
      if (mark > 0) { changed = 1; continue; }
      if (lit != repr) changed = 1;
      lglmark (lgl, repr);
      *q++ = repr;
    }
    oldsz = p - c;
    for (r = d; r < q; r++) lglunmark (lgl, *r);
    newsz = q - d;
    assert (satisfied || newsz == oldsz || changed);
    if (druplig && !satisfied && newsz > 1 && changed)
      *q = 0, lgldrupligaddclsaux (lgl, REDCS, d);
    if (satisfied || !oldsz) { q = d - (act >= 0); continue; }
    if (newsz >= 4) {
      assert (act < 0 || d[-1] == act);
      *q++ = 0;
      assert (d <= c);
    } else if (!newsz) {
      LOG (1, "found empty clause while cleaning decomposition");
      lglmt (lgl);
      q = d - (act >= 0);
    } else if (newsz == 1) {
      LOG (1, "new unit %d while cleaning decomposition", d[0]);
      lglunit (lgl, d[0]);
      q = d - (act >= 0);
    } else if (newsz == 2) {
      t = red ? &lgl->dis->red.bin : &lgl->dis->irr.bin;
      if (s != t) {
	lglpushstk (lgl, t, d[0]);
	lglpushstk (lgl, t, d[1]);
	lglpushstk (lgl, t, 0);
	q = d - (act >= 0);
      } else *q++ = 0;
    } else {
      assert (newsz == 3);
      t = red ? &lgl->dis->red.trn : &lgl->dis->irr.trn;
      if (s != t) {
	lglpushstk (lgl, t, d[0]);
	lglpushstk (lgl, t, d[1]);
	lglpushstk (lgl, t, d[2]);
	lglpushstk (lgl, t, 0);
	q = d - (act >= 0);
      } else *q++ = 0;
    }
    if (druplig && (satisfied || changed)) {
      lglpushstk (lgl, &saved, 0);
      lgldrupligdelclsaux (lgl, saved.start);
    }
  }
  s->top = q;
  lglrelstk (lgl, &saved);
}

static void lgldcpconnaux (LGL * lgl, int red, int glue, Stk * s) {
  int * start = s->start, * q, * d, lit, size, lidx, act;
  const int * p, * c, * eos = s->top;
  assert (red == 0 || red == REDCS);
  assert (!glue || red);
  q = start;
  for (c = q; c < eos; c = p + 1) {
    if (lglisact (act = *c)) *q++ = *c++; else act = -1;
    d = q;
    for (p = c; (lit = *p); p++) {
      assert (!lgl->repr[abs (lit)]);
      assert (!lgl->vals[abs (lit)]);
      *q++ = lit;
    }
    size = q - d;
    if (size == 2) {
      q = d - (act >= 0);
      lglwchbin (lgl, d[0], d[1], red);
      lglwchbin (lgl, d[1], d[0], red);
    } else if (size == 3) {
      q = d - (act >= 0);
      lglwchtrn (lgl, d[0], d[1], d[2], red);
      lglwchtrn (lgl, d[1], d[0], d[2], red);
      lglwchtrn (lgl, d[2], d[0], d[1], red);
    } else {
      assert (size > 3);
      *q++ = 0;
      lidx = d - start;
      if (red) {
	assert (lidx <= MAXREDLIDX);
	lidx <<= GLUESHFT;
	assert (0 <= lidx);
	lidx |= glue;
      }
      (void) lglwchlrg (lgl, d[0], d[1], red, lidx);
      (void) lglwchlrg (lgl, d[1], d[0], red, lidx);
    }
  }
  s->top = q;
}

static void lgldcpcon (LGL * lgl) {
  Stk * lir;
  int glue;
  lgldcpconnaux (lgl, 0, 0, &lgl->dis->irr.bin);
  lgldcpconnaux (lgl, REDCS, 0, &lgl->dis->red.bin);
  lgldcpconnaux (lgl, 0, 0, &lgl->dis->irr.trn);
  lgldcpconnaux (lgl, REDCS, 0, &lgl->dis->red.trn);
  lglrelstk (lgl, &lgl->dis->irr.bin);
  lglrelstk (lgl, &lgl->dis->irr.trn);
  lglrelstk (lgl, &lgl->dis->red.bin);
  lglrelstk (lgl, &lgl->dis->red.trn);
  DEL (lgl->dis, 1);
  lgldcpconnaux (lgl, 0, 0, &lgl->irr);
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    lgldcpconnaux (lgl, REDCS, glue, lir);
  }
  lglfullyconnected (lgl);
}

static void lgldcpcln (LGL * lgl) {
  int glue, old, rounds = 0;
  Stk * lir;
  do {
    rounds++;
    old = lgl->stats->fixed.current;
    lgldcpclnstk (lgl, 0, &lgl->irr);
    lgldcpclnstk (lgl, 0, &lgl->dis->irr.bin);
    lgldcpclnstk (lgl, 0, &lgl->dis->irr.trn);
    lgldcpclnstk (lgl, REDCS, &lgl->dis->red.bin);
    lgldcpclnstk (lgl, REDCS, &lgl->dis->red.trn);
    for (glue = 0; glue < MAXGLUE; glue++) {
      lir = lgl->red + glue;
      lgldcpclnstk (lgl, REDCS, lir);
    }
  } while (old < lgl->stats->fixed.current);
  LOG (1, "iterated %d decomposition cleaning rounds", rounds);
}

static void lglepush (LGL * lgl, int ilit) {
  int elit = ilit ? lglexport (lgl, ilit) : 0;
  lglpushstk (lgl, &lgl->extend, elit);
  LOG (4, "pushing external %d internal %d", elit, ilit);
}

static void lglemerge (LGL * lgl, int ilit0, int ilit1) {
  int elit0 = lglexport (lgl, ilit0), elit1 = lglexport (lgl, ilit1);
  int repr0 = lglerepr (lgl, elit0), repr1 = lglerepr (lgl, elit1);
  Ext * ext0 = lglelit2ext (lgl, repr0);
  Ext * ext1 = lglelit2ext (lgl, repr1);
#ifndef NDEBUG
  int repr = repr1;
#endif
  assert (abs (repr0) != abs (repr1));
  if (repr0 < 0) {
#ifndef NLGLOG
    repr0 *= -1;
#endif
    repr1 *= -1;
  }
  ext0->equiv = 1;
  ext0->repr = repr1;
  if (ext1->aliased) ext0->aliased = 1;
  LOG (2, "merging external literals %d and %d", repr0, repr1);
  assert (lglerepr (lgl, elit0) == repr);
  assert (lglerepr (lgl, elit1) == repr);
  assert (!(ext0->frozen || ext0->tmpfrozen) ||
	    ext1->frozen || ext1->tmpfrozen);
  lglepush (lgl, -ilit0); lglepush (lgl, ilit1); lglepush (lgl, 0);
  lglepush (lgl, ilit0); lglepush (lgl, -ilit1); lglepush (lgl, 0);
  lgldrupligaddclsarg (lgl, REDCS, -ilit0, ilit1, 0);
  lgldrupligaddclsarg (lgl, REDCS, ilit0, -ilit1, 0);
}

static void lglimerge (LGL * lgl, int lit, int repr) {
  int idx = abs (lit);
  AVar * av = lglavar (lgl, idx);
  assert (!lglifrozen (lgl, lit) || lglifrozen (lgl, repr));
  if (lit < 0) repr = -repr;
  assert (av->type == FREEVAR);
  assert (lgl->repr);
  av->type = EQUIVAR;
  lgl->repr[idx] = repr;
  lgl->stats->prgss++;
  lgl->stats->irrprgss++;
  lgl->stats->equiv.sum++;
  lgl->stats->equiv.current++;
  assert (lgl->stats->equiv.sum > 0);
  assert (lgl->stats->equiv.current > 0);
  lglemerge (lgl, idx, repr);
}

static void lglfreezer (LGL * lgl) {
  int frozen, melted, tmpfrozen, elit, erepr, ilit;
  Ext * ext, * rext;
  int * p, eass;
  if (lgl->frozen) return;
  for (elit = 1; elit <= lgl->maxext; elit++)
    lgl->ext[elit].tmpfrozen = 0;
  tmpfrozen = frozen = 0;
  if (!lglmtstk (&lgl->eassume)) {
    for (p = lgl->eassume.start; p < lgl->eassume.top; p++) {
      eass = *p;
      ext = lglelit2ext (lgl, eass);
      assert (!ext->melted);
      assert (!ext->eliminated);
      assert (!ext->blocking);
      if (!ext->frozen && !ext->tmpfrozen) {
	ext->tmpfrozen = 1;
	tmpfrozen++;
	LOG (2, "temporarily freezing external assumption %d", eass);
	erepr = lglerepr (lgl, eass);
	rext = lglelit2ext (lgl, erepr);
	if (ext != rext && !rext->frozen && !rext->tmpfrozen) {
	  assert (!rext->equiv);
	  assert (!rext->eliminated);
	  // assert (!rext->blocking);
	  LOG (2,
	    "temporarily freezing external assumption literal %d", erepr);
	  rext->tmpfrozen = 1;
	  tmpfrozen++;
	}
      }
    }
  }
  for (elit = 1; elit <= lgl->maxext; elit++) {
    ext = lglelit2ext (lgl, elit);
    if (!ext->frozen) continue;
    frozen++;
    assert (!ext->melted);
    assert (!ext->eliminated);
    assert (!ext->blocking);
    erepr = lglerepr (lgl, elit);
    rext = lglelit2ext (lgl, erepr);
    if (ext == rext) continue;
    if (rext->frozen) continue;
    if (rext->tmpfrozen) continue;
    // assert (!rext->melted);
    assert (!rext->equiv);
    assert (!rext->eliminated);
    // assert (!rext->blocking);
    LOG (2, "temporarily freezing external literal %d", erepr);
    rext->tmpfrozen = 1;
    tmpfrozen++;
  }
  melted = 0;
  for (elit = 1; elit <= lgl->maxext; elit++) {
    ext = lglelit2ext (lgl, elit);
    if (ext->frozen) continue;
    if (ext->melted) continue;
    if (ext->tmpfrozen) continue;
    if (!ext->imported) continue;
    LOG (2, "permanently melted external %d", elit);
    ext->melted = 1;
    melted++;
  }
  LOG (2, "found %d frozen external variables", frozen);
  LOG (2, "temporarily frozen %d external variables", tmpfrozen);
  LOG (2, "permanently melted %d external variables", melted);
  lgl->frozen = 1;
  LOG (2, "frozen solver");
  melted = frozen = 0;
  for (ilit = 2; ilit < lgl->nvars; ilit++) {
    if (!lglisfree (lgl, ilit)) continue;
    if (lglifrozen (lgl, ilit)) frozen++; else melted++;
  }
  lgl->allfrozen = !melted;
  if (lgl->allfrozen) 
    lglprt (lgl, 1, "[freezer] all %d free variables frozen", frozen);
  else
    lglprt (lgl, 1,
      "[freezer] frozen %d variables out of %d free variables %.0f%%",
      frozen, frozen + melted, lglpcnt (frozen, frozen + melted));
}

static int lglcmprepr (LGL * lgl, int a, int b) {
  int f = lglifrozen (lgl, a), g = lglifrozen (lgl, b), res;
  if ((res = g - f)) return res;
  if ((res = (abs (a) - abs (b)))) return res;
  return a - b;
}

static int lgltarjan (LGL * lgl) {
  int * dfsimap, * mindfsimap, idx, oidx, sign, lit, blit, tag, other;
  int dfsi, mindfsi, ulit, uother, tmp, repr, res, sgn, frozen;
  const int * p, * w, * eow;
  Stk stk, component;
  AVar * av;
  HTS * hts;
  if (lgl->mt) return 0;
  if (!lgl->nvars) return 1;
  assert (lgl->frozen);
  dfsi = 0;
  NEW (dfsimap, 2*lgl->nvars);
  NEW (mindfsimap, 2*lgl->nvars);
  NEW (lgl->repr, lgl->nvars);
  CLR (stk); CLR (component);
  res = 1;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      ulit = lglulit (lit);
      tmp = dfsimap[ulit];
      if (tmp) continue;
      lglpushstk (lgl, &stk, lit);
      while (!lglmtstk (&stk)) {
	lit = lglpopstk (&stk);
	if (lit) {
	  ulit = lglulit (lit);
	  if (dfsimap[ulit]) continue;
	  dfsimap[ulit] = mindfsimap[ulit] = ++dfsi;
	  lglpushstk (lgl, &component, lit);
	  assert (dfsi > 0);
	  lglpushstk (lgl, &stk, lit);
	  lglpushstk (lgl, &stk, 0);
	  hts = lglhts (lgl, -lit);
	  if (!hts->offset) continue;
	  assert (hts->count > 0);
	  w = lglhts2wchs (lgl, hts);
	  eow = w + hts->count;
	  for (p = w; p < eow; p++) {
	    blit = *p;
	    tag = blit & MASKCS;
	    if (tag != BINCS) { p++; continue; }
	    other = blit >> RMSHFT;
	    uother = lglulit (other);
	    tmp = dfsimap[uother];
	    if (tmp) continue;
	    lglpushstk (lgl, &stk, other);
	  }
	} else {
	  assert (!lglmtstk (&stk));
	  lit = lglpopstk (&stk);
	  ulit = lglulit (lit);
	  mindfsi = dfsimap[ulit];
	  assert (mindfsi);
	  hts = lglhts (lgl, -lit);
	  w = lglhts2wchs (lgl, hts);
	  eow = w + hts->count;
	  for (p = w; p < eow; p++) {
	    blit = *p;
	    tag = blit & MASKCS;
	    if (tag != BINCS) { p++; continue; }
	    other = blit >> RMSHFT;
	    uother = lglulit (other);
	    tmp = mindfsimap[uother];
	    if (tmp >= mindfsi) continue;
	    mindfsi = tmp;
	  }
	  if (mindfsi == dfsimap[ulit]) {
	    repr = lit;
	    frozen = lglifrozen (lgl, repr);
	    for (p = component.top - 1; (other = *p) != lit; p--) {
	      if (lglcmprepr (lgl, other, repr) < 0) repr = other;
	      if (!frozen && lglifrozen (lgl, other)) frozen = 1;
	    }
	    while ((other = lglpopstk (&component)) != lit) {
	      mindfsimap[lglulit (other)] = INT_MAX;
	      if (other == repr) continue;
	      if (other == -repr) {
		LOG (1, "empty clause since repr[%d] = %d", repr, other);
		lgldrupligaddclsarg (lgl, REDCS, repr, 0);
		lglmt (lgl); res = 0; goto DONE;
	      }
	      sgn = lglsgn (other);
	      oidx = abs (other);
	      tmp = lgl->repr[oidx];
	      if (tmp == sgn * repr) continue;
	      LOG (2, "repr[%d] = %d", oidx, sgn * repr);
	      if (tmp) {
		LOG (1, "empty clause since repr[%d] = %d and repr[%d] = %d",
		     oidx, tmp, oidx, sgn * repr);
		lgldrupligaddclsarg (lgl, REDCS, repr, 0);
		lglmt (lgl); res = 0; goto DONE;
	      } else {
		av = lglavar (lgl, oidx);
		assert (sgn*oidx == other);
		if (av->type == FREEVAR) lglimerge (lgl, other, repr);
		else assert (av->type == FIXEDVAR);
	      }
	    }
	    mindfsimap[lglulit (lit)] = INT_MAX;
	    if (frozen) {
	      LOG (2, "equivalence class of %d is frozen", repr);
	      assert (lglifrozen (lgl, repr));
	    }
	  } else mindfsimap[ulit] = mindfsi;
	}
      }
    }
  }
DONE:
  lglrelstk (lgl, &stk);
  lglrelstk (lgl, &component);
  DEL (mindfsimap, 2*lgl->nvars);
  DEL (dfsimap, 2*lgl->nvars);
  if (!res) DEL (lgl->repr, lgl->nvars);
  if (lgl->mt) lgldrupligaddclsarg (lgl, REDCS, 0);
  return res;
}

static int lglsyncunits (LGL * lgl) {
  int * units, * eou, * p, elit, erepr, ilit, res, count = 0;
  void (*produce)(void*, int);
  int64_t steps;
  Ext * ext;
  Val val;
  if (lgl->mt) return 0;
  if (!lgl->cbs) return 1;
  if (!lgl->cbs->units.consume.fun) return 1;
  assert (!lgl->simp || !lgl->level);
  steps = lglsteps (lgl);
  if (steps < lgl->limits->sync.steps) return 1;
  lgl->limits->sync.steps = steps + lgl->opts->syncunint.val;
  lgl->stats->sync.units.consumed.calls++;
  lgl->cbs->units.consume.fun (lgl->cbs->units.consume.state, &units, &eou);
  if (units == eou) return 1;
  lgl->stats->sync.units.consumed.tried++;
  produce = lgl->cbs->units.produce.fun;
  lgl->cbs->units.produce.fun = 0;
  for (p = units; !lgl->mt && p < eou; p++) {
    elit = *p;
    erepr = lglerepr (lgl, elit);
    ext = lglelit2ext (lgl, erepr);
    assert (!ext->equiv);
    ilit = ext->repr;
    if (!ilit) continue;
    if (erepr < 0) ilit = -ilit;
    if (ilit == 1) continue;
    if (ilit == -1) val = -1;
    else {
      assert (abs (ilit) > 1);
      val = lglval (lgl, ilit);
      if (val && lglevel (lgl, ilit)) val = 0;
    }
    if (val == 1) continue;
    if (val == -1) {
      LOG (1, "mismatching synchronized external unit %d", elit);
      if (lgl->level > 0) lglbacktrack (lgl, 0);
      lglmt (lgl);
    } else if (!lglisfree (lgl, ilit)) continue;
    else {
      assert (!val);
      if (lgl->level > 0) lglbacktrack (lgl, 0);
      lglunit (lgl, ilit);
      LOG (2, "importing internal unit %d external %d",
	   lgl->tid, ilit, elit);
      count++;
    }
  }
  lgl->cbs->units.produce.fun = produce;
  if (lgl->cbs->units.consumed.fun)
    lgl->cbs->units.consumed.fun (lgl->cbs->units.consumed.state, count);
  if (count) lgl->stats->sync.units.consumed.actual++;
  if (lgl->mt) return 0;
  if (count) LOG (1, "imported %d units", count);
  if (!count) return 1;
  assert (!lgl->level);
  res = lglbcp (lgl);
  if(!res && !lgl->mt) lglmt (lgl);
  return res;
}

static int lglelitblockingoreliminated (LGL * lgl, int elit) {
  Ext * ext = lglelit2ext (lgl, elit);
  return ext->blocking || ext->eliminated;
}

static int lglsynclsexist (LGL * lgl) {
  int len, lit, blit, tag, other, other2;
  int * s, * p, * w, * eow;
  HTS * hts;
  len = lglcntstk (&lgl->clause);
  assert (!len || lgl->clause.top[-1]);
  if (len <= 1) return 0;
  s = lgl->clause.start;
  for (p = s + 1; p + 1 < lgl->clause.top; p++) {
    assert (lglmarked (lgl, *p) > 0);
    if (lglhts (lgl, *s)->count > lglhts (lgl, *p)->count)
      SWAP (int, *s, *p);
  }
  hts = lglhts (lgl, (lit = *s));
  assert (lglmarked (lgl, lit) > 0);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    if (tag == BINCS) {
      other = blit >> RMSHFT;
      if (lglmarked (lgl, other) > 0) return 1;
    } else {
      assert (tag == TRNCS);
      if (len <= 2) continue;
      other = blit >> RMSHFT;
      if (lglmarked (lgl, other) > 0) return 1;
      other2 = *p;
      if (lglmarked (lgl, other2) > 0) return 1;
    }
  }
  return 0;
}

static int lglsyncls (LGL * lgl) {
  int maxlevel, level, nonfalse, numtrue, res, delta, glue, consumed;
  int * cls, elit, erepr, tmp, ilit, len, newglue;
  const int * p;
  int64_t rate;
  if (lgl->mt) return 0;
  if (!lgl->cbs) return 1;
  if (!lgl->cbs->cls.consume.fun) return 1;
  assert (!lgl->simp);
  if (lgl->stats->confs < lgl->limits->sync.confs) return 1;
  delta = lgl->opts->synclsint.val;
  if (lgl->stats->sync.cls.consumed.calls) {
    rate = 100*lgl->stats->sync.cls.consumed.tried;
    rate /= lgl->stats->sync.cls.consumed.calls;
    LOG (2, "syncls tried/calls = %lld/%lld = %d%%",
      (LGLL) lgl->stats->sync.cls.consumed.tried,
      (LGLL) lgl->stats->sync.cls.consumed.calls,
      rate);
    if (rate) delta /= rate;
  }
  lgl->limits->sync.confs = lgl->stats->confs + delta;
  lgl->stats->sync.cls.consumed.calls++;
  consumed = 0;
RESTART:
  lgl->cbs->cls.consume.fun (lgl->cbs->cls.consume.state, &cls, &glue);
  if (!cls) return 1;
  lgl->stats->sync.cls.consumed.tried++;
  LOGCLS (2, cls, "trying to import external clause");
  assert (lglmtstk (&lgl->clause));
  maxlevel = nonfalse = numtrue = 0;
#ifndef NDEBUG
  for (p = cls; (elit = *p); p++) {
    ilit = lglimport (lgl, elit);
    if (abs (ilit) <= 1) continue;
    assert (!lglmarked (lgl, ilit));
  }
#endif
  for (p = cls; (elit = *p); p++) {
    erepr = lglerepr (lgl, elit);
    if (lglelitblockingoreliminated (lgl, erepr)) break;
    ilit = lglimport (lgl, erepr);
    if (!ilit) break;
    if (ilit == 1) break;
    if (ilit == -1) continue;
    tmp = lglifixed (lgl, ilit);
    if (tmp > 0) break;
    if (tmp < 0) continue;
    tmp = lglmarked (lgl, ilit);
    if (tmp > 0) continue;
    if (tmp < 0) break;
    lglpushstk (lgl, &lgl->clause, ilit);
    lglmark (lgl, ilit);
    tmp = lglval (lgl, ilit);
    if (tmp > 0) numtrue++;
    else if (!tmp) nonfalse++;
    else if ((level = lglevel (lgl, ilit)) > maxlevel) maxlevel = level;
  }
  res = 1;
  if (!elit && lglsynclsexist (lgl)) elit = INT_MAX;
  for (p = lgl->clause.start; p < lgl->clause.top; p++)
    lglunmark (lgl, *p);
  if (elit) goto DONE;
  len = lglcntstk (&lgl->clause);
  if (!numtrue && nonfalse <= 1) {
    if (len <= 1 || maxlevel <= 1) level = 0;
    else {
      level = 0;
      for (p = lgl->clause.start; p < lgl->clause.top; p++) {
	ilit = *p;
	tmp = lglval (lgl, ilit);
	assert (tmp <= 0);
	if (!tmp) continue;
	tmp = lglevel (lgl, ilit);
	if (tmp < maxlevel && tmp > level) level = tmp;
      }
    }
    if (level < lgl->level) {
      LOG (2, "importing clause requires to backtrack to level %d", level);
      lglbacktrack (lgl, level);
    }
  }
  lglpushstk (lgl, &lgl->clause, 0);
  newglue = glue;
  LOGCLS (2, lgl->clause.start,
    "successfully imported as glue %d redundant glue %d length %d clause",
    newglue, glue, len);
  lgl->stats->sync.cls.consumed.actual++;
  lgldrupligaddcls (lgl, 0);			// TODO?
  lgladdcls (lgl, REDCS, newglue, !numtrue);
  consumed++;
  if (lgl->mt) res = 0;
  else res = lglbcpsearch (lgl);
DONE:
  lglclnstk (&lgl->clause);
  if (res && lgl->opts->synclsall.val) goto RESTART;
  if (lgl->cbs->cls.consumed.fun)
    lgl->cbs->cls.consumed.fun (lgl->cbs->cls.consumed.state, consumed);
  return res;
}

static int lglprbpull (LGL * lgl, int lit, int probe) {
  AVar * av;
  assert (lgl->level == 1);
  av = lglavar (lgl, lit);
  if (av->mark) return 0;
  if (!lglevel (lgl, lit)) return 0;
  assert (lglevel (lgl, lit) == 1);
  av->mark = 1;
  lglpushstk (lgl, &lgl->seen, -lit);
  LOG (3, "pulled in literal %d during probing analysis", -lit);
  return 1;
}

static int lglprbana (LGL * lgl, int probe) {
  int open, lit, r0, r1, tag, red, other, res, * p, * rsn;
  assert (lgl->level == 1);
  assert (lgl->conf.lit);
  assert (lglmtstk (&lgl->seen));
  lit = lgl->conf.lit;
  r0 = lgl->conf.rsn[0], r1 = lgl->conf.rsn[1];
  open = lglprbpull (lgl, lit, probe);
  LOG (2, "starting probing analysis with reason of literal %d", lit);
  for (;;) {
    assert (lglevel (lgl, lit) == 1);
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      if (lglprbpull (lgl, other, probe)) open++;
      if (tag == TRNCS && lglprbpull (lgl, r1, probe)) open++;
    } else {
      assert (tag == LRGCS);
      red = r0 & REDCS;
      p = lglidx2lits (lgl, red, r1);
      while ((other = *p++)) open += lglprbpull (lgl, other, probe);
    }
    LOG (3, "open %d antecedents in probing analysis", open-1);
    assert (open > 0);
    while (!lglmarked (lgl, lit = lglpopstk (&lgl->trail)))
      lglunassign (lgl, lit);
    lglunassign (lgl, lit);
    if (!--open) { res = lit; break; }
    LOG (2, "analyzing reason of literal %d in probing analysis next", lit);
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0], r1 = rsn[1];
  }
  assert (res);
  if (res == probe)
    LOG (2, "probing analysis returns the probe %d as 1st UIP", probe);
  else
    LOG (2, "probing analysis returns different 1st UIP %d and not probe %d",
	 res, probe);
  lglpopnunmarkstk (lgl, &lgl->seen);
  return res;
}

static int lglederef (LGL * lgl, int elit) {
  int ilit, res;
  Ext * ext;
  assert (elit);
  if (abs (elit) > lgl->maxext) return -1;
  ext = lglelit2ext (lgl, elit);
  if (!(res = ext->val)) {
    assert (!ext->equiv);
    ilit = ext->repr;
    res = ilit ? lglcval (lgl, ilit) : -1;
  }
  if (elit < 0) res = -res;
  return res;
}

static int lgldecomp (LGL *); // TODO move

static int lglhasbin (LGL * lgl, int a, int b) {
  int blit, tag, other, res = 0;
  const int * w, * eow, * p;
  int64_t inc;
  HTS * ha, * hb;
  ha = lglhts (lgl, a);
  hb = lglhts (lgl, b);
  if (hb->count < ha->count) {
    SWAP (int, a, b); SWAP (HTS *, ha, hb);
  }
  w = lglhts2wchs (lgl, ha);
  eow = w + ha->count;
  for (p = w; !res && p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == OCCS) continue;
    if (tag == TRNCS || tag == LRGCS) { p++; continue; }
    assert (tag == BINCS);
    other = blit >> RMSHFT;
    if (other == b) res = 1;
  }
  inc = 2 + (int)(p - w);
  if (lgl->card) ADDSTEPS (card.steps, inc);
  if (lgl->simpleprobing) ADDSTEPS (prb.simple.steps, inc);
  return res;
}

static void lglwrkinit (LGL * lgl, int posonly, int fifo) {
  int size, lit;
  NEW (lgl->wrk, 1);
  lgl->wrk->fifo = fifo;
  size = lgl->wrk->size = lgl->nvars;
  if (posonly) {
    NEW (lgl->wrk->pos, size);
    lgl->wrk->posonly = 1;
  } else {
    NEW (lgl->wrk->pos, 2*size);
    lgl->wrk->pos += size;
    for (lit = -size + 1; lit < -1; lit++) lgl->wrk->pos[lit] = -1;
  }
  for (lit = 2; lit < size; lit++) lgl->wrk->pos[lit] = -1;
}

static void lglwrkreset (LGL * lgl) {
  lglrelstk (lgl, &lgl->wrk->queue);
  if (lgl->wrk->posonly) DEL (lgl->wrk->pos, lgl->wrk->size);
  else {
    lgl->wrk->pos -= lgl->wrk->size;
    DEL (lgl->wrk->pos, 2*lgl->wrk->size);
  }
  DEL (lgl->wrk, 1);
}

static void lglwrkcompact (LGL * lgl) {
  int i, j = 0, lit, tail = lglcntstk (&lgl->wrk->queue);
  for (i = lgl->wrk->head; i < tail; i++) {
    lit = lgl->wrk->queue.start[i];
    if (!lit) continue;
    assert (!lgl->wrk->posonly || 1 < lit);
    assert (1 < abs (lit) && abs (lit) < lgl->wrk->size);
    assert (lgl->wrk->pos[lit] == i);
    if (!lglisfree (lgl, lit)) {
      lgl->wrk->pos[lit] = -1;
      assert (lgl->wrk->count > 0);
      lgl->wrk->count--;
    } else {
      lgl->wrk->queue.start[j] = lit;
      lgl->wrk->pos[lit] = j++;
    }
  }
  lglrststk (&lgl->wrk->queue, j);
  lgl->wrk->head = 0;
}

static int lglwrktouched (LGL * lgl, int lit) {
  if (lgl->wrk->posonly) lit = abs (lit);
  return lgl->wrk->pos[lit] >= 0;
}

static int lglwrktouch (LGL * lgl, int lit) {
  int tail, pos;
  if (!lglisfree (lgl, lit)) return 1;
  if (lgl->donotsched) {
    if (lgl->ternresing && lglavar (lgl, lit)->donoternres) return 1;
    if (lgl->simpleprobing && lglavar (lgl, lit)->donotsimpleprobe) return 1;
  }
  if (lgl->wrk->posonly) lit = abs (lit);
  tail = lglcntstk (&lgl->wrk->queue);
  LOG (4, "work touch %d", lit);
  if ((pos = lgl->wrk->pos[lit]) >= 0) {
    assert (lgl->wrk->queue.start[pos] == lit);
    lgl->wrk->queue.start[pos] = 0;
  }
  lgl->wrk->count++;
  assert (lgl->wrk->count > 0);
  lgl->wrk->pos[lit] = tail;
  lglpushstk (lgl, &lgl->wrk->queue, lit);
  if (tail/2 > lgl->wrk->count) lglwrkcompact (lgl);
  return 1;
}

static int lglwrkdeq (LGL * lgl) {
  int res, pos;
  while ((pos = lgl->wrk->head) < lglcntstk (&lgl->wrk->queue)) {
    lgl->wrk->head++;
    res = lgl->wrk->queue.start[pos];
    if (!res) continue;
    lgl->wrk->queue.start[pos] = 0;
    assert (lgl->wrk->count > 0);
    lgl->wrk->count--;
    assert (lgl->wrk->pos[res] == pos);
    lgl->wrk->pos[res] = -1;
    if (lglisfree (lgl, res)) return res;
  }
  return 0;
}

static int lglwrkpop (LGL * lgl) {
  int res;
  while (lglcntstk (&lgl->wrk->queue) > lgl->wrk->head) {
    res = lglpopstk (&lgl->wrk->queue);
    if (!res) continue;
#ifndef NDEBUG
    {
      int pos = lglcntstk (&lgl->wrk->queue);
      assert (lgl->wrk->pos[res] == pos);
    }
#endif
    lgl->wrk->pos[res] = -1;
    if (lglisfree (lgl, res)) return res;
  }
  return 0;
}

static int lglwrknext (LGL * lgl) {
  return lgl->wrk->fifo ? lglwrkdeq (lgl) : lglwrkpop (lgl);
}

static int lglrandlitrav (LGL * lgl, int (*fun)(LGL*,int lit)) {
  int delta, mod, prev, first, ulit, count;
  if (lgl->nvars < 2) return 0;
  first = mod = 2*lgl->nvars;
  ulit = lglrand (lgl) % mod;
  delta = lglrand (lgl) % mod;
  if (!delta) delta++;
  while (lglgcd (delta, mod) > 1)
    if (++delta == mod) delta = 1;
  count = mod;
  LOG (2,
    "random literal traversal start %d delta %d mod %d",
     ulit, delta, mod);
  for (;;) {
    count--;
    assert (count >= 0);
    if (ulit >= 4 && !fun (lgl, lglilit (ulit))) return 0;
    prev = ulit;
    ulit += delta;
    if (ulit >= mod) ulit -= mod;
    if (ulit == first) { assert (!count); break; }
    if (first == mod) first = prev;
  }
  return 1;
}

static void lglsimpleprobeinit (LGL * lgl) {
  int idx, rem = 0, ret = 0;
  for (idx = 2; idx < lgl->nvars; idx++) lgl->avars[idx].equiv = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    if (lglavar (lgl, idx)->donotsimpleprobe) ret++; else rem++;
  }
  if (!rem) {
    ret = 0;
    for (idx = 2; idx < lgl->nvars; idx++) {
      if (!lglisfree (lgl, idx)) continue;
      lglavar (lgl, idx)->donotsimpleprobe = 0;
      rem++;
    }
  }
  if (!ret)
    lglprt (lgl, 1,
      "[simpleprobe-%d] all %d free variables schedulable",
      lgl->stats->prb.simple.count, rem);
  else
    lglprt (lgl, 1,
      "[simpleprobe-%d] %d schedulable variables %.0f%%",
      lgl->stats->prb.simple.count, rem, lglpcnt (rem, lglrem (lgl)));
  lglwrkinit (lgl, 0, 1);
  assert (!lgl->donotsched), lgl->donotsched = 1;
  lglrandlitrav (lgl, lglwrktouch);
  assert (lgl->donotsched), lgl->donotsched = 0;
  assert (lgl->opts->prbsimple.val);
  lglchkirrstats (lgl);
}

static void lglsimpleprobereset (LGL * lgl, int nvars) {
  const int * p;
  int idx;
  lglrelstk (lgl, &lgl->sprb->units);
  lglrelstk (lgl, &lgl->sprb->impls);
  lglrelstk (lgl, &lgl->sprb->eqs);
  for (idx = 2; idx < lgl->nvars; idx++) lgl->avars[idx].donotsimpleprobe = 1;
  for (p = lgl->wrk->queue.start; p < lgl->wrk->queue.top; p++)
    lgl->avars[abs (*p)].donotsimpleprobe = 0;
  lglwrkreset (lgl);
  lglrelstk (lgl, &lgl->sprb->counted);
  lglrelstk (lgl, &lgl->sprb->marked);
  assert (nvars == lgl->nvars);
  lgl->sprb->spes -= nvars;
  DEL (lgl->sprb->spes, 2*nvars);
}

static int lglflush (LGL *);
static void lgldense (LGL *, int rmredbintrn);
static void lglsparse (LGL *);

static int lglsimpleprobeunits (LGL * lgl) {
  const int * p;
  int lit, res;
  Val val;
  res = 0;
  lglchkirrstats (lgl);
  for (p = lgl->sprb->units.start; !lgl->mt && p < lgl->sprb->units.top; p++) {
    lit = *p;
    val = lglval (lgl, lit);
    if (val > 0) continue;
    lgl->stats->prb.simple.failed++;
    if (val < 0) {
      lgldrupligaddclsarg (lgl, REDCS, lit, 0);
      LOG (1, "inconsistent unit %d", lit);
      lglmt (lgl);
    } else {
      lglunit (lgl, lit);
      res++;
      if (!lglflush (lgl)) {
	LOG (1, "propagating simple HBR unit %d results in conflict", lit);
	lglmt (lgl);
      }
    }
  }
  return res;
}

static int lglsimpleprobeimpls (LGL * lgl) {
  int a, b, res;
  res = 0;
  while (!lglmtstk (&lgl->sprb->impls)) {
    b = lglpopstk (&lgl->sprb->impls);
    a = lglpopstk (&lgl->sprb->impls);
    if (lglval (lgl, a) || lglval (lgl, b)) continue;
    if (lglhasbin (lgl, a, b)) continue;
    LOG (2, "adding previously detected hyper binary resolvent %d %d", a, b);
    lgldrupligaddclsarg (lgl, REDCS, a, b, 0);
    res++;
    lgl->stats->hbr.cnt++;
    lgl->stats->hbr.simple++;
    (void) lglwchbin (lgl, a, b, REDCS);
    (void) lglwchbin (lgl, b, a, REDCS);
    lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
    lglwrktouch (lgl, -a);
    lglwrktouch (lgl, -b);
    if (!lglhasbin (lgl, -a, -b)) continue;
    LOG (2, "found equivalent literals %d and %d", -a, b);
    lglpushstk (lgl, &lgl->sprb->eqs, -a);
    lglpushstk (lgl, &lgl->sprb->eqs, b);
  }
  return res;
}

static int lglhasonlybin (LGL * lgl, int lit, int other) {
  HTS * hts = lglhts (lgl, lit);
  const int * w;
  int blit;
  if (hts->count != 1) return 0;
  w = lglhts2wchs (lgl, hts);
  blit = *w;
  if ((blit & MASKCS) != BINCS) return 0;
  return (blit >> RMSHFT) == other;
}

static int lglsimpleprobemerged (LGL * lgl, int a, int b) {
  return lglhasonlybin (lgl, -a, b) && lglhasonlybin (lgl, -b, a);
}

static int lglflushclauses (LGL * lgl, int lit);

static void lglsimpleprobeclscp (LGL * lgl, int nonrepr, int repr, Stk * stk) {
  int blit, tag, red, other, other2, lidx, count, found, start, trivial;
  const int * p, * w, * eow, * c, * q;
  HTS * hts = lglhts (lgl, nonrepr);
  assert (abs (repr) < abs (nonrepr));
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  count = 0;
  for (p = w; p < eow; p++) {
    INCSTEPS (prb.simple.steps);
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    start = lglcntstk (stk);
    trivial = 0;
    red = blit & REDCS;
    lglpushstk (lgl, stk, red);
    lglpushstk (lgl, stk, repr);
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      if (other == -repr) trivial = 1;
      else if (other != repr) lglpushstk (lgl, stk, other);
      if (tag == TRNCS) {
	other2 = *p;
	if (other2 == -repr) trivial = 1;
	else if (other2 != repr) lglpushstk (lgl, stk, other2);
      }
    } else {
      assert (tag == OCCS);
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, red, lidx);
      found = 0;
      for (q = c; !trivial && (other = *q); q++) {
	if (other >= NOTALIT) trivial = 1;
	else if (other == nonrepr) found++;
	else if (other == -repr) trivial = 1;
	else if (other != repr) lglpushstk (lgl, stk, other);
      }
      assert (trivial || found);
    }
    if (trivial) lglrststk (stk, start);
    else lglpushstk (lgl, stk, 0), count++;
  }
  LOG (2, "copied %d clauses with %d replacing %d by %d",
       count, nonrepr, nonrepr, repr);
}

static int lglsimpleprobebinexists (LGL * lgl, int a, int b) {
  const int * p, * w, * eow;
  int blit, tag, red, other;
  HTS * hts;
  hts = lglhts (lgl, a);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    red = blit & REDCS;
    if (red) continue;
    other = blit >> RMSHFT;
    if (other == b) return 1;
  }
  return 0;
}

static int lglsimpleprobetrnexists (LGL * lgl, int a, int b, int c) {
  int blit, tag, red, other, other2;
  const int * p, * w, * eow;
  HTS * hts;
  hts = lglhts (lgl, a);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    other = blit >> RMSHFT;
    if (tag == BINCS) {
      if (other == b) return 1;
      if (other == c) return 1;
    } else if (tag == TRNCS) {
      other2 = *p;
      if (other == b && other2 == c) return 1;
      if (other == c && other2 == b) return 1;
    }
  }
  return 0;
}

static int lglsimpleprobelrgexists (LGL * lgl, int a) {
  int blit, tag, red, other, other2, lidx, res;
  const int * p, * w, * eow, * c, * q;
  HTS * hts;
  for (p = lgl->clause.start; p + 1 < lgl->clause.top; p++) {
    other = *p;
    assert (!lglsignedmarked (lgl, other));
    lglsignedmark (lgl, other);
  }
  assert (lglsignedmarked (lgl, a));
  hts = lglhts (lgl, a);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  res = 0;
  for (p = w; !res && p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red || tag == LRGCS) continue;
    other = blit >> RMSHFT;
    if (tag == BINCS) {
      res = lglsignedmarked (lgl, other);
    } else if (tag == TRNCS) {
      other2 = *p;
      res = lglsignedmarked (lgl, other) && lglsignedmarked (lgl, other2);
    } else {
      assert (tag == OCCS);
      lidx = other;
      c = lglidx2lits (lgl, 0, lidx);
      for (q = c; (other = *q); q++)
	if (!lglsignedmarked (lgl, other)) break;
      res = !other;
    }
  }
  for (p = lgl->clause.start; p + 1 < lgl->clause.top; p++) 
    lglunmark (lgl, *p);
  return res;
}

static int lglsimpleprobeclausexists (LGL * lgl) {
  int len = lglcntstk (&lgl->clause) - 1, a, b, c, * p, * s, res;
  assert (len >= 0);
  assert (!lgl->clause.top[-1]);
  s = lgl->clause.start;
  for (p = s + 1; p + 1 < lgl->clause.top; p++)
    if (lglhts (lgl, *s)->count > lglhts (lgl, *p)->count)
      SWAP (int, *s, *p);
  a = lgl->clause.start[0];
  if (len == 2) {
    b = lgl->clause.start[1];
    res = lglsimpleprobebinexists (lgl, a, b);
  } else if (len == 3) {
    b = lgl->clause.start[1];
    c = lgl->clause.start[2];
    res = lglsimpleprobetrnexists (lgl, a, b, c);
  } else if (len > 3)
    res = lglsimpleprobelrgexists (lgl, a);
  else res = 0;
  if (res) LOG (2, "will not add already existing clause");
  return res;
}

static void lglsimpleprobeaddclausesonstack (LGL * lgl, Stk * stk) {
  int count, red, lit, size;
  const int * c, * p, * q;
  count = 0;
  for (c = stk->start; c < stk->top; c = p + 1) {
    red = *(p = c);
    if (p[1] == REMOVED) {
      p++;
      while (p + 1 < stk->top && p[1] == REMOVED) p++;
      continue;
    }
    assert (!red || red == REDCS);
    assert (lglmtstk (&lgl->clause));
    do {
      lit = *++p;
      lglpushstk (lgl, &lgl->clause, lit);
    } while (lit);
    if (!lglisimpcls (lgl) && !lglsimpleprobeclausexists (lgl)) {
      lgldrupligaddcls (lgl, REDCS);
      q = lgl->clause.start;
      size = lglcntstk (&lgl->clause);
      assert (size > 0);
      assert (!q[size-1]);
      size--;
      if (size > 2 && lgl->opts->prbsimple.val >= 3)
	while ((lit = *q++))
	  lglwrktouch (lgl, lit);
      if (size == 2 && lgl->opts->prbsimple.val >= 2)
	lglwrktouch (lgl, -q[0]),
	lglwrktouch (lgl, -q[1]);
      lgladdcls (lgl, red, 0, 1);
      count++;
    }
    lglclnstk (&lgl->clause);
    if (!lglflush (lgl)) break;
  }
  LOG (2, "added %d non-trivial clauses", count);
}

static void lglsimpleprobeaddprbincls (LGL * lgl, int a, int b) {
  assert (lgl->probing);
  assert (lglmtstk (&lgl->clause));
  assert (abs (a) != abs (b));
  assert (!lglval (lgl, a));
  assert (!lglval (lgl, b));
  lglpushstk (lgl, &lgl->clause, a);
  lglpushstk (lgl, &lgl->clause, b);
  lglpushstk (lgl, &lgl->clause, 0);
  if (!lglsimpleprobeclausexists (lgl)) {
    LOG (2, "added simple probing connecting binary clause", a, b);
    lgldrupligaddcls (lgl, REDCS);
    lgladdcls (lgl, 0, 0, 1);
  }
  lglclnstk (&lgl->clause);
}

static int lglcmpilit (int * a, int * b) {
  int res, l = *a, k = *b;
  if ((res = abs (l) - abs (k))) return res;
  return l - k;
}

static int lglcmpcls (LGL * lgl, const int * c, const int * d) {
  const int * p, * q;
  if (*c >= REMOVED && *d >= REMOVED) return c - d;
  if (*c >= REMOVED) return 1;
  if (*d >= REMOVED) return -1;
  for (p = c, q = d; *p && *q == *p; p++, q++)
    ;
  return *p - *q;
}

static int lglcmpsz (LGL * lgl, const int * start, PSz * p, PSz * q) {
  const int * c, * d;
  int res;
  if ((res = p->size - q->size)) return res;
  c = start + p->pos, d = start + q->pos;
  if ((res = lglcmpcls (lgl, c, d))) return res;
  if ((res = c[-1] - d[-1])) return res;
  return p->pos - q->pos;
}

#define LGLCMPSZ(A,B) (lglcmpsz(lgl, start, (A), (B)))

static void lglrmdupclsonstack (LGL * lgl, Stk * stk, Stk * sort) {
  int * start, * c, * p, * d, pos, size, i;
  PSz * ps;
  lglclnstk (sort);
  start = stk->start;
  for (c = start; c < stk->top; c = p + 1) {
    c++;
    assert (c < stk->top);
    pos = c - start;
    size = 0;
    for (p = c; *p; p++) size++;
    SORT (int, c, size, lglcmpilit);
    lglpushstk (lgl, sort, pos);
    lglpushstk (lgl, sort, size);
  }
  size = lglcntstk (sort)/2;
  if (size <= 1) return;
  ps = (PSz *) sort->start;
  SORT (PSz, ps, size, LGLCMPSZ);
  for (i = 1; i < size; i++) {
    if (ps[i-1].size != ps[i].size) continue;
    c = stk->start + ps[i-1].pos;
    d = stk->start + ps[i].pos;
    if (lglcmpcls (lgl, c, d)) continue;
    LOGCLS (4, d, "not copying duplicate %s clause", lglred2str (d[-1]));
    while (*d) *d++ = REMOVED;
    *d = REMOVED;
  }
}

static void lglsimpleprobemerge (LGL * lgl, int repr, int nonrepr) {
  const int druplig = lgl->opts->druplig.val;
  Val valrepr, valnonrepr;
  Stk stk, sort;
  int unit;
  lglchkirrstats (lgl);
  lgl->stats->prb.simple.eqs++;
  assert (abs (repr) < abs (nonrepr));
  lglavar (lgl, nonrepr)->equiv = 1;
  CLR (stk); CLR (sort);
  if (druplig) {
    lgldrupligaddclsarg (lgl, REDCS, repr, -nonrepr, 0),
    lgldrupligaddclsarg (lgl, REDCS, -repr, nonrepr, 0);
  }
  lglsimpleprobeclscp (lgl, nonrepr, repr, &stk);
  lglsimpleprobeclscp (lgl, -nonrepr, -repr, &stk);
  lglrmdupclsonstack (lgl, &stk, &sort);
  lglsimpleprobeaddclausesonstack (lgl, &stk);
  lglrelstk (lgl, &sort);
  lglrelstk (lgl, &stk);
  lglflushclauses (lgl, nonrepr);
  lglflushclauses (lgl, -nonrepr);
  if (lgl->mt) goto FIXDRUPLIG;
  valrepr = lglval (lgl, repr);
  valnonrepr = lglval (lgl, nonrepr);
  if (valrepr && valnonrepr == valrepr) goto FIXDRUPLIG;
  if (valrepr && valrepr == -valrepr) {
    LOG (1, "equality between %d and %d became inconsistent", repr, nonrepr);
    lglmt (lgl);
    goto FIXDRUPLIG;
  }
  if (valrepr && !valnonrepr) unit = valrepr < 0 ? -nonrepr : nonrepr;
  else if (!valrepr && valnonrepr) unit = valnonrepr < 0 ? -repr : repr;
  else unit = 0, assert (!valrepr), assert (!valnonrepr);
  if (unit) {
    LOG (1, "new unit %d from equality between %d and %d", unit, repr, nonrepr);
    lglunit (lgl, unit);
    (void) lglflush (lgl);
  } else lglsimpleprobeaddprbincls (lgl, repr, -nonrepr),
	 lglsimpleprobeaddprbincls (lgl, -repr, nonrepr);
  lglchkirrstats (lgl);
FIXDRUPLIG:
  if (druplig) {
    lgldrupligdelclsarg (lgl, repr, -nonrepr, 0),
    lgldrupligdelclsarg (lgl, -repr, nonrepr, 0);
  }
}

static int lglsimpleprobeqs (LGL * lgl) {
  int a, b, res;
  res = 0;
  while (!lgl->mt && !lglmtstk (&lgl->sprb->eqs)) {
    a = lglpopstk (&lgl->sprb->eqs);
    b = lglpopstk (&lgl->sprb->eqs);
    if (lglval (lgl, a)) continue;
    assert (!lglval (lgl, b));
    assert (abs (a) != abs (b));
    if (lglsimpleprobemerged (lgl, a, b)) continue;
    if (abs (b) < abs (a)) SWAP (int, a, b);
    lglsimpleprobemerge (lgl, a, b);
    res++;
  }
  return res;
}

static SPE * lglspe (LGL * lgl, int lit) {
  assert (2 <= abs (lit) && abs (lit) < lgl->nvars);
  return lgl->sprb->spes + lit;
}

static void lglsimpleprobehbr (LGL * lgl, int touched, const int * c) {
  int blit, tag, lit, other, count, val, maxcount, rem, first, second;
  const int * p, * q, * w, * eow;
  unsigned sum, tmp;
  SPE * spe;
  HTS * hts;
  first = second = count = sum = 0;
  for (p = c; (lit = *p); p++) {
    if (lglwrktouched (lgl, lit)) return;
    if ((val = lglval (lgl, lit)) > 0) return;
    if (val < 0) continue;
    if (!first) first = lit;
    else if (!second) second = lit;
    sum += (unsigned) lit;
    count++;
  }
  if (count == 2) {
    assert (first && second);
    if (lglhasbin (lgl, -first, -second)) {
      LOG (2, "found equivalent literals %d and %d", -first, second);
      lglpushstk (lgl, &lgl->sprb->eqs, -first);
      lglpushstk (lgl, &lgl->sprb->eqs, second);
      goto DONE;
    }
  }
  rem = count;
  maxcount = 0;
  assert (lglmtstk (&lgl->sprb->counted));
  for (p = c; (lit = *p); p++) {
    if (INCSTEPS (prb.simple.steps) >= lgl->limits->prb.steps) goto DONE;
    val = lglval (lgl, lit);
    assert (val <= 0);
    if (val) continue;
    hts = lglhts (lgl, -lit);
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    assert (lglmtstk (&lgl->sprb->marked));
    for (q = w; q < eow; q++) {
      if (INCSTEPS (prb.simple.steps) >= lgl->limits->prb.steps) goto DONE;
      blit = *q;
      tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) q++;
      if (tag != BINCS) continue;
      other = blit >> RMSHFT;
      val = lglval (lgl, other);
      assert (val >= 0);
      if (val) continue;
      if ((spe = lglspe (lgl, other))->mark) continue;
      if (lglspe (lgl, -other)->mark) {
	LOG (2, "unit %d through very simple hyper binary resolution", -lit);
	lglpushstk (lgl, &lgl->sprb->units, -lit);
	goto DONE;
      }
      if (!spe->count) lglpushstk (lgl, &lgl->sprb->counted, other);
      spe->sum += (unsigned) lit;
      spe->count++;
      spe->mark = 1;
      lglpushstk (lgl, &lgl->sprb->marked, other);
      if (spe->count > maxcount) maxcount = spe->count;
    }
    while (!lglmtstk (&lgl->sprb->marked)) {
      other = lglpopstk (&lgl->sprb->marked);
      spe = lglspe (lgl, other);
      assert (spe->mark);
      spe->mark = 0;
    }
    rem--;
    assert (maxcount + rem <= count);
    if (maxcount + rem + 1 < count) goto DONE;
  }
  if (count <= 2) goto DONE;
  for (q = lgl->sprb->counted.start; q < lgl->sprb->counted.top; q++) {
    other = *q;
    assert (!lglval (lgl, other));
    spe = lglspe (lgl, other);
    assert (spe->count <= count);
    if (spe->count == count) {
      LOG (2, "unit %d through simple hyper binary resolution", other);
      lglpushstk (lgl, &lgl->sprb->units, other);
    } else if (spe->count + 1 == count) {
      tmp = sum - spe->sum;
      lit = (int) tmp;
      assert (2 <= abs (lit) && abs (lit) < lgl->nvars);
      if (abs (lit) != abs (other) && !lglhasbin (lgl, other, lit)) {
	LOG (2, "simple hyper binary resolvent %d %d", other, lit);
	lglpushstk (lgl, &lgl->sprb->impls, other);
	lglpushstk (lgl, &lgl->sprb->impls, lit);
      }
    }
  }
  for (p = c; (lit = *p); p++) {
    if (lglval (lgl, lit)) continue;
    spe = lglspe (lgl, lit);
    if (spe->count + 2 != count) continue;
    tmp = sum - spe->sum;
    tmp -= (unsigned) lit;
    other = (int) tmp;
    assert (2 <= abs (other) && abs (other) < lgl->nvars);
    if (abs (lit) != abs (other) && !lglhasbin (lgl, other, lit)) {
      LOG (2, "self-subsuming hyper binary resolvent %d %d", other, lit);
      lglpushstk (lgl, &lgl->sprb->impls, other);
      lglpushstk (lgl, &lgl->sprb->impls, lit);
    }
  }
DONE:
  while (!lglmtstk (&lgl->sprb->counted)) {
    lit = lglpopstk (&lgl->sprb->counted);
    spe = lglspe (lgl, lit);
    CLRPTR (spe);
  }
  lglclnstk (&lgl->sprb->marked);
}

static void lglpushnmarkseen (LGL * lgl, int lit) {
  lglpushstk (lgl, &lgl->seen, lit);
  lglmarkunmarked (lgl, lit);
}

static void lglsignedmarknpushseen (LGL * lgl, int lit) {
  lglsignedmark (lgl, lit);
  lglpushstk (lgl, &lgl->seen, lit);
}

static void lglsimpleliftmark (LGL * lgl, int root, int level) {
  const int * p, * w, * eow;
  int blit, tag, other;
  HTS * hts;
  INCSTEPS (prb.simple.steps);
  assert (level > 0);
  assert (lglsignedmarked (lgl, -root));
  LOG (3, "next simple lifting marking from %d at level %d", root, level);
  hts = lglhts (lgl, root);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    other = blit >> RMSHFT;
    if (lglsignedmarked (lgl, other)) continue;
    lglsignedmarknpushseen (lgl, other);
    LOG (4, "next simple lifting marking from %d at level %d marked %d", 
         root, level, other);
    if (level > 1) lglsimpleliftmark (lgl, -other, level-1);
  }
}

static void lglsimpleliftcollect (LGL * lgl, int root, int start, int level) {
  const int * p, * w, * eow;
  int blit, tag, other;
  HTS * hts;
  INCSTEPS (prb.simple.steps);
  assert (level > 0);
  LOG (3, "next simple lifting collecting from %d at level %d", start, level);
  hts = lglhts (lgl, start);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    other = blit >> RMSHFT;
    if (other == -root) continue;
    if (lglsignedmarked (lgl, other)) {
      LOG (2, "simple lifted unit %d with root %d", other, root);
      lglpushstk (lgl, &lgl->sprb->units, other);
    } else if (other != root && lglsignedmarked (lgl, -other)) {
      LOG (2, "found equivalent literals %d and %d", root, other);
      lglpushstk (lgl, &lgl->sprb->eqs, root);
      lglpushstk (lgl, &lgl->sprb->eqs, other);
    } 
    if (level > 1) lglsimpleliftcollect (lgl, root, -other, level-1);
  }
}

static void lglsimplelift (LGL * lgl, int root) {
  int count, pos, neg;
  pos = lglhts (lgl, root)->count;
  neg = lglhts (lgl, -root)->count;
  if (neg < pos) root = -root;
  LOG (2, "next simple lifting %d", root);
  assert (lglmtstk (&lgl->seen));
  assert (!lglsignedmarked (lgl, -root));
  lglsignedmarknpushseen (lgl, -root);
  lglsimpleliftmark (lgl, root, lgl->opts->prbsimpleliftdepth.val);
  count = lglcntstk (&lgl->seen);
  LOG (3, "simple probing lifting marked %d literals for root %d", 
       count, root);
  if (!count) return;
  lglsimpleliftcollect (lgl, root, -root, lgl->opts->prbsimpleliftdepth.val);
#ifndef NLGLOG
  {
    int units = lglcntstk (&lgl->sprb->units);
    int eqs = lglcntstk (&lgl->sprb->eqs);
    assert (!(eqs & 1));
    eqs >>= 1;
    LOG (3, "found %d units through simple lifting for %d", units, root);
    LOG (3, "found %d equivalences through simple lifting for %d", eqs, root);
  }
#endif
  lglpopnunmarkstk (lgl, &lgl->seen);
}

static void lglsimpleprobelit (LGL * lgl, int lit) {
  int blit, tag, other, other2, red, lidx, cls[4];
  const int * p, * w, * eow, * c;
  HTS * hts;
  lgl->stats->prb.simple.probed++;
  assert (!lglval (lgl, lit));
  lglclnstk (&lgl->sprb->units);
  lglclnstk (&lgl->sprb->impls);
  if (!lglwrktouched (lgl, -lit)) lglsimplelift (lgl, lit);
  LOG (2, "next simple probing %d", lit);
  hts = lglhts (lgl, lit);
  if (!hts->count) return;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    if (INCSTEPS (prb.simple.steps) >= lgl->limits->prb.steps) goto DONE;
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == BINCS || tag == LRGCS) continue;
    if (tag == TRNCS) {
      other = blit >> RMSHFT;
      if (lglval (lgl, other)) continue;
      other2 = *p;
      if (lglval (lgl, other2)) continue;
      cls[0] = lit, cls[1] = other, cls[2] = other2, cls[3] = 0;
      lglsimpleprobehbr (lgl, lit, cls);
    } else {
      assert (tag == OCCS);
      red = (blit & REDCS);
      lidx = (blit >> RMSHFT);
      c = lglidx2lits (lgl, red, lidx);
      lglsimpleprobehbr (lgl, lit, c);
    }
  }
DONE:
  assert (lglmtstk (&lgl->seen));
  lglpopnunmarkstk (lgl, &lgl->seen);
}

static void lglprtsimpleproberem (LGL * lgl) {
  int idx, ret = 0, rem = 0, sum;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    if (lglavar (lgl, idx)->donotsimpleprobe) ret++; else rem++;
  }
  if (rem) {
    sum = rem + ret;
    lglprt (lgl, 1,
      "[simpleprobe-%d] %d variables remain %.0f%% (%d retained %.0f%%)",
      lgl->stats->prb.simple.count,
      rem, lglpcnt (rem, sum),
      ret, lglpcnt (ret, sum));
  } else {
    lglprt (lgl, 1,
      "[simpleprobe-%d] fully completed simple probing",
      lgl->stats->prb.simple.count);
    for (idx = 2; idx < lgl->nvars; idx++)
      lglavar (lgl, idx)->donotsimpleprobe = 0;
  }
}

static int64_t lglirrlits (LGL * lgl) { return lgl->stats->irr.lits.cur; }

static int64_t lglredlits (LGL * lgl) {
  int64_t res = 2*lgl->stats->red.bin + 3*lgl->stats->red.trn;
  int glue;
  for (glue = 0; glue <= MAXGLUE; glue++) {
    res += lglcntstk (lgl->red + glue);
    res -= 2*lgl->stats->lir[glue].clauses;
  }
  return res;
}

static int lglszpenaux (LGL * lgl, int litstoo, int redtoo) {
  int64_t size64;
  int res;
  size64 = lgl->stats->irr.clauses.cur;
  if (litstoo) size64 += lglirrlits (lgl)/4;
  if (redtoo) {
    size64 += lgl->stats->irr.clauses.cur;
    if (litstoo) size64 += lglredlits (lgl)/4;
  }
  assert (size64 >= 0);
  size64 /= lgl->opts->sizepen.val;
  if (size64 >= INT_MAX) res = 32;
  else res = lglceild ((int) size64);
  if (res < 0) res = 0;
  if (res > lgl->opts->sizemaxpen.val) res = lgl->opts->sizemaxpen.val;
  return res;
}

static int lglszpen (LGL * lgl) { return lglszpenaux (lgl, 0, 0); }

#ifndef NLGLYALSAT

static int lglitszpen (LGL * lgl) {
  int res = lglceild (lgl->stats->irr.lits.cur/lgl->opts->sizepen.val);
  if (res < 0) res = 0;
  if (res > lgl->opts->sizemaxpen.val + 2)
    res = lgl->opts->sizemaxpen.val + 2;
  return res;
}

#endif

static int64_t lglvisearch (LGL * lgl) {
  int64_t res = lgl->stats->visits.search;
  assert (res >= lgl->limits->inc.visits);
  res -= lgl->limits->inc.visits;
  return res;
}

static void lglsetprbsimplelim (LGL * lgl) {
  int64_t limit, irrlim;
  int pen, szpen;
  if (lgl->opts->prbsimplertc.val || lgl->opts->prbrtc.val) {
    lgl->limits->prb.steps = LLMAX;
    lglprt (lgl, 1,
      "[simpleprobe-%d] really no limit (run to completion)", 
      lgl->stats->prb.simple.count);
  } else {
    limit = (lgl->opts->prbsimplereleff.val*lglvisearch (lgl))/1000;
    if (limit < lgl->opts->prbsimplemineff.val) 
      limit = lgl->opts->prbsimplemineff.val;
    if (lgl->opts->prbsimplemaxeff.val >= 0 &&
        limit > lgl->opts->prbsimplemaxeff.val)
      limit = lgl->opts->prbsimplemaxeff.val;
    if (lgl->stats->prb.simple.count <= 1 &&
        lgl->opts->boost.val &&
        lgl->opts->prbsimpleboost.val > 1) {
      lglprt (lgl, 1,
	"[simpleprobe-%d] boosting simple probing limit by %d",
	lgl->stats->prb.simple.count, lgl->opts->prbsimpleboost.val);
      limit *= lgl->opts->prbsimpleboost.val;
    }
    limit >>= (pen = lgl->limits->prb.simple.pen + (szpen = lglszpen (lgl)));
    irrlim = (2*lgl->stats->irr.clauses.cur) >> szpen;
    if (lgl->opts->irrlim.val && limit < irrlim) {
      limit = irrlim;
      lglprt (lgl, 1,
  "[simpleprobe-%d] limit %lld based on %d irredundant clauses penalty %d",
	lgl->stats->prb.simple.count,
	(LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
    } else
      lglprt (lgl, 1,
	"[simpleprobe-%d] limit %lld penalty %d = %d + %d",
	lgl->stats->prb.simple.count, (LGLL) limit,
	pen, lgl->limits->prb.simple.pen, szpen);
    lgl->limits->prb.steps = lgl->stats->prb.simple.steps + limit;
  }
}

static int lgldelaying (LGL * lgl, const char * name, int * delptr) {
  if (!*delptr) return 0;
  *delptr -= 1;
  lglprt (lgl, 2,
    "[%s-delayed] skipping this scheduled invocation and %d more",
    name, *delptr);
  return 1;
}

static int lglsimpleprobe (LGL * lgl) {
  int deltarem, nunits, hbrs, neqs, oldrem = lglrem (lgl);
  int lit, success, nvars;

  if (lgldelaying (lgl, "simpleprobe",
        &lgl->limits->prb.simple.del.rem)) return 1;

  lglstart (lgl, &lgl->times->prb.simple);
  lgl->stats->prb.simple.count++;

  assert (!lgl->simp && !lgl->probing && !lgl->simpleprobing);
  lgl->simp = lgl->probing = lgl->simpleprobing = 1;


  NEW (lgl->sprb, 1);

  if (lgl->level > 0) lglbacktrack (lgl, 0);
  lglgc (lgl);
  assert (lgl->frozen);
  lgldense (lgl, 0);
  lglsimpleprobeinit (lgl);
  lglsetprbsimplelim (lgl);
  neqs = hbrs = nunits = 0;

  nvars = lgl->nvars;
  NEW (lgl->sprb->spes, 2*nvars);
  lgl->sprb->spes += nvars;

  while (!lgl->mt && (lit = lglwrknext (lgl))) {
    if (INCSTEPS (prb.simple.steps) >= lgl->limits->prb.steps) break;
    if (!lglisfree (lgl, lit)) continue;
    if (lglavar (lgl, lit)->equiv) continue;
    lglsimpleprobelit (lgl, lit);
    if (lgl->mt) break;
    lglchkirrstats (lgl);
    nunits += lglsimpleprobeunits (lgl);
    if (lgl->mt) break;
    hbrs += lglsimpleprobeimpls (lgl);
    if (lgl->mt) break;
    neqs += lglsimpleprobeqs (lgl);
    if (!lglflush (lgl)) break;
    if (lglterminate (lgl)) break;
    if (!lglsyncunits (lgl)) break;
  }

  lglsimpleprobereset (lgl, nvars);
  lglsparse (lgl);
  if (!lgl->mt) lgldecomp (lgl);

  DEL (lgl->sprb, 1);

  deltarem = oldrem - lglrem (lgl);
  success = deltarem || hbrs || nunits;
  LGLUPDPEN (prb.simple, deltarem);
  lglprtsimpleproberem (lgl);

  lglprt (lgl, 1 + !success,
    "[simpleprobe-%d] removed %d variables, found %d hbrs, %d units",
    lgl->stats->prb.simple.count, deltarem, hbrs, nunits);

  assert (lgl->simp && lgl->probing && lgl->simpleprobing);
  lgl->simp = lgl->probing = lgl->simpleprobing = 0;
  lglrep (lgl, 2, 'p');
  lglstop (lgl);
  return !lgl->mt;
}

static int lglmvbcls (LGL * lgl, int a, int b) {
  int res = 0;
  assert (abs (a) != abs (b));
  assert (!lglval (lgl, a));
  assert (!lglval (lgl, b));
  assert (lglmtstk (&lgl->clause)); 
  lglpushstk (lgl, &lgl->clause, a);
  lglpushstk (lgl, &lgl->clause, b);
  lglpushstk (lgl, &lgl->clause, 0);
  if (!lglsimpleprobeclausexists (lgl)) {
    LOG (2, "moving redundant binary clause %d %d", a, b);
    lgldrupligaddcls (lgl, REDCS);
    lgladdcls (lgl, REDCS, 0, 1);
    res = 1;
  }
  lglclnstk (&lgl->clause);
  lgl->stats->moved.bin++;
  return res;
}

static int lglrmvbcls (LGL * lgl, int a, int b) {
  lglrmbcls (lgl, a, b, 0);
  if (lgl->opts->move.val) return lglmvbcls (lgl, a, b);
  return 0;
}

static int lglmvtcls (LGL * lgl, int a, int b, int c) {
  int res = 0;
  assert (abs (a) != abs (b));
  assert (abs (a) != abs (c));
  assert (abs (b) != abs (c));
  assert (lglmtstk (&lgl->clause)); 
  lglpushstk (lgl, &lgl->clause, a);
  lglpushstk (lgl, &lgl->clause, b);
  lglpushstk (lgl, &lgl->clause, c);
  lglpushstk (lgl, &lgl->clause, 0);
  if (!lglsimpleprobeclausexists (lgl)) {
    LOG (2, "moving redundant ternary clause %d %d %d", a, b, c);
    lgldrupligaddcls (lgl, REDCS);
    lgladdcls (lgl, REDCS, 0, 1);
    res = 1;
  }
  lglclnstk (&lgl->clause);
  lgl->stats->moved.trn++;
  return res;
}

static int lglrmvtcls (LGL * lgl, int a, int b, int c) {
  assert (abs (a) != abs (b));
  assert (abs (a) != abs (c));
  assert (abs (b) != abs (c));
  lglrmtcls (lgl, a, b, c, 0);
  if (lgl->opts->move.val >= 2) return lglmvtcls (lgl, a, b, c);
  return 0;
}

static int lglwaiting (LGL * lgl, const char * str, int wait) {
  if (!wait) return 0;
  if (!lgl->wait) return 0;
  if (wait >= 2 && lgl->opts->elim.val && !lgl->elmrtc) {
    if (str)
      lglprt (lgl, 2,
	"[%s-waiting] on variable elimination to be completed", str);
    return 1;
  }
  if (wait >= 1 && lgl->opts->block.val && !lgl->blkrtc) {
    if (str)
      lglprt (lgl, 2, 
	"[%s-waiting] on blocked clause elimination to be completed", str);
    return 1;
  }
  return 0;
}

static void lglbasicate (LGL * lgl, int lit) {
  const int druplig = lgl->opts->druplig.val;
  int blit, tag, red, other, other2, lidx;
  const int * w, * eow, * p, * c, * l;
  int nonfalse, numtrue, val;
  HTS * hts;
  if (!lgl->opts->bate.val) return;
  if (lglwaiting (lgl, 0, lgl->opts->batewait.val)) return;
RESTART:
  hts = lglhts (lgl, -lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = * p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    if (tag == BINCS) continue;
    if (tag == TRNCS) {
      other = blit >> RMSHFT;
      numtrue = 0;
      if ((val = lglval (lgl, other)) < 0) continue;
      if (val > 0) {
	if (!lglevel (lgl, other)) continue;
	if (lgltd (lgl, other)->irr) numtrue++;
      }
      other2 = *p;
      if ((val = lglval (lgl, other2)) < 0) continue;
      if (val > 0) {
	if (!lglevel (lgl, other2)) continue;
	if (lgltd (lgl, other2)->irr) numtrue++;
      }
      if (!numtrue) continue;
      LOG (2, "basic ATE ternary clause %d %d %d", -lit, other, other2);
      lgl->stats->prb.basic.ate.trnr++;
      if (!lglrmvtcls (lgl, -lit, other, other2))
	lgldrupligdelclsarg (lgl, -lit, other, other2, 0);
      goto RESTART;
    } else {
      assert (tag == OCCS || tag == LRGCS);
      if (tag == LRGCS && lgl->dense) continue;
      lidx = (tag == LRGCS) ? *p : (blit >> RMSHFT);
      assert (!red);
      c = lglidx2lits (lgl, 0, lidx);
      numtrue = nonfalse = 0;
      for (l = c; (nonfalse < 2 || !numtrue) && (other = *l); l++) {
	if (other == -lit) continue;
	assert (other != lit);
	if ((val = lglval (lgl, other)) >= 0) nonfalse++;
	if (val > 0) {
	   if (!lglevel (lgl, other)) { numtrue = -1; break; }
	   if (lgltd (lgl, other)->irr) numtrue++;
	}
      }
      if (numtrue > 0 && nonfalse >= 2) {
	LOGCLS (2, c, "basic ATE large clause");
	lgl->stats->prb.basic.ate.lrg++;
	if (druplig) lgldrupligdelclsaux (lgl, c);
	lglrmlcls (lgl, lidx, 0);
	goto RESTART;
      }
    }
  }
}

static void lglbasicatestats (LGL * lgl) {
  int n = lgl->stats->prb.basic.ate.lrg + lgl->stats->prb.basic.ate.trnr;
  int d = n - lgl->stats->prb.basic.lastate;
  assert (d >= 0);
  if (d <= 0) return;
  lgl->stats->prb.basic.ate.count++;
  lglprt (lgl, 1,
    "[bate-%d] eliminated %d asymmetric tautologies during probing",
    lgl->stats->prb.basic.ate.count, d);
  lgl->stats->prb.basic.lastate = n;
}

static void lglbasicprobelit (LGL * lgl, int root) {
  int old, ok, dom, lit, val;
  Stk lift, saved;
  const int * p;
  CLR (lift); CLR (saved);
  assert (lgl->simp);
  assert (lgl->probing || lgl->cceing);
  assert (!lgl->level);
  LOG (2, "next probe %d positive phase", root);
  assert (!lgl->level);
  if (lgl->treelooking) lgl->stats->prb.treelook.probed++;
  else if (lgl->cceing) lgl->stats->cce.probed++;
  else assert (lgl->basicprobing), lgl->stats->prb.basic.probed++;
  if (lglrand (lgl) & (1<<12)) root = -root;
  lgliassume (lgl, root);
  old = lgl->next;
  ok = lglbcp (lgl);
  dom = 0;
  if (ok) {
    lglclnstk (&saved);
    lglbasicate (lgl, root);
    for (p = lgl->trail.start + old; p < lgl->trail.top; p++) {
      lit = *p;
      if (lit == root) continue;
      lglpushstk (lgl, &saved, lit);
    }
  } else dom = lglprbana (lgl, root);
  lglbacktrack (lgl, 0);
  if (!ok) {
    LOG (1, "failed literal %d on probing", dom, root);
    lglpushstk (lgl, &lift, -dom);
    goto MERGE;
  }
  LOG (2, "next probe %d negative phase", -root);
  assert (!lgl->level);
  if (lgl->treelooking) lgl->stats->prb.treelook.probed++;
  else if (lgl->cceing) lgl->stats->cce.probed++;
  else assert (lgl->basicprobing), lgl->stats->prb.basic.probed++;
  lgliassume (lgl, -root);
  ok = lglbcp (lgl);
  if (ok) {
    lglbasicate (lgl, -root);
    for (p = saved.start; p < saved.top; p++) {
      lit = *p;
      val = lglval (lgl, lit);
      if (val <= 0) continue;
      if (lgl->treelooking) lgl->stats->prb.treelook.lifted++;
      else if (lgl->cceing) lgl->stats->cce.lifted++;
      else assert (lgl->basicprobing), lgl->stats->prb.basic.lifted++;
      lglpushstk (lgl, &lift, lit);
      LOG (2, "lifted %d", lit);
    }
  } else dom = lglprbana (lgl, -root);
  lglbacktrack (lgl, 0);
  if (!ok) {
    LOG (1, "failed literal %d on probing %d", dom, -root);
    lglpushstk (lgl, &lift, -dom);
  }
MERGE:
  while (!lglmtstk (&lift)) {
    lit = lglpopstk (&lift);
    val = lglval (lgl, lit);
    if (val > 0) continue;
    if (val < 0) goto EMPTY;
    if (lgl->opts->druplig.val) {
      lgldrupligaddclsarg (lgl, REDCS, -root, lit, 0);
      lgldrupligaddclsarg (lgl, REDCS, root, lit, 0);
    }
    lglunit (lgl, lit);
    if (lgl->opts->druplig.val) {
      lgldrupligdelclsarg (lgl, -root, lit, 0);
      lgldrupligdelclsarg (lgl, root, lit, 0);
    }
    if (lgl->treelooking) lgl->stats->prb.treelook.failed++;
    else if (lgl->cceing) lgl->stats->cce.failed++;
    else assert (lgl->basicprobing), lgl->stats->prb.basic.failed++;
    if (lglbcp (lgl)) continue;
EMPTY:
    LOG (1, "empty clause after propagating lifted and failed literals");
    lglmt (lgl);
  }
  lglrelstk (lgl, &lift);
  lglrelstk (lgl, &saved);
}

static TVar * lgltvar (LGL * lgl, int lit) {
  int idx = abs (lit);
  assert (2 <= idx && idx < lgl->nvars);
  assert (lgl->tlk);
  return lgl->tlk->tvars + idx;
}

static void lglsignedtlmark (LGL * lgl, int lit) {
  TVar * tv = lgltvar (lgl, lit);
  unsigned bit = 1u << (lit < 0);
  if (tv->mark & bit) return;
  tv->mark |= bit;
}

static int lglsignedtlmarked (LGL * lgl, int lit) {
  TVar * tv = lgltvar (lgl, lit);
  unsigned bit = 1u << (lit < 0);
  return tv->mark & bit;
}

static void lgltlenq (LGL * lgl, int start) {
  int lit, blit, tag, other, oldcount, newcount, * stk;
  unsigned delta, i, j, mod;
  const int * p, * w, * eos;
  HTS * hts;
  assert (!lglsignedtlmarked (lgl, start));
  lglsignedtlmark (lgl, start);
  lglpushstk (lgl, &lgl->tlk->stk, start);
  while (!lglmtstk (&lgl->tlk->stk)) {
    lit = lglpopstk (&lgl->tlk->stk);
    LOG (2, "tree-look enqueue %d%s", lit, lit == start ? " start":"");
    if (lit) {
      assert (!lglval (lgl, lit));
      assert (lglsignedtlmarked (lgl, lit));
      lglpushstk (lgl, &lgl->tlk->seen, lit);
      lglpushstk (lgl, &lgl->tlk->stk, 0);
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eos = w + hts->count;
      oldcount = lglcntstk (&lgl->tlk->stk);
      for (p = w; p < eos; p++) {
        INCSTEPS (prb.treelook.steps);
	blit = *p;
	tag = blit & MASKCS;
	if (tag == OCCS) continue;
	if (tag == TRNCS || tag == LRGCS) { p++; continue; }
	assert (tag == BINCS);
	other = -(blit >> RMSHFT);
	if (lglval (lgl, other)) assert (lglval (lgl, other) < 0);
	else if (!lglsignedtlmarked (lgl, other)) {
	  lglsignedtlmark (lgl, other);
	  lglpushstk (lgl, &lgl->tlk->stk, other);
	}
      }
      newcount = lglcntstk (&lgl->tlk->stk);
      delta = newcount - oldcount;
      assert (delta >= 0);
      if ((mod = delta) <= 1) continue;
      stk = lgl->tlk->stk.start;
      for (i = 0; i < delta-1; i++, mod--) {
	assert (mod > 0);
	j = i + (lglrand (lgl) % mod);
	assert (i <= j && j < delta);
	if (i == j) continue;
	SWAP (int, stk[i + oldcount], stk[j + oldcount]);
      }
    } else lglpushstk (lgl, &lgl->tlk->seen, 0);
  }
}

static int lglisroot (LGL * lgl, int lit) { return !lglhasbins (lgl, lit); }

static void lgltlunmarkall (LGL * lgl) {
  int idx;
  for (idx = 2; idx < lgl->nvars; idx++)
    lgl->tlk->tvars[idx].mark = 0;
}

static int lgltlschedlit (LGL * lgl, int lit) {
  if (INCSTEPS (prb.treelook.steps) > lgl->limits->prb.steps) return 0;
  if (!lglisfree (lgl, lit)) return 1;
  if (lglsignedtlmarked (lgl, lit)) return 1;
  if (!lglisroot (lgl, -lit)) return 1;
  if (!lgl->tlk->lkhd && lglavar (lgl, lit)->donotreelook) return 1;
  if (lgl->opts->treelook.val >= 2) {
    lglbasicprobelit (lgl, -lit);
    if (lgl->mt) return 0;
    if (lglterminate (lgl)) return 0;
    if (!lglisfree (lgl, lit)) return 1;
    if (!lglisroot (lgl, -lit)) return 1;
    if (!lglhasbins (lgl, lit)) return 1;
  }
  lgltlenq (lgl, lit);
  return 1;
}

static int lgltlschedanylit (LGL * lgl, int lit) {
  if (INCSTEPS (prb.treelook.steps) > lgl->limits->prb.steps) return 0;
  if (!lglisfree (lgl, lit)) return 1;
  if (lglsignedtlmarked (lgl, lit)) return 1;
  if (!lgl->tlk->lkhd && lglavar (lgl, lit)->donotreelook) return 1;
  if (lgl->opts->treelook.val >= 2) {
    lglbasicprobelit (lgl, -lit);
    if (lgl->mt) return 0;
    if (lglterminate (lgl)) return 0;
    if (!lglisfree (lgl, lit)) return 1;
  }
  lgltlenq (lgl, lit);
  return 1;
}

static void lgltlsched (LGL * lgl) {
  int idx, round, count, * p;
  LOG (1, "scheduling tree-look literals");
  for (round = 0; !lgl->mt && round < 2; round++) {
    assert (lglmtstk (&lgl->tlk->seen));
    assert (lglmtstk (&lgl->tlk->stk));
    if (lglrandlitrav (lgl, lgltlschedlit))
      lglrandlitrav (lgl, lgltlschedanylit);
    lgltlunmarkall (lgl);
    lglrelstk (lgl, &lgl->tlk->stk);
    if (!lglmtstk (&lgl->tlk->seen)) break;
    for (idx = 2; idx < lgl->nvars; idx++)
      lglavar (lgl, idx)->donotreelook = 0;
  }
  lglfitstk (lgl, &lgl->tlk->seen);
  count = 0;
  for (p = lgl->tlk->seen.start; p < lgl->tlk->seen.top; p++)
    if (*p) count++;
  lglprt (lgl, 1,
    "[treelook-%d] scheduled %d literals %.0f%%",
    lgl->stats->prb.treelook.count, count, lglpcnt (count, 2*lglrem (lgl)));
  if (!count)
    for (idx = 2; idx < lgl->nvars; idx++)
      lglavar (lgl, idx)->donotreelook = 0;
}

static void lgltlassign (LGL * lgl, Stk * assignment, int lit) {
  TVar * tv;
  LOG (2, "tree-look assign %d", lit);
  tv = lgltvar (lgl, lit);
  assert (!tv->val);
  tv->val = lglsgn (lit) * (1 + lglcntstk (assignment));
  lglpushstk (lgl, assignment, lit);
  assert (tv->val);
  assert (lglsgn (tv->val) == lglsgn (lit));
}

static void lgltlunassign (LGL * lgl, int lit) {
  TVar * tv;
  LOG (2, "tree-look unassign %d", lit);
  tv = lgltvar (lgl, lit);
  assert (tv->val);
  assert (lglsgn (tv->val) == lglsgn (lit));
  tv->val = 0;
}

static int lgltlval (LGL * lgl, int lit) {
  TVar * tv = lgltvar (lgl, lit);
  int res;
  if (!tv->val) return 0;
  res = lglsgn (tv->val);
  if (lit < 0) res = -res;
  return res;
}

static void lglincreducedptr (LGL * lgl, Flt * reducedptr, int size) {
  Flt reduced = *reducedptr, inc = lglflt (-size, 1);
  reduced = lgladdflt (reduced, inc);
  LOG (2, "reduced score incremented to %s from %s by %s (size %d)",
       lglflt2str (lgl, reduced), 
       lglflt2str (lgl, *reducedptr), 
       lglflt2str (lgl, inc),
       size);
  *reducedptr = reduced;
}

static int lgltlbcp (LGL * lgl,
                     Stk * assignment, Flt * reducedptr, int dom) {
  int next = lglcntstk (assignment), next2 = next, lit, size, implied;
  int blit, tag, other, other2, val, lidx, red, found, trivial;
  int numnonfalse, numfalse, firstfalse, litval, skip;
  const int * p, * w, * eos, * c, * q;
  HTS * hts;
  if (lglval (lgl, dom)) return 1;
  assert (!lgltlval (lgl, dom));
  lgltlassign (lgl, assignment, dom);
  lgl->stats->prb.treelook.probed++;
  LOG (2, "starting tree-look bcp on %d", dom);
  for (;;) {
    if (next2 < lglcntstk (assignment)) {
      assert (lgl->simp);
      INCSTEPS (props.simp);
      if (lgl->lkhd) INCSTEPS (props.lkhd);
      lit = lglpeek (assignment, next2++);
      assert (lgltlval (lgl, lit) > 0);
      LOG (2, "tree-look binary clause bcp on %d", lit);
      hts = lglhts (lgl, -lit);
      w = lglhts2wchs (lgl, hts);
      eos = w + hts->count;
      for (p = w; p < eos; p++) {
	assert (lgl->simp);
	lgl->stats->visits.simp++;
	if (lgl->lkhd) lgl->stats->visits.lkhd++;
	INCSTEPS (prb.treelook.steps);
	blit = *p;
	tag = blit & MASKCS;
	if (tag == OCCS) continue;
	if (tag == TRNCS || tag == LRGCS) { p++; continue; }
	assert (tag == BINCS);
	other = blit >> RMSHFT;
	val = lglval (lgl, other);
	if (val < 0) return 0;
	if (val > 0) continue;
	val = lgltlval (lgl, other);
	if (val < 0) return 0;
	if (reducedptr) lglincreducedptr (lgl, reducedptr, 2);
	if (val > 0) continue;
	lgltlassign (lgl, assignment, other);
      }
    } else if (next < lglcntstk (assignment)) {
      lit = lglpeek (assignment, next++);
      litval = lgltlval (lgl, lit);
      assert (litval > 0);
      LOG (2, "tree-look non-binary clause bcp on %d", lit);
      hts = lglhts (lgl, -lit);
      w = lglhts2wchs (lgl, hts);
      eos = w + hts->count;
      for (p = w; p < eos; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == LRGCS || tag == TRNCS) p++;
	if (tag == BINCS || tag == LRGCS) continue;
	INCSTEPS (prb.treelook.steps);
	assert (lglmtstk (&lgl->clause));
	skip = trivial = 0;
	if (tag == TRNCS) {
	  other = blit >> RMSHFT;
	  other2 = *p;
	  if (lglval (lgl, other) > 0 || 
	      lglval (lgl, other2) > 0) skip = 1;
	  else {
	    if (lgltlval (lgl, other) > 0 ||
	        lgltlval (lgl, other2) > 0) trivial = 1;
	    lglpushstk (lgl, &lgl->clause, -lit),
	    lglpushstk (lgl, &lgl->clause, other),
	    lglpushstk (lgl, &lgl->clause, other2);
	  }
	} else {
	  assert (tag == OCCS);
	  red = blit & REDCS;
	  lidx = blit >> RMSHFT;
	  found = trivial = 0;
	  c = lglidx2lits (lgl, red, lidx);
	  INCSTEPS (prb.treelook.steps);
	  for (q = c; !skip && (other = *q); q++) {
	    if (other >= NOTALIT) skip = 1;
	    else if (lglval (lgl, other) > 0) skip = 1;
	    else {
	      if (other == -lit) assert (!found), found++;
	      if (lgltlval (lgl, other) > 0) trivial = 1;
	      lglpushstk (lgl, &lgl->clause, other);
	    }
	  }
	  assert (skip || found);
	}
	numnonfalse = numfalse = size = implied = 0;
	firstfalse = 1;
	if (!skip) {
	  INCSTEPS (prb.treelook.steps);
	  for (q = lgl->clause.start; q < lgl->clause.top; q++) {
	    other = *q;
	    if (lglval (lgl, other) < 0) continue;
	    size++;
	    if ((val = lgltlval (lgl, other)) < 0) {
	      if (reducedptr && -val < litval) firstfalse = 0;
	      numfalse++; 
	      continue; 
	    }
	    numnonfalse++;
	    if (implied == NOTALIT) continue;
	    else if (implied) implied = NOTALIT;
	    else implied = other;
	  }
	}
	lglclnstk (&lgl->clause);
	if (skip) continue;
	if (reducedptr && firstfalse) 
	  lglincreducedptr (lgl, reducedptr, size);
	if (trivial) continue;
	if (!numnonfalse) { assert (!implied); return 0; }
	assert (implied);
	if (implied == NOTALIT) continue;
	assert (numnonfalse == 1);
	if (!numfalse) continue; // TODO remove?
	INCSTEPS (prb.treelook.steps);
	if (tag == TRNCS) lgl->stats->hbr.trn++; else lgl->stats->hbr.lrg++;
	LOG (2, "tree-look hyper binary resolvent %d %d", -dom, implied);
        lgldrupligaddclsarg (lgl, REDCS, -dom, implied, 0);
	(void) lglwchbin (lgl, -dom, implied, REDCS);
	(void) lglwchbin (lgl, implied, -dom, REDCS);
	lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
	lgl->stats->hbr.cnt++;
	lgl->stats->prgss++;
	lgltlassign (lgl, assignment, implied);
	assert (next > 0),  next--; // force to redo this trn/lrg literal
	break;	// and continue outer 'next2' prop on 'implied'
      }
    } else break;
  }
  if (reducedptr) assert (lgl->tlk->lkhd), lgl->tlk->lkhd[dom] = *reducedptr;
  return 1;
}

static void lgltreelooklit (LGL * lgl, Stk * a, Ftk * r, int lit) {
  Flt reduced;
  LOG (2, "treelook dequeue %d", lit);
  if (lit) {
    if (lgl->opts->treelook.val >= 2 &&
	lglmtstk (a) &&
	lglisfree (lgl, lit)) lglbasicprobelit (lgl, -lit);
    if (r) {
      reduced = lglmtftk (r) ? FLTMIN : lgltopftk (r);
      lglpushftk (lgl, r, reduced);
    }
    lglpushstk (lgl, a, 0);
    if (lgl->mt || !lglisfree (lgl, lit)) return;
    if (lgltlval (lgl, -lit) > 0 ||
	(!lgltlval (lgl, lit) && 
	 !lgltlbcp (lgl, a, r ? &reduced : 0, lit))) {
      int tmp;
      LOG (1, "tree-look failed literal %d", lit);
      if (!(tmp = lglval (lgl, lit))) {
	lgl->stats->prb.treelook.failed++;
	lglunit (lgl, -lit);
	if (!lglbcp (lgl)) {
	  LOG (1, "inconsistent tree-look failed literal");
	  if (!lgl->mt) lglmt (lgl);
	}
      } else if (tmp > 0) {
	lgl->stats->prb.treelook.failed++;
	LOG (1, "tree-look failed literal literal %d inconsistent", lit);
	if (!lgl->mt) lglmt (lgl);
      } else LOG (1, "tree-look failed literal %d already found", lit);
    }
    if (r) {
      assert (r->start < r->top);
      assert (r->top[-1] <= reduced);
      r->top[-1] = reduced;
    }
  } else {
    if (r) lglpopftk (r);
    while ((lit = lglpopstk (a)))
      lgltlunassign (lgl, lit);
  }
}

static int64_t lglsetprbtreelooklim (LGL * lgl, int * lkhdresptr) {
  int szpen, lastpen, pen, boost;
  int64_t limit, irrlim;
  if (lgl->opts->treelookrtc.val || lgl->opts->prbrtc.val) {
    limit = lgl->limits->prb.steps = LLMAX;
    lglprt (lgl, 1,
      "[treelook-%d] really no limit (run to completion)",
      lgl->stats->prb.treelook.count);
  } else if (lkhdresptr && lgl->opts->treelookfull.val) {
    limit = lgl->limits->prb.steps = LLMAX;
    lglprt (lgl, 1,
      "[treelook-%d] unlimited look-ahead requested",
      lgl->stats->prb.treelook.count);
  } else {
    limit = (lgl->opts->treelookreleff.val*lglvisearch (lgl))/2000;
    if (limit < lgl->opts->treelookmineff.val)
      limit = lgl->opts->treelookmineff.val;
    if (lgl->opts->treelookmaxeff.val >= 0 &&
        limit > lgl->opts->treelookmaxeff.val)
      limit = lgl->opts->treelookmaxeff.val;
    assert (lgl->tlk);
    szpen = lglszpen (lgl);
    lastpen = lgl->tlk->lkhd ? 
      lgl->limits->lkhdpen : lgl->limits->prb.treelook.pen;
    limit >>= (pen = szpen + lastpen);
    irrlim = (lgl->stats->irr.clauses.cur/4) >> szpen;
    if (lgl->opts->boost.val && lgl->tlk->lkhd)
      boost = lgl->opts->treelookboost.val;
    else boost = 1;
    limit *= boost;
    if (lgl->opts->irrlim.val && limit < irrlim) {
      limit = irrlim;
      lglprt (lgl, 1, 
  "[treelook-%d] limit %lld based on %d irredundant clauses penalty %d",
	lgl->stats->prb.treelook.count, 
	(LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
    } else
      lglprt (lgl, 1, 
	"[treelook-%d] limit %lld penalty %d = %d + %d boost %d",
	lgl->stats->prb.treelook.count, (LGLL) limit,
	pen, lastpen, szpen, boost);
    if (lkhdresptr)
      lglprt (lgl, 1, "[treelook-%d] limited look-ahead requested",
	      lgl->stats->prb.treelook.count);
    lgl->limits->prb.steps = lgl->stats->prb.treelook.steps + limit;
  }

  return limit;
}

static void lglclntlvals (LGL * lgl) {
  int idx;
  for (idx = 2; idx < lgl->nvars; idx++) lgl->tlk->tvars[idx].val = 0;
}

#ifndef NDEBUG
static int lglieliminated (LGL * lgl, int ilit) {
  return lglelit2ext (lgl, lglexport (lgl, ilit))->eliminated;
}
#endif

static int lgliblocking (LGL * lgl, int ilit) {
  return lglelit2ext (lgl, lglexport (lgl, ilit))->blocking;
}

static void lgltlsetlkhd (LGL * lgl, int * lkhdresptr, int remlits) {
  LKHD lkhdrescore, lkhdscore, lkhdpos, lkhdneg;
  Flt jwhrescore, jwhscore, jwhpos, jwhneg;
  int idx, lkhdres, phase, elit;
  Ext * ext;
  assert (lkhdresptr);
  lkhdres = 0; lkhdrescore = FLTMIN; jwhrescore = FLTMIN;
  assert (!lgl->nvars || lgl->tlk->lkhd);
  lgljwh (lgl);
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    assert (!lglieliminated (lgl, idx));
    if (lkhdresptr && lgliblocking (lgl, idx)) continue;
    if (!remlits) {
      lkhdpos = lgl->tlk->lkhd[idx];
      lkhdneg = lgl->tlk->lkhd[-idx];
      lkhdscore = lglmulflt (lkhdneg, lkhdpos);
      if (lkhdscore > FLTMIN)
	lkhdscore = lgladdflt (lkhdscore, lgladdflt (lkhdneg, lkhdpos));
    } else lkhdscore = lkhdpos = lkhdneg = FLTMIN;
    jwhpos = lgl->jwh[lglulit (idx)];
    jwhneg = lgl->jwh[lglulit (-idx)];
    jwhscore = lglmulflt (jwhpos, jwhneg);
    jwhscore = lgladdflt (jwhscore, lgladdflt (jwhpos, jwhneg));
    LOG (1,
      "final tree based look-ahead score [%s,%s] "
      "(pos [%s,%s], neg [%s,%s]) of %d",
       lglflt2str (lgl, lkhdscore), lglflt2str (lgl,jwhscore),
       lglflt2str (lgl, lkhdpos), lglflt2str (lgl,jwhpos),
       lglflt2str (lgl, lkhdneg), lglflt2str (lgl,jwhneg),
       idx);

    // phase with less weighted reductions
         if (lkhdpos > lkhdneg) phase = -1;
    else if (lkhdpos < lkhdneg) phase = 1;
    // then with more weighted occs
    else if (jwhpos > jwhneg) phase = 1;
    else if (jwhpos < jwhneg) phase = -1;
    // otherwise negative phase
    else phase = -1;

    if (lkhdres) {
      if (lkhdscore < lkhdrescore) continue;
      if (lkhdscore == lkhdrescore && jwhscore <= jwhrescore) continue;
    }
    lkhdrescore = lkhdscore;
    jwhrescore = jwhscore;
    lkhdres = phase * idx;
  }
  if (lkhdres) {
    elit = lglexport (lgl, lkhdres);
    ext = lglelit2ext (lgl, elit);
    assert (!ext->eliminated);
    assert (!ext->blocking);
    lglprt (lgl, 1, "[treelook-%d] best look-ahead %d score [%s,%s]",
      lgl->stats->prb.treelook.count, lkhdres,
      lglflt2str (lgl, lkhdrescore), lglflt2str (lgl, jwhrescore));
    if (ext->melted) {
      ext->melted = 0;
      LOG (2, "tree-look-ahead winner external %d not melted anymore", elit);
    } else
      LOG (2,
	"tree-look-ahead winner external %d was not melted anyhow", elit);
  } else LOG (1, "no proper best tree-look-ahead literal found");
  if (lkhdresptr) *lkhdresptr = lkhdres;
}

static void lglgenericreport (LGL * lgl, const char * name, int count,
                              int probed, int nprobes, double start) {
  int div, mod;
  assert (nprobes >= 0);
  if (!nprobes || lgl->opts->verbose.val < 2) return;
  if (lgl->opts->verbose.val == 2) div = 10;
  else if (lgl->opts->verbose.val == 3) div = 100;
  else div = 0;
  mod = div ? (nprobes + div - 1) / div : 1;
  assert (mod > 0);
  if (probed % mod) return;
  lglprt (lgl, 1,
    "[%s-%d] probed %d/%d (%.0f%%) %.1f sec %d vars %.0f MB",
    name, count, probed, nprobes, lglpcnt (probed, nprobes),
    lglgetime (lgl) - start, lglrem (lgl), lglmb (lgl));
}

static void lgltreelookreport (LGL * lgl,
                              int probed, int nprobes, double start) {
  lglgenericreport (lgl,
     "treelook", lgl->stats->prb.treelook.count, probed, nprobes, start);
}

static int lgltreelookaux (LGL * lgl, int * lkhdresptr) {
  int oldhbrs, oldrem, remvarsall, remvarslkhd, remlits, notfullyscheduled;
  int deltavars, newhbrs, success, idx, next, lit, nseen;
  int64_t oldsteps, steps, limit;
  Stk assignment;
  double start;
  Ftk reduced;
  TVar * tv;
  AVar * av;

  if (lgl->mt) return 0;
  if (lkhdresptr) *lkhdresptr = 0;
  if (!lgl->nvars) return 1;

  lglstart (lgl, &lgl->times->prb.treelook);
  lgl->stats->prb.treelook.count++;

  NEW (lgl->tlk, 1);
  NEW (lgl->tlk->tvars, lgl->nvars);

  assert (!lgl->simp && !lgl->probing && !lgl->treelooking);
  lgl->simp = lgl->probing = lgl->treelooking = 1;

  if (lgl->level > 0) lglbacktrack (lgl, 0);
  oldhbrs = lgl->stats->hbr.cnt;
  oldrem = lglrem (lgl);

  assert (!lgl->tlk->lkhd);
  if (lkhdresptr) {
    NEW (lgl->tlk->lkhd, 2*lgl->nvars);
    lgl->tlk->lkhd += lgl->nvars;
    assert (lgl->tlk->lkhd);
  }

  limit = lglsetprbtreelooklim (lgl, lkhdresptr);
  oldsteps = lgl->stats->prb.treelook.steps;

  lgltlsched (lgl);

  steps = lgl->stats->prb.treelook.steps - oldsteps;
  lglprt (lgl, 1, "[treelook-%d] scheduling used %lld steps",
    lgl->stats->prb.treelook.count, (LGLL) steps);

  if (limit != LLMAX) {
    notfullyscheduled =
      (lgl->stats->prb.treelook.steps >= lgl->limits->prb.steps);
    lgl->limits->prb.steps = lgl->stats->prb.treelook.steps + limit;
    if (notfullyscheduled)
      lglprt (lgl, 1, "[treelook-%d] not fully scheduled",
 	lgl->stats->prb.treelook.count);
    else
      lglprt (lgl, 1, "[treelook-%d] scheduled completely",
 	lgl->stats->prb.treelook.count);
  } else notfullyscheduled = 0;

  CLR (assignment); CLR (reduced);
  remlits = remvarsall = remvarslkhd = 0;

  nseen = lglcntstk (&lgl->tlk->seen);
  if (!lgl->mt && nseen) {

    (void) lglsetprbtreelooklim (lgl, lkhdresptr);
    oldsteps = lgl->stats->prb.treelook.steps;

    lgldense (lgl, 0);
    next = 0;
    start = lglgetime (lgl);
    lgltreelookreport (lgl, next, nseen, start);
    while (!lgl->mt &&
	   !lglterminate (lgl) &&
	   lglsyncunits (lgl) &&
	   next < nseen &&
	   lgl->stats->prb.treelook.steps < lgl->limits->prb.steps) {
      lit = lglpeek (&lgl->tlk->seen, next++);
      lgltreelooklit (lgl, &assignment, lkhdresptr ? &reduced : 0, lit);
      lgltreelookreport (lgl, next, nseen, start);
    }
    lgltreelookreport (lgl, next, nseen, start);
    lglclntlvals (lgl);
    assert (lgl->stats->prb.treelook.steps >= oldsteps);
    steps = lgl->stats->prb.treelook.steps - oldsteps;
    lglprt (lgl, 1, "[treelook-%d] used %lld steps",
      lgl->stats->prb.treelook.count, (LGLL) steps);
    while (next < lglcntstk (&lgl->tlk->seen)) {
      lit = lglpeek (&lgl->tlk->seen, next++);
      if (!lit) continue;
      if (!lglisfree (lgl, lit)) continue;
      remlits++;
      tv = lgltvar (lgl, lit);
      tv->val = 1;
    }
    for (idx = 2; idx < lgl->nvars; idx++)
      if (lglisfree (lgl, idx)) {
	tv = lgltvar (lgl, idx);
	av = lglavar (lgl, idx);
	if (tv->val) {
	   tv->val = 0;
	   if (!av->donotreelook) remvarsall++;
	   remvarslkhd++;
	} else if (!av->donotreelook) av->donotreelook = 1;
      }
    assert (remvarslkhd >= remvarsall);

    if (remvarsall || notfullyscheduled) {
      lglprt (lgl, 1, "[treelook-%d] %d literals remain %.0f%%%s",
	lgl->stats->prb.treelook.count,
	remlits, lglpcnt (remlits, 2*lglrem (lgl)),
        lkhdresptr ? " in look-ahead" : "");
      if (lkhdresptr)
	lglprt (lgl, 1, "[treelook-%d] %d look-ahead variables remain %.0f%%",
	  lgl->stats->prb.treelook.count,
	  remvarslkhd, lglpcnt (remvarslkhd, lglrem (lgl)));
      lglprt (lgl, 1,
	"[treelook-%d] %d variables remain to probed next time %.0f%%",
	lgl->stats->prb.treelook.count,
	remvarsall, lglpcnt (remvarsall, lglrem (lgl)));
    } else {
      lglprt (lgl, 1, 
        "[treelook-%d] fully completed tree based probing%s",
	lgl->stats->prb.treelook.count, lkhdresptr ? " in look-ahead" : "");
      for (idx = 2; idx < lgl->nvars; idx++)
	lglavar (lgl, idx)->donotreelook = 0;
    }
    lglsparse (lgl);
  }

  DEL (lgl->tlk->tvars, lgl->nvars);
  lglgc (lgl);
  lglrelftk (lgl, &reduced);
  lglrelstk (lgl, &assignment);
  lglrelstk (lgl, &lgl->tlk->seen);
  if (!lgl->mt && lkhdresptr) 
    lgltlsetlkhd (lgl, lkhdresptr, remlits || notfullyscheduled);
  if (lgl->tlk->lkhd) {
    lgl->tlk->lkhd -= lgl->nvars;
    DEL (lgl->tlk->lkhd, 2*lgl->nvars);
  }
  DEL (lgl->tlk, 1);
  newhbrs = lgl->stats->hbr.cnt - oldhbrs;
  if (newhbrs && !lgl->mt && !lkhdresptr) lgldecomp (lgl);

  assert (lgl->simp && lgl->probing && lgl->treelooking);
  lgl->simp = lgl->probing = lgl->treelooking = 0;

  deltavars = oldrem - lglrem (lgl);
  success = deltavars || newhbrs;
  if (!lkhdresptr) LGLUPDPEN (prb.treelook, deltavars);
  else if (remlits && lgl->limits->lkhdpen < lgl->opts->penmax.val)
    lgl->limits->lkhdpen++;
  else if (!remlits && lgl->limits->lkhdpen)
    lgl->limits->lkhdpen--;
  lglprt (lgl, 1 + !success,
	  "[treelook-%d] removed %d variables, found %d hbrs",
	  lgl->stats->prb.treelook.count, deltavars, newhbrs);
  lglrep (lgl, 2, 'p');
  lglstop (lgl);
  lglbasicatestats (lgl);
  return !lgl->mt;
}

static int lgltreelook (LGL * lgl) {
  if (lgldelaying (lgl, "treelook",
        &lgl->limits->prb.treelook.del.rem)) return 1;
  return lgltreelookaux (lgl, 0);
}

static int lgljwhlook (LGL * lgl) {
  Flt best, pos, neg, score;
  int res, idx, elit;
  Ext * ext;
  lgljwh (lgl);
  best = FLTMIN;
  res = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    assert (!lglieliminated (lgl, idx));
    if (lgliblocking (lgl, idx)) continue;
    pos = lgl->jwh[lglulit (idx)];
    neg = lgl->jwh[lglulit (-idx)];
    score = lglmulflt (pos, neg);
    score = lgladdflt (score, lgladdflt (pos, neg));
    if (res && score <= best) continue;
    LOG (1, "jwh look-ahead score %s (pos %s, neg %s) of %d",
      lglflt2str (lgl, score), lglflt2str (lgl, pos), lglflt2str (lgl, neg),
      idx);
    res = (pos > neg) ? idx : -idx;
    best = score;
  }
  if (res) {
    elit = lglexport (lgl, res);
    ext = lglelit2ext (lgl, elit);
    lglprt (lgl, 1, "[jwhlook] best look-ahead %d score %s",
            res, lglflt2str (lgl, best));
    if (ext->melted) {
      ext->melted = 0;
      LOG (2, "jwh-look-ahead winner external %d not melted anymore", elit);
    } else
      LOG (2, "jwh-look-ahead winner external %d was not melted anyhow", elit);
  } else LOG (1, "no proper best jwh-look-ahead literal found");
  return res;
}

static int lglislook (LGL * lgl) {
  int64_t best, pos, neg, score;
  int res, idx, elit, * scores;
  Ext * ext;
  scores = lglis (lgl);
  best = res = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    assert (!lglieliminated (lgl, idx));
    if (lgliblocking (lgl, idx)) continue;
    pos = scores[idx], neg = scores[-idx];
    score = pos * neg + pos + neg;
    assert (0 <= score && pos <= score && neg <= score);
    if (res && score <= best) continue;
    LOG (1,
      "LIS look-ahead score %lld (pos %lld, neg %lld) of %d",
      (LGLL) score, (LGLL) pos, (LGLL) neg, idx);
    res = (pos > neg) ? idx : -idx;
    best = score;
  }
  scores -= lgl->nvars;
  DEL (scores, 2*lgl->nvars);
  if (res) {
    elit = lglexport (lgl, res);
    ext = lglelit2ext (lgl, elit);
    assert (!ext->eliminated && !ext->blocking);
    lglprt (lgl, 1,
      "[lislook] best LIS look-ahead %d score %lld", 
      res, (LGLL) best);
    if (ext->melted) {
      ext->melted = 0;
      LOG (2, "look-ahead winner external %d not melted anymore", elit);
    } else
      LOG (2, "look-ahead winner external %d was not melted anyhow", elit);
  } else LOG (1, "no proper best LIS look-ahead literal found");
  return res;
}

static int64_t lglsatmul64 (int64_t a, int64_t b) {
  assert (a >= 0), assert (b >= 0);
  return (b && (LLMAX / b < a)) ? LLMAX : a * b;
}

static int64_t lglsatadd64 (int64_t a, int64_t b) {
  assert (a >= 0), assert (b >= 0);
  return (LLMAX - b < a) ? LLMAX : a + b;
}

static int64_t * lglsumlenscores (LGL * lgl) {
  int idx, sign, lit, tag, blit, other, other2, red;
  const int *p, * w, * eow, * c;
  int64_t * res, len;
  Val val, tmp, tmp2;
  HTS * hts;
  Stk * s;
  NEW (res, 2*lgl->nvars);
  res += lgl->nvars;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      val = lglval (lgl, lit);
      if (val > 0) continue;
      hts = lglhts (lgl, lit);
      if (!hts->offset) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	if (red) continue;
	other = blit >> RMSHFT;
	if (abs (other) < abs (lit)) continue;
	tmp = lglval (lgl, other);
	if (tmp > 0) continue;
	if (tag == BINCS) {
	  assert (!tmp);
	  res[lit] += 2;
	  res[other] += 2;
	} else {
	  assert (tag == TRNCS);
	  other2 = *p;
	  if (abs (other2) < abs (lit)) continue;
	  tmp2 = lglval (lgl, other2);
	  if (tmp2 > 0) continue;
	  assert ((val > 0) + (tmp > 0) + (tmp2 > 0) == 0);
	  assert ((val < 0) + (tmp < 0) + (tmp2 < 0) <= 1);
	  len = !val + !tmp + !tmp2;
	  if (!val) res[lit] += len;
	  if (!tmp) res[other] += len;
	  if (!tmp2) res[other2] += len;
	}
      }
    }
  s = &lgl->irr;
  for (c = s->start; c < s->top; c = p + 1) {
    p = c;
    if (*p >= NOTALIT) continue;
    val = -1;
    len = 0;
    while ((other = *p)) {
      tmp = lglval (lgl, other);
      if (tmp > val) val = tmp;
      if (!tmp) len++;
      p++;
    }
    if (val > 0) continue;
    for (p = c; (other = *p); p++)
      if (!lglval (lgl, other))
	res[other] += len;
  }
  return res;
}

static int lglsumlenlook (LGL * lgl) {
  int64_t best, pos, neg, score, * scores;
  int res, idx, elit;
  Ext * ext;
  scores = lglsumlenscores (lgl);
  best = res = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    assert (!lglieliminated (lgl, idx));
    if (lgliblocking (lgl, idx)) continue;
    pos = scores[idx], neg = scores[-idx];
    score = lglsatadd64 (lglsatmul64 (pos, neg), lglsatadd64 (pos, neg));
    assert (0 <= score), assert (pos <= score), assert (neg <= score);
    if (res && score <= best) continue;
    LOG (1,
      "look-ahead score %lld (pos %lld, neg %lld) of %d",
      (LGLL) score, (LGLL) pos, (LGLL) neg, idx);
    res = (pos > neg) ? idx : -idx;
    best = score;
  }
  scores -= lgl->nvars;
  DEL (scores, 2*lgl->nvars);
  if (res) {
    elit = lglexport (lgl, res);
    ext = lglelit2ext (lgl, elit);
    assert (!ext->eliminated && !ext->blocking);
    lglprt (lgl, 1,
      "[sumlook] best look-ahead %d score %lld", 
      res, (LGLL) best);
    if (ext->melted) {
      ext->melted = 0;
      LOG (2, "look-ahead winner external %d not melted anymore", elit);
    } else
      LOG (2, "look-ahead winner external %d was not melted anyhow", elit);
  } else LOG (1, "no proper best look-ahead literal found");
  return res;
}

static int lglschedbasicprobe (LGL * lgl, Stk * probes, int round) {
  int idx, res, i, j, donotbasicprobes, keepscheduled;
  assert (lglmtstk (probes));
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    if (lgl->opts->prbasic.val <= 1 &&
        (lglhasbins (lgl, idx) == lglhasbins (lgl, -idx))) continue;
    LOG (1, "new probe %d", idx);
    lglpushstk (lgl, probes, idx);
  }
  res = lglcntstk (probes);
  donotbasicprobes = keepscheduled = 0;
  for (i = 0; i < res; i++) {
    idx = lglpeek (probes, i);
    if (!idx) continue;
    assert (lglisfree (lgl, idx));
    if (lglavar (lgl, idx)->donotbasicprobe) donotbasicprobes++;
    else keepscheduled++;
  }
  if (!keepscheduled) {
    for (i = 0; i < res; i++) {
      idx = lglpeek (probes, i);
      if (!idx) continue;
      assert (lglisfree (lgl, idx));
      lglavar (lgl, idx)->donotbasicprobe = 0;
      keepscheduled++;
    }
    donotbasicprobes = 0;
  }
  for (i = 0; i < res; i++) {
    idx = lglpeek (probes, i);
    if (!idx) continue;
    assert (lglisfree (lgl, idx));
    if (lglavar (lgl, idx)->donotbasicprobe) donotbasicprobes++;
    else keepscheduled++;
  }
  j = 0;
  for (i = 0; i < res; i++) {
    idx = lglpeek (probes, i);
    if (!idx) continue;
    if (!lglavar (lgl, idx)->donotbasicprobe)
      lglpoke (probes, j++, idx);
  }
  lglrststk (probes, (res = j));
  if (!res)
    lglprt (lgl, 2, "[basicprobe-%d-%d] no potential probes found",
	    lgl->stats->prb.basic.count, round);
  else if (!donotbasicprobes)
    lglprt (lgl, 2, "[basicprobe-%d-%d] scheduled all %d potential probes",
	    lgl->stats->prb.basic.count, round, res);
  else
    lglprt (lgl, 2, "[basicprobe-%d-%d] scheduled %d probes %.0f%%",
	    lgl->stats->prb.basic.count, round,
	    res, lglpcnt (res, lglrem (lgl)));
  return res;
}

static void lglsetprbasiclim (LGL * lgl) {
  int64_t limit, irrlim;
  int pen, szpen;
  if (lgl->opts->prbasicrtc.val || lgl->opts->prbrtc.val) {
    lgl->limits->prb.steps = LLMAX;
    lglprt (lgl, 1,
      "[basicprobe-%d] really no limit (run to completion)", 
      lgl->stats->prb.basic.count);
  } else {
    limit = (lgl->opts->prbasicreleff.val*lglvisearch (lgl))/1000;
    if (limit < lgl->opts->prbasicmineff.val)
      limit = lgl->opts->prbasicmineff.val;
    if (lgl->opts->prbasicmaxeff.val >= 0 &&
	limit > lgl->opts->prbasicmaxeff.val)
      limit = lgl->opts->prbasicmaxeff.val;
    limit >>= (pen = lgl->limits->prb.basic.pen + (szpen = lglszpen (lgl)));
    irrlim = (8*lgl->stats->irr.clauses.cur) >> szpen;
    if (lgl->opts->irrlim.val && limit < irrlim) {
      limit = irrlim;
      lglprt (lgl, 1,
    "[basicprobe-%d] limit %lld based on %d irredundant clauses penalty %d",
	lgl->stats->prb.basic.count,
	(LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
    } else
      lglprt (lgl, 1, "[basicprobe-%d] limit %lld penalty %d = %d + %d",
	lgl->stats->prb.basic.count, (LGLL) limit,
	pen, lgl->limits->prb.basic.pen, szpen);
    lgl->limits->prb.steps = lgl->stats->prb.basic.steps + limit;
  }
}

static void lglbasicprobereport (LGL * lgl,
                                 int probed, int nprobes, double start) {
  lglgenericreport (lgl,
    "basicprobe", lgl->stats->prb.basic.count, probed, nprobes, start);
}

static int lglbasicprobe (LGL * lgl) {
#ifndef NLGLOG
  int origprobed = lgl->stats->prb.basic.probed;
#endif
  int origfailed = lgl->stats->prb.basic.failed;
  int origlifted = lgl->stats->prb.basic.lifted;
  int orighbr = lgl->stats->hbr.cnt;
  int root, failed, lifted, units, first, idx;
  int oldrem, deltarem, deltahbr, remprobes;
  int nprobes, success, round, probed;
  int oldhbr, oldfailed, oldlifted;
  Stk probes, lift, saved;
  unsigned pos, delta;
  double start;
  if (!lgl->nvars) return 1;
  if (!lgl->opts->probe.val) return 1;
  if (lgldelaying (lgl, "basicprobe",
        &lgl->limits->prb.basic.del.rem)) return 1;
  lglstart (lgl, &lgl->times->prb.basic);
  lgl->stats->prb.basic.count++;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  assert (!lgl->simp && !lgl->probing && !lgl->basicprobing);
  lgl->simp = lgl->probing = lgl->basicprobing = 1;
  CLR (lift); CLR (probes); CLR (saved);
  lglsetprbasiclim (lgl);
  oldfailed = origfailed;
  oldlifted = origlifted;
  oldhbr = lgl->stats->hbr.cnt;
  oldrem = lglrem (lgl);
  round = 0;
RESTART:
  nprobes = lglschedbasicprobe (lgl, &probes, round);
  remprobes = 0;
  if (!nprobes) goto DONE;
  pos = lglrand (lgl) % nprobes;
  delta = lglrand (lgl) % nprobes;
  if (!delta) delta++;
  probed = 0;
  start = lglgetime (lgl);
  lglbasicprobereport (lgl, probed, nprobes, start);
  while (lglgcd (delta, nprobes) > 1)
    if (++delta == nprobes) delta = 1;
  LOG (1, "probing start %u delta %u mod %u", pos, delta, nprobes);
  first = 0;
  while (!lgl->mt) {
    if (lgl->stats->prb.basic.steps >= lgl->limits->prb.steps) break;
    if (lglterminate (lgl)) break;
    if (!lglsyncunits (lgl)) break;
    assert (pos < (unsigned) nprobes);
    root = probes.start[pos];
    probes.start[pos] = 0;
    if (!root || root == first) {
      lglprt (lgl, 1,
        "[basicprobe-%d-%d] %d sched %.0f%%, %d failed, %d lifted, %d hbrs",
	lgl->stats->prb.basic.count, round,
	nprobes, lglpcnt (nprobes, lglrem (lgl)),
        lgl->stats->prb.basic.failed - oldfailed,
        lgl->stats->prb.basic.lifted - oldlifted,
        lgl->stats->hbr.cnt - oldhbr);
      for (idx = 2; idx < lgl->nvars; idx++)
	lglavar (lgl, idx)->donotbasicprobe = 0;
      break;
    }
    lglavar (lgl, root)->donotbasicprobe = 1;
    if (!first) first = root;
    pos += delta;
    if (pos >= nprobes) pos -= nprobes;
    if (!lglisfree (lgl, root)) continue;
    lglbasicprobereport (lgl, ++probed, nprobes, start);
    lglbasicprobelit (lgl, root);
  }
  lglbasicprobereport (lgl, probed, nprobes, start);
  if (!lgl->mt) {
    if (lgl->stats->prb.basic.steps >= lgl->limits->prb.steps) {
      while (!lglmtstk (&probes))
	if((idx = lglpopstk (&probes)) && lglisfree (lgl, idx)) remprobes++;
      lglprt (lgl, 1, 
        "[basicprobe-%d-%d] %d probes remain %.0f%% after last round",
	lgl->stats->prb.basic.count, round,
	remprobes, lglpcnt (remprobes, lglrem (lgl)));
    } else if (round >= lgl->opts->prbasicroundlim.val) {
      lglprt (lgl, 1,
	      "[basicprobe-%d-%d] round limit %d hit",
	      lgl->stats->prb.basic.count, round, 
	      lgl->opts->prbasicroundlim.val);
    } else if (lgl->stats->prb.basic.failed > oldfailed ||
               lgl->stats->prb.basic.lifted > oldlifted ||
	       lgl->stats->hbr.cnt > oldhbr) {
      oldfailed = lgl->stats->prb.basic.failed;
      oldlifted = lgl->stats->prb.basic.lifted;
      lglclnstk (&probes);
      if (oldhbr < lgl->stats->hbr.cnt && lgl->opts->decompose.val)
	if (!lgldecomp (lgl)) goto DONE;
      oldhbr = lgl->stats->hbr.cnt;
      round++;
      goto RESTART;
    } else {
      assert (!remprobes);
      lglprt (lgl, 1,
	      "[basicprobe-%d-%d] fully completed probing",
	      lgl->stats->prb.basic.count, round);
      for (idx = 2; idx < lgl->nvars; idx++)
	lglavar (lgl, idx)->donotbasicprobe = 0;
    }
  }
DONE:
  lglrelstk (lgl, &lift);
  lglrelstk (lgl, &probes);
  lglrelstk (lgl, &saved);

  assert (lgl->stats->hbr.cnt >= orighbr);
  assert (lglrem (lgl) <= oldrem);
  deltarem = oldrem - lglrem (lgl);
  deltahbr = lgl->stats->hbr.cnt - orighbr;
  success = deltarem || deltahbr;
  LGLUPDPEN (prb.basic, deltarem);
  assert (lgl->stats->prb.basic.failed >= origfailed);
  assert (lgl->stats->prb.basic.lifted >= origlifted);
  failed = lgl->stats->prb.basic.failed - origfailed;
  lifted = lgl->stats->prb.basic.lifted - origlifted;
#ifndef NLGLOG
  assert (lgl->stats->prb.basic.probed >= origprobed);
  probed = lgl->stats->prb.basic.probed - origprobed;
  LOG (1, "%ssuccessfully probed %d out of %d probes %.1f%%",
       success ? "" : "un", probed, nprobes, lglpcnt (probed, nprobes));
  LOG (1, "found %d failed %.1f%% lifted %d through probing",
       failed, lglpcnt (failed, probed), lifted);
#endif
  assert (lgl->probing && lgl->simp && lgl->basicprobing);
  lgl->simp = lgl->probing = lgl->basicprobing = 0;
  units = failed + lifted;
  lglprt (lgl, 1 + !units,
    "[basicprobe-%d-%d] %d units = %d failed (%.0f%%) + %d lifted (%.0f%%)",
    lgl->stats->prb.basic.count, round,
    units, failed, lglpcnt (failed, units), lifted, lglpcnt (lifted, units));
  lglprt (lgl, 1 + !success,
    "[basicprobe-%d-%d] removed %d variables, found %d hbrs",
    lgl->stats->prb.basic.count, round, deltarem, deltahbr);
  lglrep (lgl, 2, 'p');
  lglstop (lgl);
  lglbasicatestats (lgl);
  return !lgl->mt;
}

static int lglsmallirr (LGL * lgl) {
  int maxirrlidx = lglcntstk (&lgl->irr), limit;
  int64_t tmp = MAXREDLIDX;
  tmp *= lgl->opts->smallirr.val;
  tmp /= 100;
  limit = (tmp < INT_MAX) ? tmp : INT_MAX;
  if (maxirrlidx >= limit) return 0;
  return  1;
}

static int lglprobe (LGL * lgl) {
  int res = 1, mod = 0, all, small = lglsmallirr (lgl);
  int (*prb[3])(LGL *);
  lglstart (lgl, &lgl->times->probe);
  if (small && lgl->opts->prbsimple.val) prb[mod++] = lglsimpleprobe;
  if (small && lgl->opts->treelook.val) prb[mod++] = lgltreelook;
  if (lgl->opts->prbasic.val) prb[mod++] = lglbasicprobe;
  all = lgl->stats->prb.simple.count;
  all += lgl->stats->prb.basic.count;
  all += lgl->stats->prb.treelook.count;
  if (lgl->stats->simp.count == 2) {
    int i;
    res = 1;
    for (i = 0; res && i < mod; i++) res = prb[i] (lgl);
  } else res = mod ? prb[all % mod] (lgl) : 1;
  lglstop (lgl);
  return res;
}

static void lglinitevars (LGL * lgl) {
  EVar * ev;
  int idx;
  assert (lgl->occs);
  NEW (lgl->evars, lgl->nvars);
  for (idx = 2; idx < lgl->nvars; idx++) {
    ev = lgl->evars + idx;
    ev->pos = -1;
  }
}

static void lgldense (LGL * lgl, int rmredbintrn) {
  int lit, lidx, count, idx, other, other2, blit, sign, tag, red;
  const int * start, * top, * c, * p, * eow;
  int * q, * w;
  EVar * ev;
  HTS * hts;
  LOG (1, "transition to dense mode");
  assert (!lgl->dense);
  assert (!lgl->rmredbintrn);
  assert (!lgl->evars);
  assert (lglsmallirr (lgl));
  assert (lglmtstk (&lgl->esched));
  assert (lglmtstk (&lgl->saved.bin));
  assert (lglmtstk (&lgl->saved.trn));
  assert (!lgl->eliminating || !lgl->elm->pivot);
  lgl->stats->dense++;
  if (rmredbintrn) {
    lgl->rmredbintrn = 1;
    LOG (1, "temporarily removing redundant binary and ternary clauses");
  }
  count = 0;
  if (lgl->occs) lglinitevars (lgl);
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->count) continue;
      q = w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	red = blit & REDCS;
	if (red) {
	   if (tag == LRGCS) continue;
	   if (rmredbintrn) {
	     assert (tag == BINCS || tag == TRNCS);
	     other = blit >> RMSHFT;
	     if (abs (other) < idx) continue;
	     if (tag == TRNCS) {
	       other2 = *p;
	       if (abs (other2) < idx) continue;
	       lglpushstk (lgl, &lgl->saved.trn, lit);
	       lglpushstk (lgl, &lgl->saved.trn, other);
	       lglpushstk (lgl, &lgl->saved.trn, other2);
	       assert (lgl->stats->red.trn);
	       lgl->stats->red.trn--;
	     } else {
	       lglpushstk (lgl, &lgl->saved.bin, lit);
	       lglpushstk (lgl, &lgl->saved.bin, other);
	       assert (lgl->stats->red.bin);
	       lgl->stats->red.bin--;
	     }
	   } else {
	     *q++ = blit;
	     if (tag == TRNCS) *q++ = *p;
	   }
	} else {
	  *q++ = blit;
	  if (tag == LRGCS || tag == TRNCS) *q++ = *p;
	  if (tag == LRGCS) continue;
	  assert (tag == BINCS || tag == TRNCS);
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  if (tag == TRNCS) {
	    other2 = *p;
	    if (abs (other2) < idx) continue;
	    lglincocc (lgl, other2), count++;
	  }
	  lglincocc (lgl, lit), count++;
	  lglincocc (lgl, other), count++;
	}
      }
      lglshrinkhts (lgl, hts, q - w);
    }
  lglfitstk (lgl, &lgl->saved.bin);
  lglfitstk (lgl, &lgl->saved.trn);
  if (count)
    LOG (1, "counted %d occurrences in small irredundant clauses", count);
  {
    count = 0;
    start = lgl->irr.start;
    top = lgl->irr.top;
    for (c = start; c < top; c = p + 1) {
      p = c;
      if (*c >= NOTALIT) continue;
      lidx = c - start;
      assert (0 <= lidx), assert (lidx < MAXIRRLIDX);
      blit = (lidx << RMSHFT) | OCCS;
      for (; (lit = *p); p++) {
	hts = lglhts (lgl, lit);
	lglpushwch (lgl, hts, blit);
	lglincocc (lgl, lit), count++;
      }
    }
  }
  if (count)
    LOG (1, "counted %d occurrences in large irredundant clauses", count);
  count = 0;
  if (lgl->occs) {
    for (idx = 2; idx < lgl->nvars; idx++) {
      ev = lglevar (lgl, idx);
      if (ev->pos >= 0) continue;
      if (lglifrozen (lgl, idx)) continue;
      if (lgl->donotsched) {
	AVar * av = lglavar (lgl, idx);
	if (lgl->eliminating && av->donotelm) continue;
	if (lgl->blocking && av->donotblk) continue;
      }
      assert (!ev->occ[0] && !ev->occ[1]);
      lglesched (lgl, idx);
      count++;
    }
    if (count) LOG (1, "scheduled %d zombies", count);
  }
  LOG (1, "continuing in dense mode");
  lgl->dense = 1;
  lglfullyconnected (lgl);
  if (lgl->occs && lgl->opts->verbose.val >= 1) {
    const char * str;
    int inst, vl;
    count = 0;
    if (lgl->eliminating) str = "elim", inst = lgl->stats->elm.count, vl = 1;
    else if (lgl->blocking) str = "block", inst = lgl->stats->blk.count, vl=1;
    else str = "dense", inst = lgl->stats->dense, vl = 2;
    for (idx = 2; idx < lgl->nvars; idx++)
      if (lglevar (lgl, idx)->pos >= 0) count++;
    lglprt (lgl, vl,
      "[%s-%d] scheduled %d variables %.0f%%",
      str, inst, count, lglpcnt (count, lgl->nvars-2));
  }
}

static void lglsparse (LGL * lgl) {
  int idx, sign, lit, count, blit, tag;
  int * w, *p, * eow, * q;
  HTS * hts;
  assert (!lgl->notfullyconnected);
  assert (lgl->dense);
  lgl->stats->sparse++;
  count = 0;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      if (!hts->count) continue;
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = q = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == OCCS) { count++; continue; }
	*q++ = blit;
	if (tag == BINCS) continue;
	assert (tag == LRGCS || tag == TRNCS);
	assert (p + 1 < eow);
	*q++ = *++p;
      }
      assert (hts->count - (p - q) == q - w);
      lglshrinkhts (lgl, hts, q - w);
    }
  if (lgl->occs) {
    DEL (lgl->evars, lgl->nvars);
    lglrelstk (lgl, &lgl->esched);
  }
  LOG (1, "removed %d full irredundant occurrences", count);
  lgl->dense = 0;
  lgl->notfullyconnected = 1;
  LOG (1, "large clauses not fully connected yet");
}

static int lglm2i (LGL * lgl, int mlit) {
  int res, midx = abs (mlit);
  assert (0 < midx);
  res = lglpeek (&lgl->elm->m2i, midx);
  if (mlit < 0) res = -res;
  return res;
}

static int lgli2m (LGL * lgl, int ilit) {
  AVar * av = lglavar (lgl, ilit);
  int res = av->mark;
  if (!res) {
    res = lglcntstk (&lgl->seen) + 1;
    av->mark = res;
    assert (2*lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm->noccs) - 2);
    assert (2*lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm->mark) - 2);
    assert (2*lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm->occs) - 2);
    assert (lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm->m2i) - 1);
    lglpushstk (lgl, &lgl->seen, abs (ilit));
    lglpushstk (lgl, &lgl->elm->noccs, 0);
    lglpushstk (lgl, &lgl->elm->noccs, 0);
    lglpushstk (lgl, &lgl->elm->mark, 0);
    lglpushstk (lgl, &lgl->elm->mark, 0);
    lglpushstk (lgl, &lgl->elm->occs, 0);
    lglpushstk (lgl, &lgl->elm->occs, 0);
    lglpushstk (lgl, &lgl->elm->m2i, abs (ilit));
    LOG (4, "mapped internal variable %d to marked variable %d",
	 abs (ilit), res);
  }
  if (ilit < 0) res = -res;
  return res;
}

static unsigned lglsig (int lit) {
  unsigned ulit = lglulit (lit), res;
  assert (ulit >= 2);
  ulit -= 2;
  res = (1u << (ulit & 31));
  return res;
}

static void lgladdecl (LGL * lgl, const int * c) {
  int ilit, mlit, umlit, size = 0, next, prev;
  unsigned csig = 0;
  const int * p;
  Val val;
#if !defined (NDEBUG) || !defined (NLGLOG)
  int lidx;
#endif
  LOGCLS (3, c, "copying irredundant clause");
  INCSTEPS (elm.copies);
  size = 0;
  for (p = c; (ilit = *p); p++) {
    val = lglval (lgl, ilit);
    assert (val <= 0);
    if (val < 0) continue;
    size++;
    if (abs (ilit) == lgl->elm->pivot) continue;
    mlit = lgli2m (lgl, ilit);
    assert (abs (mlit) != 1);
    csig |= lglsig (mlit);
  }
  assert (size >= 1);
  next = lglcntstk (&lgl->elm->lits);
#if !defined (NDEBUG) || !defined (NLGLOG)
  lidx = next;
#endif
  assert (next > 0);
  for (p = c; (ilit = *p); p++) {
    val = lglval (lgl, ilit);
    if (val < 0) continue;
    mlit = lgli2m (lgl, ilit);
    lglpushstk (lgl, &lgl->elm->lits, mlit);
    umlit = lglulit (mlit);
    prev = lglpeek (&lgl->elm->occs, umlit);
    lglpushstk (lgl, &lgl->elm->next, prev);
    lglpoke (&lgl->elm->occs, umlit, next++);
    lglpushstk (lgl, &lgl->elm->csigs, csig);
    lglpushstk (lgl, &lgl->elm->sizes, size);
    lgl->elm->noccs.start[umlit]++;
  }
  lglpushstk (lgl, &lgl->elm->lits, 0);
  lglpushstk (lgl, &lgl->elm->next, 0);
  lglpushstk (lgl, &lgl->elm->csigs, 0);
  lglpushstk (lgl, &lgl->elm->sizes, 0);
  lgl->elm->necls++;
  LOGCLS (4, lgl->elm->lits.start + lidx, "copied and mapped clause");
#ifndef NDEBUG
  LOGMCLS (4, lgl->elm->lits.start + lidx, "copied and remapped clause");
  {
    int i, j = 0;
    for (i = 0; c[i]; i++) {
      Val val = lglval (lgl, c[i]);
      assert (val <= 0);
      if (val < 0) continue;
      assert (c[i] == lglm2i (lgl, lglpeek (&lgl->elm->lits, lidx + j++)));
    }
  }
#endif
}

static int lglecls (LGL * lgl, int lit) {
  int blit, tag, red, other, lidx, count;
  const int * p, * w, * eow, * c;
  int d[4];
  HTS * hts;
  LOG (3, "copying irredundant clauses with %d", lit);
  count = 0;
  hts = lglhts (lgl, lit);
  if (!hts->count) return 0;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    red = blit & REDCS;
    if (red) continue;
    if (tag == BINCS || tag == TRNCS) {
      d[0] = lit;
      other = blit >> RMSHFT;
      d[1] = other;
      if (tag == TRNCS) d[2] = *p, d[3] = 0;
      else d[2] = 0;
      c = d;
    } else {
      assert (tag == OCCS);
      lidx = (tag == OCCS) ? (blit >> RMSHFT) : *p;
      c = lglidx2lits (lgl, 0, lidx);
    }
    lgladdecl (lgl, c);
    count++;
  }
  return count;
}

static void lglrstecls (LGL * lgl)  {
  assert (lgl->elm->pivot);
  lglclnstk (&lgl->elm->lits);
  lglclnstk (&lgl->elm->next);
  lglclnstk (&lgl->elm->csigs);
  lglclnstk (&lgl->elm->sizes);
  lglclnstk (&lgl->elm->occs);
  lglclnstk (&lgl->elm->noccs);
  lglclnstk (&lgl->elm->mark);
  lglclnstk (&lgl->elm->m2i);
  lglpopnunmarkstk (lgl, &lgl->seen);
  lgl->elm->pivot = 0;
}

static void lglrelecls (LGL * lgl)  {
  lglrelstk (lgl, &lgl->elm->lits);
  lglrelstk (lgl, &lgl->elm->next);
  lglrelstk (lgl, &lgl->elm->csigs);
  lglrelstk (lgl, &lgl->elm->sizes);
  lglrelstk (lgl, &lgl->elm->occs);
  lglrelstk (lgl, &lgl->elm->noccs);
  lglrelstk (lgl, &lgl->elm->mark);
  lglrelstk (lgl, &lgl->elm->m2i);
  lglrelstk (lgl, &lgl->elm->clv);
}

static void lglinitecls (LGL * lgl, int idx) {
#ifndef NLGLOG
  int clauses;
#endif
  assert (!lgl->elm->pivot);
  assert (idx >= 2);
  assert (lglmtstk (&lgl->elm->lits));
  assert (lglmtstk (&lgl->elm->next));
  assert (lglmtstk (&lgl->elm->csigs));
  assert (lglmtstk (&lgl->elm->sizes));
  assert (lglmtstk (&lgl->elm->occs));
  assert (lglmtstk (&lgl->elm->noccs));
  assert (lglmtstk (&lgl->elm->m2i));
  assert (lglmtstk (&lgl->seen));
  lgl->elm->pivot = idx;
  lglpushstk (lgl, &lgl->elm->mark, 0);
  lglpushstk (lgl, &lgl->elm->mark, 0);
  lglpushstk (lgl, &lgl->elm->occs, 0);
  lglpushstk (lgl, &lgl->elm->occs, 0);
  lglpushstk (lgl, &lgl->elm->noccs, 0);
  lglpushstk (lgl, &lgl->elm->noccs, 0);
  lglpushstk (lgl, &lgl->elm->m2i, 0);
  (void) lgli2m (lgl, idx);
  lglpushstk (lgl, &lgl->elm->lits, 0);
  lglpushstk (lgl, &lgl->elm->next, 0);
  lglpushstk (lgl, &lgl->elm->csigs, 0);
  lglpushstk (lgl, &lgl->elm->sizes, 0);
  lgl->elm->necls = 0;
#ifndef NLGLOG
  clauses =
#endif
  lglecls (lgl, idx);
  lgl->elm->negcls = lgl->elm->necls;
  lgl->elm->neglidx = lglcntstk (&lgl->elm->lits);
#ifndef NLGLOG
  clauses +=
#endif
  lglecls (lgl, -idx);
  LOG (2, "found %d variables in %d clauses with %d or %d",
       lglcntstk (&lgl->seen), clauses, idx, -idx);
  assert (lgl->elm->pivot);
}

static void lglelrmcls (LGL * lgl, int lit, int * c, int clidx) {
  int lidx, i, other, ulit, * lits, * csigs, blit, tag, red, other2;
  int * p, * eow, * w, count;
  HTS * hts;
#ifndef NDEBUG
  int size;
#endif
  lits = lgl->elm->lits.start;
  csigs = lgl->elm->csigs.start;
  assert (lits < c && c < lgl->elm->lits.top - 1);
  lidx = c - lits;
  LOGCLS (2, c, "removing clause");
  for (i = lidx; (other = lits[i]); i++) {
    assert (other < NOTALIT);
    lits[i] = REMOVED;
    csigs[i] = 0;
    ulit = lglulit (other);
    assert (ulit < lglcntstk (&lgl->elm->noccs));
    assert (lgl->elm->noccs.start[ulit] > 0);
    lgl->elm->noccs.start[ulit] -= 1;
  }
#ifndef NDEBUG
  size = lglpeek (&lgl->elm->sizes, lidx);
#endif
  hts = lglhts (lgl, lit);
  assert (hts->count > 0 && hts->count >= clidx);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  blit = tag = count = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    red = blit & REDCS;
    if (red) continue;
    if (count == clidx) break;
    count++;
  }
  assert (count == clidx);
  assert (blit && tag);
  assert (p < eow);
  if (tag == BINCS) {
    assert (size >= 2);
    other = blit >> RMSHFT;
    lglrmbcls (lgl, lit, other, 0);
    lgldrupligdelclsarg (lgl, lit, other, 0);
  } else if (tag == TRNCS) {
    other = blit >> RMSHFT;
    other2 = *p;
    lgldrupligdelclsarg (lgl, lit, other, other2, 0);
    lglrmtcls (lgl, lit, other, other2, 0);
  } else {
    assert (tag == OCCS);
    lidx = (tag == OCCS) ? (blit >> RMSHFT) : *p;
#ifndef NDEBUG
    {
      int * q, * d = lglidx2lits (lgl, 0, lidx);
      for (q = d; *q; q++)
	;
      assert (q - d >= size);
    }
#endif
    lgldrupligdelclsaux (lgl, lglidx2lits (lgl, 0, lidx));
    lglrmlcls (lgl, lidx, 0);
  }
}

#define BWL 2

static int lglbacksub (LGL * lgl, int * c, int str,
                       int ** dptr, int * dlidxptr) {
  int * start = lgl->elm->lits.start, * p, * q, marked = 0, res, * d;
  int lit, ulit, occ, next, osize, other, uolit, size, plit, phase, clidx;
  unsigned ocsig, csig = 0, masksig;
#ifndef NLGLOG
  const char * mode = str ? "strengthening" : "subsumption";
#endif
  LOGMCLS (BWL + 1, c, "backward %s check for clause", mode);
  LOGCLS (BWL + 1, c, "backward %s check for mapped clause", mode);
  phase = (c - start) >= lgl->elm->neglidx;
  for (p = c; (lit = *p); p++)
    if (abs (lit) != 1)
      csig |= lglsig (lit);
  size = p - c;
  assert (csig == lglpeek (&lgl->elm->csigs, c - start));
  assert (size == lglpeek (&lgl->elm->sizes, c - start));
  res = 0;
  if (dptr) *dptr = 0;
  if (dlidxptr) *dlidxptr = 0;

  if (str) phase = !phase;
  lit = phase ? -1 : 1;
  masksig = ~(lglsig (-lit) | lglsig (lit));

  ulit = lglulit (lit);
  occ = lglpeek (&lgl->elm->noccs, ulit);
  if (!str && occ <= 1) return 0;
  if (str && !occ) return 0;
  if (occ > lgl->elm->bkwdocclim) return 0;
  for (next = lglpeek (&lgl->elm->occs, ulit);
       !res && next &&
	 lgl->limits->elm.steps > lgl->stats->elm.steps;
       next = lglpeek (&lgl->elm->next, next)) {
      INCSTEPS (elm.steps);
      if (next == p - start) continue;
      if (phase != (next >= lgl->elm->neglidx)) continue;
      plit = lglpeek (&lgl->elm->lits, next);
      if (plit >= NOTALIT) continue;
      assert (plit == lit);
      osize = lglpeek (&lgl->elm->sizes, next);
      INCSTEPS (elm.steps);
      if (osize > size) continue;
      ocsig = lglpeek (&lgl->elm->csigs, next);
      INCSTEPS (elm.steps);
      assert (ocsig);
      ocsig &= masksig;
      if ((ocsig & ~csig)) continue;
      if (!marked) {
	for (q = c; (other = *q); q++) {
	  if (str && abs (other) == 1) other = -other;
	  uolit = lglulit (other);
	  assert (!lglpeek (&lgl->elm->mark, uolit));
	  lglpoke (&lgl->elm->mark, uolit, 1);
	}
	marked = 1;
        ADDSTEPS (elm.steps, q-c);
      }
      d = lgl->elm->lits.start + next;
      if (c <= d && d < c + size) continue;
      if (str) lgl->stats->elm.strchks++; else lgl->stats->elm.subchks++;
      while (d[-1]) d--;
      assert (c != d);
      LOGMCLS (BWL + 1, d, "backward %s check with clause", mode);
      res = 1;
      for (q = d; res && (other = *q); q++) {
	uolit = lglulit (other);
	res = lglpeek (&lgl->elm->mark, uolit);
      }
      ADDSTEPS (elm.steps, q-d);
      if (!res || !str || osize < size) continue;
      ADDSTEPS (elm.steps, q-d);
      LOGMCLS (BWL, d,
        "static double strengthened by double self-subsuming resolution");
      q = lgl->elm->lits.start;
      if (phase) {
        assert ((c - start) < lgl->elm->neglidx);
        assert ((d - start) >= lgl->elm->neglidx);
	q += lgl->elm->neglidx;
      } else {
        assert (!phase);
        assert ((d - start) < lgl->elm->neglidx);
        assert ((c - start) >= lgl->elm->neglidx);
	assert (!lglpeek (&lgl->elm->lits, 0));
	q++;
      }
      clidx = 0;
      while (q < d) {
	other = *q++;
	if (other >= NOTALIT) {
	  while (*q++)
	    ;
	  continue;
	}
	if (!other) clidx++;
      }
      LOGMCLS (BWL, d,
	"strengthened and subsumed original irredundant clause");
      LOGCLS (BWL, d,
        "strengthened and subsumed mapped irredundant clause");
      *dptr = d, *dlidxptr = clidx;
      assert (res);
  }
  if (marked) {
    for (p = c; (lit = *p); p++) {
      if (str && abs (lit) == 1) lit = -lit;
      ulit = lglulit (lit);
      assert (lglpeek (&lgl->elm->mark, ulit));
      lglpoke (&lgl->elm->mark, ulit, 0);
    }
    ADDSTEPS (elm.steps, q-c);
  }
  return res;
}

static void lglelmsub (LGL * lgl) {
  int clidx, count, subsumed, pivot, * c;
  if (!lgl->opts->elmotfsub.val) return;
  count = clidx = subsumed = 0;
  pivot = lgl->elm->pivot;
  for (c = lgl->elm->lits.start + 1;
       c < lgl->elm->lits.top &&
	 lgl->limits->elm.steps > lgl->stats->elm.steps;
       c++) {
    INCSTEPS (elm.steps);
    if (count++ == lgl->elm->negcls) clidx = 0, pivot = -pivot;
    if (lglbacksub (lgl, c, 0, 0, 0)) {
      subsumed++;
      lgl->stats->elm.sub++;
      LOGMCLS (BWL, c, "subsumed original irredundant clause");
      LOGCLS (3, c, "subsumed mapped irredundant clause");
      lglelrmcls (lgl, pivot, c, clidx);
    } else clidx++;
    while (*c) c++;
  }
  LOG (BWL + !subsumed,
    "subsumed %d clauses containing %d or %d",
    subsumed, lgl->elm->pivot, -lgl->elm->pivot);
}

static int lglelmstr (LGL * lgl) {
  int clidx, count, strengthened, pivot, * c, * p, mlit, ilit, res, found;
  int * d, dlidx;
  int size;
  if (!lgl->opts->elmotfstr.val) return 0;
  count = clidx = strengthened = 0;
  pivot = lgl->elm->pivot;
  res = 0;
  LOG (3, "strengthening with pivot %d", pivot);
  for (c = lgl->elm->lits.start + 1;
       c < lgl->elm->lits.top &&
	 lgl->limits->elm.steps > lgl->stats->elm.steps;
       c++) {
    INCSTEPS (elm.steps);
    if (count++ == lgl->elm->negcls) {
      clidx = 0, pivot = -pivot;
      LOG (3, "strengthening with pivot %d", pivot);
    }
    if (*c == REMOVED) {
      while (*c) { assert (*c == REMOVED); c++; }
      continue;
    }
    if (lglbacksub (lgl, c, 1, &d, &dlidx)) {
      strengthened++;
      lgl->stats->elm.str++;
      LOGMCLS (2, c, "strengthening original irredundant clause");
      LOGCLS (3, c, "strengthening mapped irredundant clause");
      assert (lglmtstk (&lgl->clause));
      found = 0;
      size = 0;
      for (p = c; (mlit = *p); p++) {
	ilit = lglm2i (lgl, *p);
	if (ilit == pivot) { found++; continue; }
	assert (!lglval (lgl, ilit));
	lglpushstk (lgl, &lgl->clause, ilit);
	size++;
      }
      assert (found);
      lglpushstk (lgl, &lgl->clause, 0);
      LOGCLS (2, lgl->clause.start, "static strengthened irredundant clause");
      lgldrupligaddcls (lgl, REDCS);
      if (d) lglelrmcls (lgl, -pivot, d, dlidx);
      lglelrmcls (lgl, pivot, c, clidx);
      lgladdcls (lgl, 0, 0, 1);
      lglclnstk (&lgl->clause);
      if (size == 1) { res = 1; break; }
    } else clidx++;
    while (*c) c++;
  }
  LOG (2, "strengthened %d clauses containing %d or %d",
       strengthened, lgl->elm->pivot, -lgl->elm->pivot);
  return res;
}

static int lglflushclauses (LGL * lgl, int lit) {
  int blit, tag, red, other, other2, count, glue, res;
  const int druplig = lgl->opts->druplig.val;
  const int * p, * w, * eow;
  int lidx, glidx, slidx;
  int * c, * q;
  HTS * hts;
  Stk * s;
#ifndef NDEBUG
  int occs;
#endif
  lglchkirrstats (lgl);
  assert (lgl->probing || lgl->lkhd || lgl->dense);
  hts = lglhts (lgl, lit);
  if (!hts->count) return 0;
#ifndef NDEBUG
  occs = lgl->occs ? lglocc (lgl, lit) : 0;
#endif
  res = 0;
  LOG (2, "flushing clauses with literal %d", lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  count = 0;
  for (p = w; p < eow; p++) {
    if (lgl->blocking) INCSTEPS (blk.steps);
    if (lgl->eliminating) INCSTEPS (elm.steps);
    if (lgl->simpleprobing) INCSTEPS (prb.simple.steps);
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    other = blit >> RMSHFT;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == BINCS) {
      lglrmbwch (lgl, other, lit, red);
      LOG (2, "flushed %s binary clause %d %d", lglred2str (red), lit, other);
      if (druplig) lgldrupligdelclsarg (lgl, lit, other, 0);
      lgldeclscnt (lgl, 2, red, 0);
      if (!red) lgldecocc (lgl, lit), lgldecocc (lgl, other), res++;
      count++;
    } else if (tag == TRNCS) {
      other2 = *p;
      lglrmtwch (lgl, other2, lit, other, red);
      lglrmtwch (lgl, other, lit, other2, red);
      LOG (2, "flushed %s ternary clause %d %d %d",
	   lglred2str (red), lit, other, other2);
      if (druplig) lgldrupligdelclsarg (lgl, lit, other, other2, 0);
      lgldeclscnt (lgl, 3, red, 0);
      if (!red)  {
	lgldecocc (lgl, lit);
	lgldecocc (lgl, other);
	lgldecocc (lgl, other2);
	res++;
      }
      count++;
    } else {
      assert (tag == OCCS || tag == LRGCS);
      if (tag == LRGCS) {
	lidx = *p;
	s = lglidx2stk (lgl, red, lidx);
	if (red) {
	  glue = lidx & GLUEMASK;
	  c = s->start + (lidx >> GLUESHFT);
	} else {
	  glue = 0;
	  c = s->start + lidx;
	}
      } else {
	lidx = (blit >> RMSHFT);
	s = &lgl->irr;
	c = s->start + lidx;
	glue = 0;
      }
      if (c >= s->top || (other = c[0]) >= NOTALIT) continue;
      LOGCLS (2, c, "flushed %s large clause", lglred2str (red));
      if (druplig) lgldrupligdelclsaux (lgl, c);
      if (tag == LRGCS) {
	if (other == lit) other = c[1];
	assert (abs (other) != abs (lit));
	lglrmlwch (lgl, other, red, lidx);
      } else {
	glidx = lidx;
	if (red) glidx <<= GLUESHFT;
	if (c[1] != lit) lglrmlwch (lgl, c[1], red, glidx);
	if (other != lit) lglrmlwch (lgl, other, red, glidx);
      }
      if (red) {
	assert (!glue);
	LGLCHKACT (c[-1]);
	c[-1] = REMOVED;
      } else lgldecocc (lgl, lit);
      for (q = c; (other = *q); q++) { assert (other < NOTALIT);
	*q = REMOVED;
	if (other == lit) continue;
	if (red && glue) continue;
	slidx = lidx;
	if (red && tag == LRGCS) slidx >>= GLUESHFT;
	lglrmlocc (lgl, other, red, slidx);
	if (!red) lgldecocc (lgl, other);
      }
      *q = REMOVED;
      lgldeclscnt (lgl, q - c, red, glue);
      lgltrimlitstk (lgl, red, lidx);
      if (!red) res++;
      count++;
    }
  }
#ifndef NDEBUG
  if (lgl->occs) assert (occs == res);
#endif
  lglshrinkhts (lgl, hts, 0);
  LOG (2, "flushed %d clauses with %d including %d irredundant",
       count, lit, res);
  lglchkirrstats (lgl);
  return res;
}

static int lglflushlits (LGL * lgl, int lit) {
  int blit, tag, red, other, other2, size, satisfied, d[3], glue;
  const int druplig = lgl->opts->druplig.val;
  int * p, * w, * eow, * c, * l, * k;
  int lidx, slidx, glidx;
  int count, res;
  Val val, val2;
  long delta;
  Stk saved;
  Stk * s;

// Some compilers do not like local functions, thus we use macros instead.
//
#define FIXPTRS() do { p += delta, w += delta, eow += delta; } while (0)

  HTS * hts;
  LOG (2, "flushing literal %d from clauses", lit);
  assert (!lgl->level);
  assert (lglifixed (lgl, lit) < 0);
  assert (lgl->dense);
  lglchkirrstats (lgl);
  hts = lglhts (lgl, lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  res = count = 0;
  CLR (saved);
  for (p = w; p < eow; p++) {
    if (lgl->blocking) INCSTEPS (blk.steps);
    if (lgl->eliminating) INCSTEPS (elm.steps);
    if (lgl->simpleprobing) INCSTEPS (prb.simple.steps);
    count++;
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    if (tag == BINCS) {
      other = blit >> RMSHFT;
      assert ((red && lgliselim (lgl, other)) || lglval (lgl, other) > 0);
      lglrmbwch (lgl, other, lit, red);
      LOG (2, "flushed %s binary clause %d %d", lglred2str (red), lit, other);
      if (druplig) lgldrupligdelclsarg (lgl, lit, other, 0);
      lgldeclscnt (lgl, 2, red, 0);
      if (!red) {
	if (lgl->dense) lgldecocc (lgl, lit), lgldecocc (lgl, other);
	res++;
      }
    } else if (tag == TRNCS) {
      other = blit >> RMSHFT;
      other2 = *++p;
      lglrmtwch (lgl, other2, lit, other, red);
      lglrmtwch (lgl, other, lit, other2, red);
      LOG (2, "flushed %s ternary clause %d %d %d",
	   lglred2str (red), lit, other, other2);
      lgldeclscnt (lgl, 3, red, 0);
      if (!red)  {
	if (lgl->dense) {
	  lgldecocc (lgl, lit);
	  lgldecocc (lgl, other);
	  lgldecocc (lgl, other2);
	}
	res++;
      }
      val = lglval (lgl, other);
      val2 = lglval (lgl, other2);
      if (!val && !val2) {
	LOG (2,
  "reducing flushed %s ternary clause %d %d %d to binary %s clause %d %d",
	     lglred2str (red),
	     lit, other, other2,
	     lglred2str (red),
	     other, other2);
	delta = lglwchbin (lgl, other, other2, red);
	delta += lglwchbin (lgl, other2, other, red);
	if (lgl->simpleprobing && lgl->opts->prbsimple.val >= 2)
	  lglwrktouch (lgl, -other), lglwrktouch (lgl, -other2);
	if (delta) FIXPTRS ();
	if (red) {
	  lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
	} else {
	  lglincirr (lgl, 2);
	  if (lgl->dense) lglincocc (lgl, other), lglincocc (lgl, other2);
	}
	if (druplig) lgldrupligaddclsarg (lgl, REDCS, other, other2, 0);
      } else {
#ifndef NDEBUG
	if (!red || (!lgliselim (lgl, other) && !lgliselim (lgl, other2)))
	  assert (val > 0 || val2 > 0);
#endif
      }
      if (druplig) lgldrupligdelclsarg (lgl, lit, other, other2, 0);
    } else {
      assert (tag == OCCS || tag == LRGCS);
      lidx = (tag == LRGCS) ? *++p : (blit >> RMSHFT);
      s = lglidx2stk (lgl, red, lidx);
      c = s->start + (red ? (lidx >> GLUESHFT) : lidx);
      if (c >= s->top || c[0] >= NOTALIT) continue;
      size = satisfied = 0;
      assert (lglmtstk (&saved));
      for (l = c; (other = *l); l++) {
	if (druplig) lglpushstk (lgl, &saved, other);
	if (satisfied) continue;
	if (other == lit) continue;
	if ((val = lglval (lgl, other)) < 0) continue;
	if (val > 0) { satisfied = 1; continue; }
	if (size < 3) d[size] = other;
	size++;
      }
      if (!satisfied && size == 2) {
	LOGCLS (2, c,
	  "reducing to binary %s clause %d %d flushed large %s clause",
	     lglred2str (red), d[0], d[1], lglred2str (red));
	delta = lglwchbin (lgl, d[0], d[1], red);
	delta += lglwchbin (lgl, d[1], d[0], red);
	if (delta) FIXPTRS ();
	if (red) {
	  lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
	} else {
	  lglincirr (lgl, 2);
	  if (lgl->dense) lglincocc (lgl, d[0]), lglincocc (lgl, d[1]);
	}
	if (lgl->simpleprobing && lgl->opts->prbsimple.val >= 2)
	  lglwrktouch (lgl, -d[0]), lglwrktouch (lgl, -d[1]);
	if (druplig) lgldrupligaddclsarg (lgl, REDCS, d[0], d[1], 0);
      }
      if (!satisfied && size == 3) {
	LOGCLS (2, c,
	  "reducing to ternary %s clause %d %d %d flushed large %s clause",
	     lglred2str (red), d[0], d[1], d[2], lglred2str (red));
	delta = lglwchtrn (lgl, d[0], d[1], d[2], red);
	delta += lglwchtrn (lgl, d[1], d[0], d[2], red);
	delta += lglwchtrn (lgl, d[2], d[0], d[1], red);
	if (delta) FIXPTRS ();
	if (red) {
	  lgl->stats->red.trn++, assert (lgl->stats->red.trn > 0);
	} else {
	  lglincirr (lgl, 3);
	  if (lgl->dense) {
	    lglincocc (lgl, d[0]);
	    lglincocc (lgl, d[1]);
	    lglincocc (lgl, d[2]);
	  }
	}
	if (lgl->simpleprobing && lgl->opts->prbsimple.val >= 3)
	  lglwrktouch (lgl, d[0]),
	  lglwrktouch (lgl, d[1]),
	  lglwrktouch (lgl, d[2]); 
	if (druplig) lgldrupligaddclsarg (lgl, REDCS, d[0], d[1], d[2], 0);
      }
      if (lgl->dense && !red) {
	for (l = c; (other = *l); l++) {
	  if (satisfied || size <= 3 || lglval (lgl, other) < 0) {
	    if (!red) lgldecocc (lgl, other);
	    if (other != lit) {
	      slidx = lidx;
	      if (red && tag == LRGCS) slidx >>= GLUESHFT;
	      lglrmlocc (lgl, other, red, slidx);
	    }
	  }
	}
      }
      glidx = lidx;
      if (red && tag == OCCS) glidx <<= GLUESHFT;
      if (c[0] != lit) lglrmlwch (lgl, c[0], red, glidx);
      if (c[1] != lit) lglrmlwch (lgl, c[1], red, glidx);
      if (satisfied || size <= 3) {
	if (red) { LGLCHKACT (c[-1]); c[-1] = REMOVED; }
	for (k = c; (other = *k); k++) *k = REMOVED;
	*k = REMOVED;
	if (red) {
	  glue = (tag == LRGCS) ? (lidx & GLUEMASK) : 0;
	  assert (lgl->stats->lir[glue].clauses > 0);
	  lgl->stats->lir[glue].clauses--;
	  assert (lgl->stats->red.lrg > 0);
	  lgl->stats->red.lrg--;
	} else lgldecirr (lgl, k - c);
      } else {
	for (l = k = c; (other = *l); l++) {
	  if ((val = lglval (lgl, other)) < 0) continue;
	  if (lgl->simpleprobing && lgl->opts->prbsimple.val >= 3)
	    lglwrktouch (lgl, other);
	  assert (abs (other) != abs (lit));
	  assert (!val);
	  *k++ = other;
	}
	assert (size == k - c);
	if (!red && k < l) {
	  assert (lgl->stats->irr.lits.cur >= l - k);
	  lgl->stats->irr.lits.cur -= l - k;
	}
	*k++ = 0;
	while (k <= l) *k++ = REMOVED;
	delta = lglwchlrg (lgl, c[0], c[1], red, glidx);
	delta += lglwchlrg (lgl, c[1], c[0], red, glidx);
	if (delta) FIXPTRS ();
	if (druplig) lgldrupligaddclsaux (lgl, REDCS, c);
      }
      lgltrimlitstk (lgl, red, lidx);
      if (druplig) {
	assert (lglcntstk (&saved) >= 4);
	lglpushstk (lgl, &saved, 0);
	lgldrupligdelclsaux (lgl, saved.start);
	lglclnstk (&saved);
      }
    }
  }
  lglrelstk (lgl, &saved);
  hts = lglhts (lgl, lit);
  lglshrinkhts (lgl, hts, 0);
  LOG (2, "flushed %d occurrences of literal %d including %d irredundant",
       count, lit, res);
  lglchkirrstats (lgl);
  return res;

#undef FIXPTRS

}

static int lglflush (LGL * lgl) {
  int lit, count;
  if (lgl->mt) return 0;
  lglchkirrstats (lgl);
  assert (!lgl->level);
  assert (lgl->probing || lgl->lkhd || lgl->dense);
  if (lgl->flushed == lglcntstk (&lgl->trail)) return 1;
  if (!lglbcp (lgl)) { lglmt (lgl); return 0; }
  if (!lglsyncunits (lgl)) { assert (lgl->mt); return 0; }
  count = 0;
  while  (lgl->flushed < lglcntstk (&lgl->trail)) {
    lit = lglpeek (&lgl->trail, lgl->flushed++);
    lglflushclauses (lgl, lit);
    lglflushlits (lgl, -lit);
    count++;
  }
  LOG (2, "flushed %d literals", count);
  assert (!lgl->mt);
  return 1;
}

static void lglblockinglit (LGL * lgl, int ilit) {
  int elit = lglexport (lgl, ilit), sgnbit = (1 << (elit < 0));
  Ext * ext = lglelit2ext (lgl, elit);
  assert (!ext->equiv);
  assert (!ext->eliminated);
  assert (abs (ext->repr) == abs (ilit));
  if (ext->blocking & sgnbit) return;
  ext->blocking |= sgnbit;
  LOG (3, "marking external %d internal %d as blocking", elit, ilit);
  lgl->stats->blk.lits++;
}

static void lglelmfrelit (LGL * lgl, int mpivot,
			  int * sop, int * eop, int * son, int * eon) {
  int ipivot = mpivot * lgl->elm->pivot, clidx, ilit, tmp, cover, maxcover;
  int * c, * d, * p, * q, lit, nontrivial, idx, sgn, clen, reslen;
  assert (mpivot == 1 || mpivot == -1);
  assert (ipivot);
  LOG (3,
       "blocked clause elimination and forced resolution of clauses with %d",
	ipivot);
  clidx = 0;
  cover = lglpeek (&lgl->elm->noccs, lglulit (-mpivot));
  for (c = sop; c < eop; c = p + 1) {
    if (lgl->eliminating) INCSTEPS (elm.steps);
    if (*c == REMOVED) {
      for (p = c + 1; *p; p++)
	;
      continue;
    }
    maxcover = 0;
    for (p = c; (lit = *p); p++) {
      if (lit == mpivot) continue;
      assert (lit != -mpivot);
      maxcover += lglpeek (&lgl->elm->noccs, lglulit (-lit));
    }
    if (maxcover < cover - 1) { clidx++; continue; }
    for (p = c; (lit = *p); p++) {
      if (lit == mpivot) continue;
      assert (lit != -mpivot);
      idx = abs (lit);
      assert (!lglpeek (&lgl->elm->mark, idx));
      sgn = lglsgn (lit);
      lglpoke (&lgl->elm->mark, idx, sgn);
    }
    nontrivial = 0;
    clen = p - c;
    for (d = son; !nontrivial && d < eon; d = q + 1) {
      INCSTEPS (elm.steps);
      if (*d == REMOVED) {
	for (q = d + 1; *q; q++)
	  ;
	continue;
      }
      INCSTEPS (elm.resolutions);
      LOGMCLS (3, c, "trying forced resolution 1st antecedent");
      LOGMCLS (3, d, "trying forced resolution 2nd antecedent");
      assert (clen > 0);
      reslen = clen - 1;
      for (q = d; (lit = *q); q++) {
	if (lit == -mpivot) continue;
	assert (lit != mpivot);
	idx = abs (lit), sgn = lglsgn (lit);
	tmp = lglpeek (&lgl->elm->mark, idx);
	if (tmp == -sgn) break;
	if (tmp != sgn) reslen++;
      }
      if (lit) {
	while (*++q) ;
	LOG (3, "trying forced resolution ends with trivial resolvent");
      } else {
	LOG (3, "non trivial resolvent in blocked clause elimination");
	nontrivial = INT_MAX;
      }
    }
    for (p = c; (lit = *p); p++) {
      if (lit == mpivot) continue;
      assert (lit != -mpivot);
      idx = abs (lit);
      assert (lglpeek (&lgl->elm->mark, idx) == lglsgn (lit));
      lglpoke (&lgl->elm->mark, idx, 0);
    }
    assert (lgl->opts->elim.val);
    if (!nontrivial &&
        lgl->opts->block.val &&
	lgl->opts->elmblk.val &&
	(!lgl->opts->elmblkwait.val || !lgl->opts->elim.val || lgl->elmrtc)) {
      assert (maxcover >= cover);
      lgl->stats->elm.blkd++;
      LOGMCLS (2, c, "blocked on %d clause", ipivot);
      lglepush (lgl, ipivot);
      for (p = c; (lit = *p); p++) {
	if (lit == mpivot) continue;
	assert (lit != -mpivot);
	ilit = lglm2i (lgl, lit);
	lglepush (lgl, ilit);
      }
      lglepush (lgl, 0);
      lglelrmcls (lgl, ipivot, c, clidx);
      lglblockinglit (lgl, ipivot);
      continue;
    }
    clidx++;
    if (lgl->limits->elm.steps <= lgl->stats->elm.steps) {
      LOG (2, "maximum number of steps in elimination exhausted");
      return;
    }
  }
}

static void lglelmfre (LGL * lgl) {
  int * sop, * eop, * son, * eon;
  assert (lgl->elm->pivot);
  sop = lgl->elm->lits.start + 1;
  eop = son = lgl->elm->lits.start + lgl->elm->neglidx;
  eon = lgl->elm->lits.top;
  lglelmfrelit (lgl, 1, sop, eop, son, eon);
  lglelmfrelit (lgl, -1, son, eon, sop, eop);
}

static void lgleliminated (LGL * lgl, int pivot) {
  AVar * av;
  int elit;
  Ext * e;
  assert (!lglifrozen (lgl, pivot));
  av = lglavar (lgl, pivot);
  assert (av->type == FREEVAR);
  av->type = ELIMVAR;
  lgl->stats->elm.elmd++;
  assert (lgl->stats->elm.elmd > 0);
  lglflushclauses (lgl, pivot);
  lglflushclauses (lgl, -pivot);
  LOG (2, "eliminated %d", pivot);
  elit = lglexport (lgl, pivot);
  e = lglelit2ext (lgl, elit);
  assert (!e->eliminated);
  assert (!e->equiv);
  e->eliminated = 1;
}

static void lglepusheliminated (LGL * lgl, int idx) {
  const int * p, * w, * eow, * c, * l;
  int lit, blit, tag, red, other;
  HTS * hts;
  lit = (lglocc (lgl, idx) < lglocc (lgl, -idx)) ? idx : -idx;
  LOG (3, "keeping clauses with %d for extending assignment", lit);
  hts = lglhts (lgl, lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    red = blit & REDCS;
    if (red) continue;
    lglepush (lgl, lit);
    if (tag == BINCS || tag == TRNCS) {
      lglepush (lgl, blit >> RMSHFT);
      if (tag == TRNCS)
	lglepush (lgl, *p);
    } else {
      assert (tag == OCCS);
      c = lglidx2lits (lgl, 0, blit >> RMSHFT);
      for (l = c; (other = *l); l++)
	if (other != lit)
	  lglepush (lgl, other);
    }
    lglepush (lgl, 0);
  }
  lglepush (lgl, -lit);
  lglepush (lgl, 0);
  lgleliminated (lgl, idx);
}

static int lglunhimpl (const DFPR * dfpr, int a, int b) {
  int u = lglulit (a), v = lglulit (b), c, d, f, g;
  c = dfpr[u].discovered; if (!c) return 0;
  d = dfpr[v].discovered; if (!d) return 0;
  f = dfpr[u].finished, g = dfpr[v].finished;
  assert (0 < c && c < f);
  assert (0 < d && d < g);
  return c < d && g < f;
}

static int lglunhimplies2 (const DFPR * dfpr, int a, int b) {
  return lglunhimpl (dfpr, a, b) || lglunhimpl (dfpr, -b, -a);
}

static int lglunhimplincl (const DFPR * dfpr, int a, int b) {
  int u = lglulit (a), v = lglulit (b), c, d, f, g;
  c = dfpr[u].discovered; if (!c) return 0;
  d = dfpr[v].discovered; if (!d) return 0;
  f = dfpr[u].finished, g = dfpr[v].finished;
  assert (0 < c && c < f);
  assert (0 < d && d < g);
  return c <= d && g <= f;
}

static int lglunhimplies2incl (const DFPR * dfpr, int a, int b) {
  return lglunhimplincl (dfpr, a, b) || lglunhimplincl (dfpr, -b, -a);
}

static int lglhastrn (LGL * lgl, int a, int b, int c) {
  int blit, tag, other, other2;
  const int * w, * eow, * p;
  HTS * ha, * hb, * hc;
  ha = lglhts (lgl, a);
  hb = lglhts (lgl, b);
  if (hb->count < ha->count) { SWAP (int, a, b); SWAP (HTS *, ha, hb); }
  hc = lglhts (lgl, c);
  if (hc->count < ha->count) { SWAP (int, a, c); SWAP (HTS *, ha, hc); }
  w = lglhts2wchs (lgl, ha);
  eow = w + ha->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == OCCS) continue;
    if (tag == BINCS) {
      other = blit >> RMSHFT;
      if (other == b || other == c) return 1;
      continue;
    }
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    assert (tag == TRNCS);
    other = blit >> RMSHFT;
    if (other != b && other != c) continue;
    other2 = *p;
    if (other2 == b || other2 == c) return 1;
  }
  if (hc->count < hb->count) { SWAP (int, b, c); SWAP (HTS *, hb, hc); }
  w = lglhts2wchs (lgl, hb);
  eow = w + hb->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == OCCS) continue;
    if (tag == TRNCS || tag == LRGCS) { p++; continue; }
    assert (tag == BINCS);
    other = blit >> RMSHFT;
    if (other == c) return 1;
  }
  return 0;
}

static int64_t lglfactor (LGL * lgl, int lim, int count) {
  int64_t factor, res;
  if (!count) return lim;
  switch (lgl->opts->factor.val) {
    default: factor = 1; break;
    case 1: factor = lglceild (count); break;
    case 2: factor = count; break;
    case 3: factor = count*(int64_t)count; break;
  }
  if (!factor) factor = 1;
  if (factor > lgl->opts->factmax.val) factor = lgl->opts->factmax.val;
  res = lim * factor;
  return res;
}

static int lglforcedve (LGL * lgl, int idx) {
  int pocc = lglocc (lgl, idx);
  int nocc = lglocc (lgl, -idx);
  int count = lgl->stats->elm.count;
  if (!pocc) return 1;
  if (!nocc) return 1;
  if (pocc + nocc <= lgl->opts->elmoccsumforced.val) return 1;
  if (lgl->opts->elmfull.val) return 0;
  if (pocc >= lglfactor (lgl, lgl->opts->elmocclim1.val, count)) return -1;
  if (nocc >= lglfactor (lgl, lgl->opts->elmocclim1.val, count)) return -1;
  if (pocc < lglfactor (lgl, lgl->opts->elmocclim2.val, count)) return 0;
  if (nocc < lglfactor (lgl, lgl->opts->elmocclim2.val, count)) return 0;
  return -1;
}

static int lgltrylargeve (LGL * lgl) {
  const int * c, * d, * sop, * eop, * son, * eon, * p, * q, * start, * end;
  int lit, idx, sgn, tmp, ip, ilit, npocc, nnocc, limit, count, i, res;
  int clen, dlen, reslen, maxreslen;
  ip = lgl->elm->pivot;
  assert (ip);
  if ((res = lglforcedve (lgl, ip))) return res > 0;
  sop = lgl->elm->lits.start + 1;
  eop = son = lgl->elm->lits.start + lgl->elm->neglidx;
  eon = lgl->elm->lits.top;
  npocc = lglpeek (&lgl->elm->noccs, lglulit (1));
  nnocc = lglpeek (&lgl->elm->noccs, lglulit (-1));
  limit = npocc + nnocc;
  count = 0;
  for (i = 0; i <= 1; i++) {
    start = i ? son : sop;
    end = i ? eon : eop;
    for (c = start; c < end; c++) {
      INCSTEPS (elm.steps);
      if (*c == REMOVED) { while (*c) c++; continue; }
      while ((lit = *c)) {
	(void) lglm2i (lgl, lit);
	c++;
      }
      count++;
    }
  }
  assert (count == limit);
  LOG (3, "trying clause distribution for %d with limit %d", ip, limit);
  maxreslen = 0;
  for (c = sop; c < eop && limit >= 0; c = p + 1) {
    INCSTEPS (elm.steps);
    if (*c == REMOVED) {
      for (p = c + 1; *p; p++)
        ;
      continue;
    }
    assert (lglmtstk (&lgl->resolvent));
    clen = 0;
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      assert (lit != -1);
      idx = abs (lit);
      assert (!lglpeek (&lgl->elm->mark, idx));
      sgn = lglsgn (lit);
      lglpoke (&lgl->elm->mark, idx, sgn);
      ilit = lglm2i (lgl, lit);
      lglpushstk (lgl, &lgl->resolvent, ilit);
      clen++;
    }
    for (d = son; limit >= 0 && d < eon; d = q + 1) {
      INCSTEPS (elm.steps);
      if (*d == REMOVED) {
	for (q = d + 1; *q; q++)
	  ;
	continue;
      }
      INCSTEPS (elm.resolutions);
      LOGMCLS (3, c, "trying resolution 1st antecedent");
      LOGMCLS (3, d, "trying resolution 2nd antecedent");
      dlen = 0;
      reslen = clen;
      for (q = d; (lit = *q); q++) {
	if (lit == -1) continue;
	dlen++;
	assert (lit != 1);
	idx = abs (lit), sgn = lglsgn (lit);
	tmp = lglpeek (&lgl->elm->mark, idx);
	if (tmp == -sgn) break;
	if (tmp == sgn) continue;
	ilit = lglm2i (lgl, lit);
	lglpushstk (lgl, &lgl->resolvent, ilit);
	reslen++;
      }
      assert (reslen == lglcntstk (&lgl->resolvent));
      if (!lit && reslen == 1) {
	LOG (3, "trying resolution ends with unit clause");
	lit = lglpeek (&lgl->resolvent, 0);
	limit += lglevar (lgl, lit)->occ[lit < 0];
      } else if (lit) {
	while (*++q) ;
	LOG (3, "trying resolution ends with trivial resolvent");
      } else {
	limit--;
	LOG (3,
	     "trying resolution with non trivial resolvent remaining %d",
	     limit);
	if (reslen > maxreslen) maxreslen = reslen;
      }
      assert (!*q);
      lglrststk (&lgl->resolvent, clen);
    }
    lglclnstk (&lgl->resolvent);
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      assert (lit != -1);
      idx = abs (lit);
      assert (lglpeek (&lgl->elm->mark, idx) == lglsgn (lit));
      lglpoke (&lgl->elm->mark, idx, 0);
    }
    if (lgl->limits->elm.steps <= lgl->stats->elm.steps) {
      LOG (2, "maximum number of steps in elimination exhausted");
      return 0;
    }
  }
  assert (lglm2i (lgl, 1) == ip);
  if (limit < 0) {
    LOG (3, "resolving away %d would increase number of clauses", ip);
    return 0;
  }
  if (limit) LOG (2, "resolving away %d removes %d clauses", ip, limit);
  else LOG (2, "resolving away %d does not change number of clauses", ip);
  return 1;
}

static void lgldolargeve (LGL * lgl) {
  const int * c, * d, * sop, * eop, * son, * eon, * p, * q, * start, * end;
  int lit, idx, sgn, tmp, ip, ilit, mp, npocc, nnocc;
  int clen, dlen, reslen;
  Val val;
  ip = lgl->elm->pivot;
  assert (ip);
  sop = lgl->elm->lits.start + 1;
  eop = son = lgl->elm->lits.start + lgl->elm->neglidx;
  eon = lgl->elm->lits.top;
  npocc = lglpeek (&lgl->elm->noccs, lglulit (1));
  nnocc = lglpeek (&lgl->elm->noccs, lglulit (-1));
  LOG (2, "(large) variable elimination of %d", lgl->elm->pivot);
  if (npocc < nnocc) start = sop, end = eop, mp = 1;
  else start = son, end = eon, ip = -ip, mp = -1;
  LOG (3, "will save clauses with %d for extending assignment", ip);
  for (c = start; c < end; c = p + 1) {
    INCSTEPS (elm.steps);
    if (*c == REMOVED) {
      for (p = c + 1; *p; p++)
	;
      continue;
    }
    lglepush (lgl, ip);
    for (p = c; (lit = *p); p++)  {
      if (lit == mp) continue;
      assert (lit != -mp);
      ilit = lglm2i (lgl, lit);
      lglepush (lgl, ilit);
    }
    lglepush (lgl, 0);
  }
  lglepush (lgl, -ip);
  lglepush (lgl, 0);
  for (c = sop; c < eop; c = p + 1) {
    INCSTEPS (elm.steps);
    if (*c == REMOVED) {
      for (p = c + 1; *p; p++)
	;
      continue;
    }
    assert (lglmtstk (&lgl->resolvent));
    clen = 0;
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      assert (lit != -1);
      idx = abs (lit);
      assert (!lglpeek (&lgl->elm->mark, idx));
      sgn = lglsgn (lit);
      lglpoke (&lgl->elm->mark, idx, sgn);
      ilit = lglm2i (lgl, lit);
      lglpushstk (lgl, &lgl->resolvent, ilit);
      clen++;
    }
    for (d = son; d < eon; d = q + 1) {
      INCSTEPS (elm.steps);
      if (*d == REMOVED) {
	for (q = d + 1; *q; q++)
	  ;
	continue;
      }
      INCSTEPS (elm.resolutions);
      assert (lglmtstk (&lgl->clause));
      dlen = 0;
      reslen = clen;
      for (q = d; (lit = *q); q++) {
	if (lit == -1) continue;
	dlen++;
	assert (lit != 1);
	idx = abs (lit), sgn = lglsgn (lit);
	tmp = lglpeek (&lgl->elm->mark, idx);
	if (tmp == sgn) continue;
	if (tmp == -sgn) break;
	ilit = lglm2i (lgl, lit);
	val = lglval (lgl, ilit);
	if (val < 0) continue;
	if (val > 0) break;
	lglpushstk (lgl, &lgl->clause, ilit);
	ilit = lglm2i (lgl, lit);
	lglpushstk (lgl, &lgl->resolvent, ilit);
	reslen++;
      }
      assert (reslen == lglcntstk (&lgl->resolvent));
      if (!lit && reslen == 1) {
	goto RESOLVE;
      } if (lit) {
	while (*++q) ;
      } else {
RESOLVE:
	LOGMCLS (3, c, "resolving variable elimination 1st antecedent");
	LOGMCLS (3, d, "resolving variable elimination 2nd antecedent");
	for (p = c; (lit = *p); p++) {
	  if (lit == 1) continue;
	  assert (lit != -1);
	  ilit = lglm2i (lgl, lit);
	  val = lglval (lgl, ilit);
	  if (val < 0) continue;
	  if (val > 0) break;
	  lglpushstk (lgl, &lgl->clause, ilit);
	}
	if (!lit) {
	  lglpushstk (lgl, &lgl->clause, 0);
	  LOGCLS (3, lgl->clause.start, "variable elimination resolvent");
	  lgldrupligaddcls (lgl, REDCS);
	  lgladdcls (lgl, 0, 0, 1);
	}
      }
      lglclnstk (&lgl->clause);
      assert (!*q);
      lglrststk (&lgl->resolvent, clen);
    }
    lglclnstk (&lgl->resolvent);
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      assert (lit != -1);
      idx = abs (lit);
      assert (lglpeek (&lgl->elm->mark, idx) == lglsgn (lit));
      lglpoke (&lgl->elm->mark, idx, 0);
    }
  }
  lgleliminated (lgl, lgl->elm->pivot);
  lgl->stats->elm.large++;
}

static void lglelimlitaux (LGL * lgl, int idx) {
  lglelmsub (lgl);
  if (lglelmstr (lgl)) return;
  lglelmfre (lgl);
  if (lgltrylargeve (lgl)) lgldolargeve (lgl);
}

static int lgls2m (LGL * lgl, int ilit) {
  AVar * av = lglavar (lgl, ilit);
  int res = av->mark;
  if (!res) {
    res = lglcntstk (&lgl->seen) + 1;
    if (res > lgl->opts->smallvevars.val + 1) return 0;
    av->mark = res;
    assert (lglcntstk (&lgl->seen) == lglcntstk (&lgl->elm->m2i) - 1);
    lglpushstk (lgl, &lgl->seen, abs (ilit));
    lglpushstk (lgl, &lgl->elm->m2i, abs (ilit));
    LOG (4, "mapped internal variable %d to marked variable %d",
	 abs (ilit), res);
  }
  if (ilit < 0) res = -res;
  return res;
}

static void lglvar2funaux (int v, Fun res, int negate) {
  uint64_t tmp;
  int i, j, p;
  assert (0 <= v && v < FUNVAR);
  if (v < 6) {
    tmp = lglbasevar2funtab[v];
    if (negate) tmp = ~tmp;
    for (i = 0; i < FUNQUADS; i++)
      res[i] = tmp;
  } else {
    tmp = negate ? ~0ull : 0ull;
    p = 1 << (v - 6);
    j = 0;
    for (i = 0; i < FUNQUADS; i++) {
      res[i] = tmp;
      if (++j < p) continue;
      tmp = ~tmp;
      j = 0;
    }
  }
}

static void lglvar2fun (int v, Fun res) {
  lglvar2funaux (v, res, 0);
}

static void lglnegvar2fun (int v, Fun res) {
  lglvar2funaux (v, res, 1);
}

static void lglfuncpy (Fun dst, const Fun src) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    dst[i] = src[i];
}

static void lglfalsefun (Fun res) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    res[i] = 0ll;
}

static void lgltruefun (Fun res) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    res[i] = ~0ll;
}

static int lglisfalsefun (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (f[i] != 0ll) return 0;
  return 1;
}

static int lglistruefun (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (f[i] != ~0ll) return 0;
  return 1;
}

static void lglorfun (Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] |= b[i];
}

static void lglornegfun (Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] |= ~b[i];
}

static void lglor3fun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] = b[i] | c[i];
}

static void lglor3negfun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] = b[i] | ~c[i];
}

static void lglandornegfun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] &= b[i] | ~c[i];
}

static void lglandfun (Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] &= b[i];
}

static void lgland3fun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] = b[i] & c[i];
}

static void lgland3negfun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    a[i] = b[i] & ~c[i];
}

static void lglsrfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  assert (0 <= shift);
  b = shift & 63;
  q = shift >> 6;
  j = 0;
  i = q;
  assert (i >= 0);
  l = 64 - b;
  while (j < FUNQUADS) {
    if (i < FUNQUADS) {
      tmp = a[i] >> b;
      rest = (b && i+1 < FUNQUADS) ? (a[i+1] << l) : 0ull;
      a[j] = rest | tmp;
    } else a[j] = 0ull;
    i++, j++;
  }
}

static void lglslfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  assert (0 <= shift);
  b = shift & 63;
  q = shift >> 6;
  j = FUNQUADS - 1;
  i = j - q;
  l = 64 - b;
  while (j >= 0) {
    if (i >= 0) {
      tmp = a[i] << b;
      rest = (b && i > 0) ? (a[i-1] >> l) : 0ll;
      a[j] = rest | tmp;
    } else a[j] = 0ll;
    i--, j--;
  }
}

static void lgls2fun (int mlit, Fun res) {
  int midx = abs (mlit), sidx = midx - 2;
  assert (0 <= sidx && sidx < FUNVAR);
  if (mlit < 0) lglnegvar2fun (sidx, res);
  else lglvar2fun (sidx, res);
}

static int lglinitsmallve (LGL * lgl, int lit, Fun res) {
  int blit, tag, red, other, other2, lidx, mlit;
  const int * p, * w, * eow, * c, * q;
  Fun cls, tmp;
  HTS * hts;
  Val val;
  assert (!lglval (lgl, lit));
  LOG (3, "initializing small variable eliminiation for %d", lit);
#ifndef NDEBUG
  mlit =
#endif
  lgls2m (lgl, lit);
  assert (abs (mlit) == 1);
  hts = lglhts (lgl, lit);
  lgltruefun (res);
  if (!hts->count) goto DONE;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    INCSTEPS (elm.steps);
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    red = blit & REDCS;
    if (red) continue;
    lglfalsefun (cls);
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      val = lglval (lgl, other);
      assert (val <= 0);
      if (!val) {
	mlit = lgls2m (lgl, other);
	if (!mlit) return 0;
	lgls2fun (mlit, tmp);
	lglorfun (cls, tmp);
      }
      if (tag == TRNCS) {
	other2 = *p;
	val = lglval (lgl, other2);
	assert (val <= 0);
	if (!val) {
	  mlit = lgls2m (lgl, other2);
	  if (!mlit) return 0;
	  lgls2fun (mlit, tmp);
	  lglorfun (cls, tmp);
	}
      }
    } else {
      assert (tag == OCCS);
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      for (q = c; (other = *q); q++) {
	if (other == lit) continue;
	assert (other != -lit);
	val = lglval (lgl, other);
	assert (val <= 0);
	if (!val) {
	  mlit = lgls2m (lgl, other);
	  if (!mlit) return 0;
	  lgls2fun (mlit, tmp);
	  lglorfun (cls, tmp);
	}
      }
    }
    assert (!lglisfalsefun (cls));
    assert (!lglistruefun (cls));
    lglandfun (res, cls);
    INCSTEPS (elm.copies);
  }
DONE:
  return 1;
}

static void lglresetsmallve (LGL * lgl) {
  lglclnstk (&lgl->elm->m2i);
  lglclnstk (&lgl->elm->clv);
  lglpopnunmarkstk (lgl, &lgl->seen);
}

static void lglsmallevalcls (unsigned cls, Fun res) {
  Fun tmp;
  int v;
  lglfalsefun (res);
  for (v = 0; v < FUNVAR; v++) {
    if (cls & (1 << (2*v + 1))) {
      lglvar2fun (v, tmp);
      lglornegfun (res, tmp);
    } else if (cls & (1 << (2*v))) {
      lglvar2fun (v, tmp);
      lglorfun (res, tmp);
    }
  }
}

static Cnf lglpos2cnf (int pos) { assert (pos >=0 ); return pos; }
static Cnf lglsize2cnf (int s) { assert (s >=0 ); return ((Cnf)s) << 32; }
static int lglcnf2pos (Cnf cnf) { return cnf & 0xfffffll; }
static int lglcnf2size (Cnf cnf) { return cnf >> 32; }

static Cnf lglcnf (int pos, int size) {
  return lglpos2cnf (pos) | lglsize2cnf (size);
}

static void lglsmallevalcnf (LGL * lgl, Cnf cnf, Fun res) {
  Fun tmp;
  int i, n, p, cls;
  p = lglcnf2pos (cnf);
  n = lglcnf2size (cnf);
  lgltruefun (res);
  for (i = 0; i < n; i++) {
    cls = lglpeek (&lgl->elm->clv, p + i);
    lglsmallevalcls (cls, tmp);
    lglandfun (res, tmp);
  }
}

static void lglnegcofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  lglvar2fun (v, mask);
  lgland3negfun (masked, f, mask);
  lglfuncpy (res, masked);
  lglslfun (masked, (1 << v));
  lglorfun (res, masked);
}

static void lglposcofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  lglvar2fun (v, mask);
  lgland3fun (masked, f, mask);
  lglfuncpy (res, masked);
  lglsrfun (masked, (1 << v));
  lglorfun (res, masked);
}

static int lglsmallfundeps0 (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (((f[i] & 0xaaaaaaaaaaaaaaaaull)>>1) !=
         (f[i] & 0x5555555555555555ull)) return 1;
  return 0;
}

static int lglsmallfundeps1 (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (((f[i] & 0xccccccccccccccccull)>>2) !=
         (f[i] & 0x3333333333333333ull)) return 1;
  return 0;
}

static int lglsmallfundeps2 (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (((f[i] & 0xf0f0f0f0f0f0f0f0ull)>>4) !=
         (f[i] & 0x0f0f0f0f0f0f0f0full)) return 1;
  return 0;
}

static int lglsmallfundeps3 (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (((f[i] & 0xff00ff00ff00ff00ull)>>8) !=
         (f[i] & 0x00ff00ff00ff00ffull)) return 1;
  return 0;
}

static int lglsmallfundeps4 (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (((f[i] & 0xffff0000ffff0000ull)>>16) !=
         (f[i] & 0x0000ffff0000ffffull)) return 1;
  return 0;
}

static int lglsmallfundeps5 (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (((f[i] & 0xffffffff00000000ull)>>32) !=
         (f[i] & 0x00000000ffffffffull)) return 1;
  return 0;
}

static int lglsmallfundepsgen (const Fun f, int min) {
  const int c = (1 << (min - 6));
  int i, j;
  assert (min >= 6);
  for (i = 0; i < FUNQUADS; i += (1 << (min - 5)))
    for (j = 0; j < c; j++)
      if (f[i + j] != f[i + c + j]) return 1;
  return 0;
}

static int lglsmalltopvar (const Fun f, int min) {
  int i;
  switch (min) {
    case 0: if (lglsmallfundeps0 (f)) return 0;
    case 1: if (lglsmallfundeps1 (f)) return 1;
    case 2: if (lglsmallfundeps2 (f)) return 2;
    case 3: if (lglsmallfundeps3 (f)) return 3;
    case 4: if (lglsmallfundeps4 (f)) return 4;
    case 5: if (lglsmallfundeps5 (f)) return 5;
  }
  for (i = lglmax (6, min); i <= FUNVAR - 2; i++)
    if (lglsmallfundepsgen (f, i)) return i;
  return i;
}

static Cnf lglsmalladdlit2cnf (LGL * lgl, Cnf cnf, int lit) {
  int p, m, q, n, i, cls;
  Cnf res;
  p = lglcnf2pos (cnf);
  m = lglcnf2size (cnf);
  q = lglcntstk (&lgl->elm->clv);
  for (i = 0; i < m; i++) {
    cls = lglpeek (&lgl->elm->clv, p + i);
    assert (!(cls & lit));
    cls |= lit;
    lglpushstk (lgl, &lgl->elm->clv, cls);
  }
  n = lglcntstk (&lgl->elm->clv) - q;
  res = lglcnf (q, n);
  return res;
}

#ifndef NDEBUG
static int lglefun (const Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (a[i] & ~b[i]) return 0;
  return 1;
}
#endif

// The dual version of Minato's algorithm for computing an irredundant
// product of sums.   The original algorithm computes an irredundant sum of
// products. It uses BDDs for representing boolean functions and ZDDs for
// manipulating sum of product.  We work with function tables stored as bit
// maps and plain CNFs stored as lists of clauses instead.

static Cnf lglsmallipos (LGL * lgl, const Fun U, const Fun L, int min) {
  Fun U0, U1, L0, L1, Unew, ftmp;
  Cnf c0, c1, cstar, ctmp, res;
  int x, y, z;
  assert (lglefun (L, U));
  if (lglistruefun (U)) return TRUECNF;
  if (lglisfalsefun (L)) return FALSECNF;
  lgl->stats->elm.ipos++;
  assert (min < lglcntstk (&lgl->elm->m2i));
  y = lglsmalltopvar (U, min);
  z = lglsmalltopvar (L, min);
  INCSTEPS (elm.steps);
  x = (y < z) ? y : z;
  assert (x < FUNVAR);
  lglnegcofactorfun (U, x, U0); lglposcofactorfun (U, x, U1);
  lglnegcofactorfun (L, x, L0); lglposcofactorfun (L, x, L1);
  lglor3negfun (ftmp, U0, L1);
  c0 = lglsmallipos (lgl, ftmp, L0, min+1);
  lglor3negfun (ftmp, U1, L0);
  c1 = lglsmallipos (lgl, ftmp, L1, min+1);
  lglsmallevalcnf (lgl, c0, ftmp);
  lglor3negfun (Unew, U0, ftmp);
  lglsmallevalcnf (lgl, c1, ftmp);
  lglandornegfun (Unew, U1, ftmp);
  lglor3fun (ftmp, L0, L1);
  cstar = lglsmallipos (lgl, Unew, ftmp, min+1);
  assert (cstar != FALSECNF);
  ctmp = lglsmalladdlit2cnf (lgl, c1, (1 << (2*x + 1)));
  res = lglcnf2pos (ctmp);
  ctmp = lglsmalladdlit2cnf (lgl, c0, (1 << (2*x)));
  if (res == TRUECNF) res = lglcnf2pos (ctmp);
  ctmp = lglsmalladdlit2cnf (lgl, cstar, 0);
  if (res == TRUECNF) res = lglcnf2pos (ctmp);
  res |= lglsize2cnf (lglcntstk (&lgl->elm->clv) - res);
  return res;
}

static void lglsmallve (LGL * lgl, Cnf cnf) {
  int * soc = lgl->elm->clv.start + lglcnf2pos (cnf);
  int * eoc = soc + lglcnf2size (cnf);
  int * p, cls, v, lit, trivial;
  Val val;
  for (p = soc; !lgl->mt && p < eoc; p++) {
    cls = *p;
    assert (lglmtstk (&lgl->clause));
    trivial = 0;
    for (v = 0; v < FUNVAR; v++) {
      if (cls & (1 << (2*v + 1))) lit = -lglm2i (lgl, v+2);
      else if (cls & (1 << (2*v))) lit = lglm2i (lgl, v+2);
      else continue;
      val = lglval (lgl, lit);
      if (val < 0) continue;
      if (val > 0) trivial = 1;
      lglpushstk (lgl, &lgl->clause, lit);
    }
    if (!trivial) {
      INCSTEPS (elm.resolutions);
      lglpushstk (lgl, &lgl->clause, 0);
      LOGCLS (3, lgl->clause.start, "small elimination resolvent");
      lgldrupligaddcls (lgl, REDCS);
      lgladdcls (lgl, 0, 0, 1);
    }
    lglclnstk (&lgl->clause);
  }
}

static int lglsmallisunitcls (LGL * lgl, int cls) {
  int fidx, fsign, flit, mlit, ilit;
  ilit = 0;
  for (fidx = 0; fidx < FUNVAR; fidx++)
    for (fsign = 0; fsign <= 1; fsign++) {
      flit = 1<<(2*fidx + fsign);
      if (!(cls & flit)) continue;
      if (ilit) return 0;
      mlit = (fidx + 2) * (fsign ? -1 : 1);
      ilit = lglm2i (lgl, mlit);
    }
  return ilit;
}

static int lglsmallcnfunits (LGL * lgl, Cnf cnf) {
  int p, m, i, res, cls, ilit;
  p = lglcnf2pos (cnf);
  m = lglcnf2size (cnf);
  res = 0;
  for (i = 0; i < m; i++) {
    cls = lglpeek (&lgl->elm->clv, p + i);
    ilit = lglsmallisunitcls (lgl, cls);
    if (!ilit) continue;
    assert (lglval (lgl, ilit) >= 0);
    lglunit (lgl, ilit);
    res++;
  }
  return res;
}

static int lgltrysmallve (LGL * lgl, int idx) {
  int res, new, old, units;
  Fun pos, neg, fun;
  EVar * ev;
  Cnf cnf;
  assert (lglmtstk (&lgl->elm->m2i));
  assert (lglmtstk (&lgl->seen));
  assert (lglmtstk (&lgl->elm->clv));
  if (!lgl->opts->smallve.val) return 0;
  if (lgl->opts->smallvewait.val && !lgl->elmrtc) return 0;
  lglpushstk (lgl, &lgl->elm->m2i, 0);
  lglpushstk (lgl, &lgl->elm->clv, 0);
  res = 0;
  if (lglinitsmallve (lgl, idx, pos) && lglinitsmallve (lgl, -idx, neg)) {
    lglor3fun (fun, pos, neg);
    cnf = lglsmallipos (lgl, fun, fun, 0);
    new = lglcnf2size (cnf);
    units = lglsmallcnfunits (lgl, cnf);
    assert (units <= new);
    new -= units;
    ev = lglevar (lgl, idx);
    old = ev->occ[0] + ev->occ[1];
    LOG (2,
"small elimination of %d replaces %d old with %d new clauses and %d units",
      idx, old, new, units);
    lgl->stats->elm.small.tried++;
    if (new > old) {
      if (units > 0) {
	LOG (2,
"unforced small elimination of %d would add %d clauses but produces %d units",
	  idx, new - old, units);
        res = 1;
      } else {
	LOG (2,
"unforced small elimination of %d would add %d clauses considered failed",
	  idx, new - old);
        lgl->stats->elm.small.failed++;
      }
    } else {
      LOG (2,
"small elimination of %d removes %d clauses thus considered promising",
	idx, old - new);
      lglepusheliminated (lgl, idx);
      lglflushclauses (lgl, idx);
      lglflushclauses (lgl, -idx);
      lglsmallve (lgl, cnf);
      lgl->stats->elm.small.elm++;
      res = 1;
    }
  } else LOG (2, "too many variables for small elimination");
  lglresetsmallve (lgl);
  return res;
}

static int lgl2manyoccs4elm (LGL * lgl, int lit) {
  return lglocc (lgl, lit) > 
           lglfactor (lgl, lgl->opts->elmocclim.val, lgl->stats->elm.count);
}

static int lglchkoccs4elmlit (LGL * lgl, int lit) {
  int blit, tag, red, other, other2, lidx, size, lits, count;
  const int * p, * w, * eow, * c, * l;
  int64_t litslim;
  HTS * hts;
  if (lgl->opts->elmfull.val) return 1;
  count = lgl->stats->elm.count;
  litslim = lglfactor (lgl, lgl->opts->elmlitslim.val, count);
  hts = lglhts (lgl, lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  lits = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (red || tag == LRGCS) continue;
    if (tag == BINCS) {
      other = blit >> RMSHFT;
      if (lgl2manyoccs4elm (lgl, other)) return 0;
      lits += 2;
    } else if (tag == TRNCS) {
      other = blit >> RMSHFT;
      if (lgl2manyoccs4elm (lgl, other)) return 0;
      other2 = *p;
      if (lgl2manyoccs4elm (lgl, other2)) return 0;
      lits += 3;
    } else {
      assert (tag == OCCS);
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      size = 0;
      for (l = c; (other = *l); l++) {
        if (lgl2manyoccs4elm (lgl, other)) return 0;
        if (++size > lglfactor (lgl, lgl->opts->elmclslim.val, count))
	  return 0;
      }
      lits += size;
    }
    if (lits > litslim) return 0;
  }
  return 1;
}

static int lglchkoccs4elm (LGL * lgl, int idx) {
  int res;
  if ((res = lglforcedve (lgl, idx)) > 0) return 1;
  if (res < 0) return 0;
  if (lgl2manyoccs4elm (lgl, idx)) return 0;
  if (lgl2manyoccs4elm (lgl, -idx)) return 0;
  if (!lglchkoccs4elmlit (lgl, idx)) return 0;
  if (!lglchkoccs4elmlit (lgl, -idx)) return 0;
  return 1;
}

static int lglispure (LGL * lgl, int lit) {
  if (!lgl->opts->pure.val) return 0;
  if (lglifrozen (lgl, lit)) return 0;
  return !lglocc (lgl, -lit);
}

static int lglpurelit (LGL * lgl, int lit) {
  int res;
  LOG(1, "pure literal %d", lit);
  assert (!lglocc (lgl, -lit));
  res = lglflushclauses (lgl, lit);
  assert (lgl->blocking || lgl->eliminating);
  if (lgl->blocking) {
    lgl->stats->blk.pure++;
    lgl->stats->blk.clauses += res;
    ADDSTEPS (blk.steps, res);
  }
  if (lgl->eliminating) {
    lgl->stats->elm.pure++;
    ADDSTEPS (elm.steps, res);
  }
  lglepusheliminated (lgl, lit);
  return res;
}

static void lglelimlit (LGL * lgl, int idx) {
  int forced;
  if (!lglisfree (lgl, idx)) return;
  if (lglispure (lgl, idx)) { (void) lglpurelit (lgl, idx); return; }
  if (lglispure (lgl, -idx)) { (void) lglpurelit (lgl, -idx); return; }
  if (!lglchkoccs4elm (lgl, idx)) return;
  LOG (2, "trying to eliminate %d", idx);
  if ((forced = lglforcedve (lgl, idx)) < 0) return;
  if (!forced && lgltrysmallve (lgl, idx)) return;
  lglinitecls (lgl, idx);
  lglelimlitaux (lgl, idx);
  if (lgl->elm->pivot) lglrstecls (lgl);
}

static int lglblockcls (LGL * lgl, int lit) {
  int blit, tag, red, other, other2, lidx, val, count, size;
  const int * p, * w, * eow, * c, *l;
  int bc = lgl->stats->blk.count;
  HTS * hts;
  INCSTEPS (blk.steps);
  hts = lglhts (lgl, lit);
  if (!hts->count) return 1;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  count = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    red = blit & REDCS;
    if (red) continue;
    count++;
    lgl->stats->blk.res++;
    INCSTEPS (blk.steps);
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      val = lglmarked (lgl, other);
      if (val < 0) continue;
      if (tag == TRNCS) {
	other2 = *p;
	val = lglmarked (lgl, other2);
	if (val < 0) continue;
      }
    } else {
      assert (tag == OCCS);
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      size = 0;
      for (l = c; (other = *l); l++) {
	val = lglmarked (lgl, other);
	if (++size > lglfactor (lgl, lgl->opts->blkclslim.val, bc)) return 0;
	if (val < 0) break;
      }
      if (other) continue;
    }
    return 0;
  }
  LOG (3, "resolved %d trivial resolvents on %d", count, lit);
  return 1;
}

static int lgl2manyoccs4blk (LGL * lgl, int lit) {
  return lglhts (lgl, lit)->count >
           lglfactor (lgl, lgl->opts->blkocclim.val, lgl->stats->blk.count);
}

static int lgldonotblocklit (LGL * lgl, int lit) {
  int pocc = lglocc (lgl, lit);
  int nocc = lglocc (lgl, -lit);
  int count = lgl->stats->blk.count;
  if (pocc >= lglfactor (lgl, lgl->opts->blkocclim1.val, count)) return 1;
  if (nocc >= lglfactor (lgl, lgl->opts->blkocclim1.val, count)) return 1;
  if (pocc < lglfactor (lgl, lgl->opts->blkocclim2.val, count)) return 0;
  if (nocc < lglfactor (lgl, lgl->opts->blkocclim2.val, count)) return 0;
  return 1;
}

static int lglblocklit (LGL * lgl, int lit, Stk * stk) {
  int blit, tag, red, blocked, other, other2, lidx, count, size;
  int bc = lgl->stats->blk.count;
  int * p, * w, * eow, * c, * l;
  HTS * hts;
  if (lglval (lgl, lit)) return 0;
  if (lgldonotblocklit (lgl, lit)) return 0;
  if (lgl2manyoccs4blk (lgl, lit)) return 0;
  hts = lglhts (lgl, lit);
  assert (!lgl->opts->pure.val || hts->count > 0);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  count = 0;
  assert (lglmtstk (stk+2) && lglmtstk (stk+3) && lglmtstk (stk+4));
  for (p = w; p < eow; p++) {
    if (INCSTEPS (blk.steps) >= lgl->limits->blk.steps) break;
    if (lglterminate (lgl)) break;
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    red = blit & REDCS;
    if (red) continue;
    assert (lglmtstk (&lgl->seen));
    blocked = 0;
    if (tag == BINCS || tag == TRNCS) {
      if (!lgl->opts->blksmall.val) continue;
      other = blit >> RMSHFT;
      if (lgl2manyoccs4blk (lgl, other)) continue;
      lglpushnmarkseen (lgl, other);
      if (tag == TRNCS) {
	other2 = *p;
        if (lgl2manyoccs4blk (lgl, other2)) goto CONTINUE;
	lglpushnmarkseen (lgl, other2);
      }
    } else {
      assert (tag == OCCS);
      if (!lgl->opts->blklarge.val) continue;
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      size = 0;
      for (l = c; (other = *l); l++) {
	if (other == lit) continue;
        if (lgl2manyoccs4blk (lgl, other)) goto CONTINUE;
	if (++size > lglfactor (lgl, lgl->opts->blkclslim.val, bc))
	  goto CONTINUE;
	lglpushnmarkseen (lgl, other);
      }
    }
    blocked = lglblockcls (lgl, -lit);
CONTINUE:
    lglpopnunmarkstk (lgl, &lgl->seen);
    if (!blocked) continue;
    if (tag == BINCS) {
      other = blit >> RMSHFT;
      lglpushstk (lgl, stk+2, other);
    } else if (tag == TRNCS) {
      other = blit >> RMSHFT;
      lglpushstk (lgl, stk+3, other);
      other2 = *p;
      lglpushstk (lgl, stk+3, other2);
    } else {
      assert (tag == OCCS);
      lidx = blit >> RMSHFT;
      lglpushstk (lgl, stk+4, lidx);
    }
  }
  while (!lglmtstk (stk+2)) {
    if (INCSTEPS (blk.steps) >= lgl->limits->blk.steps) break;
    count++;
    other = lglpopstk (stk+2);
    LOG (2, "blocked binary clause %d %d on %d", lit, other, lit);
    lglrmbcls (lgl, lit, other, 0);
    lglepush (lgl, lit);
    lglepush (lgl, other);
    lglepush (lgl, 0);
    if (!lglmvbcls (lgl, lit, other))
      lgldrupligdelclsarg (lgl, lit, other, 0);
  }
  while (!lglmtstk (stk+3)) {
    if (INCSTEPS (blk.steps) >= lgl->limits->blk.steps) break;
    count++;
    other2 = lglpopstk (stk+3);
    other = lglpopstk (stk+3);
    LOG (2, "blocked ternary clause %d %d %d on %d", lit, other, other2, lit);
    lglrmtcls (lgl, lit, other, other2, 0);
    lglepush (lgl, lit);
    lglepush (lgl, other);
    lglepush (lgl, other2);
    lglepush (lgl, 0);
    if (!lglmvtcls (lgl, lit, other, other2))
      lgldrupligdelclsarg (lgl, lit, other, other2, 0);
  }
  while (!lglmtstk (stk+4)) {
    if (INCSTEPS (blk.steps) >= lgl->limits->blk.steps) break;
    lidx = lglpopstk (stk+4);
    count++;
    c = lglidx2lits (lgl, 0, lidx);
    LOGCLS (2, c, "blocked on %d large clause", lit);
    lgldrupligdelclsaux (lgl, c);
    lglepush (lgl, lit);
    for (l = c; (other = *l); l++)
      if (other != lit) lglepush (lgl, other);
    lglepush (lgl, 0);
    lglrmlcls (lgl, lidx, 0);
  }
  LOG (2, "found %d blocked clauses with %d", count, lit);
  lgl->stats->blk.clauses += count;
  if (count > 0) lglblockinglit (lgl, lit);
  lglclnstk (stk+2), lglclnstk (stk+3), lglclnstk (stk+4);
  return count;
}

static void lglsetblklim (LGL * lgl) {
  int64_t limit, irrlim;
  int pen, szpen;
  if (lgl->opts->blkrtc.val) {
    lgl->limits->blk.steps = LLMAX;
    lglprt (lgl, 1,
      "[block-%d] really no limit (run to completion)",
      lgl->stats->blk.count);
  } else {
    limit = (lgl->opts->blkreleff.val*lglvisearch (lgl))/1000;
    if (limit < lgl->opts->blkmineff.val) limit = lgl->opts->blkmineff.val;
    if (lgl->opts->blkmaxeff.val >= 0 && limit > lgl->opts->blkmaxeff.val)
      limit = lgl->opts->blkmaxeff.val;
    if (lgl->stats->blk.count <= 1 &&
        lgl->opts->boost.val &&
	lglrem (lgl) < lgl->opts->blkboostvlim.val) {
      lglprt (lgl, 1,
        "[block-%d] boosting limit by %d",
	lgl->stats->blk.count, lgl->opts->blkboost.val);
      limit *= lgl->opts->blkboost.val;
    }
    limit >>= (pen = lgl->limits->blk.pen + (szpen = lglszpen (lgl)));
    irrlim = (lgl->stats->irr.clauses.cur/2) >> szpen;
    if (lgl->opts->irrlim.val && limit < irrlim) {
      limit = irrlim;
      lglprt (lgl, 1, 
  "[block-%d] limit of %lld steps based on %d irredundant clauses penalty %d",
	lgl->stats->blk.count,
	(LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
    } else
      lglprt (lgl, 1, 
	"[block-%d] limit of %lld steps penalty %d = %d + %d",
	lgl->stats->blk.count, (LGLL) limit,
	pen, lgl->limits->blk.pen, szpen);
    lgl->limits->blk.steps = lgl->stats->blk.steps + limit;
  }
}

static int lgleschedrem (LGL * lgl, int this_time) {
  int idx, res = 0, count;
  const char * str;
  AVar * av;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (lglifrozen (lgl, idx)) continue;
    if (!lglisfree (lgl, idx)) continue;
    av = lglavar (lgl, idx);
    if (lgl->eliminating && av->donotelm) continue;
    if (lgl->blocking && av->donotblk) continue;
    res++;
  }
  assert (lgl->eliminating || lgl->blocking);
  if (lgl->eliminating) count = lgl->stats->elm.count, str = "elim";
  else assert (lgl->blocking), count = lgl->stats->blk.count, str = "block";
  if (res)
    lglprt (lgl, 1,
      "[%s-%d] %d variables %.0f%% %s time",
      str, count,
      res, lglpcnt (res, lglrem (lgl)),
      this_time ? "will be scheduled this" : "remain to be tried next");
  else {
    lglprt (lgl, 1,
      "[%s-%d] no untried remaining variables left",
      str, count);
    for (idx = 2; idx < lgl->nvars; idx++) {
      av = lglavar (lgl, idx);
      if (lgl->eliminating) av->donotelm = 0;
      if (lgl->blocking) av->donotblk = 0;
    }
  }
  return res;
}

static void lglsetdonotesched (LGL * lgl, int completed) {
  AVar * av;
  EVar * ev;
  int idx;
  assert (lgl->eliminating + lgl->blocking == 1);
  for (idx = 2; idx < lgl->nvars; idx++) {
    av = lglavar (lgl, idx);
    ev = lglevar (lgl, idx);
    if (lgl->eliminating) {
      if (completed) av->donotelm = 0;
      else if (ev->pos < 0) av->donotelm = 1;
    }
    if (lgl->blocking) {
      if (completed) av->donotblk = 0;
      else if (ev->pos < 0) av->donotblk = 1;
    }
  }
}

static int lglblkdone (LGL * lgl) {
  if (!lglsmallirr (lgl)) return 1;
  if (lglterminate (lgl)) return 1;
  if (lglmtstk (&lgl->esched)) return 1;
  if (lgl->stats->blk.steps >= lgl->limits->blk.steps) return 1;
  return 0;
}

static void lglblock (LGL * lgl) {
  int oldrem = lgl->blkrem, oldall = lgl->blkall;
  int oldirr = lgl->stats->irr.clauses.cur;
  int idx, count, all, rem, success;
  Stk blocked[5];
  assert (lglsmallirr (lgl));
  assert (!lgl->simp);
  assert (!lgl->dense);
  assert (!lgl->eliminating);
  assert (!lgl->blocking);
  assert (!lgl->occs);
  lglstart (lgl, &lgl->times->block);
  if (lgl->level) lglbacktrack (lgl, 0);
  lgl->simp = lgl->blocking = lgl->occs = 1;
  lgl->stats->blk.count++;
  lglgc (lgl);
  assert (lgl->frozen);
  assert (!(oldall && !oldrem));
  all = !oldrem || !oldall;
  if (all)
    lglprt (lgl, 1,
      "[block-%d] scheduling all variables this time",
      lgl->stats->blk.count);
  else if (!lgleschedrem (lgl, 1)) all = 1, oldrem = 0;
  if (!all) assert (!lgl->donotsched), lgl->donotsched = 1;
  lgldense (lgl, 1);
  if (!all) assert (lgl->donotsched), lgl->donotsched = 0;
  lglsetblklim (lgl);
  CLR (blocked);
  count = 0;
  if (!lgl->opts->blkresched.val)
    assert (!lgl->donotsched), lgl->donotsched = 1;
  while (!lglblkdone (lgl)) {
    idx = lglpopesched (lgl);
    lglavar (lgl, idx)->donotblk = 1;
    if (!lglisfree (lgl, idx)) continue;
    if (lglispure (lgl, -idx)) count += lglpurelit (lgl, -idx);
    else if (lglispure (lgl, idx)) count += lglpurelit (lgl, idx);
    else {
      if (lglocc (lgl, -idx) > lglocc (lgl, idx)) idx = -idx;
      count += lglblocklit (lgl, idx, blocked);
      count += lglblocklit (lgl, -idx, blocked);
    }
  }
  if (!lgl->opts->blkresched.val)
    assert (lgl->donotsched), lgl->donotsched = 0;
  rem = lglcntstk (&lgl->esched);
  if (!rem) {
    lglprt (lgl, 1,
      "[block-%d] fully completed",
      lgl->stats->blk.count);
    lgl->blkrtc = 1;
  } else {
    lglprt (lgl, 1,
      "[block-%d] incomplete %d not tried %.0f%%",
      lgl->stats->blk.count, rem, lglpcnt (rem, lgl->nvars - 2));
  }
  lglsetdonotesched (lgl, !rem);
  lglrelstk (lgl, &lgl->esched);
  lglsparse (lgl);
  lglgc (lgl);
  lglrelstk (lgl, blocked+2);
  lglrelstk (lgl, blocked+3);
  lglrelstk (lgl, blocked+4);
  lgl->blkrem = rem > 0;
  lgl->blkall = all && lgl->blkrem;
  lglprt (lgl, 1,
    "[block-%d] transition to [ all %d rem %d ] state",
    lgl->stats->blk.count, lgl->blkall, lgl->blkrem);
  assert (lgl->simp && lgl->blocking && lgl->occs);
  lgl->blocking = lgl->simp = lgl->occs = 0;
  lgl->stats->irrprgss += count;
  lglprt (lgl, 1,
    "[block-%d] eliminated %d blocked clauses",
    lgl->stats->blk.count, count);
  if (!lgl->blkrtc &&
      lgl->stats->blk.count <= lgl->opts->blksuccessmaxwortc.val) {
    success = 1;
    lglprt (lgl, 1,
      "[block-%d] considered successful since not run to completion yet",
      lgl->stats->blk.count);
  } else if (count) {
    success = (oldirr/lgl->opts->blksuccessrat.val <= count);
    if (!success)
      lglprt (lgl, 1,
	"[block-%d] %d < 1/%d * %d = %d considered unsuccessful",
	lgl->stats->blk.count, count, lgl->opts->blksuccessrat.val,
	oldirr, oldirr/lgl->opts->blksuccessrat.val);
  } else success = 0;
  LGLUPDPEN (blk, success);
  lglrep (lgl, 2, 'k');
  lglstop (lgl);
  assert (!lgl->mt);
}

static void lglsetccelim (LGL * lgl) {
  int count = lgl->stats->cce.count - lgl->opts->cceboostdel.val;
  int64_t limit, irrlim;
  int pen, szpen;
  if (lgl->opts->ccertc.val > 1) {
    lgl->limits->cce.steps = LLMAX;
    lglprt (lgl, 1,
      "[cce-%d] really no limit (run to completion)",
      lgl->stats->cce.count);
  } else if (lgl->opts->ccertc.val ||
      (count > 0 &&
       lglrem (lgl) < lgl->opts->ccertcintvlim.val &&
       !(count % lgl->opts->ccertcint.val))) {
    limit = 4000000000ll;
    lgl->limits->cce.steps = lgl->stats->cce.steps + limit;
    lglprt (lgl, 1,
       "[cce-%d] almost no limit of %lld steps",
       lgl->stats->cce.count, (LGLL) limit);
  } else {
    limit = (lgl->opts->ccereleff.val*lglvisearch (lgl))/1000;
    if (limit < lgl->opts->ccemineff.val) limit = lgl->opts->ccemineff.val;
    if (lgl->opts->ccemaxeff.val >= 0 && limit > lgl->opts->ccemaxeff.val)
      limit = lgl->opts->ccemaxeff.val;
    if (count > 0 &&
        (count <= 1 || !(count % lgl->opts->cceboostint.val)) &&
        lgl->opts->boost.val &&
	lgl->nvars < lgl->opts->cceboostvlim.val) {
      lglprt (lgl, 1,
        "[cce-%d] boosting limit by %d",
	lgl->stats->cce.count, lgl->opts->cceboost.val);
      limit *= lgl->opts->cceboost.val;
    }
    limit >>= (pen = lgl->limits->cce.pen + (szpen = lglszpen (lgl)));
    irrlim = (lgl->stats->irr.clauses.cur) >> szpen;
    if (lgl->opts->irrlim.val && limit < irrlim) {
      limit = irrlim;
      lglprt (lgl, 1,
  "[cce-%d] limit of %lld steps based on %d irredundant clauses penalty %d",
	lgl->stats->cce.count,
	(LGLL) limit, lgl->stats->irr.clauses.cur, szpen );
    } else
      lglprt (lgl, 1,
	"[cce-%d] limit of %lld steps penalty %d = %d + %d",
	lgl->stats->cce.count, (LGLL) limit,
	pen, lgl->limits->cce.pen, szpen);
    lgl->limits->cce.steps = lgl->stats->cce.steps + limit;
  }
}

#define CCELOGLEVEL 2

static void lglsignedmark2 (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int bit = 1 << (2 + (lit < 0));
  if (av->mark & bit) return;
  av->mark |= bit;
}

static void lglsignedunmark2 (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int bit = 1 << (2 + (lit < 0));
  if (!(av->mark & bit)) return;
  av->mark &= ~bit;
}

static int lglsignedmarked2 (LGL * lgl, int lit) {
  AVar * av = lglavar (lgl, lit);
  int bit = 1 << (2 + (lit < 0));
  return av->mark & bit;
}

static int lglabcecls (LGL * lgl, int lit, const int * c) {
  int other, found = 0;
  const int * p;
  for (p = c; (other = *p); p++)
    if (other == -lit) found++;
    else if (lglsignedmarked (lgl, -other)) return 1;
  assert (found == 1);
  return 0;
}

static int lglabce (LGL * lgl, int lit) {
  const int * p, * w, * eow, * c;
  int blit, tag, other, cls[4];
  HTS * hts;
  assert (!lglifrozen (lgl, lit));
  hts = lglhts (lgl, -lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  cls[0] = -lit, cls[3] = 0;
  for (p = w; p < eow; p++) {
    if (lgl->limits->cce.steps <= INCSTEPS (cce.steps)) return 0;
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (blit & REDCS) continue;
    if (tag == LRGCS) continue;
    other = blit >> RMSHFT;
    cls[1] = other;
    if (tag == BINCS) cls[2] = 0, c = cls;
    else if (tag == TRNCS) cls[2] = *p, c = cls;
    else assert (tag == OCCS), c = lglidx2lits (lgl, 0, other);
    if (!lglabcecls (lgl, lit, c)) return 0;
  }
  return 1;
}

static int lglcceclause (LGL * lgl,
                         const int * c, 
			 int igntag,
			 int cce) {
  int other, res, nextala, nextcla, lit, blit, tag, other2, i, j, n;
  int ala, first, old, prev, steps, lidx;
  int * newtop, * d, * q, * r;
  const int * p, * eow, * w;
  long delta;
  HTS * hts;
  LOGCLS (CCELOGLEVEL, c, "trying CCE on clause");
  assert (lglmtstk (&lgl->cce->extend));
  assert (lglmtstk (&lgl->cce->cla));
  assert (lglmtstk (&lgl->seen));
  for (p = c; (other = *p); p++) {
    assert (!lglmarked (lgl, other));
    lglpushstk (lgl, &lgl->seen, other);
    lglpushstk (lgl, &lgl->cce->cla, other);
    lglsignedmark (lgl, other);
  }
  n = lglcntstk (&lgl->seen);
  for (i = n-1; i > 0; i--) {
    j = lglrand (lgl) % (i + 1);
    if (j == i) continue;
    SWAP (int, lgl->seen.start[i], lgl->seen.start[j]);
    SWAP (int, lgl->cce->cla.start[i], lgl->cce->cla.start[j]);
  }
  nextcla = nextala = res = 0;
ALA:
  while (!res && nextala < lglcntstk (&lgl->seen)) {
    lit = lglpeek (&lgl->seen, nextala++);
    assert (lglsignedmarked (lgl, lit));
    assert (!lglsignedmarked (lgl, -lit));
    hts = lglhts (lgl, lit);
    w = newtop = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    steps = 0;
    for (p = w; !res && p < eow; p++) {
      steps++;
      blit = *p;
      *newtop++ = blit;
      tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) *newtop++ = *++p;
      if (tag == OCCS) continue;
      if (blit & REDCS) continue;
      other = blit >> RMSHFT;
      if (lglsignedmarked (lgl, -other)) continue;
      if (tag == BINCS) {
	if (lglsignedmarked (lgl, other)) {
	  if (igntag == BINCS) {
	    if (c[0] == lit && c[1] == other) continue;
	    if (c[1] == lit && c[0] == other) continue;
	  }
	  LOG (CCELOGLEVEL, 
	       "ALA on binary clause %d %d results in ATE", lit, other);
	  res = 1;
	} else {
	  assert (!lglmarked (lgl, other));
	  LOG (CCELOGLEVEL, "ALA %d through binary clause %d %d", 
	       -other, lit, other);
	  lglsignedmark (lgl, -other);
	  lglpushstk (lgl, &lgl->seen, -other);
	}
      } else if (tag == TRNCS) {
	other2 = *p;
	if (lglsignedmarked (lgl, -other2)) continue;
	if (lglsignedmarked (lgl, other)) {
	  if (lglsignedmarked (lgl, other2)) {
	    if (igntag == TRNCS) {
	      if (c[0] == lit && c[1] == other && c[2] == other2) continue;
	      if (c[0] == lit && c[2] == other && c[1] == other2) continue;
	      if (c[1] == lit && c[0] == other && c[2] == other2) continue;
	      if (c[1] == lit && c[2] == other && c[0] == other2) continue;
	      if (c[2] == lit && c[0] == other && c[1] == other2) continue;
	      if (c[2] == lit && c[1] == other && c[0] == other2) continue;
	    }
	    LOG (CCELOGLEVEL,
	      "ALA on ternary clause %d %d %d results in ATE",
	      lit, other, other2);
	    res = 1;
	  } else {
	    assert (!lglmarked (lgl, other2));
	    LOG (CCELOGLEVEL, 
	         "ALA %d through ternary clause %d %d %d (1st case)",
		 -other2, lit, other, other2);
	    lglsignedmark (lgl, -other2);
	    lglpushstk (lgl, &lgl->seen, -other2);
	  }
	} else if (lglsignedmarked (lgl, other2)) {
	  assert (!lglmarked (lgl, other));
	  LOG (CCELOGLEVEL, 
	      "ALA %d through ternary clause %d %d %d (2nd case)",
	      -other, lit, other, other2);
	  lglsignedmark (lgl, -other);
	  lglpushstk (lgl, &lgl->seen, -other);
	}
      } else {
	assert (tag == LRGCS);
	d = lglidx2lits (lgl, 0, (lidx = *p));
	if (d == c) continue;
	if (d[0] == lit) SWAP (int, d[0], d[1]);
	assert (d[1] == lit);
	if (lglsignedmarked (lgl, -d[0])) continue;
	for (q = d + 2; (other = *q); q++) {
	  if (lglsignedmarked (lgl, -other)) break;
	  if (!lglsignedmarked (lgl, other)) break;
	}
	if (other) {
	  newtop -= 2, assert (w <= newtop);
	  SWAP (int, d[1], *q);
	  assert (d[1] == other);
          delta = lglwchlrg (lgl, d[1], d[0], 0, lidx);
	  if (delta) w += delta, p += delta, newtop += delta, eow += delta;
	} else if (lglsignedmarked (lgl, d[0])) {
	  LOGCLS (CCELOGLEVEL, d, "ATE after ALA on large clause");
	  res = 1;
	} else {
	  ala = -d[0];
	  assert (!lglmarked (lgl, ala));
	  LOGCLS (CCELOGLEVEL, d, "ALA %d through large clause", ala);
	  lglsignedmark (lgl, ala);
	  lglpushstk (lgl, &lgl->seen, ala);
	}
      }
    }
    assert (newtop <= eow);
    while (p < eow) *newtop++ = *p++;
    lglshrinkhts (lgl, hts, newtop - w);
    if (lgl->limits->cce.steps <= ADDSTEPS (cce.steps, steps)) goto DONE;
  }
  if (res || !lgl->opts->block.val || cce < 3) goto SKIPCLA;
  while (!res && nextcla < lglcntstk (&lgl->cce->cla)) {
    lit = lglpeek (&lgl->cce->cla, nextcla++);
    if (lglifrozen (lgl, lit)) continue;
    assert (lglsignedmarked (lgl, lit));
    assert (!lglsignedmarked (lgl, -lit));
    hts = lglhts (lgl, -lit);
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    old = lglcntstk (&lgl->cce->cla);
    first = 1;
    for (p = w; p < eow; p++) {
      if (lgl->limits->cce.steps <= INCSTEPS (cce.steps)) goto DONE;
      blit = *p;
      tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) p++;
      if (tag == LRGCS) continue;
      if (blit & REDCS) continue;
      other = blit >> RMSHFT;
      if (first) {
	if (tag == BINCS) {
	  if (lglsignedmarked (lgl, -other)) continue;
	  if (!lglsignedmarked (lgl, other))
	    lglpushstk (lgl, &lgl->cce->cla, other);
	} else if (tag == TRNCS) {
	  if (lglsignedmarked (lgl, -other)) continue;
	  if (lglsignedmarked (lgl, -(other2 = *p))) continue;
	  if (!lglsignedmarked (lgl, other))
	    lglpushstk (lgl, &lgl->cce->cla, other);
	  if (!lglsignedmarked (lgl, other2))
	    lglpushstk (lgl, &lgl->cce->cla, other2);
	} else { 
	  assert (tag == OCCS);
	  d = lglidx2lits (lgl, 0, other);
	  assert (d != c);
	  for (q = d; (other = *q); q++) {
	    if (other == -lit) continue;
	    if (lglsignedmarked (lgl, -other)) break;
	  }
	  if (other) continue;
	  for (q = d; (other = *q); q++)
	    if (other != -lit && !lglsignedmarked (lgl, other))
	      lglpushstk (lgl, &lgl->cce->cla, other);
	}
	first = 0;
      } else {
	r = lgl->cce->cla.start + old;
	if (tag == BINCS) {
	  if (lglsignedmarked (lgl, -other)) continue;
	  for (q = r; q < lgl->cce->cla.top; q++)
	    if (*q == other) *r++ = *q;
	} else if (tag == TRNCS) {
	  if (lglsignedmarked (lgl, -other)) continue;
	  if (lglsignedmarked (lgl, -(other2 = *p))) continue;
	  for (q = r; q < lgl->cce->cla.top; q++)
	    if (*q == other || *q == other2) *r++ = *q;
	} else {
	  assert (tag == OCCS);
	  d = lglidx2lits (lgl, 0, other);
	  assert (d != c);
	  for (q = d; (other = *q); q++) {
	    if (other == -lit) continue;
	    if (lglsignedmarked (lgl, -other)) break;
	  }
	  if (other) continue;
	  for (q = d; (other = *q); q++) {
	    if (other == -lit) continue;
	    assert (other != lit);
	    assert (!lglsignedmarked2 (lgl, other));
	    assert (!lglsignedmarked2 (lgl, -other));
	    lglsignedmark2 (lgl, other);
	  }
	  for (q = r; q < lgl->cce->cla.top; q++)
	    if (lglsignedmarked2 (lgl, (other = *q)))
	      *r++ = other;
	  for (q = d; (other = *q); q++) {
	    if (other == -lit) continue;
	    assert (other != lit);
	    assert (lglsignedmarked2 (lgl, other));
	    lglsignedunmark2 (lgl, other);
	  }
	}
	if ((lgl->cce->cla.top = r) == lgl->cce->cla.start + old) break;
      }
    } 
    if (lglcntstk (&lgl->cce->cla) > old) {
      nextcla = 0;
      lglpushstk (lgl, &lgl->cce->extend, lit);
      for (q = lgl->cce->cla.start; q < lgl->cce->cla.start + old; q++)
	if (*q != lit) lglpushstk (lgl, &lgl->cce->extend, *q);
      lglpushstk (lgl, &lgl->cce->extend, 0);
    }
    for (q = lgl->cce->cla.start + old; !res && q < lgl->cce->cla.top; q++) {
      if (lglsignedmarked (lgl, -*q)) {
	LOG (CCELOGLEVEL, "CLA on %d results in ATE", *q);
	res = 1;
      } else {
	LOG (CCELOGLEVEL, "CLA %d on %d", *q, lit);
	lglpushstk (lgl, &lgl->seen, *q);
	lglsignedmark (lgl, *q);
      }
    }
    if (!res && p == eow && nextala < lglcntstk (&lgl->seen)) goto ALA;
  }
SKIPCLA:
  if (res) {
    LOGCLS (CCELOGLEVEL, c, "ATE clause");
    lgl->stats->cce.ate++;
  } else if (lgl->opts->block.val && cce >= 2) {
   for (p = lgl->cce->cla.start; p < lgl->cce->cla.top; p++)
     if (!lglifrozen (lgl, (other = *p)) && (res = lglabce (lgl, other))) 
       break;
    if (res) {
      LOGCLS (CCELOGLEVEL, c, "ABCE on %d clause", other);
      lglpushstk (lgl, &lgl->cce->extend, other);
      for (p = lgl->cce->cla.start; p < lgl->cce->cla.top; p++)
        if (*p != other) lglpushstk (lgl, &lgl->cce->extend, *p);
      lglpushstk (lgl, &lgl->cce->extend, 0);
      lgl->stats->cce.abce++;
    }
  }
  if (res) lgl->stats->cce.eliminated++;
DONE:
  lglpopnunmarkstk (lgl, &lgl->seen);
  lglclnstk (&lgl->cce->cla);
  if (res && !lglmtstk (&lgl->cce->extend)) {
    assert (cce >= 2);
    assert (lgl->opts->block.val);
    prev = 0;
    for (p = lgl->cce->extend.start; p < lgl->cce->extend.top; p++) {
      lit = *p;
      lglepush (lgl, lit);
      if (!prev) assert (!lglifrozen (lgl, lit)), lglblockinglit (lgl, lit);
      prev = lit;
    }
  }
  lglclnstk (&lgl->cce->extend);
  return res;
}

static const char * lglcce2str (int cce) {
  assert (0 <= cce), assert (cce <= 3);
  if (cce == 3) return "ACCE";
  else if (cce == 2) return "ABCE";
  else if (cce == 1) return "ATE";
  else return "none";
}

static int lglccesmallclauses (LGL * lgl, int lit) {
  int idx = abs (lit), blit, tag, red, other, other2;
  HTS * hts = lglhts (lgl, lit);
  const int * p, * w, * eow;
  CCE * cce = lgl->cce;
  Stk * clauses;
  assert (cce);
  if (!lglisfree (lgl, lit)) return 1;
  clauses = &cce->clauses;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  INCSTEPS (cce.steps);
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == OCCS) continue;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    red = blit & REDCS;
    if (red) continue;
    other = blit >> RMSHFT;
    if (abs (other) < idx) continue;
    if (!lglisfree (lgl, other)) continue;
    if (tag == TRNCS) {
      other2 = *p;
      if (abs (other2) < idx) continue;
      if (abs (other2) < abs (other)) continue;
      if (!lglisfree (lgl, other2)) continue;
      lglpushstk (lgl, clauses, other2);
      cce->trn++;
    } else {
      assert (tag == BINCS);
      cce->bin++;
    }
    lglpushstk (lgl, clauses, other);
    lglpushstk (lgl, clauses, lit);
    lglpushstk (lgl, clauses, 0);
  }
  return 1;
}

static void lglccesmall (LGL * lgl, int cce, int round) {
  int count, valid, invalid, tried, eliminated, elim2, elim3;
  int size, lit, tag;
  const int * p, * c;
  Stk * clauses;
  assert (lgl->cce);
  clauses = &lgl->cce->clauses;
  assert (!lgl->cce->clauses.start);
  lglrandlitrav (lgl, lglccesmallclauses);
  lglfitstk (lgl, &lgl->cce->clauses);
  count = lgl->cce->bin + lgl->cce->trn;
  lglprt (lgl, 1,
    "[cce-%d-%d] scheduling %d clauses = %d binary + %d ternary",
    lgl->stats->cce.count, round, count, lgl->cce->bin, lgl->cce->trn);
  tried = eliminated = invalid = elim2 = elim3 = 0;
  for (c = clauses->start; c < clauses->top; c = p + 1) {
    if (lgl->mt) break;
    if (lglterminate (lgl)) break;
    if (lgl->limits->cce.steps <= lgl->stats->cce.steps) break;
    valid = 1;
    for (p = c; (lit = *p); p++)
      if (!lglisfree (lgl, lit))
	valid = 0;
    if (valid) {
      tried++;
      size = p - c;
      assert (2 <= size), assert (size <= 3);
      tag = size == 2 ? BINCS : TRNCS;
      if (!lglcceclause (lgl, c, tag, cce)) continue;
      eliminated++;
      if (size == 2) {
        if (!lglrmvbcls (lgl, c[0], c[1]))
	  lgldrupligdelclsarg (lgl, c[0], c[1], 0);
	elim2++;
      } else {
	assert (size == 3);
        if (!lglrmvtcls (lgl, c[0], c[1], c[2]))
	  lgldrupligdelclsarg (lgl, c[0], c[1], c[2], 0);
	elim3++;
      }
    } else invalid++;
  }
  assert (count >= tried + invalid);
  lglrelstk (lgl, &lgl->cce->clauses);
  if (tried)
    lglprt (lgl, 1,
      "[cce-%d-%d] tried to eliminate %d small clauses %.0f%%",
      lgl->stats->cce.count, round, tried, lglpcnt (tried, count));
  if (elim2)
    lglprt (lgl, 1,
      "[cce-%d-%d] eliminated %d binary clauses %.0f%%",
      lgl->stats->cce.count, round, elim2, lglpcnt (elim2, lgl->cce->bin));
  if (elim3)
    lglprt (lgl, 1,
      "[cce-%d-%d] eliminated %d ternary clauses %.0f%%",
      lgl->stats->cce.count, round, elim3, lglpcnt (elim3, lgl->cce->trn));
  if (eliminated)
    lglprt (lgl, 1,
      "[cce-%d-%d] eliminated %d small clauses %.0f%%",
      lgl->stats->cce.count, round, eliminated, lglpcnt (eliminated, count));
}

static int lglcce (LGL * lgl) {
  int oldvars = lgl->nvars, cce, lenlim, startirr, success;
  int oldirr, eliminated, total, idx, round;
  int completedsmall, completedlarge;
  int64_t oldsteps, deltasteps;
  int elmlarge, elmsmall;
  lglstart (lgl, &lgl->times->cce);
  lgl->stats->cce.count++;
  lglsetccelim (lgl);
  round = total = 0;
  startirr = lgl->stats->irr.clauses.cur;
RESTART:
  round++;
  lenlim = INT_MAX;
  cce = lgl->opts->cce.val;
  if (cce == 3 && lgl->ccertc < 2 &&
      lgl->opts->cce3wait.val >= lgl->stats->cce.count) {
    lglprt (lgl, 2,
      "[cce-%d-%d] restricted to ABCE since ccertc=%s",
      lgl->stats->cce.count, round, lglcce2str (lgl->ccertc));
    cce = 2;
  }
  if (cce == 2 && lgl->ccertc < 1 &&
      lgl->opts->cce2wait.val >= lgl->stats->cce.count) {
    lglprt (lgl, 2,
      "[cce-%d-%d] restricted to ATE since ccertc=%s",
      lgl->stats->cce.count, round, lglcce2str (lgl->ccertc));
   cce = 1;
  }
  if (cce > 1 && !(lgl->stats->cce.count % lgl->opts->cceateint.val)) {
    lglprt (lgl, 2,
      "[cce-%d-%d] restricted to ATE due to ATE interval %d",
      lgl->stats->cce.count, round, lgl->opts->cceateint.val);
    cce = 1;
  }
  oldirr = lgl->stats->irr.clauses.cur;
  lglprt (lgl, 2, "[cce-%d-%d] starting round %d (%s)",
          lgl->stats->cce.count, round, round, lglcce2str (cce));
  assert (!lgl->simp && !lgl->cceing && !lgl->occs);
  lgl->cceing = lgl->simp = 1;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  NEW (lgl->cce, 1);
  NEW (lgl->cce->rem, oldvars);
  for (idx = 2; idx < oldvars; idx++) lgl->cce->rem[idx] = INT_MAX;
  lglgc (lgl);
  assert (lgl->frozen);
  lgldense (lgl, 1);
  oldsteps = lgl->stats->cce.steps;
  elmlarge = 0;
  while (!lgl->mt && 
         lenlim > 4 &&
	 !lglterminate (lgl) &&
	 lgl->limits->cce.steps > lgl->stats->cce.steps) {
    int maxlen = 0, count;
    const int * p, * c;
    Stk lidcs;
    CLR (lidcs);
    for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
      int len, lidx;
      if (*(p = c) >= NOTALIT) continue;
      while (*p) p++;
      len = p - c;
      if (len >= lenlim) continue;
      if (len < maxlen) continue;
      if (len > maxlen) {
	lglclnstk (&lidcs);
	maxlen = len;
      }
      lidx = c - lgl->irr.start;
      lglpushstk (lgl, &lidcs, lidx);
    }
    ADDSTEPS (cce.steps, lglcntstk (&lgl->irr)/128);
    count = lglcntstk (&lidcs);
    lglprt (lgl, 2,
      "[cce-%d-%d] scheduling %d clauses of length %d",
      lgl->stats->cce.count, round, count, maxlen);
    eliminated = 0;
    for (p = lidcs.start;
         p < lidcs.top &&
	 !lgl->mt &&
	 !lglterminate (lgl) &&
	 lgl->limits->cce.steps > lgl->stats->cce.steps; 
	 p++) {
      int lidx = *p;
      c = lgl->irr.start + lidx;
      if (*c >= NOTALIT) continue;
      if (!lglcceclause (lgl, c, OCCS, cce)) continue;
      lgldrupligdelclsaux (lgl, c);
      lglrmlcls (lgl, lidx, 0);
      eliminated++;
    }
    elmlarge += eliminated;
    lglrelstk (lgl, &lidcs);
    lenlim = maxlen;
    lglprt (lgl, 1 + !eliminated,
      "[cce-%d-%d] eliminated %d clauses out of %d (%.0f%%) of length %d",
      lgl->stats->cce.count, round,
      eliminated, count, lglpcnt (eliminated, count), maxlen);
  }
  completedlarge = (lgl->limits->cce.steps > lgl->stats->cce.steps);
  if (completedlarge)
    lglprt (lgl, 1,
      "[cce-%d-%d] completed large round (%s)",
      lgl->stats->cce.count, round, lglcce2str (cce));
  else
    lglprt (lgl, 1, 
      "[cce-%d-%d] incomplete large round (%s)",
      lgl->stats->cce.count, round, lglcce2str (cce));
  deltasteps = lgl->stats->cce.steps - oldsteps;
  lglprt (lgl, 1 + !elmlarge,
    "[cce-%d-%d] eliminated %d large clauses in %lld steps",
    lgl->stats->cce.count, round, elmlarge, (LGLL) deltasteps);
  deltasteps /= 2;
  if (LLMAX - deltasteps > lgl->limits->cce.steps) {
    lgl->limits->cce.steps += deltasteps;
    lglprt (lgl, 1,
      "[cce-%d-%d] allowing another %lld steps for small clauses",
      lgl->stats->cce.count, round, deltasteps);
  } else {
    lgl->limits->cce.steps = LLMAX;
    lglprt (lgl, 1,
      "[cce-%d-%d] unlimited number of steps for small clauses",
      lgl->stats->cce.count, round);
  }
  lglccesmall (lgl, cce, round);
  elmsmall = oldirr - lgl->stats->irr.clauses.cur - elmlarge;
  lglprt (lgl, 1 + !elmsmall,
    "[cce-%d-%d] eliminated %d small clauses in %lld steps",
    lgl->stats->cce.count, round, elmsmall,
    (LGLL) lgl->stats->cce.steps - oldsteps - deltasteps);
  completedsmall = (lgl->limits->cce.steps > lgl->stats->cce.steps);
  COVER (!completedsmall && lgl->opts->ccertc.val > 1);
  if (completedsmall)
    lglprt (lgl, 1,
      "[cce-%d-%d] completed small round (%s)",
      lgl->stats->cce.count, round, lglcce2str (cce));
  else
    lglprt (lgl, 1, 
      "[cce-%d-%d] incomplete small round (%s)",
      lgl->stats->cce.count, round, lglcce2str (cce));
  if (completedsmall && completedlarge) {
    if (lgl->ccertc < cce) {
      lgl->ccertc = cce;
      lglprt (lgl, 1, 
	"[cce-%d-%d] completed small and large (%s)",
	lgl->stats->cce.count, round, lglcce2str (cce));
    }
  }
  lglsparse (lgl);
  lglgc (lgl);
  lglrelstk (lgl, &lgl->cce->extend);
  lglrelstk (lgl, &lgl->cce->cla);
  DEL (lgl->cce->rem, oldvars);
  DEL (lgl->cce, 1);
  assert (oldirr >= lgl->stats->irr.clauses.cur);
  eliminated = oldirr - lgl->stats->irr.clauses.cur;
  total += eliminated;
  lglprt (lgl, 1,
    "[cce-%d-%d] eliminated %d covered clauses in round %d",
    lgl->stats->cce.count, round, eliminated, round);
  assert (lgl->simp && lgl->cceing);
  lgl->cceing = lgl->simp = 0;
  if (!lgl->mt &&
      eliminated &&
      !lglterminate (lgl) &&
      round < lgl->opts->ccemaxround.val &&
      lgl->limits->cce.steps > lgl->stats->cce.steps) goto RESTART;
  lglprt (lgl, 1,
    "[cce-%d] eliminated %d covered clauses in TOTAL during %d rounds",
    lgl->stats->cce.count, total, round);
  if (total) {
    success = (startirr/lgl->opts->ccesuccessrat.val <= total);
    if (!success)
      lglprt (lgl, 1,
	"[cce-%d] %d < 1/%d * %d = %d considered unsuccessful",
	lgl->stats->cce.count, total, lgl->opts->ccesuccessrat.val,
	startirr, startirr/lgl->opts->ccesuccessrat.val);
  } else success = 0;
  LGLUPDPEN (cce, success);
  lglrep (lgl, 2, 'E');
  lglstop (lgl);
  lglbasicatestats (lgl);
  return !lgl->mt;
}

static void lglsetelmlim (LGL * lgl, int * reschedptr) {
  int count = lgl->stats->elm.count - lgl->opts->elmboostdel.val;
  int pen, szpen, resched = 0;
  int64_t limit, irrlim;
  if (lgl->opts->elmrtc.val > 1) {
    lgl->limits->elm.steps = LLMAX;
    lglprt (lgl, 1,
      "[elim-%d] really no limit (run to completion)",
      lgl->stats->elm.count);
    resched = (lgl->opts->elmresched.val & 4);
  } else if (lgl->opts->elmrtc.val ||
             (count > 0 &&
	      lglrem (lgl) < lgl->opts->elmrtcintvlim.val &&
             !(count % lgl->opts->elmrtcint.val))) {
    limit = 100000000000ll;
    lgl->limits->elm.steps = lgl->stats->elm.steps + limit;
    lglprt (lgl, 1,
      "[elim-%d] almost no limit of %lld steps",
      lgl->stats->elm.count, (LGLL) limit);
    resched = (lgl->opts->elmresched.val & 4);
  } else {
    limit = (lgl->opts->elmreleff.val*lglvisearch (lgl))/1000;
    if (limit < lgl->opts->elmineff.val) limit = lgl->opts->elmineff.val;
    if (lgl->opts->elmaxeff.val >= 0 && limit > lgl->opts->elmaxeff.val)
      limit = lgl->opts->elmaxeff.val;
    if (count > 0 &&
        (count == 1 ||
        !(count % lgl->opts->elmboostint.val)) &&
	lglrem (lgl) < lgl->opts->elmboostvlim.val &&
        lgl->opts->boost.val &&
        lgl->opts->elmboost.val > 1) {
      lglprt (lgl, 1,
        "[elim-%d] boosting limit by %d",
	lgl->stats->elm.count, lgl->opts->elmboost.val);
      limit *= lgl->opts->elmboost.val;
      resched = (lgl->opts->elmresched.val & 2);
    } else resched = (lgl->opts->elmresched.val & 1);
    limit >>= (pen = lgl->limits->elm.pen + (szpen = lglszpen (lgl)));
    irrlim = (lgl->stats->irr.clauses.cur) >> szpen;
    if (lgl->opts->irrlim.val && limit < irrlim) {
      limit = irrlim;
      lglprt (lgl, 1,
  "[elim-%d] limit of %lld steps based on %d irredundant clauses penalty %d",
	lgl->stats->elm.count,
	(LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
    } else
      lglprt (lgl, 1,
        "[elim-%d] limit of %lld steps penalty %d = %d + %d",
	lgl->stats->elm.count, (LGLL) limit,
	pen, lgl->limits->elm.pen, szpen);
    lgl->limits->elm.steps = lgl->stats->elm.steps + limit;
  }
  lglprt (lgl, 1,					// TODO 2?
    "[elim-%d] rescheduling of touched variables %s",
    lgl->stats->elm.count, resched ? "enabled" : "disabled");
  *reschedptr = resched;
}

static int lglforceschedall (LGL * lgl) {
  const int oldonotsched = lgl->donotsched;
  int idx, res = 0;
  AVar * av;
  assert (lgl->eliminating);
  assert (lglmtstk (&lgl->esched));
  assert (lgl->touching), lgl->touching = 0;
  lgl->donotsched = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (lglifrozen (lgl, idx)) continue;
    if (!lglisfree (lgl, idx)) continue;
    av = lglavar (lgl, idx);
    av->donotelm = 0;
    lglesched (lgl, idx);
    res++;
  }
  assert (!lgl->touching), lgl->touching = 1;
  assert (!lgl->donotsched);
  if (oldonotsched) lgl->donotsched = 1;
  lglprt (lgl, 1,
    "[elim-%d-%d] fully rescheduled %d variables %.0f%%",
    lgl->stats->elm.count, lgl->elm->round,
    res, lglpcnt (res, lgl->nvars - 2));
  return res;
}

static void lgladdstrbincls (LGL * lgl, int a, int b) {
  assert (lglisfree (lgl, a));
  assert (lglisfree (lgl, b));
  assert (lglmtstk (&lgl->clause));
  lglpushstk (lgl, &lgl->clause, a);
  lglpushstk (lgl, &lgl->clause, b);
  lglpushstk (lgl, &lgl->clause, 0);
  LOG (BWL, "strengthened binary clause", a, b);
  lgldrupligaddcls (lgl, REDCS);
  lgladdcls (lgl, 0, 0, 1);
  lglclnstk (&lgl->clause);
}

static int lglbackwardlit (LGL * lgl,
			   const int * clause, const int * skip,
			   int size, int minlit,
			   int *subptr, int *strptr) {
  int res, blit, tag, red, other, other2, lidx, count, remove, hit;
  const int druplig = lgl->opts->druplig.val;
  const int * p, * w, * eow, * c, * l;
  int marked, marked2, val;
  Stk saved;
  HTS * hts;
  CLR (saved);
  assert (!lgl->level);
  lgl->stats->bkwd.tried.lits++;
  LOGCLS (BWL, clause,
    "backward subsume and strengthen clauses with %d by size %d clause",
    minlit, size);
  hit = res = 0;
  hts = lglhts (lgl, minlit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; !res && p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    if (p == skip) continue;
    red = blit & REDCS;
    if (red) continue;
    lgl->stats->bkwd.tried.occs++;
    INCSTEPS (elm.steps);
    if (tag == BINCS) {
      if (size > 2) continue;
      other = blit >> RMSHFT;
      if (!lglisfree (lgl, other)) continue;
      marked = lglmarked (lgl, other);
      if (marked > 0) {
	if (size == 2 && !hit++) continue;
	LOG (BWL, "subsumed binary clause %d %d", minlit, other);
	assert (!(w <= skip && skip < eow) || skip < p);
	ADDSTEPS (elm.steps, 2);
        if (druplig) lgldrupligdelclsarg (lgl, minlit, other, 0);
	lglrmbcls (lgl, minlit, other, 0);
	lgl->stats->bkwd.sub2++;
	*subptr += 1;
	res = 1;
      } else if (marked < 0) {
	LOG (BWL,
	  "removing %d and thus strengthening binary clause %d %d",
	  other, minlit, other);
	assert (p != skip);
	ADDSTEPS (elm.steps, 2);
	lglunit (lgl, minlit);
	lgl->stats->bkwd.str2++;
	*strptr += 1;
	res = 1;
      }
    } else if (tag == TRNCS) {
      if (size > 3) continue;
      other = blit >> RMSHFT;
      other2 = *p;
      if (!lglisfree (lgl, other)) continue;
      if (!lglisfree (lgl, other2)) continue;
      marked = lglmarked (lgl, other);
      marked2 = lglmarked (lgl, other2);
      if ((size == 2 && (marked > 0 || marked2 > 0)) ||
          (size == 3 && marked > 0 && marked2 > 0)) {
	if (size == 3 && !hit++) continue;
	assert (!(w <= skip && skip < eow) || skip < p);
	LOG (BWL,
	  "subsumed ternary clause %d %d %d",
	  minlit, other, other2);
	ADDSTEPS (elm.steps, 3);
        if (druplig) lgldrupligdelclsarg (lgl, minlit, other, other2, 0);
	lglrmtcls (lgl, minlit, other, other2, 0);
	lgl->stats->bkwd.sub3++;
	*subptr += 1;
	res = 1;
      } else {
	if (marked < 0 && marked2 > 0) {
	  int tmp = other; other = other2; other2 = tmp;
	} else if (marked <= 0 || marked2 >= 0) continue;
	LOG (BWL,
	  "removing %d and thus strengthening ternary clause %d %d %d",
	  other2, minlit, other, other2);
	assert (lglmarked (lgl, other) > 0);
	assert (lglmarked (lgl, other2) < 0);
	lgladdstrbincls (lgl, minlit, other);
        if (druplig) lgldrupligdelclsarg (lgl, minlit, other, other2, 0);
	lglrmtcls (lgl, minlit, other, other2, 0);
	if (size == 3) {
	  LOG (BWL,
	    "removing %d and thus strengthening ternary clause %d %d %d",
	    other2, minlit, other, -other2);
          if (druplig) lgldrupligdelclsarg (lgl, minlit, other, -other2, 0);
	  lglrmtcls (lgl, minlit, other, -other2, 0);
	  lgl->stats->bkwd.str3self++;
	}
	ADDSTEPS (elm.steps, 3);
	lgl->stats->bkwd.str3++;
	*strptr += 1;
	res = 1;
      }
    } else {
      assert (tag == OCCS);
      lidx = blit >> RMSHFT;
      c = lglidx2lits (lgl, 0, lidx);
      if (c == skip) continue;
      INCSTEPS (elm.steps);
      count = size;
      remove = 0;
      for (l = c; (other = *l); l++) {
	val = lglval (lgl, other);
	if (val > 0) { remove = INT_MAX; break; }
	if (val < 0) continue;
	assert (!val);
	marked = lglmarked (lgl, other);
	if (!marked) continue;
	count--;
	if (marked > 0) continue;
	if (remove) { remove = INT_MAX; break; }
	remove = other;
      }
      if (count > 0) continue;
      if (remove == INT_MAX) continue;
      if (!remove) {
	assert (!(w <= skip && skip < eow) || skip < p);
	LOGCLS (BWL, c, "subsumed large clause");
	ADDSTEPS (elm.steps, (l - c));
	if (druplig) lgldrupligdelclsaux (lgl, c);
	lglrmlcls (lgl, lidx, 0);
	lgl->stats->bkwd.subl++;
	*subptr += 1;
	res = 1;
      } else if (lglsmallirr (lgl)) {
	LOGCLS (BWL, c, "removing %d and thus strengthening clause", remove);
	assert (lglmtstk (&lgl->clause));
	assert (lglmtstk (&saved));
	for (l = c; (other = *l); l++) {
	  if (druplig) lglpushstk (lgl, &saved, other);
	  if (other == remove) continue;
	  val = lglval (lgl, other);
	  if (val < 0) continue;
	  assert (!val);
	  lglpushstk (lgl, &lgl->clause, other);
	}
	lglpushstk (lgl, &lgl->clause, 0);
	LOGCLS (BWL, lgl->clause.start, "strengthened clause");

	if (druplig) {
	  lgldrupligaddcls (lgl, REDCS);
	  assert (l - c == lglcntstk (&saved));
	  lglpushstk (lgl, &saved, 0);
	  lgldrupligdelclsaux (lgl, saved.start);
	  lglclnstk (&saved);
	}
	ADDSTEPS (elm.steps, (l - c));
	lglrmlcls (lgl, lidx, 0);
	if (l - c == size) lgl->stats->bkwd.strlself++;

	lgladdcls (lgl, 0, 0, 1);
	lglclnstk (&lgl->clause);
	lgl->stats->bkwd.strl++;
	*strptr += 1;
	res = 1;
      }
    }
  }
  lglrelstk (lgl, &saved);
  return res;
}

static int lglbackwardclause (LGL * lgl,
                              const int * clause, const int * skip,
			      int * subsumedptr, int * strengthenedptr) {
  int lit, size, minlit, minlit2, minocc, minocc2, tmpocc, res, large;
  const int * p;
  long delta;
  lgl->stats->bkwd.tried.clauses++;
  INCSTEPS (elm.steps);
  minocc = minlit = minocc2 = minlit2 = 0;
  for (p = clause; (lit = *p); p++) {
    lglmarkunmarked (lgl, lit);
    tmpocc = lglocc (lgl, lit);
    if (!minlit || tmpocc < minocc) {
      minocc2 = minocc, minlit2 = minlit;
      minocc = tmpocc, minlit = lit;
    } else if (!minlit2 || tmpocc < minocc2) {
      minocc2 = tmpocc, minlit2 = lit;
    }
  }
  size = p - clause;
  assert (size >= 2);
  LOG (BWL, "minimum occurrence %d of literal %d", minocc, minlit);
  LOG (BWL, "next minimum occurrence %d of literal %d", minocc2, minlit2);
  large = (lgl->irr.start <= clause && clause < lgl->irr.top);
  delta = large ? clause - lgl->irr.start : 0;
  res = lglbackwardlit (lgl, clause, skip,
		        size, minlit, subsumedptr, strengthenedptr);
  if (!res) {
    res = lglbackwardlit (lgl, clause, skip,
			  size, minlit2, subsumedptr, strengthenedptr);
  }
  if (res && large) clause = lgl->irr.start + delta;
  for (p = clause; (lit = *p); p++)
    lglunmark (lgl, lit);
  return res;
}

static void lglbackward (LGL * lgl, int * u, int * t,
                         int64_t steps, int * completedptr) {
  int idx, sign, lit, blit, red, tag, other, other2, clause[4], * w;
  int oldtouched, newtouched, round, touched;
  int64_t limit, delta, scaled;
  const int * p, * eow, * c;
  HTS * hts;
  Stk stk;
  lglstart (lgl, &lgl->times->backward);
  lgl->elm->bkwdocclim =
    lglfactor (lgl, lgl->opts->bkwdocclim.val, lgl->stats->elm.count);
  CLR (stk);
  *u = *t = 0;
  if (LLMAX/lgl->opts->bkwdscale.val <= steps/100) scaled = LLMAX;
  else scaled = steps/100 * lgl->opts->bkwdscale.val;
  if (lgl->limits->elm.steps - scaled <= lgl->stats->elm.steps)
    limit = lgl->limits->elm.steps;
  else limit = lgl->stats->elm.steps + scaled;
  delta = limit - lgl->stats->elm.steps;
  lglprt (lgl, 1,
    "[elim-%d-%d] backward subsumption/strengthening limit %lld",
    lgl->stats->elm.count, lgl->elm->round, delta);
  round = 0;
RESTARTOUCHED:
  round++;
  oldtouched = lglcntstk (&lgl->elm->touched.stk);
  assert (oldtouched >= lgl->elm->touched.mt);
  oldtouched -= lgl->elm->touched.mt;
  lglprt (lgl, 1,
    "[elim-%d-%d-%d] backward checking %d touched variables %.0f%%",
    lgl->stats->elm.count, lgl->elm->round, round,
    oldtouched, lglpcnt (oldtouched, lglrem (lgl)));
  *completedptr = 0;
  while ((idx = lglpoptouched (lgl))) {
    for (sign = -1; sign <= 1; sign += 2) {
RESTARTLIT:
      if (lgl->mt) goto DONE;
      if (lglterminate (lgl)) goto DONE;

      // TODO DID NOT WORK?  REMOVE OR FIX?
      // if (!lglsyncunits (lgl)) goto DONE;

      if (!lglisfree (lgl, idx)) continue;
      if (INCSTEPS (elm.steps) >= limit) goto DONE;
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      lglclnstk (&stk);
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag != BINCS) continue;
	red = blit & REDCS;
	if (red) continue;
	lglpushstk (lgl, &stk, blit);
      }
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag != TRNCS) continue;
	red = blit & REDCS;
	if (red) continue;
	lglpushstk (lgl, &stk, blit);
	lglpushstk (lgl, &stk, *p);
      }
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	red = blit & REDCS;
	if (!red && (tag == BINCS || tag == TRNCS)) continue;
	lglpushstk (lgl, &stk, blit);
	if (tag == TRNCS || tag == LRGCS)
	  lglpushstk (lgl, &stk, *p);
      }
      assert (lglcntstk (&stk) == hts->count);
      memcpy (w, stk.start, lglcntstk (&stk) * sizeof *w);
      clause[0] = lit;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	if (red) continue;
	if (INCSTEPS (elm.steps) >= limit) goto DONE;
	if (tag == BINCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  clause[1] = other, clause[2] = 0;
	  if (!lglbackwardclause (lgl, clause, p, u, t)) continue;
	} else if (tag == TRNCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  clause[1] = other, clause[2] = other2, clause[3] = 0;
	  if (!lglbackwardclause (lgl, clause, p, u, t)) continue;
	} else { assert (tag == OCCS); continue; }
	if (lglflush (lgl)) goto RESTARTLIT;
	else goto DONE;
      }
    }
  }
  for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
    if (!lglsmallirr (lgl)) goto DONE;
    if (INCSTEPS (elm.steps) >= limit) goto DONE;
    if (*(p = c) >= NOTALIT) continue;
    touched = 0;
    while ((lit = *p)) {
      if (!touched && lgltouched (lgl, lit)) touched = 1;
      p++;
    }
    if (touched) lglbackwardclause (lgl, c, c, u, t);
  }
  if (round < lgl->opts->bkwdroundlim.val &&
      !lglmtstk (&lgl->elm->touched.stk))
    goto RESTARTOUCHED;
  *completedptr = 1;
DONE:
  newtouched = lglcntstk (&lgl->elm->touched.stk);
  assert (newtouched >= lgl->elm->touched.mt);
  newtouched -= lgl->elm->touched.mt;
  if (*completedptr)
    assert (!newtouched),
    lglprt (lgl, 1,
      "[elim-%d-%d-%d] fully completed backward checking in %d rounds",
      lgl->stats->elm.count, lgl->elm->round, round, round);
  else
    lglprt (lgl, 1,
      "[elim-%d-%d-%d] incomplete backward checking %d remain %.0f%%",
      lgl->stats->elm.count, lgl->elm->round, round,
      newtouched, lglpcnt (newtouched, oldtouched));
  lglrelstk (lgl, &stk);
  lglstop (lgl);
}

static int lglelmdone (LGL * lgl, int * allptr) {
  int newelmd, eliminated, subsumed, strengthened, bkwdcompleted;
  const int oldonotsched = lgl->donotsched;
  const int newdonotsched = !lgl->opts->bkwdresched.val;
  int64_t steps, oldsteps;
  if (!lglsmallirr (lgl)) return 1;
  if (lglterminate (lgl)) return 1;
  if (lgl->limits->elm.steps <= lgl->stats->elm.steps) return 1;
  if (!lglmtstk (&lgl->esched)) return 0;
  steps = ((oldsteps = lgl->stats->elm.steps) - lgl->elm->oldsteps);
  eliminated = (newelmd = lgl->stats->elm.elmd) - lgl->elm->oldelmd;
  assert (eliminated >= 0);
  if (eliminated <= 0) {
    lglprt (lgl, 1,
      "[elim-%d-%d] no variable eliminated in round %d in %lld steps",
      lgl->stats->elm.count, lgl->elm->round,
      lgl->elm->round, (LGLL) steps);
    return 1;
  }
  lglprt (lgl, 1,
    "[elim-%d-%d] eliminated %d variables %.0f%% in round %d in %lld steps",
    lgl->stats->elm.count, lgl->elm->round, eliminated, 
    lglpcnt (eliminated, lgl->nvars - 2), lgl->elm->round, (LGLL) steps);
  if (oldonotsched != newdonotsched) lgl->donotsched = newdonotsched;
  lglbackward (lgl, &subsumed, &strengthened, steps, &bkwdcompleted);
  if (oldonotsched != newdonotsched) lgl->donotsched = oldonotsched;
  steps = lgl->stats->elm.steps - oldsteps;
  lglprt (lgl, 1,
    "[elim-%d-%d] subsumed %d and strengthened %d clauses in %lld steps",
    lgl->stats->elm.count, lgl->elm->round, subsumed, strengthened,
    (LGLL) steps);
  lgl->stats->elm.rounds++;
  lgl->elm->oldelmd = newelmd;
  lgl->elm->oldsteps = lgl->stats->elm.steps;
  if (lgl->mt) return 1;
  if (lgl->limits->elm.steps <= lgl->stats->elm.steps) return 1;
  if (lgl->elm->round >= lgl->opts->elmroundlim.val) return 1;
  if (!lglmtstk (&lgl->esched)) {
    lglprt (lgl, 1,
      "[elim-%d-%d] rescheduled %d variables %.0f%% by backward subsumption",
      lgl->stats->elm.count, lgl->elm->round,
      lglcntstk (&lgl->esched),
      lglpcnt (lglcntstk (&lgl->esched), lglrem (lgl)));
    lgl->elm->round++;
    return 0;
  }
  if (bkwdcompleted && *allptr) return 1;
  *allptr = 1;
  if (!lglforceschedall (lgl)) return 1;
  lgl->elm->round++;
  return 0;
}

static void lglinitouched (LGL * lgl) {
  int idx;
  assert (lgl->eliminating);
  lgl->elm->touched.nvars = lgl->nvars;
  NEW (lgl->elm->touched.pos, lgl->nvars);
  for (idx = 2; idx < lgl->nvars; idx++)
    lgl->elm->touched.pos[idx] = -1;
}

static void lglreltouched (LGL * lgl) {
  lglrelstk (lgl, &lgl->elm->touched.stk);
  DEL (lgl->elm->touched.pos, lgl->elm->touched.nvars);
}

static int lglelim (LGL * lgl) {
  int res = 1, idx, elmd, oldnvars, sched, success, all, rem;
  int oldrem = lgl->elmrem, oldall = lgl->elmall, resched;
  assert (lgl->opts->elim.val);
  assert (!lgl->mt);
  assert (lgl->nvars > 2);
  assert (!lgl->eliminating);
  assert (!lgl->simp);
  assert (!lgl->occs);
  lglstart (lgl, &lgl->times->elim);
  lgl->stats->elm.count++;
  lgl->eliminating = lgl->simp = lgl->occs = 1;
  NEW (lgl->elm, 1);
  lgl->elm->oldelmd = lgl->stats->elm.elmd;
  lgl->elm->round = 1;
  lgl->elm->oldsteps = lgl->stats->elm.steps;
  lgl->stats->elm.rounds++;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  oldnvars = lglrem (lgl);
  lglgc (lgl);
  assert (lgl->frozen);
  assert (!(oldall && !oldrem));
  all = !oldrem || !oldall;
  if (all)
    lglprt (lgl, 1,
      "[elim-%d] scheduling all variables this time",
       lgl->stats->elm.count);
  else if (!lgleschedrem (lgl, 1)) all = 1, oldrem = 0;
  if (!all) assert (!lgl->donotsched), lgl->donotsched = 1;
  assert (!lgl->touching);
  lgldense (lgl, 1);
  lglinitouched (lgl);
  if (!all) assert (lgl->donotsched), lgl->donotsched = 0;
  assert (!lgl->touching), lgl->touching = 1;
  lglsetelmlim (lgl, &resched);
  if (!resched) assert (!lgl->donotsched), lgl->donotsched = 1;
  sched = lglcntstk (&lgl->esched);
  while (res && !lglelmdone (lgl, &all)) {
    idx = lglpopesched (lgl);
    lglavar (lgl, idx)->donotelm = 1;
    lglelimlit (lgl, idx);
    res = lglflush (lgl);
    assert (res || lgl->mt);
  }
  assert (lgl->touching), lgl->touching = 0;
  if (!resched) assert (lgl->donotsched), lgl->donotsched = 0;
  rem = lglcntstk (&lgl->esched);
  if (!rem) {
    lglprt (lgl, 1,
      "[elim-%d] fully completed in %d rounds",
      lgl->stats->elm.count, lgl->elm->round);
    lgl->elmrtc = 1;
  } else {
    lglprt (lgl, 1,
      "[elim-%d] incomplete %d not tried %.0f%% in round %d",
      lgl->stats->elm.count,
      rem, lglpcnt (rem, lgl->nvars - 2),
      lgl->elm->round);
  }
  lglsetdonotesched (lgl, !rem);
  lglrelstk (lgl, &lgl->esched);
  lglreltouched (lgl);
  lglrelecls (lgl);
  lglsparse (lgl);
  lglgc (lgl);
  DEL (lgl->elm, 1);
  lgl->elmrem = rem > 0;
  lgl->elmall = all && lgl->elmrem;
  lglprt (lgl, 1,
    "[elim-%d] transition to [ all %d rem %d ] state",
    lgl->stats->elm.count, lgl->elmall, lgl->elmrem);
  elmd = oldnvars - lglrem (lgl);
  lgl->stats->irrprgss += elmd;
  lglprt (lgl, 1,
    "[elim-%d] eliminated %d = %.0f%% variables out of %d scheduled",
    lgl->stats->elm.count, elmd, lglpcnt (elmd, sched), sched);
  if (!lgl->elmrtc  &&
      lgl->stats->elm.count <= lgl->opts->elmsuccessmaxwortc.val) {
    success = 1;
    lglprt (lgl, 1,
      "[elim-%d] considered successful since not run to completion yet",
      lgl->stats->elm.count);
  } else if (elmd) {
    success = (oldnvars/lgl->opts->elmsuccessrat.val <= elmd);
    if (!success)
      lglprt (lgl, 1,
	"[elim-%d] %d < 1/%d * %d = %d considered unsuccessful",
	lgl->stats->elm.count, elmd, lgl->opts->elmsuccessrat.val,
	sched, sched/lgl->opts->elmsuccessrat.val);
  } else success = 0;
  LGLUPDPEN (elm, success);
  lglrep (lgl, 2, 'e');
  assert (lgl->eliminating && lgl->simp && lgl->occs);
  lgl->eliminating = lgl->simp = lgl->occs = 0;
  lglstop (lgl);
  return !lgl->mt;
}

static int lglsynceqs (LGL * lgl) {
  int * ereprs, emax = lgl->maxext;
  int elit1, erepr1, elit2, erepr2;
  int ilit1, irepr1, ilit2, irepr2;
  int consumed = 0, produced = 0;
  assert (!lgl->mt);
  assert (!lgl->level);
  if (!lgl->nvars) return 1;
  if (!lgl->cbs) return 1;
  if (!lgl->cbs->eqs.lock.fun) return 1;
  assert (lgl->repr);
  ereprs = lgl->cbs->eqs.lock.fun (lgl->cbs->eqs.lock.state);
  produced = consumed = 0;
  for (elit1 = 1; elit1 <= emax; elit1++) {
    if (lglelitblockingoreliminated (lgl, elit1)) continue;
    elit2 = lglptrjmp (ereprs, emax, elit1);
    if (elit2 == elit1) continue;
    if (lglelitblockingoreliminated (lgl, elit2)) continue;
    assert (elit2 != -elit1);
    erepr1 = lglerepr (lgl, elit1);
    if (lglelitblockingoreliminated (lgl, erepr1)) continue;
    erepr2 = lglerepr (lgl, elit2);
    if (lglelitblockingoreliminated (lgl, erepr2)) continue;
    if (erepr1 == erepr2) continue;
    if (erepr1 == -erepr2) {
INCONSISTENT:
      LOG (1, "inconsistent external equivalence %d %d", elit1, elit2);
      assert (!lgl->level);
      lglmt (lgl);
      goto DONE;
    }
    ilit1 = lglimport (lgl, elit1);
    ilit2 = lglimport (lgl, elit2);
    if (ilit1 == ilit2) continue;
    if (ilit1 == -ilit2) goto INCONSISTENT;
    if (abs (ilit1) <= 1) continue;
    if (abs (ilit2) <= 1) continue;
    irepr1 = lglirepr (lgl, ilit1);
    irepr2 = lglirepr (lgl, ilit2);
    if (irepr1 == irepr2) continue;
    if (irepr1 == -irepr2) goto INCONSISTENT;
    if (abs (irepr1) <= 1) continue;
    if (abs (irepr2) <= 1) continue;
    LOG (2, "importing external equivalence %d %d as internal %d %d",
	 elit1, elit2, irepr1, irepr2);
    if (!lglisfree (lgl, irepr1)) continue;
    if (!lglisfree (lgl, irepr2)) continue;
    consumed++;
    lglimerge (lgl, irepr1, irepr2);
  }
  LOG (1, "consumed %d equivalences", consumed);
  for (elit1 = 1; elit1 <= emax; elit1++) {
    elit2 = lglerepr (lgl, elit1);
    if (elit1 == elit2) continue;
    assert (elit1 != -elit2);
    erepr1 = lglptrjmp (ereprs, emax, elit1);
    erepr2 = lglptrjmp (ereprs, emax, elit2);
    if (erepr1 == erepr2) continue;
    assert (erepr1 != -erepr2);
    LOG (2, "exporting external equivalence %d %d", erepr1, erepr2);
    produced++;
    ereprs[abs (erepr1)] = (erepr1 < 0) ? -erepr2 : erepr2;
  }
  LOG (1, "produced %d equivalences", produced);
DONE:
  if (lgl->cbs->eqs.unlock.fun)
    lgl->cbs->eqs.unlock.fun (lgl->cbs->eqs.unlock.state, consumed, produced);
  return !lgl->mt;
}

static int lgldecomp (LGL * lgl) {
  int res = 1, oldnvars = lgl->nvars, removed;
  assert (lgl->opts->decompose.val || lgl->probing || lgl->gaussing || lgl->sweeping);
  assert (!lgl->decomposing);
  lglstart (lgl, &lgl->times->decompose);
  lgl->stats->decomps++;
  lgl->decomposing = 1;
  lgl->simp++;
  assert (lgl->simp > 0);
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  res = 0;
  lglgc (lgl);
  if (!lglsyncunits (lgl)) goto DONE;
  lglgc (lgl);
  if (lgl->mt) goto DONE;
  if (!lgltarjan (lgl)) goto DONE;
  if (!lglsynceqs (lgl)) goto DONE;
  lglchkred (lgl);
  lgldcpdis (lgl);
  lgldcpcln (lgl);
  lgldcpcon (lgl);
  lglcompact (lgl);
  lglmap (lgl);
  if (lgl->mt) goto DONE;
  if (!lglbcp (lgl)) { lglmt (lgl); goto DONE; }
  lglcount (lgl);
  lglgc (lgl);
  if (lgl->mt) goto DONE;
  res = 1;
DONE:
  if (lgl->repr) DEL (lgl->repr, lgl->nvars);
  assert (lgl->decomposing);
  lgl->decomposing = 0;
  ASSERT (lgl->simp > 0);
  lgl->simp--;
  removed = oldnvars - lgl->nvars;
  if (removed)
    lglprt (lgl, 1,
      "[decomp-%d] removed %d variables",
      lgl->stats->decomps, removed);
  lglrep (lgl, 2, 'd');
  lglstop (lgl);
  return res;
}

int lglnvars (LGL * lgl) { return lglrem (lgl); }

int lglnclauses (LGL * lgl) { return lgl->stats->irr.clauses.cur; }

static int lgldstpull (LGL * lgl, int lit) {
  AVar * av;
  av = lglavar (lgl, lit);
  assert ((lit > 0) == av->wasfalse);
  if (av->mark) return 0;
  if (!lglevel (lgl, lit)) return 0;
  av->mark = 1;
  if (lgldecision (lgl, lit)) {
    lglpushstk (lgl, &lgl->clause, lit);
    LOG (3, "added %d to learned clause", lit);
  } else {
    lglpushstk (lgl, &lgl->seen, -lit);
    LOG (3, "pulled in distillation literal %d", -lit);
  }
  return 1;
}

static int lglanalit (LGL * lgl, int lit) {
  int r0, r1, antecedents, other, next, tag, * p, * rsn;
  AVar * av;
  assert (lglmtstk (&lgl->seen));
  assert (lglmtstk (&lgl->clause));
  antecedents = 1;
  av = lglavar (lgl, lit);
  rsn = lglrsn (lgl, lit);
  r0 = rsn[0], r1 = rsn[1];
  LOGREASON (2, lit, r0, r1, "starting literal analysis for %d with", lit);
  LOG (3, "added %d to learned clause", lit);
  lglpushstk (lgl, &lgl->clause, lit);
  assert ((lit < 0) == av->wasfalse);
  assert (!av->mark);
  av->mark = 1;
  next = 0;
  for (;;) {
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      lgldstpull (lgl, other);
      if (tag == TRNCS) lgldstpull (lgl, r1);
    } else if (tag == UNITCS) assert (!lglevel (lgl, lit));
    else if (tag == DECISION) assert (lglavar (lgl, lit)->assumed);
    else {
      assert (tag == LRGCS);
      for (p = lglidx2lits (lgl, (r0 & REDCS), r1); (other = *p); p++)
	if (other != lit) lgldstpull (lgl, *p);
    }
    if (next == lglcntstk (&lgl->seen)) break;
    lit = lglpeek (&lgl->seen, next++);
    assert ((lit < 0) == lglavar (lgl, lit)->wasfalse);
    rsn = lglrsn (lgl, lit);
    r0 = rsn[0], r1 = rsn[1];
    LOGREASON (2, lit, r0, r1, "literal analysis of");
    antecedents++;
  }
  lglpopnunmarkstk (lgl, &lgl->seen);
  LOG (2, "literal analysis used %d antecedents", antecedents);
  assert (lglcntstk (&lgl->clause) >= 1);
  return antecedents;
}

static int lglfailedass (LGL * lgl) {
  assert (lgl->level >= lgl->alevel);
  return lgl->level == lgl->alevel && lgl->failed;
}

static void lglanafailed (LGL * lgl) {
  int ilit, elit, erepr, failed, size;
  unsigned bit, rbit, ibit, count;
  Ext * ext, * rext;
  const int * p;
  AVar * av;
  assert (lgl->mt || lglfailedass (lgl));
  if (lgl->mt) {
    LOG (1, "no failed assumptions since CNF unconditionally inconsistent");
  } else if ((failed = lgl->failed) == -1) {
    assert (!lgl->level);
    elit = 0;
    for (p = lgl->eassume.start; !elit && p < lgl->eassume.top; p++) {
      erepr = lglerepr (lgl, *p);
      if (lglederef (lgl, erepr) < 0) elit = *p;
    }
    assert (elit);
    LOG (1, "found single external failed assumption %d", elit);
    ext = lglelit2ext (lgl, elit);
    assert (!ext->failed);
    bit = 1u << (elit < 0);
    assert (ext->assumed & bit);
    ext->failed |= bit;
  } else {
    assert (abs (failed) > 1);
    if ((av = lglavar (lgl, failed))->assumed == 3) {
      LOG (1, "inconsistent internal assumptions %d and %d", failed, -failed);
      assert (!av->failed);
      av->failed = 3;
    } else {
      lglanalit (lgl, -failed);
      for (p = lgl->clause.start; p < lgl->clause.top; p++) {
	ilit = *p;
	av = lglavar (lgl, ilit);
	bit = (1u << (ilit > 0));
	assert (av->assumed & bit);
	assert (!(av->failed & bit));
	av->failed |= bit;
      }
      size = lglcntstk (&lgl->clause);
      assert (size > 0);
      lglpushstk (lgl, &lgl->clause, 0);
      lglprt (lgl, 2,
	 "[analyze-final] learned clause with size %d out of %d",
	 size, lglcntstk (&lgl->eassume));
      LOGCLS (2, lgl->clause.start, "failed assumption clause");
      lgldrupligaddcls (lgl, REDCS);
      lgladdcls (lgl, REDCS, size, 0);
      lglpopstk (&lgl->clause);
      lglpopnunmarkstk (lgl, &lgl->clause);
    }
    count = 0;
    for (p = lgl->eassume.start; p < lgl->eassume.top; p++) {
      elit =  *p;
      bit = 1u << (elit < 0);
      ext = lglelit2ext (lgl, elit);
      assert (!ext->eliminated && !ext->blocking);
      assert (ext->assumed & bit);
      if (ext->failed & bit) continue;
      if (ext->equiv) {
	erepr = ext->repr;
	rbit = bit;
	if (erepr < 0) rbit ^= 3;
	if (elit < 0) erepr = -erepr;
	rext = lglelit2ext (lgl, erepr);
	assert (!rext->equiv);
	if (rext->failed & rbit) continue;
	ilit = rext->repr;
	ibit = rbit;
	if (ilit < 0) ilit = -ilit, ibit ^= 3;
	if (ilit == 1) continue;
	assert (ilit && ilit != -1);
	av = lglavar (lgl, ilit);
	if (!(av->failed & ibit)) continue;
	rext->failed |= rbit;
	count++;
	if (rext->assumed & rbit) {
	  LOG (2,
	       "found representative external failed assumption %d",
	       erepr);
	} else {
	  LOG (2,
	       "found non representative external failed assumption %d",
	       elit);
	  ext->failed |= bit;
	}
      } else {
	ilit = ext->repr;
	ibit = bit;
	if (ilit < 0) ilit = -ilit, ibit ^= 3;
	if (ilit == 1) continue;
	assert (ilit && ilit != -1);
	av = lglavar (lgl, ilit);
	if (!(av->failed & ibit)) continue;
	LOG (2, "found external failed assumption %d", elit);
	ext->failed |= bit;
	count++;
      }
    }
    LOG (1, "found %u external failed assumptions", count);
  }
  TRANS (FAILED);
}

static void lglternreslit (LGL * lgl, int lit) {
  int * pw, * peow, * nw, * neow, * p, * n;
  int pblit, ptag, pother, pother2, pdelta;
  int nblit, ntag, nother, nother2, ndelta;
  HTS * phts, * nhts;
  int a, b, c;

  phts = lglhts (lgl, lit);
  pw = lglhts2wchs (lgl, phts);
  peow = pw + phts->count;
  nhts = lglhts (lgl, -lit);
  nw = lglhts2wchs (lgl, nhts);
  neow = nw + nhts->count;
  for (n = nw; n < neow; n++) {
    if (INCSTEPS (ternres.steps) >= lgl->limits->ternres.steps) return;
    nblit = *n;
    ntag = nblit & MASKCS;
    if (ntag == BINCS || ntag == OCCS) continue;
    if (ntag == TRNCS) break;
    assert (ntag == LRGCS);
    n++;
  }
  if (n >= neow) return;
  for (p = pw;
       p < peow && lgl->stats->ternres.steps < lgl->limits->ternres.steps;
       p++) {
    INCSTEPS (ternres.steps);
    pblit = *p;
    ptag = pblit & MASKCS;
    if (ptag == BINCS || ptag == OCCS) continue;
    if (ptag == TRNCS || ptag == LRGCS) p++;
    if (ptag == LRGCS) continue;
    assert (ptag == TRNCS);
    pother = pblit >> RMSHFT;
    if (lglval (lgl, pother)) continue;
    pother2 = *p;
    if (lglval (lgl, pother2)) continue;
    for (n = nw;
	 n < neow && lgl->stats->ternres.steps < lgl->limits->ternres.steps;
	 n++) {
      INCSTEPS (ternres.steps);
      nblit = *n;
      ntag = nblit & MASKCS;
      if (ntag == BINCS || ntag == OCCS) continue;
      if (ntag == TRNCS || ntag == LRGCS) n++;
      if (ntag == LRGCS) continue;
      assert (ntag == TRNCS);
      nother = nblit >> RMSHFT;
      if (lglval (lgl, nother)) continue;
      nother2 = *n;
      if (lglval (lgl, nother2)) continue;
      if ((nother == pother && nother2 == pother2) ||
	  (nother == pother2 && nother2 == pother)) {
	a = nother, b = nother2;
	if (lglhasbin (lgl, a, b)) continue;
	lgl->stats->ternres.bin++;
	LOG (2, "ternary resolvent %d %d", a, b);
	lgldrupligaddclsarg (lgl, REDCS, a, b, 0);
	lglwchbin (lgl, a, b, REDCS);
	lglwchbin (lgl, b, a, REDCS);
	lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
	lglwrktouch (lgl, a);
	lglwrktouch (lgl, b);
      } else {
	a = nother, b = nother2;
	if (nother == pother || nother2 == pother) c = pother2;
	else if (nother == pother2 || nother2 == pother2) c = pother;
	else continue;
	assert (a != b && b != c && a != c);
	assert (a != -b);
	if (a == -c || b == -c) continue;
	if (lglhastrn (lgl, a, b, c)) continue;
	lgl->stats->ternres.trn++;
	LOG (2, "ternary resolvent %d %d %d", a, b, c);
	lgldrupligaddclsarg (lgl, REDCS, a, b, c, 0);
	lglwchtrn (lgl, a, b, c, REDCS);
	lglwchtrn (lgl, b, a, c, REDCS);
	lglwchtrn (lgl, c, a, b, REDCS);
	lgl->stats->red.trn++, assert (lgl->stats->red.trn > 0);
	lglwrktouch (lgl, a);
	lglwrktouch (lgl, b);
	lglwrktouch (lgl, c);
      }
      pdelta = p - pw;
      phts = lglhts (lgl, lit);
      pw = lglhts2wchs (lgl, phts);
      peow = pw + phts->count;
      p = pw + pdelta;
      ndelta = n - nw;
      nhts = lglhts (lgl, -lit);
      nw = lglhts2wchs (lgl, nhts);
      neow = nw + nhts->count;
      n = nw + ndelta;
    }
  }
}

static void lglternresidx (LGL * lgl, int idx) {
  lglternreslit (lgl, idx);
  lglternreslit (lgl, -idx);
}

static void lglseternreslim (LGL * lgl) {
  int64_t limit, irrlim;
  int pen, szpen;
  if (lgl->opts->ternresrtc.val) {
    lgl->limits->ternres.steps = LLMAX;
    lglprt (lgl, 1,
       "[ternres-%d] really no limit (run to completion)",
       lgl->stats->ternres.count);
  } else {
    limit = (lgl->opts->trnreleff.val*lglvisearch (lgl))/1000;
    if (limit < lgl->opts->trnrmineff.val) limit = lgl->opts->trnrmineff.val;
    if (lgl->opts->trnrmaxeff.val >= 0 && limit > lgl->opts->trnrmaxeff.val)
      limit = lgl->opts->trnrmaxeff.val;
    if (lgl->stats->ternres.count <= 1 &&
        lgl->opts->boost.val &&
        lgl->opts->ternresboost.val > 1) {
      lglprt (lgl, 1,
        "[ternres-%d] boosting ternary resolution limit by %d",
	lgl->stats->ternres.count, lgl->opts->ternresboost.val);
      limit *= lgl->opts->ternresboost.val;
    }
    limit >>= (pen = lgl->limits->ternres.pen + (szpen = lglszpen (lgl)));
    irrlim = (4*lgl->stats->irr.clauses.cur) >> szpen;
    if (lgl->opts->irrlim.val && limit < irrlim) {
      limit = irrlim;
      lglprt (lgl, 1,
  "[ternres-%d] limit %lld based on %d irredundant clauses penalty %d",
	lgl->stats->ternres.count,
	(LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
    } else
      lglprt (lgl, 1, "[ternres-%d] limit %lld with penalty %d = %d + %d",
	lgl->stats->ternres.count, (LGLL) limit,
	pen, lgl->limits->ternres.pen, szpen);
    lgl->limits->ternres.steps = lgl->stats->ternres.steps + limit;
  }
}

static void lglprternresrem (LGL * lgl) {
  int idx, ret = 0, rem = 0, sum;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    if (lglavar (lgl, idx)->donoternres) ret++; else rem++;
  }
  if (rem) {
    sum = ret + rem;
    lglprt (lgl, 1,
      "[ternres-%d] %d variables remain %.0f%% (%d retained %.0f%%)",
      lgl->stats->ternres.count,
      rem, lglpcnt (rem, sum),
      ret, lglpcnt (ret, sum));
  } else {
    lglprt (lgl, 1,
      "[ternres-%d] fully completed ternary resolution",
      lgl->stats->ternres.count);
    for (idx = 2; idx < lgl->nvars; idx++)
      lglavar (lgl, idx)->donoternres = 0;
  }
}

static void lglternresinit (LGL * lgl) {
  int idx, schedulable = 0, donoternres = 0;
  lglwrkinit (lgl, 1, 1);
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    if (lglavar (lgl, idx)->donoternres) donoternres++;
    else schedulable++;
  }
  if (!schedulable) {
    donoternres = 0;
    for (idx = 2; idx < lgl->nvars; idx++) {
      if (!lglisfree (lgl, idx)) continue;
      lglavar (lgl, idx)->donoternres = 0;
      schedulable++;
    }
  }
  if (!donoternres)
    lglprt (lgl, 1,
      "[ternres-%d] all %d free variables schedulable",
      lgl->stats->ternres.count, schedulable);
  else
    lglprt (lgl, 1,
      "[ternres-%d] %d schedulable variables %.0f%%",
      lgl->stats->ternres.count, schedulable, lglpcnt (schedulable, lgl->nvars-2));
  assert (!lgl->donotsched), lgl->donotsched = 1;
  lglrandidxtrav (lgl, lglwrktouch);
  assert (lgl->donotsched), lgl->donotsched = 0;
}

static int lglternres (LGL * lgl) {
  int before, after, delta;
  int before2, after2, delta2;
  int before3, after3, delta3;
  int success, lit;
  if (lgl->nvars <= 2) return 1;
  lglstart (lgl, &lgl->times->ternres);
  ASSERT (!lgl->simp && !lgl->ternresing);
  lgl->simp = lgl->ternresing = 1;
  lgl->stats->ternres.count++;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  lglseternreslim (lgl);

  lglternresinit (lgl);

  before2 = lgl->stats->ternres.bin;
  before3 = lgl->stats->ternres.trn;
  while (lgl->stats->ternres.steps < lgl->limits->ternres.steps) {
    if (lglterminate (lgl)) break;
    if (!lglsyncunits (lgl)) break;
    if (!(lit = lglwrknext (lgl))) {
      lglprt (lgl, 2,  "[ternres-%d] saturated", lgl->stats->ternres.count);
      break;
    }
    INCSTEPS (ternres.steps);
    assert (lit > 0);
    if (!lglisfree (lgl, lit)) continue;
    lglavar (lgl, lit)->donoternres = 1;
    lglternresidx (lgl, lit);
  }
  after2 = lgl->stats->ternres.bin;
  after3 = lgl->stats->ternres.trn;
  after = after2 + after3;
  before = before2 + before3;
  delta2 = after2 - before2;
  delta3 = after3 - before3;
  delta = after - before;
  success = before < after;
  lglprt (lgl, 1,
    "[ternres-%d] %d ternary resolvents (%d bin, %d trn)",
    lgl->stats->ternres.count, delta, delta2, delta3);
  LGLUPDPEN (ternres, success);
  assert (lgl->simp && lgl->ternresing);
  lgl->simp = lgl->ternresing = 0;
  lglprternresrem (lgl);
  lglrep (lgl, 2, 'T');
  lglwrkreset (lgl);
  lglstop (lgl);
  return !lgl->mt;
}

typedef struct POSLIDX { int pos, lidx; } POSLIDX;

int lglcmposlidx (LGL * lgl, int * lits, POSLIDX * a, POSLIDX * b) {
  const int * c = lits + a->pos, * d = lits + b->pos;
  int i, l, k, p, q;
  for (i = 0; i < 4; i++) {
    l = c[i], k = d[i];
    ASSERT (l != INT_MIN);
    ASSERT (k != INT_MIN);
    p = abs (l), q = abs (k);
    if (p < q) return -1;
    if (p > q) return 1;
    if (l < k) return -1;
    if (l > k) return 1;
  }
  return 0;
}

#define LGLCMPOSLIDX(A,B) lglcmposlidx (lgl, lits.start, (A), (B))

static int lglquatres1 (LGL * lgl, int * trnptr) {
  int mask, size, lidx, count, lrg, total, tlrg, pos, m[4], i, j, k, l, n;
  int glue, maxglue = lglscaleglue (lgl, 4), pivot, a, b, redi, redj, red;
  int assigned, trn, sub;
  const int * p, * c, * d;
  POSLIDX * pls;
  Stk lits, clauses, *s;
  assert (!lgl->level);
  assert (lgl->notrim);
  lglstart (lgl, &lgl->times->quatres1);
  CLR (lits); CLR (clauses);
  total = trn = sub = tlrg = 0;
  for (glue = -1; glue <= maxglue; glue++) {
    count = lrg = 0;
    if (glue < 0) mask = MAXGLUE, s = &lgl->irr;
    else mask = glue, s = lgl->red + glue;
    for (c = s->start; c < s->top; c = p + 1) {
      if (*c >= REMOVED) { p = c; continue; }
      if (glue >= 0) assert (lglisact (*c)), c++;
      assigned = 0;
      for (p = c; *p; p++)
	if (lglval (lgl, *p)) assigned++;
      if (assigned) continue;
      size = p - c;
      lrg++;
      if (size > 4) continue;
      assert (size == 4);
      lidx = c - s->start;
      assert (lidx >= 0);
      lidx <<= GLUESHFT;
      lidx |= mask;
      pos = lglcntstk (&lits);
      assert (!(pos & 3));
      lglpushstk (lgl, &clauses, pos);
      lglpushstk (lgl, &clauses, lidx);
      for (i = 0; i < 4; i++) m[i] = c[i];
      for (i = 0; i < 3; i++)
	for (j = i+1; j < 4; j++)
	  if (abs (m[i]) > abs (m[j]))
	    SWAP (int, m[i], m[j]);
      for (i = 0; i < 4; i++) lglpushstk (lgl, &lits, m[i]);
      count++;
    }
    if (glue < 0)
      lglprt (lgl, 2,
	"[quatres-%d] found %d irredundant quaternary clauses %.0f%%",
	lgl->stats->quatres.count, count, lglpcnt (count, lrg));
    else
      lglprt (lgl, 2,
	"[quatres-%d] found %d glue %d quaternary clauses %.0f%%",
	lgl->stats->quatres.count, count, glue, lglpcnt (count, lrg));
    total += count;
    tlrg += lrg;
  }
  lglfitstk (lgl, &lits), lglfitstk (lgl, &clauses);
  lglprt (lgl, 1 + !tlrg,
    "[quatres-%d] found %d quaternary clauses %.0f%% in total",
    lgl->stats->quatres.count, total, lglpcnt (total, tlrg));
  pls = (POSLIDX*) clauses.start;
  assert (lglcntstk (&clauses) == 2*total);
  SORT (POSLIDX, pls, total, LGLCMPOSLIDX);
#if 0
  for (i = 0; i < total; i++) {
    c = lits.start + pls[i].pos;
    lidx = pls[i].lidx;
    printf ("c pls[%d] %d %d %d %d (glue %d, pos %d)\n",
      i,
      c[0], c[1], c[2], c[3],
      (lidx & GLUEMASK), (lidx >> GLUESHFT));
  }
#endif
  for (i = 0; i < total - 1; i++) {
    pos = pls[i].pos;
    if (pos < 0) continue;
    c = lits.start + pos;
    for (j = i + 1; j < total; j++) {
      if (pls[i].pos < 0) break;
      pos = pls[j].pos;
      if (pos < 0) break;
      d = lits.start + pos;
      pivot = 0;
      for (k = 0; k < 4; k++) {
	a = c[k], b = d[k];
	if (abs (a) != abs (b)) break;
	if (a == b) continue;
	if (pivot) break;
	pivot = a;
      }
      if (k < 4) break;
      assert (i != j);
      assert (pls[i].lidx != pls[j].lidx);
      redi = ((pls[i].lidx & GLUEMASK) == MAXGLUE) ? 0 : REDCS;
      redj = ((pls[j].lidx & GLUEMASK) == MAXGLUE) ? 0 : REDCS;
      if (pivot) {
	n = 0;
	for (l = 0; l < 4; l++) if (c[l] != pivot) m[n++] = c[l];
	assert (n == 3);
	if (lglhastrn (lgl, m[0], m[1], m[2])) continue;
	red = redi & redj;
	LOG (2,
	  "self-subsuming %s ternary resolvent %d %d %d",
	  red ? "redundant" : "irredundant", m[0], m[1], m[2]);
	lgldrupligaddclsarg (lgl, REDCS, m[0], m[1], m[2], 0);
	lglwchtrn (lgl, m[0], m[1], m[2], red);
	lglwchtrn (lgl, m[1], m[0], m[2], red);
	lglwchtrn (lgl, m[2], m[0], m[1], red);
	if (!red) lglincirr (lgl, 3);
	else lgl->stats->red.trn++, assert (lgl->stats->red.trn > 0);
	lgl->stats->quatres.self2++;
	*trnptr += 1, trn++;
	lgldrupligdelclsarg (lgl, c[0], c[1], c[2], c[3], 0);
	if (redi) lglrmlcls (lgl, pls[i].lidx, REDCS);
	else lglrmlcls (lgl, (pls[i].lidx >> GLUESHFT), 0);
	lgldrupligdelclsarg (lgl, d[0], d[1], d[2], d[3], 0);
	if (redj) lglrmlcls (lgl, pls[j].lidx, REDCS);
	else lglrmlcls (lgl, (pls[j].lidx >> GLUESHFT), 0);
	pls[i].pos = pls[j].pos = -1;
      } else if (redi) {
	lgl->stats->quatres.dup++, sub++;
	lgldrupligdelclsarg (lgl, c[0], c[1], c[2], c[3], 0);
        lglrmlcls (lgl, pls[i].lidx, REDCS);
	pls[i].pos = -1;
      } else if (redj) {
	lgl->stats->quatres.dup++;
	lgldrupligdelclsarg (lgl, d[0], d[1], d[2], d[3], 0);
	lglrmlcls (lgl, pls[j].lidx, REDCS);
	pls[j].pos = -1;
      } else {
	lgl->stats->quatres.dup++;
	lgldrupligdelclsarg (lgl, d[0], d[1], d[2], d[3], 0);
	lglrmlcls (lgl, (pls[j].lidx >> GLUESHFT), 0);
	pls[j].pos = -1;
      }
    }
  }
  lglrelstk (lgl, &lits), lglrelstk (lgl, &clauses);
  lglprt (lgl, 1 + !sub,
    "[quatres-%d-1] removed %d duplicate quaternary clauses",
    lgl->stats->quatres.count, sub);
  lglprt (lgl, 1 + !trn,
    "[quatres-%d-1] added %d double-self-subsuming ternary resolvents",
    lgl->stats->quatres.count, trn);
  lglstop (lgl);
  return tlrg;
}

static int lglhasquad (LGL * lgl) {
  int blit, tag, red, other, other2, lidx, glue, count, lit, other3, val;
  const int * p, * w, * eow, * q, * c, * d, * r, * l;
  int maxglue = lglscaleglue (lgl, 4);
  int maxcount, tmpcount, maxlit;
  HTS * hts;
  assert (lglcntstk (&lgl->clause) == 5);
  maxcount = -1, maxlit = 0;
  for (p = (c = lgl->clause.start); (lit = *p); p++) {
    assert (!lglval (lgl, lit));
    tmpcount = lglhts (lgl, lit)->count;
    if (tmpcount <= maxcount) continue;
    maxcount = tmpcount, maxlit = lit;
  }
  assert (maxlit), assert (maxcount >= 0);
  for (p = c; (lit = *p); p++) {
    if (lit == maxlit) continue;
    hts = lglhts (lgl, lit);
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    for (q = w; q < eow; q++) {
      blit = *q;
      tag = blit & MASKCS;
      if (tag == BINCS) {
	other = blit >> RMSHFT;
	for (r = c; (other3 = *r); r++)
	  if (other3 == other) return 1;
      } else if (tag == TRNCS) {
	other = blit >> RMSHFT;
	other2 = *++q;
	count = 0;
	for (r = c; (other3 = *r); r++) {
	       if (other3 == other) { if (++count == 2) return 1; }
	  else if (other3 == other2) { if (++count == 2) return 1; }
	}
      } else {
	assert (tag == LRGCS);
	red = blit & REDCS;
	lidx = *++q;
	if (red) {
	  glue = lidx & GLUEMASK;
	  if (glue > maxglue) continue;
	}
	d = lglidx2lits (lgl, red, lidx);
	count = 0;
	for (l = d; (other = *l); l++) {
	  val = lglval (lgl, other);
	  if (val > 0) break;
	  if (val < 0) continue;
	  if (count >= 4) break;
	  for (r = c; (other3 = *r); r++)
	    if (other3 == other) break;
	  if (!other3) break;
	  count++;
	}
	if (!other) return 1;
      }
    }
  }
  return 0;
}

static void lglquatres2 (LGL * lgl, int * trnptr, int * quadptr) {
  int lit, sign, other, blit, tag, red, lidx, trn, quat, glue, glue2;
  int count, pos, neg, extra, pivot, other2, other3, rednew;
  const int * start, * c, * p, * w, * eow, * q, * d, * l;
  int maxcheck = lgl->stats->quatres.count, check;
  int maxglue = lglscaleglue (lgl, 4), val;
  long delta;
  HTS * hts;
  Stk * s;
  lglstart (lgl, &lgl->times->quatres2);
  assert (!lgl->level);
  assert (lgl->notrim);
  trn = quat = 0;
  for (glue = -1; glue <= maxglue; glue++) {
    s = (glue < 0) ? &lgl->irr : lgl->red + glue;
    for (c = (start = s->start); c < s->top; c = p + 1) {
      if (*c >= REMOVED) { p = c; continue; }
      if (glue >= 0) assert (lglisact (*c)), c++;
      count = 0;
      for (p = c; (lit = *p); p++) {
	val = lglval (lgl, lit);
	if (val < 0) continue;
	if (val > 0) break;
	if (++count > 4) break;
      }
      if (lit) {
	while (*++p)
	  ;
	continue;
      }
      assert (count <= 4);
      if (count < 4) continue;
      for (p = c; (lit = *p); p++)
	if (!lglval (lgl, lit))
	  lglmark (lgl, lit);
      for (p = c; (lit = *p); p++) {
	if (lglval (lgl, lit)) continue;
	for (sign = -1; sign <= 1; sign += 2) {
	  hts = lglhts (lgl, sign*lit);
	  w = lglhts2wchs (lgl, hts);
	  eow = w + hts->count;
	  check = 0;
	  for (q = w; check < maxcheck && q < eow; q++) {
	    blit = *q;
	    tag = blit & MASKCS;
	    red = blit & REDCS;
	    if (tag == TRNCS || tag == LRGCS) q++;
	    if (maxglue < MAXGLUE && tag == LRGCS) {
	      lidx = *q;
	      if (red) {
		glue2 = lidx & GLUEMASK;
		if (glue2 > maxglue) continue;
	      } else glue2 = -1;
	      if (glue2 < glue) continue;
	      d = lglidx2lits (lgl, red, lidx);
	      if (d == c) continue;
	      if (glue2 == glue && d < c) continue;
	      check++;
	      count = pos = neg = extra = pivot = 0;
	      for (l = d; (other = *l); l++) {
		val = lglval (lgl, other);
		if (val < 0) continue;
		if (val > 0) break;
		val = lglmarked (lgl, other);
		if (val < 0) {
		  if (neg++) break;	
		  pivot = other;
		} else if (val > 0) {
		   if (++pos > 2) break;
		} else {
		  assert (!val);
		  if (count++) break;
		  extra = other;
		}
	      }
	      if (other) continue;
	      if (neg != 1 || pos != 2 || count != 1) continue;
	      assert (extra);
	      assert (lglmtstk (&lgl->clause));
	      for (l = c; (other = *l); l++) {
		if (lglval (lgl, other)) continue;
		if (other == pivot) continue;
		if (other == -pivot) continue;
		lglpushstk (lgl, &lgl->clause, other);
	      }
	      lglpushstk (lgl, &lgl->clause, extra);
	      lglpushstk (lgl, &lgl->clause, 0);
	      if (!lglhasquad (lgl)) {
		LOGCLS (0, c,
		  "1st pivot %d quaternary scaled glue %d antecedent",
		  -pivot, glue);
		LOGCLS (0, d,
		  "2nd pivot %d quaternary scaled glue %d antecedent",
		  pivot, glue2);
		LOGCLS (0, lgl->clause.start, "found quaternary resolvent");
		LOG (5, "before: w + %d = q = eow - %d", (int)(q - w), (int)(eow - w));
		lgldrupligaddcls (lgl, REDCS);
		lgladdcls (lgl, REDCS, 4, 0);
		delta = s->start - start;
		if (delta) {
		  LOG (5, "fixing glue %d clauses start by %ld", glue, delta);
		  c += delta, p += delta, start = s->start;
		}
		hts = lglhts (lgl, sign*lit);
		delta = lglhts2wchs (lgl, hts) - w;
		if (delta) {
		  LOG (5, "fixing %d watches start by %ld", sign*lit, delta);
		  w += delta, q += delta;
		}
		if (w + hts->count != eow) {
		  LOG (5, "fixing %d watches end from %x to %x",
		    sign*lit, eow, w + hts->count);
		  eow = w + hts->count;
		}
		LOG (5, "after: w + %d = q = eow - %d", (int)(q - w), (int)(eow - w));
		lgl->stats->quatres.quat++;
		*quadptr += 1, quat++;
	      }
	      lglclnstk (&lgl->clause);
	    } else if (tag == TRNCS) {
	      if (sign > 0) continue;
	      other = blit >> RMSHFT;
	      if (lglval (lgl, other)) continue;
	      if (lglmarked (lgl, other) <= 0) continue;
	      other2 = *q;
	      if (lglval (lgl, other2)) continue;
	      if (lglmarked (lgl, other2) <= 0) continue;
	      // This gives a usefull ternary self-subsuming resolvent:
	      // (lit A B C) resolved with (-lit A B) gives (A B C)
	      // Other cases produce too many quaternary resolvents (b7ztz6).
	      LOGCLS (0, c,
		"1st pivot %d quaternary scaled glue %d antecedent",
		lit, glue);
	      LOG (0,
	        "2nd pivot %d ternary antecedent %d %d %d",
		-lit, -lit, other, other2);
	      extra = 0;
	      for (l = c; !extra; l++) {
		other3 = *l;
		assert (other3);
		if (other3 == lit) continue;
		assert (other3 != -lit);
		if (other3 == other) continue;
		if (other3 == other2) continue;
		val = lglval (lgl, other3);
		assert (val <= 0);
		if (val) continue;
		extra = other3;
	      }
	      assert (extra != -other);
	      assert (extra != -other2);
	      rednew = (glue >= 0) ? REDCS : 0;
	      LOG (0,
		"self-subsuming %s ternary resolvent %d %d %d",
		rednew ? "redundant" : "irredundant", other, other2, extra);
	      lgldrupligaddclsarg (lgl, REDCS, other, other2, extra, 0);
	      lglwchtrn (lgl, other, other2, extra, rednew);
	      lglwchtrn (lgl, other2, other, extra, rednew);
	      lglwchtrn (lgl, extra, other, other2, rednew);
	      // NOTE: 'hts', 'q', 'w', 'eow' might be invalid now.
	      // But 'c' has to remain valid:
	      assert (s->start == start), assert (c + 4 < s->top);
	      if (!rednew) lglincirr (lgl, 3);
	      else lgl->stats->red.trn++, assert (lgl->stats->red.trn > 0);
	      lgl->stats->quatres.self1++;
	      *trnptr += 1, trn++;
	      for (p = c; (other3 = *p); p++)	// set 'p' to point after 'c'
		if (!lglval (lgl, other3))	// reset marks now because
		  lglunmark (lgl, other3);	// 'lglrmlcls' invalidates 'c'
	      lidx = c - start;
	      if (rednew) {
		assert (lidx >= 0);
		lidx <<= GLUESHFT;
		assert (lidx >= 0);
		assert (0 <= glue), assert (glue <= MAXGLUE);
		lidx |= glue;
	      }
	      lgldrupligdelclsaux (lgl, c);
	      assert (!*p);
	      lglrmlcls (lgl, lidx, rednew);	// rednew = redold (of 'c')
	      assert (start <= c), assert (c + 3 < p), assert (p <= s->top);
	      assert (p[-0] == REMOVED);
	      assert (p[-1] == REMOVED);
	      assert (p[-2] == REMOVED);
	      assert (p[-3] == REMOVED);
	      assert (p[-4] == REMOVED), assert (c[0] == REMOVED);
	      goto NEXT_CLAUSE;
	    }
	  }
	}
      }
      for (p = c; (lit = *p); p++)
	if (!lglval (lgl, lit))
	  lglunmark (lgl, lit);
NEXT_CLAUSE:
      ;
    }
  }
  lglprt (lgl, 1 + !trn,
    "[quatres-%d-2] added %d single-self-subsuming ternary resolvents",
    lgl->stats->quatres.count, trn);
  lglprt (lgl, 1 + !quat,
    "[quatres-%d-2] added %d quaternary resolvents",
    lgl->stats->quatres.count, quat);
  lglstop (lgl);
}

static void lglquatres (LGL * lgl) {
  int trn, quad;
  lglstart (lgl, &lgl->times->quatres);
  if (lgl->level) lglbacktrack (lgl, 0);
  assert (!lgl->simp), assert (!lgl->quatres), assert (!lgl->notrim);
  lgl->simp = lgl->quatres = lgl->notrim = 1;
  lgl->stats->quatres.count++;
  trn = quad = 0;
  if (lglquatres1 (lgl, &trn)) lglquatres2 (lgl, &trn, &quad);
  LGLUPDPEN (quatres, trn + quad);
  assert (lgl->simp), assert (lgl->quatres), assert (lgl->notrim);
  lgl->simp = lgl->quatres = lgl->notrim = 0;
  lglrep (lgl, 2, 'q');
  lglstop (lgl);
}

static int lgltrdbin (LGL * lgl, int start, int target, int irr) {
  int lit, next, blit, tag, red, other, * p, * w, * eow, res, ign, val;
  HTS * hts;
  assert (lglmtstk (&lgl->seen));
  assert (abs (start) < abs (target));
  LOG (2, "trying transitive reduction of %s binary clause %d %d",
       lglred2str (irr^REDCS), start, target);
  lgl->stats->trd.bins++;
  lglpushnmarkseen (lgl, -start);
  next = 0;
  res = 0;
  ign = 1;
  while (next < lglcntstk (&lgl->seen)) {
    lit = lglpeek (&lgl->seen, next++);
    INCSTEPS (trd.steps);
    LOG (3, "transitive reduction search step %d", lit);
    val = lglval (lgl, lit);
    if (val) continue;
    hts = lglhts (lgl, -lit);
    if (!hts->count) continue;
    w = lglhts2wchs (lgl, hts);
    eow = w + hts->count;
    for (p = w; p < eow; p++) {
      blit = *p;
      tag = blit & MASKCS;
      if (tag == LRGCS || tag == TRNCS) p++;
      if (tag != BINCS) continue;
      red = blit & REDCS;
      if (irr && red) continue;
      other = blit >> RMSHFT;
      if (other == start) continue;
      if (other == target) {
	if (lit == -start && ign) { ign = 0; continue; }
	LOG (2, "transitive path closed with %s binary clause %d %d",
	     lglred2str (red), -lit, other);
	res = 1;
	goto DONE;
      }
      val = lglmarked (lgl, other);
      if (val > 0) continue;
      if (val < 0) {
	assert (lgl->level == 0);
	lgl->stats->trd.failed++;
	LOG (1, "failed literal %d in transitive reduction", -start);
	lglunit (lgl, start);
	val = lglbcp (lgl);
	if (!val && !lgl->mt) lglmt (lgl);
	assert (val || lgl->mt);
	res = -1;
	goto DONE;
      }
      lglpushnmarkseen (lgl, other);
      LOG (3, "transitive reduction follows %s binary clause %d %d",
	   lglred2str (red), -lit, other);
    }
  }
DONE:
  lglpopnunmarkstk (lgl, &lgl->seen);
  return res;
}

static void lgltrdlit (LGL * lgl, int start) {
  int target, * w, * p, * eow, blit, tag, red, val;
#ifndef NDEBUG
  int unassigned = lgl->unassigned;
#endif
  HTS * hts;
  val = lglval (lgl, start);
  if (val) return;
  LOG (2, "transitive reduction of binary clauses with %d", start);
  assert (lglmtstk (&lgl->seen));
  hts = lglhts (lgl, start);
  if (!hts->count) return;
  lgl->stats->trd.lits++;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w;
       p < eow && (lgl->stats->trd.steps < lgl->limits->trd.steps);
       p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    target = blit >> RMSHFT;
    if (abs (start) > abs (target)) continue;
    red = blit & REDCS;
    val = lgltrdbin (lgl, start, target, red^REDCS);
    if (!val) continue;
    if (val < 0) { assert (lgl->mt || lgl->unassigned < unassigned); break; }
    LOG (2, "removing transitive redundant %s binary clause %d %d",
	 lglred2str (red), start, target);
    lgl->stats->trd.red++;
    lgl->stats->prgss++;
    lgldrupligdelclsarg (lgl, start, target, 0);
    lglrmbwch (lgl, start, target, red);
    lglrmbwch (lgl, target, start, red);
    assert (!lgl->dense);
    if (red) assert (lgl->stats->red.bin > 0), lgl->stats->red.bin--;
    else lgldecirr (lgl, 2);
    break;
  }
}

static void lglsetrdlim (LGL * lgl) {
  int64_t limit, irrlim;
  int pen, szpen;
  limit = (lgl->opts->trdreleff.val*lglvisearch (lgl))/1000;
  if (limit < lgl->opts->trdmineff.val) limit = lgl->opts->trdmineff.val;
  if (lgl->opts->trdmaxeff.val >= 0 && limit > lgl->opts->trdmaxeff.val)
    limit = lgl->opts->trdmaxeff.val;
  limit >>= (pen = lgl->limits->trd.pen + (szpen = lglszpen (lgl)));
  irrlim = (lgl->stats->irr.clauses.cur) >> szpen;
  if (lgl->opts->irrlim.val && limit < irrlim) {
    limit = irrlim;
    lglprt (lgl, 1,
  "[transred-%d] limit %lld based on %d irredundant clauses penalty %d",
      lgl->stats->trd.count,
      (LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
  } else
    lglprt (lgl, 1, "[transred-%d] limit %lld with penalty %d = %d + %d",
      lgl->stats->trd.count, (LGLL) limit,
      pen, lgl->limits->trd.pen, szpen);
  lgl->limits->trd.steps = lgl->stats->trd.steps + limit;
}

static int lgltrd (LGL * lgl) {
  unsigned pos, delta, mod, ulit, first, last;
  int failed = lgl->stats->trd.failed;
  int red = lgl->stats->trd.red;
  int lit, count, success;
  if (lgl->nvars <= 2) return 1;
  lgl->stats->trd.count++;
  lglstart (lgl, &lgl->times->transred);
  assert (!lgl->simp);
  lgl->simp = 1;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  lglsetrdlim (lgl);
  mod = 2*(lgl->nvars - 2);
  assert (mod > 0);
  pos = lglrand (lgl) % mod;
  delta = lglrand (lgl) % mod;
  if (!delta) delta++;
  while (lglgcd (delta, mod) > 1)
    if (++delta == mod) delta = 1;
  LOG (1, "transitive reduction start %u delta %u mod %u", pos, delta, mod);
  first = mod;
  count = 0;
  while (lgl->stats->trd.steps < lgl->limits->trd.steps) {
    if (lglterminate (lgl)) break;
    if (!lglsyncunits (lgl)) break;
    ulit = pos + 4;
    lit = lglilit (ulit);
    lgltrdlit (lgl, lit);
    count++;
    assert (count <= mod);
    if (lgl->mt) break;
    last = pos;
    pos += delta;
    if (pos >= mod) pos -= mod;
    if (pos == first) { assert (count == mod); break; }
    if (mod == 1) break;
    if (first == mod) first = last;
  }
  failed = lgl->stats->trd.failed - failed;
  red = lgl->stats->trd.red - red;
  success = failed || red;
  LGLUPDPEN (trd, success);
  assert (lgl->simp);
  lglprt (lgl, 1,
    "[transred-%d] removed %d transitive binary clauses",
    lgl->stats->trd.count, red);
  lglprt (lgl, 1 + !failed,
    "[transred-%d] found %d units",
    lgl->stats->trd.count, failed);
  lgl->simp = 0;
  lglrep (lgl, 2, 'D');
  lglstop (lgl);
  return !lgl->mt;
}

static int lglunhdhasbins (LGL * lgl, const DFPR * dfpr,
			   int lit, int irronly) {
  int blit, tag, other, val, red, ulit;
  const int * p, * w, * eos;
  HTS * hts;
  assert (!lglval (lgl, lit));
  hts = lglhts (lgl, lit);
  w = lglhts2wchs (lgl, hts);
  eos = w + hts->count;
  for (p = w; p < eos; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == OCCS) continue;
    if (tag == TRNCS || tag == LRGCS) { p++; continue; }
    red = blit & REDCS;
    if (irronly && red) continue;
    other = blit >> RMSHFT;
    val = lglval (lgl, other);
    assert (val >= 0);
    if (val > 0) continue;
    ulit = lglulit (other);
    if (!dfpr[ulit].discovered) return 1;
  }
  return 0;
}

static int lglunhdisroot (LGL * lgl, int lit, DFPR * dfpr, int irronly) {
  int res = !lglunhdhasbins (lgl, dfpr, lit, irronly);
  assert (!res || !dfpr[lglulit (lit)].discovered);
  return res;
}

static int lglmtwtk (Wtk * wtk) { return wtk->top == wtk->start; }

static int lglfullwtk (Wtk * wtk) { return wtk->top == wtk->end; }

static int lglsizewtk (Wtk * wtk) { return wtk->end - wtk->start; }

static int lglcntwtk (Wtk * wtk) { return wtk->top - wtk->start; }

static void lglrelwtk (LGL * lgl, Wtk * wtk) {
  DEL (wtk->start, lglsizewtk (wtk));
  memset (wtk, 0, sizeof *wtk);
}

static void lglenlwtk (LGL * lgl, Wtk * wtk) {
  int oldsize = lglsizewtk (wtk);
  int newsize = oldsize ? 2*oldsize : 1;
  int count = lglcntwtk (wtk);
  RSZ (wtk->start, oldsize, newsize);
  wtk->top = wtk->start + count;
  wtk->end = wtk->start + newsize;
}

static void lglpushwtk (LGL * lgl, Wtk * wtk,
			Wrag wrag, int lit, int other, int red) {
  Work w;
  if (lglfullwtk (wtk)) lglenlwtk (lgl, wtk);
  w.wrag = wrag;
  w.other = other;
  w.red = red ? 1 : 0;
  w.removed = 0;
  w.lit = lit;
  *wtk->top++ = w;
}

static int lglstamp (LGL * lgl, int root,
		     DFPR * dfpr, DFOPF * dfopf,
		     Wtk * work, Stk * units, Stk * sccs, Stk * trds,
		     int * visitedptr, int stamp, int irronly) {
  int uroot, lit, ulit, blit, tag, red, other, failed, uother, unotother;
  int observed, discovered, pos, undiscovered;
  unsigned start, end, mod, i, j, sccsize;
  const int * p, * w, * eos;
  int startstamp;
  const Work * r;
  int removed;
  HTS * hts;
  Wrag wrag;
  if (lglval (lgl, root)) return stamp;
  uroot =  lglulit (root);
  if (dfpr[uroot].discovered) return stamp;
  assert (!dfpr[uroot].finished);
  assert (lglmtwtk (work));
  assert (lglmtstk (units));
  assert (lglmtstk (sccs));
  assert (lglmtstk (trds));
  LOG (3, "stamping dfs %s %d %s",
       (lglunhdisroot (lgl, root, dfpr, irronly) ? "root" : "start"), root,
       irronly ? "only over irredundant clauses" :
		 "also over redundant clauses");
  startstamp = 0;
  lglpushwtk (lgl, work, PREFIX, root, 0, 0);
  while (!lglmtwtk (work)) {
    INCSTEPS (unhd.steps);
    LGLPOPWTK (work, wrag, lit, other, red, removed);
    if (removed) continue;
    if (wrag == PREFIX) {
      ulit = lglulit (lit);
      if (dfpr[ulit].discovered) {
	dfopf[ulit].observed = stamp;
	LOG (3, "stamping %d observed %d", lit, stamp);
	continue;
      }
      assert (!dfpr[ulit].finished);
      dfpr[ulit].discovered = ++stamp;
      dfopf[ulit].observed = stamp;
      LOG (3, "stamping %d observed %d", lit, stamp);
      *visitedptr += 1;
      if (!startstamp) {
	startstamp = stamp;
	LOG (3, "root %d with stamp %d", lit, startstamp);
	dfpr[ulit].root = lit;
	LOG (4, "stamping %d root %d", lit, lit);
	assert (!dfpr[ulit].parent);
	LOG (4, "stamping %d parent %d", lit, 0);
      }
      LOG (4, "stamping %d discovered %d", lit, stamp);
      lglpushwtk (lgl, work, POSTFIX, lit, 0, 0);
      assert (dfopf[ulit].pushed < 0);
      dfopf[ulit].pushed = lglcntwtk (work);
      assert (!dfopf[ulit].flag);
      dfopf[ulit].flag = 1;
      lglpushstk (lgl, sccs, lit);
      hts = lglhts (lgl, -lit);
      w = lglhts2wchs (lgl, hts);
      eos = w + hts->count;
      for (undiscovered = 0; undiscovered <= 1 ; undiscovered++) {
	start = lglcntwtk (work);
	for (p = w; p < eos; p++) {
	  blit = *p;
	  tag = blit & MASKCS;
	  if (tag == OCCS) continue;
	  if (tag == TRNCS || tag == LRGCS) { p++; continue; }
	  assert (tag == BINCS);
	  red = blit & REDCS;
	  if (irronly && red) continue;
	  other = blit >> RMSHFT;
	  if (lglval (lgl, other)) continue;
	  uother = lglulit (other);
	  if (undiscovered != !dfpr[uother].discovered) continue;
	  // Kind of defensive, since 'lglrmbindup' should avoid it
	  // and this fix may not really work anyhow since it does
	  // not distinguish between irredundant and redundant clauses.
	  // Thus we put a hard COVER here.
	  COVER (lglsignedmarked (lgl, other) > 0);
	  if (lglsignedmarked (lgl, other) > 0) {
	    LOG (2, "stamping skips duplicated edge %d %d", lit, other);
	    continue;
	  }
	  lglsignedmark (lgl, other);
	  lglpushwtk (lgl, work, BEFORE, lit, other, red);
	}
	end = lglcntwtk (work);
	for (r = work->start + start; r < work->top; r++)
	  lglunmark (lgl, r->other);
	mod = (end - start);
	if (mod <= 1) continue;
	for (i = start; i < end - 1;  i++) {
	  assert (1 < mod && mod == (end - i));
	  j = lglrand (lgl) % mod--;
	  if (!j) continue;
	  j = i + j;
	  SWAP (Work, work->start[i], work->start[j]);
	}
      }
    } else if (wrag == BEFORE) {	// before recursive call
      LOG (2, "stamping edge %d %d before recursion", lit, other);
      lglpushwtk (lgl, work, AFTER, lit, other, red);
      ulit = lglulit (lit);
      uother = lglulit (other);
      unotother = lglulit (-other);
      if (lgl->opts->unhdextstamp.val && (irronly || red) &&
	  dfopf[uother].observed > dfpr[ulit].discovered) {
	LOG (2, "transitive edge %d %d during stamping", lit, other);
	lgl->stats->unhd.stamp.trds++;
	lgl->stats->prgss++;
	if (red) lgl->stats->unhd.tauts.red++;
	lglrmbcls (lgl, -lit, other, red);
	if ((pos = dfopf[unotother].pushed) >= 0) {
	  while (pos  < lglcntwtk (work)) {
	    if (work->start[pos].lit != -other) break;
	    if (work->start[pos].other == -lit) {
	      LOG (3, "removing edge %d %d from DFS stack", -other, -lit);
	      work->start[pos].removed = 1;
	    }
	    pos++;
	  }
	}
	work->top--;
	assert (dfpr[uother].discovered); // and thus 'parent' + 'root' set
	continue;
      }
      observed = dfopf[unotother].observed;
      if (lgl->opts->unhdextstamp.val && startstamp <= observed) {
	LOG (1, "stamping failing edge %d %d", lit, other);
	for (failed = lit;
	     dfpr[lglulit (failed)].discovered > observed;
	     failed = dfpr[lglulit (failed)].parent)
	  assert (failed);
	LOG (1, "stamping failed literal %d", failed);
	lglpushstk (lgl, units, -failed);
	lgl->stats->unhd.stamp.failed++;
	if (dfpr[unotother].discovered && !dfpr[unotother].finished) {
	  LOG (2, "stamping skips edge %d %d after failed literal %d",
	       lit, other, failed);
	  work->top--;
	  continue;
	}
      }
      if (!dfpr[uother].discovered) {
	dfpr[uother].parent = lit;
	LOG (4, "stamping %d parent %d", other, lit);
	dfpr[uother].root = root;
	LOG (4, "stamping %d root %d", other, root);
	lglpushwtk (lgl, work, PREFIX, other, 0, 0);
      }
    } else if (wrag == AFTER) {		// after recursive call
      LOG (2, "stamping edge %d %d after recursion", lit, other);
      uother = lglulit (other);
      ulit = lglulit (lit);
      if (lgl->opts->unhdextstamp.val && !dfpr[uother].finished &&
	  dfpr[uother].discovered < dfpr[ulit].discovered) {
	LOG (2, "stamping back edge %d %d", lit, other);
	dfpr[ulit].discovered = dfpr[uother].discovered;
	LOG (3, "stamping %d reduced discovered to %d",
	     lit, dfpr[ulit].discovered);
	if (dfopf[ulit].flag) {
	  LOG (2, "stamping %d as being part of a non-trivial SCC", lit);
	  dfopf[ulit].flag = 0;
	}
      }
      dfopf[uother].observed = stamp;
      LOG (3, "stamping %d observed %d", other, stamp);
    } else {
      assert (wrag == POSTFIX);
      LOG (2, "stamping postfix %d", lit);
      ulit = lglulit (lit);
      if (dfopf[ulit].flag) {
	stamp++;
	sccsize = 0;
	discovered = dfpr[ulit].discovered;
	do {
	  other = lglpopstk (sccs);
	  uother = lglulit (other);
	  dfopf[uother].pushed = -1;
	  dfopf[uother].flag = 0;
	  dfpr[uother].discovered = discovered;
	  dfpr[uother].finished = stamp;
	  LOG (3, "stamping %d interval %d %d parent %d root %d",
	       other, dfpr[uother].discovered, dfpr[uother].finished,
	       dfpr[uother].parent, dfpr[uother].root);
	  sccsize++;
	} while (other != lit);
	assert (lgl->opts->unhdextstamp.val || sccsize == 1);
	if (sccsize > 1) {
	  LOG (2, "stamping non trivial SCC of size %d", sccsize);
	  lgl->stats->unhd.stamp.sumsccsizes += sccsize;
	  lgl->stats->unhd.stamp.sccs++;
	}
      } else assert (lgl->opts->unhdextstamp.val);
    }
  }
  assert (lglmtwtk (work));
  assert (lglmtstk (sccs));
  return stamp;
}

static int lglunhlca (LGL * lgl, const DFPR * dfpr, int a, int b) {
  const DFPR * c, * d;
  int u, v, p;
  if (a == b) return a;
  u = lglulit (a), v = lglulit (b);
  c = dfpr + u, d = dfpr + v;
  if (c->discovered <= d->discovered) {
    p = a;
  } else {
    assert (c->discovered > d->discovered);
    p = b;
    SWAP (const DFPR *, c, d);
  }
  for (;;) {
    assert (c->discovered <= d->discovered);
    if (d->finished <= c->finished) break;
    p = c->parent;
    if (!p) break;
    u = lglulit (p);
    c = dfpr + u;
  }
  LOG (3, "unhiding least common ancestor of %d and %d is %d", a, b, p);
  return p;
}

static int lglunhidefailed (LGL * lgl, const DFPR * dfpr) {
  int idx, sign, lit, unit, nfailed = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      if (lglterminate (lgl)) return 0;
      if (!lglsyncunits (lgl)) return 0;
      INCSTEPS (unhd.steps);
      lit = sign * idx;
      if (lglval (lgl, lit)) continue;
      if (!dfpr[lglulit (lit)].discovered) continue;
      if (lglunhimplincl (dfpr, lit, -lit)) {
	unit = -lit;
	LOG (2, "unhiding %d implies %d", lit, -lit);
      } else if (lglunhimplincl (dfpr, -lit, lit)) {
	unit = lit;
	LOG (2, "unhiding %d implies %d", -lit, lit);
      } else continue;
      LOG (1, "unhiding failed literal %d", -unit);
      lglunit (lgl, unit);
      lgl->stats->unhd.failed.lits++;
      nfailed++;
      if (lglbcp (lgl)) continue;
      LOG (1, "empty clause after propagating unhidden failed literal");
      assert (!lgl->mt);
      lglmt (lgl);
      return 0;
    }
  }
  LOG (1, "unhiding %d failed literals in this round", nfailed);
  return 1;
}

static int lglunhroot (const DFPR * dfpr, int lit) {
  return dfpr[lglulit (lit)].root;
}

static int lglunhidebintrn (LGL * lgl, const DFPR * dfpr, int irronly) {
  int idx, sign, lit, blit, tag, red, other, other2, unit, root, lca;
  int nbinred, ntrnred, nbinunits, ntrnunits, ntrnstr, ntrnhbrs;
  const int * p, * eow;
  int ulit, uother;
  int * w , * q;
  long delta;
  HTS * hts;
  nbinred = ntrnred = nbinunits = ntrnunits = ntrnstr = ntrnhbrs = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      if (lglterminate (lgl)) return 0;
      if (!lglsyncunits (lgl)) return 0;
      INCSTEPS (unhd.steps);
      lit = sign * idx;
      if (lglval (lgl, lit)) continue;
      ulit = lglulit (lit);
      if (!dfpr[ulit].discovered) continue;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      q = w;
      for (p = w; p < eow; p++) {
	blit = *p;
	*q++ = blit;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) *q++ = *++p;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	other = blit >> RMSHFT;
	if (lglval (lgl, other)) continue;
	uother = lglulit (other);
	if (tag == BINCS) {
	  if (lglunhimplies2 (dfpr, other, lit)) {
	    LOG (2, "unhiding removal of literal %d "
		    "with implication %d %d from binary clause %d %d",
		 other, other, lit, lit, other);
	    lgl->stats->unhd.units.bin++;
	    nbinunits++;
	    unit = lit;
UNIT:
	    lglunit (lgl, unit);
	    p++;
	    while (p < eow) *q++ = *p++;
	    lglshrinkhts (lgl, hts, hts->count - (p - q));
	    if (lglbcp (lgl)) goto NEXTIDX;
	    LOG (1, "empty clause after propagating unhidden lifted unit");
	    assert (!lgl->mt);
	    lglmt (lgl);
	    return 0;
	  } else if ((root = lglunhroot (dfpr, -lit)) &&
		     !lglval (lgl, root) &&
		     root == lglunhroot (dfpr, -other)) {
	    LOG (2, "negated literals in binary clause %d %d implied by %d",
		 lit, other, root);
	    lgl->stats->unhd.failed.bin++;
	    lca = lglunhlca (lgl, dfpr, -lit, -other);
	    unit = -lca;
	    assert (unit);
	    goto UNIT;
	  } else if (!irronly && !red) continue;
	  else {
	    if (dfpr[uother].parent == -lit) continue;
	    if (dfpr[ulit].parent == -other) continue;
	    if (!lglunhimplies2 (dfpr, -lit, other)) continue;
	    LOG (2, "unhiding tautological binary clause %d %d", lit, other);
	    lgl->stats->unhd.tauts.bin++;
	    lgl->stats->prgss++;
	    if (red) lgl->stats->unhd.tauts.red++;
	    nbinred++;
	    lglrmbwch (lgl, other, lit, red);
	    LOG (2, "removed %s binary clause %d %d",
		 lglred2str (red), lit, other);
	    lgldeclscnt (lgl, 2, red, 0);
	    assert (!lgl->dense);
	    q--;
	  }
	} else {
	  assert (tag == TRNCS);
	  other2 = *p;
	  if (lglval (lgl, other2)) continue;
	  if (lglunhimplies2incl (dfpr, other, lit) &&
	      lglunhimplies2incl (dfpr, other2, lit)) {
	    LOG (2,
		 "unhiding removal of literals %d and %d with implications "
		 "%d %d and %d %d from ternary clause %d %d %d",
		 other, other2,
		 other, lit,
		 other2, lit,
		 lit, other, other2);
	    lgl->stats->unhd.str.trn += 2;
	    if (red) lgl->stats->unhd.str.red += 2;
	    lgl->stats->unhd.units.trn++;
	    ntrnunits++;
	    unit = lit;
	    goto UNIT;
	  } else if ((root = lglunhroot (dfpr, -lit)) &&
		     !lglval (lgl, root) &&
		     root == lglunhroot (dfpr, -other) &&
		     root == lglunhroot (dfpr, -other2)) {
	    LOG (2,
	      "negation of literals in ternary clauses %d %d %d "
	      "implied by %d", lit, other, other2, root);
	    lgl->stats->unhd.failed.trn++;
	    lca = lglunhlca (lgl, dfpr, -lit, -other);
	    assert (lca);
	    lca = lglunhlca (lgl, dfpr, lca, -other2);
	    assert (lca);
	    unit = -lca;
	    goto UNIT;
	  } else if ((red || irronly) &&
		     (lglunhimplies2incl (dfpr, -lit, other) ||
		      lglunhimplies2incl (dfpr, -lit, other2))) {

	    if (!lgl->opts->unhdatrn.val) continue;
	    if (red && lgl->opts->unhdatrn.val == 1) continue;

	    LOG (2, "unhiding %s tautological ternary clause %d %d %d",
		 lglred2str (red), lit, other, other2);
	    lgl->stats->unhd.tauts.trn++;
	    lgl->stats->prgss++;
	    if (red) lgl->stats->unhd.tauts.red++;
	    ntrnred++;
	    lglrmtwch (lgl, other, lit, other2, red);
	    lglrmtwch (lgl, other2, lit, other, red);
	    LOG (2, "removed %s ternary clause %d %d %d",
		 lglred2str (red), lit, other, other2);
	    lgldeclscnt (lgl, 3, red, 0);
	    assert (!lgl->dense);
	    if (!red && lgl->opts->move.val >= 2) {
	      long delta;
	      assert (q >= w);
	      assert (q[-2] == blit);
	      assert (q[-1] == other2);
	      q[-2] |= REDCS;
	      delta = lglwchtrn (lgl, other, lit, other2, REDCS);
	      delta += lglwchtrn (lgl, other2, lit, other, REDCS);
	      if (delta) w += delta, eow += delta, p += delta, q += delta;
	      LOG (2, "moved ternary clause %d %d %d", lit, other, other2);
              lgl->stats->red.trn++, assert (lgl->stats->red.trn > 0);
	      lgl->stats->moved.trn++;
	    } else q -= 2;
	  } else if (lglunhimplies2incl (dfpr, other2, lit)) {
TRNSTR:
	    LOG (2,
		 "unhiding removal of literal %d with implication "
		 "%d %d from ternary clause %d %d %d",
		 other2, other2, lit, lit, other, other2);
	    lgl->stats->unhd.str.trn++;
	    lgl->stats->prgss++;
	    if (red) lgl->stats->unhd.str.red++;
	    ntrnstr++;
	    lglrmtwch (lgl, other, lit, other2, red);
	    lglrmtwch (lgl, other2, lit, other, red);
	    LOG (2, "removed %s ternary clause %d %d %d",
		 lglred2str (red), lit, other, other2);
	    lgldeclscnt (lgl, 3, red, 0);
	    if (!red) lglincirr (lgl, 2);
	    else lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
	    delta = lglwchbin (lgl, other, lit, red);
	    if (delta) { p += delta, q += delta, eow += delta, w += delta; }
	    (--q)[-1] = red | BINCS | RMSHFTLIT (other);
	    lgldrupligaddclsarg (lgl, REDCS, lit, other, 0);
	    continue;
	  } else if (lglunhimplies2incl (dfpr, other, lit)) {
	    SWAP (int, other, other2);
	    goto TRNSTR;
	  } else if (lgl->opts->unhdhbr.val &&
		     (root = lglunhroot (dfpr, -lit)) &&
		     !lglval (lgl, root)) {
	    if (root == lglunhroot (dfpr, -other2)) {
	      lca = lglunhlca (lgl, dfpr, -lit, -other2);
	    } else if (root == lglunhroot (dfpr, -other)) {
	      lca = lglunhlca (lgl, dfpr, -lit, -other);
	      SWAP (int, other, other2);
	    } else if (lglunhimplies2incl (dfpr, root, -other2)) lca = root;
	    else if (lglunhimplies2incl (dfpr, root, -other)) {
	      lca = root;
	      SWAP (int, other, other2);
	    } else continue;
	    assert (lca);
	    if (abs (lca) == abs (lit)) continue;
	    if (abs (lca) == abs (other)) continue;
	    if (abs (lca) == abs (other2)) continue;
	    if (lglunhimplies2incl (dfpr, lca, other)) continue;
	    LOG (2,
	      "negations of literals %d %d in ternary clause %d %d %d "
	      "implied by %d", lit, other2, lit, other, other2, lca);
	    lgl->stats->unhd.hbrs.trn++;
	    if (red) lgl->stats->unhd.hbrs.red++;
	    lgl->stats->prgss++;
	    ntrnhbrs++;
	    LOG (2, "unhidden hyper binary resolved clause %d %d",-lca,other);
	    lgldrupligaddclsarg (lgl, REDCS, -lca, other, 0);
	    assert (lca != -lit);
	    lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
	    delta = lglwchbin (lgl, -lca, other, REDCS);
	    if (delta) { p += delta, q += delta, eow += delta, w += delta; }
	    delta = lglwchbin (lgl, other, -lca, REDCS);
	    if (delta) { p += delta, q += delta, eow += delta, w += delta; }
	  }
	}
      }
      lglshrinkhts (lgl, hts, hts->count - (p - q));
    }
NEXTIDX:
    ;
  }
  if (nbinred) LOG (2, "unhiding %d tautological binary clauses", nbinred);
  if (nbinunits) LOG (2, "unhiding %d units in binary clauses", nbinunits);
  if (ntrnred) LOG (2, "unhiding %d tautological ternary clauses", ntrnred);
  if (ntrnstr) LOG (2, "unhiding %d strengthened ternary clauses", ntrnstr);
  if (ntrnunits) LOG (2, "unhiding %d units in ternary clauses", ntrnunits);
  if (ntrnstr) LOG (2, 
    "unhidden %d hyper binary resolution from ternary clauses", ntrnhbrs);
  return 1;
}

static int lglcmpdfl (const DFL * a, const DFL * b) {
  return a->discovered - b->discovered;
}

static int lglunhideglue (LGL * lgl, const DFPR * dfpr, int glue, int irronly) {
  DFL * dfl, * eodfl, * d, * e; int szdfl, posdfl, negdfl, ndfl, res;
  int oldsize, newsize, hastobesatisfied, satisfied, tautological;
  int watched, lit, ulit, val, sign, nonfalse, root, lca, unit;
  int ntaut = 0, nstr = 0, nunits = 0, nhbrs = 0, lidx;
  int * p, * q, * c, * eoc, red;
  int lca1, lca2, root1, root2;
  Stk * lits;
#ifndef NLGLOG
  char type[20];
  if (glue < 0) sprintf (type, "irredundant");
  else sprintf (type, "redundant glue %d", glue);
#endif
  assert (!lgl->mt);
  assert (-1 <= glue && glue < MAXGLUE);
  if (glue < 0) {
    lits = &lgl->irr;
    red = 0;
  } else {
    lits = lgl->red + glue;
    red = REDCS;
  }
  res = 1;
  dfl = 0; szdfl = 0;
  // go through all clauses of this glue and for each do:
  //
  //   SHRINK  simplify clause according to current assignment
  //   FAILED  check if it is a hidden failed literal
  //   HTE     check if it is a hidden tautology
  //   STRNEG  remove hidden literals using complement literals
  //   STRPOS  remove hidden literals using positive literals
  //   HBR     perform unhiding hyper binary resolution
  //   NEXT    clean up, unwatch if necessary, reconnect bin/trn, bcp unit
  //
  for (c = lits->start; !lgl->mt && c < lits->top; c = eoc + 1) {
    if (lglterminate (lgl) || !lglsyncunits (lgl)) { res = 0; break; }
    if ((lit = *(eoc = c)) >= NOTALIT) continue;
    INCSTEPS (unhd.steps);
    lidx = c - lits->start;
    if (red) { lidx <<= GLUESHFT; lidx |= glue; }
    watched = 1;
    while (*eoc) eoc++;
    oldsize = eoc - c;

    unit = hastobesatisfied = satisfied = tautological = ndfl = 0;
//SHRINK: check satisfied + remove false literals + count visited
    q = c;
    nonfalse = posdfl = negdfl = 0;
    for (p = c; p < eoc; p++) {
      lit = *p;
      val = lglval (lgl, lit);
      if (val > 0) {
	satisfied = 1;
	q = c + 2;
	break;
      }
      if (val < 0) {
	if (p < c + 2) {
	  *q++ = lit;		// watched, so have to keep it
	  hastobesatisfied = 1;	// for assertion checking only
	}
	continue;
      }
      *q++ = lit;
      nonfalse++;
      if (dfpr[lglulit (lit)].discovered) posdfl++;	// count pos in BIG
      if (dfpr[lglulit (-lit)].discovered) negdfl++;	// count neg in BIG
    }
    *(eoc = q) = 0;
    assert (eoc - c >= 2);	// we assume bcp done before
    ndfl = posdfl + negdfl;	// number of literals in BIG
    if (hastobesatisfied) assert (satisfied);
    if (satisfied || ndfl < 2) goto NEXT;
    assert (nonfalse = eoc - c);
    assert (nonfalse >= negdfl);
//FAILED: find root implying all negated literals
    if (nonfalse != negdfl) goto HTE;	// not enough complement lits in BIG
    assert (c < eoc);
    root = lglunhroot (dfpr, -*c);
    if (lglval (lgl, root)) goto HTE;
    for (p = c + 1; p < eoc && lglunhroot (dfpr, -*p) == root; p++)
      ;
    if (p < eoc) goto HTE;		// at least two roots
    LOGCLS (2, c, "unhiding failed literal through large %s clause",type);
    LOG (2, "unhiding that all negations are implied by root %d", root);
    lca = -*c;
    for (p = c + 1; p < eoc; p++)
      lca = lglunhlca (lgl, dfpr, -*p, lca);
    assert (!lglval (lgl, lca));
    LOG (2, "unhiding failed large %s clause implied by LCA %d", type, lca);
    lgl->stats->unhd.failed.lrg++;
    unit = -lca;
    goto NEXT;  // otherwise need to properly unwatch and restart etc.
		// which is too difficult to implement so leave further
		// simplification of this clause to next unhiding round
HTE:
    if (glue < 0 && !irronly) goto STRNEG; // skip tautology checking if
					   // redundant clauses used and
					   // we work on irredundant clauses
    if (posdfl < 2 || negdfl < 2) goto STRNEG;
    if (ndfl > szdfl) { RSZ (dfl, szdfl, ndfl); szdfl = ndfl; }
    ndfl = 0;
    // copy all literals and their complements to 'dfl'
    for (p = c; p < eoc; p++) {
      for (sign = -1; sign <= 1; sign += 2) {
	lit = *p;
	ulit = lglulit (sign * lit);
	if (!dfpr[ulit].discovered) continue;	// not in BIG so skip
	assert (ndfl < szdfl);
	dfl[ndfl].discovered = dfpr[ulit].discovered;
	dfl[ndfl].finished = dfpr[ulit].finished;
	dfl[ndfl].sign = sign;
#ifndef NLGLOG
	dfl[ndfl].lit4logging = lit;
#endif
	ndfl++;
      }
    }
    ADDSTEPS (unhd.steps, 6);				// rough guess
    SORT (DFL, dfl, ndfl, lglcmpdfl);
    eodfl = dfl + ndfl;
    // Now check if there are two consecutive literals, the first
    // a complement of a literal in the clause, which implies another
    // literal actually occurring positive in the clause, where
    // 'd' ranges over complement literals
    // 'e' ranges over original literals
    for (d = dfl; d < eodfl - 1; d++)
      if (d->sign < 0) break;			// get first negative pos
    while (d < eodfl - 1) {
      assert (d->sign < 0);
      for (e = d + 1; e < eodfl && e->finished < d->finished; e++) {
	if (e->sign < 0) continue;		// get next positive pos
	assert (d->sign < 0 && e->sign > 0);
	assert (d->discovered <= e->discovered);
	assert (e ->finished <= d->finished);
	LOGCLS (2, c,
		"unhiding with implication %d %d tautological %s clause",
		-d->lit4logging, e->lit4logging, type);
	ntaut++;
	lgl->stats->unhd.tauts.lrg++;
	if (red) lgl->stats->unhd.tauts.red++;
	lgl->stats->prgss++;
	tautological = 1;
	goto NEXT;
      }
      for (d = e; d < eodfl && d->sign > 0; d++)
	;
    }
STRNEG:
    if (negdfl < 2) goto STRPOS;
    if (negdfl > szdfl) { RSZ (dfl, szdfl, negdfl); szdfl = negdfl; }
    INCSTEPS (unhd.steps);
    ndfl = 0;
    // copy complement literals to 'dfl'
    for (p = c; p < eoc; p++) {
      lit = *p;
      ulit = lglulit (-lit);			// NOTE: '-lit' not 'lit'
      if (!dfpr[ulit].discovered) continue;
      assert (ndfl < szdfl);
      dfl[ndfl].discovered = dfpr[ulit].discovered;	// of '-lit'
      dfl[ndfl].finished = dfpr[ulit].finished;		// of '-lit'
      dfl[ndfl].lit = lit;			// NOTE: but 'lit' here
      ndfl++;
    }
    if (ndfl < 2) goto STRPOS;
    ADDSTEPS (unhd.steps, 3);			// rough guess
    SORT (DFL, dfl, ndfl, lglcmpdfl);
    eodfl = dfl + ndfl;
    for (d = dfl; d < eodfl - 1; d = e) {
      assert (d->discovered);
      for (e = d + 1; e < eodfl && d->finished >= e->finished; e++) {
	assert (d->discovered <= e->discovered);
	lit = e->lit;
	LOGCLS (2, c,
		"unhiding removal of literal %d "
		"with implication %d %d from large %s clause",
		lit, -d->lit, -e->lit, type);
	e->lit = 0;
	nstr++;
	lgl->stats->unhd.str.lrg++;
	if (red) lgl->stats->unhd.str.red++;
	lgl->stats->prgss++;
	if (!watched) continue;
	if (lit != c[0] && lit != c[1]) continue;
	lglrmlwch (lgl, c[0], red, lidx);
	lglrmlwch (lgl, c[1], red, lidx);
	watched = 0;
      }
    }
    assert (eoc - c >= 1 );
    q = c;
    if (watched) q += 2;			// keep watched literals
						// if we still watch
    // move non BIG literals
    for (p = q; p < eoc; p++) {
      lit = *p;
      ulit = lglulit (-lit);			// NOTE: '-lit' not 'lit'
      if (dfpr[ulit].discovered) continue;
      *q++ = lit;
    }
    // copy from 'dfl' unremoved BIG literals back to clause
    for (d = dfl; d < eodfl; d++) {
      lit = d->lit;
      if (!lit) continue;
      if (watched && lit == c[0]) continue;
      if (watched && lit == c[1]) continue;
      *q++ = lit;
    }
    *(eoc = q) = 0;
STRPOS:
    if (posdfl < 2) goto HBR;
    if (posdfl > szdfl) { RSZ (dfl, szdfl, posdfl); szdfl = posdfl; }
    ndfl = 0;
    // copy original literals to 'dfl' but sort reverse wrt 'discovered'
    for (p = c; p < eoc; p++) {
      lit = *p;
      ulit = lglulit (lit);			// NOTE: now 'lit'
      if (!dfpr[ulit].discovered) continue;
      assert (ndfl < szdfl);
      dfl[ndfl].discovered = -dfpr[ulit].discovered;	// of 'lit'
      dfl[ndfl].finished = -dfpr[ulit].finished;		// of 'lit'
      dfl[ndfl].lit = lit;
      ndfl++;
    }
    if (ndfl < 2) goto NEXT;
    ADDSTEPS (unhd.steps, 3);			// rough guess
    SORT (DFL, dfl, ndfl, lglcmpdfl);
    eodfl = dfl + ndfl;
    for (d = dfl; d < eodfl - 1; d = e) {
      assert (d->discovered);
      for (e = d + 1; e < eodfl && d->finished >= e->finished; e++) {
	assert (d->discovered <= e->discovered);
	lit = e->lit;
	LOGCLS (2, c,
		"unhiding removal of literal %d "
		"with implication %d %d from large %s clause",
		lit, e->lit, d->lit, type);
	e->lit = 0;
	nstr++;
	lgl->stats->unhd.str.lrg++;
	if (red) lgl->stats->unhd.str.red++;
	lgl->stats->prgss++;
	if (!watched) continue;
	if (lit != c[0] && lit != c[1]) continue;
	lglrmlwch (lgl, c[0], red, lidx);
	lglrmlwch (lgl, c[1], red, lidx);
	watched = 0;
      }
    }
    assert (eoc - c >= 1 );
    q = c;
    if (watched) q += 2;
    for (p = q; p < eoc; p++) {
      lit = *p;
      ulit = lglulit (lit);			// NOTE: now 'lit'
      if (dfpr[ulit].discovered) continue;
      *q++ = lit;
    }
    for (d = dfl; d < eodfl; d++) {
      lit = d->lit;
      if (!lit) continue;
      if (watched && lit == c[0]) continue;
      if (watched && lit == c[1]) continue;
      *q++ = lit;
    }
    *(eoc = q) = 0;
HBR:
    if (!lgl->opts->unhdhbr.val) goto NEXT;
    if (eoc - c < 3) goto NEXT;
    root1 = root2 = lca1 = lca2 = 0;
    for (p = c; (lit = *p); p++) {
      root = lglunhroot (dfpr, -lit);
      if (!root) root = -lit;
      if (!root1) { root1 = root; continue; }
      if (root1 == root) continue;
      if (!root2) { root2 = root; continue; }
      if (root2 == root) continue;
      if (lglunhimplies2incl (dfpr, root1, -lit)) { lca1 = root1; continue; }
      if (lglunhimplies2incl (dfpr, root2, -lit)) { lca2 = root2; continue; }
      goto NEXT;			// else more than two roots ...
    }
    assert (root1);
    if (!root2) goto NEXT;
    if (root1 == -root2) goto NEXT;
    if (lglunhimplies2incl (dfpr, root1, -root2)) goto NEXT;
    LOGCLS (2, c, "root hyper binary resolution %d %d of %s clause",
	    -root1, -root2, type);
    if (!lca1 && !lca2) {
      for (p = c; (lit = *p); p++) {
	root = lglunhroot (dfpr, -lit);
	if (root) {
	  if (root == root1)
	    lca1 = lca1 ? lglunhlca (lgl, dfpr, lca1, -lit) : -lit;
	  if (root == root2)
	    lca2 = lca2 ? lglunhlca (lgl, dfpr, lca2, -lit) : -lit;
	} else {
	  assert (!lca2);
	  if (lca1) lca2 = -lit; else lca1 = -lit;
	}
      }
    } else {
      if (!lca1) lca1 = root1;
      if (!lca2) lca2 = root2;
    }
    if (lca1 == -lca2) goto NEXT;
    if (lglunhimplies2incl (dfpr, lca1, -lca2)) goto NEXT;
    LOGCLS (2, c, "lca hyper binary resolution %d %d of %s clause",
	    -lca1, -lca2, type);
    lgl->stats->unhd.hbrs.lrg++;
    if (red) lgl->stats->unhd.hbrs.red++;
    lgldrupligaddclsarg (lgl, REDCS, -lca1, -lca2, 0);
    lglwchbin (lgl, -lca1, -lca2, REDCS);
    lglwchbin (lgl, -lca2, -lca1, REDCS);
    lgl->stats->red.bin++;
    assert (lgl->stats->red.bin > 0);
NEXT:
    newsize = eoc - c;
    assert (satisfied || tautological || newsize >= 1);
    if (newsize <= 3 || satisfied || tautological) {
      lgldeclscnt (lgl, oldsize, red, glue);
      if (watched) {
	lglrmlwch (lgl, c[0], red, lidx);
	lglrmlwch (lgl, c[1], red, lidx);
      }
    } else if (!red) {
      assert (lgl->stats->irr.lits.cur >= c + oldsize - eoc);
      lgl->stats->irr.lits.cur -= c + oldsize - eoc;
    }
    assert (!*eoc);
    for (p = c + oldsize; p > eoc; p--) *p = REMOVED;
    if (satisfied || tautological) {
      while (p >= c) *p-- = REMOVED;
      if (red) { LGLCHKACT (c[-1]); c[-1] = REMOVED; }
      eoc = c + oldsize;
      continue;
    }
    if (newsize < oldsize) lgldrupligaddclsaux (lgl, REDCS, c);
    if (red && newsize <= 3) { LGLCHKACT (c[-1]); c[-1] = REMOVED; }
    if (newsize > 3 && !watched) {
      (void) lglwchlrg (lgl, c[0], c[1], red, lidx);
      (void) lglwchlrg (lgl, c[1], c[0], red, lidx);
    } else if (newsize == 3) {
      LOGCLS (2, c, "large %s clause became ternary", type);
      lglwchtrn (lgl, c[0], c[1], c[2], red);
      lglwchtrn (lgl, c[1], c[0], c[2], red);
      lglwchtrn (lgl, c[2], c[0], c[1], red);
      if (!red) lglincirr (lgl, 3);
      else lgl->stats->red.trn++, assert (lgl->stats->red.trn > 0);
      c[0] = c[1] = c[2] = *eoc = REMOVED;
    } else if (newsize == 2) {
      LOGCLS (2, c, "large %s clause became binary", type);
      lglwchbin (lgl, c[0], c[1], red);
      lglwchbin (lgl, c[1], c[0], red);
      if (!red) lglincirr (lgl, 2);
      else lgl->stats->red.bin++, assert (lgl->stats->red.bin > 0);
      c[0] = c[1] = *eoc = REMOVED;
    } else if (newsize == 1) {
      LOGCLS (2, c, "large %s clause became unit", type);
      unit = c[0];		// even works if unit already set
      c[0] = *eoc = REMOVED;
      lgl->stats->unhd.units.lrg++;
      nunits++;
    }
    if (!unit) continue;
    lglunit (lgl, unit);
    if (lglbcp (lgl)) continue;
    assert (!lgl->mt);
    lglmt (lgl);
    LOG (1, "unhiding large clause produces empty clause");
    res = 0;
  }
  if (nunits)
    LOG (1, "unhiding %d units from large %s clauses", nunits, type);
  if (ntaut)
    LOG (1, "unhiding %d large tautological %s clauses", ntaut, type);
  if (nstr)
    LOG (1, "unhiding removal of %d literals in %s clauses", nstr, type);
  if (nhbrs)
    LOG (1, "unhiding %d hyper binary resolutions in %s clauses", nhbrs, type);
  if (dfl) DEL (dfl, szdfl);
  return res;
}

static void lglfixlrgwchs (LGL * lgl) {
  int idx, sign, lit, blit, tag, red, lidx, fixed;
  const int * p, * eow, * c;
  int * q, * w;
  HTS * hts;
  fixed = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      q = w;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == BINCS) { *q++ = blit; continue; }
	lidx = *++p;
	if (tag == TRNCS) { *q++ = blit; *q++ = lidx; continue; }
	assert (tag == LRGCS);
	red = blit & REDCS;
	c = lglidx2lits (lgl, red, lidx);
	if (*c >= NOTALIT) { fixed++; continue; }
	*q++ = blit;
	*q++ = lidx;
      }
      lglshrinkhts (lgl, hts, hts->count - (p - q));
    }
  }
  assert (!(fixed & 1));
  if (fixed) LOG (1, "fixed %d large watches", fixed);
}

static int lglunhidelrg (LGL * lgl, const DFPR * dfpr, int irronly) {
  int glue, res = 1;
  for (glue = -1; res && glue < MAXGLUE; glue++)
    res = lglunhideglue (lgl, dfpr, glue, irronly);
  lglfixlrgwchs (lgl);
  return res;
}

static int lglunhdunits (LGL * lgl) {
  int res = lgl->stats->unhd.units.bin;
  res += lgl->stats->unhd.units.trn;
  res += lgl->stats->unhd.units.lrg;
  return res;
}

static int lglunhdfailed (LGL * lgl) {
  int res = lgl->stats->unhd.stamp.failed;
  res += lgl->stats->unhd.failed.lits;
  res += lgl->stats->unhd.failed.bin;
  res += lgl->stats->unhd.failed.trn;
  res += lgl->stats->unhd.failed.lrg;
  return res;
}

static int lglunhdhbrs (LGL * lgl) {
  int res = lgl->stats->unhd.hbrs.trn;
  res += lgl->stats->unhd.hbrs.lrg;
  return res;
}

static int lglunhdtauts (LGL * lgl) {
  int res = lgl->stats->unhd.stamp.trds;
  res += lgl->stats->unhd.tauts.bin;
  res += lgl->stats->unhd.tauts.trn;
  res += lgl->stats->unhd.tauts.lrg;
  return res;
}

static int lglunhdstrd (LGL * lgl) {
  int res = lgl->stats->unhd.units.bin;	// shared!
  res += lgl->stats->unhd.str.trn;
  res += lgl->stats->unhd.str.lrg;
  return res;
}

static void lglrmbindup (LGL * lgl) {
  int idx, sign, lit, blit, tag, red, other, round, redrem, irrem;
  int * w, * eow, * p, * q;
  HTS * hts;
  redrem = irrem = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      assert (lglmtstk (&lgl->seen));
      for (round = 0; round < 2; round++) {
	hts = lglhts (lgl, lit);
	w = lglhts2wchs (lgl, hts);
	eow = w + hts->count;
	q = w;
	for (p = w; p < eow; p++) {
	  blit = *p;
	  tag = blit & MASKCS;
	  if (tag != BINCS) *q++ = blit;
	  if (tag== LRGCS || tag == TRNCS) *q++ = *++p;
	  if (tag != BINCS) continue;
	  red = blit & REDCS;
	  other = blit >> RMSHFT;
	  if (lglsignedmarked (lgl, other)) {
	    if (round && !red) goto ONLYCOPY;
	    if (red) redrem++; else irrem++;
	    if (abs (lit) > abs (other)) {
	      LOG (2,
		"removing duplicated %s binary clause %d %d and 2nd watch %d",
		lglred2str (red), lit, other, other);
	      lgldeclscnt (lgl, 2, red, 0);
	      if (!red && lgl->dense)
		lgldecocc (lgl, lit), lgldecocc (lgl, other);
	      lgl->stats->bindup.removed++;
	      if (red) lgl->stats->bindup.red++;
	    } else
	      LOG (2,
		"removing 1st watch %d of duplicated %s binary clause %d %d",
		other, lglred2str (red), other, lit);
	  } else {
	    if ((!round && !red) || (round && red))
	      lglsignedmarknpushseen (lgl, other);
ONLYCOPY:
	    *q++ = blit;
	  }
	}
	lglshrinkhts (lgl, hts, hts->count - (p - q));
      }
      lglpopnunmarkstk (lgl, &lgl->seen);
    }
  }
  assert (!(irrem & 1));
  assert (!(redrem & 1));
}

static DFPR * lglstampall (LGL * lgl, int irronly) {
  int roots, searches, noimpls, unassigned, visited;
  unsigned pos, delta, mod, ulit, first, last, count;
  int root, stamp, rootsonly, lit;
  Stk units, sccs, trds;
  DFOPF * dfopf, * q;
  DFPR * dfpr;
  Wtk work;
  Val val;
  if (lgl->nvars <= 2) return 0;
  lglrmbindup (lgl);
  NEW (dfpr, 2*lgl->nvars);
  NEW (dfopf, 2*lgl->nvars);
  CLR (work); CLR (sccs); CLR (trds); CLR (units);
  for (q = dfopf; q < dfopf + 2*lgl->nvars; q++) q->pushed = -1;
  searches = roots = noimpls = unassigned = stamp = visited = 0;
  for (rootsonly = 1; rootsonly >= 0; rootsonly--) {
    count = 0;
    first = mod = 2*(lgl->nvars - 2);
    assert (mod > 0);
    pos = lglrand (lgl) % mod;
    delta = lglrand (lgl) % mod;
    if (!delta) delta++;
    while (lglgcd (delta, mod) > 1)
      if (++delta == mod) delta = 1;
    LOG (2, "unhiding %s round start %u delta %u mod %u",
	 (rootsonly ? "roots-only": "non-root"), pos, delta, mod);
    for (;;) {
      if (lglterminate (lgl)) { searches = 0; goto DONE; }
      if (!lglsyncunits (lgl)) { assert (lgl->mt); goto DONE; }
      ulit = pos + 4;
      root = lglilit (ulit);
      INCSTEPS (unhd.steps);
      count++;
      if (lglval (lgl, root)) goto CONTINUE;
      if (rootsonly) unassigned++;
      if (dfpr[lglulit (root)].discovered) goto CONTINUE;
      if (rootsonly &&
	  !lglunhdisroot (lgl, root, dfpr, irronly)) goto CONTINUE;
      if (!lglunhdhasbins (lgl, dfpr, -root, irronly)) {
	if (rootsonly) noimpls++;
	goto CONTINUE;
      }
      if (rootsonly) roots++;
      searches++;
      assert (lglmtstk (&units));
      stamp = lglstamp (lgl, root, dfpr, dfopf,
			&work, &units, &sccs, &trds, &visited,
			stamp, irronly);
      while (!lglmtstk (&units)) {
	lit = lglpopstk (&units);
	val = lglval (lgl, lit);
	if (val > 0) continue;
	if (val < 0) {
	  assert (!lgl->mt);
	  LOG (1, "unhidding stamp unit %d already false", lit);
	  lglmt (lgl);
	  goto DONE;
	}
	lglunit (lgl, lit);
	if (!lglbcp (lgl)) {
	  assert (!lgl->mt);
	  LOG (1, "propagating unhidden stamp unit %d failed", lit);
	  lglmt (lgl);
	  goto DONE;
	}
      }
CONTINUE:
      last = pos;
      pos += delta;
      if (pos >= mod) pos -= mod;
      if (pos == first) { assert (count == mod); break; }
      if (mod == 1) break;
      if (first == mod) first = last;
    }
  }
  assert (searches >= roots);
  lglprt (lgl, 2,
	  "[unhd-%d-%d] %d unassigned variables out of %d (%.0f%%)",
	  lgl->stats->unhd.count, lgl->stats->unhd.rounds,
	  lgl->unassigned, lgl->nvars - 2,
	    lglpcnt (lgl->unassigned, lgl->nvars - 2));
  lglprt (lgl, 2,
	  "[unhd-%d-%d] %d root literals out of %d (%.0f%%)",
	  lgl->stats->unhd.count, lgl->stats->unhd.rounds,
	  roots, unassigned, lglpcnt (roots, unassigned));
  lglprt (lgl, 2,
    "[unhd-%d-%d] %d additional non-root searches out of %d (%.0f%%)",
	  lgl->stats->unhd.count, lgl->stats->unhd.rounds,
	  searches - roots, unassigned,
	    lglpcnt (searches - roots, unassigned));
  lglprt (lgl, 2,
	  "[unhd-%d-%d] %d literals not in F2 out of %d (%.0f%%)",
	  lgl->stats->unhd.count, lgl->stats->unhd.rounds,
	  noimpls, unassigned, lglpcnt (noimpls, unassigned));
  lglprt (lgl, 2,
	  "[unhd-%d-%d] %d visited literals out of %d (%.0f%%)",
	  lgl->stats->unhd.count, lgl->stats->unhd.rounds,
	  visited, unassigned, lglpcnt (visited, unassigned));
  lglprt (lgl, 2,
	  "[unhd-%d-%d] %.2f average number visited literals per search",
	  lgl->stats->unhd.count, lgl->stats->unhd.rounds,
	  lglavg (visited, searches));
DONE:
  if (!searches || lgl->mt) { DEL (dfpr, 2*lgl->nvars); dfpr = 0; }
  lglrelwtk (lgl, &work);
  lglrelstk (lgl, &units);
  lglrelstk (lgl, &sccs);
  lglrelstk (lgl, &trds);
  DEL (dfopf, 2*lgl->nvars);
  return dfpr;
}

static void lglsetunhdlim (LGL * lgl) {
  int64_t limit, irrlim;
  int pen, szpen;
  limit = (lgl->opts->unhdreleff.val*lglvisearch (lgl))/1000;
  if (limit < lgl->opts->unhdmineff.val) limit = lgl->opts->unhdmineff.val;
  if (lgl->opts->unhdmaxeff.val >= 0 && limit > lgl->opts->unhdmaxeff.val)
    limit = lgl->opts->unhdmaxeff.val;
  limit >>= (pen = lgl->limits->unhd.pen + (szpen = lglszpenaux (lgl, 1, 1)));
  irrlim = (lgl->stats->irr.clauses.cur/16) >> szpen;
  if (lgl->opts->irrlim.val && limit < irrlim) {
    limit = irrlim;
    lglprt (lgl, 1,
      "[unhide-%d] limit %lld based on %d irredundant clauses penalty %d",
      lgl->stats->unhd.count,
      (LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
  } else
    lglprt (lgl, 1, "[unhide-%d] limit %lld with penalty %d = %d + %d",
      lgl->stats->unhd.count, (LGLL) limit,
      pen, lgl->limits->unhd.pen, szpen);
  lgl->limits->unhd.steps = lgl->stats->unhd.steps + limit;
}

static int lglunhide (LGL * lgl) {
  int irronly, round, maxrounds, noprgssrounds, success;
  int oldunits, oldfailed, oldtauts, oldhbrs, oldstrd;
  int deltaunits, deltafailed;
  int64_t roundprgss = 0;
  DFPR * dfpr = 0;
  assert (lgl->opts->unhide.val);
  if (lgl->nvars <= 2) return 1;
  lgl->stats->unhd.count++;
  assert (!lgl->unhiding);
  lgl->unhiding = 1;
  assert (!lgl->simp);
  lgl->simp = 1;
  lglstart (lgl, &lgl->times->unhide);
  irronly = !lgl->stats->red.bin || (lgl->stats->unhd.count & 1);
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  maxrounds = lgl->opts->unhdroundlim.val;
  lglsetunhdlim (lgl);
  oldunits = lglunhdunits (lgl);
  oldfailed = lglunhdfailed (lgl);
  oldtauts = lglunhdtauts (lgl);
  oldhbrs = lglunhdhbrs (lgl);
  oldstrd = lglunhdstrd (lgl);
  noprgssrounds = round = 0;
  while (!lgl->mt) {
    if (round >= maxrounds) break;
    if (round > 0 &&
        roundprgss == lgl->stats->prgss &&
	noprgssrounds++ == lgl->opts->unhdlnpr.val) {
      LOG (1, "too many non progress unhiding rounds");
      break;
    }
    round++;
    roundprgss = lgl->stats->prgss;
    lgl->stats->unhd.rounds++;
    lglgc (lgl);
    if (!lgl->nvars || lgl->mt) break;
    assert (!dfpr);
    dfpr = lglstampall (lgl, irronly);
    if (!dfpr) break;
    if (!lglunhidefailed (lgl, dfpr)) break;
    if (!lglunhidebintrn (lgl, dfpr, irronly)) break;
    if (!lglunhidelrg (lgl, dfpr, irronly)) break;
    if (lgl->stats->unhd.steps >= lgl->limits->unhd.steps) break;
    irronly = !lgl->stats->red.bin || !irronly;
    DEL (dfpr, 2*lgl->nvars);
    assert (!dfpr);
  }
  if (dfpr) DEL (dfpr, 2*lgl->nvars);
  lglprt (lgl, 1,
    "[unhide-%d-%d] %d units, %d failed, %d tauts, %d hbrs, %d literals",
    lgl->stats->unhd.count, lgl->stats->unhd.rounds,
    (deltaunits = lglunhdunits (lgl) - oldunits),
    (deltafailed = lglunhdfailed (lgl) - oldfailed),
    lglunhdtauts (lgl) - oldtauts,
    lglunhdhbrs (lgl) - oldhbrs,
    lglunhdstrd (lgl) - oldstrd);
  success = deltaunits + deltafailed;
  LGLUPDPEN (unhd, success);
  assert (lgl->simp);
  lgl->simp = 0;
  assert (lgl->unhiding);
  lgl->unhiding = 0;
  lglrep (lgl, 2, 'u');
  lglstop (lgl);
  return !lgl->mt;
}

static int lglpar64 (uint64_t i) {
  unsigned x;
  int res = 0;
  for (x = i; x; x = x & (x - 1))
    res = !res;
  return res;
}

static uint64_t lgldec64 (uint64_t i) {
  uint64_t res;
  for (res = i - 1; lglpar64 (res); res--)
    ;
  return res;
}

static void lglgdump (LGL * lgl) {
#ifndef NLGLOG
  const int * p, * start, * top;
  start = lgl->gauss->xors.start;
  top = lgl->gauss->xors.top;
  for (p = start; p < top; p++) {
    if (*p >= NOTALIT) continue;
    fprintf (lgl->out, "c eqn[%lld]", (LGLL)(p - start));
    while (*p > 1) fprintf (lgl->out, " %d", *p++);
    fprintf (lgl->out, " = %d\n", *p);
  }
#endif
}

static int lglgaussubclsaux (LGL * lgl, uint64_t signs,  const int * c) {
  int lit, i, min, minocc, tmpocc, blit, tag, other, other2, red, lidx;
  const int * p, * w, * eow, * d, * q;
  HTS * hts;
  assert (lgl->dense);
  minocc = INT_MAX;
  min = i = 0;
  INCSTEPS (gauss.steps.extr);
  for (p = c; (lit = *p); p++) {
    if (lglmarked (lgl, lit)) return 0;
    assert (i < 8 * sizeof signs);
    if (signs & (1ull << i++)) lit = -lit;
    lglsignedmark (lgl, lit);
    tmpocc = lglocc (lgl, lit) + lglhts (lgl, lit)->count;
    assert (tmpocc < INT_MAX);
    if (tmpocc >= minocc) continue;
    minocc = tmpocc;
    min = lit;
  }
  assert (min);
  hts = lglhts (lgl, min);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    INCSTEPS (gauss.steps.extr);
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    if (tag == BINCS) {
      other = blit >> RMSHFT;
      if (lglsignedmarked (lgl, other)) return 1;
    } else if (tag == TRNCS) {
      other = blit >> RMSHFT;
      if (!lglsignedmarked (lgl, other)) continue;
      other2 = *p;
      if (lglsignedmarked (lgl, other2)) return 1;
    } else {
      assert (tag == OCCS);
      red = blit & REDCS;
      lidx = blit >> RMSHFT;
      d = lglidx2lits (lgl, red, lidx);
      for (q = d; (other = *q); q++)
	if (!lglsignedmarked (lgl, other)) break;
      if (!other) return 1;
    }
  }
  return 0;
}

static int lglgaussubcls (LGL * lgl, uint64_t signs,  const int * c) {
  int res = lglgaussubclsaux (lgl, signs, c), lit;
  const int * p;
  for (p = c; (lit = *p); p++) lglunmark (lgl, lit);
  return res;
}

#define GL 2

static int lglgaussextractxoraux (LGL * lgl, const int * c) {
  int lit, val, size, maxsize, negs, start, max, *d, * q;
  int allxors = lgl->opts->gaussextrall.val;
  uint64_t signs;
  const int * p;
  assert (!lgl->level);
  maxsize = lgl->opts->gaussmaxor.val;
  max = negs = size = 0;
  start = lglcntstk (&lgl->gauss->xors);
  for (p = c; (lit = *p); p++) {
    if ((val = lglval (lgl, lit)) > 0) return 0;
    if (val < 0) continue;
    if (lit < 0) { 
      if (!allxors && negs) return 0;
      negs = !negs; 
    }
    if (!max || abs (max) < abs (lit)) max = lit;
    lglpushstk (lgl, &lgl->gauss->xors, lit);
    if (++size > maxsize) return 0;
  }
  assert (negs == 0 || negs == 1);
  if (size <= 1) return 0;
  if (!allxors && negs && max > 0) return 0;
  lglpushstk (lgl, &lgl->gauss->xors, 0);
  d = lgl->gauss->xors.start + start;
  assert (size <= 8 * sizeof signs);
  signs = lgldec64 (1ull << size);
  do {
    if (!lglgaussubcls (lgl, signs, d)) break;
    signs = lgldec64 (signs);
  } while (signs &&
           lgl->stats->gauss.steps.extr < lgl->limits->gauss.steps.extr);
  if (signs) return 0;
  for (q = d; (lit = *q); q++) *q = abs (lit);
  *q = !negs;
  LOGEQN (GL, start, "extracted %d-ary XOR constraint",  size);
  lgl->stats->gauss.arity.sum += size;
  if (lgl->stats->gauss.arity.max.total < size)
    lgl->stats->gauss.arity.max.total = size;
  if (lgl->stats->gauss.arity.max.last < size)
    lgl->stats->gauss.arity.max.last = size;
  lgl->stats->gauss.extracted.total++;
  lgl->stats->gauss.extracted.last++;
  return 1;
}

static int lglgaussextractxor (LGL * lgl, const int * c) {
  int old = lglcntstk (&lgl->gauss->xors), res;
  if (!(res = lglgaussextractxoraux (lgl, c)))
    lglrststk (&lgl->gauss->xors, old);
  return res;
}

static int lglgaussextractsmallit (LGL * lgl, int lit) {
  int allxors = lgl->opts->gaussextrall.val;
  int cls[4], blit, tag, other, other2;
  const int * w, * eow, * p;
  HTS * hts;
  if (lgl->stats->gauss.steps.extr >= lgl->limits->gauss.steps.extr) 
    return 0;
  if (lglval (lgl, lit) > 0) return 1;
  hts = lglhts (lgl, lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == OCCS || tag == LRGCS) continue;
    other = blit >> RMSHFT;
    if (!allxors && abs (other) < lit) continue;
    cls[0] = lit;
    cls[1] = other;
    if (tag == TRNCS) {
      other2 = *p;
      if (!allxors && abs (other2) < lit) continue;
      cls[2] = other2;
      cls[3] = 0;
    } else {
      assert (tag == BINCS);
      cls[2] = 0;
    }
    lglgaussextractxor (lgl, cls);
  }
  return 1;
}

static int lglgaussextractsmall (LGL * lgl) {
  int64_t before = lgl->stats->gauss.extracted.total, after, delta;
  int res;
  lglrandlitrav (lgl, lglgaussextractsmallit);
  after = lgl->stats->gauss.extracted.total;
  delta = after - before;
  res = (delta > INT_MAX) ? INT_MAX : delta;
  return res;
}

static int lglgaussextractlarge (LGL * lgl) {
  const int * p, * c;
  int res = 0;
  for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
    if (lgl->stats->gauss.steps.extr >= lgl->limits->gauss.steps.extr) break;
    if (*(p = c) >= NOTALIT) continue;
    res += lglgaussextractxor (lgl, c);
    while (*p) p++;
  }
  return res;
}

static void lglgaussconeqn (LGL * lgl, int eqn) {
  const int * xors = lgl->gauss->xors.start;
  int i, var;
  INCSTEPS (gauss.steps.elim);
  for (i = eqn; (var = xors[i]) > 1; i++)
    lglpushstk (lgl, lgl->gauss->occs + var, eqn);
}

static void lglgaussdiseqn (LGL * lgl, int eqn) {
  int * xors = lgl->gauss->xors.start, i, var;
  for (i = eqn; (var = xors[i]) > 1; i++) {
    xors[i] = NOTALIT;
    lgl->gauss->garbage++;
    INCSTEPS (gauss.steps.elim);
    lglrmstk (lgl->gauss->occs + var, eqn);
  }
  xors[i] = NOTALIT;
  lgl->gauss->garbage++;
}

static void lglgaussconnect (LGL * lgl) {
  int c, i, eox = lglcntstk (&lgl->gauss->xors), connected, var, vars;
  const int * xors = lgl->gauss->xors.start;
  Stk * occs;
  LOG (2,  "connecting equations");
  assert (!lgl->gauss->occs);
  NEW (lgl->gauss->occs, lgl->nvars);
  vars = connected = 0;
  for (c = 0; c < eox; c = i + 1) {
    INCSTEPS (gauss.steps.elim);
    for (i = c; (var = xors[i]) > 1; i++) {
      occs = lgl->gauss->occs + var;
      if (lglmtstk (occs)) vars++;
      lglpushstk (lgl, lgl->gauss->occs + var, c);
      connected++;
    }
  }
  lglprt (lgl, 1, 
     "[gauss-%d] connected %d occurrences of %d variables (average %.1f)",
      lgl->stats->gauss.count, connected, vars, lglavg (connected, vars));
}

static int lglgaussorderidx (LGL * lgl,  int var) {
  assert (2 <= var && var < lgl->nvars);
  if (!lglmtstk (lgl->gauss->occs + var))
    lglpushstk (lgl, &lgl->gauss->order, var);
  return 1;
}

static void lglgaussorder (LGL * lgl) {
  lglrandidxtrav (lgl, lglgaussorderidx);
  NEW (lgl->gauss->eliminated, lgl->nvars);
}

static void lglgaussdisconnect (LGL * lgl) {
  int idx;
  assert (lgl->gauss->occs);
  LOG (2, "disconnecting equations");
  for (idx = 2; idx < lgl->nvars; idx++)
    lglrelstk (lgl, lgl->gauss->occs + idx);
  DEL (lgl->gauss->occs, lgl->nvars);
  assert (!lgl->gauss->occs);
}

static void lglgaussextract (LGL * lgl) {
  int extracted, lits;
  assert (lglsmallirr (lgl));
  if (lgl->level) lglbacktrack (lgl, 0);
  lglgc (lgl);
  if (lgl->mt) return;
  lgldense (lgl, 0);
  extracted = lglgaussextractsmall (lgl);
  extracted += lglgaussextractlarge (lgl);
  lits = lglcntstk (&lgl->gauss->xors) - extracted;
  lglprt (lgl, 1,
    "[gauss-%d] extracted %d xors of average arity %.1f",
    lgl->stats->gauss.count, extracted, lglavg (lits, extracted));
  lglsparse (lgl);
  lglgc (lgl);
  if (lgl->mt) return;
  lglfitstk (lgl, &lgl->gauss->xors);
}

static int lglgaussoccs (LGL * lgl, int a) {
  return lglcntstk (lgl->gauss->occs + a);
}

static int lglcmpgauss (LGL * lgl, int a, int b) {
  int res = lglgaussoccs (lgl, a) - lglgaussoccs (lgl, b);
  if (!res) res = a - b;
  return res;
}

#define LGLCMPGAUSS(A,B) lglcmpgauss (lgl, *(A), *(B))

static void lglgaussort (LGL * lgl) {
  int max = lglcntstk (&lgl->gauss->order), rest, * start;
  assert (lgl->gauss->next <= max);
  rest = max - lgl->gauss->next;
  start = lgl->gauss->order.start + lgl->gauss->next;
  ADDSTEPS (gauss.steps.elim, rest);
  SORT (int, start, rest, LGLCMPGAUSS);
  lglprt (lgl, 3, 
     "[gauss-%d] sorted %d remaining variables",
      lgl->stats->gauss.count, rest);
}

static int lglgausspickeqn (LGL * lgl, int pivot) {
  int res, cand, weight, size, tmp, other, found;
  const int * p, * e, * q;
  Stk * occs;
  assert (lglgaussoccs (lgl, pivot));
  res = -1;
  weight = INT_MAX; size = INT_MAX;
  occs = lgl->gauss->occs + pivot;
  for (p = occs->start; p < occs->top; p++) {
    e = lgl->gauss->xors.start + (cand = *p);
    found = tmp = 0;
    INCSTEPS (gauss.steps.elim);
    for (q = e; (other = *q) > 1; q++) {
      if (lgl->gauss->eliminated[other]) break;
      if (other == pivot) { assert (!found); found++; continue; }
      tmp += lglgaussoccs (lgl, other) - 1;
    }
    if (other > 1) continue;
    assert (found);
    if (res >= 0 && q - e >= size) continue;
    if (res >= 0 && q - e == size && tmp >= weight) continue;
    weight = tmp;
    size = q - e;
    res = cand;
  }
  if (res >= 0)
    LOGEQN (2, res, "picking size %d weight %d equation", size, weight);
  else
    LOG (2, "no uneliminated equation for pivot %d left", pivot);
  return res;
}

static void lglcpystk (LGL * lgl, Stk * dst, Stk * src) {
  const int * p;
  for (p = src->start; p < src->top; p++)
    lglpushstk (lgl, dst, *p);
}

static int lglgaussaddeqn (LGL * lgl, int eqn) {
  const int * p;
  AVar * av;
  int var;
  for (p = lgl->gauss->xors.start + eqn; (var = *p) > 1; p++) {
    av = lglavar (lgl, var);
    if (!av->mark) lglpushstk (lgl, &lgl->clause, var);
    av->mark = !av->mark;
  }
  return var;
}

static void lglgaussubst (LGL * lgl, int pivot, int subst) {
  Stk * occs = lgl->gauss->occs + pivot;
  int eqn, rhs, res;
  const int * p;
  int * q;
  assert (lglcntstk (occs) > 1);
  while (lglcntstk (occs) > 1) {
    if (lglterminate (lgl)) return;
    eqn = occs->start[0];
    if (eqn == subst) eqn = occs->start[1];
    assert (lglmtstk (&lgl->clause));
    LOGEQN (2, subst, "  1st row (kept)     ");
    rhs = lglgaussaddeqn (lgl, eqn);
    LOGEQN (2, eqn, "  2nd row (replaced) ");
    if (lglgaussaddeqn (lgl, subst)) rhs = !rhs;
    lglgaussdiseqn (lgl, eqn);
    q = lgl->clause.start;
    for (p = q; p < lgl->clause.top; p++)
      if (lglmarked (lgl, *p)) *q++ = *p;
    lgl->clause.top = q;
    if (!lglmtstk (&lgl->clause)) {
      res = lglcntstk (&lgl->gauss->xors);
      lglcpystk (lgl, &lgl->gauss->xors, &lgl->clause);
      lglpushstk (lgl, &lgl->gauss->xors, rhs);
      LOGEQN (2, res, "  result row         ");
      lglgaussconeqn (lgl, res);
    } else if (rhs == 0) {
      LOG (2, "trivial result row 0 = 0");
    } else {
      assert (rhs == 1);
      LOG (1, "inconsistent result row 0 = 1 from gaussian elimination");
      lgl->mt= 1;
    }
    lglpopnunmarkstk (lgl, &lgl->clause);
  }
}

static void lglgausschkeliminated (LGL * lgl) {
#ifndef NDEBUG
  int idx, eliminated, occs;
  if (!lgl->opts->check.val) return;
  for (idx = 2; idx < lgl->nvars; idx++) {
    eliminated = lgl->gauss->eliminated[idx];
    occs = lglgaussoccs (lgl, idx);
    if (eliminated == 1) assert (occs == 1);
    if (eliminated == 2) assert (occs == 0);
  }
#endif
}

static void lglgaussgc (LGL * lgl) {
  int count = lglcntstk (&lgl->gauss->xors), * q;
  const int * p;
  if (lgl->gauss->garbage < count/2 + 10000) return;
  lgl->stats->gauss.gcs++;
  lglprt (lgl, 2, 
     "[gauss-%d] collecting %d garbage out of %d",
     lgl->stats->gauss.count, lgl->gauss->garbage, count);
  lglgaussdisconnect (lgl);
  q = lgl->gauss->xors.start;
  for (p = q; p < lgl->gauss->xors.top; p++)
    if (*p != NOTALIT) *q++ = *p;
  lgl->gauss->xors.top = q;
  lglfitstk (lgl, &lgl->gauss->xors);
  lglgaussconnect (lgl);
  lgl->gauss->garbage = 0;
}

static int lglgausselimvar (LGL * lgl, int pivot) {
  int subst, changed, occs, eliminated;
  LOG (2, "eliminating variable %d occurring %d times",
       pivot, lglgaussoccs (lgl, pivot));
  assert (!lgl->gauss->eliminated[pivot]);
  if (!(occs = lglgaussoccs (lgl, pivot))) {
    LOG (2, "variable %d disappeared ", pivot);
    eliminated = 2;
    changed = 0;
  } else if (occs == 1) {
    LOG (2, "eliminated variable %d occurrs exactly once", pivot);
    eliminated = 1;
    changed = 0;
  } else {
    lglgaussgc (lgl);
    subst = lglgausspickeqn (lgl, pivot);
    if (subst >= 0) {
      lglgaussubst (lgl, pivot, subst);
      eliminated = 1;
      changed = 1;
    } else {
      eliminated = 3;
      changed = 0;
    }
  }
  lgl->gauss->eliminated[pivot] = eliminated;
  lglgausschkeliminated (lgl);
  return changed;
}

static void lglgausselim (LGL * lgl) {
  int pivot, changed = 1;
  while (!lgl->mt && lgl->gauss->next < lglcntstk (&lgl->gauss->order)) {
    if (lgl->stats->gauss.steps.elim >= lgl->limits->gauss.steps.elim) break;
    if (lglterminate (lgl)) break;
    if (changed) lglgaussort (lgl);
    pivot = lglpeek (&lgl->gauss->order, lgl->gauss->next++);
    changed = lglgausselimvar (lgl, pivot);
  }
}

static void lglgaussinit (LGL * lgl) {
  assert (!lgl->gauss);
  NEW (lgl->gauss, 1);
}

static void lglgaussreset (LGL * lgl) {
  assert (lgl->gauss);
  if (lgl->gauss->occs) lglgaussdisconnect (lgl);
  if (lgl->gauss->eliminated) DEL (lgl->gauss->eliminated, lgl->nvars);
  lglrelstk (lgl, &lgl->gauss->xors);
  lglrelstk (lgl, &lgl->gauss->order);
  DEL (lgl->gauss, 1);
}

static int lglgaussexp2 (LGL * lgl, int a, int b) {
  assert (lgl->gaussing);
  assert (lglmtstk (&lgl->clause));
  if (lglhasbin (lgl, a, b)) return 0;
  lglpushstk (lgl, &lgl->clause, a);
  lglpushstk (lgl, &lgl->clause, b);
  lglpushstk (lgl, &lgl->clause, 0);
  LOGCLS (2, lgl->clause.start, "gauss exported binary clause");
  lgladdcls (lgl, REDCS, 0, 0);
  lglclnstk (&lgl->clause);
  return 1;
}

static int lglgaussexp3 (LGL * lgl, int a, int b, int c) {
  assert (lgl->gaussing);
  assert (lglmtstk (&lgl->clause));
  if (lglhastrn (lgl, a, b, c)) return 0;
  lglpushstk (lgl, &lgl->clause, a);
  lglpushstk (lgl, &lgl->clause, b);
  lglpushstk (lgl, &lgl->clause, c);
  lglpushstk (lgl, &lgl->clause, 0);
  LOGCLS (2, lgl->clause.start, "gauss exported ternary clause");
  lgladdcls (lgl, REDCS, 0, 0);
  lglclnstk (&lgl->clause);
  return 1;
}

static int lglgaussexport (LGL * lgl) {
  int var, size, val, rhs, unit, a, b, c, exported;
  const int * e, * p, * q;
  for (e = lgl->gauss->xors.start; e < lgl->gauss->xors.top; e = p + 1) {
    if (*(p = e) >= NOTALIT) continue;
    while ((var = *p) > 1) p++;
    rhs = *p;
    assert (lglmtstk (&lgl->clause));
    for (q = e; q < p; q++) {
      var = *q;
      val = lglval (lgl, var);
      if (val < 0) continue;
      if (val > 0) { rhs = !rhs; continue; }
      lglpushstk (lgl, &lgl->clause, var);
    }
    size = lglcntstk (&lgl->clause);
    if (!size && !rhs) continue;
    if (!size && rhs) {
      LOGEQN (1, e - lgl->gauss->xors.start, 
              "gauss exporting inconsistent equation");
      return 0;
    }
    a = (size > 0) ? lgl->clause.start[0] : 0;
    b = (size > 1) ? lgl->clause.start[1] : 0;
    c = (size > 2) ? lgl->clause.start[2] : 0;
    lglclnstk (&lgl->clause);
    if (size == 1) {
      unit = a;
      if (!rhs) unit = -unit;
      LOG (1, "gauss exporting unit %d", unit);
      lgl->stats->gauss.units++;
      lglunit (lgl, unit);
    } else if (size == 2) {
      if (rhs) b = -b;
      exported = lglgaussexp2 (lgl, -a, b);
      exported |= lglgaussexp2 (lgl, a, -b);
      if (exported) {
	LOG (1, "gauss exporting equivalence %d = %d", a, b);
	lgl->stats->gauss.equivs++;
      }
    } else if (size == 3 && lgl->opts->gaussexptrn.val) {
      if (!rhs) c = -c;
      exported = lglgaussexp3 (lgl, a, b, c);
      exported |= lglgaussexp3 (lgl, a, -b, -c);
      exported |= lglgaussexp3 (lgl, -a, b, -c);
      exported |= lglgaussexp3 (lgl, -a, -b, c);
      if (exported) {
	LOG (1, "gauss exporting ternary equation %d + %d + %d = 1", 
	     a, b, c);
	lgl->stats->gauss.trneqs++;
      }
    }
  }
  return 1;
}

static void lglsetgausslim (LGL * lgl) {
  int64_t limit, irrlim;
  int pen, szpen;
  limit = (lgl->opts->gaussreleff.val*lglvisearch (lgl))/1000;
  if (limit < lgl->opts->gaussmineff.val) limit = lgl->opts->gaussmineff.val;
  if (lgl->opts->gaussmaxeff.val >= 0 && limit > lgl->opts->gaussmaxeff.val)
    limit = lgl->opts->gaussmaxeff.val;
  limit >>= (pen = lgl->limits->gauss.pen + (szpen = lglszpen (lgl)));
  irrlim = (lgl->stats->irr.clauses.cur/2) >> szpen;
  if (lgl->opts->irrlim.val && limit < irrlim) {
    limit = irrlim;
    lglprt (lgl, 1,
      "[gauss-%d] limit %lld based on %d irredundant clauses penalty %d",
      lgl->stats->gauss.count,
      (LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
  } else
    lglprt (lgl, 1, "[gauss-%d] limit %lld penalty %d = %d + %d",
      lgl->stats->gauss.count, (LGLL) limit,
      pen, lgl->limits->gauss.pen, szpen);
  lgl->limits->gauss.steps.extr = lgl->stats->gauss.steps.extr + limit;
  lgl->limits->gauss.steps.elim = lgl->stats->gauss.steps.elim + limit;
}

static int lglgauss (LGL * lgl) {
  int oldunits, oldequivs, oldtrneqs;
  int units, equivs, trneqs;
  int success;
  assert (lgl->opts->gauss.val);
  if (lgl->mt) return 0;
  if (lgl->nvars <= 2) return 1;
  lglstart (lgl, &lgl->times->gauss);
  assert (!lgl->simp && !lgl->gaussing);
  lgl->simp = lgl->gaussing = 1;
  lgl->stats->gauss.count++;
  lgl->stats->gauss.extracted.last = 0;
  lgl->stats->gauss.arity.max.last = 0;
  lglsetgausslim (lgl);
  lglgaussinit (lgl);
  lglgaussextract (lgl);
  oldunits = lgl->stats->gauss.units;
  oldequivs = lgl->stats->gauss.equivs;
  oldtrneqs = lgl->stats->gauss.trneqs;
  if (!lglmtstk (&lgl->gauss->xors)) {
    lglgaussconnect (lgl);
    lglgaussorder (lgl);
    lglsetgausslim (lgl);
    lglgausselim (lgl);
    if (!lgl->mt && !lglterminate (lgl)) {
      if (lgl->opts->verbose.val >= 3) lglgdump (lgl);
      lglgaussdisconnect (lgl);
      if (!lglgaussexport (lgl) || !lglbcp (lgl)) lglmt (lgl);
      else if (lgl->limits->gauss.steps.extr > lgl->stats->gauss.steps.extr &&
               lgl->limits->gauss.steps.elim > lgl->stats->gauss.steps.elim)
	lglprt (lgl, 1, "[gauss-%d] fully completed", lgl->stats->gauss.count);
    }
  }
  lglgaussreset (lgl);
  units = lgl->stats->gauss.units - oldunits;
  equivs = lgl->stats->gauss.equivs - oldequivs;
  trneqs = lgl->stats->gauss.trneqs - oldtrneqs;
  success = units || equivs;
  if (!lgl->mt && success && !lglterminate (lgl) && lgl->opts->decompose.val)
    lgldecomp (lgl);
  if (trneqs) success = 1;
  if (lgl->mt)
    lglprt (lgl, 1, "[gauss-%d] proved unsatisfiability",
      lgl->stats->gauss.count);
  else {
    lglprt (lgl, 1, 
      "[gauss-%d] exported %d unary, %d binary and %d ternary equations",
      lgl->stats->gauss.count, units, equivs, trneqs);
  }
  LGLUPDPEN (gauss, success);
  lglrep (lgl, 2, 'G');
  assert (lgl->simp && lgl->gaussing);
  lgl->simp = lgl->gaussing = 0;
  lglstop (lgl);
  return !lgl->mt;
}

/*------------------------------------------------------------------------*/

#define CARDLOGLEVEL 2

static int lglcardsub (LGL * lgl, const int * lits, int bound) {
  int count, size, res, minlit, minocc, nocc, lit, pos, otherbound;
  Card * card = lgl->card;
  const int * p, * c, * q;
  Stk * s;
  minocc = INT_MAX;
  minlit = 0;
  for (p = lits; minocc && (lit = *p); p++) {
    lglmarkunmarked (lgl, lit);
    s = card->occs + lit;
    INCSTEPS (card.steps);
    nocc = lglcntstk (s);
    if (nocc > minocc) continue;
    minlit = lit;
    minocc = nocc;
  }
  res = 0;
  if (minocc && minlit) {
    size = p - lits;
    s = card->occs + minlit;
    for (p = s->start; p < s->top; p++) {
      pos = *p;
      c = card->cards.start + pos;
      INCSTEPS (card.steps);
      otherbound = *c;
      if (otherbound > bound) continue;
      count = 0;
      INCSTEPS (card.steps);
      for (q = c + 1; *q; q++) count++;
      if (count < size) continue;
      count = 0;
      INCSTEPS (card.steps);
      for (q = c + 1; (count < size) && (lit = *q); q++)
	if (lglmarked (lgl, lit) > 0) count++;
      if (count >= size) {
	LOGCLS (CARDLOGLEVEL, lits,
	  "subsumed cardinality constraint %d >=", bound);
	LOGCLS (CARDLOGLEVEL, c + 1,
	  "subsuming cardinality constraint %d >=", otherbound);
	res = 1;
      }
    }
  }
  for (p = lits; (lit = *p); p++) lglunmark (lgl, lit);
  return res;
}

static int lglcard1sub (LGL * lgl, const int * lits) {
  int res, minlit, minocc, nocc, lit, count, size;
  Card * card = lgl->card;
  const int * p, * c, * q;
  Stk * s;
  minocc = INT_MAX;
  minlit = 0;
  for (p = lits; minocc && (lit = *p); p++) {
    lglmarkunmarked (lgl, lit);
    s = card->occs + lit;
    INCSTEPS (card.steps);
    nocc = lglcntstk (s);
    if (nocc > minocc) continue;
    minlit = lit;
    minocc = nocc;
  }
  res = 0;
  if (!minocc || !minlit) goto DONE;
  size = p - lits;
  s = card->occs + minlit;
  count = 0;
  for (p = s->start; !res && p < s->top; p++) {
    c = card->atmost1.start + *p;
    for (q = c; (lit = *q); q++)
      if (lglmarked (lgl, lit) && ++count >= size)
	break;
    if (!lit) continue;
    LOGCLS (CARDLOGLEVEL, lits,
      "subsumed at-most-one cardinality constraint 1 >=");
    LOGCLS (CARDLOGLEVEL, c,
      "subsuming at-most-one cardinality constraint 1 >=");
    res = 1;
  }
DONE:
  for (p = lits; (lit = *p); p++) lglunmark (lgl, lit);
  return res;
}

static int lglcard2sub (LGL * lgl, const int * lits, int * minlitptr) {
  int res, minlit, minocc, nocc, lit, count, size;
  Card * card = lgl->card;
  const int * p, * c, * q;
  Stk * s;
  minocc = INT_MAX;
  minlit = 0;
  for (p = lits; minocc && (lit = *p); p++) {
    lglmarkunmarked (lgl, lit);
    s = card->occs + lit;
    INCSTEPS (card.steps);
    nocc = lglcntstk (s);
    if (nocc > minocc) continue;
    minlit = lit;
    minocc = nocc;
  }
  assert (!minocc || p + 1 == card->atmost2.top);
  res = 0;
  if (!minocc || !minlit || *minlitptr == minlit) goto DONE;
  *minlitptr = minlit;
  size = p - lits;
  s = card->occs + minlit;
  count = 0;
  for (p = s->start; !res && p < s->top; p++) {
    c = card->atmost2.start + *p;
    for (q = c; (lit = *q); q++)
      if (lglmarked (lgl, lit) && ++count >= size)
	break;
    if (!lit) continue;
    LOGCLS (CARDLOGLEVEL, lits,
      "subsumed at-most-two cardinality constraint 2 >=");
    LOGCLS (CARDLOGLEVEL, c,
      "subsuming at-most-two cardinality constraint 2 >=");
    res = 1;
  }
DONE:
  for (p = lits; (lit = *p); p++) lglunmark (lgl, lit);
  return res;
}

static int lgladdcard (LGL * lgl, const int * lits, int bound) {
  Card * card = lgl->card;
  const int * p;
  int start, lit;
#if !defined(NDEBUG) || !defined(NLGLOG)
  int size = 0;
  for (p = lits; *p; p++) size++;
#endif
  if (lglcardsub (lgl, lits, bound)) {
    lgl->stats->card.subsumed++;
    return 0;
  }
  LOGCLS (CARDLOGLEVEL, lits,
    "new %s cardinality constraint %d >=",
    (bound + 1 < size ? "real" : "pseudo"), bound);
  assert (bound <= size);
  assert (size <=
    lglfactor (lgl, lgl->stats->card.count, lgl->opts->cardmaxlen.val));
#ifndef NDEBUG
  for (p = lits; (lit = *p); p++) assert (!card->eliminated[abs (lit)]);
  for (p = lits; (lit = *p); p++) assert (!card->count[abs (lit)]);
#endif
  assert (card);
  start = lglcntstk (&card->cards);
  lglpushstk (lgl, &card->cards, bound);
  for (p = lits; (lit = *p); p++) {
    lglpushstk (lgl, &card->cards, lit);
    lglpushstk (lgl, card->occs + lit, start);
  }
  lglpushstk (lgl, &card->cards, 0);
  return 1;
}

static void lglcardfmstep (LGL * lgl, int pivot,
                           int cardposidx, int cardnegidx) {
  int bn, bp, ln, lp, b, c, s, lit, idx, addcard, len, unit[2], div, elim;
  const int cardcut = lgl->opts->cardcut.val;
  const int * p, * q, * cn, * cp;
  int * r, divsame, cardmaxlen;
  Card * card = lgl->card;
  INCSTEPS (card.steps);
  lgl->stats->card.resolved++;
  assert (0 <= cardposidx && cardposidx < lglcntstk (&card->cards));
  assert (0 <= cardnegidx && cardnegidx < lglcntstk (&card->cards));
  cp = card->cards.start + cardposidx;
  cn = card->cards.start + cardnegidx;
  bp = *cp++; assert (bp >= 0);
  bn = *cn++; assert (bp >= 0);
  LOGCLS (CARDLOGLEVEL, cp,
    "first antecedent fourier-motzkin on %d cardinality constraint %d >=",
    pivot, bp);
  LOGCLS (CARDLOGLEVEL, cn,
    "second antecedent fourier-motzkin on %d cardinality constraint %d >=",
    -pivot, bn);
  b = bp + bn;
  LOG (CARDLOGLEVEL, "starting with bound %d", b);
  assert (lglmtstk (&lgl->clause));
  for (p = cp; (lit = *p); p++) {
    idx = abs (lit);
    assert (!card->count[idx]);
    lglpushstk (lgl, &lgl->clause, idx);
    card->count[idx] += lglsgn (lit);
  }
  lp = p - cp;
  assert (bp < lp);
  elim = 0;
  div = 1;
  for (q = cn; (lit = *q); q++) {
    idx = abs (lit);
    c = card->count[idx];
    assert (!c || abs (c) == 1);
    s = lglsgn (lit);
    if (!c) lglpushstk (lgl, &lgl->clause, idx);
    card->count[idx] += s;
    if (c && c != s) elim++;
    if (c == s) div = 2;
  }
  ln = q - cn;
  assert (bn < ln);
  divsame = 1;
  for (p = lgl->clause.start; divsame && p < lgl->clause.top; p++) {
    idx = abs (*p);
    c = card->count[idx];
    if (!c) continue;
    if (c < 0) c = -c;
    divsame = (c == div);
  }
#ifndef NLGLOG
  if (lgl->opts->log.val >= CARDLOGLEVEL) {
    int first = 1;
    lglogstart (lgl, CARDLOGLEVEL,
      "pseudo-boolean resolvent %d - %d >= ", b, elim);
    for (p = lgl->clause.start; p < lgl->clause.top; p++) {
      idx = *p;
      assert (1 < idx), assert (idx < lgl->nvars);
      c = card->count[idx];
      if (!c) continue;
      if (!first)
	fprintf (lgl->out, " %c ", (c < 0) ? '-' : '+');
      else if (c < 0)
	fputs ("-", lgl->out);
      first = 0;
      c = abs (c);
      assert (c > 0);
      if (c != 1) fprintf (lgl->out, "%d*", c);
      fprintf (lgl->out, "%d", idx);
    }
    if (first) fputs ("0", lgl->out);
    lglogend (lgl);
  }
#endif
  LOG (CARDLOGLEVEL,
    "size %d cardinalty resolvent contains %d eliminated division %d %s", 
    lglcntstk (&lgl->clause) - elim, elim, div, divsame ? "all" : "some");
  r = lgl->clause.start;
  for (p = r; p < lgl->clause.top; p++) {
    idx = *p;
    c = card->count[idx];
    if (divsame || cardcut == 1) c /= div;
    else if (abs (c) != 1 && cardcut == 2 && div == 2) c = 0;
    if (!c) continue;
    lit = (c < 0) ? -idx : idx;
    *r++ = lit;
  }
  lgl->clause.top = r;
  b -= elim;
  assert (div == 1 || div == 2);
  if ((divsame || cardcut == 1) && div == 2) b /= 2;
  len = lglcntstk (&lgl->clause);
  lglpushstk (lgl, &lgl->clause, 0);
  addcard = 0;
  cardmaxlen =
    lglfactor (lgl, lgl->stats->card.count, lgl->opts->cardmaxlen.val);
  if (!cardcut && div > 1) {
    LOG (CARDLOGLEVEL,
      "ignoring resolved cardinality constraint which requires cut");
    assert (!addcard);
  } else if (b < 0) {
    assert (!addcard);
    assert (!lgl->mt);
    LOGCLS (CARDLOGLEVEL, lgl->clause.start,
      "inconsistent cardinality constraint %d >=", b);
    lglmt (lgl);
  } else if (b == 0) {
    assert (!addcard);
    LOGCLS (CARDLOGLEVEL, lgl->clause.start,
      "forcing cardinality constraint %d >=", b);
    for (p = lgl->clause.start; p < lgl->clause.top - 1; p++) {
      lit = *p;
      assert (lit);
      lgl->stats->card.units++;
      lglpushstk (lgl, &lgl->card->units, -lit);
      card->count[abs (lit)] = 0;
      unit[0] = lit;
      unit[1] = 0;
      (void) lgladdcard (lgl, unit, 0);
    }
  } else if (b >= len) {
    LOGCLS (CARDLOGLEVEL, lgl->clause.start,
      "trivial resolved cardinality constraint %d >=", b);
    assert (!addcard);
  } else if (len > cardmaxlen) {
    LOGCLS (CARDLOGLEVEL, lgl->clause.start, 
      "length %d exceeds limit %d of resolved cardinality constraint %d >=",
      len, cardmaxlen, b);
  } else {
    addcard = 1;
    assert (0 < b);
    LOGCLS (CARDLOGLEVEL, lgl->clause.start,
      "resolved cardinality constraint %d >=", b);
    if (b == 1 && 
        ((ln >= 3 && lp >= 3) ||
         lglcntstk (&lgl->clause) > 
	   lglfactor (lgl,
	     lgl->stats->card.count, lgl->opts->cardexpam1.val))) {
      LOGCLS (CARDLOGLEVEL, lgl->clause.start,
        "saving to export at-most-one constraint 1 >=");
      for (p = lgl->clause.start; p < lgl->clause.top; p++)
	lglpushstk (lgl, &lgl->card->expam1, *p);
    }
  }
  cp = card->cards.start + cardposidx + 1;
  cn = card->cards.start + cardnegidx + 1;
  for (p = cp; (lit = *p); p++) card->count[abs (lit)] = 0;
  for (q = cn; (lit = *q); q++) card->count[abs (lit)] = 0;
  if (addcard > 0) (void) lgladdcard (lgl, lgl->clause.start, b);
  lglclnstk (&lgl->clause);
  // COVER (cardcut == 2 && div == 2 && divsame);
}

static void lglrmcardexcept (LGL * lgl, int cardidx, int except) {
  Card * card = lgl->card;
  int * c, * p, lit;
  assert (0 <= cardidx && cardidx < lglcntstk (&card->cards));
  c = card->cards.start + cardidx + 1;
  LOGCLS (CARDLOGLEVEL, c, "removing cardinality constraint %d >=", c[-1]);
  for (p = c; (lit = *p); p++)
    if (lit != except)
      lglrmstk (card->occs + lit, cardidx);
}

static int lglcardocc (LGL * lgl, int a) {
  return lglcntstk (lgl->card->occs + a);
}

static int lglcmpcard (LGL * lgl, int a, int b) {
  int64_t s = lglcardocc (lgl, a) * (int64_t) lglcardocc (lgl, -a);
  int64_t t = lglcardocc (lgl, b) * (int64_t) lglcardocc (lgl, -b);
  if (s > t) return -1;
  if (s < t) return 1;
  return b - a;
}

#define LGLCMPCARD(A,B) lglcmpcard (lgl, *(A), *(B))

static void lglcardresched (LGL * lgl) {
  Stk * elim = &lgl->card->elim;
  int count = lglcntstk (elim);
  ADDSTEPS (card.steps, 4*count);
  SORT (int, elim->start, lglcntstk (elim), LGLCMPCARD);
  lgl->stats->card.resched++;
}

static void lglcardfmlit (LGL * lgl, int pivot) {
  Stk * poccs = lgl->card->occs + pivot, * noccs = lgl->card->occs - pivot;
  int pcnt = lglcntstk (poccs), ncnt = lglcntstk (noccs);
  int count = lgl->stats->card.count;
  const int * p, * q;
  assert (pivot > 0);
  assert (!lgl->card->eliminated[pivot]);
  if (!pcnt || !ncnt) goto DONE;
  if (pcnt > lglfactor (lgl, lgl->opts->cardocclim1.val, count)) goto DONE;
  if (ncnt > lglfactor (lgl, lgl->opts->cardocclim1.val, count)) goto DONE;
  if (pcnt > lglfactor (lgl, lgl->opts->cardocclim2.val, count) &&
      ncnt > lglfactor (lgl, lgl->opts->cardocclim2.val, count)) goto DONE;
  lgl->stats->card.eliminated++;
  lgl->card->eliminated[pivot] = 1;
  LOG (CARDLOGLEVEL,
    "fourier-motzkin pivot %d with %d positive and %d negative occurrences",
    pivot, pcnt, ncnt);
  for (p = poccs->start; !lgl->mt && p < poccs->top; p++)
    for (q = noccs->start; !lgl->mt && q < noccs->top; q++)
      lglcardfmstep (lgl, pivot, *p, *q);
DONE:
  for (p = poccs->start; !lgl->mt && p < poccs->top; p++) {
    lglrmcardexcept (lgl, *p, pivot);
    INCSTEPS (card.steps);
  }
  for (q = noccs->start; !lgl->mt && q < noccs->top; q++) {
    lglrmcardexcept (lgl, *q, -pivot);
    INCSTEPS (card.steps);
  }
  lglrelstk (lgl, poccs);
  lglrelstk (lgl, noccs);
  if (!(lgl->stats->card.eliminated % lgl->opts->cardreschedint.val))
    lglcardresched (lgl);
}

static void lglcardfm (LGL * lgl) {
  Stk * elim;
  lglcardresched (lgl);
  elim = &lgl->card->elim;
  while (!lgl->mt && 
         !lglmtstk (elim) &&
         !lglterminate (lgl) &&
         lgl->limits->card.steps >= INCSTEPS (card.steps))
    lglcardfmlit (lgl, lglpopstk (elim));
}

static int64_t lglsetcardlim (LGL * lgl) {
  int64_t limit, irrlim;
  int pen, szpen;
  limit = (lgl->opts->cardreleff.val*lglvisearch (lgl))/1000;
  if (limit < lgl->opts->cardmineff.val) limit = lgl->opts->cardmineff.val;
  if (lgl->opts->cardmaxeff.val >= 0 && limit > lgl->opts->cardmaxeff.val)
    limit = lgl->opts->cardmaxeff.val;
  limit >>= (pen = lgl->limits->card.pen + (szpen = lglszpen (lgl)));
  irrlim = (lgl->stats->irr.clauses.cur/4) >> szpen;
  if (lgl->opts->irrlim.val && limit < irrlim) {
    limit = irrlim;
    lglprt (lgl, 1,
      "[card-%d] limit %lld based on %d irredundant clauses penalty %d",
      lgl->stats->card.count,
      (LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
  } else
    lglprt (lgl, 1, "[card-%d] limit %lld penalty %d = %d + %d",
      lgl->stats->card.count, (LGLL) limit,
      pen, lgl->limits->card.pen, szpen);
  lgl->limits->card.steps = lgl->stats->card.steps + limit;
  return limit;
}

static void lglsetcardlimagain (LGL * lgl, int64_t limit) {
  lglprt (lgl, 1,
    "[card-%d] using previous limit %lld for elimination",
    lgl->stats->card.count, (LGLL) limit, lgl->stats->irr.clauses.cur);
  lgl->limits->card.steps = lgl->stats->card.steps + limit;
}

static int lglcard1extractlit (LGL * lgl, int lit) {
  const int ignused = lgl->opts->cardignused.val;
  int blit, tag, other, other2, i, j, cntother;
  int start, size, trivial, subsumed;
  const int * p, * w, * eow;
  Card * card;
  HTS * hts;
  lgl->stats->card.found.am1.last.cnt = 0;
  lgl->stats->card.found.am1.last.max = 0;
  if (lglterminate (lgl)) return 0;
  if (lgl->limits->card.steps < INCSTEPS (card.steps)) return 0;
  card = lgl->card;
  if (ignused && card->lit2used[lit]) return 1;
  start = lglcntstk (&card->atmost1);
  LOG (CARDLOGLEVEL + 1,
    "starting at-most-one clique[%d] for %d",
    start, lit);
  lglpushstk (lgl, &card->atmost1, lit);
  card->marked[lit] = 1;
  hts = lglhts (lgl, -lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  INCSTEPS (card.steps);
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    other = -(blit >> RMSHFT);
    if (ignused && card->lit2used[other]) continue;
    for (i = start + 1; i < lglcntstk (&card->atmost1); i++) {
      other2 = lglpeek (&card->atmost1, i);
      if (!lglhasbin (lgl, -other, -other2)) break;
    }
    if (i < lglcntstk (&card->atmost1)) continue;
    card->marked[other] = 1;
    assert (i == lglcntstk (&card->atmost1));
    lglpushstk (lgl, &card->atmost1, other);
    LOG (CARDLOGLEVEL + 1,
       "adding %d to at-most-one clique[%d] for %d", other, start, lit);
    cntother = lglhts (lgl, -other)->count;
    for (j = start + 1; j < i; j++) {
      int tmp = lglpeek (&card->atmost1, j);
      int cntmp = lglhts (lgl, -tmp)->count;
      if (cntmp > cntother) break;
    }
    if (j < i) {
      int k;
      for (k = i; k > j; k--)
	card->atmost1.start[k] = card->atmost1.start[k - 1];
      card->atmost1.start[j] = other;
    }
#ifndef NDEBUG
    for (j = start + 1; j + 1 < i; j++) 
      assert (lglhts (lgl, -lglpeek (&card->atmost1, j))->count <=
              lglhts (lgl, -lglpeek (&card->atmost1, j+1))->count);
#endif
  }
  size = lglcntstk (&card->atmost1) - start;
  trivial = (size <= 2);
  if (!ignused) {
    lglpushstk (lgl, &card->atmost1, 0);
    subsumed = lglcard1sub (lgl, card->atmost1.start + start);
    lglpopstk (&card->atmost1);
  } else subsumed = 0;
  for (p = card->atmost1.start + start; p < card->atmost1.top; p++) {
    other = *p;
    assert (card->marked[other]);
    card->marked[other] = 0;
    if (!trivial && !subsumed) card->lit2used[other] = 1;
  }
  if (trivial || subsumed) {
    LOG (CARDLOGLEVEL + 1,
      "resetting at-most-one clique[%d] for %d of trivial size %d",
      start, lit, size);
    lglrststk (&card->atmost1, start);
  } else {
#ifndef NLGLOG
    if (lgl->opts->log.val >= CARDLOGLEVEL) {
      lglogstart (lgl, CARDLOGLEVEL,
	"non trivial size %d at-most-one constraint 1 >= ", size);
      for (i = start; i < start + size; i++) {
	if (i > start) fputs (" + ", lgl->out);
	fprintf (lgl->out, "%d", lglpeek (&card->atmost1, i));
      }
      lglogend (lgl);
    }
#endif
    if (!ignused) {
      for (i = start; i < start + size; i++) {
	other = lglpeek (&card->atmost1, i);
	lglpushstk (lgl, &card->occs[other], start);
      }
    }
    lglpushstk (lgl, &card->atmost1, 0);
    lgl->stats->card.found.am1.total.sum += size;
    lgl->stats->card.found.am1.total.cnt++;
    lgl->stats->card.found.am1.last.cnt++;
    if (lgl->stats->card.found.am1.total.max < size)
      lgl->stats->card.found.am1.total.max = size;
    if (lgl->stats->card.found.am1.last.max < size)
      lgl->stats->card.found.am1.last.max = size;
  }
  return 1;
}

static void lglcardreloccs (LGL * lgl) {
  Card * card = lgl->card;
  int sign, idx, lit;
  assert (card), assert (!lgl->nvars || card->occs);
  for (sign = -1; sign <= 1; sign += 2)
    for (idx = 2; idx < lgl->nvars; idx++) {
      lit = sign * idx;
      lglrelstk (lgl, &card->occs[lit]);
    }
  card->occs -= lgl->nvars;
  DEL (card->occs, 2*lgl->nvars);
}

static int lglcard1extract (LGL * lgl) {
  struct { int cnt; int64_t sum; } before, after, delta;
  const int ignused = lgl->opts->cardignused.val;
  Card * card = lgl->card;

  lglpushstk (lgl, &card->atmost1, 0);

  NEW (card->lit2used, 2*lgl->nvars);
  card->lit2used += lgl->nvars;
  NEW (card->marked, 2*lgl->nvars);
  card->marked += lgl->nvars;
  if (!ignused) {
    NEW (card->occs, 2*lgl->nvars);
    card->occs += lgl->nvars;
  }

  before.cnt = lgl->stats->card.found.am1.total.cnt;
  before.sum = lgl->stats->card.found.am1.total.sum;

  lglrandlitrav (lgl, lglcard1extractlit);

  after.cnt = lgl->stats->card.found.am1.total.cnt;
  after.sum = lgl->stats->card.found.am1.total.sum;
  assert (after.cnt >= before.cnt);
  assert (after.sum >= before.sum);
  delta.cnt = after.cnt - before.cnt;
  delta.sum = after.sum - before.sum;

  card->lit2used -= lgl->nvars;
  DEL (card->lit2used, 2*lgl->nvars);
  card->marked -= lgl->nvars;
  DEL (card->marked, 2*lgl->nvars);
  if (!ignused) lglcardreloccs (lgl);

  if (delta.cnt)
    lglprt (lgl, 1, 
      "[card-%d] found %d at-most-one constraints of average size %.1f",
      lgl->stats->card.count, delta.cnt, lglavg (delta.sum, delta.cnt));
  else
    lglprt (lgl, 1,
      "[card-%d] no at-most-one constraint found",
      lgl->stats->card.count);

  return delta.cnt;
}

static int lglcard2extractlit (LGL * lgl, int lit) {
  int blit, tag, other, other2, other3, i, j, k, res = 1;
  const int ignused = lgl->opts->cardignused.val;
  int start, size, minlit;
  const int * p, * w, * eow;
  int * q;
  Card * card;
  HTS * hts;
  lgl->stats->card.found.am2.last.cnt = 0;
  lgl->stats->card.found.am2.last.max = 0;
  if (lglterminate (lgl)) return 0;
  if (lgl->limits->card.steps < INCSTEPS (card.steps)) return 0;
  card = lgl->card;
  if (ignused && card->lit2used[lit]) return 1;

  start = lglcntstk (&card->atmost2);
  LOG (CARDLOGLEVEL + 1, "starting at-most-two clique[%d] for %d", start, lit);
  assert (!card->lit2count[lit]);
  hts = lglhts (lgl, -lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  INCSTEPS (card.steps);
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != TRNCS) continue;
    other = -(blit >> RMSHFT);
    other2 = -*p;
    if (card->lit2count[-other] || card->lit2count[-other2]) continue;
    if (!card->lit2count[lit]++) lglpushstk (lgl, &card->atmost2, lit);
    if (!card->lit2count[other]++) lglpushstk (lgl, &card->atmost2, other);
    if (!card->lit2count[other2]++) lglpushstk (lgl, &card->atmost2, other2);
  }
  q = card->atmost2.start + start;
  for (p = q; p < card->atmost2.top; p++) {
    if (card->lit2count [other =*p] > 1) *q++ = other;
    else card->lit2count[other] = 0;
  }
  card->atmost2.top = q;
  size = lglcntstk (&card->atmost2) - start;
  if (size < 4) {
    LOG (CARDLOGLEVEL + 1,
      "less than 4 literals occuring 2 times in ternary clauses with %d",
       -lit);
FAILED:
    while (lglcntstk (&card->atmost2) > start) {
      int lit = lglpopstk (&card->atmost2);
      assert (card->lit2count[lit] > 0);
      card->lit2count[lit] = 0;
    }
    return res;
  }
  minlit = 0;
RESTART:
  if (!ignused) {
    int subsumed;
    lglpushstk (lgl, &card->atmost2, 0);
    subsumed = lglcard2sub (lgl, card->atmost2.start + start, &minlit);
    lglpopstk (&card->atmost2);
    if (subsumed) goto FAILED;
  }
  LOG (CARDLOGLEVEL + 1, "trying to connect %d literals", size-1);
  for (i = 0; i < size-2; i++) {
    other = -lglpeek (&card->atmost2, start + i);
    for (j = i+1; j < size-1; j++) {
      other2 = -lglpeek (&card->atmost2, start + j);
      for (k = j+1; k < size; k++) {
	if (lgl->limits->card.steps < INCSTEPS (card.steps)) {
	  LOG (CARDLOGLEVEL + 1, "cardinality extraction step limit hit");
	  res = 0;
	  goto FAILED;
	}
	other3 = -lglpeek (&card->atmost2, start + k);
	if (!lglhastrn (lgl, other, other2, other3)) {
	  LOG (CARDLOGLEVEL + 1,
	    "ternary clause %d %d %d missing", other, other2, other3);
	  assert (size >= 4);
	  if (size == 4) goto FAILED;
	  int l, tmp;
	  if (k > j + 1) l = k;
	  else {
	    int occ2 = card->lit2count[-other2];
	    int occ3 = card->lit2count[-other3];
	    if (occ2 > occ3) l = k;
	    else if (occ2 < occ3) l = j;
	    else {
	      occ2 = lglhts (lgl, other2)->count;
	      occ3 = lglhts (lgl, other3)->count;
	      if (occ2 > occ3) l = k;
	      else if (occ2 < occ3) l = j;
	      else l = (lglrand (lgl) & 1) ? j : k;
	    }
	  }
	  tmp = lglpeek (&card->atmost2, start + l);
	  assert (abs (tmp) != abs (lit));
	  assert (card->lit2count[tmp] > 0);
	  card->lit2count[tmp] = 0;
	  while (l + 1 < size) {
	    tmp = lglpeek (&card->atmost2, start + l + 1);
	    assert (abs (tmp) != abs (lit));
	    lglpoke (&card->atmost2, start + l++, tmp);
	  }
	  assert (l == size - 1);
	  card->atmost2.top--;
	  size--;
	  assert (size >= 4);
	  assert (card->atmost2.start + start + size == card->atmost2.top);
	  goto RESTART;
	}
      }
    }
  }
#ifndef NLGLOG
  if (lgl->opts->log.val >= CARDLOGLEVEL) {
    lglogstart (lgl, CARDLOGLEVEL,
      "non trivial size %d at-most-two constraint 2 >= ", size);
    for (i = start; i < start + size; i++) {
      if (i > start) fputs (" + ", lgl->out);
      fprintf (lgl->out, "%d", lglpeek (&card->atmost2, i));
    }
    lglogend (lgl);
  }
#endif
  for (i = start; i < start + size; i++) {
    other = lglpeek (&card->atmost2, i);
    card->lit2count[other] = 0;
    card->lit2used[other] = 1;
    if (!ignused) lglpushstk (lgl, &card->occs[other], start);
  }
  lglpushstk (lgl, &card->atmost2, 0);
  lgl->stats->card.found.am2.total.sum += size;
  lgl->stats->card.found.am2.total.cnt++;
  lgl->stats->card.found.am2.last.cnt++;
  if (lgl->stats->card.found.am2.total.max < size)
    lgl->stats->card.found.am2.total.max = size;
  if (lgl->stats->card.found.am2.last.max < size)
    lgl->stats->card.found.am2.last.max = size;
  return res;
}

static int lglcard2extract (LGL * lgl) {
  struct { int cnt; int64_t sum; } before, after, delta;
  const int ignused = lgl->opts->cardignused.val;
  Card * card = lgl->card;

  lglpushstk (lgl, &card->atmost2, 0);
  NEW (card->lit2used, 2*lgl->nvars);
  card->lit2used += lgl->nvars;
  NEW (card->lit2count, 2*lgl->nvars);
  card->lit2count += lgl->nvars;
  if (!ignused) {
    NEW (card->occs, 2*lgl->nvars);
    card->occs += lgl->nvars;
  }

  before.cnt = lgl->stats->card.found.am2.total.cnt;
  before.sum = lgl->stats->card.found.am2.total.sum;

  lglrandlitrav (lgl, lglcard2extractlit);

  after.cnt = lgl->stats->card.found.am2.total.cnt;
  after.sum = lgl->stats->card.found.am2.total.sum;
  assert (after.cnt >= before.cnt);
  assert (after.sum >= before.sum);
  delta.cnt = after.cnt - before.cnt;
  delta.sum = after.sum - before.sum;

  card->lit2used -= lgl->nvars;
  DEL (card->lit2used, 2*lgl->nvars);
  card->lit2count -= lgl->nvars;
  DEL (card->lit2count, 2*lgl->nvars);
  if (!ignused) lglcardreloccs (lgl);

  if (delta.cnt)
    lglprt (lgl, 1, 
      "[card-%d] found %d at-most-two constraints of average size %.1f",
      lgl->stats->card.count, delta.cnt, lglavg (delta.sum, delta.cnt));
  else
    lglprt (lgl, 1,
      "[card-%d] no at-most-two constraint found",
      lgl->stats->card.count);

  return delta.cnt;
}

static int lglcarduseclswithlit (LGL * lgl, int lit) {
  int pos = !lglmtstk (lgl->card->occs + lit);
  int neg = !lglmtstk (lgl->card->occs - lit);
  int level = lgl->opts->carduse.val;
  switch (level) {
    case 0: return 0;
    case 1: return pos && !neg;
    case 2: return pos;
    default: assert (level == 3); return pos || neg;
  }
}

static int lglcardelim (LGL * lgl, int count) {
  int blit, tag, other, other2, bound, used;
  int idx, sign, lit, start, len, res, glue;
  const int * p, * w, * eow, * c, * q;
  Card * card = lgl->card;
  int cardmaxlen;
  int clause[4];
  HTS * hts;
  Stk * s;

  NEW (card->occs, 2*lgl->nvars);
  NEW (card->eliminated, lgl->nvars);
  NEW (card->count, lgl->nvars);
  card->occs += lgl->nvars;
  used = 0;
  cardmaxlen =
    lglfactor (lgl, lgl->stats->card.count, lgl->opts->cardmaxlen.val);
  for (start = 1; start < lglcntstk (&card->atmost1); start++) {
    for (len = 0; lglpeek (&card->atmost1, start + len); len++)
      ;
    if (len >= lgl->opts->cardminlen.val &&
	len <= cardmaxlen &&
        lgladdcard (lgl, card->atmost1.start + start, 1)) {
      lgl->stats->card.used.am1.sum += len;
      lgl->stats->card.used.am1.cnt++;
      used++;
    }
    start += len;
  }
  for (start = 1; start < lglcntstk (&card->atmost2); start++) {
    for (len = 0; lglpeek (&card->atmost2, start + len); len++)
      ;
    if (len >= lgl->opts->cardminlen.val &&
	len <= cardmaxlen &&
        lgladdcard (lgl, card->atmost2.start + start, 2)) {
      lgl->stats->card.used.am2.sum += len;
      lgl->stats->card.used.am2.cnt++;
      used++;
    }
    start += len;
  }
  if (used) {
    lglprt (lgl, 1,
      "[card-%d] %d out of %d constraints (%.0f%%) meet size limits",
      lgl->stats->card.count, used, count, lglpcnt (used, count));
  } else {
    lglprt (lgl, 1,
      "[card-%d] no constraint out of %d meets size limits",
      lgl->stats->card.count, count);
    goto SKIP;
  }
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (lglmtstk (card->occs + idx) &&
	lglmtstk (card->occs - idx)) continue;
    LOG (CARDLOGLEVEL, "variable %d scheduled for elimination", idx);
    lglpushstk (lgl, &card->elim, idx);
  }
  if (!lgl->opts->carduse.val) goto DO_NOT_USE_CLAUSES;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (lglterminate (lgl) ||
	lgl->limits->card.steps < INCSTEPS (card.steps)) goto SKIP;
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      if (!lglcarduseclswithlit (lgl, lit)) continue;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == BINCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  clause[0] = -lit, clause[1] = -other, clause[2] = 0;
	  (void) lgladdcard (lgl, clause, 1);
	} else if (tag == TRNCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  clause[0] = -lit, clause[1] = -other,
	  clause[2] = -other2, clause[3] = 0;
	  (void) lgladdcard (lgl, clause, 2);
	} else assert (tag == LRGCS);
      }
    }
  }
  for (glue = -1; glue <= lgl->opts->cardglue.val; glue++) {
    s = (glue < 0) ? &lgl->irr : lgl->red + glue;
    for (c = s->start; c < s->top; c = p + 1) {
      if (*(p = c) >= NOTALIT) continue;
      for (p = c; *p; p++)
	;
      for (q = c; (lit = *q); q++)
	if (lglcarduseclswithlit (lgl, lit)) break;
      if (!lit) continue;
      len = p - c;
      if (len > cardmaxlen) continue;
      assert (len >= 4);
      bound = len - 1;
      assert (lglmtstk (&lgl->clause));
      for (q = c; (lit = *q); q++)
	lglpushstk (lgl, &lgl->clause, -lit);
      lglpushstk (lgl, &lgl->clause, 0);
      (void) lgladdcard (lgl, lgl->clause.start, bound);
      lglclnstk (&lgl->clause);
      if (lglterminate (lgl) ||
	  lgl->limits->card.steps < INCSTEPS (card.steps)) goto SKIP;
    }
  }
DO_NOT_USE_CLAUSES:
  lglcardfm (lgl);
SKIP:
  lglcardreloccs (lgl);
  DEL (card->count, lgl->nvars);
  lglrelstk (lgl, &card->cards);
  lglrelstk (lgl, &card->elim);
  DEL (card->eliminated, lgl->nvars);
  if (lgl->mt)
    lglprt (lgl, 1,
      "[card-%d] produced empty clause",
      lgl->stats->card.count);
  else if (!lglmtstk (&card->units)) {
    lglprt (lgl, 1,
       "[card-%d] found %d units",
       lgl->stats->card.count, lglcntstk (&card->units));
    while (!lgl->mt && !lglmtstk (&card->units)) {
      lit = lglpopstk (&card->units);
      if (lglval (lgl, lit) > 0) continue;
      if (lglval (lgl, lit) < 0) {
	lglprt (lgl, 1,
	  "[card-%d] found inconsistent unit",
	  lgl->stats->card.count);
	lglmt (lgl);
      } else {
	lglunit (lgl, lit);
	if (!lglbcp (lgl)) {
	  lglprt (lgl, 1,
	    "[card-%d] inconsistent unit propagation",
	    lgl->stats->card.count);
	  assert (!lgl->mt);
	  lglmt (lgl);
	}
      }
    }
  }
  res = lglcntstk (&card->units);
  lglrelstk (lgl, &card->units);
  if (!lgl->mt) {
    if (res)
      lglprt (lgl, 1, 
	"[card-%d] found %d units", lgl->stats->card.count, res);
    else
      lglprt (lgl, 1, "[card-%d] no units found", lgl->stats->card.count);

    if (!lglmtstk (&card->expam1)) {
      int generated = 0, exported = 0, genused = 0;
      for (c = card->expam1.start; c < card->expam1.top; c = p + 1) {
	int a, usefull = 0;
	generated++;
	for (p = c; (a = *p); p++) if (lglval (lgl, a)) break;
	if (a) {
	  while (*++p)
	    ;
	  continue;
	}
	for (p = c; (a = -*p); p++) {
	  int b;
	  for (q = p + 1; (b = -*q); q++)
	    if (!lglhasbin (lgl, a, b)) {
	      LOG (CARDLOGLEVEL,
	        "exporting at-most-one constraint binary clause %d %d",
		a, b);
	      assert (lglmtstk (&lgl->clause));
	      lglpushstk (lgl, &lgl->clause, a);
	      lglpushstk (lgl, &lgl->clause, b);
	      lglpushstk (lgl, &lgl->clause, 0);
	      lgladdcls (lgl, REDCS, 0, 1);
	      lglclnstk (&lgl->clause);
	      lgl->stats->card.expam1++;
	      exported++;
	      usefull = 1;
	    }
	}
	if (usefull) genused++;
      }
      lglprt (lgl, 1,
        "[card-%d] generated %d at-most-one constraints, %d used %.0f%%",
        lgl->stats->card.count,
	generated, genused, lglpcnt (genused, generated));
      lglprt (lgl, 1,
	"[card-%d] exported %d binary clauses, %.1f per/constraint",
        lgl->stats->card.count, exported, lglavg (exported, genused));
    } else
      lglprt (lgl, 1, 
        "[card-%d] no at-most-one constraints generated",
        lgl->stats->card.count);
  }
  lglrelstk (lgl, &card->expam1);
  return res;
}

static int lglcard (LGL * lgl) {
  int success, count;
  int64_t limit;
  assert (!lgl->mt);
  lglstart (lgl, &lgl->times->card);
  lgl->stats->card.count++;
  if (lgl->level) lglbacktrack (lgl, 0);
  limit = lglsetcardlim (lgl);
  assert (!lgl->card);
  NEW (lgl->card, 1);
  count = lglcard1extract (lgl) + lglcard2extract (lgl);
  if (!lglterminate (lgl) && count) {
    lglsetcardlimagain (lgl, limit);
    success = lglcardelim (lgl, count);
  } else success = 0;
  lglrelstk (lgl, &lgl->card->atmost1);
  lglrelstk (lgl, &lgl->card->atmost2);
  DEL (lgl->card, 1);
  LGLUPDPEN (card, success);
  lglstop (lgl);
  return !lgl->mt;
}

/*------------------------------------------------------------------------*/

static int lglbcaoccmin (LGL * lgl, int lit) {
  int * p, * w, * eow;
  int res, blit, red, tag;
  HTS * hts;
  hts = lglhts (lgl, lit);
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  res = 0;
  for (p = w; res <= 3 && p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag == LRGCS) continue;
    if (!red) res++;
  }
  return res;
}

static int lglbcaskiplit (LGL * lgl, int lit) {
  int pocc, nocc;
  if (lgl->opts->bca.val >= 2) return 0;
  pocc = lglbcaoccmin (lgl, lit);
  if (pocc <= 1) return 1;
  nocc = lglbcaoccmin (lgl, -lit);
  if (nocc <= 1) return 1;
  return pocc == 2 && nocc == 2;
}

static void lglbcalitaux (LGL * lgl, int lit) {
  int first, blit, tag, red, lidx, other, tmp, found, other2, found2, * r;
  const int * w, * p, * eow, * c, * q;
  Stk * covered = &lgl->bca->covered;
  int round;
  HTS * hts;
  assert (lglisfree (lgl, lit));
  assert (lgl->opts->bca.val);
  assert (!(lglavar (lgl, lit)->inred & (1 << (lit < 0))));
  hts = lglhts (lgl, lit);
  if (!hts->count) return;
  if (lglbcaskiplit (lgl, lit)) { lgl->stats->bca.skipped++; return; }
  assert (lglmtstk (covered));
  first = 1;
  w = lglhts2wchs (lgl, hts);
  eow = w + hts->count;
  for (round = 0; round < 2; round++) {
    for (p = w; (first || !lglmtstk (covered)) && p < eow; p++) {
      blit = *p;
      tag = blit & MASKCS;
      red = blit & REDCS;
      if (tag == TRNCS || tag == LRGCS) p++;
      assert (!red || tag != LRGCS);
      if (tag == LRGCS) continue;
      if (round != (tag == OCCS)) continue;
      INCSTEPS (bca.steps);
      if (tag == BINCS) {
	assert (!round);
	other = blit >> RMSHFT;
	if (lglval (lgl, other) > 0) continue;
	assert (!lglval (lgl, other));
	found = first;
	while (!lglmtstk (covered))
	  if (other == lglpopstk (covered)) found = 1;
	if (found) lglpushstk (lgl, covered, other);
      } else if (tag == TRNCS) {
	assert (!round);
	other = blit >> RMSHFT;
	if (lglval (lgl, other) > 0) continue;
	other2 = *p;
	if (lglval (lgl, other2) > 0) continue;
	found = found2 = first;
	while (!lglmtstk (covered))
	  if (other == (tmp = lglpopstk (covered))) found = 1;
	  else if (tmp == other2) found2 = 1;
	if (found && !lglval (lgl, other)) lglpushstk (lgl, covered, other);
	if (found2 && !lglval (lgl, other2)) lglpushstk (lgl, covered, other2);
      } else {
	assert (!red);
	assert (round);
	assert (tag == OCCS);
	lidx = blit >> RMSHFT;
	c = lglidx2lits (lgl, red, lidx);
	INCSTEPS (bca.steps);
	for (q = c; (other = *q); q++)
	  if (other != lit && lglval (lgl, other) > 0) break;
	if (other) continue;
	if (first) {
	  for (q = c; (other = *q); q++)
	    if (other != lit && !lglval (lgl, other))
	      lglpushstk (lgl, covered, other);
	} else {
	  for (q = covered->start; q < covered->top; q++)
	    assert (!lglsignedmarked (lgl, *q)), lglsignedmark (lgl, *q);
	  for (q = c; (other = *q); q++)
	    if (other != lit && lglsignedmarked (lgl, other))
	      assert (!lglval (lgl, other)), lglsignedunmark (lgl, other);
	  r = covered->start;
	  for (q = r; q < covered->top; q++)
	    if (lglsignedmarked (lgl, (other = *q)))
	      lglsignedunmark (lgl, other);
	    else *r++ = other;
	  covered->top = r;
	}
      }
      first = 0;
    }
  }
}

static int lglbcalit (LGL * lgl, int lit) {
  unsigned bit;
  AVar * av;
  int other;
  if (lgl->limits->bca.steps < lgl->stats->bca.steps) return 0;
  if (lgl->limits->bca.added < lgl->stats->bca.added) return 0;
  if (lglterminate (lgl)) return 0;
  if (lglifrozen (lgl, lit)) return 1;
  if (!lglisfree (lgl, lit)) return 1;
  av = lglavar (lgl, lit);
  bit = (1 << (lit < 0));
  if (av->inred & bit) return 1;
  lglbcalitaux (lgl, lit);
  while (!lglmtstk (&lgl->bca->covered)) {
    INCSTEPS (bca.steps);
    other = lglpopstk (&lgl->bca->covered);
    if (lglhasbin (lgl, -lit, -other)) continue;
    LOG (2, "adding binary blocked clause %d %d", -lit, -other);
    assert (lglmtstk (&lgl->clause));
    lglpushstk (lgl, &lgl->clause, -lit);
    lglpushstk (lgl, &lgl->clause, -other);
    lglpushstk (lgl, &lgl->clause, 0);
    lgladdcls (lgl, REDCS, 0, 1);
    lglclnstk (&lgl->clause);
    lgl->stats->bca.added++;
  }
  return 1;
}

static void lglupdbcadel (LGL * lgl, int success) {
  if (success && lgl->limits->bca.del.cur)
    lgl->limits->bca.del.cur /= 2;
  if (!success && lgl->limits->bca.del.cur < lgl->opts->delmax.val)
    lgl->limits->bca.del.cur++;
  lgl->limits->bca.del.rem = lgl->limits->bca.del.cur;
}

static void lglbca (LGL * lgl) {
  int oldadded = lgl->stats->bca.added, added, limadded;
  int idx, glue, other, inred, usable, scale;
  const int * c, * p;
  int64_t oldsteps, lim64;
  unsigned bit;
  AVar * av;

  lglstart (lgl, &lgl->times->bca);

  NEW (lgl->bca, 1);

  lgl->stats->bca.count++;
  oldsteps = lgl->stats->bca.steps;
  lgl->limits->bca.steps = oldsteps + lgl->opts->bcamaxeff.val;

  limadded = lgl->stats->irr.clauses.cur;
  scale = lgl->opts->bcaddlimldscale.val;
  if (scale < 0) limadded >>= -scale;
  else if ((INT_MAX >> scale) < limadded) limadded = INT_MAX;
  else limadded <<=scale;
  lim64 = lgl->stats->bca.added/2;
  lim64 += limadded/2 + 500;
  if (lim64 > (int64_t) INT_MAX) lim64 = INT_MAX;
  lgl->limits->bca.added = lim64;

  lglprt (lgl, 1,
    "[bca-%d] limit of %d steps and %d added (scaled %d)",
    lgl->stats->bca.count, lgl->opts->bcamaxeff.val,
    lgl->limits->bca.added, scale);

  assert (!lgl->bcaing);
  lgl->bcaing = 1;

  if (lgl->level > 0) lglbacktrack (lgl, 0);
  lglgc (lgl);
  assert (lgl->frozen);

  for (idx = 2; idx < lgl->nvars; idx++) lglavar (lgl, idx)->inred = 0;
  inred = 0;
  for (glue = 0; glue <= MAXGLUE; glue++) {
    Stk * s = lgl->red + glue;
    for (c = s->start; c < s->top; c = p + 1) {
      p = c;
      if (*p >= NOTALIT) continue;
      INCSTEPS (bca.steps);
      while ((other = *p)) {
	p++;
	bit = (1 << (other < 0));
	av = lglavar (lgl, other);
	if (av->inred & bit) continue;
	av->inred |= bit;
	inred++;
      }
    }
  }
  lglprt (lgl, 2, 
    "[bca-%d] %d out of %d literals in large redundant clauses %.0f%%",
    lgl->stats->bca.count,
    inred, 2*(lgl->nvars-1), lglpcnt (inred, 2*(lgl->nvars-1)));

  usable = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (lglifrozen (lgl, idx)) continue;
    if (!lglisfree (lgl, idx)) continue;
    av = lglavar (lgl, idx);
    for (bit = 1; bit <= 2; bit++) if (!(av->inred & bit)) usable++;
  }
  lglprt (lgl, 1, 
    "[bca-%d] %d out of %d literals actually usable %.0f%%",
    lgl->stats->bca.count,
    usable, 2*(lgl->nvars-1), lglpcnt (usable, 2*(lgl->nvars-1)));

  if (usable < lgl->opts->bcaminuse.val) {
    lglprt (lgl, 1, "[bca-%d] not enough literals usable",
            lgl->stats->bca.count);
    goto DONE;
  }

  lgldense (lgl, 0);
  lglrandlitrav (lgl, lglbcalit);
  lglsparse (lgl);
  lglgc (lgl);

DONE:
  added = lgl->stats->bca.added - oldadded;
  lglprt (lgl, 1, "[bca-%d] added %d blocked clauses in %lld steps",
          lgl->stats->bca.count, added, 
	  (LGLL) lgl->stats->bca.steps - oldsteps);
  assert (lgl->bcaing);
  lgl->bcaing = 0;
  lglupdbcadel (lgl, added);
  lglrelstk (lgl, &lgl->bca->covered);
  DEL (lgl->bca, 1);
  lglstop (lgl);
}

/*------------------------------------------------------------------------*/

static int lgltreducing (LGL * lgl) {
  if (lgldelaying (lgl, "transred", &lgl->limits->trd.del.rem)) return 0;
  if (lglwaiting (lgl, "transred", lgl->opts->transredwait.val)) return 0;
  return lgl->opts->transred.val;
}

static int lglunhiding (LGL * lgl) { 
  if (lgldelaying (lgl, "unhide", &lgl->limits->unhd.del.rem)) return 0;
  if (lglwaiting (lgl, "unhide", lgl->opts->unhidewait.val)) return 0;
  return lgl->opts->unhide.val;
}

static int lgldecomposing (LGL * lgl) { return lgl->opts->decompose.val; }

static int lglblocking (LGL * lgl) {
  if (!lgl->opts->block.val) return 0;
  if (lgl->allfrozen) return 0;
  if (lgldelaying (lgl, "block", &lgl->limits->blk.del.rem)) return 0;
  if (lgl->opts->blockwait.val && lgl->wait &&
      (!lgl->opts->elim.val || !lgl->elmrtc)) {
    lglprt (lgl, 2, 
      "[block-waiting] for bounded variable elimination to be completed");
    return 0;
  }
  if (!lglsmallirr (lgl)) return 0;
  if (lgl->nvars <= 2) return 0;
  if (lgl->mt) return 0;
  if (lgl->blkrem) return 1;
  return lgl->stats->irrprgss > lgl->limits->blk.irrprgss;
}

static int lgleliminating (LGL * lgl) {
  if (!lgl->opts->elim.val) return 0;
  if (lgl->allfrozen) return 0;
  if (lgldelaying (lgl, "elim", &lgl->limits->elm.del.rem)) return 0;
  if (!lglsmallirr (lgl)) return 0;
  if (lgl->nvars <= 2) return 0;
  if (lgl->mt) return 0;
  if (lgl->elmrem) return 1;
  return lgl->stats->irrprgss > lgl->limits->elm.irrprgss;
}

static int lglbcaing (LGL * lgl) {
  if (!lgl->opts->bca.val) return 0;
  if (lgl->allfrozen) return 0;
  if (lgldelaying (lgl, "bca", &lgl->limits->bca.del.rem)) return 0;
  if (lglwaiting (lgl, "bca", lgl->opts->bcawait.val)) return 0;
  if (!lglsmallirr (lgl)) return 0;
  return 1;
}

static int lglreducing (LGL * lgl) {
  int reducable;
  if (!lgl->opts->reduce.val) return 0;
  reducable = lgl->stats->red.lrg;
  assert (reducable >= lgl->lrgluereasons);
  reducable -= lgl->lrgluereasons;
  assert (reducable >= lgl->stats->lir[0].clauses);
  reducable -= lgl->stats->lir[0].clauses;
  return reducable >= lgl->limits->reduce.redlarge;
}

static int lgldefragmenting (LGL * lgl) {
  int relfree;
  if (lgl->stats->pshwchs < lgl->limits->dfg) return 0;
  if (!lgl->nvars) return 0;
  relfree = (100 * lgl->wchs->free + 99) / lgl->nvars;
  return relfree >= lgl->opts->defragfree.val;
}

static int lglforcerestart (LGL * lgl) {
  const int64_t  percent = lgl->opts->restartforcelim.val;
  int64_t actual, smoothed, limit;
  int forcing;
  assert (lgl->opts->restartcheckforced.val);
  assert (percent);
  switch (lgl->opts->restartforcemode.val) {
    default:
    case 0:
      actual = lgl->stats->glue.fast.val;
      smoothed = lgl->stats->avglue.val;
      break;
    case 1:
      actual = lgl->stats->glue.fast.val;
      smoothed = lgl->stats->glue.slow.val;
      break;
    case 2:
      actual = lgl->stats->glue.diff.actual;
      smoothed = lgl->stats->glue.diff.smoothed.val;
      break;
  }
  assert (lglvalidint64 (smoothed));
  limit = (smoothed < 0 ? -smoothed : smoothed);
  assert (limit >= 0);
  if (!lglvalidint64 (limit)) return 0;
  limit /= 100;
  if (INT64MAX/percent < limit) return 0;
  limit *= percent;
  forcing = (limit < actual);
  LOG (2,
    "%s glue MACD %g * %.2f = %g %s %g at %lld conflicts",
    (forcing ? "forcing" : "not forcing"),
    smoothed/(double)(1ll<<32),
    lgl->opts->restartforcelim.val/100.0,
    limit/(double)(1ll<<32),
    forcing ? "<" : ">=",
    actual/(double)(1ll<<32),
    (LGLL) lgl->stats->confs);
  return forcing;
}

static int lgldelayrestart (LGL * lgl) {
  const int64_t   actual = ((int64_t)lgl->level) << 32;
  const int64_t smoothed = lgl->stats->jlevel.slow.val;
  const int64_t  percent = lgl->opts->restartdelaylim.val;
  int64_t limit;
  int delaying;
  assert (lgl->opts->restartdelay.val);
  assert (percent);
  assert (lglvalidint64 (smoothed));
  limit = (smoothed < 0 ? -smoothed : smoothed);
  assert (limit >= 0);
  if (!lglvalidint64 (limit)) return 0;
  limit /= 100;
  if (INT64MAX/percent < limit) return 0;
  limit *= percent;
  delaying = (limit > actual);
  LOG (2,
    "%s restart MACD %g * %.2f = %g %s %g at %lld conflicts",
    (delaying ? "delaying" : "not delaying"),
    smoothed/(double)(1ll<<32),
    lgl->opts->restartdelaylim.val/100.0,
    limit/(double)(1ll<<32),
    delaying ? ">" : "<=",
    actual/(double)(1ll<<32),
    (LGLL) lgl->stats->confs);
  return delaying;
}

static int lglrestarting (LGL * lgl) {
  int assumptions;
  if (lgl->stats->confs < lgl->limits->restart.confs) return 0;
  if (!lgl->opts->restart.val) return 0;
  if (!lgl->level) return 0;
  if ((assumptions = lglcntstk (&lgl->assume))) {
    if (lgl->assumed < assumptions) return 0;
    assert (lgl->alevel <= lgl->level);
    if (lgl->alevel == lgl->level) return 0;
  }
  lgl->stats->restarts.checked++;
  lgl->limits->restart.confs = lgl->stats->confs + 1;
  if (lgl->opts->restartfixed.val) return 1;
  if (lgl->opts->agility.val &&
      ((100*lgl->stats->agility) >> 32) > lgl->opts->agilitylim.val) {
    lgl->stats->restarts.agile++;
NORESTART:
    lgl->stats->restarts.skipped++;
    lglrep (lgl, 3, 'L');
    return 0;
  }
  if (lgl->opts->restartdelay.val && lgldelayrestart (lgl)) {
    lgl->stats->restarts.delayed++;
    goto NORESTART;
  }
  if (lgl->opts->restartblock.val == 2 && lglblockrestart (lgl)) {
    lgl->limits->restart.confs = lgl->stats->confs + lgl->opts->restartint.val;
    lgl->stats->restarts.blocked++;
    goto NORESTART;
  }
  if (lgl->opts->restartcheckforced.val && !lglforcerestart (lgl)) {
    lgl->stats->restarts.notforced++;
    goto NORESTART;
  }
  lgl->stats->restarts.forced++;
#ifndef NLGLFILES
  {
    static FILE * restartfile = 0;
    if (!restartfile) restartfile = fopen ("/tmp/restarts", "w");
    fprintf (restartfile, "%lld\n", (LGLL) lgl->stats->confs);
    fflush (restartfile);
  }
#endif
  return 1;
}

static int lglquatresolving (LGL * lgl) { 
  if (lgldelaying (lgl, "quatres", &lgl->limits->quatres.del.rem)) return 0;
  if (lglwaiting (lgl, "quatres", lgl->opts->quatreswait.val)) return 0;
  return lgl->opts->quatres.val;
}

static int lglternresolving (LGL * lgl) { 
  if (lgldelaying (lgl, "ternres", &lgl->limits->ternres.del.rem)) return 0;
  if (lglwaiting (lgl, "ternres", lgl->opts->ternreswait.val)) return 0;
  return lgl->opts->ternres.val;
}

static int lglgaussing (LGL * lgl) { 
  if (lgldelaying (lgl, "gauss", &lgl->limits->gauss.del.rem)) return 0;
  if (lglwaiting (lgl, "gauss", lgl->opts->gausswait.val)) return 0;
  if (!lglsmallirr (lgl)) return 0;
  return lgl->opts->gauss.val;
}

static int lglprobing (LGL * lgl) {
  if (!lgl->opts->probe.val) return 0;
  if (lgl->opts->prbasic.val) return 1;
  if (!lglsmallirr (lgl)) return 0;
  if (lgl->opts->prbsimple.val) return 1;
  if (lgl->opts->treelook.val) return 1;
  return 0;
}

static int lglcarding (LGL * lgl) {
  if (!lgl->opts->card.val) return 0;
  if (lgldelaying (lgl, "card", &lgl->limits->card.del.rem)) return 0;
  if (lglwaiting (lgl, "card", lgl->opts->cardwait.val)) return 0;
  return 1;
}

static int lglcceing (LGL * lgl) {
  if (!lgl->opts->cce.val) return 0;
  if (lgl->allfrozen) return 0;
  if (lgldelaying (lgl, "cce", &lgl->limits->cce.del.rem)) return 0;
  if (lglwaiting (lgl, "cce", lgl->opts->ccewait.val)) return 0;
  if (!lglsmallirr (lgl)) return 0;
  return 1;
}

/*------------------------------------------------------------------------*/

static void lglupdlocslim (LGL * lgl, int updconflimtoo) {
  int rem = lglrem (lgl), varslimit, vardelta;
  vardelta = (rem * lgl->opts->locsvared.val + 999)/1000;
  if (vardelta > rem) vardelta = rem;
  varslimit = rem - vardelta;
  lgl->limits->locs.vars = varslimit;
  lglprt (lgl, 1 + !lgl->opts->locs.val,
    "[locs-lim] next local search variable limit %d = %d - %d",
    varslimit, rem, vardelta);
  if (!updconflimtoo) return;
  lgl->limits->locs.inc += lgl->opts->locscint.val;
  assert (lgl->limits->locs.confs <= LLMAX - lgl->limits->locs.inc);
  lgl->limits->locs.confs = lgl->stats->confs + lgl->limits->locs.inc;
  lglprt (lgl, 1 + !lgl->opts->locs.val,
    "[locs-lim] next local search conflict limit increased by %d to %lld",
    lgl->limits->locs.inc, lgl->limits->locs.confs);
}

static int lglocsing (LGL * lgl) {
#ifndef NLGLYALSAT
  int rem;
  if (!lgl->opts->locs.val) return 0;
  if (lgl->limits->locs.confs > lgl->stats->confs) return 0;
  if (lgl->stats->irr.clauses.cur > lgl->opts->locsclim.val) {
    lglprt (lgl, 2, "[locs] skipped due to too many clauses");
    return 0;
  }
  rem = lglrem (lgl);
  if (rem < lgl->limits->locs.vars) {
    lglprt (lgl, 2,
      "[locs-limit] local search skipped (remaining %d < limit %d)",
      rem, lgl->limits->locs.vars);
    lglupdlocslim (lgl, 1);
    return 0;
  }
  if (lglwaiting (lgl, "locs", lgl->opts->locswait.val)) return 0;
  if (lgl->opts->locs.val < 0) return 1;
  return (lgl->stats->locs.count < lgl->opts->locs.val);
#else
  (void) lgl;
  return 0;
#endif
}

#ifndef NLGLYALSAT

static void lglocscopy (LGL * lgl, Yals * yals) {
  int idx, sign, lit, blit, tag, red, other, other2;
  int count, redcount, units, tmp;
  const int * p, * w, * eow, * c;
  HTS * hts;
  Stk * s;
  assert (!lgl->level);
  if (!lgl->mt && !lglbcp (lgl)) lglmt (lgl);
  if (!lgl->mt) lglgc (lgl);
  if (lgl->mt) return;
  count = redcount = units = 0;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      assert (!lglval (lgl, lit));
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (red && tag == BINCS && lgl->opts->locsred.val < 2) continue;
	if (red && tag == TRNCS && lgl->opts->locsred.val < 3) continue;
	if (tag != BINCS && tag != TRNCS) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	assert (!lglval (lgl, other));
	if (tag == TRNCS) {
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  assert (!lglval (lgl, other2));
	} else other2 = 0;
	yals_add (yals, lit);
	yals_add (yals, other);
	if (other2) yals_add (yals, other2);
	yals_add (yals, 0);
	if (red) redcount++;
	count++;
      }
    }
  for (idx = 2; idx < lgl->nvars; idx++) {
    tmp = lglifixed (lgl, idx);
    if (!tmp) continue;
    lit = (tmp < 0) ? -idx : idx;
    yals_add (yals, lit);
    yals_add (yals, 0);
    units++;
  }
  for (red = -1; red < MAXGLUE; red++) {
    s = red < 0 ? &lgl->irr : lgl->red + red;
    if (red >= 0 && lgl->opts->locsred.val < 4) break;
    for (c = s->start; c < s->top; c = p + 1) {
      p = c;
      if (*p >= NOTALIT) continue;
      while ((other = *p)) {
	assert (!lglval (lgl, other));
	yals_add (yals, other);
	p++;
      }
      yals_add (yals, 0);
      if (red >= 0) redcount++;
      count++;
    }
  }

  lglprt (lgl, 1,
    "[locs-%d] copied %d irredundant clauses",
    lgl->stats->locs.count, count - redcount);
  if (redcount)
    lglprt (lgl, 1,
      "[locs-%d] copied %d redundant clauses",
      lgl->stats->locs.count, redcount);
  if (units)
    lglprt (lgl, 1,
      "[locs-%d] copied %d units",
      lgl->stats->locs.count, units);

  for (count = 0; count < lglcntstk (&lgl->assume); count++) {
    lit = lglpeek (&lgl->assume, count);
    if (abs (lit) <= 0) continue;
    yals_add (yals, lit);
    yals_add (yals, 0);
  }
  if (count)
    lglprt (lgl, 1,
      "[locs-%d] copied %d assumptions as %d unit clauses",
      lgl->stats->locs.count, count, count);
  else
    lglprt (lgl, 2,
      "[locs-%d] no assumptions copied",
      lgl->stats->locs.count);
}

static int64_t lglsetlocslim (LGL * lgl) {
  int pen, boost;
  int64_t limit;
  if (lgl->opts->locsrtc.val) {
    limit = LLMAX;
    lglprt (lgl, 1,
      "[locs-%d] really no limit (run to completion)",
      lgl->stats->locs.count);
  } else {
    limit = (lgl->opts->locsreleff.val*lglvisearch (lgl))/100;
    if (limit < lgl->opts->locsmineff.val) 
      limit = lgl->opts->locsmineff.val;
    if (lgl->opts->locsmaxeff.val >= 0 &&
        limit > lgl->opts->locsmaxeff.val)
      limit = lgl->opts->locsmaxeff.val;
    if (lgl->stats->locs.count <= 1 &&
        lgl->opts->boost.val &&
        lgl->opts->locsboost.val > 1) {
      boost = lgl->opts->locsboost.val;
      lglprt (lgl, 1,
	"[locs-%d] intially boosting limit by factor of %d",
	lgl->stats->locs.count, boost);
    } else boost = 1;
    limit *= boost;
    pen = lglitszpen (lgl);
    limit >>= pen;
    lglprt (lgl, 1,
      "[locs-%d] limit %lld literal penalty %d",
      lgl->stats->locs.count, (LGLL) limit, pen);
  }
  return limit;
}

#endif

static int lglocsaux (LGL * lgl, int hitlim) {
  int lkhd = 0;
#ifndef NLGLYALSAT
  int save = lgl->opts->locsexport.val && lgl->opts->phasesave.val;
  int res, min, pos, neg, idx, lit, old_val, len;
  const int set = lgl->opts->locset.val;
  unsigned long long seed;
  char * prefix;
  int64_t limit;
  AVar * av;
  Val val;
  Yals * yals;
  lglstart (lgl, &lgl->times->locs);
  if (lgl->level) lglbacktrack (lgl, 0);
  if (!lgl->stats->locs.count++) {
    const char * yals_version ();
    if (lgl->opts->verbose.val > 0)
      lglprt (lgl, 1,
	"[locs-%d] %s",
	lgl->stats->locs.count, yals_version ());
    else if (lgl->opts->locsbanner.val) {
      char * prefix = lgl->prefix;
      lgl->prefix = "c ";
      lglprt (lgl, 0, "%s", yals_version ());
      lgl->prefix = prefix;
    }
  }
  yals = yals_new_with_mem_mgr ( lgl,
	   (YalsMalloc) lglnew, (YalsRealloc) lglrsz, (YalsFree) lgldel);
  yals_setout (yals, lgl->out);
  len = strlen (lgl->prefix) + 80;
  NEW (prefix, len);
  if (lgl->tid >= 0)
    sprintf (prefix, "%s%d [locs-%d] ",
      lgl->prefix, lgl->tid, lgl->stats->locs.count);
  else
    sprintf (prefix, "%s[locs-%d] ", lgl->prefix, lgl->stats->locs.count);
  yals_setprefix (yals, prefix);
  DEL (prefix, len);
  old_val = yals_getopt (yals, "verbose");
  if (old_val < lgl->opts->verbose.val)
    yals_setopt (yals, "verbose", lgl->opts->verbose.val);
  seed = lglrand (lgl);
  if (lgl->tid >= 0) seed *= lgl->tid + 1;
  seed += 1237 * (unsigned) lgl->stats->locs.count;
  yals_srand (yals, seed);
  if (hitlim > 0) yals_setopt (yals, "hitlim", hitlim);
  lglocscopy (lgl, yals);
  if (lgl->mt) goto DONE;
  limit = lglsetlocslim (lgl);
  pos = neg = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    av = lglavar (lgl, idx);
         if (set == 2 && av->phase > 0) lit = idx;
    else if (set == 2 && av->phase < 0) lit = -idx;
    else if (set == 1 && av->locsval > 0) lit = idx;
    else if (set == 1 && av->locsval < 0) lit = -idx;
    else continue;
    assert (lit);
    if (lit < 0) neg++; else pos++;
    yals_setphase (yals, lit);
  }
  lglprt (lgl, 1,
    "[locs-%d] importing %d positive %.0f%% and %d negative %.0f%% phases",
    lgl->stats->locs.count,
    pos, lglpcnt (pos, pos + neg),
    neg, lglpcnt (neg, pos + neg));
  if (limit < LLMAX/1000) limit *= 1000; else limit = LLMAX;
  yals_setmemslimit (yals, limit);
  if (lgl->cbs && lgl->cbs->term.fun)
    yals_seterm (yals, lgl->cbs->term.fun, lgl->cbs->term.state);
  if (lgl->cbs && lgl->cbs->getime)
    yals_setime (yals, lgl->cbs->getime);
  if (lgl->cbs && lgl->cbs->msglock.lock)
    yals_setmsglock (yals,
      lgl->cbs->msglock.lock,
      lgl->cbs->msglock.unlock,
      lgl->cbs->msglock.state);
  res = yals_sat (yals);
  min = yals_minimum (yals);
  lglprt (lgl, 1,
    "[locs-%d] local search returns %d with minimum %d",
    lgl->stats->locs.count, res, min);
  if (min < lgl->stats->locs.min) lgl->stats->locs.min = min;
  lgl->stats->locs.flips += yals_flips (yals);
  lgl->stats->locs.mems += yals_mems (yals);
  if (res == 10) save = 1;
  pos = neg = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    val = yals_deref (yals, idx);
    assert (abs (val) == 1);
    av = lglavar (lgl, idx);
    if (val < 0) neg++, av->locsval = -1;
    else if (val > 0) pos++, av->locsval = 1;
    if (save) av->phase = val;
  }
  lglprt (lgl, 1,
    "[locs-%d] %s %d positive %.0f%% and %d negative %.0f%% phases",
    lgl->stats->locs.count,
    save ? "exported" : "found",
    pos, lglpcnt (pos, pos + neg),
    neg, lglpcnt (neg, pos + neg));
DONE:
  if (lgl->opts->verbose.val >= 1) yals_stats (yals);
  yals_del (yals);
  lglstop (lgl);
#endif
  return lkhd;
}

static void lglocs (LGL * lgl) {
  (void) lglocsaux (lgl, 0);
  lglupdlocslim (lgl, 1);
}

static int lglocslook (LGL * lgl) {
  int res = lglocsaux (lgl, 100000), elit;
  Ext * ext;
  if (res) {
    elit = lglexport (lgl, res);
    ext = lglelit2ext (lgl, elit);
    if (!ext->eliminated && !ext->blocking) {
      lglprt (lgl, 1, "[locslook] best local search look-ahead %d", res);
      if (ext->melted) {
	ext->melted = 0;
	LOG (2, "look-ahead winner external %d not melted anymore", elit);
      } else
	LOG (2, "look-ahead winner external %d was not melted anyhow", elit);
    } else {
      lglprt (lgl, 1, "[locslook] no valid local search look-ahead");
      lglprt (lgl, 1, "[locslook] falling back to JWH");
      res = lgljwhlook (lgl);
    }
  } else LOG (1, "no proper local search look-ahead literal found");

  return res;
}

/*------------------------------------------------------------------------*/

static int lglforklit (int ilit) {
  int idx = abs (ilit), res;
  assert (idx > 1);
  res = idx - 1;
  if (ilit < 0) res = -res;
  return res;
}

/*------------------------------------------------------------------------*/

static int lglsweeping (LGL * lgl) {
  if (!lglsmallirr (lgl)) return 0;
  if (!lgl->opts->sweep.val) return 0;
  if (lgldelaying (lgl, "sweep", &lgl->limits->sweep.del.rem)) return 0;
  if (lglwaiting (lgl, "sweep", lgl->opts->sweepwait.val)) return 0;
  return 1;
}

static void lglinitsweep (LGL * lgl) {
  int idx, lit, pos, neg, rem = 0, ret = 0;
  AVar * av;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    if (lglavar (lgl, idx)->donotsweep) ret++; else rem++;
  }
  if (!rem) {
    ret = 0;
    for (idx = 2; idx < lgl->nvars; idx++) {
      if (!lglisfree (lgl, idx)) continue;
      lglavar (lgl, idx)->donotsweep = 0;
      rem++;
    }
  }
  pos = neg = 0;
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    av = lglavar (lgl, idx);
    if (av->donotsweep) continue;
    if (av->phase <= 0) lit = -idx, neg++;
    else lit = idx, pos++;
    lglpushstk (lgl, &lgl->swp->partition, lit);
  }
  assert (pos + neg == rem);
  if (rem > 1) {
    lglpushstk (lgl, &lgl->swp->partition, 0);
    lgl->swp->partitions++;
  } else if (rem) {
    assert (rem == 1);
    lglclnstk (&lgl->swp->partition);
  } else assert (lglmtstk (&lgl->swp->partition));
  lglprt (lgl, 1,
    "[sweep-%d-%d] %d pos %.1f%% + %d neg %.1f%% = %d sched %.1f%% ret %d",
    lgl->stats->sweep.count, lgl->swp->round,
    pos, lglpcnt (pos, rem),
    neg, lglpcnt (neg, rem),
    rem, lglpcnt (rem, lgl->nvars - 2), ret);
}

static double lglsweepavgpartitionsize (LGL * lgl) {
  int count, n;
  double res;
  assert (lgl->swp);
  if (lglmtstk (&lgl->swp->partition)) return 0;
  count = lglcntstk (&lgl->swp->partition);
  n = lgl->swp->partitions;
  assert (0 < n), assert (n < count);
  res = count - n;
  res /= n;
  return res;
}

static void lgladdsweepbincls (LGL * lgl, int a, int b) {
  assert (lgl->swp);
  assert (lglmtstk (&lgl->clause));
  lglpushstk (lgl, &lgl->clause, a);
  lglpushstk (lgl, &lgl->clause, b);
  lglpushstk (lgl, &lgl->clause, 0);
  LOG (2, "sweeping detected binary clause", a, b);
  lgldrupligaddcls (lgl, REDCS);
  lgladdcls (lgl, REDCS, 0, 1);
  lglclnstk (&lgl->clause);
}

static void lglsweepsatinitlit (LGL * lgl, int lit, int a, int b) {
  int idx = abs (lit), decision;
  AVar * av;
  assert (a > 0), assert (b > 0);
  if (a == idx) return;
  if (b == idx) return;
  av = lglavar (lgl, idx);
  if (av->mark) return;
  av->mark = 1;
  if (lgldefphase (lgl, idx) <= 0) decision = -idx;
  else decision = idx;
  LOG (2, "sweep SAT adding decision %d", decision);
  lglpushstk (lgl, &lgl->swp->decision.stk, decision);
}

#define LGLCMPSWPDEC(A,B) lgldcmp (lgl, *(B), *(A))

static void lglsweepsatinit (LGL * lgl, int a, int b) {
  int i, idx, sign, lit, blit, tag, red, other, other2, lidx, old, count;
  const int sweepred = lgl->opts->sweepred.val;
  const int sweepirr = lgl->opts->sweepirr.val;
  const int * w, * eow, * p, * c, * l;
  HTS * hts;
  a = abs (a), b = abs (b);
  if (b > a) SWAP (int, a, b);
  if (a == lgl->swp->decision.cached.a &&
      b == lgl->swp->decision.cached.b) {
    LOG (2, "sweep SAT using cached environment of %d and %d", a, b);
    lgl->stats->sweep.cached++;
    count = lglcntstk (&lgl->swp->decision.stk);
    goto DONE;
  }
  lglclnstk (&lgl->swp->decision.stk);
  for (i = 0; i <= 1; i++) {
    idx = i ? b : a;
    old = lglcntstk (&lgl->swp->decision.stk);
    LOG (2, "sweep SAT initializing environment of %d", idx);
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	red = blit & REDCS;
	if (tag == BINCS) {
	  if (!red && sweepirr < 1) continue;
	  if (red && sweepred < 1) continue;
	  other = blit >> RMSHFT;
	  lglsweepsatinitlit (lgl, other, a, b);
	} else if (tag == TRNCS) {
	  if (!red && sweepirr < 2) continue;
	  if (red && sweepred < 2) continue;
	  other = blit >> RMSHFT;
	  lglsweepsatinitlit (lgl, other, a, b);
	  other2 = *p;
	  lglsweepsatinitlit (lgl, other2, a, b);
	} else {
	  assert (tag == LRGCS);
	  if (!red && sweepirr < 3) continue;
	  if (red && sweepred < 3) continue;
	  lidx = *p;
	  c = lglidx2lits (lgl, red, lidx);
	  for (l = c; (other = *l); l++)
	    lglsweepsatinitlit (lgl, other, a, b);
	}
      }
    }
    count = lglcntstk (&lgl->swp->decision.stk) - old;
    LOG (2, "sweep SAT environment of %d contains %d decisions", idx, count);
    (void) count;
  }
  for (p = lgl->swp->decision.stk.start; p < lgl->swp->decision.stk.top; p++)
    lglavar (lgl, *p)->mark = 0;
  lgl->swp->decision.cached.a = a;
  lgl->swp->decision.cached.b = b;
  count = lglcntstk (&lgl->swp->decision.stk);
  SORT (int, lgl->swp->decision.stk.start, count, LGLCMPSWPDEC);
DONE:
  LOG (2,
    "sweep SAT environment of %d and %d, contains %d decisions",
    a, b, count);
  lgl->swp->sumsize.envs += count;
  lgl->stats->sweep.sumsize.envs += count;
}

static int lglsweepdec (LGL * lgl) {
  int i, lit = 0;
  for (i = 0; i < lglcntstk (&lgl->swp->decision.stk); i++) {
    lit = lglpeek (&lgl->swp->decision.stk, i);
    if (!lglval (lgl, lit)) break;
  }
  if (i == lglcntstk (&lgl->swp->decision.stk)) {
    LOG (2, "no sweep implication decision left");
    return 0;
  }
  LOG (2,
    "sweep typed %d implication check decision %d score %s",
    lgl->swp->type, lit, lglscr2str (lgl, lglqvar (lgl, lit)->score));
  lgliassume (lgl, lit);
  lgl->swp->decision.count++;
  lgl->stats->sweep.decs++;
  return 1;
}

static int lglsweepsat (LGL * lgl, int lim, int a, int b) {
  int n = 0, aval, bval;
  assert (lgl->level == 2);
  lgl->stats->sweep.sat++;
  lgl->swp->sat++;
  LOG (2,
    "deep sweep implication SAT check %d/%d decision limit %d",
    lgl->swp->sat, lgl->stats->sweep.sat, lim);
  for (;;) {
    if (lglbcp (lgl)) {
      if (lgl->mt) return 0;
      if ((aval = lglval (lgl, a)) < 0) return 0;
      if ((bval = lglval (lgl, b)) > 0) return 0;
      if (!aval) {
	assert (!lgl->level);
	lgliassume (lgl, a);
	lgl->swp->decision.count++;
	lgl->stats->sweep.decs++;
	continue;
      }
      LOG (2, 
	"sweep typed %d assumption %d score %s",
	lgl->swp->type, a, lglscr2str (lgl, lglqvar (lgl, a)->score));
      if (!bval) {
	assert (lgl->level <= 1);
	lgliassume (lgl, -b);
	lgl->swp->decision.count++;
	lgl->stats->sweep.decs++;
	continue;
      }
      LOG (2, 
	"sweep typed %d assumption %d score %s",
	lgl->swp->type, b, lglscr2str (lgl, lglqvar (lgl, b)->score));
      assert (lglval (lgl, a) > 0), assert (lglval (lgl, b) < 0);
      if (++n > lim) {
	LOG (2, "deep sweep SAT checking decision limit %d reached", lim);
	return 1;
      }
      if (!lglsweepdec (lgl)) return 1;
    } else if (!lglana (lgl)) return 0;
  }
}

static int lglsweepliesaux (LGL * lgl, int a, int b) {
  int ok, val, res, dec;
  assert (!lgl->level);
  if (lgl->mt) return 0;
  if (lglifixed (lgl, a)) return 0;
  if (lglifixed (lgl, b)) return 0;
  lgliassume (lgl, a);
  ok = lglbcp (lgl);
  if (ok) {
    assert (lgl->level == 1);
    val = lglval (lgl, b);
    if (val > 0) {
      lglbacktrack (lgl, 0);
      LOG (1, "sweep implication check %d -> %d subsumed by BCP", a, b);
      res = 1;
    } else if (val < 0) {
      LOG (1, "sweep implication check %d -> %d incompatible with BCP", a, b);
      res = 0;
    } else {
      lgliassume (lgl, -b);
      ok = lglbcp (lgl);
      if (ok) {
	dec = lgl->stats->sweep.count - 1;
	dec *= lgl->opts->sweepfacdec.val;
	if (dec < lgl->opts->sweepmindec.val)
	  dec = lgl->opts->sweepmindec.val;
	if (dec > lgl->opts->sweepmaxdec.val)
	  dec = lgl->opts->sweepmaxdec.val;
	if (dec) {
	  lglsweepsatinit (lgl, a, b);
	  ok = lglsweepsat (lgl, dec, a, b);
	  if (ok) {
	    LOG (1, "deep sweep implication check %d -> %d failed", a, b);
	    res = 0;
	  } else {
	    lgl->stats->sweep.unsat++;
	    LOG (1, "deep sweep implication check %d -> %d succeeded", a, b);
	    if (lgl->level) lglbacktrack (lgl, 0);
	    res = 1;
	  }
	} else {
	  LOG (2, "skipping sweep implication SAT check");
	  res = 0;
	}
      } else {
	LOG (1, "shallow sweep implication check %d -> %d succeeded", a, b);
	lglbacktrack (lgl, 0);
	lgladdsweepbincls (lgl, -a, b);
	lgl->stats->sweep.impls++;
	res = 1;
      }
    }
  } else {
    lglbacktrack (lgl, 0);
    LOG (1, "failed literal %d during sweep implication check", a);
    lgl->stats->sweep.failed++;
    lglunit (lgl, -a);
    if (!lglbcp (lgl)) {
      LOG (1, "empty clause propagating unit in sweep implication check");
      lglmt (lgl);
    }
    res = 0;
  }
  return res;
}

static int lglsweeplies (LGL * lgl, int a, int b) {
  int res = lglsweepliesaux (lgl, a, b);
  if (!res) lgl->stats->sweep.queries.type[lgl->swp->type].sat++;
  else lgl->stats->sweep.queries.type[lgl->swp->type].unsat++;
  lglprt (lgl, 2,
    "[sweep-%d-%d-%d] implication check %s",
    lgl->stats->sweep.count, lgl->swp->round, lgl->swp->query,
    res ? "succeeded" : "failed");
  return res;
}

static void lglsweepquery (LGL * lgl) {
  int count = lglcntstk (&lgl->swp->partition), l, r, size;
  int p, q, a, b, i, c, newpartitions, newsize, newtotal;
  int total = count - lgl->swp->partitions, remove, val;
  int * partition = lgl->swp->partition.start;
  int minsize, best, start, bestscore;
  Stk newpartition;
  switch (lgl->swp->query % 5) {
    case 1: lgl->swp->type = 2; break;	// score
    case 2: lgl->swp->type = 1; break;	// size
    case 3: lgl->swp->type = 2; break;	// score
    case 4: lgl->swp->type = 1; break;	// size
    case 0: lgl->swp->type = 0; break;	// random
  }
  lgl->stats->sweep.queries.total++;
  lgl->stats->sweep.queries.type[lgl->swp->type].count++;
  assert (count > 0);
  lglprt (lgl, 2,
    "[sweep-%d-%d-%d] %d classes with %d vars of avg size %.1f",
    lgl->stats->sweep.count, lgl->swp->round, lgl->swp->query,
    lgl->swp->partitions, total, lglsweepavgpartitionsize (lgl));

  l = lglrand (lgl) % count;
  if (!partition[l]) { assert (l > 0); l--; }
  while (l > 0 && partition[l-1])
    l--;
  if (lgl->swp->type == 1) {		// min size partition
    INCSTEPS (sweep.steps);
    best = start = l;
    minsize = INT_MAX;
    do {
      assert (l < count);
      INCSTEPS (sweep.steps);
      size = 0;
      for (r = l; (a = partition[r]); r++) {
	COVER (lglifixed (lgl, a));
	if (lglifixed (lgl, a)) continue;
	size++;
      }
      if (size < minsize) best = l, minsize = size;
      if ((l = r + 1) == count) l = 0;
    } while (l != start);
    l = best;
  } else if (lgl->swp->type == 2) {	// best score partition
    INCSTEPS (sweep.steps);
    best = start = l;
    bestscore = 0;
    do {
      assert (l < count);
      INCSTEPS (sweep.steps);
      for (r = l; (a = partition[r]); r++) {
	if (lglifixed (lgl, a)) continue;
	if (bestscore && lgldcmp (lgl, a, bestscore) < 0) continue;
	best = l, bestscore = a;
      }
      if ((l = r + 1) == count) l = 0;
    } while (l != start);
    l = best;
  } else assert (lgl->swp->type == 0);	// random partition
  INCSTEPS (sweep.steps);
  for (r = l; partition[r]; r++)
    ;
  size = r - l;
  assert (1 < size), assert (size < count);
  lgl->swp->sumsize.classes += size;
  lgl->stats->sweep.sumsize.classes += size;
  lglprt (lgl, 2,
    "[sweep-%d-%d-%d] "
    "type %d picked size %d class [%d:%d] %.1f%%",
    lgl->stats->sweep.count, lgl->swp->round, lgl->swp->query,
    lgl->swp->type, size, l, r-1, lglpcnt (size, total));
  assert (size >= 2);
  p = lglrand (lgl) % size;
  q = lglrand (lgl) % size;
  if (p == q) q = !p;
  if (p + q >= size) q = p + q - size;
  p += l, assert (l <= p), assert (p < r);
  q += l, assert (l <= p), assert (q < r);
  assert (p != q);
  a = partition [p];
  b = partition [q];
  for (i = l; i < r; i++) {
    if (i == p) continue;
    if (i == q) continue;
    c = partition[i];
    if (lgldcmp (lgl, c, a) > 0) a = c, p = i;
  }
  for (i = l; i < r; i++) {
    if (i == p) continue;
    if (i == q) continue;
    c = partition[i];
    if (lgldcmp (lgl, c, b) > 0) b = c, q = i;
  }
  assert (a), assert (b);
  assert (abs (a) != abs (b));
  LOG (2,
    "picked literal pair %d and %d at position %d and %d",
    a, b, p, q);
  assert (!lgl->level);
  if (lglsweeplies (lgl, a, b) && lglsweeplies (lgl, b, a)) {
    assert (!lgl->level);
    lgl->stats->sweep.equivs++;
    remove = b;
    LOG (2,
      "found equivalence between %d and %d and will remove %d",
      a, b, b);
  } else remove = 0;
  CLR (newpartition);
  newsize = newpartitions = 0;
  if (!lgl->mt) {
    for (val = -1; val <= 1; val++) {
      for (i = 0; i < count; i++) {
	if ((c = partition[i])) {
	  if (c == remove) continue;
	  if (lglifixed (lgl, c)) continue;
	  if (lglval (lgl, c) != val) continue;
	  lglpushstk (lgl, &newpartition, c);
	  newsize++;
	} else if (newsize > 1) {
	  lglpushstk (lgl, &newpartition, 0);
	  newpartitions++;
	  newsize = 0;
	} else if (newsize) {
	  assert (newsize == 1);
	  (void) lglpopstk (&newpartition);
	  newsize = 0;
	}
      }
    }
    ADDSTEPS (sweep.steps, (count >> 3));
  }
  assert (!newsize);
  assert (!newpartitions || !newpartition.top[-1]);
  newtotal = lglcntstk (&newpartition) - newpartitions;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  if (lgl->swp->partitions >= newpartitions)
    lglprt (lgl, 2,
      "[sweep-%d-%d-%d] removed %d literals and removed %d classes",
      lgl->stats->sweep.count, lgl->swp->round, lgl->swp->query,
      total - newtotal, lgl->swp->partitions - newpartitions);
  else
    lglprt (lgl, 2,
      "[sweep-%d-%d-%d] removed %d literals and added %d classes",
      lgl->stats->sweep.count, lgl->swp->round, lgl->swp->query,
      total - newtotal, newpartitions - lgl->swp->partitions);
  lgl->swp->partitions = newpartitions;
  lglfitstk (lgl, &newpartition);
  lglrelstk (lgl, &lgl->swp->partition);
  lgl->swp->partition = newpartition;
}

static void lglsetsweeplim (LGL * lgl) {
  int count = lgl->stats->sweep.count - lgl->opts->sweepboostdel.val;
  int64_t limit, irrlim;
  int pen, szpen;
  if (lgl->opts->sweeprtc.val > 1) {
    lgl->limits->sweep.steps = LLMAX;
    lglprt (lgl, 1,
      "[sweep-%d] really no limit (run to completion)", 
      lgl->stats->sweep.count);
  } else if (lgl->opts->sweeprtc.val ||
	     lgl->opts->prbrtc.val ||
	     (count > 0 &&
	      lglrem (lgl) < lgl->opts->sweeprtcintvlim.val &&
	      !(count % lgl->opts->sweeprtcint.val))) {
    limit = 4000000000ll;
    lgl->limits->sweep.steps = lgl->stats->sweep.steps + limit;
    lglprt (lgl, 1,
      "[sweep-%d] almost no limit of %lld steps", 
      lgl->stats->sweep.count, (LGLL) limit);
  } else {
    limit = (lgl->opts->sweepreleff.val*lglvisearch (lgl))/1000;
    if (limit < lgl->opts->sweepmineff.val)
      limit = lgl->opts->sweepmineff.val;
    if (lgl->opts->sweepmaxeff.val >= 0 &&
	limit > lgl->opts->sweepmaxeff.val)
      limit = lgl->opts->sweepmaxeff.val;
    if (count > 0 &&
        (count <= 1 || !(count % lgl->opts->sweepboostint.val)) &&
	lglrem (lgl) < lgl->opts->sweepboostvlim.val &&
        lgl->opts->boost.val &&
        lgl->opts->sweepboost.val > 1) {
      lglprt (lgl, 1,
	"[sweep-%d] boosting sweeping limit by %d",
	lgl->stats->sweep.count, lgl->opts->sweepboost.val);
      limit *= lgl->opts->sweepboost.val;
    }
    limit >>= (pen = lgl->limits->sweep.pen + (szpen = lglszpen (lgl)));
    irrlim = (2*lgl->stats->irr.clauses.cur) >> szpen;
    if (lgl->opts->irrlim.val && limit < irrlim) {
      limit = irrlim;
      lglprt (lgl, 1,
	"[sweep-%d] limit %lld based on %d irredundant clauses penalty %d",
	lgl->stats->sweep.count,
	(LGLL) limit, lgl->stats->irr.clauses.cur, szpen);
    } else
      lglprt (lgl, 1,
        "[sweep-%d] limit %lld penalty %d = %d + %d",
	lgl->stats->sweep.count, (LGLL) limit,
	pen, lgl->limits->sweep.pen, szpen);
    lgl->limits->sweep.steps = lgl->stats->sweep.steps + limit;
  }
}

static void lglsweepretain (LGL * lgl) {
  int idx, ret = 0, rem = 0, sum;
  const int * p;
  for (idx = 2; idx < lgl->nvars; idx++)
    lglavar (lgl, idx)->donotsweep = 1;
  for (p = lgl->swp->partition.start;
       p < lgl->swp->partition.top;
       p++) {
    if(!(idx = *p)) continue;
    lglavar (lgl, idx)->donotsweep = 0;
  }
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    if (lglavar (lgl, idx)->donotsweep) ret++; else rem++;
  }
  if (rem) {
    sum = rem + ret;
    lglprt (lgl, 1,
      "[sweep-%d-%d] %d variables remain %.0f%% (%d retained %.0f%%)",
      lgl->stats->sweep.count, lgl->swp->round,
      rem, lglpcnt (rem, sum),
      ret, lglpcnt (ret, sum));
  } else {
    lglprt (lgl, 1,
      "[sweep-%d-%d] fully completed sweeping round",
      lgl->stats->sweep.count, lgl->swp->round);
    for (idx = 2; idx < lgl->nvars; idx++)
      lglavar (lgl, idx)->donotsweep = 0;
    lgl->sweeprtc = 1;
  }
}

static int lglsweep (LGL * lgl) {
  int deltarem, deltafailed, deltaimpls, deltaequivs, deltaorigrem;
  int round, origrem, oldrem, oldfailed, oldimpls, oldequivs;
  int64_t oldsteps, deltasteps, origqueries, deltaqueries;
  int success, forgive;
  lglstart (lgl, &lgl->times->sweep);
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  assert (!lgl->simp), assert (!lgl->sweeping);
  lgl->simp = lgl->sweeping = 1;
  if (!lglbcp (lgl)) goto DONE;
  lglgc (lgl);
  if (lgl->mt) goto DONE;
  lgl->stats->sweep.count++;
  lglsetsweeplim (lgl);
  origrem = lglrem (lgl);
  origqueries = lgl->stats->sweep.queries.total;
  round = 0;
  forgive = lgl->opts->sweepforgive.val;
RESTART:
  round++; 
  lgl->stats->sweep.rounds++;
  oldrem = lglrem (lgl);
  oldfailed = lgl->stats->sweep.failed;
  oldimpls = lgl->stats->sweep.impls;
  oldequivs = lgl->stats->sweep.equivs;
  oldsteps = lgl->stats->sweep.steps;
  assert (!lgl->swp);
  NEW (lgl->swp, 1);
  lgl->swp->round = round;
  lglinitsweep (lgl);
  for (lgl->swp->query = 1;
    !lgl->mt &&
      !lglmtstk (&lgl->swp->partition) &&
      lgl->stats->sweep.steps <= lgl->limits->sweep.steps;
    lgl->swp->query++)
    lglsweepquery (lgl);
  deltasteps = lgl->stats->sweep.steps - oldsteps;
  lglprt (lgl, 1,
    "[sweep-%d-%d] %lld steps %d queries %.2f avg class size",
    lgl->stats->sweep.count, round,
    (LGLL) deltasteps, lgl->swp->query,
      lglavg (lgl->swp->sumsize.classes, lgl->swp->query));
  lglprt (lgl, 1,
    "[sweep-%d-%d] %d decisions %d SAT calls %.2f avg env size",
    lgl->stats->sweep.count, round,
    lgl->swp->decision.count, lgl->swp->sat,
      lglavg (lgl->swp->sumsize.envs, lgl->swp->sat));
  lglrelstk (lgl, &lgl->swp->decision.stk);
  lglsweepretain (lgl);
  lglrelstk (lgl, &lgl->swp->partition);
  if (!lgl->mt) lgldecomp (lgl);
  assert (lgl->swp->round == round);
  DEL (lgl->swp, 1);
  lgl->swp = 0;
  deltarem = oldrem - lglrem (lgl);
  deltafailed = lgl->stats->sweep.failed - oldfailed;
  deltaimpls = lgl->stats->sweep.impls - oldimpls;
  deltaequivs = lgl->stats->sweep.equivs - oldequivs;
  lglprt (lgl, 1,
    "[sweep-%d-%d] removed %d vars (%d failed, %d eqs, %d impls)",
    lgl->stats->sweep.count, round,
    deltarem, deltafailed, deltaequivs, deltaimpls);
  if ((deltarem || forgive > 0) &&
      !lgl->mt &&
      (lgl->opts->sweepmaxround.val < 0 ||
       round < lgl->opts->sweepmaxround.val) &&
      lgl->stats->sweep.steps <= lgl->limits->sweep.steps) {
    if (deltarem) forgive = lgl->opts->sweepforgive.val; else forgive--;
    goto RESTART;
  }
  deltaorigrem = origrem - lglrem (lgl);
  if (!lgl->sweeprtc &&
      lgl->stats->sweep.count <= lgl->opts->sweepsuccessmaxwortc.val) {
    success = 1;
    lglprt (lgl, 1,
      "[sweep-%d] considered successful since not run to completion yet",
      lgl->stats->sweep.count);
  } else if (deltaorigrem) {
    success = (origrem/lgl->opts->sweepsuccessrat.val <= deltaorigrem);
    if (!success)
      lglprt (lgl, 1,
	"[sweep-%d] %d < 1/%d * %d = %d considered unsuccessful",
	lgl->stats->sweep.count, deltaorigrem, lgl->opts->sweepsuccessrat.val,
	origrem, origrem/lgl->opts->sweepsuccessrat.val);
  } else success = 0;
  LGLUPDPEN (sweep, success);
  deltaqueries = lgl->stats->sweep.queries.total - origqueries;
  lglprt (lgl, 1,
    "[sweep-%d] removed %d vars in TOTAL (%d rounds, %lld queries)",
    lgl->stats->sweep.count, deltaorigrem, round, (LGLL) deltaqueries);
DONE:
  assert (lgl->simp), assert (lgl->sweeping);
  lgl->simp = lgl->sweeping = 0;
  lglstop (lgl);
  return !lgl->mt;
}

/*------------------------------------------------------------------------*/

static int lglqcmp (LGL * lgl, int a, int b) {
  Flt ascore, bscore, pos, neg;
  pos = lgl->jwh[lglulit (a)];
  neg = lgl->jwh[lglulit (-a)];
  ascore = lglmulflt (pos, neg);
  pos = lgl->jwh[lglulit (b)];
  neg = lgl->jwh[lglulit (-b)];
  bscore = lglmulflt (pos, neg);
  if (ascore < bscore) return -1;
  if (ascore > bscore) return 1;
  return a - b;
}

#define LGLQCMP(A,B) lglqcmp (lgl, *(A), *(B))

static void lglqueuesort (LGL * lgl) {
  int count, i, lit;
  QVar * qv;
  lglstart (lgl, &lgl->times->queuesort);
  if (lgl->queue.mt) lglqueueflush (lgl);
  lgl->stats->queue.sorted++;
  assert (!lgl->queue.mt);
  count = lglcntstk (&lgl->queue.stk);
  assert (count > 0);
  SORT (int, lgl->queue.stk.start, count, LGLQCMP);
  for (i = 0; i < count; i++) {
    lit = lglpeek (&lgl->queue.stk, i);
    qv = lglqvar (lgl, lit);
    assert (qv->enqueued);
    assert (qv->pos >= 0);
    qv->pos = i;
  }
  lglprt (lgl, 2,
    "[sort-queue-%d] sorted %d after %lld conflicts and %lld flushed queues",
    (LGLL) lgl->stats->queue.sorted, count,
    (LGLL) lgl->stats->confs, (LGLL) lgl->stats->queue.flushed);
  lgl->queue.next = count - 1;
  lglstop (lgl);
}

static int lglqueuesorting (LGL * lgl) {
  int count = lglcntstk (&lgl->queue.stk);
  assert (lgl->queue.mt <= count);
  if (lgl->queue.mt >= count) return 0;
  return lgl->opts->queuesort.val;
}

/*------------------------------------------------------------------------*/

#define LGLCMPSCR(A,B) lglscrcmp (lgl, *(A), *(B))

static void lglshowscoredist (LGL * lgl) {
  int idx, pos = 0, zero = 0, min = 0, sum = 0, diff;
  Flt * scores;
  QVar * q;
  lglstart (lgl, &lgl->times->showscoredist);
  NEW (scores, lgl->nvars);
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (!lglisfree (lgl, idx)) continue;
    q = lglqvar (lgl, idx);
    if (q->score == FLTMIN) zero++;
    else if (q->score <= lgl->minscore) min++;
    else pos++;
    scores[sum++] = q->score;
  }
  lglprt (lgl, 1, 
    "[score-distribution-%d] "
    "%d pos %.2f%%, %d min %.2f%%, %d zero %.2f%%",
    lgl->stats->simp.count,
    pos, lglpcnt (pos, sum),
    min, lglpcnt (min, sum),
    zero, lglpcnt (zero, sum));
  SORT (Flt, scores, sum, LGLCMPSCR);
  diff = 0;
  for (idx = 0; idx < sum; idx++)
    if (!idx || lglscrcmp (lgl, scores[idx-1], scores[idx])) diff++;
  DEL (scores, lgl->nvars);
  lglprt (lgl, 1, 
    "[score-distribution-%d] "
    "%d different %.2f%% out of total %d variables",
    lgl->stats->simp.count,
    diff, lglpcnt (diff, sum),
    sum);
  lglstop (lgl);
}

static Features lglfeatures (LGL * lgl) {
  int idx, sign, lit, blit, tag, red, other, other1, len, lrg;
  const int * p, * w, * eow, * c;
  HTS * hts;
  Features res;
  CLR (res);
  res.n = lgl->stats->features;
  res.s = lglsec (lgl);
  res.vo = lgl->limits->inc.vars.start;
  res.vc = lglrem (lgl);
  res.co = lgl->limits->inc.clauses.start;
  res.cc = lgl->stats->irr.clauses.cur;
  res.x = lgl->stats->gauss.extracted.last;
  res.a1 = lgl->stats->card.found.am1.last.cnt;
  res.a2 = lgl->stats->card.found.am2.last.cnt;
  res.c = lgl->stats->confs / 1000;
  res.o = lgl->stats->otfs.total / 1000;
  res.g = lgl->stats->glue.slow.val >> 32;
  res.j = lgl->stats->jlevel.slow.val >> 32;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (red || tag == LRGCS) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	if (tag == BINCS) {
	  res.b++;
	} else {
	  assert (tag == TRNCS);
	  other1 = *p;
	  if (abs (other1) < idx) continue;
	  res.t++;
	}
      }
    }
  lrg = 0;
  for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
    if (*(p = c) >= REMOVED) continue;
    while (*++p)
      ;
    len = p - c;
    if (len <= 4) res.q++;
    else if (len <= 10) res.c1++;
    else if (len <= 100) res.c2++;
    else if (len <= 1000) res.c3++;
    else if (len <= 10000) res.c4++;
    else lrg++;
  }
  assert (res.b + res.t + res.q + 
          res.c1 + res.c2 + res.c3 + res.c4 + lrg == res.cc);
  return res;
}

static Features lglnormfeatures (Features f) {
  Features res = f;
  int * p = (int*) &res, i;
  for (i = 2; i < NFEATURES; i++)
    p[i] = lglceild (p[i] + 1);
  return res;
}

static int lglintstrlen (int i) {
  assert (i >= 0);
  if (i < 10) return 1;
  if (i < 100) return 2;
  if (i < 1000) return 3;
  if (i < 10000) return 4;
  if (i < 100000) return 5;
  if (i < 1000000) return 6;
  if (i < 10000000) return 7;
  if (i < 100000000) return 8;
  if (i < 1000000000) return 9;
  return 10;
}

static void lglshowfeatures (LGL * lgl) {
  int size[NFEATURES], i;
  const int * p;
  char fmt[20];
  Features f, n;
  if (!lgl->opts->features.val) return;
  if (lgl->opts->verbose.val <= 0) return;
  if (lgl->stats->features >= lgl->opts->features.val) return;
  lglstart (lgl, &lgl->times->showfeatures);
  f = lglfeatures (lgl);
  p = (int*) &f;
  for (i = 0; i < NFEATURES; i++)
    size[i] = lglmax (strlen (featurenames[i]), lglintstrlen (p[i]));

  lglmsgstart (lgl, 0);
  fprintf (lgl->out, "[heatures-%d]", f.n);
  for (i = 0; i < NFEATURES; i++) {
    sprintf (fmt, " %%%ds",  size[i]);
    fprintf (lgl->out, fmt, featurenames[i]);
  }
  lglmsgend (lgl);

  lglmsgstart (lgl, 0);
  fprintf (lgl->out, "[features-%d]", f.n);
  for (i = 0; i < NFEATURES; i++) {
    sprintf (fmt, " %%%dd",  size[i]);
    fprintf (lgl->out, fmt, p[i]);
  }
  lglmsgend (lgl);

  n = lglnormfeatures (f);
  p = (int*) &n;
  lglmsgstart (lgl, 0);
  fprintf (lgl->out, "[neatures-%d]", n.n);
  for (i = 0; i < NFEATURES; i++) {
    sprintf (fmt, " %%%dd",  size[i]);
    fprintf (lgl->out, fmt, p[i]);
  }
  lglmsgend (lgl);
  lgl->stats->features++;
  lglstop (lgl);
}

/*------------------------------------------------------------------------*/

static int lglisimp (LGL * lgl) {
  if (!lgl->opts->simplify.val) return 1;

  if (lglquatresolving (lgl)) lglquatres (lgl);
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglternresolving (lgl) && !lglternres (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglcarding (lgl) && !lglcard (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglgaussing (lgl) && !lglgauss (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lgldecomposing (lgl) && !lgldecomp (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglprobing (lgl) && !lglprobe (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglunhiding (lgl) && !lglunhide (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lgltreducing (lgl) && !lgltrd (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglblocking (lgl)) lglblock (lgl);
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglcceing (lgl) && !lglcce (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lgleliminating (lgl) && !lglelim (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (!lgltopgc (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglbcaing (lgl)) lglbca (lgl);
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglsweeping (lgl) && !lglsweep (lgl)) return 0;
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (!lgl->allphaseset) lglphase (lgl);
  if (lglterminate (lgl)) return 1;
  assert (!lgl->mt);

  if (lglqueuesorting (lgl)) lglqueuesort (lgl);
  if (lglterminate (lgl)) return 1;

  lgldefrag (lgl);
  if (lglterminate (lgl)) return 1;

  lglshowscoredist (lgl);
  lglshowfeatures (lgl);

  return 1;
}

static void lglupdsimpcinc (LGL * lgl, int red, int success) {
  const char * type = "no";
  int inc = 0, div = 1, res;
  assert (red >= 0);
  if (red <= 100) {
    if (red > 0) {
      switch (lgl->opts->simpcintincdiv.val) {
	case 3: 
	  if (red >= 50) div = 4;
	  else if (red >= 20) div = 3;
	  else if (red >= 10) div = 2;
	  break;
	case 2: div = red/2 + 1; break;
	case 1: div = red/1 + 1; break;
	case 0:
	default: 
          assert (!lgl->opts->simpcintincdiv.val);
	  break;
      }
    }
    inc = lgl->opts->simpcintinc.val;
    if (lgl->opts->simplify.val == 1) {
      type = "arithmetic";
    } else if (lgl->opts->simplify.val == 2) {
      if (inc < lgl->limits->simp.cinc) inc = lgl->limits->simp.cinc;
      type = "geometric";
    } else inc = 0;
  }
  res = inc / div;
  if (lgl->limits->simp.cinc - res <= INT_MAX)
    lgl->limits->simp.cinc += res;
  lglprt (lgl, 2,
    "[simplification-%d] new lgl->limits->simp.cinc %d",
    lgl->stats->simp.count, lgl->limits->simp.cinc);
  if (div > 1)
    lglprt (lgl, 1,
      "[simplification-%d] %s conflict interval increment %d = %d / %d",
      lgl->stats->simp.count, type, res, inc, div);
  else
    lglprt (lgl, 1,
      "[simplification-%d] full %s conflict interval increment %d",
      lgl->stats->simp.count, type, res);

  if (success &&
      lgl->opts->simpcintmaxsoft.val >= 0 &&
      lgl->limits->simp.cinc >= lgl->opts->simpcintmaxsoft.val) {
    lgl->limits->simp.cinc = lgl->opts->simpcintmaxsoft.val;
    lglprt (lgl, 1,
      "[simplification-%d] "
      "conflict interval soft limit %d reached",
      lgl->stats->simp.count, lgl->limits->simp.cinc);
  } else if (lgl->opts->simpcintmaxhard.val >= 0 &&
             lgl->limits->simp.cinc >= lgl->opts->simpcintmaxhard.val) {
    lgl->limits->simp.cinc = lgl->opts->simpcintmaxhard.val;
    lglprt (lgl, 1,
      "[simplification-%d] "
      "conflict interval hard limit %d reached",
      lgl->stats->simp.count, lgl->limits->simp.cinc);
  }
}

static void lglsethardsimplim (LGL * lgl) {
  int64_t hard, delta;
  delta = lgl->limits->simp.confs - lgl->stats->confs;
  if (delta < 0) delta = 0;
  delta *= lgl->opts->simpincdelmaxfact.val;
  delta /= 100;
  if (delta < lgl->opts->simpincdelmaxmin.val)
    delta = lgl->opts->simpincdelmaxmin.val;
  if (LLMAX - delta < lgl->limits->simp.confs) hard = LLMAX;
  else hard = lgl->limits->simp.confs + delta;
  lgl->limits->simp.hard = hard;
  lglprt (lgl, 1,	// TODO set this to 2
    "[simplification-%d] hard conflict limit %lld (soft %lld + delta %lld)",
    lgl->stats->simp.count,
    (LGLL) lgl->limits->simp.hard, (LGLL) lgl->limits->simp.confs, (LGLL) delta);
}

static void lglupdsimpint (LGL * lgl, int oldrem, int oldirr, int forced) {
  int remvar, remirr, pcntred, simpcinc;
  int64_t pcntremvar64, pcntremirr64;
  int pcntremvar, pcntremirr;

  remvar = oldrem - lglrem (lgl);
  if (remvar < 0) remvar = 0;
  pcntremvar64 = (remvar > 0) ? ((1000ll*remvar)/oldrem + 5)/10 : 0ll;
  assert (pcntremvar64 <= 100);
  pcntremvar = pcntremvar64;
  lglprt (lgl, 1,
    "[simplification-%d] removed %d variables %.1f%% "
    "(%d remain %0.f%%)",
    lgl->stats->simp.count, remvar, lglpcnt (remvar, oldrem),
    lglrem (lgl), lglpcnt (lglrem (lgl), lgl->limits->inc.vars.start));

  remirr = oldirr - lgl->stats->irr.clauses.cur;
  if (remirr < 0) remirr = 0;
  pcntremirr64 = (remirr > 0) ? ((1000ll*remirr)/oldirr + 5)/10 : 0ll;
  assert (pcntremirr64 <= 100);
  pcntremirr = pcntremirr64;
  lglprt (lgl, 1,
    "[simplification-%d] removed %d irredundant clauses %.1f%% "
    "(%d remain %.0f%%)",
    lgl->stats->simp.count, remirr, lglpcnt (remirr, oldirr),
    lgl->stats->irr.clauses.cur,
      lglpcnt (lgl->stats->irr.clauses.cur, lgl->limits->inc.clauses.start));

  pcntred = lglmax (pcntremvar, pcntremirr);
  lglprt (lgl, 1,
    "[simplification-%d] maximum reduction of %d%% = max (%d%%, %d%%)",
    lgl->stats->simp.count, pcntred, pcntremvar, pcntremirr);

  if (forced) {
    simpcinc = 0;
    lglprt (lgl, 1,
      "[simplification-%d] forced so keeping old conflict interval %d",
      lgl->stats->simp.count, lgl->limits->simp.cinc);
  } else if (lgl->stats->confs < lgl->limits->simp.confs &&
             (simpcinc = lgl->limits->simp.cinc)) {
    lglprt (lgl, 1,
      "[simplification-%d] keeping old conflict interval %d "
      "(non-conflict triggered simplification)",
      lgl->stats->simp.count, lgl->limits->simp.cinc);
  } else if (remvar > 0 && pcntred >= lgl->opts->simprtc.val) {
    int64_t scaledcinc;
    int factor;
    lglprt (lgl, 1,
      "[simplification-%d] large reduction %d%% >= %d%% limit",
      lgl->stats->simp.count, pcntred, lgl->opts->simprtc.val);
    factor = lgl->opts->simpidiv.val - lgl->stats->simp.count;
    if (factor <= 0) factor = 1;
    simpcinc = lgl->opts->simpcintdelay.val / factor;
    scaledcinc = lgl->stats->confs/lgl->opts->simpiscale.val;
    if (scaledcinc > lgl->limits->simp.cinc)
      scaledcinc = lgl->limits->simp.cinc;
    if (scaledcinc < simpcinc) {
      lglprt (lgl, 1,
	"[simplification-%d] next conflict interval %d = %d/%d",
	lgl->stats->simp.count,
	simpcinc, lgl->opts->simpcintdelay.val, factor);
    } else {
      assert (scaledcinc <= INT_MAX);
      simpcinc = (int) scaledcinc;
      lglprt (lgl, 1,
	"[simplification-%d] next conflict interval %d = min (%lld/%d, %d)",
	lgl->stats->simp.count,
	simpcinc, (LGLL) lgl->stats->confs, lgl->opts->simpiscale.val,
	lgl->limits->simp.cinc);
    }
  } else {
    lglupdsimpcinc (lgl, pcntred, remvar || remirr);
    simpcinc = lgl->limits->simp.cinc;
    lglprt (lgl, 1,
      "[simplification-%d] new conflict interval %d",
      lgl->stats->simp.count, simpcinc);
  }

  if (forced) {
    lglprt (lgl, 1,
      "[simplification-%d] conflict limit remains at %lld (hard %lld)",
      lgl->stats->simp.count,
      (LGLL) lgl->limits->simp.confs, (LGLL) lgl->limits->simp.hard);
  } else {
    int penalty, pensimpcinc;
         if (!lgl->opts->simpintsizepen.val ||
	     lgl->stats->irr.clauses.cur <    1000000)    penalty = 1;
    else if (lgl->stats->irr.clauses.cur <   10000000)    penalty = 2;
    else /*  lgl->stats->irr.clauses.cur >=  10000000) */ penalty = 4;
    if (INT_MAX/penalty < simpcinc) pensimpcinc = INT_MAX;
    else pensimpcinc = penalty * simpcinc;
    lglprt (lgl, 1,
      "[simplification-%d] penalized conflict interval %d = %d * %d",
      lgl->stats->simp.count, pensimpcinc, penalty, simpcinc);
    assert (pensimpcinc >= 0);
    lgl->limits->simp.confs = lgl->stats->confs + pensimpcinc;
    assert (lgl->limits->simp.confs >= 0);
    lglsethardsimplim (lgl);
    lglprt (lgl, 1,
      "[simplification-%d] new conflict limit %lld (hard %lld)",
      lgl->stats->simp.count,
      (LGLL) lgl->limits->simp.confs, (LGLL) lgl->limits->simp.hard);
  }

  if (lgl->stats->confs >= lgl->limits->simp.confs) {
    lgl->limits->simp.confs = lgl->stats->confs + 1;
    if (lgl->limits->simp.hard < lgl->limits->simp.confs)
       lgl->limits->simp.hard = lgl->limits->simp.confs;
    lglprt (lgl, 1,
      "[simplification-%d] "
      "fixed conflict limit %d (wait at least for one conflict)",
      lgl->stats->simp.count, lgl->stats->confs);
  }

  if (forced == 1 &&
      lgl->limits->simp.itinc < lgl->opts->simpitintinclim.val) {
    if (lgl->limits->simp.itinc < INT_MAX/10) lgl->limits->simp.itinc *= 10;
    else lgl->limits->simp.itinc = INT_MAX;
    if (lgl->limits->simp.itinc > lgl->opts->simpitintinclim.val)
      lgl->limits->simp.itinc = lgl->opts->simpitintinclim.val;
    lglprt (lgl, 1,
      "[simplification-%d] new iteration interval %d",
      lgl->stats->simp.count, lgl->limits->simp.itinc);
  }
  lgl->limits->simp.its = lgl->stats->its.count + lgl->limits->simp.itinc;

  if (forced == 2 &&
      lgl->limits->simp.binc < lgl->opts->simpbintinclim.val) {
    if (lgl->limits->simp.binc < INT_MAX/10) lgl->limits->simp.binc *= 10;
    else lgl->limits->simp.binc = INT_MAX;
    if (lgl->limits->simp.binc > lgl->opts->simpbintinclim.val)
      lgl->limits->simp.binc = lgl->opts->simpbintinclim.val;
    lglprt (lgl, 1,
      "[simplification-%d] new binary interval %d",
      lgl->stats->simp.count, lgl->limits->simp.binc);
  }
  lgl->limits->simp.bin = lgl->stats->bins + lgl->limits->simp.binc;

  if (forced == 3 &&
      lgl->limits->simp.tinc < lgl->opts->simptintinclim.val) {
    if (lgl->limits->simp.tinc < INT_MAX/10) lgl->limits->simp.tinc *= 10;
    else lgl->limits->simp.tinc = INT_MAX;
    if (lgl->limits->simp.tinc > lgl->opts->simptintinclim.val)
      lgl->limits->simp.tinc = lgl->opts->simptintinclim.val;
    lglprt (lgl, 1,
      "[simplification-%d] new ternary interval %d",
      lgl->stats->simp.count, lgl->limits->simp.tinc);
  }
  lgl->limits->simp.trn = lgl->stats->trns + lgl->limits->simp.tinc;

  lgl->limits->simp.vars = lglrem (lgl);
  lgl->repforcehead = 1;
  if (lgl->wait > 0) lgl->wait--;

#ifndef NLGLFILES
  {
    static FILE * simpsfile = 0;
    if (!simpsfile) simpsfile = fopen ("/tmp/simps", "w");
    fprintf (simpsfile, "%lld\n", (LGLL) lgl->stats->confs);
    fflush (simpsfile);
  }
#endif
}

static int lglpreprocessing (LGL * lgl, int forced) {
  int res, oldrem, oldirr;
  if (lgl->mt) return 0;
  assert (!lgl->searching);
  lgl->stats->simp.count++;
  oldrem = lglrem (lgl);
  oldirr = lgl->stats->irr.clauses.cur;
  res = lglisimp (lgl);
  lglupdsimpint (lgl, oldrem, oldirr, forced);
  assert (res == !lgl->mt);
  return res;
}

static int lglsimplimhit (LGL * lgl, int * forcedptr) {
  int64_t n, o, d;
  int a, r, res = 0;;
  if (!lgl->opts->inprocessing.val && lgl->stats->simp.count) return 0;
  if (lgl->stats->confs < lgl->limits->simp.hard) {
    if (lgl->opts->simpitintdecdelay.val &&
        lgl->stats->its.avg.diff.smoothed.val < 0) return 0;
    if (lgl->opts->simpjleveldecdelay.val &&
        lgl->stats->jlevel.diff.smoothed.val < 0) return 0;
  }
  if (lgl->stats->confs >= lgl->limits->simp.confs) {
    lglprt (lgl, 1, "");
    lglprt (lgl, 1,
      "[simplification-%d] "
      "limit %lld conflicts (hard %lld) hit after %lld conflicts",
      lgl->stats->simp.count + 1,
      (LGLL) lgl->limits->simp.confs, (LGLL) lgl->limits->simp.hard,
      (LGLL) lgl->stats->confs);
    lgl->stats->simp.limhit.confs++;
    *forcedptr = 0;
    res = 1;
  }
  if (!res && lgl->stats->trns >= lgl->limits->simp.trn) {
    lglprt (lgl, 1, "");
    lglprt (lgl, 1,
      "[simplification-%d] limit of %lld ternary hit after %lld ternaries",
      lgl->stats->simp.count + 1,
      (LGLL) lgl->limits->simp.trn, (LGLL) lgl->stats->trns);
    lgl->stats->simp.limhit.trn++;
    *forcedptr = 3;
    res = 1;
  }
  if (!res && lgl->stats->bins >= lgl->limits->simp.bin) {
    lglprt (lgl, 1, "");
    lglprt (lgl, 1,
      "[simplification-%d] limit of %lld binary hit after %lld binaries",
      lgl->stats->simp.count + 1,
      (LGLL) lgl->limits->simp.bin, (LGLL) lgl->stats->bins);
    lgl->stats->simp.limhit.bin++;
    *forcedptr = 2;
    res = 1;
  }
  if (!res && lgl->stats->its.count >= lgl->limits->simp.its) {
    lglprt (lgl, 1, "");
    lglprt (lgl, 1,
      "[simplification-%d] limit of %lld iterations hit after %d iterations",
      lgl->stats->simp.count + 1,
      (LGLL) lgl->limits->simp.its, lgl->stats->its.count);
    lgl->stats->simp.limhit.its++;
    *forcedptr = 1;
    res = 1;
  }
  if (!res &&
      (o = lgl->limits->simp.vars) &&
      (n = lglrem (lgl)) >= lgl->opts->simpvarlim.val) {
    d = n - o;
    r = 100*d;
    r /= o;
    if (r <= INT_MIN || r > INT_MAX) a = INT_MAX;
    else if (r < 0) a = -r;
    else a = r;
    if (a >= lgl->opts->simpvarchg.val) {
      lglprt (lgl, 1, "");
      lglprt (lgl, 1,
	"[simplification-%d] limit hit: "
	"remaining variables changed from %lld to %lld by %d%%",
	lgl->stats->simp.count + 1, (LGLL) o, (LGLL) n, r);
      lgl->stats->simp.limhit.vars++;
      *forcedptr = -1;
      res = 1;
    }
  }
  return res;
}

static int lglinprocessing (LGL * lgl) {
  int res, oldrem, oldirr, forced;
  assert (lgl->searching);
  if (!lglsimplimhit (lgl, &forced)) return !lgl->mt;
  lgl->stats->simp.count++;
  lglstart (lgl, &lgl->times->inprocessing);
  oldrem = lglrem (lgl);
  oldirr = lgl->stats->irr.clauses.cur;
  res = lglisimp (lgl);
  lglupdsimpint (lgl, oldrem, oldirr, forced);
  lglstop (lgl);
  assert (res == !lgl->mt);
  return res;
}

static int lglbcptop (LGL * lgl) {
  int res;
  if (lglbcp (lgl)) res = 1;
  else {
#ifndef NDEBUG
    int tmp =
#endif
    lglana (lgl);
    assert (!tmp);
    if (lgl->conf.lit) {
      LOG (1, "top level propagation produces inconsistency");
      lglmt (lgl);
    } else assert (lgl->failed);
    res = 0;
  }
  return res;
}

static int lglimhit (LGL * lgl, Lim * lim) {
  if (!lim) return 0;
  if (lim->decs >= 0 && lgl->stats->decisions >= lim->decs) {
    lglprt (lgl, 1, "[limits] decision limit %lld hit at %lld decisions",
      (LGLL) lim->decs, (LGLL) lgl->stats->decisions);
    return 1;
  }
  if (lim->confs >= 0 && lgl->stats->confs >= lim->confs) {
    lglprt (lgl, 1, "[limits] conflict limit %lld hit at %lld conflicts",
      (LGLL) lim->confs, (LGLL) lgl->stats->confs);
    return 1;
  }
  if (lim->props >= 0 && lgl->stats->props.search >= lim->props) {
    lglprt (lgl, 1,
      "[limits] propagation limit %lld hit at %lld propagations",
      (LGLL) lim->props, (LGLL) lgl->stats->props.search);
    return 1;
  }
  return 0;
}

static int lgloop (LGL * lgl, Lim * lim) {
  unsigned confs = 0;
  for (;;) {
    if (lglbcpsearch (lgl) && lglinprocessing (lgl)) {
      if (lglterminate (lgl)) return 0;
      if (!lglsyncunits (lgl)) return 20;
      if (!lglsyncls (lgl)) continue;
      if (lglfailedass (lgl)) return 20;
      if (lglreducing (lgl)) lglreduce (lgl, 0);
      if (lgldefragmenting (lgl)) lgldefrag (lgl);
      if (lglimhit (lgl, lim)) return 0;
      if (lglocsing (lgl)) lglocs (lgl);
      if (lglrestarting (lgl)) { lglrestart (lgl); continue; }
      if (!lgldecide (lgl)) return 10;
    } else if (!lglana (lgl)) return 20;
    else if (!(++confs & 15) && lglterminate (lgl)) return 0;
  }
}

static int lglsearch (LGL * lgl, Lim * lim) {
  int res;
  assert (!lgl->searching);
  lgl->searching = 1;
  lglstart (lgl, &lgl->times->search);
  res = lgloop (lgl, lim);
  assert (lgl->searching);
  lgl->searching = 0;
  lglstop (lgl);
  return res;
}

static int lgltopsimp (LGL * lgl, int forcesimp) {
  assert (lgl->state == READY);
  if (lgl->mt) return 20;
  if (lglfailedass (lgl)) return 20;
  if (!lglbcptop (lgl)) return 20;
  if (lgl->mt || lglfailedass (lgl)) return 20;
  if (lglterminate (lgl)) return 0;
  lglshowfeatures (lgl);
  if ((forcesimp || lglsimplimhit (lgl, &forcesimp)) &&
      !lglpreprocessing (lgl, forcesimp)) return 20;
  if (lglfailedass (lgl)) return 20;
  lglrep (lgl, 2, 's');
  return 0;
}

static int lglsolve (LGL * lgl, Lim * lim, int forcesimp) {
  int res;
  lglstart (lgl, &lgl->times->preprocessing);
  res = lgltopsimp (lgl, forcesimp);
  lglstop (lgl);
  if (res) { assert (res == 20); return res; }
  return lglsearch (lgl, lim);
}

static void lglincsetup (LGL * lgl) {

  if (lgl->opts->incsavevisits.val)
    lgl->limits->inc.visits = lgl->stats->visits.search;

  assert (lgl->limits->inc.clauses.add <= lgl->stats->irr.clauses.add);
  if (lgl->limits->inc.clauses.add < lgl->stats->irr.clauses.add) {
    lgl->limits->inc.clauses.add = lgl->stats->irr.clauses.add;
    lgl->elmrtc = lgl->blkrtc = lgl->ccertc = 0;
    lgl->wait = lgl->opts->waitmax.val;
  }

  lgl->limits->inc.clauses.start = lgl->stats->irr.clauses.cur;
  lgl->limits->inc.vars.start = lglrem (lgl);

  lglinitredl (lgl);

  lgl->stats->locs.min = INT_MAX;
  lglupdlocslim (lgl, 0);

  CLR (lgl->limits->restart);
  lgl->limits->restart.confs = lgl->stats->confs;

  if (lgl->opts->incredcint.val > 1) {
    lgl->limits->simp.cinc /= lgl->opts->incredcint.val;
    lglprt (lgl, 1,
       "[incremental-setup] conflict interval increment reduced to %d",
       lgl->limits->simp.cinc);
  }
  if (lgl->opts->incredconfslim.val) {
    lgl->limits->simp.confs =
      ((100-lgl->opts->incredconfslim.val)*lgl->limits->simp.confs)/100;
    lglsethardsimplim (lgl);
    lglprt (lgl, 1,
       "[incremental-setup] conflict limit reduced to %lld (hard %lld)",
       (LGLL) lgl->limits->simp.confs, (LGLL) lgl->limits->simp.hard);
  }

  if (!lgl->limits->simp.itinc)
    lgl->limits->simp.itinc = lgl->opts->simpitintinc.val;
  lgl->limits->simp.its =
    lgl->stats->its.count + lgl->opts->simpitintinc.val;

  if (!lgl->limits->simp.binc)
    lgl->limits->simp.binc = lgl->opts->simpbintinc.val;
  lgl->limits->simp.bin = lgl->stats->bins + lgl->opts->simpbintinc.val;

  if (!lgl->limits->simp.tinc)
    lgl->limits->simp.tinc = lgl->opts->simptintinc.val;
  lgl->limits->simp.trn = lgl->stats->trns + lgl->opts->simptintinc.val;

  lglinitmacd (lgl, &lgl->stats->jlevel,
    lgl->opts->jlevelmacdfast.val,
    lgl->opts->jlevelmacdslow.val,
    lgl->opts->jlevelmacdsmooth.val);

  lglinitema (lgl, &lgl->stats->tlevel, lgl->opts->tlevelema.val);

  lglinitmacd (lgl, &lgl->stats->glue,
    lgl->opts->gluemacdfast.val,
    lgl->opts->gluemacdslow.val,
    lgl->opts->gluemacdsmooth.val);

  lglinitavg (&lgl->stats->avglue);

  lglinitmacd (lgl, &lgl->stats->its.avg,
    lgl->opts->itsmacdfast.val,
    lgl->opts->itsmacdslow.val,
    lgl->opts->itsmacdsmooth.val);

  lglinitema (lgl, &lgl->stats->stability.avg, lgl->opts->stabema.val);

  CLR (lgl->limits->elm.del);
  CLR (lgl->limits->blk.del);

  CLR (lgl->limits->trd.del);
  CLR (lgl->limits->unhd.del);
  CLR (lgl->limits->ternres.del);
  CLR (lgl->limits->cce.del);
  CLR (lgl->limits->card.del);

  CLR (lgl->limits->gauss.del);

  CLR (lgl->limits->prb.simple.del);
  CLR (lgl->limits->prb.basic.del);
  CLR (lgl->limits->prb.treelook.del);

  CLR (lgl->limits->bca.del);
}

static void lglsetup (LGL * lgl) {
  if (lgl->setuponce) goto DONE;
  lgl->limits->dfg = lgl->stats->pshwchs + lgl->opts->defragint.val;

  lgl->limits->blk.irrprgss = -1;
  lgl->limits->elm.irrprgss = -1;
  lgl->limits->term.steps = -1;

  lgl->rng.w = (unsigned) lgl->opts->seed.val;
  lgl->rng.z = ~lgl->rng.w;
  lgl->rng.w <<= 1;
  lgl->rng.z <<= 1;
  lgl->rng.w += 1;
  lgl->rng.z += 1;
  lgl->rng.w *= 2019164533u, lgl->rng.z *= 1000632769u;

  assert (!lgl->stats->decisions);
  lgl->limits->randec += lgl->opts->randecint.val/2;
  lgl->limits->randec += lglrand (lgl) % lgl->opts->randecint.val;

  lgl->limits->simp.vars = lglrem (lgl);

  lgl->setuponce = 1;
  lglchkenv (lgl);
DONE:
  lglinitscores (lgl);
  lglincsetup (lgl);
  TRANS (READY);
}

static void lglinitsolve (LGL * lgl) {
  if (lgl->state != READY) lglsetup (lgl);
  lglredvars (lgl);
  lglfitstk (lgl, &lgl->irr);
#ifndef NCHKSOL
  lglfitstk (lgl, &lgl->orig);
#endif
  lglrep (lgl, 1, '*');
}

static void lgleassign (LGL * lgl, int lit) {
  Ext * ext;
  ext = lglelit2ext (lgl, lit);
  LOG (3, "external assign %d ", lit);
  ext->val = lglsgn (lit);
}

static void lglcomputechanged (LGL * lgl) {
  Ext * ext;
  int eidx;
  lgl->changed = 0;
  for (eidx = 1; eidx <= lgl->maxext; eidx++) {
    ext = lglelit2ext (lgl, eidx);
    if (ext->oldval && ext->oldval != ext->val) lgl->changed++;
    ext->oldval = ext->val;
  }
  LOG (1, "changed %d assignments in extension", lgl->changed);
}

static void lglextend (LGL * lgl) {
  int * p, lit, eidx, ilit, next, satisfied, val, * start, erepr, equiv;
  Ext * ext, * extrepr;
  assert (lgl->state & SATISFIED);
  assert (!(lgl->state & EXTENDED));
  lgleunassignall (lgl);
  for (equiv = 0; equiv <= 1; equiv++) {
    if (equiv)
      LOG (1, "initializing assignment of non-representative externals");
    else
      LOG (1, "initializing assignment of external representatives");
    for (eidx = 1; eidx <= lgl->maxext; eidx++) {
      ext = lglelit2ext (lgl, eidx);
      if (!ext->imported) continue;
      if (equiv != ext->equiv) continue;
      assert (!ext->val);
      if (ext->equiv) {
	erepr = lglerepr (lgl, eidx);
LOG (3, "initializing external %d assignment from external representative %d",
	 eidx, erepr);
	assert (erepr != eidx);
	extrepr = lglelit2ext (lgl, erepr);
	if (!(val = extrepr->val)) {
	  ilit = extrepr->repr;
	  if (ilit) {
	    LOG (3, "using external %d to internal %d mapping",
		 abs (erepr), ilit);
	    val = lglcval (lgl, ilit);
	  } else
LOG (3, "external %d without internal representative", abs (erepr));
	}
	if (erepr < 0) val = -val;
      } else
      if ((ilit = ext->repr)) {
	LOG (3, "using external %d to internal %d mapping", eidx, ilit);
	val = lglcval (lgl, ilit);
      } else {
	LOG (3, "external %d without internal representative", eidx);
	val = 0;
      }
      lit = (val > 0) ? eidx : -eidx;
      lgleassign (lgl, lit);
    }
  }
  start = lgl->extend.start;
  p = lgl->extend.top;
  if (p == start) goto SKIP;
  assert (p > start);
  p--;
  assert (!*p);
  while (p > start) {
#ifndef NLGLOG
    if (lgl->opts->log.val >= 4) {
      int * q;
      for (q = p; q > start && q[-1]; q--)
	;
      LOGCLS (4, q, "next sigma clause to consider");
    }
#endif
    satisfied = 0;
    next = 0;
    do {
      lit = next;
      if (p == start) next = 0; else next = *--p;
      if (!lit || satisfied) continue;
      val = lglederef (lgl, lit);
      assert (!next || val);
      if (val > 0) {
	LOG (4, "sigma clause satisfied by %d", lit);
	satisfied = 1;
      }
    } while (next);
    assert (lit);
    if (satisfied) continue;
    lgleassign (lgl, lit);
  }
SKIP:
  lglcomputechanged (lgl);
  TRANS (EXTENDED);
}

void lglsetphases (LGL * lgl) {
  int elit, phase;
  REQINITNOTFORKED ();
  TRAPI ("setphases");
  REQUIRE (SATISFIED | EXTENDED);
  if (!(lgl->state & EXTENDED)) lglextend (lgl);
  for (elit = 1; elit <= lgl->maxext; elit++) {
    phase = lglederef (lgl, elit);
    assert (abs (phase) <= 1);
    lglesetphase (lgl, elit, phase);
  }
  if (lgl->clone) lglsetphases (lgl->clone);
}

#ifndef NCHKSOL
#include <signal.h>
#include <unistd.h>
static void lglchksol (LGL * lgl) {
  int * p, * c, * eoo = lgl->orig.top, lit, satisfied, sign, idx;
  unsigned bit;
  Ext * ext;
  assert (lglmtstk (&lgl->orig) || !eoo[-1]);
  assert (lgl->state == EXTENDED);
  for (c = lgl->orig.start; c < eoo; c = p + 1) {
    satisfied = 0;
    for (p = c; (lit = *p); p++)
      if (!satisfied && lglederef (lgl, lit) > 0)
	satisfied = 1;
    if (satisfied) continue;
    fflush (stderr);
    lglmsgstart (lgl, 0);
    fprintf (lgl->out, "unsatisfied original external clause");
    for (p = c; (lit = *p); p++) fprintf (lgl->out, " %d", lit);
    lglmsgend (lgl);
    ASSERT (satisfied);
    usleep (1000);
    abort ();	// NOTE: not 'lglabort' on purpose !!
  }
  for (idx = 1; idx <= lgl->maxext; idx++) {
    ext = lglelit2ext (lgl, idx);
    if (!ext->assumed) continue;
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      bit = 1u << (lit < 0);
      if (!(ext->assumed & bit)) continue;
      if (lglederef (lgl, lit) > 0) continue;
      lglprt (lgl, 0, "unsatisfied assumption %d", lit);
      assert (lglederef (lgl, lit) > 0);
      usleep (1000);
      abort ();	// DITO: not 'lglabort' on purpose !!
    }
  }
}
#endif

static void lglclass (LGL * lgl, LGL * from) {
  Ext * extfrom, * extlgl;
  int eidx, cloned;
  REQINITNOTFORKED ();
  ABORTIF (lgl->mt, "can not clone assignment into inconsistent manager");
  ABORTIF (!from, "uninitialized 'from' solver");
  ABORTIF (!(from->state & (SATISFIED | EXTENDED)),
    "require 'from' state to be (SATISFIED | EXTENDED)"); 
  ABORTIF (from->maxext != lgl->maxext,
    "can not clone assignments for different sets of variables");
  if (!(from->state & EXTENDED)) lglextend (from);
  lglreset (lgl);
  lgleunassignall (lgl);
  cloned = lgl->changed = 0;
  for (eidx = 1; eidx <= lgl->maxext; eidx++) {
    extlgl = lglelit2ext (lgl, eidx);
    if (!extlgl->imported) continue;
    extfrom = lglelit2ext (from, eidx);
    ABORTIF (!extfrom->imported, 
      "can not clone assignment of literal imported only by 'to'");
    assert (extfrom->val == 1 || extfrom->val == -1);
    lgleassign (lgl, extfrom->val*eidx);
    cloned++;
  }
  lglcomputechanged (lgl);
  lglprt (lgl, 1, "[class] cloned %d assignments (%d changed)",
          cloned, lgl->changed);
  TRANS (EXTENDED);
#ifndef NCHKSOL
  lglchksol (lgl);
#endif
}

static void lglnegass (LGL * lgl) {
  const int  * p;
  Stk eassume;
  REQINITNOTFORKED ();
  TRAPI ("negass");
  if (lgl->mt) return;
  CLR (eassume);
  for (p = lgl->eassume.start; p < lgl->eassume.top; p++)
    lglpushstk (lgl, &eassume, *p);
  for (p = eassume.start; p < eassume.top; p++)
    lgleadd (lgl, -*p);
  lgleadd (lgl, 0);
  assert (lglmtstk (&lgl->eassume));
  for (p = eassume.start; p < eassume.top; p++)
    lglassume (lgl, *p);
  lglrelstk (lgl, &eassume);
  lgluse (lgl);
  if (lgl->clone) lglnegass (lgl->clone);
}

static int lglcompactify (LGL * lgl, int res) {
  if (!lgl->opts->compact.val) return 0;
  if (!res) return 1;
  if (res == 20) return 1;
  assert (res == 10);
  return lgl->opts->compact.val >= 2;
}

static int lglisat (LGL * lgl, Lim * lim, int simpits) {
  int res, count, reported = lgl->stats->reported;
  lglreset (lgl);
  lglinitsolve (lgl);
  res = lglsolve (lgl, lim, 0);
  for (count = 0; !res && count < simpits; count++) {
    lglprt (lgl, 1,
      "[simplification-%d] next forced simplification iteration %d",
      lgl->stats->simp.count + 1, count + 1);
    res = lglsolve (lgl, lim, 1);
  }
  if (lglcompactify (lgl, res)) lglcompact (lgl);
  if (!res) {
    TRANS (UNKNOWN);
    lglrep (lgl, 1, '?');
  }
  if (res == 10) {
    TRANS (SATISFIED);
    lglrep (lgl, 1, '1');
  }
  if (res == 20) {
    TRANS (UNSATISFIED);
    if (!lgl->level && !lgl->mt) assert (lgl->failed);
    lglrep (lgl, 1, '0');
  }
  if (reported != lgl->stats->reported) lglflshrep (lgl);
  if (res == 10) lglextend (lgl);
#ifndef NCHKSOL
  if (res == 10) lglchksol (lgl);
#endif
  return res;
}

int lglunclone (LGL * lgl, LGL * from) {
  int res;
  REQINITNOTFORKED ();
  if (lgl->mt) return 20;
  ABORTIF (!from, "uninitialized 'from' solver");
  if (from->mt || (from->state & UNSATISFIED)) {
    lglprt (lgl, 1, "[unclone] unsatisfied state");
    lglnegass (lgl);
    res = lglisat (lgl, 0, 0);
  } else if (from->state & (SATISFIED | EXTENDED)) {
    lglprt (lgl, 1, "[unclone] satisfied state");
    lglclass (lgl, from);
    res = 10;
  } else {
    lglprt (lgl, 1, "[unclone] unknown state");
    lglreset (lgl);
    TRANS (UNKNOWN);
    res = 0;
  }
  return res;
}

#define CHKCLONESTATS(STATS) \
do { \
  assert (clone->stats->STATS == orig->stats->STATS); \
} while (0)

static void lglchkclonesamestats (LGL * orig) {
#ifndef NDEBUG
  LGL * clone = orig->clone;
  assert (clone);
  assert (clone->state == orig->state);
  CHKCLONESTATS (confs);
  CHKCLONESTATS (decisions);
  CHKCLONESTATS (bytes.current);
  CHKCLONESTATS (bytes.max);
  CHKCLONESTATS (props.search);
  CHKCLONESTATS (props.simp);
  CHKCLONESTATS (props.lkhd);
  CHKCLONESTATS (visits.search);
  CHKCLONESTATS (visits.simp);
  CHKCLONESTATS (visits.lkhd);
#endif
}

#define CHKCLONE() \
do { \
  if (!lgl->clone) break; \
  lglchkclonesamestats (lgl); \
} while (0)

#define CHKCLONENORES(FUN) \
do { \
  if (!lgl->clone) break; \
  FUN (lgl->clone); \
  CHKCLONE (); \
} while (0)

#define CHKCLONERES(FUN,RES) \
do { \
  int CLONERES; \
  if (!lgl->clone) break; \
  CLONERES = FUN (lgl->clone); \
  ABORTIF (CLONERES != (RES), \
           "%s (lgl->clone) = %d differs from %s (lgl) = %d", \
	   __FUNCTION__, CLONERES, __FUNCTION__, (RES)); \
  CHKCLONE (); \
} while (0)

#define RETURN(FUN,RES) \
do { \
  TRAPI ("return %d", (RES)); \
  CHKCLONERES (FUN, (RES)); \
} while (0)

#define CHKCLONEARGRES(FUN,ARG,RES) \
do { \
  int CLONERES; \
  if (!lgl->clone) break; \
  CLONERES = FUN (lgl->clone, (ARG)); \
  ABORTIF (CLONERES != (RES), \
           "%s (lgl->clone, %d) = %d differs from %s (lgl, %d) = %d", \
	   __FUNCTION__, (ARG), CLONERES, __FUNCTION__, (ARG), (RES)); \
  CHKCLONE (); \
} while (0)

#define RETURNARG(FUN,ARG,RES) \
do { \
  TRAPI ("return %d", (RES)); \
  CHKCLONEARGRES (FUN, (ARG), (RES)); \
} while (0)

static void lglsetlim (LGL * lgl, Lim * lim) {
  int64_t clim, dlim, plim, confs, decs, props, delay, delayed;
  if ((dlim = lgl->opts->dlim.val) < 0) {
    lim->decs = -1;
    lglprt (lgl, 1, "[limits] no decision limit");
  } else {
    decs = lgl->stats->decisions;
    lim->decs = (decs >= LLMAX - dlim) ? LLMAX : decs + dlim;
    lglprt (lgl, 1, "[limits] decision limit %lld after %lld decisions", 
            (LGLL) lim->decs, (LGLL) decs);
  }
  if ((clim = lgl->opts->clim.val) < 0) {
    lim->confs = -1;
    lglprt (lgl, 1, "[limits] no conflict limit");
  } else {
    confs = lgl->stats->confs;
    lim->confs = (confs >= LLMAX - clim) ? LLMAX : confs + clim;
    lglprt (lgl, 1, "[limits] conflict limit %lld after %lld conflicts", 
            (LGLL) lim->confs, (LGLL) confs);
  }
  if ((plim = lgl->opts->plim.val) < 0) {
    lim->props = -1;
    lglprt (lgl, 1, "[limits] no propagation limit");
  } else {
    plim *= 1000;
    props = lgl->stats->props.search;
    lim->props = (props >= LLMAX - plim) ? LLMAX : props + plim;
    lglprt (lgl, 1,
      "[limits] propagation limit %lld after %lld propagations", 
      (LGLL) lim->props, (LGLL) props);
  }
  if ((delay = lgl->opts->simpinitdelay.val) > 0) {
    delayed = lgl->stats->confs + delay;
    if (delayed > lgl->limits->simp.confs) {
      lgl->limits->simp.confs = delayed;
      lglsethardsimplim (lgl);
      lglprt (lgl, 1,
	"[limits] simplification delayed by %lld to %lld conflicts (hard %lld)",
	(LGLL) delay, (LGLL) lgl->limits->simp.confs, (LGLL) lgl->limits->simp.hard);
    } else lglprt (lgl, 1, 
             "[limits] simplification conflict limit already exceeds delay");
  } else lglprt (lgl, 1, 
           "[limits] simplification not delayed since 'simpdelay' zero");
}

int lglsat (LGL * lgl) {
  int res;
  Lim lim;
  REQINITNOTFORKED ();
  TRAPI ("sat");
  lglstart (lgl, &lgl->times->all);
  lgl->stats->calls.sat++;
  ABORTIF (!lglmtstk (&lgl->clause), "clause terminating zero missing");
  lglfreezer (lgl);
  lglsetlim (lgl, &lim);
  res = lglisat (lgl, &lim, 0);
  lglstop (lgl);
  RETURN (lglsat, res);
  return res;
}

int lglookahead (LGL * lgl) {
  int ilit, res;
  REQINITNOTFORKED ();
  TRAPI ("lkhd");
  ABORTIF (!lglmtstk (&lgl->eassume), "imcompatible with 'lglassume'");
  ABORTIF (!lglmtstk (&lgl->clause), "clause terminating zero missing");
  ABORTIF (lgl->opts->druplig.val && lgl->opts->lkhd.val == 2,
    "can not use tree based look ahead while Druplig is enabled");
  lglstart (lgl, &lgl->times->all);
  lglstart (lgl, &lgl->times->lookahead);
  lgl->stats->calls.lkhd++;
  lglreset (lgl);
  assert (!lgl->lkhd);
  lgl->lkhd = 1;
  lglfreezer (lgl);
  if (lgl->level) lglbacktrack (lgl, 0);
  if (!lgl->mt && lglbcp (lgl)) {
    ilit = 0;
    if (lgl->opts->lkhd.val == 2 && !lglsmallirr (lgl))
      ilit = lgljwhlook (lgl);
    else switch (lgl->opts->lkhd.val) {
      case -1: ilit = lglocslook (lgl); break;
      case 0: ilit = lglislook (lgl); break;
      case 1: ilit = lgljwhlook (lgl); break;
      case 2:
	if (!lgltreelookaux (lgl, &ilit)) assert (lgl->mt);
	break;
      case 3:
      default:
        assert (lgl->opts->lkhd.val == 3);
	ilit = lglsumlenlook (lgl);
	break;
    }
    res = (!lgl->mt && ilit) ? lglexport (lgl, ilit) : 0;
    assert (!res || !lglelit2ext (lgl, res)->melted);
  } else lglmt (lgl), res = 0;
  assert (lgl->lkhd);
  lgl->lkhd = 0;
  lglstop (lgl);
  lglstop (lgl);
  TRANS (LOOKED);
  RETURN (lglookahead, res);
  return res;
}

int lglchanged (LGL * lgl) {
  int res;
  REQINITNOTFORKED ();
  TRAPI ("changed");
  REQUIRE (EXTENDED);
  res = lgl->changed;
  RETURN (lglchanged, res);
  return res;
}

int lglsimp (LGL * lgl, int iterations) {
  Lim lim;
  int res;
  REQINITNOTFORKED ();
  TRAPI ("simp %d", iterations);
  ABORTIF (iterations < 0, "negative number of simplification iterations");
  ABORTIF (!lglmtstk (&lgl->clause), "clause terminating zero missing");
  lglstart (lgl, &lgl->times->all);
  lgl->stats->calls.simp++;
  lglfreezer (lgl);
  CLR (lim);
  lim.decs = lgl->stats->decisions;
  res = lglisat (lgl, &lim, iterations);
  assert (!lgl->level);
  lglstop (lgl);
  RETURNARG (lglsimp, iterations, res);
  return res;
}

int lglmaxvar (LGL * lgl) {
  int res;
  REQINITNOTFORKED ();
  TRAPI ("maxvar");
  res = lgl->maxext;
  RETURN (lglmaxvar, res);
  return res;
}

int lglincvar (LGL  *lgl) {
  int res;
  REQINITNOTFORKED ();
  TRAPI ("incvar");
  res = lgl->maxext + 1;
  (void) lglimport (lgl, res);
  RETURN (lglincvar, res);
  return res;
}

int lglderef (LGL * lgl, int elit) {
  int res;
  REQINIT ();
  TRAPI ("deref %d", elit);
  lgl->stats->calls.deref++;
  ABORTIF (!elit, "can not deref zero literal");
  REQUIRE (SATISFIED | EXTENDED);
  if (!(lgl->state & EXTENDED)) lglextend (lgl);
  res = lglederef (lgl, elit);
  RETURNARG (lglderef, elit, res);
  return res;
}

int lglfailed (LGL * lgl, int elit) {
  unsigned bit;
  Ext * ext;
  int res;
  REQINITNOTFORKED ();
  TRAPI ("failed %d", elit);
  lgl->stats->calls.failed++;
  ABORTIF (!elit, "can not check zero failed literal");
  REQUIRE (UNSATISFIED | FAILED);
  ABORTIF (abs (elit) > lgl->maxext,
	   "can not check unimported failed literal");
  ext = lglelit2ext (lgl, elit);
  bit = 1u << (elit < 0);
  ABORTIF (!(ext->assumed & bit),
	   "can not check unassumed failed literal");
  if (!(lgl->state & FAILED)) {
    lglstart (lgl, &lgl->times->all);
    lglanafailed (lgl);
    lglstop (lgl);
  }
  res = (ext->failed & bit) != 0;
  RETURNARG (lglfailed, elit, res);
  return res;
}

int lglinconsistent (LGL * lgl) {
  int res;
  TRAPI ("inconsistent");
  res = (lgl->mt != 0);
  RETURN (lglinconsistent, res);
  return res;
}

static int lglefixed (LGL * lgl, int elit) {
  int res, ilit;
  assert (elit);
  if (abs (elit) > lgl->maxext) return 0;
  ilit = lglimport (lgl, elit);
  if (!ilit) res = 0;
  else if (abs (ilit) == 1) res = ilit;
  else res = lglifixed (lgl , ilit);
  return res;
}

int lglfixed (LGL * lgl, int elit) {
  int res;
  REQINITNOTFORKED ();
  TRAPI ("fixed %d", elit);
  lgl->stats->calls.fixed++;
  ABORTIF (!elit, "can not deref zero literal");
  res = lglefixed (lgl, elit);
  RETURNARG (lglfixed, elit, res);
  return res;
}

int lglrepr (LGL * lgl, int elit) {
  int res, eidx = abs (elit);
  REQINITNOTFORKED ();
  TRAPI ("repr %d", elit);
  lgl->stats->calls.repr++;
  if (eidx > lgl->maxext) res = elit;
  else {
    res = lglerepr (lgl, elit);
    if (abs (res) <= 1) res = elit;
  }
  RETURNARG (lglrepr, elit, res);
  return res;
}

void lglfreeze (LGL * lgl, int elit) {
  Ext * ext;
  REQINITNOTFORKED ();
  TRAPI ("freeze %d", elit);
  lgl->stats->calls.freeze++;
  ABORTIF (!elit, "can not freeze zero literal");
  REQUIRE (UNUSED|OPTSET|USED|RESET|SATISFIED|UNSATISFIED|FAILED|LOOKED|
	   UNKNOWN|EXTENDED);
  LOG (2, "freezing external literal %d", elit);
  (void) lglimport (lgl, elit);
  ext = lglelit2ext (lgl, elit);
  ABORTIF (ext->melted, "freezing melted literal %d", elit);
  assert (!ext->blocking && !ext->eliminated);
  ABORTIF (ext->frozen == INT_MAX, "literal %d frozen too often", elit);
  ext->frozen++;
  if (!ext->frozen) {
    lgl->stats->irrprgss++;
    lglmelter (lgl);
  }
  if (lgl->clone) lglfreeze (lgl->clone, elit);
}

int lglfrozen (LGL * lgl, int elit) {
  Ext * ext;
  int res;
  REQINITNOTFORKED ();
  TRAPI ("frozen %d", elit);
  ABORTIF (!elit, "can not check zero literal for being frozen");
  if (abs (elit) > lgl->maxext) res = INT_MAX;
  else if (!(ext = lglelit2ext (lgl, elit))->imported) res = INT_MAX;
  else res = ext->frozen;
  RETURNARG (lglfrozen, elit, res);
  return res;
}

int lglusable (LGL * lgl, int elit) {
  Ext * ext;
  int res;
  REQINITNOTFORKED ();
  TRAPI ("usable %d", elit);
  ABORTIF (!elit, "can not check zero literal for being usable");
  if (abs (elit) > lgl->maxext) res = 1;
  else if (!(ext = lglelit2ext (lgl, elit))->imported) res = 1;
  else res = !ext->melted;
  RETURNARG (lglusable, elit, res);
  return res;
}

static int lglereusable (LGL * lgl, int elit) {
  Ext * ext;
  int res;
  if (abs (elit) > lgl->maxext) res = 1;
  else if (!(ext = lglelit2ext (lgl, elit))->imported) res = 1;
  else if (ext->blocking) res = 0;
  else if (ext->eliminated) res = 0;
  else if (ext->equiv) res = 0;
  else if (abs (ext->repr) == 1) res = 0;
  else res = 1;
  return res;
}

int lglreusable (LGL * lgl, int elit) {
  int res;
  REQINITNOTFORKED ();
  TRAPI ("reusable %d", elit);
  ABORTIF (!elit, "can not check zero literal for being reusable");
  res = lglereusable (lgl, elit);
  RETURNARG (lglreusable, elit, res);
  return res;
}

void lglreuse (LGL * lgl, int elit) {
  Ext * ext;
  REQINITNOTFORKED ();
  TRAPI ("reuse %d", elit);
  ABORTIF (!elit, "can not reuse zero literal");
  ABORTIF (!lglereusable (lgl, elit), "can not reuse non-reusable literal");
  if (abs (elit) <= lgl->maxext) {
    ext = lglelit2ext (lgl, elit);
    if (ext->imported) {
      assert (!ext->blocking);
      assert (!ext->eliminated);
      if (ext->melted) {
	LOG (2,
	  "forced permanently melted external %d to be reused",
	  elit);
	ext->melted = 0;
	lglmelter (lgl);
      }
    }
  }
  if (lgl->clone) lglreuse (lgl->clone, elit);
}

void lglmeltall (LGL * lgl) {
  int idx, melted;
  Ext * ext;
  REQINITNOTFORKED ();
  TRAPI ("meltall");
  melted = 0;
  for (idx = 1; idx <= lgl->maxext; idx++) {
    ext = lglelit2ext (lgl, idx);
    ext->melted = 0;
    if (!ext->frozen) continue;
    lgl->stats->irrprgss++;
    ext->frozen = 0;
    melted++;
  }
  lglprt (lgl, 1, "[meltall] melted %d frozen literals", melted);
  lglmelter (lgl);
  if (lgl->clone) lglmeltall (lgl->clone);
}

void lglmelt (LGL * lgl, int elit) {
  Ext * ext;
  REQINITNOTFORKED ();
  TRAPI ("melt %d", elit);
  lgl->stats->calls.melt++;
  ABORTIF (!elit, "can not melt zero literal");
  REQUIRE (UNUSED|OPTSET|USED|RESET|
	   SATISFIED|UNSATISFIED|FAILED|UNKNOWN|LOOKED|
	   EXTENDED);
  LOG (2, "melting external literal %d", elit);
  (void) lglimport (lgl, elit);
  ext = lglelit2ext (lgl, elit);
  ABORTIF (!ext->frozen, "can not melt fully unfrozen literal %d", elit);
  assert (!ext->blocking && !ext->eliminated);
  ext->frozen--;
  lglmelter (lgl);	// TODO guard  by !ext->frozen?
  if (lgl->clone) lglmelt (lgl->clone, elit);
}

void lglreconstk (LGL * lgl, int ** startptr, int ** toptr) {
  REQINITNOTFORKED ();
  TRAPI ("reconstk");
  lglfitstk (lgl, &lgl->extend);	// 'lglcompact' -> 'lglclone'!!
  if (startptr) *startptr = lgl->extend.start;
  if (toptr) *toptr = lgl->extend.top;
  if (lgl->clone) lglreconstk (lgl->clone, 0, 0);
}

static void lglprstart (LGL * lgl) {
  assert (lgl->prefix);
  fputs (lgl->prefix, lgl->out);
  if (lgl->tid >= 0) fprintf (lgl->out, "%d ", lgl->tid);
}

static void lglprs (LGL * lgl, const char * fmt, ...) {
  va_list ap;
  lglprstart (lgl);
  va_start (ap, fmt);
  vfprintf (lgl->out, fmt, ap);
  va_end (ap);
  fputc ('\n', lgl->out);
}

static void lglprsline (LGL * lgl) {
  lglprstart (lgl);
  fputc ('\n', lgl->out);
}

static double lglsqr (double a) { return a*a; }

static void lglgluestats (LGL * lgl) {
  int64_t added, reduced, retired, forcing, resolved, conflicts;
  int64_t wadded, wreduced, wretired, wforcing, wresolved, wconflicts;
  int64_t avgadded, avgreduced, avgretired, avgforcing, avgresolved, avgconflicts;
  double madded, mreduced, mretired, mforcing, mresolved, mconflicts;
  double vadded, vreduced, vretired, vforcing, vresolved, vconflicts;
  double sadded, sreduced, sretired, sforcing, sresolved, sconflicts;
  Stats * s = lgl->stats;
  int glue, maxglue;
  lglprs (lgl,
    "scaled glue%11s %3s %9s %3s %9s %3s %9s %3s %9s %3s %9s %7s",
    "added","", "reduced","", "retired","",
    "forcing","", "resolved","", "conflicts", "maxmb");
  added = reduced = retired = forcing = resolved = conflicts = 0;
  wadded = wreduced = wretired = wforcing = wresolved = wconflicts = 0;
  for (glue = 0; glue <= MAXGLUE; glue++) {
    added += s->lir[glue].added;
    reduced += s->lir[glue].reduced;
    retired += s->lir[glue].retired;
    forcing += s->lir[glue].forcing;
    resolved += s->lir[glue].resolved;
    conflicts += s->lir[glue].conflicts;
    wadded += glue*s->lir[glue].added;
    wreduced += glue*s->lir[glue].reduced;
    wretired += glue*s->lir[glue].retired;
    wforcing += glue*s->lir[glue].forcing;
    wresolved += glue*s->lir[glue].resolved;
    wconflicts += glue*s->lir[glue].conflicts;
  }
  avgadded = added ? (((10*wadded)/added+5)/10) : 0;
  avgreduced = reduced ? (((10*wreduced)/reduced+5)/10) : 0;
  avgretired = retired ? (((10*wretired)/retired+5)/10) : 0;
  avgforcing = forcing ? (((10*wforcing)/forcing+5)/10) : 0;
  avgresolved = resolved ? (((10*wresolved)/resolved+5)/10) : 0;
  avgconflicts = conflicts ? (((10*wconflicts)/conflicts+5)/10) : 0;
  lglprsline (lgl);
  lglprs (lgl,
    "all %14lld %13lld %13lld %13lld %13lld %13lld",
     (LGLL) added,
     (LGLL) reduced,
     (LGLL) retired,
     (LGLL) forcing,
     (LGLL) resolved,
     (LGLL) conflicts);
  lglprsline (lgl);
  if (lgl->opts->verbose.val < 2) {
    for (maxglue = MAXGLUE; maxglue >= 1; maxglue--)
      if (s->lir[maxglue].added) break;
    if (maxglue + 1 == MAXGLUE) maxglue = MAXGLUE;
  } else maxglue = MAXGLUE;
  for (glue = 0; glue <= maxglue; glue++) {
    lglprs (lgl,
      "%2d %-5d %9lld %3.0f%c%9lld %3.0f%c%9lld %3.0f%c%9lld %3.0f%c%9lld %3.0f%c%9lld %3.0f%c %6.1f",
      glue,
      lglunscaleglue (lgl, glue),
      (LGLL) s->lir[glue].added,
	lglpcnt (s->lir[glue].added, added),
	(glue == avgadded) ? '<' : ' ',
      (LGLL) s->lir[glue].reduced,
	lglpcnt (s->lir[glue].reduced, reduced),
	(glue == avgreduced) ? '<' : ' ',
      (LGLL) s->lir[glue].retired,
	lglpcnt (s->lir[glue].retired, retired),
	(glue == avgretired) ? '<' : ' ',
      (LGLL) s->lir[glue].forcing,
	lglpcnt (s->lir[glue].forcing, forcing),
	(glue == avgforcing) ? '<' : ' ',
      (LGLL) s->lir[glue].resolved,
	lglpcnt (s->lir[glue].resolved, resolved),
	(glue == avgresolved) ? '<' : ' ',
      (LGLL) s->lir[glue].conflicts,
	lglpcnt (s->lir[glue].conflicts, conflicts),
	(glue == avgconflicts) ? '<' : ' ',
	s->lir[glue].maxbytes/(double)(1<<20));
  }
  lglprsline (lgl);

  madded = lglavg (wadded, added),
  mreduced = lglavg (wreduced, reduced),
  mretired = lglavg (wretired, retired),
  mforcing = lglavg (wforcing, forcing),
  mresolved = lglavg (wresolved, resolved),
  mconflicts = lglavg (wconflicts, conflicts);

  lglprs (lgl,
    "avg  %19.1f%14.1f%14.1f%14.1f%14.1f%14.1f",
     madded, mreduced, mretired, mforcing, mresolved, mconflicts);

  vadded = vreduced = vretired = vforcing = vresolved = vconflicts = 0;
  for (glue = 0; glue <= MAXGLUE; glue++) {
    vadded += s->lir[glue].added * lglsqr (glue - madded);
    vreduced += s->lir[glue].reduced * lglsqr (glue - mreduced);
    vretired += s->lir[glue].retired * lglsqr (glue - mretired);
    vforcing += s->lir[glue].forcing * lglsqr (glue - mforcing);
    vresolved += s->lir[glue].resolved * lglsqr (glue - mresolved);
    vconflicts += s->lir[glue].conflicts * lglsqr (glue - mconflicts);
  }
  sadded = sqrt (lglavg (vadded, added));
  sreduced = sqrt (lglavg (vreduced, reduced));
  sretired = sqrt (lglavg (vretired, retired));
  sforcing = sqrt (lglavg (vforcing, forcing));
  sresolved = sqrt (lglavg (vresolved, resolved));
  sconflicts = sqrt (lglavg (vconflicts, conflicts));

  lglprs (lgl,
    "std  %19.1f%14.1f%14.1f%14.1f%14.1f%14.1f",
     sadded, sreduced, sretired, sforcing, sresolved, sconflicts);
}

typedef struct TN { double t; const char * n; } TN;

static int lglcmptn (const TN * a, const TN * b) {
  if (a->t > b->t) return -1;
  if (a->t < b->t) return 1;
  return strcmp (a->n, b->n);
}

#define INSTN(NAME,FIELD) \
do { \
  TN * tn; \
  if (lglignprofptr (lgl, &ts->FIELD)) break; \
  tn = tns + ntns++; \
  ASSERT (ntns <= sztns); \
  tn->t = ts->FIELD; \
  tn->n = #NAME; \
} while (0)

static void lglprofsort (LGL * lgl) {
  int i, ntns, nimportant, nprint;
  Times * ts = lgl->times;
  const int sztns = 100;
  TN tns[sztns];
  double sum;

  ntns = 0;

  INSTN (analysis, analysis);
  INSTN (backward, backward);
  INSTN (bca, bca);
  INSTN (block, block);
  INSTN (bump, bump);
  INSTN (card, card);
  INSTN (cce, cce);
  INSTN (decide, decide);
  INSTN (decompose, decompose);
  INSTN (defrag, defrag);
  INSTN (druplig, druplig);
  INSTN (elim, elim);
  INSTN (gauss, gauss);
  INSTN (gc, gc);
  INSTN (heapdecision, heapdecision);
  INSTN (locs, locs);
  INSTN (mincls, mincls);
  INSTN (phase, phase);
  INSTN (probe, probe);
  INSTN (quatres1, quatres1);
  INSTN (quatres2, quatres2);
  INSTN (quatres, quatres);
  INSTN (queuedecision, queuedecision);
  INSTN (queuesort, queuesort);
  INSTN (redcls, redcls);
  INSTN (reduce, reduce);
  INSTN (restart, restart);
  INSTN (showfeatures, showfeatures);
  INSTN (showscoredist, showscoredist);
  INSTN (subl, subl);
  INSTN (sweep, sweep);
  INSTN (ternres, ternres);
  INSTN (transred, transred);
  INSTN (unhide, unhide);

  // Force insertion sort to avoid implicit memory allocation!
  // Otherwise an already existing memory corruption will trigger
  // another signal and thus might result in non-termination.

  ISORT (TN, lglcmptn, tns, ntns);

  sum = 0;
  assert (ntns > 3);
  for (nimportant = ntns-1; nimportant > 3; nimportant--) {
    sum += tns[nimportant].t;
    if (lglpcnt (sum, ts->all) >= 1.0) break;
  }
  if (nimportant == ntns - 1) nimportant++;

  if (!lgl->opts->profilelong.val && lgl->opts->verbose.val < 2)
    nprint = nimportant;
  else nprint = ntns;

  for (i = 0; i < nprint; i++) {
    if (i == nimportant) {
      if (i) lglprs (lgl, "");
      lglprs (lgl, "%8.3f < 1%% rest (below)", sum);
      if (i + 1 < nprint) lglprs (lgl, "");
    }
    lglprs (lgl, "%8.3f %3.0f%% %s",
      tns[i].t, lglpcnt (tns[i].t, ts->all), tns[i].n);
  }

  if (nimportant == nprint && nprint < ntns) {
    if (nprint) lglprs (lgl, "");
    lglprs (lgl, "%8.3f < 1%% rest (not shown)", sum);
  }
}

static void lglprof (LGL * lgl) {
  Times * ts = lgl->times;
  double t = ts->all, simp, search;

  assert (lgl->opts->verbose.val >= 0);
  simp = ts->preprocessing + ts->inprocessing;
  if (!lgl->opts->verbose.val || !lgl->opts->profile.val) goto SHORT;

  lglprofsort (lgl);

  if (!lglignprofptr (lgl, &ts->prb.simple) &&
      (lgl->opts->profilelong.val ||
       lgl->opts->verbose.val >= 2 ||
       ts->prb.simple || ts->prb.basic || ts->prb.treelook)) {
    lglprs (lgl, "----------------------------------");
    lglprs (lgl, "%8.3f %3.0f%% probe simple    %3.0f%%",
      ts->prb.simple,
      lglpcnt (ts->prb.simple, t),
      lglpcnt (ts->prb.simple, ts->probe));
    lglprs (lgl, "%8.3f %3.0f%% probe basic     %3.0f%%",
      ts->prb.basic,
      lglpcnt (ts->prb.basic, t),
      lglpcnt (ts->prb.basic, ts->probe));
    lglprs (lgl, "%8.3f %3.0f%% probe tree-look %3.0f%%",
      ts->prb.treelook,
      lglpcnt (ts->prb.treelook, t),
      lglpcnt (ts->prb.treelook, ts->probe));
  }
  lglprs (lgl, "==================================");
  lglprs (lgl, "%8.3f %3.0f%% preprocessing   %3.0f%%",
    ts->preprocessing,
    lglpcnt (ts->preprocessing, t),
    lglpcnt (ts->preprocessing, simp));
  lglprs (lgl, "%8.3f %3.0f%% inprocessing    %3.0f%%",
    ts->inprocessing,
    lglpcnt (ts->inprocessing, t),
    lglpcnt (ts->inprocessing, simp));
  lglprs (lgl, "==================================");
SHORT:
  lglprs (lgl, "%8.3f %3.0f%% simplifying", simp, lglpcnt (simp, t));
  if (lgl->stats->calls.lkhd)
    lglprs (lgl, "%8.3f %3.0f%% lookahead",
      ts->lookahead, lglpcnt (ts->lookahead, t));
  search = ts->search - ts->inprocessing;
  lglprs (lgl, "%8.3f %3.0f%% search", search, lglpcnt (search, t));
  lglprs (lgl, "==================================");
  lglprs (lgl, "%8.3f %3.0f%% all", t, 100.0);
}

void lglstats (LGL * lgl) {
  long long visits, min, p, steps, sum;
  int remaining, removed;
  Stats * s;
  double t;
  REQINITNOTFORKED ();
  if (lgl->opts->verbose.val < 0) return;
  lglflushtimers (lgl);
  s = lgl->stats;
  t = lgl->times->all;
  p = s->props.search + s->props.simp + s->props.lkhd;
  if (!lgl->opts->verbose.val) goto SHORT;

  lglprs (lgl, "agil: %.2f%% agility",
    100.0 * (s->agility / (double) (1ll << 32)));

  sum = s->prb.basic.ate.trnr + s->prb.basic.ate.lrg;
  lglprs (lgl, 
    "bate: %lld basic ate = %d trn %.0f%% + %d lrg %.0f%% in %d updates",
    sum, s->prb.basic.ate.trnr, lglpcnt (s->prb.basic.ate.trnr, sum),
    s->prb.basic.ate.lrg, lglpcnt (s->prb.basic.ate.lrg, sum),
    s->prb.basic.ate.count);

  lglprs (lgl,
    "bcas: %d count, %lld added (%lld skipped), %lld steps",
    s->bca.count, (LGLL) s->bca.added, s->bca.skipped, (LGLL) s->bca.steps);

  lglprs (lgl,
    "bkwd: tried %lld clauses, %lld lits, %.2f lits/clause",
    (LGLL) s->bkwd.tried.clauses, (LGLL) s->bkwd.tried.lits,
    lglavg (s->bkwd.tried.lits, s->bkwd.tried.clauses));
  lglprs (lgl,
    "bkwd: checked %lld occs, %.2f occs/clause, %.2f occs/lit",
    (LGLL) s->bkwd.tried.occs,
    lglavg (s->bkwd.tried.occs, s->bkwd.tried.clauses),
    lglavg (s->bkwd.tried.occs, s->bkwd.tried.lits));
  lglprs (lgl,
    "bkwd: subsumed %d binary, %d ternary, %d large",
    s->bkwd.sub2, s->bkwd.sub3, s->bkwd.subl);
  lglprs (lgl,
    "bkwd: strengthened %d binary, "
    "%d ternary (%.0f%% self), %d large (%.0f%% self)",
    s->bkwd.str2,
    s->bkwd.str3, lglpcnt (s->bkwd.str3self, s->bkwd.str3),
    s->bkwd.strl, lglpcnt (s->bkwd.strlself, s->bkwd.strl));

  lglprs (lgl,
    "blkd: %d bces, %d removed, %lld resolutions, %lld steps",
    s->blk.count, s->blk.clauses, (LGLL) s->blk.res, (LGLL) s->blk.steps);
  lglprs (lgl,
    "blkd: %d blocking literals %.0f%%, %d pure",
    s->blk.lits, lglpcnt (s->blk.lits, 2*lgl->maxext), s->blk.pure);

  lglprs (lgl,
    "bump: %lld bumped seen, %lld lits %.1f on average",
    s->bump.count,
    (LGLL) s->bump.lits,
    lglavg (s->bump.lits, s->bump.count));

  lglprs (lgl,
    "card: %d count, %d units, %d am1, %lld steps",
    s->card.count, s->card.units, s->card.expam1, (LGLL) s->card.steps);
  lglprs (lgl,
    "card: %d rescheduled, %lld eliminated, %lld resolved, %lld subsumed",
    s->card.resched, (LGLL) s->card.eliminated,
    (LGLL) s->card.resolved, (LGLL) s->card.subsumed);
  lglprs (lgl,
    "card: %d at-most-one constraints found, average size %.2f",
    s->card.found.am1.total.cnt,
    lglavg (s->card.found.am1.total.sum, s->card.found.am1.total.cnt));
  lglprs (lgl,
    "card: %d at-most-one constraints used %.0f%%, average size %.2f",
    s->card.used.am1.cnt,
    lglpcnt (s->card.used.am1.cnt, s->card.found.am1.total.cnt),
    lglavg (s->card.used.am1.sum, s->card.used.am1.cnt));
  lglprs (lgl,
    "card: %d at-most-two constraints found, average size %.2f",
    s->card.found.am2.total.cnt,
    lglavg (s->card.found.am2.total.sum, s->card.found.am2.total.cnt));
  lglprs (lgl,
    "card: %d at-most-two constraints used %.0f%%, average size %.2f",
    s->card.used.am2.cnt,
    lglpcnt (s->card.used.am2.cnt, s->card.found.am2.total.cnt),
    lglavg (s->card.used.am2.sum, s->card.used.am2.cnt));

  lglprs (lgl,
    "cces: %d cces, %d eliminated, %d ate %.0f%%, %d abce %.0f%%",
    s->cce.count, s->cce.eliminated,
    s->cce.ate, lglpcnt (s->cce.ate, s->cce.eliminated),
    s->cce.abce, lglpcnt (s->cce.abce, s->cce.eliminated));
  lglprs (lgl,
    "cces: %lld probed, %d lifted, %d failed",
    (LGLL) s->cce.probed, s->cce.lifted, s->cce.failed);
  lglprs (lgl,
    "cces: %lld cached, %lld rsz, %lld cols %.0f%%, "
    "%lld srch, %lld hits %.0f%%",
    (LGLL) s->cce.cache.ins,
    (LGLL) s->cce.cache.rsz,
    (LGLL) s->cce.cache.cols,
      lglpcnt (s->cce.cache.cols, s->cce.cache.ins),
    (LGLL) s->cce.cache.search,
    (LGLL) s->cce.cache.hits,
      lglpcnt (s->cce.cache.hits, s->cce.cache.search));

  lglprs (lgl,
    "clls: %lld sat, %lld simp, %lld freeze, %lld melt",
    (LGLL) s->calls.sat, (LGLL) s->calls.simp,
    (LGLL) s->calls.freeze, (LGLL) s->calls.melt);
  lglprs (lgl,
    "clls: %lld add, %lld assume, %lld deref, %lld failed",
    (LGLL) s->calls.add, (LGLL) s->calls.assume,
    (LGLL) s->calls.deref, (LGLL) s->calls.failed);
  lglprs (lgl,
    "clls: %lld lkhd, %lld cassume, %lld mosat",
    (LGLL) s->calls.lkhd, (LGLL) s->calls.cassume, (LGLL) s->calls.mosat);

  lglprs (lgl,
    "coll: %d gcs, %d rescored clauses, %d rescored vars",
    s->gcs, s->rescored.clauses, s->rescored.vars);

  lglprs (lgl,
    "dcps: %d decompositions, %d equivalent %.0f%%",
	  s->decomps, s->equiv.sum, lglpcnt (s->equiv.sum, lgl->maxext));

  lglprs (lgl,
    "deco: %lld decision-only clauses %.0f%%, %.0f%% reduction",
    s->mincls.deco, lglpcnt (s->mincls.deco, s->clauses.learned),
    lglpcnt (s->deco.sum.orig - s->deco.sum.red, s->deco.sum.orig)); 

  lglprs (lgl,
    "decs: %lld total, %lld rnd %.3f%%, %lld heap %.3f%, %lld queue %.3f%%",
    (LGLL) s->decisions,
    (LGLL) s->randecs, lglpcnt (s->randecs, s->decisions),
    (LGLL) s->hdecs, lglpcnt (s->hdecs, s->decisions),
    (LGLL) s->qdecs, lglpcnt (s->qdecs, s->decisions));

  lglprs (lgl,
    "elms: %d elims, %d eliminated %.0f%%, %d pure %.0f%%",
     s->elm.count,
     s->elm.elmd, lglpcnt (s->elm.elmd, lgl->maxext),
     s->elm.pure, lglpcnt (s->elm.pure, s->elm.elmd));
  lglprs (lgl,
    "elms: %d rounds, %.1f rounds/bve",
    s->elm.rounds, lglavg (s->elm.rounds, s->elm.count));
  lglprs (lgl,
    "elms: %d small %.0f%%, %d large %.0f%%",
    s->elm.small.elm, lglpcnt (s->elm.small.elm, s->elm.elmd),
    s->elm.large, lglpcnt (s->elm.large, s->elm.elmd));
  lglprs (lgl,
    "elms: %d tried small, %d succeeded %.0f%%, %d failed %.0f%%",
    s->elm.small.tried, s->elm.small.tried - s->elm.small.failed,
      lglpcnt (s->elm.small.tried - s->elm.small.failed, s->elm.small.tried),
    s->elm.small.failed,
      lglpcnt (s->elm.small.failed, s->elm.small.tried));
  lglprs (lgl,
    "elms: %d subsumed, %d strengthened, %d blocked",
    s->elm.sub, s->elm.str, s->elm.blkd);
  lglprs (lgl,
    "elms: %lld copies, %lld resolutions, %lld ipos",
    (LGLL) s->elm.copies, (LGLL) s->elm.resolutions, (LGLL) s->elm.ipos);
  lglprs (lgl,
    "elms: %lld subchks, %lld strchks",
    (LGLL) s->elm.subchks, (LGLL) s->elm.strchks);

  lglprs (lgl,
    "gaus: %lld extractions, %lld extracted, %.1f size, %d max",
    s->gauss.count, s->gauss.extracted,
    lglavg (s->gauss.arity.sum, s->gauss.extracted.total),
    s->gauss.arity.max);
  lglprs (lgl,
    "gaus: exported %d units, %d binary and %d ternary equations",
    s->gauss.units, s->gauss.equivs, s->gauss.trneqs);
  steps = s->gauss.steps.extr + s->gauss.steps.extr;
  lglprs (lgl,
    "gaus: %d gc, %lld steps, %lld extr %.0f%%, %lld elim %.0f%%",
    s->gauss.gcs, (LGLL) steps,
    s->gauss.steps.extr, lglpcnt (s->gauss.steps.extr, steps),
    s->gauss.steps.elim, lglpcnt (s->gauss.steps.elim, steps));

  lglprs (lgl,
    "glue: %.1f orig avg, %.1f real avg, %.1f scaled avg",
    lglavg (s->clauses.glue, s->clauses.learned),
    lglavg (s->clauses.realglue, s->clauses.learned),
    lglavg (s->clauses.scglue, s->clauses.learned));
  lglprs (lgl,
    "glue: %lld maxscaledglue=%d (%.0f%%), %lld kept %.0f%%",
    (LGLL) s->clauses.maxglue.count, MAXGLUE,
    lglpcnt (s->clauses.maxglue.count, s->clauses.learned),
    (LGLL) s->clauses.maxglue.kept,
    lglpcnt (s->clauses.maxglue.kept, s->clauses.learned));

  lglprs (lgl,
    "hbrs: %d = %d simple %.0f%% + %d trn %.0f%% + %d lrg %.0f%%, %d sub %.0f%%",
    s->hbr.cnt,
    s->hbr.simple, lglpcnt (s->hbr.simple, s->hbr.cnt),
    s->hbr.trn, lglpcnt (s->hbr.trn, s->hbr.cnt),
    s->hbr.lrg, lglpcnt (s->hbr.lrg, s->hbr.cnt),
    s->hbr.sub, lglpcnt (s->hbr.sub, s->hbr.cnt));

  lglprs (lgl,
    "locs: %d count, %lld flips, %lld mems, %d minimun",
    s->locs.count, (LGLL) s->locs.flips, (LGLL) s->locs.mems, s->locs.min);

  assert (s->lits.nonmin >= s->lits.learned);
  min = s->lits.nonmin - s->lits.learned;
  lglprs (lgl,
    "lrnd: %lld clauses, %.1f length",
    (LGLL) s->clauses.learned,
    lglavg (s->lits.learned, s->clauses.learned));
  lglprs (lgl,
    "lrnd: %lld lits = %lld orig - %lld removed %.0f%%",
    (LGLL) s->lits.learned,
    (LGLL) s->lits.nonmin,
    (LGLL) min, lglpcnt (min, s->lits.nonmin));
  lglprs (lgl,
    "lrnd: %lld uips %.0f%%, %lld flips %.0f%%",
    (LGLL) s->uips, lglpcnt (s->uips, s->clauses.learned),
    (LGLL) s->decflipped, lglpcnt (s->decflipped, s->clauses.learned));

  sum = s->mincls.min + s->mincls.bin + s->mincls.size + s->mincls.deco;
  lglprs (lgl,
    "mins: %lld mins %.0f%%, %lld bin %.0f%%, %lld size %.0f%%",
    (LGLL) s->mincls.min, lglpcnt (s->mincls.min, sum),
    (LGLL) s->mincls.bin, lglpcnt (s->mincls.bin, sum),
    (LGLL) s->mincls.size, lglpcnt (s->mincls.size, sum),
    (LGLL) s->mincls.deco, lglpcnt (s->mincls.deco, sum));
  lglprs (lgl,
    "mins: %lld poisoned searches, %lld hits, %.0f%% hit rate",
    (LGLL) s->mincls.poison.search, (LGLL) s->mincls.poison.hits,
    lglpcnt (s->mincls.poison.hits, s->mincls.poison.search));
  lglprs (lgl,
    "mins: %lld used twice searches, %lld hits, %.0f%% hit rate",
    (LGLL) s->mincls.usedtwice.search, (LGLL) s->mincls.usedtwice.hits,
    lglpcnt (s->mincls.usedtwice.hits, s->mincls.usedtwice.search));

  sum = s->moved.bin + s->moved.trn;
  lglprs (lgl,
    "move: moved %lld, %lld bin %.0f%%, %lld trn %.0f%%",
    sum,
    (LGLL) s->moved.bin, lglpcnt (s->moved.bin, sum),
    (LGLL) s->moved.trn, lglpcnt (s->moved.trn, sum));

  sum = s->otfs.str.red + s->otfs.str.irr;
  assert (sum == s->otfs.str.bin + s->otfs.str.trn + s->otfs.str.lrg);
  lglprs (lgl,
    "otfs: %lld driving %.0f%%, %lld restarting %.0f%%",
    (LGLL) s->otfs.driving, lglpcnt (s->otfs.driving, sum),
    (LGLL) s->otfs.restarting, lglpcnt (s->otfs.restarting, sum));
  lglprs (lgl,
    "otfs: str %lld, %lld red %.0f%%, %lld irr %.0f%%",
    sum,
    (LGLL) s->otfs.str.red, lglpcnt (s->otfs.str.red, sum),
    (LGLL) s->otfs.str.irr, lglpcnt (s->otfs.str.irr, sum));
  lglprs (lgl,
    "otfs: str %lld, %lld bin %.0f%%, %lld trn %.0f%%, %lld lrg %.0f%%",
    sum,
    (LGLL) s->otfs.str.bin, lglpcnt (s->otfs.str.bin, sum),
    (LGLL) s->otfs.str.trn, lglpcnt (s->otfs.str.trn, sum),
    (LGLL) s->otfs.str.lrg, lglpcnt (s->otfs.str.lrg, sum));

  sum = s->otfs.sub.red + s->otfs.sub.irr;
  assert (sum == s->otfs.total);
  assert (sum == s->otfs.sub.bin + s->otfs.sub.trn + s->otfs.sub.lrg);
  lglprs (lgl,
    "otfs: sub %lld, %lld red %.0f%%, %lld irr %.0f%%",
    sum,
    (LGLL) s->otfs.sub.red, lglpcnt (s->otfs.sub.red, sum),
    (LGLL) s->otfs.sub.irr, lglpcnt (s->otfs.sub.irr, sum));
  lglprs (lgl,
    "otfs: sub %lld, %lld bin %.0f%%, %lld trn %.0f%%, %lld lrg %.0f%%",
    sum,
    (LGLL) s->otfs.sub.bin, lglpcnt (s->otfs.sub.bin, sum),
    (LGLL) s->otfs.sub.trn, lglpcnt (s->otfs.sub.trn, sum),
    (LGLL) s->otfs.sub.lrg, lglpcnt (s->otfs.sub.lrg, sum));

  lglprs (lgl,
    "phas: %lld computed, %lld set, %lld pos (%.0f%%), %lld neg (%.0f%%)",
    (LGLL) s->phase.count, (LGLL) s->phase.set,
    (LGLL) s->phase.pos, lglpcnt (s->phase.pos, s->phase.set),
    (LGLL) s->phase.neg, lglpcnt (s->phase.neg, s->phase.set));

  lglprs (lgl,
    "prbs: %d basic, %lld probed, %d failed, %d lifted",
    s->prb.basic.count, (LGLL) s->prb.basic.probed,
    s->prb.basic.failed, s->prb.basic.lifted);
  lglprs (lgl,
    "prbs: %d simple, %lld probed, %d failed, %d eqs",
    s->prb.simple.count, (LGLL) s->prb.simple.probed,
    s->prb.simple.failed, s->prb.simple.eqs);
  lglprs (lgl,
    "prbs: %d treelook, %lld probed, %d failed, %d lifted",
    s->prb.treelook.count, (LGLL) s->prb.treelook.probed,
    s->prb.treelook.failed, s->prb.treelook.lifted);

  lglprs (lgl,
    "prom: %lld locked %.0f%% out of %lld tried",
    (LGLL) s->promote.locked,
    lglpcnt (s->promote.locked, s->promote.tried),
    (LGLL) s->promote.tried);

  lglprs (lgl,
    "prps: %lld props, %.0f props/dec",
    (LGLL) p, lglavg (s->props.search, s->decisions));
  lglprs (lgl,
    "prps: %.0f%% srch, %.0f%% simp, %.0f%% lkhd",
    lglpcnt (s->props.search, p), lglpcnt (s->props.simp, p),
    lglpcnt (s->props.lkhd, p));

  lglprs (lgl,
    "quat: %d count, %lld quat, %lld self1, %lld self2, %lld dup",
    s->quatres.count,
    (LGLL) s->quatres.quat,
    (LGLL) s->quatres.self1,
    (LGLL) s->quatres.self2,
    (LGLL) s->quatres.dup);
 
  lglprs (lgl,
    "queu: %lld flushed, %lld sorted, %lld decisions %.3f%%",
    (LGLL) s->queue.flushed, (LGLL) s->queue.sorted,
    (LGLL) s->qdecs, lglpcnt (s->qdecs, s->decisions));

  lglprs (lgl,
    "redc: %lld clauses %.0f%%, %lld tried %.0f%%, %lld sat %.0f%%",
    (LGLL) s->redcls.cls.red,
      lglpcnt (s->redcls.cls.red, s->redcls.cls.tried),
    (LGLL) s->redcls.cls.tried,
      lglpcnt (s->redcls.cls.tried, s->confs),
    (LGLL) s->redcls.cls.sat,
      lglpcnt (s->redcls.cls.sat, s->redcls.cls.tried));
  lglprs (lgl,
    "redc: %lld lits %.0f%%, %lld tried %.0f%%, %lld sat %.0f%%",
    (LGLL) s->redcls.lits.red,
      lglpcnt (s->redcls.lits.red, s->redcls.lits.tried),
    (LGLL) s->redcls.lits.tried,
      lglpcnt (s->redcls.lits.tried, s->lits.nonmin),
    (LGLL) s->redcls.lits.sat,
      lglpcnt (s->redcls.lits.sat, s->redcls.lits.tried));
  lglprs (lgl,
    "redc: %lld times jump level reduced, %.1f levels on average",
    (LGLL) s->redcls.jlevel.red,
    lglavg (s->redcls.jlevel.sum, s->redcls.jlevel.red));

  lglprs (lgl,
    "reds: %d count, %.1f conflicts per reduce",
    s->reduced.count, lglavg (s->confs, s->reduced.count));
  lglprs (lgl,
    "reds: %d memlim %.0f%%, %d arith %.0f%%",
    s->reduced.memlim, lglpcnt (s->reduced.memlim, s->reduced.count),
    s->reduced.arith, lglpcnt (s->reduced.arith, s->reduced.count));
  sum = s->reduced.collected + s->reduced.retired;
  lglprs (lgl,
    "reds: %lld collected %.0f%%, %lld retired %.0f%%",
    s->reduced.collected, lglpcnt (s->reduced.collected, sum),
    s->reduced.retired, lglpcnt (s->reduced.retired, sum));

  lglprs (lgl,
    "rmbd: %d removed, %d red %.0f%%",
    s->bindup.removed, s->bindup.red,
    lglpcnt (s->bindup.red, s->bindup.removed));

  lglprs (lgl,
    "rsts: %lld restarts %.0f%% of checked, %lld skipped %.0f%%",
    (LGLL) s->restarts.count,
      lglpcnt (s->restarts.count, s->restarts.checked),
    (LGLL) s->restarts.skipped,
      lglpcnt (s->restarts.skipped, s->restarts.checked));
  lglprs (lgl,
    "rsts: %lld checks %.0f%%, %lld forced %.0f%%",
    (LGLL) s->restarts.checked,
      lglpcnt (s->restarts.checked, s->confs),
    (LGLL) s->restarts.forced,
      lglpcnt (s->restarts.forced, s->restarts.checked));
  lglprs (lgl,
    "rsts: %lld not forced (%.0f%% of checked, %.0f%% of skipped)",
    (LGLL) s->restarts.notforced,
      lglpcnt (s->restarts.notforced, s->restarts.checked),
      lglpcnt (s->restarts.notforced, s->restarts.skipped));
  lglprs (lgl,
    "rsts: %lld agile %.0f%% of skipped, %lld delayed %.0f%%",
    (LGLL) s->restarts.agile,
      lglpcnt (s->restarts.agile, s->restarts.skipped),
    (LGLL) s->restarts.delayed,
      lglpcnt (s->restarts.delayed, s->restarts.skipped));
  lglprs (lgl,
    "rsts: %lld blocked %.2f%% restart, %lld reused %.0f%%",
    (LGLL) s->restarts.blocked,
      lglpcnt (s->restarts.blocked, s->restarts.count),
    (LGLL) s->restarts.reused,
      lglpcnt (s->restarts.reused, s->restarts.skipped));
  lglprs (lgl,
    "rsts: %lld partial reuse %.1f%% of restarts, kept %.1f%%",
    (LGLL) s->restarts.kept.count,
    lglpcnt (s->restarts.kept.count, s->restarts.count),
    lglavg (s->restarts.kept.sum, s->restarts.kept.count));
  lglprs (lgl,
    "rsts: %lld delta %.1f avg, %lld penalty %.1f avg",
    (LGLL) s->restarts.delta.delta,
      lglavg (s->restarts.delta.delta, s->restarts.delta.count),
    (LGLL) s->restarts.delta.pen,
      lglavg (s->restarts.delta.pen, s->restarts.delta.count));

  lglprs (lgl,
    "scic: %lld set, %.1f%% min, %.1f%% max",
    (LGLL) s->setscincf.count,
    s->setscincf.min/10.0, s->setscincf.max/10.0);

  lglprs (lgl,
    "simp: %d count, %d confs %0.f%%, %d vars %.0f%%",
    s->simp.count,
    s->simp.limhit.confs, lglpcnt (s->simp.limhit.confs, s->simp.count),
    s->simp.limhit.vars, lglpcnt (s->simp.limhit.vars, s->simp.count));
  lglprs (lgl,
    "simp: %d its %0.f%%, %d bin %.0f%%, %d trns %.0f%%",
    s->simp.limhit.its, lglpcnt (s->simp.limhit.its, s->simp.count),
    s->simp.limhit.bin, lglpcnt (s->simp.limhit.bin, s->simp.count),
    s->simp.limhit.trn, lglpcnt (s->simp.limhit.trn, s->simp.count));

   lglprs (lgl,
    "subl: %lld count (%lld tried %.1f), %lld sub out of %lld (%.1f%%)",
    s->subl.count, s->subl.tried, lglavg (s->subl.tried, s->subl.count),
    s->subl.sub, s->subl.cands, lglpcnt (s->subl.sub, s->subl.cands));

  lglprs (lgl,
    "swps: %d count, %lld rounds, %lld queries (%.1f/round)",
    s->sweep.count, (LGLL) s->sweep.rounds, (LGLL) s->sweep.queries.total,
    lglavg (s->sweep.queries.total, s->sweep.rounds));
  lglprs (lgl,
    "swps: %lld sat calls, %lld unsat (%.1f%% success rate)",
    s->sweep.sat,
    s->sweep.unsat, lglavg (s->sweep.confs, s->sweep.sat));
  lglprs (lgl,
    "swps: %lld decisions %.1f, %lld conflicts %.1f",
    (LGLL) s->sweep.decs, lglavg (s->sweep.decs, s->sweep.sat),
    (LGLL) s->sweep.confs, lglavg (s->sweep.confs, s->sweep.sat));
  lglprs (lgl,
    "swps; %.1f avg class size, %.1f avg environment size",
    lglavg (s->sweep.sumsize.classes, s->sweep.queries.total),
    lglavg (s->sweep.sumsize.envs, s->sweep.sat));
  lglprs (lgl,
    "swps: %d failed, %d impls, %d equivs",
    s->sweep.failed, s->sweep.impls, s->sweep.equivs);

  lglprs (lgl,
    "swp0: %lld type 0 queries, %lld unsat (%.1f%%), %lld sat (%.1f%%)",
    (LGLL) s->sweep.queries.type[0].count,
    (LGLL) s->sweep.queries.type[0].unsat,
    lglpcnt (s->sweep.queries.type[0].unsat, s->sweep.queries.type[0].count),
    (LGLL) s->sweep.queries.type[0].sat,
    lglpcnt (s->sweep.queries.type[0].sat, s->sweep.queries.type[0].count));
  lglprs (lgl,
    "swp1: %lld type 1 queries, %lld unsat (%.1f%%), %lld sat (%.1f%%)",
    (LGLL) s->sweep.queries.type[1].count,
    (LGLL) s->sweep.queries.type[1].unsat,
    lglpcnt (s->sweep.queries.type[1].unsat, s->sweep.queries.type[1].count),
    (LGLL) s->sweep.queries.type[1].sat,
    lglpcnt (s->sweep.queries.type[1].sat, s->sweep.queries.type[1].count));
  lglprs (lgl,
    "swp2: %lld type 2 queries, %lld unsat (%.1f%%), %lld sat (%.1f%%)",
    (LGLL) s->sweep.queries.type[2].count,
    (LGLL) s->sweep.queries.type[2].unsat,
    lglpcnt (s->sweep.queries.type[2].unsat, s->sweep.queries.type[2].count),
    (LGLL) s->sweep.queries.type[2].sat,
    lglpcnt (s->sweep.queries.type[2].sat, s->sweep.queries.type[2].count));

  lglprs (lgl,
    "sync: %lld produced units, %lld successful consumptions %.0f%%",
    s->sync.units.produced, s->sync.units.consumed.actual,
    lglpcnt (s->sync.units.consumed.actual, s->sync.units.produced));
  lglprs (lgl,
    "sync: %lld consume units calls, %lld tried %.0f%%, %lld success %.0f%%",
    s->sync.units.consumed.calls,
    s->sync.units.consumed.tried,
    lglpcnt (s->sync.units.consumed.tried, s->sync.units.consumed.calls),
    s->sync.units.consumed.actual,
    lglpcnt (s->sync.units.consumed.actual, s->sync.units.consumed.calls));
  lglprs (lgl,
    "sync: %lld produced clauses, %lld successful consumptions %.0f%%",
    s->sync.cls.produced, s->sync.cls.consumed.actual,
    lglpcnt (s->sync.cls.consumed.actual, s->sync.cls.produced));
  lglprs (lgl,
    "sync: %lld consume clause calls, %lld tried %.0f%%, %lld success %.0f%%",
    s->sync.cls.consumed.calls,
    s->sync.cls.consumed.tried,
    lglpcnt (s->sync.cls.consumed.tried, s->sync.cls.consumed.calls),
    s->sync.cls.consumed.actual,
    lglpcnt (s->sync.cls.consumed.actual, s->sync.cls.consumed.calls));

  lglprs (lgl, "time: %lld calls to obtain time", (LGLL) s->times);

  lglprs (lgl,
    "tops: %d fixed %.0f%%, %d its, %.2f confs/it",
    s->fixed.sum, lglpcnt (s->fixed.sum, lgl->maxext), 
    s->its.count, lglavg (s->confs, s->its.count));

  lglprs (lgl,
    "trds: %d transitive reductions, %d removed, %d failed",
    s->trd.count, s->trd.red, s->trd.failed);
  lglprs (lgl,
    "trds: %lld nodes, %lld edges, %lld steps",
    (LGLL) s->trd.lits, (LGLL) s->trd.bins, (LGLL) s->trd.steps);

  lglprs (lgl, "trim: %lld words, %.1f MB",
    (LGLL) s->trims, (s->trims * sizeof (int)) / (double)(1<<20));

  lglprs (lgl,
    "trnr: %d count, %d bin, %d trn, %lld steps",
    s->ternres.count, s->ternres.bin,
    s->ternres.trn, (LGLL) s->ternres.steps);

  lglprs (lgl,
    "unhd: %d count, %d rounds, %lld steps",
    s->unhd.count, s->unhd.rounds, (LGLL) s->unhd.steps);
  lglprs (lgl,
    "unhd: %d non-trivial sccs of average size %.1f",
    s->unhd.stamp.sccs,
    lglavg (s->unhd.stamp.sumsccsizes, s->unhd.stamp.sccs));
  sum = lglunhdunits (lgl);
  lglprs (lgl,
    "unhd: %lld units, %d bin, %d trn, %d lrg",
    sum, s->unhd.units.bin, s->unhd.units.trn, s->unhd.units.lrg);
  sum = lglunhdfailed (lgl);
  lglprs (lgl,
    "unhd: %lld failed, %d stamp, %d lits, %d bin, %d trn, %d lrg",
    sum, s->unhd.stamp.failed, s->unhd.failed.lits,
    s->unhd.failed.bin, s->unhd.failed.trn, s->unhd.units.lrg);
  sum = lglunhdtauts (lgl);
  lglprs (lgl,
    "unhd: %lld tauts, %d bin %.0f%%, %d trn %.0f%%, %d lrg %.0f%%",
    sum,
    s->unhd.tauts.bin, lglpcnt (s->unhd.tauts.bin, sum),
    s->unhd.tauts.trn, lglpcnt (s->unhd.tauts.trn, sum),
    s->unhd.tauts.lrg, lglpcnt (s->unhd.tauts.lrg, sum));
  lglprs (lgl,
    "unhd: %lld tauts, %d stamp %.0f%%, %d red %.0f%%",
    sum,
    s->unhd.stamp.trds, lglpcnt (s->unhd.stamp.trds, sum),
    s->unhd.tauts.red, lglpcnt (s->unhd.tauts.red, sum));
  sum = lglunhdhbrs (lgl);
  lglprs (lgl,
    "unhd: %lld hbrs, %d trn %.0f%%, %d lrg %.0f%%, %d red %.0f%%",
    sum,
    s->unhd.hbrs.trn, lglpcnt (s->unhd.hbrs.trn, sum),
    s->unhd.hbrs.lrg, lglpcnt (s->unhd.hbrs.lrg, sum),
    s->unhd.hbrs.red, lglpcnt (s->unhd.hbrs.red, sum));
  sum = lglunhdstrd (lgl);
  lglprs (lgl,
    "unhd: %lld str, %d bin %.0f%%, %d trn %.0f%%, %d lrg %.0f%%, %d red %.0f%%",
    sum,
    s->unhd.units.bin, lglpcnt (s->unhd.units.bin, sum),
    s->unhd.str.trn, lglpcnt (s->unhd.str.trn, sum),
    s->unhd.str.lrg, lglpcnt (s->unhd.str.lrg, sum),
    s->unhd.str.red, lglpcnt (s->unhd.str.red, sum));

  removed = s->fixed.sum + s->elm.elmd + s->equiv.sum;
  remaining = lgl->maxext - removed;
  assert (remaining >= 0);
  lglprs (lgl,
    "vars: %d remaining %.0f%% and %d removed %.0f%% out of %d",
    remaining, lglpcnt (remaining, lgl->maxext),
    removed, lglpcnt (removed, lgl->maxext), lgl->maxext);
  lglprs (lgl,
    "vars: %d fixed %.0f%%, %d eliminated %.0f%%, %d equivalent %.0f%%",
    s->fixed.sum, lglpcnt (s->fixed.sum, lgl->maxext),
    s->elm.elmd, lglpcnt (s->elm.elmd, lgl->maxext),
    s->equiv.sum, lglpcnt (s->equiv.sum, lgl->maxext));

  visits = s->visits.search + s->visits.simp + s->visits.lkhd;
  lglprs (lgl,
    "vsts: %lld visits, %.0f%% srch, %.0f%% simp, %.0f%% lkhd",
    (LGLL) visits, lglpcnt (s->visits.search, visits),
    lglpcnt (s->visits.simp, visits), lglpcnt (s->visits.lkhd, visits));
  lglprs (lgl,
    "vsts: %.1f search visits per propagation, %.1f per conflict",
    lglavg (s->visits.search, s->props.search),
    lglavg (s->visits.search, s->confs));

  lglprs (lgl,
    "wchs: %lld pushed, %lld enlarged, %d defrags",
    (LGLL) s->pshwchs, (LGLL) s->enlwchs, s->defrags);

  lglprsline (lgl);
  lglgluestats (lgl);
  lglprsline (lgl);

#ifndef NLGLDRUPLIG
  if (lgl->druplig) {
    druplig_stats (lgl->druplig, lgl->out);
    lglprsline (lgl);
  }
#endif

SHORT:
  lglprof (lgl);
  lglprsline (lgl);
  lglprs (lgl,
    "%13lld conflicts,    %10.1f confs/sec",
    (LGLL) s->confs, lglavg (s->confs, t));
  lglprs (lgl,
    "%13lld ternaries,    %10.1f confs/ternary",
    (LGLL) s->trns, lglavg (s->confs, s->trns));
  lglprs (lgl,
    "%13lld binaries,     %10.1f confs/binary",
    (LGLL) s->bins, lglavg (s->confs, s->bins));
  lglprs (lgl,
    "%13lld iterations,   %10.1f confs/iteration",
    (LGLL) s->its.count, lglavg (s->confs, s->its.count));
  lglprsline (lgl);
  lglprs (lgl,
    "%13lld reductions,   %10.1f redus/sec, %8.1f confs/reduction",
    (LGLL) s->reduced.count,
    lglavg (s->reduced.count, t), lglavg (s->confs, s->reduced.count));
  lglprs (lgl,
    "%13lld restarts,     %10.1f rests/sec, %8.1f confs/restart",
    (LGLL) s->restarts.count,
    lglavg (s->restarts.count, t), lglavg (s->confs, s->restarts.count));
  lglprs (lgl,
    "%13lld decisions,    %10.1f decis/sec, %8.1f decis/conflict",
    (LGLL) s->decisions,
    lglavg (s->decisions, t), lglavg (s->decisions, s->confs));
  lglprs (lgl,
    "%13lld propagations, %10.1f props/sec, %8.1f props/decision",
    (LGLL) p, lglavg (p, t), lglavg (p, s->decisions));
  lglprsline (lgl);
  lglprs (lgl, "%.1f seconds, %.1f MB", t, lglmaxmb (lgl));
  fflush (lgl->out);
}

int64_t lglgetprops (LGL * lgl) {
  REQINITNOTFORKED ();
  return lgl->stats->props.search + lgl->stats->props.simp;
}

int64_t lglgetconfs (LGL * lgl) {
  REQINITNOTFORKED ();
  return lgl->stats->confs;
}

int64_t lglgetdecs (LGL * lgl) {
  REQINITNOTFORKED ();
  return lgl->stats->decisions;
}

void lglsizes (LGL * lgl) {
  lglprt (lgl, 0, "sizeof (int) == %ld", (long) sizeof (int));
  lglprt (lgl, 0, "sizeof (unsigned) == %ld", (long) sizeof (unsigned));
  lglprt (lgl, 0, "sizeof (void*) == %ld", (long) sizeof (void*));
  lglprt (lgl, 0, "sizeof (Stk) == %ld", (long) sizeof (Stk));
  lglprt (lgl, 0, "sizeof (Fun) == %ld", (long) sizeof (Fun));
  lglprt (lgl, 0, "sizeof (AVar) == %ld", (long) sizeof (AVar));
  lglprt (lgl, 0, "sizeof (DVar) == %ld", (long) sizeof (DVar));
  lglprt (lgl, 0, "sizeof (QVar) == %ld", (long) sizeof (QVar));
  lglprt (lgl, 0, "sizeof (EVar) == %ld", (long) sizeof (EVar));
  lglprt (lgl, 0, "sizeof (Stats.lir) == %ld", (long) sizeof ((Stats*)0)->lir);
  lglprt (lgl, 0, "sizeof (Stats) == %ld", (long) sizeof (Stats));
  lglprt (lgl, 0, "sizeof (LGL) == %ld", (long) sizeof (LGL));
  lglprt (lgl, 0, "MAXVAR == %ld", (long) MAXVAR);
  lglprt (lgl, 0, "MAXREDLIDX == %ld", (long) MAXREDLIDX);
  lglprt (lgl, 0, "MAXIRRLIDX == %ld", (long) MAXIRRLIDX);
}

#define LGLRELSTK(MGR,STKPTR) \
do { \
  assert (lglmtstk (STKPTR)); \
  lglrelstk ((MGR), (STKPTR)); \
} while (0)

void lglrelease (LGL * lgl) {
  lgldealloc dealloc;
  int i;

  REQINIT ();
  if (lgl->clone) lglrelease (lgl->clone), lgl->clone = 0;
  TRAPI ("release");

#ifndef NLGLDRUPLIG
  if (lgl->druplig) druplig_reset (lgl->druplig), lgl->druplig = 0;
#endif

  // Heap state starts here:

  DEL (lgl->avars, lgl->szvars);
  DEL (lgl->doms, 2*lgl->szvars);
  DEL (lgl->drail, lgl->szdrail);
  DEL (lgl->dvars, lgl->szvars);
  DEL (lgl->ext, lgl->szext);
  DEL (lgl->i2e, lgl->szvars);
  DEL (lgl->jwh, 2*lgl->szvars);
  DEL (lgl->qvars, lgl->szvars);
  DEL (lgl->vals, lgl->szvars);

  lglrelctk (lgl, &lgl->control);

  lglrelstk (lgl, &lgl->assume);
#ifndef NDEBUG
  lglrelstk (lgl, &lgl->prevclause);
#endif
  lglrelstk (lgl, &lgl->clause);
  lglrelstk (lgl, &lgl->dsched);
  lglrelstk (lgl, &lgl->queue.stk);
  lglrelstk (lgl, &lgl->eassume);
  lglrelstk (lgl, &lgl->eclause);
  lglrelstk (lgl, &lgl->extend);
  lglrelstk (lgl, &lgl->learned);
  lglrelstk (lgl, &lgl->frames);
  lglrelstk (lgl, &lgl->promote);
  lglrelstk (lgl, &lgl->trail);
  lglrelstk (lgl, &lgl->wchs->stk);

#ifndef NCHKSOL
  lglrelstk (lgl, &lgl->orig);
#endif

  lglrelstk (lgl, &lgl->irr);
  for (i = 0; i <= MAXGLUE; i++) lglrelstk (lgl, &lgl->red[i]);

  // The following heap allocated memory has no state:

  LGLRELSTK (lgl, &lgl->lcaseen);
  LGLRELSTK (lgl, &lgl->resolvent);
  LGLRELSTK (lgl, &lgl->minstk);
  LGLRELSTK (lgl, &lgl->poisoned);
  LGLRELSTK (lgl, &lgl->seen);

  lglrelstk (lgl, &lgl->saved.bin);
  lglrelstk (lgl, &lgl->saved.trn);

  DEL (lgl->limits, 1);
  DEL (lgl->times, 1);
  DEL (lgl->timers, 1);
  DEL (lgl->red, MAXGLUE+1);
  DEL (lgl->wchs, 1);

  if (lgl->fltstr) DEL (lgl->fltstr, 1);
  if (lgl->cbs) DEL (lgl->cbs, 1);		// next to last
  lgldelstr (lgl, lgl->prefix);			// last

  // adjust upfront the mem counters ...

  lgldec (lgl, sizeof *lgl->stats);
  lgldec (lgl, sizeof *lgl->opts);
  lgldec (lgl, sizeof *lgl->mem);
  lgldec (lgl, sizeof *lgl);

  assert (getenv ("LGLEAK") || !lgl->stats->bytes.current);

  if (lgl->closeapitrace == 1) fclose (lgl->apitrace);
  if (lgl->closeapitrace == 2) pclose (lgl->apitrace);

  if ((dealloc = lgl->mem->dealloc)) {
     void * memstate = lgl->mem->state;
     if (lgl->stats) dealloc (memstate, lgl->stats, sizeof *lgl->stats);
     if (lgl->times) dealloc (memstate, lgl->times, sizeof *lgl->times);
     if (lgl->opts) dealloc (memstate, lgl->opts, sizeof *lgl->opts);
     assert (lgl->mem);
     dealloc (memstate, lgl->mem, sizeof *lgl->mem);
     dealloc (memstate, lgl, sizeof *lgl);
  } else {
    free (lgl->stats);
    free (lgl->times);
    free (lgl->opts);
    free (lgl->mem);
    free (lgl);
  }
}

void lglutrav (LGL * lgl, void * state, void (*trav)(void *, int)) {
  int elit, val;
  REQINITNOTFORKED ();
  if (!lgl->mt && !lglbcp (lgl)) lglmt (lgl);
  if (!lgl->mt) lglgc (lgl);
  if (lgl->mt) return;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  for (elit = 1; elit <= lgl->maxext; elit++) {
    if (!(val = lglefixed (lgl, elit))) continue;
    trav (state, (val < 0) ? -elit : elit);
  }
}

void lgletrav (LGL * lgl, void * state, void (*trav)(void *, int, int)) {
  int elit, erepr;
  REQINITNOTFORKED ();
  if (!lgl->mt && !lglbcp (lgl)) lglmt (lgl);
  if (!lgl->mt) lglgc (lgl);
  if (lgl->mt) return;
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  for (elit = 1; elit <= lgl->maxext; elit++) {
    if (lglefixed (lgl, elit)) continue;
    erepr = lglerepr (lgl, elit);
    if (erepr == elit) continue;
    trav (state, elit, erepr);
  }
}

static void lglictrav (LGL * lgl, int internal,
                       void * state, void (*trav)(void *, int)) {
  int idx, sign, lit, blit, tag, red, other, other2;
  const int * p, * w, * eow, * c;
  HTS * hts;
  REQINITNOTFORKED ();
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  if (!lgl->mt && !lglbcp (lgl)) lglmt (lgl);
  if (!lgl->mt) lglgc (lgl);
  if (lgl->mt) { trav (state, 0); return; }
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      assert (!lglval (lgl, lit));
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (red) continue;
	if (tag != BINCS && tag != TRNCS) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	assert (!lglval (lgl, other));
	if (tag == TRNCS) {
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  assert (!lglval (lgl, other2));
	} else other2 = 0;
	trav (state, internal ? lit : lglexport (lgl, lit));
	trav (state, internal ? other : lglexport (lgl, other));
	if (other2) trav (state, internal ? other2 : lglexport (lgl, other2));
	trav (state, 0);
      }
    }
  for (c = lgl->irr.start; c < lgl->irr.top; c = p + 1) {
    p = c;
    if (*p >= NOTALIT) continue;
    while ((other = *p)) {
      assert (!lglval (lgl, other));
      trav (state, internal ? other : lglexport (lgl, other));
      p++;
    }
    trav (state, 0);
  }
}

void lglctrav (LGL * lgl, void * state, void (*trav)(void *, int)) {
  lglictrav (lgl, 0, state, trav);
}

static void lgltravcounter (void * voidptr, int lit) {
  int * cntptr = voidptr;
  if (!lit) *cntptr += 1;
}

static void lgltravprinter (void * voidptr, int lit) {
  FILE * out = voidptr;
  if (lit) fprintf (out, "%d ", lit);
  else fprintf (out, "0\n");
}

void lglprint (LGL * lgl, FILE * file) {
  int count = 0;
  lglctrav (lgl, &count, lgltravcounter);
  fprintf (file, "p cnf %d %d\n", lglmaxvar (lgl), count);
  lglctrav (lgl, file, lgltravprinter);
}

void lglprintall (LGL * lgl, FILE * file) {
  int count = 0;
  lgltravall (lgl, &count, lgltravcounter);
  fprintf (file, "p cnf %d %d\n", lglmaxvar (lgl), count);
  lgltravall (lgl, file, lgltravprinter);
}

void lglrtrav (LGL * lgl, void * state, void (*trav)(void *, int, int)) {
  int idx, sign, lit, blit, tag, red, other, other2, glue;
  const int * p, * c, * w, * eow;
  Stk * lir;
  HTS * hts;
  REQINITNOTFORKED ();
  if (lgl->mt) return;
  lglgc (lgl);
  if (lgl->level > 0) lglbacktrack (lgl, 0);
  for (idx = 2; idx < lgl->nvars; idx++) {
    if (lglval (lgl, idx)) continue;
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (!red) continue;
	if (tag != BINCS && tag != TRNCS) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	assert (!lglval (lgl, other));
	if (tag == TRNCS) {
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  assert (!lglval (lgl, other2));
	} else other2 = 0;
	trav (state, lglexport (lgl, lit), 0);
	trav (state, lglexport (lgl, other), 0);
	if (other2) trav (state, lglexport (lgl, other2), 0);
	trav (state, 0, 0);
      }
    }
  }
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    for (c = lir->start; c < lir->top; c = p + 1) {
      p = c;
      if (*p >= NOTALIT) continue;
      while ((other = *p)) {
	assert (!lglval (lgl, other));
	trav (state, lglexport (lgl, other), 0);
	p++;
      }
      trav (state, 0, 0);
    }
  }
}

static void lgltravallu (void * voidptr, int unit) {
  Trv * state = voidptr;
  state->trav (state->state, unit);
  state->trav (state->state, 0);
}

static void lgltravalle (void * voidptr, int lit, int repr) {
  Trv * state = voidptr;
  state->trav (state->state, -lit);
  state->trav (state->state, repr);
  state->trav (state->state, 0);
  state->trav (state->state, lit);
  state->trav (state->state, -repr);
  state->trav (state->state, 0);
}

void lgltravall (LGL * lgl, void * state, void (*trav)(void *, int)) {
  Trv travstate;
  travstate.state = state;
  travstate.trav = trav;
  lglutrav (lgl, &travstate, lgltravallu);
  lgletrav (lgl, &travstate, lgltravalle);
  lglctrav (lgl, state, trav);
}

#ifndef NDEBUG

void lgldump (LGL * lgl) {
  int idx, sign, lit, blit, tag, red, other, other2, glue;
  const int * p, * w, * eow, * c, * top;
  Stk * lir;
  HTS * hts;
  for (idx = 2; idx < lgl->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = lglhts (lgl, lit);
      w = lglhts2wchs (lgl, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == BINCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  other2 = 0;
	} else if (tag == TRNCS) {
	  other = blit >> RMSHFT;
	  if (abs (other) < idx) continue;
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	} else continue;
	fprintf (lgl->out, "%s %d %d", red ? "red" : "irr", lit, other);
	if (tag == TRNCS) fprintf (lgl->out, " %d", other2);
	fprintf (lgl->out, "\n");
      }
    }
  top = lgl->irr.top;
  for (c = lgl->irr.start; c < top; c = p + 1) {
    p = c;
    if (*p >= NOTALIT) continue;
    fprintf (lgl->out, "irr");
    while (*p) fprintf (lgl->out, " %d", *p++);
    fprintf (lgl->out, "\n");
  }
  for (glue = 0; glue < MAXGLUE; glue++) {
    lir = lgl->red + glue;
    top = lir->top;
    for (c = lir->start; c < top; c = p + 1) {
      p = c;
      if (*p >= NOTALIT) continue;
      fprintf (lgl->out, "glue%d", glue);
      while (*p) fprintf (lgl->out, " %d", *p++);
      fprintf (lgl->out, "\n");
    }
  }
}

#endif

static void lglforkadd (void * ptr, int lit) {
  lgladd (ptr, lit ? lglforklit (lit) : 0);
}

LGL * lglfork (LGL * parent) {
  LGL * child;
  {
    LGL * lgl = parent;
    REQINIT ();
    ABORTIF (!lglmtstk (&parent->eassume), "can not fork under assumptions");
    ABORTIF (parent->forked == INT_MAX, "parent forked too often");
  }
  if (parent->level > 0) lglbacktrack (parent, 0);
  (void) lglbcp (parent);
  lglgc (parent);
  child = lglminit (parent->mem->state,
                    parent->mem->alloc,
                    parent->mem->realloc,
                    parent->mem->dealloc);
  child->parent = parent;
  memcpy (child->opts, parent->opts, sizeof *parent->opts);
  lglcopyclonenfork (child, parent);
  lglictrav (parent, 1, child, lglforkadd);
  assert (parent->stats->irr.clauses.cur == child->stats->irr.clauses.cur);
  parent->forked++;
  assert (parent->forked > 0);
  lglprt (parent, 1, "forked-%d", parent->forked);
  return child;
}

static void lglflass (LGL * lgl, LGL * from) {
  int idx, copied = 0;
  assert (!lgl->level), assert (!lgl->mt);
  assert ((from->state & (SATISFIED | EXTENDED)));
  if (lgl->nvars) assert (lgl->nvars == from->maxext + 2);
  else assert (!from->maxext);
  lglreset (lgl);
  for (idx = 2; idx < lgl->nvars; idx++) {
    int val = lglderef (from, idx-1);
    int lit = val < 0 ? -idx : idx;
    lgldassume (lgl, lit);
    copied++;
  }
  lglprt (lgl, 1, "[flass] copied %d internal assignments", copied);
  TRANS (SATISFIED);
  lglextend (lgl);
#ifndef NCHKSOL
  lglchksol (lgl);
#endif
}

int lgljoin (LGL * parent, LGL * child) {
  int res;
  {
    LGL * lgl = parent;
    ABORTIF (!parent, "uninitialized parent manager");
    ABORTIF (!child, "uninitialized child manager");
    ABORTIF (!parent->forked, "parent manager not forked");
    ABORTIF (!child->parent, "child manager has not parent");
    ABORTIF (child->parent != parent, "child manager has different parent");
    ABORTIF (!lglmtstk (&child->eassume),
      "child manager with assumptions not supported yet");
  }
  if (child->mt || (child->state & UNSATISFIED)) {
#ifndef NLGLOG
    LGL * lgl = parent;
#endif
    assert (child->mt);				  // no assumptions yet ...
    lglprt (parent, 1, "[join] unsatisfied state");
    if (!parent->mt) {
      LOG (1, "joining empty clause");
      parent->mt = 1;
    } else LOG (1, "no need to join empty clause since parent has one");
    res = 20;
  } else if (child->state & (SATISFIED | EXTENDED)) {
    lglprt (parent, 1, "[join] satisfied state");
    lglflass (parent, child);
    res = 10;
  } else {
    lglprt (parent, 1, "[join] unknown state");
    lglreset (parent);
    {
      LGL * lgl = parent;
      TRANS (UNKNOWN);
    }
    res = 0;
  }
  return res;
}
