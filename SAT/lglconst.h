#ifndef lglconst_h_INCLUDED
#define lglconst_h_INCLUDED

#include <limits.h>

#define REMOVED		INT_MAX
#define NOTALIT		((INT_MAX >> RMSHFT))
#define MAXVAR		((INT_MAX >> RMSHFT) - 2)

#define GLUESHFT	4
#define POW2GLUE	(1 << GLUESHFT)
#define MAXGLUE		(POW2GLUE - 1)
#define GLUEMASK	(POW2GLUE - 1)
#define MAXREDLIDX	((1 << (31 - GLUESHFT)) - 2)
#define MAXIRRLIDX	((1 << (31 - RMSHFT)) - 2)

#define MAXLDFW		31	
#define REPMOD 		22

#define FUNVAR		12
#define FUNQUADS	(1<<(FUNVAR - 6))
#define FALSECNF	(1ll<<32)
#define TRUECNF		0ll

#define FLTPRC 		32
#define EXPMIN 		(0x0000 ## 0000)
#define EXPZRO 		(0x1000 ## 0000)
#define EXPMAX		(0x7fff ## ffff)
#define MNTBIT		(0x0000 ## 0001 ## 0000 ## 0000 ## ull)
#define MNTMAX		(0x0000 ## 0001 ## ffff ## ffff ## ull)
#define FLTMIN		(0x0000 ## 0000 ## 0000 ## 0000 ## ll)
#define FLTMAX		(0x7fff ## ffff ## ffff ## ffff ## ll)

#define DEFSCOREXP	500

#define LLMAX		(0x7fff ## ffff ## ffff ## ffff ## ll)

#define MAXFLTSTR	6
#define MAXPHN		10

#endif
