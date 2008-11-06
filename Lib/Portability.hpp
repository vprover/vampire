#ifndef __PORTABILITY__
#define __PORTABILITY__

#ifdef _LP64
#define ARCH_X64
#elif _M_X64
//this should handle MS C++ compiler
#define ARCH_X64
#else
#define ARCH_X86
#endif

#endif /*__PORTABILITY__*/
