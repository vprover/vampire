
#include "Theory.hpp"
#if WITH_GMP
#include "Theory_gmp.cpp"
#else
#include "Theory_int.cpp"
#endif
