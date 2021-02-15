#ifndef ALLOC_HPP
#define ALLOC_HPP

#include <cstdlib>
#include <new>

namespace SMTSubsumption {


inline void* subsat_alloc(std::size_t size)
{
#ifdef SUBSAT_STANDALONE
  void* p = std::malloc(size);
#else
  void* p = ALLOC_UNKNOWN(size, "subsat");
#endif
  if (!p && size > 0) {
    throw std::bad_alloc();
  }
  return p;
}

inline void subsat_dealloc(void* p)
{
#ifdef SUBSAT_STANDALONE
  std::free(p);
#else
  DEALLOC_UNKNOWN(p, "subsat");
#endif
}


} // namespace SMTSubsumption

#endif /* !ALLOC_HPP */
