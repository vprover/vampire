/**
 * @file BitUtils.hpp
 * Defines class BitUtils.
 */


#ifndef __BitUtils__
#define __BitUtils__

namespace Lib {

class BitUtils
{
  static void zeroMemory(void* ptr, size_t bytes)
  {
    size_t* sptr=static_cast<size_t*>(ptr);
    while(bytes>=sizeof(sptr)) {
      *(sptr++)=0;
      bytes-=sizeof(sptr);
    }
    char* cptr=reinterpret_cast<char*>(sptr);
    while(bytes) {
      *(cptr++)=0;
      bytes--;
    }
  }

  inline
  static bool getBitValue(void* ptr, size_t index)
  {
    unsigned char* cptr=static_cast<unsigned char*>(ptr)+index/8;
    return ((*cptr)>>(index&7))&1;
  }
  inline
  static void setBitValue(void* ptr, size_t index, bool value)
  {
    unsigned char* cptr=static_cast<unsigned char*>(ptr)+index/8;
    if(value) {
      *cptr|=1<<(index&7);
    } else {
      *cptr&=~(1<<(index&7));
    }
  }
};

};

#endif /* __BitUtils__ */
