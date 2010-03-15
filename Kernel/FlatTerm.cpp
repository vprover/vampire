/**
 * @file FlatTerm.cpp

 * Implements class FlatTerm.
 */



#include "../Lib/Allocator.hpp"

#include "FlatTerm.hpp"

namespace Kernel
{

using namespace Lib;

/**
 * Allocate a FlatTerm object having @b num entries.
 */
void* FlatTerm::operator new(size_t sz,unsigned num)
{
  CALL("FlatTerm::operator new");
  ASS_G(num,1);
  ASS_EQ(sz, sizeof(FlatTerm));

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size=sizeof(FlatTerm)+(num-1)*sizeof(FlatTerm::Entry);

  return ALLOC_KNOWN(size,"FlatTerm");
}

/**
 * Destroy the FlatTerm object
 */
void FlatTerm::destroy()
{
  CALL("FlatTerm::destroy");
  ASS_G(_length,1);

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size=sizeof(FlatTerm)+(_length-1)*sizeof(FlatTerm::Entry);

  DEALLOC_KNOWN(this, size,"FlatTerm");
}

FlatTerm::FlatTerm(size_t length)
: _length(length)
{
  CALL("FlatTerm::FlatTerm");
}

FlatTerm* FlatTerm::create(Term* t)
{
  throw 0; //not implemented
}


};

