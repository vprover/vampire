/**
 * @file FlatTerm.hpp

 * Defines class FlatTerm.
 */

#ifndef __FlatTerm__
#define __FlatTerm__

#include "../Forwards.hpp"

namespace Kernel {

class FlatTerm
{
public:
  static FlatTerm* create(Term* t);

  enum EntryTag {
    TERM_PTR = 0,
    FUN = 1,
    VAR = 2,
    /** Either the first or the last entry of the FlatTerm */
    EDGE = 3
  };

  struct Entry
  {
    Entry() {}
    Entry(EntryTag tag, unsigned num) { _info.tag=tag; _info.number=num; }
    Entry(Term* ptr) : _ptr(ptr) {}
    union {
      Term* _ptr;
      struct {
	unsigned tag : 2;
	unsigned number : 30;
      } _info;
    };
  };
private:
  FlatTerm(size_t length);
  void* operator new(size_t,unsigned length);
  void destroy();

  size_t _length;
  bool _literal;
  Entry _data[1];
};

};

#endif /* __FlatTerm__ */
