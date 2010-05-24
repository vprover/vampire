/**
 * @file Builder.hpp
 * Defines class Builder.
 */

#ifndef __Builder__
#define __Builder__

#include "Forwards.hpp"


namespace Shell
{
namespace LTB
{



class Builder {
public:
  Builder();

  void build(VirtualIterator<string> fnames);

};

}
}

#endif // __Builder__
