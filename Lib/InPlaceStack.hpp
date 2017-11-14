
/*
 * File InPlaceStack.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file InPlaceStack.hpp
 * Defines class InPlaceStack.
 */


#ifndef __InPlaceStack__
#define __InPlaceStack__

namespace Lib {

//This class shown to be unnecessary, so it has remained unimplemented

/**
 * A stack for objects of variable size, that stores them in-place,
 * instead of storing just pointers to them. Also, data of this stack
 * don't get reallocated, a new piece of memory is allocated in addition
 * when needed and put into a list-like structure.
 *
 * Objects of class T must return number of bytes they occupy in response
 * to @b obj.memorySize() call.
 */
template<typename T>
class InPlaceStack
{
public:
  T& top();
  T pop();

  template<class Factory>
  void push(Factory f);
private:
  struct DataContainer {
    size_t size;
    DataContainer* previous;
    /** pointer to the first filled item */
    char* top;
    char data[1];
  };

  DataContainer* _curr;
};

};

#endif /* __InPlaceStack__ */
