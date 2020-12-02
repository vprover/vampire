/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Helper.hpp
 * Helper declaration for API classes.
 */

#ifndef __API_Helper__
#define __API_Helper__

namespace Lib
{
template<typename T> class VirtualIterator;
template<class C> class Stack;

class OptionsReader;
}

namespace Kernel
{
class Formula;
class FormulaUnit;
class TermList;
class Unit;
class Literal;
}

namespace Api {


class Problem;

/** Structure with auxiliary data that do not need to appear in the header file */
class DefaultHelperCore;
class FBHelperCore;
class FormulaBuilder;
class StringIterator;

/**
 * A reference counting smart pointer to FBAux
 */
class ApiHelper
{
public:
  ApiHelper();
  ~ApiHelper();
  ApiHelper(const ApiHelper& h);
  ApiHelper& operator=(const ApiHelper& h);
  ApiHelper& operator=(FBHelperCore* hc);
  bool operator==(const ApiHelper& h) const;
  bool operator!=(const ApiHelper& h) const;

  DefaultHelperCore* operator->() const;
  DefaultHelperCore* operator*() const;
protected:
  void updRef(bool inc);

  FBHelperCore* _obj;
};

class FBHelper
: public ApiHelper
{
public:
  FBHelper();
  FBHelperCore* operator->() const;
};

}

#endif // __API_Helper__
