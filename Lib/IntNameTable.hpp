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
 * @file IntNameTable.hpp
 *
 * Defines the class IntNameTable for a table of names, 
 * where insert returns an integer.
 *
 * @since 13/05/2000 flight Manchester-Atlanta, made from NameTable
 * @since 02/12/2003 Manchester, change to use strings instead of char*
 * @since 08/04/2006 Bellevue, changed to use maps
 */

#ifndef __IntNameTable__
#define __IntNameTable__

#include "Array.hpp"
#include "Map.hpp"
#include "VString.hpp"

using namespace std;

namespace Lib {

class IntNameTable 
{
 public:
  IntNameTable();
  int insert(const vstring& str);
//  /** return name number n */
//  inline vstring operator[] (int n) const { return _names[n]; }
//   int numberOfSymbols();

 private:
  Map <vstring,int,Hash> _map;
//  Array<vstring> _names;
  int _nextNumber;
}; // class NameTable

}

#endif
