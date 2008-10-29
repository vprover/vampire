/**
 * @file Rule/Prolog.hpp
 * Defines class Prolog for compiling a rule index into a Prolog program.
 * @since 08/08/2008 flight Singapore-Sydney
 */

#ifndef __Rule_Prolog__
#define __Rule_Prolog__

#include <iostream>

#include "../Lib/Map.hpp"
#include "../Rule/Index.hpp"

using namespace std;
using namespace Lib;

namespace Rule {

/**
 * Class  Prolog for compiling a rule index into a Prolog program.
 * @since 08/08/2008 flight Singapore-Sydney
 */
class Prolog
{
public:
  /**
   * Create a new object that will write in the stream str.
   * @since 08/08/2008 flight Singapore-Sydney
   */
  Prolog(ostream& str)
    : _stream(str),
      _nextAuxiliarySymbolNumber(0)
  {}
  void write(Index& index);
private:
  void write(int headers,const Index::Entry* entries);
  void write(const Index::Entry* entries);
  void writeRule(int ruleNumber,const Rule& rule);
  void writeLeaf(int entryNumber,const Index::Entry* entries);

  /** Class for assigning integers to pointers in the index */
  class Enumerator
    : public Map<const void*,int,Hash>
  {
  public:
    /** create a new enumerator */
    Enumerator()
      : _nextNumber(0)
    {}
    int add(const Index::Entry* entry);
  private:
    /** next number to use when inserted */
    int _nextNumber;
  };

  void writeVars(int m);

  void outputLiteral(bool preservePolarity,const Literal* literal);
  void outputArgs(const TermList* args);
  void outputArg(const TermList* arg);

  /** The output stream */
  ostream& _stream;
  /** Enumerator for entries in the Index */
  Enumerator _entryEnumerator;
//   /** Enumerator for leaves in the Index */
//   Enumerator _leafEnumerator;
  /** a counter used for numbering auxiliary predicates */
  int _nextAuxiliarySymbolNumber;
  /** The index currently being compiled */
  Index* _index;
}; // class Prolog

}

#endif
