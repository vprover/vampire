/**
 * @file Rule/Index.hpp
 * Defines class Index for implementing a rule index
 * @since 28/07/2008 train London-Manchester
 */

#ifndef __Rule_Index__
#define __Rule_Index__

#include "Lib/Stack.hpp"
#include "Kernel/Unit.hpp"
#include "Rule/Rule.hpp"

namespace Kernel {
  class Signature;
  class Term;
};

using namespace Lib;
using namespace Kernel;

namespace Rule {

/**
 * Class Index implementing a rule index.
 * @since 28/07/2008, train London-Manchester
 */
class Index
{
public:
  class EntryArray;

  /**
   * Entry in the index.
   * @since 01/08/2008, flight Manchester-Alicante
   */
  class Entry {
  public:
    /** function symbol or header, -1 if variable */
    int fun;
    /** arity of this symbool */
    unsigned arity;
    /** number of rules in this part of the index */
    unsigned rules;

    union {
      /** It is a leaf containing a pointer to an array of rules when the arity is 0 */
      const Rule** leaf;
      /** and an array of pointers to entries of length arity otherwise */
      EntryArray* entries;
    };
  };

  class EntryArray {
  public:
    Entry* array;
    int length;
  };

  /**
   * A candidate set is a set of candidates for unification.
   * @since 07/08/2008 train London-Manchester
   */
  class CandidateSet
  {
  public:
    // use allocator to (de)allocate objects of this class
    CLASS_NAME("Index::CandidateSet");
    USE_ALLOCATOR(CandidateSet);

    CandidateSet(Entry* entry,CandidateSet* prev);
    int total() const {return _total;}
    void cutUpTo(CandidateSet* upTo);

  private:
    // structure
    /** Entry at this node */
    Entry* _entry;
    /** The number of rules in this array of rules */
    int _length; 
    /** Total number of rules in this array and arrays below it */
    int _total;
    /** the set below */
    CandidateSet* _next;
  }; // class CandidateSet

  Index(const Signature* sig);
  ~Index();
  void compile(UnitList* units,Stack<Unit*>& goals);
  CandidateSet* retrieve(const Literal* query);
  /** Return the array of top-level entries */
  const Entry* entries() const { return _entries; }
  /** Return the number of headers */
  int headers() const { return _headers; }
  /** Return the array of all rules */
  const Rule* rules() const { return _rules; }
  /** Return the number of rules */
  int numberOfRules() const { return _numberOfRules; }

private:
  // used in compilation
  class TRule;
  class LRule;
  void sort(TRule* rules,int first,int last);
  void sort(LRule* rules,int first,int last);
  void compile(TRule* rules,int numberOfRules,EntryArray& saveTo);
  CandidateSet* retrieve(const Term* query,Entry* entry,CandidateSet* previous);
  CandidateSet* retrieve(const Term* query,EntryArray* entryArray,
			 CandidateSet* previous);

  // structure
  /** The signature for which the index is built */
  const Signature* _signature;
  /** The number of different headers in the signature */
  int _headers;
  /** the array of entries for every header in the signature */
  Entry* _entries;
  /** The array of all rules in the index */
  Rule* _rules;
  /** The number of rules in @b _rules */
  int _numberOfRules;
}; // class Index

}

#endif
