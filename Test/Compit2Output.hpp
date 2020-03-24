
/*
 * File Compit2Output.hpp.
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
 * @file Compit2Output.hpp
 * Defines class Compit2Output for writing COMPIT benchmark files.
 */

#ifndef __Compit2Output__
#define __Compit2Output__

// #include "Config.hpp"

#if COMPIT_VERSION==2

#include "Forwards.hpp"
#include "compit2.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

namespace Test {

using namespace std;
using namespace Kernel;

/**
 * Class for writing various data structures in the
 * Prolog format
 * @since 25/04/2008 flight Frankfurt-Vienna
 */
class Compit2Output
{
public:
  enum Operation {
    INSERT,
    DELETE,
    QUERY
  };

  static void print(Operation op, TermList t, unsigned resultCount=0);
  static void print(Operation op, Literal* t, unsigned resultCount=0, bool complementary=false);
private:
  static bool signaturePrinted;

  static void printSignature();
  static void printSignatureForLiterals();

  static WORD getFunctorRepr(unsigned fn);
  static WORD getPredSymbolRepr(unsigned header);
  static WORD getVarRepr(unsigned var);

  static size_t requiredSize(TermList t);
  static size_t requiredSize(Literal* lit);

  static void fail();
};

};

namespace Indexing
{
using namespace Kernel;
using namespace Test;

class CompitUnificationRecordingLiteralSubstitutionTree
: public LiteralSubstitutionTree
{
  void insert(Literal* lit, Clause* cls)
  {
    LiteralSubstitutionTree::insert(lit,cls);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
      Compit2Output::print(Compit2Output::INSERT, norm.apply(lit));
    }
  }
  void remove(Literal* lit, Clause* cls)
  {
    LiteralSubstitutionTree::remove(lit,cls);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
      Compit2Output::print(Compit2Output::DELETE, norm.apply(lit));
    }
  }

  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
  {
    SLQueryResultIterator res=LiteralSubstitutionTree::getUnifications(lit,
	complementary, retrieveSubstitutions);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
      unsigned count=0;
      while(res.hasNext()) {
	count++;
	res.next();
      }
      if(count) {
	res=LiteralSubstitutionTree::getUnifications(lit,complementary, retrieveSubstitutions);
      }
      Compit2Output::print(Compit2Output::QUERY, norm.apply(lit), count, complementary);
    }
    return res;
  }

};


class CompitUnificationRecordingTermSubstitutionTree
: public TermSubstitutionTree
{
  void insert(TermList t, Literal* lit, Clause* cls)
  {
    TermSubstitutionTree::insert(t,lit,cls);
    Renaming norm;
    norm.normalizeVariables(t);
    Compit2Output::print(Compit2Output::INSERT, norm.apply(t));
  }
  void remove(TermList t, Literal* lit, Clause* cls)
  {
    TermSubstitutionTree::remove(t,lit,cls);
    Renaming norm;
    norm.normalizeVariables(t);
    Compit2Output::print(Compit2Output::DELETE, norm.apply(t));
  }

  TermQueryResultIterator getUnifications(TermList t, bool retrieveSubstitutions)
  {
    TermQueryResultIterator res=TermSubstitutionTree::getUnifications(t,retrieveSubstitutions);
    Renaming norm;
    norm.normalizeVariables(t);
    unsigned count=0;
    while(res.hasNext()) {
      count++;
      res.next();
    }
    if(count) {
      res=TermSubstitutionTree::getUnifications(t,retrieveSubstitutions);
    }
    Compit2Output::print(Compit2Output::QUERY, norm.apply(t), count);
    return res;
  }

};

}

#endif

#endif
