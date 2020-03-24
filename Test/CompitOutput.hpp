
/*
 * File CompitOutput.hpp.
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
 * @file CompitOutput.hpp
 * Defines class CompitOutput for writing COMPIT benchmark files.
 */

#ifndef __CompitOutput__
#define __CompitOutput__

// #include "Config.hpp"

#if COMPIT_VERSION==1

#include "Forwards.hpp"

#include "Lib/VString.hpp"

namespace Test {

using namespace std;
using namespace Kernel;

/**
 * Class for writing various data structures in the
 * Prolog format
 * @since 25/04/2008 flight Frankfurt-Vienna
 */
class CompitOutput
{
public:
  enum CompitOperation {
    INSERT,
    DELETE,
    SUCCESSFUL_QUERY,
    UNSUCCESSFUL_QUERY
  };

  static void print(CompitOperation op, TermList t);
  static void print(CompitOperation op, Literal* t, bool complementary=false);
private:
  static bool signaturePrinted;

  static void printSignature();
  static void printSignatureForLiterals();
  static char getPredSymbolChar(unsigned header);
  static char getFunctorChar(unsigned fn);
  static char getVarChar(unsigned var);

  static void fail();
};

}


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
      CompitOutput::print(CompitOutput::INSERT, norm.apply(lit));
    }
  }
  void remove(Literal* lit, Clause* cls)
  {
    LiteralSubstitutionTree::remove(lit,cls);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
      CompitOutput::print(CompitOutput::DELETE, norm.apply(lit));
    }
  }

  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
  {
    SLQueryResultIterator res=LiteralSubstitutionTree::getUnifications(lit,
	complementary, retrieveSubstitutions);
    if(!lit->commutative()) {
      Renaming norm;
      norm.normalizeVariables(lit);
      if(res.hasNext()) {
	CompitOutput::print(CompitOutput::SUCCESSFUL_QUERY, norm.apply(lit), complementary);
      } else {
	CompitOutput::print(CompitOutput::UNSUCCESSFUL_QUERY, norm.apply(lit), complementary);
      }
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
    CompitOutput::print(CompitOutput::INSERT, norm.apply(t));
  }
  void remove(TermList t, Literal* lit, Clause* cls)
  {
    TermSubstitutionTree::remove(t,lit,cls);
    Renaming norm;
    norm.normalizeVariables(t);
    CompitOutput::print(CompitOutput::DELETE, norm.apply(t));
  }

  TermQueryResultIterator getUnifications(TermList t, bool retrieveSubstitutions)
  {
    TermQueryResultIterator res=TermSubstitutionTree::getUnifications(t,retrieveSubstitutions);
    Renaming norm;
    norm.normalizeVariables(t);
    if(res.hasNext()) {
      CompitOutput::print(CompitOutput::SUCCESSFUL_QUERY, norm.apply(t));
    } else {
      CompitOutput::print(CompitOutput::UNSUCCESSFUL_QUERY, norm.apply(t));
    }
    return res;
  }

};

}

#endif

#endif
