/**
 * @file CodeTreeInterfaces.hpp
 * Defines classes of indexing structures that use code trees.
 */

#ifndef __CodeTreeInterfaces__
#define __CodeTreeInterfaces__

#include "../Forwards.hpp"

#include "CodeTree.hpp"
#include "TermIndexingStructure.hpp"


namespace Indexing
{

using namespace Kernel;
using namespace Lib;

/**
 * Term indexing structure using code trees to retrieve generalizations
 */
class CodeTreeTIS : public TermIndexingStructure
{
public:
  void insert(TermList t, Literal* lit, Clause* cls);
  void remove(TermList t, Literal* lit, Clause* cls);

  TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions = true);
  bool generalizationExists(TermList t);

private:
  struct TermInfo;

  TermCodeTree _ct;
};

};
#endif /*__CodeTreeInterfaces__*/
