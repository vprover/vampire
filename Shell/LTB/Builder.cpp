/**
 * @file Builder.cpp
 * Implements class Builder.
 */

#include <fstream>

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Sort.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Shell/Options.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTPParser.hpp"

#include "Storage.hpp"

#include "Builder.hpp"

namespace Shell
{
namespace LTB
{

Builder::Builder()
{
  CALL("Builder::Builder");

}

struct StringComparator
{
  static Comparison compare(const string& a, const string& b)
  {
    CALL("DefaultComparator::compare");

    int res=a.compare(b);
    if(res==0) {
      return EQUAL;
    }
    else if(res<0) {
      return LESS;
    }
    else {
      ASS(res>0);
      return GREATER;
    }
  }
};

void Builder::build(VirtualIterator<string> fnameIterator)
{
  CALL("Builder::build");

  StringStack fnames;
  fnames.loadFromIterator(fnameIterator);

  if(env.options->normalize()) {
    sort<StringComparator>(fnames.begin(), fnames.end());
  }

  UnitList* units=0;

  StringStack::Iterator fnit(fnames);
  while(fnit.hasNext()) {
    string fname=fnit.next();
    ifstream input(fname.c_str());

    TPTPLexer lexer(input);
    TPTPParser parser(lexer);
    UnitList* newUnits = parser.units();

    units=UnitList::concat(newUnits, units);
  }

  Storage storage(false);
  storage.storeTheoryFileNames(fnames);


}



}
}

