/**
 * @file Splitter.hpp
 * Defines class Splitter.
 */


#ifndef __Splitter__
#define __Splitter__

#include "Forwards.hpp"

#include "Lib/Stack.hpp"

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Shell;

class Splitter
{
public:
  virtual ~Splitter() {}

  virtual void init(SaturationAlgorithm* sa);

  virtual bool doSplitting(Clause* cl) = 0;

  /**
   * Return true if the splitter handles the empty clause and
   * it should not be further processed
   */
  virtual bool handleEmptyClause(Clause* cl) { return false; }

  virtual void onClauseReduction(Clause* cl, Clause* premise, Clause* replacement=0);
  virtual void onClauseReduction(Clause* cl, ClauseIterator premises, Clause* replacement=0) {}
  virtual void onNewClause(Clause* cl) {}
  virtual void onAllProcessed() {}

  const Options& getOptions() const;
protected:
  class CompRec
  {
    LiteralStack _lits;
    // What does special mean? - putSpecialsTogether?
    bool _isSpecial;
  public:
    CompRec() {}
    CompRec(Literal** lits, unsigned len);

    void add(Literal* l) { _lits.push(l); }
    void markSpecial() { _isSpecial = true; }

    unsigned size() const { return _lits.size(); }
    Literal* operator[](unsigned i) const { return _lits[i]; }
    Literal* const * array() const { return _lits.begin(); }

    /**
     * Return true if components were built with putSpecialsTogether set to true
     * and the current component contains a special literal.
     */
    bool special() const { return _isSpecial; }

    class Iterator : public LiteralStack::ConstIterator {
    public:
      Iterator(const CompRec& obj) : LiteralStack::ConstIterator(obj._lits) {}
    };
  };
  
  bool getComponents(Clause* cl, Stack<CompRec>& acc);

  SaturationAlgorithm* _sa;
};

};

#endif /* __Splitter__ */
