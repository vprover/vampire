/**
 * @file InterpretationManager.hpp
 * Defines class InterpretationManager.
 */


#ifndef __InterpretationManager__
#define __InterpretationManager__

#include "Term.hpp"

namespace Kernel {

class TrivialInterpretationManager;

class InterpretationManager {
public:
  virtual ~InterpretationManager() {}

  virtual bool isInterpretedFunction(const string& name) = 0;
  virtual bool isInterpretedPredicate(const string& name) = 0;
  virtual bool isBadFunction(const string& name) = 0;
  virtual bool isBadPredicate(const string& name) = 0;

  virtual TermList simplifyFunction(TermList t) { return t; };

  /**
   * Given a @b l is a literal that can be interpreted,
   * return true iff @b l is interpreted as true.
   */
  virtual bool simplifyPredicate(Literal* l) { return l; };

  static InterpretationManager* instance();

};


class TrivialInterpretationManager
: public InterpretationManager {
  bool isInterpretedFunction(const string& name) { return false; };
  bool isInterpretedPredicate(const string& name) { return false; };
  bool isBadFunction(const string& name) { return false; };
  bool isBadPredicate(const string& name) { return false; };
};

};

#endif /* __InterpretationManager__ */
