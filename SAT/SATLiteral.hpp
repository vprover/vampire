/**
 * @file SATLiteral.hpp
 * Defines class SATLiteral.
 */


#ifndef __SATLiteral__
#define __SATLiteral__

#include <string>
#include <ostream>

#include "Shell/Options.hpp"
#include "Debug/Assertion.hpp"

#include "Kernel/Clause.hpp"


namespace SAT {

using namespace std;
using namespace Kernel;

class SATLiteral
{
public:
  inline SATLiteral(): _source(0) {}
  explicit inline SATLiteral(unsigned content) :_content(content),_source(0) {}
  /**
   * Create a SAT literal of variable @b var and polarity &b polarity
   *
   * @b var must be greater than 0 and @b polarity either 1 or 0 (for positive or negative)
   */
  inline SATLiteral(unsigned var, unsigned polarity) :_polarity(polarity), _var(var), _source(0)
  { ASS_G(var,0); ASS_NEQ(var,0x7FFFFFFF); }


  inline void set(unsigned var, bool positive) {
    _var=var;
    _polarity=positive?1:0;
  }
  inline void setContent(unsigned content) {
    _content=content;
  }

  inline bool isPositive() const { return _polarity; }
  inline bool isNegative() const { return !_polarity; }
  inline unsigned var() const { return _var; }
  inline unsigned polarity() const { return _polarity; }
  inline unsigned oppositePolarity() const { return 1-_polarity; }
  inline unsigned content() const { return _content; }

  inline SATLiteral opposite() const { return SATLiteral(content()^1); }
  /** return this literal with positive polarity */
  inline SATLiteral positive() const { return SATLiteral(content()|1); }

  inline bool operator==(const SATLiteral& l) const
  { return _content==l._content; }
  inline bool operator!=(const SATLiteral& l) const
  { return _content!=l._content; }

 /**
  * The decision to record niceness in this way has effectively
  * doubled the size of all SATLiterals, perhaps not the best
  * idea, but it does avoid having to pass this all the way down
  * to the VariableSelector
  */
  inline void recordSource(Literal* l){ cout << "RN\n";_source = l; }
  virtual unsigned getNiceness(Shell::Options::NicenessOption niceness_option);

  string toString() const;

  /**
   * Return a dummy literal that is not equal to any
   * literal present in any clause. Moreover, its var()
   * returns variable number bigger than any variable
   * present in regular literals.
   */
  inline static SATLiteral dummy() { return SATLiteral(0xFFFFFFFF); }

private:
  union {
    unsigned _content;
    struct {
      unsigned _polarity : 1;
      unsigned _var : 31;
    };
  };
 
  // The FO literal that this SAT literal represents
  // for use in computing niceness
  // This information is possibly replicated in 
  //  - Grounder, _asgn (possibly?)
  // TODO - check
  Literal* _source;
};

};

std::ostream& operator<< (std::ostream& out, const SAT::SATLiteral& lit );

#endif /* __SATLiteral__ */
