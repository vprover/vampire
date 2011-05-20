/**
 * @file FormulaTransformer.hpp
 * Defines class FormulaTransformer.
 */

#ifndef __FormulaTransformer__
#define __FormulaTransformer__

namespace Kernel {

class FormulaTransformer {
public:
  Formula* apply(Formula* f);
protected:
  FormulaTransformer() {}

  virtual Formula* applyLiteral(Formula* f) { return f; }

  virtual Formula* applyAnd(Formula* f) { return applyJunction(f); }
  virtual Formula* applyOr(Formula* f) { return applyJunction(f); }

  /** This function is called by applyAnd() and applyOr()
   * in their default implementation. */
  virtual Formula* applyJunction(Formula* f);

  virtual Formula* applyNot(Formula* f);

  virtual Formula* applyImp(Formula* f) { return applyBinary(f); }
  virtual Formula* applyIff(Formula* f) { return applyBinary(f); }
  virtual Formula* applyXor(Formula* f) { return applyBinary(f); }

  /** This function is called by applyImp(), applyIff()
   * and applyXor() in their default implementation. */
  virtual Formula* applyBinary(Formula* f);

  virtual Formula* applyForAll(Formula* f) { return applyQuantified(f); }
  virtual Formula* applyExists(Formula* f) { return applyQuantified(f); }

  /** This function is called by applyForAll() and applyExists()
   * in their default implementation. */
  virtual Formula* applyQuantified(Formula* f);


  virtual Formula* applyTrueFalse(Formula* f) { return f; }
};

}

#endif // __FormulaTransformer__
