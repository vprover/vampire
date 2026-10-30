/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file TPTPPrinter.hpp
 * Defines class TPTPPrinter, the TPTP output of units and formulas, and the TPTP syntax
 * (TPTPOutput) it shares with the proof printers. The names it prints are in
 * TPTPConstants.hpp; TPTP proofs are in TPTPProofPrinter.hpp.
 */

#ifndef __TPTPPrinter__
#define __TPTPPrinter__

#include <iosfwd>
#include <concepts>
#include <string>
#include <string_view>

#include "Lib/Metaiterators.hpp"
#include "Lib/Output.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "SAT/SATLiteral.hpp"
#include "Forwards.hpp"
#include "Shell/TPTPConstants.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/** TPTP syntax shared by TPTPPrinter and the proof printers. */
namespace TPTPOutput {

/** The role a unit of the given input type had in the input. */
const char* inputRole(UnitInputType type);

/** The TPTP symbol of a connective, with the spacing used between operands. */
const char* connectiveSymbol(Connective connective);

/** The keyword that starts an annotated formula in the given language. */
const char* languageName(Language language);
std::ostream& operator<<(std::ostream& out, Language language);

/** How to write a unit back as TPTP so that parsing the output reproduces it. */
struct ProblemRole {
  const char* role;
  /** The unit is derived from the negated conjecture and is negated back to the conjecture. */
  bool negateFormula;
};

ProblemRole problemRole(const Unit* unit);

/** A name made of a prefix, a number and a suffix, such as f12, s3, f7_D or X0. */
struct Reference {
  const char* prefix;
  unsigned number;
  const char* suffix = "";

  friend std::ostream& operator<<(std::ostream& out, Reference reference)
  { return out << reference.prefix << reference.number << reference.suffix; }
};

inline Reference variableRef(unsigned variable) { return {"X", variable}; }

/** The TPTP name of an input unit, or @b fallbackPrefix followed by its number if it has none. */
struct InputName {
  const Unit* unit;
  const char* fallbackPrefix;

  friend std::ostream& operator<<(std::ostream& out, InputName name);
};

/** The universal closure of a unit in the target language.
 * The unit must remain alive until this is inserted.
 */
struct UniversalClosure {
  const Unit* unit;
  Language targetLanguage;
  friend std::ostream& operator<<(std::ostream& out, UniversalClosure closure);
};

inline UniversalClosure universalClosure(const Unit* unit, Language targetLanguage)
{ return {unit, targetLanguage}; }

/** The variables bound by a universal quantifier in FOF, TFF, THF or TCF.
 * Type variables precede term variables; each group is sorted by variable number.
 * FOF omits sort annotations; typed languages always spell out sorts, including $i.
 */
class QuantifiedVariables {
public:
  QuantifiedVariables(const Unit* unit, Language targetLanguage);
  /** For proof components; the caller must supply unique variables. */
  QuantifiedVariables(VirtualIterator<unsigned> variables,
      const DHMap<unsigned, TermList, FnvHash, IdentityHash>& sorts,
      Language targetLanguage);

  bool isEmpty() const { return _variables.isEmpty(); }

  friend std::ostream& operator<<(std::ostream& out, QuantifiedVariables const& self);

private:
  struct Variable {
    unsigned number;
    TermList sort;
  };

  void collect(VirtualIterator<unsigned> variables,
      const DHMap<unsigned, TermList, FnvHash, IdentityHash>& sorts,
      Language targetLanguage);

  bool _typed;
  Stack<Variable> _variables;
};

/** @b inner quantified universally over @b variables; without variables, only @b inner is written. */
template<Output::Printable Inner>
struct Quantified {
  QuantifiedVariables variables;
  Inner inner;
  bool innerParentheses;

  friend std::ostream& operator<<(std::ostream& out, Quantified const& self)
  {
    if (self.variables.isEmpty()) {
      return out << self.inner;
    }
    out << "( ! [" << self.variables << "] : ";
    if (self.innerParentheses) {
      out << '(' << self.inner << ')';
    } else {
      out << self.inner;
    }
    return out << " )";
  }
};

template<Output::Printable Inner>
Quantified<Inner> quantified(QuantifiedVariables variables, Inner inner, bool innerParentheses = true)
{ return {std::move(variables), std::move(inner), innerParentheses}; }

/** The TPTP name of a literal of an AVATAR SAT clause, i.e. of a split. */
struct SplitLiteral {
  SAT::SATLiteral literal;

  friend std::ostream& operator<<(std::ostream& out, SplitLiteral self);
};

/* How Disjunction prints the elements of a clause. */
inline const Literal& disjunct(const Literal* literal) { return *literal; }
inline SplitLiteral disjunct(SAT::SATLiteral literal) { return {literal}; }

/** A hasNext/next iterator over clause elements with a disjunct() overload, which can be
 * copied to print it more than once. Copy assignment is not required; mapping iterators
 * over lambdas lack it. */
template<class I>
concept DisjunctIterator = std::copy_constructible<I> && requires(I it) {
  { it.hasNext() } -> std::convertible_to<bool>;
  { disjunct(it.next()) } -> Output::Printable;
};

/** The elements of a clause (Literal* or SAT literals), joined by " | ", or $false if there
 * are none. The clause must remain alive until this is inserted. */
template<DisjunctIterator Literals>
struct Disjunction {
  Literals literals;

  friend std::ostream& operator<<(std::ostream& out, Disjunction const& self)
  {
    auto literals = self.literals;
    if (!literals.hasNext()) {
      return out << FALSE_CONSTANT;
    }
    out << disjunct(literals.next());
    while (literals.hasNext()) {
      out << connectiveSymbol(OR) << disjunct(literals.next());
    }
    return out;
  }
};

template<DisjunctIterator Literals>
Disjunction<Literals> disjunction(Literals literals)
{ return {std::move(literals)}; }

/** A TPTP list [<contents>]; @b contents is printed without the brackets. */
template<Output::Printable Contents>
struct Bracketed {
  Contents contents;

  friend std::ostream& operator<<(std::ostream& out, Bracketed const& self)
  { return out << '[' << self.contents << ']'; }
};

template<Output::Printable Contents>
Bracketed<Contents> bracketed(Contents contents)
{ return {std::move(contents)}; }

/** (<contents>). An lvalue is referenced, so it must remain alive until this is inserted
 * (and is not copied, which matters for terms and literals); an rvalue is stored. */
template<Output::Printable Contents>
struct Parenthesized {
  Contents contents;

  friend std::ostream& operator<<(std::ostream& out, Parenthesized const& self)
  { return out << '(' << self.contents << ')'; }
};

template<Output::Printable Contents>
Parenthesized<Contents> parenthesized(Contents&& contents)
{ return {std::forward<Contents>(contents)}; }

/** The elements of an iterator separated by commas, as in TPTP lists and argument lists. */
template<class Elements>
Output::Interleaved<char, Elements> commaSeparated(Elements elements)
{ return Output::interleaved(',', std::move(elements)); }

/** The elements of an iterator mapped by @b map, separated by commas. */
template<class Elements, class Map>
Output::Interleaved<char, MappingIterator<Elements, Map, ResultOf<Map, typename Elements::ElementType>>>
commaSeparated(Elements elements, Map map)
{ return commaSeparated(getMappingIterator(std::move(elements), std::move(map))); }

template<class Writer, class Element>
concept ElementWriter = std::invocable<Writer const&, std::ostream&, Element const&>;

/** Write each element with @b write, separating the results with commas.
 * Any references captured by write must remain valid until insertion.
 */
template<class Elements, ElementWriter<typename Elements::ElementType> Writer>
auto commaSeparatedWith(Elements elements, Writer writer)
{
  return commaSeparated(std::move(elements), [writer = std::move(writer)](auto element) {
    return Output::deferred([writer, element](std::ostream& out) -> std::ostream& {
      writer(out, element);
      return out;
    });
  });
}

} // namespace TPTPOutput

/**
 * TPTP output of units and formulas.
 * Symbol declarations are not printed here; see UIHelper::outputSymbolDeclarations.
 */
class TPTPPrinter {
public:
  /* Insert these into a stream, e.g. `out << TPTPPrinter::unit(cl) << endl;`.
   * They refer to the unit or formula and to the name, which must remain alive until inserted. */

  struct UnitOutput {
    const Unit* unit;
    bool typedClauses;

    std::ostream& print(std::ostream& out) const;
    friend std::ostream& operator<<(std::ostream& out, UnitOutput const& self) { return self.print(out); }
  };

  struct NamedUnitOutput {
    const Unit* unit;
    std::string_view name;
    const char* role;
    bool typedClauses;
    bool includeSplitLevels;

    std::ostream& print(std::ostream& out) const;
    friend std::ostream& operator<<(std::ostream& out, NamedUnitOutput const& self) { return self.print(out); }
  };

  struct FormulaOutput {
    const Formula* formula;

    std::ostream& print(std::ostream& out) const;
    friend std::ostream& operator<<(std::ostream& out, FormulaOutput const& self) { return self.print(out); }
  };

  /** With @b typedClauses, a clause is printed as a tcf() unit, i.e. with an
   *  explicit universal prefix spelling out the sort of each of its variables;
   *  without it, as a cnf() unit. Formulas use thf() for higher-order input,
   *  and tff() otherwise. */
  static UnitOutput unit(const Unit* unit, bool typedClauses = false)
  { return {unit, typedClauses}; }
  /** A name would silently convert to typedClauses; use namedUnit(). */
  static UnitOutput unit(const Unit* unit, const char* name) = delete;
  /** Like unit(), but with the given name and role instead of the unit's own.
   *  The formula is printed as it is, since the role is the caller's. With
   *  @b includeSplitLevels, a clause's split levels are added as $splitLevel<n> disjuncts. */
  static NamedUnitOutput namedUnit(const Unit* unit, std::string_view name, const char* role,
      bool typedClauses = false, bool includeSplitLevels = false)
  { return {unit, name, role, typedClauses, includeSplitLevels}; }
  static FormulaOutput formula(const Formula* formula)
  { return {formula}; }

  /** The same text as unit(), as a string. */
  static std::string toString(const Unit*, bool typedClauses = false);
  /** The same text as formula(), as a string. */
  static std::string toString(const Formula*);

private:
  static std::ostream& printUnit(std::ostream& out, const Unit* unit, bool typedClauses);
  static std::ostream& printUnit(std::ostream& out, const Unit* unit, std::string_view name,
      const char* role, bool typedClauses, bool includeSplitLevels);
  static std::ostream& printFormula(std::ostream& out, const Formula* formula);

  /** cnf, tcf, tff or thf, see toString(const Unit*, bool). */
  static TPTPOutput::Language language(const Unit* unit, bool typedClauses);
  static std::ostream& printBody(std::ostream& out, const Unit* unit, bool typedClauses,
      bool negateFormula, bool includeSplitLevels);

};

} // namespace Shell

#endif // __TPTPPrinter__
