// /**
//  * @file LaTeX.hpp
//  * Defines a class LaTeX translating Vampire data structures 
//  * into LaTeX.
//  *
//  * @since 04/01/2004 Manchester
//  */

// #ifndef __LaTeX__
// #define __LaTeX__

// #include <string>

// #include "../VS/Connective.hpp"
// #include "Var.hpp"

// namespace VS {
//   class Symbol;
//   class SymbolMap;
// }

// using namespace VS;

// namespace Shell {

// class Term;
// class TermList;
// class Atom;
// class Literal;
// class Clause;
// class Formula;
// class Refutation;
// class Unit;
// class Options;


// /**
//  * Translates Vampire refutations into LaTeX.
//  * @since 04/01/2004 Manchester
//  */
// class LaTeX
// {
// public:
//   LaTeX(const Options& options,const SymbolMap* map);
//   void output (const Refutation&) const;
//   string toString(const Term&) const;
//   string toString(const string& funOrPred,const TermList& args) const;
// private:
//   /** options used for output */
//   const Options& _options;
//   /** symbol map for printing atoms, functions and variables */
//   const SymbolMap* _map;
//   string toString(const Refutation&) const;
//   string toString(Var) const;
//   string toString(const Symbol&) const;
//   string toString(const TermList&) const;
//   string toString(const Atom&) const;
//   string toString(const Literal&) const;
//   string toString(const Clause&) const;
//   string toString(const Formula&) const;
//   string toString(const Formula&, Connective c) const;
//   string toString(const Unit&) const;
//   string toStringAsInference(const Unit&) const;
// }; // class LaTeX

// }

// #endif // _LaTeX__

