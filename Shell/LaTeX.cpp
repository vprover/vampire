// /**
//  * Implements class LaTeX translating Vampire data structures 
//  * into LaTeX.
//  *
//  * @since 04/01/2004 Manchester
//  */

// #include <fstream>


// #include "../VL/Int.hpp"

// #include "../VS/SymbolMap.hpp"

// #include "Options.hpp"
// #include "LaTeX.hpp"
// #include "Refutation.hpp"

// // #include "Tracer.hpp"
// // #include "Unit.hpp"
// // #include "VampireException.hpp"

// #define KIF_EXPERIMENTS 0

// using namespace VL;
// using namespace VS;
// using namespace Shell;

// /**
//  * Initialise LaTeX.
//  * @since 26/09/2005 Bellevue
//  */
// LaTeX::LaTeX (const Options& options,const SymbolMap* map)
//   : _options(options),
//     _map(map)
// {
// } // LaTeX::LaTeX


// /**
//  * Convert the refutation to LaTeX
//  * @since 04/01/2004 Manchester
//  */
// string LaTeX::toString (const Refutation& ref) const
// {
//   TRACER("LaTeX::toString (const Refutation& ref)");

//   string result = "\\documentclass[fleqn]{article}\n"
//                   "\\usepackage{fullpage,latexsym}\n"
//                   "\\input{VampireProofMacros}\n"
//                   "\\begin{document}\n"
//                   "\\begin{VampireProof}\n";

//   VL::Iterator<Unit> units(ref.refutation());
//   while (units.hasNext()) {
//     result += toStringAsInference(units.next());
//   }

//   return result + "\\end{VampireProof}\n"
// 	          "\\end{document}\n";
// } // LaTeX::toString (const Refutation& ref)


// /**
//  * Convert the formula to LaTeX
//  *
//  * @since 12/10/2002 Tbilisi, implemented as ostream output function
//  * @since 09/12/2003 Manchester
//  * @since 11/12/2004 Manchester, true and false added
//  * @since 29/04/2005 Manchester, inequality instead of negation of equality
//  */
// string LaTeX::toString (const Formula& f) const
// {
//   TRACER("LaTeX::toString (const Formula& f)");

//   static string names [] =
//     { "", " \\Vand ", " \\Vor ", " \\Vimp ", " \\Viff ", " \\Vxor ", 
//       "\\neg ", "\\forall ", "\\exists ", "\bot", "\top"};

//   Connective c = f.connective();
//   string con = names[(int)c];
//   switch (c) {
//   case ATOM:
//     return toString(f.atom());

//   case AND:
//   case OR: 
//     {
//       string result = toString(f.args().head(),c);
//       VL::Iterator<Formula> arg (f.args().tail());
//       while (arg.hasNext()) {
// 	result += con + toString(arg.next(),c);
//       }
//       return result;
//     }

//   case IMP:
//   case IFF:
//   case XOR:
//     return toString(f.left(),c) + con + toString(f.right(),c);

//   case NOT:
//     if (f.uarg().connective() == ATOM &&
// 	f.uarg().atom().isEquality()) {
//       const TermList& ts = f.uarg().atom().args();
//       return toString(ts.head()) + " \\neq " + toString(ts.second());
//     }
//     return con + toString(f.uarg(),c);

//   case FORALL:
//   case EXISTS:
//     {
//       string result("(");
//       VL::Iterator<Var> vs(f.vars());
//       while (vs.hasNext()) {
// 	result += con + toString(vs.next()) + string(" ");
//       }
//       return result + ")" + toString(f.qarg(),c);
//     }

//   case FALSE:
//   case TRUE:
//     return con;

// #if VDEBUG
//   default:
//     ASSERTION_VIOLATION;
// #endif
//   }
// } // LaTeX::toString (const Formula&)

// /**
//  * Convert the formula in scope of another formula 
//  * to LaTeX.
//  * @param f the formula
//  * @param outer connective of the outer formula
//  * @since 09/12/2003 Manchester
//  */
// string LaTeX::toString (const Formula& f, Connective outer) const
// {
//   TRACER("LaTeX::toString (const Formula& f, Connective outer)");

//   return f.parenthesesRequired(outer) ?
//          string("(") + toString(f) + ")" :
//          toString(f);
// } // LaTeX::toString (const Formula&, Connective outer)


// /**
//  * Convert clause to LaTeX.
//  * @since 23/10/2003 Manchester, implemented as stream output function
//  * @since 09/12/2003 Manchester
//  */
// string LaTeX::toString (const Clause& c) const
// {
//   TRACER("LaTeX::toString (const Clause& c)");

//   if (c.isEmpty()) {
//     return "\\VEmptyClause";
//   }

//   string result = toString(c.literals().head());

//   VL::Iterator<Literal> lits (c.literals().tail());
//   while (lits.hasNext()) {
//     result += string(" \\Vor ") + toString(lits.next());
//   }
//   return result;
// } // LaTeX::toString (const Clause& c)


// /**
//  * Convert literal to LaTeX.
//  * @since 09/12/2003 Manchester
//  */
// string LaTeX::toString (const Literal& l) const
// {
//   TRACER("LaTeX::toString (const Literal& l)");

//   if (l.isPositive()) {
//     return toString(l.atom());
//   }
//   Atom a(l.atom());
//   if (a.isEquality()) {
//     TermList ts (a.args());
//     return toString(ts.head()) + " \\neq " + toString(ts.second());
//   }
//   return string("\\neg ") + toString(a);
// } // LaTeX::toString (const Literal& l)


// /**
//  * Otput function or predicate symbol in LaTeX
//  *
//  * @since 05/10/2002 Manchester
//  * @since 23/10/2002 Manchester, changed to handle special KIF names
//  * @since 09/09/2003 Manchester, changed to use string instead of char*
//  * @since 25/07/2005 Tallinn, changed to parse the name symbol by symbol
//  */
// string LaTeX::toString (const Symbol& s) const
// {
//   TRACER("LaTeX::toString (const Symbol& s)");

//   string symbolName; // the name of this symbol, if any
//   switch (s.kind()) {
//   case Symbol::Function:
//     {
//       const FunctionSymbol& f = static_cast<const FunctionSymbol&>(s);
//       if (f.isSkolemFunction()) {
// 	return (string)"\\sigma_{" + Int::toString(f.number()) + "}";
//       }
//       symbolName = f.name();
//     }
//     break;

//   case Symbol::Predicate:
//     {
//       const PredicateSymbol& p = static_cast<const PredicateSymbol&>(s);
//       if (p.isName()) {
// 	return (string)"\\delta_{" + Int::toString(p.number()) + "}";
//       }
//       if (p.isAnswer()) {
// 	return "\\mathit{answer}";
//       }
//       symbolName = p.name();
//     }
//     break;

//   case Symbol::Integer:
//     {
//       const IntegerConstant& i = static_cast<const IntegerConstant&>(s);
//       return Int::toString(i.value());
//     }

//   case Symbol::Real:
//     {
//       const RealConstant& r = static_cast<const RealConstant&>(s);
//       return Int::toString(r.value());
//     }

//   case Symbol::String:
//     {
//       const StringConstant& str = static_cast<const StringConstant&>(s);
//       symbolName = string("``") + str.value() + "\'\'";
//     }

// #if VDEBUG
//   default:
//     ASSERTION_VIOLATION;
// #endif
//   }

//   // cut names longer than 8000 symbols
// #define LENGTH 8004
//   char newName[LENGTH]; // LaTeX name of this symbol
//   char* name = newName;
//   const char* nm = symbolName.c_str();
//   // finding end of the name
//   const char* end = nm;
//   while (*end) {
//     end++;
//   }
//   // finding the tail consisting only of digits and turning it into
//   // the LaTeX index
//   const char* digits = end;
//   while (nm != digits) {
//     if (digits[-1] >= '0' && digits[-1] <= '9') {
//       digits--;
//     }
//     else {
//       break;
//     }
//   }
//   if (digits == nm) { // digit-only name
//     return symbolName;
//   }
//   while (nm < digits) {
//     switch (*nm) {
//     case '$':
//     case '_':
//       *name++ = '\\';
//       *name++ = *nm;
//       break;
//     default:
//       *name++ = *nm;
//       break;
//     }
//     nm++;
//   }
//   if (digits == end) {
//     *name = 0;
//     return string("\\mathit{") + newName + '}';
//   }
//   // copy digits as an index
//   *name++ = '_';
//   *name++ = '{';
//   while (digits != end) {
//     *name++ = *digits++;
//   }
//   *name++ = '}';
//   *name = 0;
//   return string("\\mathit{") + newName + '}';
// } // LaTeX::toString (const Symbol& s)


// /**
//  * Convert term to a string using the LaTeX syntax.
//  * @since 09/12/2003 Manchester
//  */
// string LaTeX::toString (const Term& t) const
// {
//   TRACER("LaTeX::toString (const Term& t)");

// //   if (_map) {
// //     string result;
// //     if (_map->toString(t,*this,result)) {
// //       return result;
// //     }
// //   }
//   if (t.isVar()) {
//     return toString(t.var());
//   }

//   return toString(t.functor()) + toString(t.args());
// } // LaTeX::toString (const Term& t)


// /**
//  * Convert term list to LaTeX.
//  * @since 09/12/2003 Manchester
//  */
// string LaTeX::toString (const TermList& terms) const
// {
//   TRACER("LaTeX::toString (const TermList& terms)");

//   if (terms.isEmpty()) {
//     return "";
//   }
//   string result = string("(") + toString(terms.head());
//   VL::Iterator<Term> ts (terms.tail());
//   while (ts.hasNext()) {
//     result += ",";
//     result += toString(ts.next());
//   }
//   return result + ")";
// } // LaTeX::toString (const TermList& terms)


// /**
//  * Convert the atom to LaTeX.
//  * @since 09/12/2003 Manchester
//  */
// string LaTeX::toString (const Atom& a) const
// {
//   TRACER("LaTeX::toString (const Atom& a)");

// //   if (_map) {
// //     string result;
// //     if (_map->toString(a,*this,result)) {
// //       return result;
// //     }
// //   }

//   TermList ts(a.args());
//   if (a.isEquality()) {
//     return toString(ts.head()) + "=" + toString(ts.second());
//   }

//   return toString(a.functor()) + toString(ts);
// } // LaTeX::toString (const Atom& a)

// /**
//  * Convert unit to LaTeX.
//  * @since 09/12/2003 Manchester
//  */
// string LaTeX::toString (const Unit& u) const
// {
//   TRACER("LaTeX::toString (const Unit& u)");

//   string prefix = Int::toString(u.number()) + ". ";
//   string postfix = string("(") + Unit::toString(u.inputType()) + ")";

//   switch (u.unitType()) {
//   case CLAUSE:
//     return prefix + toString(u.clause()) + postfix;
//   case FORMULA:
//     return prefix + toString(u.formula()) + postfix;
// #if VDEBUG
//   default:
//     ASSERTION_VIOLATION;
// #endif
//   }
// } // LaTeX::toString (const Unit& u)


// /**
//  * Convert inference to LaTeX.
//  * @since 23/10/2002 Manchester, as stream output function
//  * @since 09/12/2003 Manchester
//  */
// string LaTeX::toStringAsInference (const Unit& u) const
// {
// //   TRACER("LaTeX::toStringAsInference (const Unit& u)");

// //   UnitList parents(u.parents());
// //   string result = "[$";

// //   VL::Iterator<Unit> ps1 (parents);
// //   while (ps1.hasNext()) {
// //     result += Int::toString(ps1.next().number());
// //     if (ps1.hasNext()) {
// //       result += ",";
// //     }
// //   }
// //   if (parents.isNonEmpty()) {
// //     result += "\\rightarrow ";
// //   }
// //   const Inference& inf = u.inference();
// //   string infString = inf.rule() == IR_KERNEL ?
// //     inf.rulesAsString() :
// //     Inference::toString(inf.rule());

// //   result += Int::toString(u.number()) + "$, " + 
// //     infString + "]\\\\*[-2ex]\n";

// //   // premises
// //   result += "\\[\\begin{VampireInference}\n";

// //   if (parents.isNonEmpty()) {
// //     VL::Iterator<Unit> ps (parents);
// //     while (ps.hasNext()) {
// //       Unit premise (ps.next());
// //       result += "\\begin{VampirePremise}%\n~~";
// //       switch (premise.unitType()) {
// //       case CLAUSE:
// // 	result += toString(premise.clause());
// // 	break;
// //       case FORMULA:
// // 	result += toString(premise.formula());
// // 	break;
// //       }
// //       result += "\n\\end{VampirePremise}\n";
// //       if (ps.hasNext()) {
// // 	result += "\\VPremiseSeparator\n";
// //       }
// //     }
// //     result += "\\VConclusionSeparator\n";
// //   }

// //   // conclusion
// //   result += "\\begin{VampireConclusion}\n~~";
// //   switch (u.unitType()) {
// //   case CLAUSE:
// //     result += toString(u.clause());
// //     break;
// //   case FORMULA:
// //     result += toString(u.formula());
// //     break;
// //   }

// //   return result + "\n\\end{VampireConclusion}\n\\end{VampireInference}\n\\]\n";
// } // LaTeX::toStringAsInference (const Unit& u)


// /**
//  * Convert variable to LaTeX.
//  * @since 09/12/2003 Manchester
//  * @since 17/9/2005 flight Chicago-Frankfurt, row variables case added
//  */
// string LaTeX::toString (Var v) const
// {
//   TRACER("LaTeX::toString (Var v)");

//   if (v.toInt() < 0) { // row variable
//     return string("@_{") + Int::toString(-v.toInt()) + "}";
//   }
// #if KIF_EXPERIMENTS
//   switch (v.toInt()) {
//   case 0:
//     return "x";
//   case 1:
//     return "y";
//   case 2:
//     return "z";
//   case 3:
//     return "u";
//   case 4:
//     return "v";
//   case 5:
//     return "w";
//   default:
//     break;
//   }
// #endif
//   return string("x_{") + Int::toString(v.toInt()) + "}";
// } // LaTeX::toString (Var v)


// /**
//  * Output ref in the LaTeX form if options say so. The output is made
//  * in the file specified in options.
//  * @since 27/06/2004 Manchester
//  */
// void LaTeX::output (const Refutation& ref) const
// {
//   TRACER("LaTeX::output (const Refutation& ref)");

//   string fileName = _options.latexOutput();
//   if (fileName == "off") {
//     return;
//   }
//   string refutation = toString(ref);
//   if (fileName == "on") {
//     cout << refutation;
//     return;
//   }
//   ofstream stream(fileName.c_str());
//   if (stream) {
//     stream << refutation;
//   }
//   else {
//     cerr << "Cannot open file " << fileName << " for LaTeX output\n";
//   }
// } // LaTeX::output

// /**
//  * Convert to LaTeX a function or predicate with name funOrPred
//  * and arguments args.
//  * @since 28/09/2005 Redmond
//  */
// string LaTeX::toString (const string& funOrPred,const TermList& args) const
// {
//   return funOrPred + toString(args);
// }
