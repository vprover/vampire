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
 * Implements class LaTeX translating Vampire data structures
 * into LaTeX.
 *
 * @since 04/01/2004 Manchester
 */

#include <fstream>


// #include "VL/Int.hpp"

// #include "VS/SymbolMap.hpp"

#include "Options.hpp"
#include "LaTeX.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/Set.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Theory.hpp"

#include "Saturation/Splitter.hpp"



// #define KIF_EXPERIMENTS 0

namespace Shell
{

using namespace Lib;
using namespace Kernel;

// /**
//  * Initialise LaTeX.
//  * @since 26/09/2005 Bellevue
//  */
// LaTeX::LaTeX (const Options& options,const SymbolMap* map)
//   : _options(options),
//     _map(map)
// {
// } // LaTeX::LaTeX

vstring LaTeX::header()
{
    vstring res =  "\\documentclass[border=10pt,preview,multi,varwidth=\\maxdimen]{standalone}\n"
    "\\usepackage{latexsym}\n"
    "\\newenvironment{VampireStep}{}{}\n"
    "\\standaloneenv{VampireStep}\n"
    "\\newenvironment{VampireInference}{%\n"
    "   \\begin{array}{c}}{\\end{array}}\n"
    "\\standaloneenv{VampireInference}\n"
    "\\newenvironment{VampireInferencePremises}{}{}\n"
    "\\newenvironment{VampirePremise}%\n"
    "   {\\begin{array}{l}}%\n"
    "   {\\end{array}}\n"
    "\\newenvironment{VampireConclusion}%\n"
    "   {\\begin{array}{l}}%\n"
    "   {\\end{array}}\n"
    "\\newcommand{\\VampireUnit}[3]{%\n"
    "   #1.~#2~[#3]}\n"

    "\\newcommand{\\VPremiseSeparator}{\\\\}\n"
    "\\newcommand{\\VConclusionSeparator}{\\\\ \\hline}\n"

    "\\newcommand{\\Vor}{\\vee}\n"
    "\\newcommand{\\Vand}{\\wedge}\n"
    "\\newcommand{\\Vimp}{\\rightarrow}\n"
    "\\newcommand{\\Viff}{\\leftrightarrow}\n"
    "\\newcommand{\\Vxor}{\\not\\Viff}\n"

    "\\newcommand{\\VEmptyClause}{\\Box}\n"

    "\\begin{document}\n";

    return res;
}

vstring LaTeX::footer()
{
    return "\\end{document}\n";
}


/**
 * Convert the refutation to LaTeX
 * @since 04/01/2004 Manchester
 */
vstring LaTeX::refutationToString(Unit* ref)
{
  CALL("LaTeX::refutationToString(Unit* ref)");

  vstring res = header(); 

  Stack<Unit*> outKernel;
  Set<Unit*> handledKernel;
  Stack<Unit*> outShell;
  Set<Unit*> handledShell;

  if( ref->isClause() ) {
    Clause* refCl=static_cast<Clause*>(ref);
    Unit* cs = refCl;
    outKernel.push(cs);
    handledKernel.insert(cs);
  } else {
    outShell.push(ref);
    handledShell.insert(ref);
  }

  while(outKernel.isNonEmpty()) {
    Unit* cs=outKernel.pop();
      Clause* cl= cs->asClause();
      Inference& inf = cl->inference();

      res+=toStringAsInference(cl);
      Inference::Iterator it = inf.iterator();
      while (inf.hasNext(it)) {
	Unit* prem=inf.next(it);
	if(prem->isClause() ) {
	  //this branch is for clauses that were inserted as input into the SaturationAlgorithm object
          //Giles. Removed bdds from this, but not sure if this is redundant anyway given the previous comment.
	  Unit* premCS= prem;

	  if(!handledKernel.contains(premCS)) {
	    handledKernel.insert(premCS);
	    outKernel.push(premCS);
	  }
	} else {
	  if(!handledShell.contains(prem)) {
	    handledShell.insert(prem);
	    outShell.push(prem);
	  }
	}
      }
  }

  while(outShell.isNonEmpty()) {
    Unit* unit=outShell.pop();
    Inference& inf = unit->inference();

    res+=toStringAsInference(unit);
    Inference::Iterator it = inf.iterator();
    while (inf.hasNext(it)) {
      Unit* prem=inf.next(it);
      if(!handledShell.contains(prem)) {
	handledShell.insert(prem);
	outShell.push(prem);
      }
    }
  }

  return res + footer(); 

}


vstring LaTeX::toString(Unit* u)
{
  CALL("LaTeX::toString(Unit* u)");

  if(u->isClause()) {
    return toString(static_cast<Clause*>(u));
  } else {
    return toString(static_cast<FormulaUnit*>(u)->formula());
  }
}

vstring replaceNeg(vstring s)
{
    size_t start_pos = s.find("~",0);
    if(start_pos != std::string::npos){
      s.replace(start_pos,1,vstring(" \\neg "));
    }
    return s;
}


/**
 * Convert the formula to LaTeX
 *
 * @since 12/10/2002 Tbilisi, implemented as ostream output function
 * @since 09/12/2003 Manchester
 * @since 11/12/2004 Manchester, true and false added
 * @since 29/04/2005 Manchester, inequality instead of negation of equality
 */
vstring LaTeX::toString (Formula* f) const
{
  CALL("LaTeX::toString(Formula* f)");

  static vstring names [] =
  { "", " \\Vand ", " \\Vor ", " \\Vimp ", " \\Viff ", " \\Vxor ",
	  "\\neg ", "\\forall ", "\\exists ", "\bot", "\top", "", ""};

  Connective c = f->connective();
  vstring con = names[(int)c];
  switch (c) {
  case LITERAL:
    return toString(f->literal());

  case AND:
  case OR:
  {
    FormulaList::Iterator arg(f->args());
    ASS(arg.hasNext());
    vstring result = toString(arg.next(),c);
    while (arg.hasNext()) {
      result += con + toString(arg.next(),c);
    }
    return result;
  }

  case IMP:
  case IFF:
  case XOR:
    return toString(f->left(),c) + con + toString(f->right(),c);

  case NOT:
    if (f->uarg()->connective() == LITERAL &&
	    f->uarg()->literal()->isEquality()) {
      Literal* l = f->uarg()->literal();
      return toString(l->nthArgument(0)) + " \\neq " + toString(l->nthArgument(1));
    }
    return con + toString(f->uarg(),c);

  case FORALL:
  case EXISTS:
  {
    vstring result("(");
    VList::Iterator vs(f->vars());
    while (vs.hasNext()) {
      result += con + varToString(vs.next()) + vstring(" ");
    }
    return result + ")" + toString(f->qarg(),c);
  }

  case BOOL_TERM:
    return f->getBooleanTerm().toString();

  case FALSE:
  case TRUE:
    return con;
  
  case NAME:
    return replaceNeg(static_cast<const NamedFormula*>(f)->name());

  case NOCONN:
    ASSERTION_VIOLATION_REP(c);
  }

  ASSERTION_VIOLATION;
} // LaTeX::toString (const Formula&)

/**
 * Convert the formula in scope of another formula
 * to LaTeX.
 * @param f the formula
 * @param outer connective of the outer formula
 * @since 09/12/2003 Manchester
 */
vstring LaTeX::toString (Formula* f, Connective outer) const
{
  CALL("LaTeX::toString (Formula* f, Connective outer)");

  return f->parenthesesRequired(outer) ?
	  vstring("(") + toString(f) + ")" :
	  toString(f);
} // LaTeX::toString (const Formula&, Connective outer)


/**
 * Convert clause to LaTeX.
 * @since 23/10/2003 Manchester, implemented as stream output function
 * @since 09/12/2003 Manchester
 */
vstring LaTeX::toString (Clause* c)
{
  CALL("LaTeX::toString (Clause* c)");

  vstring result;

  if (c->isEmpty()) {
    if(c->splits() && !c->splits()->isEmpty()){
      SplitSet::Iterator sit(*c->splits());
      result = "\\mathit{false}";
      while(sit.hasNext()){
        result += vstring(" \\Vor ") + replaceNeg(Saturation::Splitter::getFormulaStringFromName(sit.next(),true /*negated*/));
      }
    }
    else{
      result = "\\VEmptyClause";
    }
  }
  else {
    result = toString((*c)[0]);

    unsigned clen=c->length();
    for(unsigned i=1;i<clen;i++) {
      result += vstring(" \\Vor ") + toString((*c)[i]);
    }
    if(c->splits() && !c->splits()->isEmpty()){
      SplitSet::Iterator sit(*c->splits());
      while(sit.hasNext()){
        result += vstring(" \\Vor ") + replaceNeg(Saturation::Splitter::getFormulaStringFromName(sit.next(),true /*negated*/));
      }
    }
  }

  return result;
} // LaTeX::toString (const Clause& c)


/**
 * Convert literal to LaTeX.
 * @since 09/12/2003 Manchester
 */
vstring LaTeX::toString (Literal* l) const
{
  CALL("LaTeX::toString (Literal* l)");

  if (l->isEquality()) {
    if (l->isNegative()) {
      return toString(l->nthArgument(0),true) + " \\neq " + toString(l->nthArgument(1),true);
    }
    else {
      return toString(l->nthArgument(0),true) + " = " + toString(l->nthArgument(1),true);
    }
  }

//   if (_map) {
//     vstring result;
//     if (_map->toString(a,*this,result)) {
//       return result;
//     }
//   }

  //Check if this symbol has an interpreted LaTeX name
  // this should be true for all known interpreted symbols and any recorded symbols
  vstring template_str = theory->tryGetInterpretedLaTeXName(l->functor(),true,l->isNegative());

  if(template_str.empty()){
    vstring res;
    if (l->isNegative()) { res="\\neg ";}
    return res+symbolToString(l->functor(), true) + toString(l->args());
  }
  else{
    // replace arguments in the template, arg0 replaces a0 etc.
    for(unsigned i=0;i<l->arity();i++){
      vstring from = "a"+Lib::Int::toString(i);
      vstring to = toString(l->nthArgument(i),true);
      size_t start_pos = 0;
      while((start_pos = template_str.find(from, start_pos)) != std::string::npos) {
         template_str.replace(start_pos, from.length(), to);
         start_pos += to.length(); 
      }
    }
    return template_str;
  }

} // LaTeX::toString (const Literal& l)


/**
 * Output function or predicate symbol in LaTeX
 *
 * @since 05/10/2002 Manchester
 * @since 23/10/2002 Manchester, changed to handle special KIF names
 * @since 09/09/2003 Manchester, changed to use string instead of char*
 * @since 25/07/2005 Tallinn, changed to parse the name symbol by symbol
 * @since 07/08/2014 Manchester, changed to use vstring
 */
vstring LaTeX::symbolToString (unsigned num, bool pred) const
{
  CALL("LaTeX::symbolToString (unsigned num, bool pred)");

  vstring symbolName; // the name of this symbol, if any

  if(pred) {
    symbolName = env.signature->predicateName(num);
  }
  else {
//    if (f.isSkolemFunction()) {
//      return (vstring)"\\sigma_{" + Int::toString(f.number()) + "}";
//    }
    symbolName = env.signature->functionName(num);
  }

  // cut names longer than 8000 symbols
#define LENGTH 8004
  char newName[LENGTH]; // LaTeX name of this symbol
  char* name = newName;
  auto substr = symbolName.substr(0,8000);
  const char* nm = substr.c_str();
  // finding end of the name
  const char* end = nm;
  while (*end) {
    end++;
  }
  // finding the tail consisting only of digits and turning it into
  // the LaTeX index
  const char* digits = end;
  while (nm != digits) {
    if (digits[-1] >= '0' && digits[-1] <= '9') {
      digits--;
    }
    else {
      break;
    }
  }
  if (digits == nm) { // digit-only name
    return symbolName;
  }
  else{
    if(digits[-1] == '.'){
      //check if this is a real digit-only name
      // i.e. of the form digts.digits
      const char* digits_real = digits;
      digits_real--;
      while(nm != digits_real){
        if (digits_real[-1] >= '0' && digits_real[-1] <= '9') {
          digits_real--;
        }
        else {
          break;
        }
      }
      if(digits_real == nm){ // real digit-only name
        return symbolName;
      }
    }
  }
  while (nm < digits) {
    switch (*nm) {
    case '$':
    case '_':
      *name++ = '\\';
      *name++ = *nm;
      break;
    default:
      *name++ = *nm;
      break;
    }
    nm++;
  }
  if (digits == end) {
    *name = 0;
    return vstring("\\mathit{") + newName + '}';
  }
  // copy digits as an index
  *name++ = '_';
  *name++ = '{';
  while (digits != end) {
    *name++ = *digits++;
  }
  *name++ = '}';
  *name = 0;
  return vstring("\\mathit{") + newName + '}';
}


/**
 * Convert term list to LaTeX.
 *
 * If it is a single term then we do not look at the next term in the
 * TermList (important to dictate in some cases) and we do not place it
 * in brackets to try and reduce the number of brackets
 *
 * @since 09/12/2003 Manchester
 */
vstring LaTeX::toString (TermList* terms,bool single) const
{
  CALL("LaTeX::toString (TermList* terms)");

  if (terms->isEmpty()) {
    return "";
  }

  vstring result = single ? "" : " (";
  bool first=true;
  TermList* t=terms;
  while(t->isNonEmpty()) {

    if(first){
      first=false;
    }
    else{
        result += ",";
    }

//   if (_map) {
//     vstring result;
//     if (_map->toString(t,*this,result)) {
//       return result;
//     }
//   }
    if(t->isVar()) {
      ASS(t->isOrdinaryVar());
      result += varToString(t->var()); 
    }
    else {
      ASS(t->isTerm());
      Term* trm=t->term();

     //Check if this symbol has an interpreted LaTeX name
     // this should be true for all known interpreted symbols and any recorded symbols
      vstring template_str = theory->tryGetInterpretedLaTeXName(trm->functor(),false);
   
      if(template_str.empty()){
        result += symbolToString(trm->functor(), false) + toString(trm->args());
      }
      else{
        // replace arguments in the template, arg0 replaces a0 etc.
        for(unsigned i=0;i<trm->arity();i++){
          vstring from = "a"+Lib::Int::toString(i);
          vstring to = toString(trm->nthArgument(i),true);
          size_t start_pos = 0;
          while((start_pos = template_str.find(from, start_pos)) != std::string::npos) {
            template_str.replace(start_pos, from.length(), to);
            start_pos += to.length();
          }
        }
        result += template_str;
      }
    }

    if(single) break;
    t=t->next();
  }
  return single? result : result + ")";
}


// /**
//  * Convert unit to LaTeX.
//  * @since 09/12/2003 Manchester
//  */
// vstring LaTeX::toString (const Unit& u) const
// {
//   TRACER("LaTeX::toString (const Unit& u)");

//   vstring prefix = Int::toString(u.number()) + ". ";
//   vstring postfix = vstring("(") + Unit::toString(u.inputType()) + ")";

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

vstring LaTeX::getClauseLatexId(Unit* cs)
{
  return Int::toString(cs->number());
}

vstring LaTeX::toStringAsInference(Unit* cs, InferenceStore::FullInference* inf)
{
  CALL("LaTeX::toStringAsInference(ClauseSpec,FullInference*)");

  vstring res("\\begin{VampireStep}\n[$");

  bool hasParents=inf->premCnt;
  for(unsigned i=0;i<inf->premCnt;i++) {
    Unit* prem=inf->premises[i];
    res += getClauseLatexId(prem);
    if(i+1<inf->premCnt) {
	res += ",";
    }
  }
  if(hasParents) {
    res += "\\rightarrow ";
  }
  res += getClauseLatexId(cs)
    +"$, "+ruleName(inf->rule)+"]\\\\\n";

  res += "\\[\\begin{VampireInference}\n";

  if(hasParents) {
    for(unsigned i=0;i<inf->premCnt;i++) {
      Unit* prem=inf->premises[i];
      res += "\\begin{VampirePremise}%\n~~";
      res += toString(prem->asClause());
      res += "\n\\end{VampirePremise}\n";
      if(i+1<inf->premCnt) {
	res += "\\VPremiseSeparator\n";
      }
    }
    res += "\\VConclusionSeparator\n";
  }

  res += "\\begin{VampireConclusion}\n~~";

  res += toString(cs->asClause());

  return res + "\n\\end{VampireConclusion}\n\\end{VampireInference}\n\\]\n\\end{VampireStep}\\n";
}

/**
 * Convert inference without propositional part to LaTeX.
 * @since 23/10/2002 Manchester, as stream output function
 * @since 09/12/2003 Manchester
 */
vstring LaTeX::toStringAsInference(Unit* unit)
{
  CALL("LaTeX::toStringAsInference(Unit* unit)");

  Inference& inf = unit->inference();

  vstring res("\\begin{VampireStep}\n[$");

  bool hasParents=false;
  Inference::Iterator it = inf.iterator();
  while (inf.hasNext(it)) {
    hasParents=true;
    Unit* prem=inf.next(it);
    res += Int::toString(prem->number());
    if(inf.hasNext(it)) {
	res += ",";
    }
  }
  if(hasParents) {
    res += "\\rightarrow ";
  }
  res += Int::toString(unit->number())+"$, "+ruleName(inf.rule())+"]\\\\\n";

  res += "\\[\\begin{VampireInference}\n";

  if(hasParents) {
    it = inf.iterator();
    while (inf.hasNext(it)) {
	Unit* prem=inf.next(it);
      res += "\\begin{VampirePremise}%\n~~";
      res += toString(prem);
      res += "\n\\end{VampirePremise}\n";
	if(inf.hasNext(it)) {
	  res += "\\VPremiseSeparator\n";
	}
    }
    res += "\\VConclusionSeparator\n";
  }

  res += "\\begin{VampireConclusion}\n~~";

  res += toString(unit);

  return res + "\n\\end{VampireConclusion}\n\\end{VampireInference}\n\\]\n\\end{VampireStep}\n";
}

/*
vstring LaTeX::splittingToString(InferenceStore::SplittingRecord* sr)
{
  CALL("LaTeX::splittingToString");

  vstring res("[$");
  res += getClauseLatexId(sr->premise);


  Stack<pair<int,Clause*> >::Iterator ncit(sr->namedComps);
  while(ncit.hasNext()) {
    res += vstring(",")+Int::toString(ncit.next().second->number())+"_D";
  }
  res += "\\rightarrow ";
  res += getClauseLatexId(sr->result)
    +"$, "+Inference::ruleName(Inference::SPLITTING)+"]\\\\*[-2ex]\n";


  res += "\\[\\begin{VampireInference}\n";

  res += "\\begin{VampirePremise}%\n~~";
  res += toString(sr->premise.cl());
  res += "\n\\end{VampirePremise}\n";

  Stack<pair<int,Clause*> >::Iterator ncit2(sr->namedComps);
  while(ncit2.hasNext()) {
    pair<int,Clause*> nrec=ncit2.next();
    res += "\\VPremiseSeparator\n";
    res += "\\begin{VampirePremise}%\n~~";
    if(nrec.first>0) {
      res += getBDDVarName(nrec.first);
    }
    else {
      res += "\\neg " + getBDDVarName(-nrec.first);
    }
    res += "\\Viff" + toString(nrec.second);
    res += "\n\\end{VampirePremise}\n";
  }
  res += "\\VConclusionSeparator\n";

  res += "\\begin{VampireConclusion}\n~~";

  res += toString(sr->result.cl());

  return res + "\n\\end{VampireConclusion}\n\\end{VampireInference}\n\\]\n";
}
*/


/**
 * Convert variable to LaTeX.
 * @since 09/12/2003 Manchester
 * @since 17/9/2005 flight Chicago-Frankfurt, row variables case added
 */
vstring LaTeX::varToString (unsigned num) const
{
  CALL("LaTeX::varToString (unsigned num)");

//  if (v.toInt() < 0) { // row variable
//    return vstring("@_{") + Int::toString(-v.toInt()) + "}";
//  }
//#if KIF_EXPERIMENTS
//  switch (v.toInt()) {
//  case 0:
//    return "x";
//  case 1:
//    return "y";
//  case 2:
//    return "z";
//  case 3:
//    return "u";
//  case 4:
//    return "v";
//  case 5:
//    return "w";
//  default:
//    break;
//  }
//#endif

  return vstring("x_{") + Int::toString(num) + "}";
} // LaTeX::toString (Var v)


// /**
//  * Output ref in the LaTeX form if options say so. The output is made
//  * in the file specified in options.
//  * @since 27/06/2004 Manchester
//  */
// void LaTeX::output (const Refutation& ref) const
// {
//   TRACER("LaTeX::output (const Refutation& ref)");

//   vstring fileName = _options.latexOutput();
//   if (fileName == "off") {
//     return;
//   }
//   vstring refutation = toString(ref);
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
// vstring LaTeX::toString (const vstring& funOrPred,const TermList& args) const
// {
//   return funOrPred + toString(args);
// }


}
