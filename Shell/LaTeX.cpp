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
// #include "Refutation.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

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


/**
 * Convert the refutation to LaTeX
 * @since 04/01/2004 Manchester
 */
string LaTeX::refutationToString(Unit* ref)
{
  CALL("LaTeX::refutationToString(Unit* ref)");

  string res = "\\documentclass[fleqn]{article}\n"
    "\\usepackage{fullpage,latexsym}\n"

    "\\newenvironment{VampireProof}{%\n"
    "	\\section{Proof}}{}\n"
    "\\newenvironment{VampireInference}{%\n"
    "	\\begin{array}{c}}{\\end{array}}\n"
    "\\newenvironment{VampireInferencePremises}{}{}\n"
    "\\newenvironment{VampirePremise}%\n"
    "	{\\begin{array}{l}}%\n"
    "	{\\end{array}}\n"
    "\\newenvironment{VampireConclusion}%\n"
    "	{\\begin{array}{l}}%\n"
    "	{\\end{array}}\n"
    "\\newcommand{\\VampireUnit}[3]{%\n"
    "	#1.~#2~[#3]}\n"

    "\\newcommand{\\VPremiseSeparator}{\\\\}\n"
    "\\newcommand{\\VConclusionSeparator}{\\\\ \\hline}\n"

    "\\newcommand{\\Vor}{\\vee}\n"
    "\\newcommand{\\Vand}{\\wedge}\n"
    "\\newcommand{\\Vimp}{\\rightarrow}\n"
    "\\newcommand{\\Viff}{\\leftrightarrow}\n"
    "\\newcommand{\\Vxor}{\\not\\Viff}\n"

    "\\newcommand{\\VEmptyClause}{\\Box}\n"

    "\\begin{document}\n"
    "\\begin{VampireProof}\n";


  InferenceStore* is=InferenceStore::instance();

  Stack<UnitSpec> outKernel;
  Set<UnitSpec> handledKernel;
  Stack<Unit*> outShell;
  Set<Unit*> handledShell;

  if( ref->isClause() ) {
    Clause* refCl=static_cast<Clause*>(ref);
    UnitSpec cs=UnitSpec(refCl);
    outKernel.push(cs);
    handledKernel.insert(cs);
  } else {
    outShell.push(ref);
    handledShell.insert(ref);
  }

  while(outKernel.isNonEmpty()) {
    UnitSpec cs=outKernel.pop();
    InferenceStore::FullInference* finf;
    if(is->findInference(cs, finf)) {
      InferenceStore::SplittingRecord* srec;
      if(finf->rule==Inference::SPLITTING && is->findSplitting(cs, srec)) {
	if(!handledKernel.contains(srec->premise)) {
	  handledKernel.insert(srec->premise);
	  outKernel.push(srec->premise);
	}
	res+=splittingToString(srec);
	continue;
      }

      res+=toStringAsInference(cs, finf);

      for(unsigned i=0;i<finf->premCnt;i++) {
	UnitSpec prem=finf->premises[i];
	ASS(prem!=cs);

	if(!handledKernel.contains(prem)) {
	  handledKernel.insert(prem);
	  outKernel.push(prem);
	}
      }

    } else {
      Clause* cl=cs.cl();
      Inference* inf = cl->inference();

      res+=toStringAsInference(cl);
      Inference::Iterator it = inf->iterator();
      while (inf->hasNext(it)) {
	Unit* prem=inf->next(it);
	if(prem->isClause() ) {
	  //this branch is for clauses that were inserted as input into the SaturationAlgorithm object
          //Giles. Removed bdds from this, but not sure if this is redundant anyway given the previous comment.
	  UnitSpec premCS=UnitSpec(prem);

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
  }

  while(outShell.isNonEmpty()) {
    Unit* unit=outShell.pop();
    Inference* inf = unit->inference();

    res+=toStringAsInference(unit);
    Inference::Iterator it = inf->iterator();
    while (inf->hasNext(it)) {
      Unit* prem=inf->next(it);
      if(!handledShell.contains(prem)) {
	handledShell.insert(prem);
	outShell.push(prem);
      }
    }
  }

  if(definitionStack.isNonEmpty()) {
    res+="\\section{BDD Definitions}\n";
    for(unsigned i=0;i<definitionStack.length();i++) {
      res+=definitionStack[i];
    }
  }

  return res + "\\end{VampireProof}\n"
    "\\end{document}\n";
}


string LaTeX::toString(Unit* u)
{
  CALL("LaTeX::toString(Unit* u)");

  if(u->isClause()) {
    return toString(static_cast<Clause*>(u));
  } else {
    return toString(static_cast<FormulaUnit*>(u)->formula());
  }
}


/**
 * Convert the formula to LaTeX
 *
 * @since 12/10/2002 Tbilisi, implemented as ostream output function
 * @since 09/12/2003 Manchester
 * @since 11/12/2004 Manchester, true and false added
 * @since 29/04/2005 Manchester, inequality instead of negation of equality
 */
string LaTeX::toString (Formula* f) const
{
  CALL("LaTeX::toString(Formula* f)");

  static string names [] =
  { "", " \\Vand ", " \\Vor ", " \\Vimp ", " \\Viff ", " \\Vxor ",
	  "\\neg ", "\\forall ", "\\exists ", "\bot", "\top"};

  Connective c = f->connective();
  string con = names[(int)c];
  switch (c) {
  case LITERAL:
    return toString(f->literal());

  case AND:
  case OR:
  {
    FormulaList::Iterator arg(f->args());
    ASS(arg.hasNext());
    string result = toString(arg.next(),c);
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
    string result("(");
    Formula::VarList::Iterator vs(f->vars());
    while (vs.hasNext()) {
      result += con + varToString(vs.next()) + string(" ");
    }
    return result + ")" + toString(f->qarg(),c);
  }

  case FALSE:
  case TRUE:
    return con;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // LaTeX::toString (const Formula&)

/**
 * Convert the formula in scope of another formula
 * to LaTeX.
 * @param f the formula
 * @param outer connective of the outer formula
 * @since 09/12/2003 Manchester
 */
string LaTeX::toString (Formula* f, Connective outer) const
{
  CALL("LaTeX::toString (Formula* f, Connective outer)");

  return f->parenthesesRequired(outer) ?
	  string("(") + toString(f) + ")" :
	  toString(f);
} // LaTeX::toString (const Formula&, Connective outer)


/**
 * Convert clause to LaTeX.
 * @since 23/10/2003 Manchester, implemented as stream output function
 * @since 09/12/2003 Manchester
 */
string LaTeX::toString (Clause* c)
{
  CALL("LaTeX::toString (Clause* c)");

  string result;

  if (c->isEmpty()) {
    result = "\\VEmptyClause";
  }
  else {
    result = toString((*c)[0]);

    unsigned clen=c->length();
    for(unsigned i=1;i<clen;i++) {
      result += string(" \\Vor ") + toString((*c)[i]);
    }
  }

  return result;
} // LaTeX::toString (const Clause& c)


/**
 * Convert literal to LaTeX.
 * @since 09/12/2003 Manchester
 */
string LaTeX::toString (Literal* l) const
{
  CALL("LaTeX::toString (Literal* l)");

  if (l->isEquality()) {
    if (l->isNegative()) {
      return toString(l->nthArgument(0)) + " \\neq " + toString(l->nthArgument(1));
    }
    else {
      return toString(l->nthArgument(0)) + "=" + toString(l->nthArgument(1));
    }
  }

//   if (_map) {
//     string result;
//     if (_map->toString(a,*this,result)) {
//       return result;
//     }
//   }

  string res;

  if (l->isNegative()) {
    res="\\neg ";
  }
  res+=symbolToString(l->functor(), true) + toString(l->args());

  return res;
} // LaTeX::toString (const Literal& l)


/**
 * Output function or predicate symbol in LaTeX
 *
 * @since 05/10/2002 Manchester
 * @since 23/10/2002 Manchester, changed to handle special KIF names
 * @since 09/09/2003 Manchester, changed to use string instead of char*
 * @since 25/07/2005 Tallinn, changed to parse the name symbol by symbol
 */
string LaTeX::symbolToString (unsigned num, bool pred) const
{
  CALL("LaTeX::symbolToString (unsigned num, bool pred)");

  string symbolName; // the name of this symbol, if any

  if(pred) {
    symbolName = env.signature->predicateName(num);
  }
  else {
//    if (f.isSkolemFunction()) {
//      return (string)"\\sigma_{" + Int::toString(f.number()) + "}";
//    }
    symbolName = env.signature->functionName(num);
  }

  // cut names longer than 8000 symbols
#define LENGTH 8004
  char newName[LENGTH]; // LaTeX name of this symbol
  char* name = newName;
  const char* nm = symbolName.substr(0,8000).c_str();
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
    return string("\\mathit{") + newName + '}';
  }
  // copy digits as an index
  *name++ = '_';
  *name++ = '{';
  while (digits != end) {
    *name++ = *digits++;
  }
  *name++ = '}';
  *name = 0;
  return string("\\mathit{") + newName + '}';
}


/**
 * Convert term list to LaTeX.
 * @since 09/12/2003 Manchester
 */
string LaTeX::toString (TermList* terms) const
{
  CALL("LaTeX::toString (TermList* terms)");

  if (terms->isEmpty()) {
    return "";
  }

  string result = string("(");
  bool first=true;
  TermList* t=terms;
  while(t->isNonEmpty()) {
//   if (_map) {
//     string result;
//     if (_map->toString(t,*this,result)) {
//       return result;
//     }
//   }
    if(t->isVar()) {
      ASS(t->isOrdinaryVar());

    }
    else {
      ASS(t->isTerm());
      Term* trm=t->term();
      result += symbolToString(trm->functor(), false) + toString(trm->args());
    }

    t=t->next();
    if (first) {
      first=false;
    }
    else if(t->isNonEmpty()){
      result += ",";
    }
  }
  return result + ")";
}


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

string LaTeX::getClauseLatexId(UnitSpec cs)
{
  return Int::toString(cs.cl()->number())+"_{"+InferenceStore::instance()->getClauseIdSuffix(cs)+"}";
}

string LaTeX::toStringAsInference(UnitSpec cs, InferenceStore::FullInference* inf)
{
  CALL("LaTeX::toStringAsInference(ClauseSpec,FullInference*)");

  string res("[$");

  bool hasParents=inf->premCnt;
  for(unsigned i=0;i<inf->premCnt;i++) {
    UnitSpec prem=inf->premises[i];
    res += getClauseLatexId(prem);
    if(i+1<inf->premCnt) {
	res += ",";
    }
  }
  if(hasParents) {
    res += "\\rightarrow ";
  }
  res += getClauseLatexId(cs)
    +"$, "+Inference::ruleName(inf->rule)+"]\\\\*[-2ex]\n";

  res += "\\[\\begin{VampireInference}\n";

  if(hasParents) {
    for(unsigned i=0;i<inf->premCnt;i++) {
      UnitSpec prem=inf->premises[i];
      res += "\\begin{VampirePremise}%\n~~";
      res += toString(prem.cl());
      res += "\n\\end{VampirePremise}\n";
      if(i+1<inf->premCnt) {
	res += "\\VPremiseSeparator\n";
      }
    }
    res += "\\VConclusionSeparator\n";
  }

  res += "\\begin{VampireConclusion}\n~~";

  res += toString(cs.cl());

  return res + "\n\\end{VampireConclusion}\n\\end{VampireInference}\n\\]\n";
}

/**
 * Convert inference without propositional part to LaTeX.
 * @since 23/10/2002 Manchester, as stream output function
 * @since 09/12/2003 Manchester
 */
string LaTeX::toStringAsInference(Unit* unit)
{
  CALL("LaTeX::toStringAsInference(Unit* unit)");

  Inference* inf = unit->inference();

  string res("[$");

  bool hasParents=false;
  Inference::Iterator it = inf->iterator();
  while (inf->hasNext(it)) {
    hasParents=true;
    Unit* prem=inf->next(it);
    res += Int::toString(prem->number());
    if(inf->hasNext(it)) {
	res += ",";
    }
  }
  if(hasParents) {
    res += "\\rightarrow ";
  }
  res += Int::toString(unit->number())+"$, "+Inference::ruleName(inf->rule())+"]\\\\*[-2ex]\n";

  res += "\\[\\begin{VampireInference}\n";

  if(hasParents) {
    it = inf->iterator();
    while (inf->hasNext(it)) {
	Unit* prem=inf->next(it);
      res += "\\begin{VampirePremise}%\n~~";
      res += toString(prem);
      res += "\n\\end{VampirePremise}\n";
	if(inf->hasNext(it)) {
	  res += "\\VPremiseSeparator\n";
	}
    }
    res += "\\VConclusionSeparator\n";
  }

  res += "\\begin{VampireConclusion}\n~~";

  res += toString(unit);

  return res + "\n\\end{VampireConclusion}\n\\end{VampireInference}\n\\]\n";
}

string LaTeX::splittingToString(InferenceStore::SplittingRecord* sr)
{
  CALL("LaTeX::splittingToString");

  string res("[$");
  res += getClauseLatexId(sr->premise);


  Stack<pair<int,Clause*> >::Iterator ncit(sr->namedComps);
  while(ncit.hasNext()) {
    res += string(",")+Int::toString(ncit.next().second->number())+"_D";
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



/**
 * Convert variable to LaTeX.
 * @since 09/12/2003 Manchester
 * @since 17/9/2005 flight Chicago-Frankfurt, row variables case added
 */
string LaTeX::varToString (unsigned num) const
{
  CALL("LaTeX::varToString (unsigned num)");

//  if (v.toInt() < 0) { // row variable
//    return string("@_{") + Int::toString(-v.toInt()) + "}";
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
  return string("x_{") + Int::toString(num) + "}";
} // LaTeX::toString (Var v)


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


string LaTeX::getBDDVarName(int var)
{
  CALL("LaTeX::getBDDVarName(int var)");

  string name;
  if(BDD::instance()->getNiceName(var, name)) {
    return string("\\mathit{") + name + '}';
  }
  return string("\\mathit{b_{") + Int::toString(var) + "}}";
}

string LaTeX::toString(BDDNode* node)
{
  CALL("LaTeX::toString(BDDNode*)");

  BDD* inst=BDD::instance();

  //predicate and function symbols are mixed here, but it's how I understood it should be done
  if(inst->isTrue(node)) {
    return "\\top";
  }
  if(inst->isFalse(node)) {
    return "\\bot";
  }

  string name;
  if(_nodeNames.find(node, name)) {
    return name;
  }


  string propPred=getBDDVarName(node->_var);
  if(inst->isTrue(node->_pos) && inst->isFalse(node->_neg)) {
    return propPred;
  }
  else if(inst->isFalse(node->_pos) && inst->isTrue(node->_neg)) {
    return "\\neg "+propPred;
  }
  else if(inst->isTrue(node->_pos)) {
    return "("+propPred+" \\Vor "+toString(node->_neg)+")";
  }
  else if(inst->isFalse(node->_neg)) {
    return "("+propPred+" \\Vand "+toString(node->_pos)+")";
  }
  else if(inst->isFalse(node->_pos)) {
    return "(\\neg "+propPred+" \\Vand "+toString(node->_neg)+")";
  }
  else if(inst->isTrue(node->_neg)) {
    return "(\\neg "+propPred+" \\Vor "+toString(node->_pos)+")";
  }
  else {
    string posDef=toString(node->_pos);
    string negDef=toString(node->_neg);

    string name=string("\\mathit{n_{") + Int::toString(_nextNodeNum++) + "}}";
    string report="$"+name+" \\Viff ("+propPred+" ? "+posDef+" : "+negDef+")$\\\\\n";
    definitionStack.push(report);
    ALWAYS(_nodeNames.insert(node, name));

    return name;
  }

}


}
