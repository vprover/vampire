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
 * @file FiniteModelMultiSorted.cpp
 * Defines class for finite models
 *
 * @since 7/01/2016 Manchester
 * @author Giles
 */

#include <climits>

#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"
#include "Lib/DHMap.hpp"

#include "Shell/Options.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/SimplifyFalseTrue.hpp"
#include "Shell/Flattening.hpp"

#include "ArgsEnumerator.hpp"
#include "FiniteModelMultiSorted.hpp"

#define DEBUG_MODEL 0

namespace FMB{

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;

// the extent of sort s under the domain sizes sizes;
// a sort with no domain in this model (size 0 -- see the comment on _sizes) behaves as a
// singleton wherever a value of it is nevertheless called for, which is also what
// ArgsEnumerator does with a 0 bound (its do/while runs the first tuple in any case)
static unsigned domainSize(const DArray<unsigned>& sizes, unsigned s)
{
  unsigned size = sizes[s];
  return size > 0 ? size : 1;
}

// captures the encoding of a symbol's table:
// the row index of the tuple args in the table of a symbol of type sig,
// under the domain sizes sizes -- the first argument position changing fastest,
// i.e. the very order in which ArgsEnumerator enumerates the tuples
static size_t tableIndex(const DArray<unsigned>& args, const DArray<unsigned>& sizes, OperatorType* sig)
{
  size_t idx = 0;
  size_t mult = 1;
  for(unsigned i=0;i<args.size();i++){
    idx += mult*(args[i]-1);
    unsigned s = sig->arg(i).term()->functor();
    unsigned dim = domainSize(sizes,s);
    ASS_G(args[i],0); ASS_LE(args[i],dim); // domain elements are 1-based and inside their sort
    mult *= dim;
  }
  return idx;
}

// computes the number of rows of the table of a symbol of type sig under the domain sizes sizes
static size_t tableSize(OperatorType* sig, unsigned arity, const DArray<unsigned>& sizes)
{
  size_t size = 1;
  for(unsigned i=0;i<arity;i++) {
    unsigned mult = domainSize(sizes,sig->arg(i).term()->functor());
    if (mult > 1 && size > SIZE_MAX / mult) {
      INVALID_OPERATION("Model too large to represent!");
    }
    size *= mult;
  }
  return size;
}

// the layers of a symbol are owned by the model, so a stack that goes away has to be emptied
// by hand; both the destructor and the wholesale rebuilds in eliminateSortFunctionsAndPredicates
// go through here
static void deleteLayersIn(DArray<Stack<FunLayer*>>& f_layers, DArray<Stack<PredLayer*>>& p_layers)
{
  for(unsigned f=0; f<f_layers.size(); f++) {
    Stack<FunLayer*>& st = f_layers[f];
    while (st.isNonEmpty()) { delete st.pop(); }
  }
  for(unsigned p=0; p<p_layers.size(); p++) {
    Stack<PredLayer*>& st = p_layers[p];
    while (st.isNonEmpty()) { delete st.pop(); }
  }
}

void FiniteModelMultiSorted::deleteAllLayers()
{
  deleteLayersIn(_f_layers,_p_layers);
}

// the explicit table of a symbol, i.e. what the SAT assignment was copied into, or nullptr
// for a symbol that never got one. It is always the *bottom* layer: initTables is the only
// thing that builds a table, and it does so before anything else exists. (It was briefly the
// top layer instead, while materializePred could stack one over a trivial or definition
// layer; nothing does that any more.) Note this is a question about where the model's
// information came from, not about what currently speaks for the symbol -- for the latter,
// ask the topmost layer's kind, as toString does
static TableFunLayer* funTableIn(const DArray<Stack<FunLayer*>>& f_layers, unsigned f)
{
  const Stack<FunLayer*>& st = f_layers[f];
  return (st.isNonEmpty() && st[0]->_kind == LayerKind::TABLE) ?
    static_cast<TableFunLayer*>(st[0]) : nullptr;
}

static TablePredLayer* predTableIn(const DArray<Stack<PredLayer*>>& p_layers, unsigned p)
{
  const Stack<PredLayer*>& st = p_layers[p];
  return (st.isNonEmpty() && st[0]->_kind == LayerKind::TABLE) ?
    static_cast<TablePredLayer*>(st[0]) : nullptr;
}

TableFunLayer* FiniteModelMultiSorted::funTable(unsigned f) const
{
  return funTableIn(_f_layers,f);
}

TablePredLayer* FiniteModelMultiSorted::predTable(unsigned p) const
{
  return predTableIn(_p_layers,p);
}

unsigned FiniteModelMultiSorted::domainSizeOf(unsigned sort) const
{
  return domainSize(_sizes,sort);
}

size_t FiniteModelMultiSorted::tableIndexOf(OperatorType* sig, const DArray<unsigned>& args) const
{
  return tableIndex(args,_sizes,sig);
}

void FiniteModelMultiSorted::initTables()
{
  deleteAllLayers();

  _f_layers.ensure(env.signature->functions());
  _p_layers.ensure(env.signature->predicates());

  for(unsigned f=0; f<env.signature->functions();f++){
    if (!funUsed(f)) {
      // the SAT solver skipped some functions as they are eliminated
      // (the model, on the other hand, should be prepared to give them values later)
      continue; // not represented: no layers at all
    }
    const Signature::Symbol* symb = env.signature->getFunction(f);

    OperatorType* sig = symb->type();
    _f_layers[f].push(new TableFunLayer(sig,tableSize(sig,symb->arity(),_sizes),MODEL_ZERO));
  }

  // equality is never tabulated, so predicate 0 keeps an empty stack
  for(unsigned p=1; p<env.signature->predicates();p++){
    if (!predUsed(p)) {
      continue; // not represented
    }
    const Signature::Symbol* symb = env.signature->getPredicate(p);

    OperatorType* sig = symb->type();
    _p_layers[p].push(new TablePredLayer(sig,tableSize(sig,symb->arity(),_sizes),MODEL_ZERO));
  }
}

void FiniteModelMultiSorted::installTrivialLayers()
{
  ASS_EQ(_now,MODEL_ZERO+1); // model_0 has to be complete before the replay touches it

  for(unsigned f=0; f<env.signature->functions();f++){
    if (_f_layers[f].isEmpty()) {
#if FMB_CHECK_MODEL_AGAINST_INPUT
      unsigned srt = env.signature->getFunction(f)->type()->result().term()->functor();
      _f_layers[f].push(new TrivialFunLayer(srt,Random::getInteger(INT_MAX),MODEL_ZERO));
#else
      _f_layers[f].push(new TrivialFunLayer(MODEL_ZERO));
#endif
    }
  }
  // predicate 0 is equality, which evaluateLiteral answers without consulting the model
  for(unsigned p=1; p<env.signature->predicates();p++){
    if (_p_layers[p].isEmpty()) {
#if FMB_CHECK_MODEL_AGAINST_INPUT
      _p_layers[p].push(new TrivialPredLayer(Random::getInteger(INT_MAX),MODEL_ZERO));
#else
      _p_layers[p].push(new TrivialPredLayer(MODEL_ZERO));
#endif
    }
  }

  // The two boolean domain elements have to be genuinely represented, and are: FOOL
  // elimination puts them in the problem, so they have a usage count and hence a table. A
  // trivial layer would give both the same value, collapsing $true and $false onto one
  // element -- boolValue would stop distinguishing them and toString's domain print would
  // name the same element twice.
  // Unless neither occurs: NewCNF defines them when it expands a quantifier over $o, and the
  // clauses can then lose every occurrence (![X:$o]: (X | ~X) becomes two tautologies,
  // checks/fmb/bool-builtin.p). Then $o has no domain in this model and nothing asks for one.
  ASS(!env.signature->foolConstantsDefined() ||
      (funRepresented(env.signature->getFoolConstantSymbol(true)) ==
       funRepresented(env.signature->getFoolConstantSymbol(false))));
}

unsigned FiniteModelMultiSorted::evalFun(unsigned f, const DArray<unsigned>& args, Timestamp asOf)
{
  Stack<FunLayer*>& st = _f_layers[f];
  for (unsigned i = st.size(); i > 0; i--) {
    if (st[i-1]->_born >= asOf) continue; // born after our reader; invisible to it
    unsigned v = st[i-1]->value(args,*this);
    if (v != FUNV_UNDEF) {
      return v;
    }
  }
  // the model has nothing to say about f on these arguments
  throw UndefinedValueException(env.signature->functionName(f));
}

char FiniteModelMultiSorted::evalPred(unsigned p, const DArray<unsigned>& args, Timestamp asOf)
{
  Stack<PredLayer*>& st = _p_layers[p];
  for (unsigned i = st.size(); i > 0; i--) {
    if (st[i-1]->_born >= asOf) continue; // born after our reader; invisible to it
    char v = st[i-1]->value(args,*this);
    if (v != INTP_UNDEF) {
      return v;
    }
  }
  throw UndefinedValueException(env.signature->predicateName(p));
}

unsigned FiniteModelMultiSorted::addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res)
{
  ASS_EQ(env.signature->functionArity(f),args.size());

  OperatorType* tp = env.signature->getFunction(f)->type();
  // a function's value must be a domain element of its result sort
  ASS_G(res,0); ASS_LE(res,domainSize(_sizes,tp->result().term()->functor()));

  DArray<unsigned>& tbl = funTable(f)->raw();
  size_t idx = tableIndex(args,_sizes,tp);

  ASS_L(idx, tbl.size());
  unsigned old = tbl[idx];
  tbl[idx] = res;
  return old;
}

char FiniteModelMultiSorted::addPredicateDefinition(unsigned p, const DArray<unsigned>& args, bool res)
{
  ASS_EQ(env.signature->predicateArity(p),args.size());

  DArray<char>& tbl = predTable(p)->raw();
  size_t idx = tableIndex(args,_sizes,env.signature->getPredicate(p)->type());

  ASS_L(idx, tbl.size());
  char old = tbl[idx];
  tbl[idx] = (res ? INTP_TRUE : INTP_FALSE);
  return old;
}

void FiniteModelMultiSorted::addSymbolicDefinition(Problem::FunDef* fd)
{
  ASS_G(_now,MODEL_ZERO);
  Stack<FunLayer*>& st = _f_layers[fd->_head->functor()];
  ASS(st.isEmpty());
  st.push(new DefFunLayer(fd,_now));
  _now++; // so that a definition added later reads this one
}

void FiniteModelMultiSorted::addSymbolicDefinition(Problem::PredDef* pd)
{
  ASS_G(_now,MODEL_ZERO);
  Stack<PredLayer*>& st = _p_layers[pd->_head->functor()];
  ASS(st.isEmpty());
  st.push(new DefPredLayer(pd,_now));
  _now++;
}

CondFlipPredLayer* FiniteModelMultiSorted::addCasesLayer(unsigned p)
{
  ASS_G(_now,MODEL_ZERO);
  CondFlipPredLayer* layer = new CondFlipPredLayer(_now);
  _p_layers[p].push(layer);
  _now++; // so that a definition added later reads it
  return layer;
}

// how Vampire spells the i-th variable, matching TermList::var(i).toString()
static std::string varName(unsigned i)
{
  return "X"+Int::toString(i);
}

bool FiniteModelMultiSorted::collectBodySymbols(TermList body, BodySymbols& out)
{
  Stack<TermList> todo;
  todo.push(body);
  while (todo.isNonEmpty()) {
    TermList cur = todo.pop();
    if (!cur.isTerm()) {
      continue;
    }
    Term* t = cur.term();
    if (t->isSort()) {
      continue; // sorts are built from type constructors, not from function symbols
    }
    if (t->isSpecial()) {
      switch (t->specialFunctor()) {
        case SpecialFunctor::FORMULA: // arity 0; everything is in the special data
          if (!collectBodySymbols(t->getSpecialData()->getFormula(),out)) {
            return false;
          }
          continue;
        case SpecialFunctor::ITE: // the condition is off to the side, the branches are arguments
          if (!collectBodySymbols(t->getSpecialData()->getITECondition(),out)) {
            return false;
          }
          break;
        case SpecialFunctor::COND: // conditions and branches alike are arguments
          break;
        default:
          return false;
      }
    } else {
      out.funs.push(t->functor());
    }
    for (unsigned i = 0; i < t->arity(); i++) {
      todo.push(*t->nthArgument(i));
    }
  }
  return true;
}

bool FiniteModelMultiSorted::collectBodySymbols(Formula* body, BodySymbols& out)
{
  SubformulaIterator sfit(body);
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    switch (sf->connective()) {
      case LITERAL: {
        Literal* lit = sf->literal();
        if (!lit->isEquality()) {
          out.preds.push(lit->functor());
        }
        for (unsigned i = 0; i < lit->arity(); i++) {
          if (!collectBodySymbols(*lit->nthArgument(i),out)) {
            return false;
          }
        }
        break;
      }
      case BOOL_TERM:
        if (!collectBodySymbols(sf->getBooleanTerm(),out)) {
          return false;
        }
        break;
      case FORALL:
      case EXISTS:
        for (VSList* vs = sf->vars(); vs; vs = vs->tail()) {
          TermList srt = vs->head().second;
          if (srt.isTerm()) {
            out.sorts.push(srt.term()->functor());
          }
        }
        break;
      default:
        break;
    }
  }
  return true;
}

std::string FiniteModelMultiSorted::toString()
{
  switch (env.options->fmbModelPrinting()) {
    case Options::FMBModelPrinting::EXPLICIT:
      return toStringExplicit();
    case Options::FMBModelPrinting::LAYERED:
      return toStringLayered();
  }
  ASSERTION_VIOLATION;
}

// the boolean domain elements are named after these two, so their definitions would just be
// the tautologies $true = $true and $false = $false
static bool funPrintable(unsigned f)
{
  return !env.signature->isFoolConstantSymbol(true,f) && !env.signature->isFoolConstantSymbol(false,f);
}

// Two predicates the parser puts in the signature are not symbols of the problem: a $distinct
// marker is TPTP's defined $distinct, and := (Signature::getDefPred) is the connective of a
// $let binding. Neither has an interpretation to print, and a declaration of either would not
// parse -- := is even polymorphic, which FMB's sorts cannot express at all
static bool predPrintable(unsigned p)
{
  return !env.signature->getPredicate(p)->distinctPred() && !env.signature->isDefPred(p);
}

/**
 * A sort with no domain in this model (size 0, see the comment on _sizes) still needs one
 * in print as soon as a printed symbol mentions it -- an unused symbol can, and every one
 * is printed, if only with its trivial value. Print it as the singleton the evaluation, and
 * hence the self-check, has used for it all along (domainSize), so that what we print is
 * the model that was checked. A sort that no printed symbol mentions stays unprinted.
 */
static void mentionSortsOf(DArray<bool>& sortPrinted, OperatorType* ot, bool withResult)
{
  for(unsigned i=0;i<ot->arity();i++){
    sortPrinted[ot->arg(i).term()->functor()] = true;
  }
  if (withResult) {
    sortPrinted[ot->result().term()->functor()] = true;
  }
}

std::string FiniteModelMultiSorted::domainConstantName(unsigned s, unsigned i)
{
  std::string sortNameLabel = (env.signature->isBoolCon(s)) ? "bool" : env.signature->typeConName(s);
  return append(prepend("fmb_", sortNameLabel),(std::string("_")+Lib::Int::toString(i)).c_str());
}

void FiniteModelMultiSorted::printDomains(std::ostream& modelStm, const DArray<bool>& sortPrinted, DomainNames& names)
{
  names.ensure(env.signature->typeCons());

  for(unsigned s=0;s<env.signature->typeCons();s++){
    if(!sortPrinted[s]) continue;
    unsigned size = domainSize(_sizes,s);

    // don't output interpreted sorts at all, we know what they are
    // ($o is the exception: FMB models it like any other sort -- FOOL elimination and
    // TheoryAxioms::applyFOOL turn the booleans into ordinary terms and axioms -- only its
    // two domain elements are built-in and already named, see below)
    if(env.signature->isInterpretedNonDefault(s) && !env.signature->isBoolCon(s))
      continue;

    std::string sortName = env.signature->typeConName(s);
    std::string sortNameLabel = (env.signature->isBoolCon(s)) ? "bool" : sortName;

    // skip declaring $i and $o, we know what they are
    if(!env.signature->isDefaultSortCon(s))
      // Sort declaration
      modelStm << "tff(" << prepend("declare_", sortNameLabel) << ",type,"<<sortName<<":$tType)." <<endl;

    names[s].ensure(size+1);

    if(env.signature->isBoolCon(s)){
      // The two boolean domain elements are FOOL's term-level booleans, printed as $true and
      // $false (or, under -show_fool on, as the internal $$true / $$false -- which the parser
      // does not accept in term position, so such a model is for reading only).
      // Which element is which is what this model says about the two constants; there are no
      // type declarations to emit for them, they are built-in.
      ASS_EQ(size,2);
      ASS(env.signature->foolConstantsDefined());
      for (unsigned i = 0; i < 2; i++) {
        bool isTrue = (i > 0);
        names[s][boolValue(isTrue)] =
          env.signature->functionName(env.signature->getFoolConstantSymbol(isTrue));
      }
      ASS_NEQ(names[s][1],names[s][2]);
    } else {
      // Domain constant declarations
      for(unsigned i=1;i<=size;i++){
        modelStm << "tff(" << append(prepend("declare_", sortNameLabel), Int::toString(i).c_str()) << ",type,";
        std::string cname = domainConstantName(s,i);
        names[s][i]=cname;
        modelStm << cname << ":" << sortName << ")." << endl;
      }
    }

    //Output domain
    modelStm << "tff(" << prepend("finite_domain_", sortNameLabel) << ",axiom," << endl;
    modelStm << "      ! [X:" << sortName << "] : (" << endl;
    modelStm << "         ";
    for(unsigned i=1;i<=size;i++){
      // the parentheses matter for $o: our own parser reads an unbracketed
      // "X = $false | X = $true" as "X = ($false | X = $true)"
      modelStm << "(X = " << names[s][i] << ")";
      if(i<size) modelStm << " | ";
      if(i==size) modelStm << endl;
      else if(i%5==0) modelStm << endl << "         ";
    }
    modelStm << "      ) )." <<endl;
    //Distinctness of domain
    modelStm << endl;
    if(size>1){
    modelStm << "tff(" << prepend("distinct_domain_", sortNameLabel) << ",axiom," << endl;
    modelStm << "         ";
    unsigned c=0;
    for(unsigned i=1;i<=size;i++){
      for(unsigned j=i+1;j<=size;j++){
        c++;
        modelStm << names[s][i] <<" != " << names[s][j];
        if(!(i==size-1 && j==size)){
           modelStm << " & ";
           if(c%5==0){ modelStm << endl << "         "; }
        }
        else{ modelStm << endl; }
      }
    }
    modelStm << ")." << endl << endl;
    }
  }
}

void FiniteModelMultiSorted::printFunType(std::ostream& modelStm, unsigned f, const std::string& name)
{
  const Signature::Symbol* symb = env.signature->getFunction(f);
  unsigned arity = symb->arity();

  OperatorType* ot = symb->type();
  modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<" : ";
  if (arity>0) {
    modelStm << "( ";
    for(unsigned i=0;i<arity;i++){
      modelStm << ot->arg(i).toString();
      if(i+1 < arity) modelStm << " * ";
    }
    modelStm << " ) > ";
  }
  modelStm << ot->result().toString() << ")." << endl;
}

void FiniteModelMultiSorted::printPredType(std::ostream& modelStm, unsigned p, const std::string& name)
{
  const Signature::Symbol* symb = env.signature->getPredicate(p);
  unsigned arity = symb->arity();
  OperatorType* ot = symb->type();
  modelStm << "tff("<<prepend("declare_", name)<<",type,"<<name<<": "; //"(";
  if (arity>0) {
    modelStm << "( ";
    for(unsigned i=0;i<arity;i++){
      TermList argST = ot->arg(i);
      unsigned argS = argST.term()->functor();
      modelStm << env.signature->typeConName(argS);
      if(i+1 < arity) modelStm << " * ";
    }
    modelStm << " ) > ";
  }
  modelStm << "$o )." << endl;
}

void FiniteModelMultiSorted::printFunTable(std::ostream& modelStm, unsigned f, const std::string& name, Timestamp asOf, const DomainNames& names)
{
  const Signature::Symbol* symb = env.signature->getFunction(f);
  unsigned arity = symb->arity();
  OperatorType* ot = symb->type();

  // A function into $o (FOOL elimination introduces such, e.g. the bG0 naming a boolean
  // subterm) is declared as f : ... > $o, which TPTP reads as a *predicate*; so a cell
  // f(...) = $false would read back as an equation between formulas, not a definition. Print
  // it the way it is read: as the predicate it then is, true where its value is $true's element
  if (env.signature->isBoolCon(ot->result().term()->functor())) {
    unsigned trueElement = boolValue(true);
    if (arity == 0) {
      bool res = (evalFun(f,DArray<unsigned>(0),asOf) == trueElement);
      modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<(res ? "" : "~")<<name<< ")."<<endl;
      return;
    }
    modelStm << "tff("<<prepend("predicate_", name)<<",axiom,"<<endl;
    bool first=true;
    ArgsEnumerator it(_sizes,ot,arity);
    do {
      const DArray<unsigned>& args = it.args();
      bool res = (evalFun(f,args,asOf) == trueElement);
      modelStm << (first ? "           " : "         & ");
      first=false;
      if(!res) modelStm << "~";
      modelStm << name << "(";
      for(unsigned j=0;j<arity;j++){
        if(j!=0) modelStm << ",";
        modelStm << names[ot->arg(j).term()->functor()][args[j]];
      }
      modelStm << ")" << endl;
    } while (it.next());
    modelStm << ")." << endl << endl;
    return;
  }

  if (arity == 0) {
    unsigned res = evalFun(f,DArray<unsigned>(0),asOf);
    ASS_G(res,0)

    TermList srtT = ot->result();
    unsigned srt = srtT.term()->functor();
    std::string cname = names[srt][res];

    modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<name<<" = " << cname << ")."<<endl;
  } else {
    modelStm << "tff("<<prepend("function_", name)<<",axiom,"<<endl;

    bool first=true;
    ArgsEnumerator it(_sizes,ot,arity);
    do {
      const DArray<unsigned>& args = it.args();
      unsigned res = evalFun(f,args,asOf);
      ASS_G(res,0)

      if (!first) {
        modelStm << "         & ";
      } else {
        modelStm << "           ";
      }
      first=false;
      modelStm << name << "(";
      for(unsigned j=0;j<arity;j++){
        if(j!=0) modelStm << ",";
        TermList argSortT = ot->arg(j);
        unsigned argSort = argSortT.term()->functor();
        modelStm << names[argSort][args[j]];
      }
      TermList resultSortT = ot->result();
      unsigned resultSort = resultSortT.term()->functor();
      modelStm << ") = " << names[resultSort][res] << endl;
    } while (it.next());
    modelStm << ")." << endl << endl;
  }
}

void FiniteModelMultiSorted::printPredTable(std::ostream& modelStm, unsigned p, const std::string& name, Timestamp asOf, const DomainNames& names)
{
  const Signature::Symbol* symb = env.signature->getPredicate(p);
  unsigned arity = symb->arity();
  OperatorType* ot = symb->type();

  if (arity==0) {
    char res = evalPred(p,DArray<unsigned>(0),asOf);
    if(res==INTP_TRUE){
      modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<name<< ")."<<endl;
    } else { // covers (res==INTP_FALSE) as well as undefined, which defaults to false
      modelStm << "tff("<<append(name,"_definition")<<",axiom,~"<<name<< ")."<<endl;
    }
  } else {
    modelStm << "tff("<<prepend("predicate_", name)<<",axiom,"<<endl;

    bool first=true;
    ArgsEnumerator it(_sizes,ot,arity);
    do {
      const DArray<unsigned>& args = it.args();
      char res = evalPred(p,args,asOf);
      ASS_NEQ(res,INTP_UNDEF)

      if (!first){
        modelStm << "         & ";
      } else {
        modelStm << "           ";
      }
      first=false;

      if(res==INTP_FALSE) modelStm << "~";
      modelStm << name << "(";
      for(unsigned j=0;j<arity;j++){
        if(j!=0) modelStm << ",";
        TermList argSortT = ot->arg(j);
        unsigned argSort = argSortT.term()->functor();
        modelStm << names[argSort][args[j]];
      }
      modelStm << ")";
      modelStm << endl;
    } while (it.next());
    modelStm << ")." << endl << endl;
  }
}

std::string FiniteModelMultiSorted::toStringExplicit()
{
  std::ostringstream modelStm;

  // Every symbol of the input, each as a table, and nothing else: no symbolic definition, so
  // no introduced symbol is ever needed -- the input does not mention any, and tables of its
  // own symbols are all it takes to evaluate it. This is the reference the layered printing
  // is compared against; the price is a table of every symbol, however large
  auto funPrinted = [&](unsigned f) {
    return funPrintable(f) && !env.signature->getFunction(f)->introduced();
  };
  auto predPrinted = [&](unsigned p) {
    return predPrintable(p) && !env.signature->getPredicate(p)->introduced();
  };

  DArray<bool> sortPrinted(env.signature->typeCons());
  for(unsigned s=0;s<sortPrinted.size();s++){
    sortPrinted[s] = (_sizes[s] > 0);
  }
  for(unsigned f=0;f<env.signature->functions();f++){
    if (funPrinted(f)) mentionSortsOf(sortPrinted,env.signature->getFunction(f)->type(),/*withResult=*/true);
  }
  for(unsigned p=1;p<env.signature->predicates();p++){
    if (predPrinted(p)) mentionSortsOf(sortPrinted,env.signature->getPredicate(p)->type(),/*withResult=*/false);
  }

  DomainNames names;
  printDomains(modelStm,sortPrinted,names);

  // Functions (including constants)
  for(unsigned f=0;f<env.signature->functions();f++){
    if(!funPrinted(f)) continue;
    const std::string& name = env.signature->functionName(f);
    printFunType(modelStm,f,name);
    printFunTable(modelStm,f,name,_now,names);
  }

  //Predicates (including propositions)
  for(unsigned p=1;p<env.signature->predicates();p++){
    if(!predPrinted(p)) continue;
    const std::string& name = env.signature->predicateName(p);
    printPredType(modelStm,p,name);
    printPredTable(modelStm,p,name,_now,names);
  }

  return modelStm.str();
}

// --- printing a definition's body, with each symbol spelled as the version it reads ---
//
// rename(pred,symbol) gives the name to print for a symbol. Only what FMB records as a body
// is covered: first-order terms and formulas, which is all there is after FOOL elimination;
// for anything else (a special term, a boolean term that is not a variable) these return
// false, having printed something incomplete, and the caller prints a table instead.

template<class Rename>
static bool printBodyTerm(std::ostream& out, TermList t, const Rename& rename)
{
  if (t.isVar()) {
    out << varName(t.var());
    return true;
  }
  Term* term = t.term();
  if (term->isSpecial()) {
    return false;
  }
  out << rename(false,term->functor());
  if (term->arity() == 0) {
    return true;
  }
  out << "(";
  for (unsigned i = 0; i < term->arity(); i++) {
    if (i) out << ",";
    if (!printBodyTerm(out,*term->nthArgument(i),rename)) {
      return false;
    }
  }
  out << ")";
  return true;
}

template<class Rename>
static bool printBodyFormula(std::ostream& out, Formula* f, const Rename& rename)
{
  switch (f->connective()) {
    case TRUE:
      out << "$true";
      return true;
    case FALSE:
      out << "$false";
      return true;
    case LITERAL: {
      Literal* l = f->literal();
      if (l->isEquality()) {
        // parenthesised wherever it stands: our parser reads "X = $false | ..." as
        // "X = ($false | ...)"
        out << "(";
        if (!printBodyTerm(out,*l->nthArgument(0),rename)) return false;
        out << (l->polarity() ? " = " : " != ");
        if (!printBodyTerm(out,*l->nthArgument(1),rename)) return false;
        out << ")";
        return true;
      }
      if (!l->polarity()) out << "~";
      out << rename(true,l->functor());
      if (l->arity() > 0) {
        out << "(";
        for (unsigned i = 0; i < l->arity(); i++) {
          if (i) out << ",";
          if (!printBodyTerm(out,*l->nthArgument(i),rename)) return false;
        }
        out << ")";
      }
      return true;
    }
    case BOOL_TERM: {
      TermList t = f->getBooleanTerm();
      if (!t.isVar()) return false;
      out << varName(t.var());
      return true;
    }
    case NOT:
      out << "~(";
      if (!printBodyFormula(out,f->uarg(),rename)) return false;
      out << ")";
      return true;
    case AND:
    case OR: {
      out << "(";
      bool first = true;
      FormulaList::Iterator it(f->args());
      while (it.hasNext()) {
        if (!first) out << (f->connective() == AND ? " & " : " | ");
        first = false;
        if (!printBodyFormula(out,it.next(),rename)) return false;
      }
      out << ")";
      return true;
    }
    case IMP:
    case IFF:
    case XOR:
      out << "(";
      if (!printBodyFormula(out,f->left(),rename)) return false;
      out << (f->connective() == IMP ? " => " : f->connective() == IFF ? " <=> " : " <~> ");
      if (!printBodyFormula(out,f->right(),rename)) return false;
      out << ")";
      return true;
    case FORALL:
    case EXISTS: {
      out << "(" << (f->connective() == FORALL ? "!" : "?") << " [";
      bool first = true;
      for (VSList* vs = f->vars(); vs; vs = vs->tail()) {
        if (!first) out << ", ";
        first = false;
        out << varName(vs->head().first) << ":" << vs->head().second.toString();
      }
      out << "] : ";
      if (!printBodyFormula(out,f->qarg(),rename)) return false;
      out << ")";
      return true;
    }
    default:
      return false;
  }
}

// The layer of a symbol's stack a reader born at born sees on top: the topmost one born
// before it (cf. evalFun). That is the version of the symbol a definition born at born reads.
// Every symbol has a layer from model_0 on (initTables / installTrivialLayers), so there is one
template<class Layer>
static unsigned layerAsOf(const Stack<Layer*>& st, Timestamp born)
{
  for (unsigned i = st.size(); i > 0; i--) {
    if (st[i-1]->_born < born) {
      return i-1;
    }
  }
  ASSERTION_VIOLATION;
  return 0;
}

/**
 * The body of a conditional flip of p, the layer-th of p's stack: a $cond with one case per
 * tuple the flip prescribes a value for, ((X0 = e) & ...), $true or $false -- a condition on
 * every argument, one case to a line -- and for every other tuple the version below, named
 * below. The cases are disjoint, so their order does not
 * matter; they come in the order of their tuples, for a reader's sake.
 */
void FiniteModelMultiSorted::printCases(std::ostream& out, unsigned p, unsigned layer, const std::string& below, const DomainNames& names)
{
  const CondFlipPredLayer* flip = static_cast<const CondFlipPredLayer*>(_p_layers[p][layer]);
  OperatorType* ot = env.signature->getPredicate(p)->type();
  unsigned arity = ot->arity();

  Stack<std::pair<ArgsKey,char>> cases;
  DHMap<ArgsKey,char, ArgsKeyHash, ArgsKeyHash2>::Iterator it(flip->prescribed());
  while (it.hasNext()) {
    ArgsKey args;
    char val;
    it.next(args,val);
    cases.push({args,val});
  }
  cases.sort([](const std::pair<ArgsKey,char>& a, const std::pair<ArgsKey,char>& b) {
    const DArray<unsigned>& x = a.first.args();
    const DArray<unsigned>& y = b.first.args();
    for (unsigned i = 0; i < x.size(); i++) {
      if (x[i] != y[i]) return x[i] < y[i];
    }
    return false;
  });

  std::string belowApplied = below;
  if (arity > 0) {
    belowApplied += "(";
    for (unsigned j = 0; j < arity; j++) {
      if (j) belowApplied += ",";
      belowApplied += varName(j);
    }
    belowApplied += ")";
  }
  auto value = [](char v) { ASS_NEQ(v,INTP_UNDEF); return v == INTP_TRUE ? "$true" : "$false"; };

  ASS(cases.isNonEmpty()); // a flip that would change nothing is not kept (restoreViaCondFlip)
  if (arity == 0) {
    out << value(cases[0].second); // the one tuple there is
    return;
  }
  // one case to a line, as a table has one cell to a line, then the fall-back on its own
  out << "$cond(" << endl;
  for (unsigned i = 0; i < cases.size(); i++) {
    const DArray<unsigned>& args = cases[i].first.args();
    out << "           (";
    for (unsigned j = 0; j < arity; j++) {
      if (j) out << " & ";
      // parenthesised: our parser reads "X = $false & ..." as "X = ($false & ...)"
      out << "(" << varName(j) << " = " << names[ot->arg(j).term()->functor()][args[j]] << ")";
    }
    out << "), " << value(cases[i].second) << "," << endl;
  }
  out << "           " << belowApplied << ")";
}

/**
 * Print the layer stacks rather than their final values. Each symbol is printed in the
 * *versions* the model needs, a version being the stack up to one of its layers, and each
 * version as that layer is: a definition as its body, over the versions of the body's
 * symbols it reads (as of its own birth, see DefFunLayer::value); a trivial value as a
 * formula; a conditional flip as a $cond, one case per tuple the flip prescribes a value for,
 * over the version directly below it for every other tuple; a global flip as the negation of
 * the version directly below it; and a table (or a trivial value under the self-check, or a
 * function into $o) as a table of the version's values.
 *
 * The final version of a symbol keeps the symbol's name. An earlier one is named by how many
 * layers lie above it: 'f_$1' is f before its last update, 'f_$2' before the one before, and
 * so on, with gaps wherever a version is not needed. (A flip that would change nothing is
 * not even kept, see restoreViaCondFlip.) The $ forces quoting, so that what
 * printing made up stands out. Should a made-up name be taken already, the separator grows
 * ('f__$1', ...), one separator for all of a symbol's versions.
 *
 * Which versions are needed, and the order to print them in, comes from a breadth-first
 * search: from the final versions of the input's own symbols (functions, then predicates,
 * each in signature order), on to the versions each printed definition reads, and the
 * version below each printed flip of either kind, in the order met. That is how an introduced symbol, or an earlier version, gets printed: only when a
 * printed definition needs it. All of it is settled first, because every type declaration
 * comes before every definition; a definition may then mention a version whose own
 * definition comes later.
 */
std::string FiniteModelMultiSorted::toStringLayered()
{
  enum class Rendering { DEFINITION, TRIVIAL, CASES, NEGATION, TABLE };
  struct Version { bool pred; unsigned sym; unsigned layer; Rendering how; };

  auto kindOf = [&](bool pred, unsigned sym, unsigned layer) {
    return pred ? _p_layers[sym][layer]->_kind : _f_layers[sym][layer]->_kind;
  };
  auto bornOf = [&](const Version& v) {
    return v.pred ? _p_layers[v.sym][v.layer]->_born : _f_layers[v.sym][v.layer]->_born;
  };
  auto bodyRename = [&](Timestamp born) {
    return [this,born](bool pred, unsigned s) -> std::string {
      return pred ? versionName(true,s,layerAsOf(_p_layers[s],born))
                  : versionName(false,s,layerAsOf(_f_layers[s],born));
    };
  };
  // print v's definition body into out; false if it is not something we can print
  auto printBody = [&](std::ostream& out, const Version& v, Timestamp born, auto rename) -> bool {
    if (v.pred) {
      Problem::PredDef* pd = static_cast<DefPredLayer*>(_p_layers[v.sym][v.layer])->def();
      if (pd->_head->isPositive()) return printBodyFormula(out,pd->_body,rename);
      out << "~(";
      bool ok = printBodyFormula(out,pd->_body,rename); // a negative head defines the complement
      out << ")";
      return ok;
    }
    Problem::FunDef* fd = static_cast<DefFunLayer*>(_f_layers[v.sym][v.layer])->def();
    return printBodyTerm(out,TermList(fd->_body),rename);
  };
  auto rendering = [&](bool pred, unsigned sym, unsigned layer) {
    Version v{pred,sym,layer,Rendering::TABLE};
    LayerKind kind = kindOf(pred,sym,layer);
    unsigned arity = pred ? env.signature->predicateArity(sym) : env.signature->functionArity(sym);
    // a function into $o reads back as a predicate, and its formula renderings (f(Xs) = t)
    // would not; its table is printed as the predicate's (see printFunTable)
    if (!pred && env.signature->isBoolCon(env.signature->getFunction(sym)->type()->result().term()->functor())) {
      return Rendering::TABLE;
    }
    if (kind == LayerKind::DEF) {
      std::ostringstream dummy;
      if (printBody(dummy,v,bornOf(v),[](bool,unsigned) { return std::string(); })) {
        return Rendering::DEFINITION;
      }
    }
    // A trivial value has a formula rendering only while it is a constant; under the
    // self-check it is pseudo-random junk instead. A symbol of arity 0 goes the same way
    // regardless: it has a single value, and printing that *is* the formula
    if (kind == LayerKind::TRIVIAL && !FMB_CHECK_MODEL_AGAINST_INPUT && arity > 0) {
      return Rendering::TRIVIAL;
    }
    if (kind == LayerKind::COND_FLIP) {
      ASS_G(layer,0); // a flip is never the bottom: every symbol has a layer from model_0 on
      return Rendering::CASES;
    }
    if (kind == LayerKind::GLOBAL_FLIP) {
      ASS_G(layer,0);
      return Rendering::NEGATION;
    }
    return Rendering::TABLE;
  };

  Stack<Version> order;
  // per symbol, which of its layers have been queued
  DArray<Stack<unsigned>> funQueued(env.signature->functions());
  DArray<Stack<unsigned>> predQueued(env.signature->predicates());
  auto queue = [&](bool pred, unsigned sym, unsigned layer) {
    if (pred ? (sym == 0 || !predPrintable(sym)) : !funPrintable(sym)) return; // equality is not in the model
    Stack<unsigned>& queued = (pred ? predQueued : funQueued)[sym];
    for (unsigned i = 0; i < queued.size(); i++) {
      if (queued[i] == layer) return;
    }
    queued.push(layer);
    order.push({pred,sym,layer,rendering(pred,sym,layer)});
  };

  for(unsigned f=0;f<env.signature->functions();f++){
    if (!env.signature->getFunction(f)->introduced() && funPrintable(f)) queue(false,f,_f_layers[f].size()-1);
  }
  for(unsigned p=1;p<env.signature->predicates();p++){
    if (!env.signature->getPredicate(p)->introduced() && predPrintable(p)) queue(true,p,_p_layers[p].size()-1);
  }

  DArray<bool> sortPrinted(env.signature->typeCons());
  for(unsigned s=0;s<sortPrinted.size();s++){
    sortPrinted[s] = (_sizes[s] > 0);
  }

  // order grows while we walk it; that is the queue
  for (unsigned i = 0; i < order.size(); i++) {
    Version cur = order[i];
    mentionSortsOf(sortPrinted,cur.pred ? env.signature->getPredicate(cur.sym)->type() : env.signature->getFunction(cur.sym)->type(),
                   /*withResult=*/!cur.pred);
    if (cur.how == Rendering::CASES || cur.how == Rendering::NEGATION) {
      queue(cur.pred,cur.sym,cur.layer-1); // what the flip leaves alone, or turns round
      continue;
    }
    if (cur.how != Rendering::DEFINITION) continue;
    Timestamp born = bornOf(cur);
    BodySymbols syms;
    if (cur.pred) {
      ALWAYS(collectBodySymbols(static_cast<DefPredLayer*>(_p_layers[cur.sym][cur.layer])->def()->_body,syms));
    } else {
      ALWAYS(collectBodySymbols(TermList(static_cast<DefFunLayer*>(_f_layers[cur.sym][cur.layer])->def()->_body),syms));
    }
    for (unsigned j = 0; j < syms.funs.size(); j++) queue(false,syms.funs[j],layerAsOf(_f_layers[syms.funs[j]],born));
    for (unsigned j = 0; j < syms.preds.size(); j++) queue(true,syms.preds[j],layerAsOf(_p_layers[syms.preds[j]],born));
    for (unsigned j = 0; j < syms.sorts.size(); j++) sortPrinted[syms.sorts[j]] = true;
  }

  chooseVersionSeparators(funQueued,predQueued,sortPrinted);

  std::ostringstream modelStm;
  DomainNames names;
  printDomains(modelStm,sortPrinted,names);

  for (unsigned i = 0; i < order.size(); i++) {
    const Version& v = order[i];
    std::string name = versionName(v.pred,v.sym,v.layer);
    if (v.pred) printPredType(modelStm,v.sym,name);
    else printFunType(modelStm,v.sym,name);
  }
  modelStm << endl;

  for (unsigned i = 0; i < order.size(); i++) {
    const Version& v = order[i];
    std::string name = versionName(v.pred,v.sym,v.layer);
    Timestamp born = bornOf(v);
    OperatorType* ot = v.pred ? env.signature->getPredicate(v.sym)->type() : env.signature->getFunction(v.sym)->type();
    unsigned arity = ot->arity();

    if (v.how == Rendering::TABLE) {
      // the version's values: everything up to and including its top layer
      if (v.pred) printPredTable(modelStm,v.sym,name,born+1,names);
      else printFunTable(modelStm,v.sym,name,born+1,names);
      continue;
    }

    // a definition's head is written with the definition's own variables
    Term* head = nullptr;
    if (v.how == Rendering::DEFINITION) {
      head = v.pred ? static_cast<Term*>(static_cast<DefPredLayer*>(_p_layers[v.sym][v.layer])->def()->_head)
                    : static_cast<DefFunLayer*>(_f_layers[v.sym][v.layer])->def()->_head;
    }
    auto var = [&](unsigned j) { return head ? head->nthArgument(j)->toString() : varName(j); };

    modelStm << "tff("<<append(name,"_symbolic_definition")<<",axiom,";
    if (arity > 0) { // quantify
      modelStm << "![";
      for (unsigned j = 0; j < arity; j++) {
        modelStm << var(j) << ":" << ot->arg(j).toString();
        if (j+1 < arity) modelStm << ", ";
      }
      modelStm << "]: ";
      if (v.pred) modelStm << "(";
    }
    modelStm << name;
    if (arity > 0) {
      modelStm << "(";
      for (unsigned j = 0; j < arity; j++) {
        if (j) modelStm << ",";
        modelStm << var(j);
      }
      modelStm << ")";
    }
    modelStm << (v.pred ? " <=> " : " = ");
    if (v.how == Rendering::DEFINITION) {
      ALWAYS(printBody(modelStm,v,born,bodyRename(born)));
    } else if (v.how == Rendering::CASES) {
      printCases(modelStm,v.sym,v.layer,versionName(true,v.sym,v.layer-1),names);
    } else if (v.how == Rendering::NEGATION) {
      modelStm << "~" << versionName(true,v.sym,v.layer-1);
      if (arity > 0) {
        modelStm << "(";
        for (unsigned j = 0; j < arity; j++) {
          if (j) modelStm << ",";
          modelStm << var(j);
        }
        modelStm << ")";
      }
    } else if (v.pred) {
      modelStm << "$false"; // the trivial layer's value
    } else {
      modelStm << names[ot->result().term()->functor()][1]; // the trivial layer's value
    }
    if (v.pred && arity > 0) modelStm << ")";
    modelStm << ")." << endl;
  }

  return modelStm.str();
}

/**
 * Settle, per symbol with an earlier version to print, the separator of its version names
 * (see toStringLayered): the first of "_$", "__$", ... under which none of its version names
 * is taken -- by a symbol or sort of the signature, a domain constant, or a version name
 * chosen before. Symbols go in signature order, so the choice is deterministic.
 */
void FiniteModelMultiSorted::chooseVersionSeparators(const DArray<Stack<unsigned>>& funQueued, const DArray<Stack<unsigned>>& predQueued,
                                                     const DArray<bool>& sortPrinted)
{
  DHSet<std::string, FnvHash, LengthHash> taken;
  for (unsigned f = 0; f < env.signature->functions(); f++) taken.insert(env.signature->functionName(f));
  for (unsigned p = 0; p < env.signature->predicates(); p++) taken.insert(env.signature->predicateName(p));
  for (unsigned s = 0; s < env.signature->typeCons(); s++) {
    taken.insert(env.signature->typeConName(s));
    if (!sortPrinted[s] || env.signature->isBoolCon(s)) continue;
    for (unsigned i = 1; i <= domainSize(_sizes,s); i++) taken.insert(domainConstantName(s,i));
  }

  _funVersionSep.init(env.signature->functions(),std::string());
  _predVersionSep.init(env.signature->predicates(),std::string());
  for (unsigned pass = 0; pass < 2; pass++) {
    bool pred = (pass == 1);
    const DArray<Stack<unsigned>>& queued = pred ? predQueued : funQueued;
    for (unsigned s = 0; s < queued.size(); s++) {
      if (queued[s].isEmpty()) continue;
      unsigned top = pred ? _p_layers[s].size()-1 : _f_layers[s].size()-1;
      const std::string& base = pred ? env.signature->predicateName(s) : env.signature->functionName(s);
      // the depths below the top this symbol is printed at
      Stack<unsigned> depths;
      for (unsigned i = 0; i < queued[s].size(); i++) {
        if (queued[s][i] != top) depths.push(top - queued[s][i]);
      }
      if (depths.isEmpty()) continue;
      std::string sep = "_$";
      auto free = [&]() {
        for (unsigned i = 0; i < depths.size(); i++) {
          if (taken.contains(versionName(base,sep,depths[i]))) return false;
        }
        return true;
      };
      while (!free()) {
        sep = "_" + sep;
      }
      for (unsigned i = 0; i < depths.size(); i++) taken.insert(versionName(base,sep,depths[i]));
      (pred ? _predVersionSep : _funVersionSep)[s] = sep;
    }
  }
}

// base, unquoted, with sep and depth appended, and quoted again ($ always needs quoting)
std::string FiniteModelMultiSorted::versionName(const std::string& base, const std::string& sep, unsigned depth)
{
  std::string inner = (base.size() >= 2 && base[0] == '\'') ? base.substr(1,base.size()-2) : base;
  return "'" + inner + sep + Int::toString(depth) + "'";
}

std::string FiniteModelMultiSorted::versionName(bool pred, unsigned sym, unsigned layer)
{
  if (!(pred ? predPrintable(sym) : funPrintable(sym))) {
    // $true / $false as terms: a domain element, printed as itself
    return pred ? env.signature->predicateName(sym) : env.signature->functionName(sym);
  }
  unsigned top = pred ? _p_layers[sym].size()-1 : _f_layers[sym].size()-1;
  const std::string& base = pred ? env.signature->predicateName(sym) : env.signature->functionName(sym);
  if (layer == top) {
    return base;
  }
  const std::string& sep = (pred ? _predVersionSep : _funVersionSep)[sym];
  ASS(!sep.empty()); // chooseVersionSeparators saw this version
  return versionName(base,sep,top-layer);
}

TermList FiniteModelMultiSorted::deFool(TermList tl)
{
  if (tl.isTerm() && tl.term()->isSpecial() &&
      tl.term()->specialFunctor() == SpecialFunctor::FORMULA) {
    Connective con = tl.term()->getSpecialData()->getFormula()->connective();
    if (con == TRUE || con == FALSE) {
      return TermList(Term::createConstant(env.signature->getFoolConstantSymbol(con == TRUE)));
    }
  }
  return tl;
}

unsigned FiniteModelMultiSorted::boolValue(bool isTrue, Timestamp asOf)
{
  if (!env.signature->foolConstantsDefined()) {
    USER_ERROR("Cannot evaluate a boolean term: this model does not have a boolean domain");
  }
  DHMap<unsigned,unsigned, FnvHash, IdentityHash> noSubst;
  return evaluateTerm(TermList(Term::createConstant(env.signature->getFoolConstantSymbol(isTrue))),noSubst,asOf);
}

unsigned FiniteModelMultiSorted::evaluateTerm(TermList tl, const DHMap<unsigned,unsigned, FnvHash, IdentityHash>& subst, Timestamp asOf)
{
  if (tl.isVar()) {
    // TODO: maybe error, if the variable is not in the map?

    // cout << "looking up for " << tl.var() << " returning " << subst.get(tl.var()) << endl;
    return subst.get(tl.var());
  }

  Term* term = tl.term();

  if (term->isSpecial()) {
    switch (term->specialFunctor()) {
      // A formula in term position; to a model that is just a boolean value, so evaluate it and
      // return the domain element the corresponding FOOL constant sits on. Both $true / $false at
      // term level and, say, p(a) for a p declared with an $o result sort (which the parser turns
      // into a predicate) arrive here.
      case SpecialFunctor::FORMULA: {
        DHMap<unsigned,unsigned, FnvHash, IdentityHash> inner(subst); // evaluateFormula wants to bind quantified variables
        return boolValue(evaluateFormula(term->getSpecialData()->getFormula(),inner,asOf),asOf);
      }

      case SpecialFunctor::ITE: {
        DHMap<unsigned,unsigned, FnvHash, IdentityHash> inner(subst);
        bool cond = evaluateFormula(term->getSpecialData()->getITECondition(),inner,asOf);
        return evaluateTerm(*term->nthArgument(cond ? 0 : 1),subst,asOf);
      }

      // first match wins, and only the branch that wins is evaluated
      case SpecialFunctor::COND: {
        unsigned arity = term->arity();
        for (unsigned i = 0; i+1 < arity; i += 2) {
          if (evaluateBooleanTerm(*term->nthArgument(i),subst,asOf)) {
            return evaluateTerm(*term->nthArgument(i+1),subst,asOf);
          }
        }
        return evaluateTerm(*term->nthArgument(arity-1),subst,asOf); // the else
      }

      // the remaining FOOL constructs we cannot evaluate
      default:
        USER_ERROR("Cannot evaluate " + tl.toString() + ", not supported");
    }
  }

  unsigned f = term->functor();
  unsigned arity = env.signature->functionArity(f);
  DArray<unsigned> args(arity);
  for(unsigned i=0;i<arity;i++){
    args[i] = evaluateTerm(*term->nthArgument(i),subst,asOf);
    ASS_G(args[i],0)
  }

  // cout << "evaluateTerm " << tl.toString() << " under " << subst << endl;

  // throws if the model does not say what f is on these arguments
  return evalFun(f,args,asOf);
}

/**
 * Evaluate an $o-sorted term as a truth value: a $cond condition, or a boolean term
 * standing where a formula is expected.
 *
 * The fallback asks boolValue for the domain element $true sits on, which a model
 * without a boolean domain does not have -- and most models have none, since only a
 * FOOL problem gives $o a domain. So peel off the special terms whose truth value we
 * can decide without one, which is every shape the parser actually builds here.
 */
bool FiniteModelMultiSorted::evaluateBooleanTerm(TermList tl, const DHMap<unsigned,unsigned, FnvHash, IdentityHash>& subst, Timestamp asOf)
{
  if (tl.isTerm() && tl.term()->isSpecial()) {
    Term* t = tl.term();
    switch (t->specialFunctor()) {
      case SpecialFunctor::FORMULA: {
        DHMap<unsigned,unsigned, FnvHash, IdentityHash> inner(subst);
        return evaluateFormula(t->getSpecialData()->getFormula(),inner,asOf);
      }
      case SpecialFunctor::ITE: {
        DHMap<unsigned,unsigned, FnvHash, IdentityHash> inner(subst);
        bool cond = evaluateFormula(t->getSpecialData()->getITECondition(),inner,asOf);
        return evaluateBooleanTerm(*t->nthArgument(cond ? 0 : 1),subst,asOf);
      }
      case SpecialFunctor::COND: {
        unsigned arity = t->arity();
        for (unsigned i = 0; i+1 < arity; i += 2) {
          if (evaluateBooleanTerm(*t->nthArgument(i),subst,asOf)) {
            return evaluateBooleanTerm(*t->nthArgument(i+1),subst,asOf);
          }
        }
        return evaluateBooleanTerm(*t->nthArgument(arity-1),subst,asOf); // the else
      }
      default:
        break;
    }
  }
  return evaluateTerm(tl,subst,asOf) == boolValue(true,asOf);
}

bool FiniteModelMultiSorted::evaluateLiteral(Literal* lit, const DHMap<unsigned,unsigned, FnvHash, IdentityHash>& subst, Timestamp asOf)
{
  unsigned p = lit->functor();
  unsigned arity = env.signature->predicateArity(p);
  DArray<unsigned> args(arity);
  for(unsigned i=0;i<arity;i++){
    args[i] = evaluateTerm(*lit->nthArgument(i),subst,asOf);
    ASS_G(args[i],0)
  }

  if(lit->isEquality()){
    return (args[0]==args[1]) == lit->polarity();
  }

  // A $distinct marker (cf. Signature::getDistinctPredicate) only occurs in the parsed input,
  // which the self-check reads: preprocessing replaces it by disequalities or a distinct
  // group, so the model has nothing to say about the marker predicate itself. It holds iff
  // the arguments denote pairwise different elements.
  if(env.signature->getPredicate(p)->distinctPred()){
    bool allDifferent = true;
    for(unsigned i=0;i<arity && allDifferent;i++){
      for(unsigned j=i+1;j<arity;j++){
        if(args[i]==args[j]){ allDifferent = false; break; }
      }
    }
    return allDifferent == lit->polarity();
  }

  // throws if the model does not say what p is on these arguments
  return (evalPred(p,args,asOf)==INTP_TRUE) == (lit->polarity());
}

void FiniteModelMultiSorted::eliminateSortFunctionsAndPredicates(const Stack<unsigned> &sortFunctions, const Stack<unsigned> &sortPredicates)
{
  // let's do functions first
  for(unsigned i = 0; i<sortFunctions.size(); i++) {
    unsigned elim_f = sortFunctions[i];
    const Signature::Symbol* elim_symb = env.signature->getFunction(elim_f);
    ASS_EQ(elim_symb->arity(),1)
    unsigned srt = elim_symb->type()->result().term()->functor();

    DHSet<unsigned, FnvHash, IdentityHash> f_range;
    DHMap<unsigned,unsigned, FnvHash, IdentityHash> new_to_old;
    DHMap<unsigned,unsigned, FnvHash, IdentityHash> old_to_new;

    unsigned origSize = _sizes[srt];
    unsigned newSize = 0;

    // srt's domain is getting reduced to the range of f
    {
      ASS(funRepresented(elim_f)); // the sort functions Monotonicity introduces occur in the clauses, so they are used
      const DArray<unsigned>& elim_tbl = funTable(elim_f)->raw();
      for(unsigned j = 1; j<=origSize; j++) {
        unsigned res = elim_tbl[j-1];
        //cout << "f(" << j << ")=" << res << endl;
        if (f_range.insert(res)) {
          newSize++;
          new_to_old.insert(newSize,res);
          old_to_new.insert(res,newSize);
        }
      }
    }

    // we will need to reencode everything

    // save the old stuff (the moved-from arrays are left empty, so initTables below
    // starts from scratch and the old layers stay ours to read from -- and to delete)
    auto old_f_layers = std::move(_f_layers);
    auto old_p_layers = std::move(_p_layers);
    auto old_sizes = _sizes.clone();

    // update size of the affected sort
    _sizes[srt] = newSize;
    // cout << "newSize " << newSize << endl;
    initTables();

    // every function and predicate need to get reencoded
    // - arguments of sort srt now iterate over a different (likely smaller domain)
    // - function values of sort srt still need to passed through the ``disappearing'' elim_f

    for(unsigned f=0; f<env.signature->functions();f++){
      if (!funRepresented(f)) {
        ASS(!funTableIn(old_f_layers,f)); // the used-symbol arrays did not change, so neither did representedness
        continue;
      }
      const Signature::Symbol* symb = env.signature->getFunction(f);
      OperatorType* sig = symb->type();
      unsigned arity = symb->arity();

      // cout << "f = " << f << " arity= " << arity << endl;

      DArray<unsigned>& tbl = funTable(f)->raw();
      const DArray<unsigned>& old_tbl = funTableIn(old_f_layers,f)->raw();

      DArray<unsigned> old_args(arity);
      size_t idx = 0; // ... will fly linearly through the new table
      ArgsEnumerator it(_sizes,sig,arity); // ... args will respect the (new) table encoding
      do {
        const DArray<unsigned>& args = it.args();
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        unsigned old_res = old_tbl[tableIndex(old_args,old_sizes,sig)];

        if (old_res) { // eliminated symbols don't have reasonable values
          unsigned res_srt = sig->result().term()->functor();
          unsigned res = (res_srt == srt) ?
                            // need to first pass old_res through elim_f, before mapping to the new domain
                            old_to_new.get(funTableIn(old_f_layers,elim_f)->raw()[old_res-1]) :
                            old_res;

          tbl[idx] = res;
        }

        idx++;
      } while (it.next());
      ASS_EQ(idx,tbl.size());
    }

    for(unsigned p=1; p<env.signature->predicates();p++){
      if (!predRepresented(p)) {
        ASS(!predTableIn(old_p_layers,p)); // the used-symbol arrays did not change, so neither did representedness
        continue;
      }
      const Signature::Symbol* symb = env.signature->getPredicate(p);
      OperatorType* sig = symb->type();
      unsigned arity = symb->arity();

      // cout << "p = " << p << " arity= " << arity << endl;

      DArray<char>& tbl = predTable(p)->raw();
      const DArray<char>& old_tbl = predTableIn(old_p_layers,p)->raw();

      DArray<unsigned> old_args(arity);
      size_t idx = 0; // ... will fly linearly through the new table
      ArgsEnumerator it(_sizes,sig,arity); // ... args will respect the (new) table encoding
      do {
        const DArray<unsigned>& args = it.args();
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        tbl[idx++] = old_tbl[tableIndex(old_args,old_sizes,sig)]; // no change for predicates
      } while (it.next());
      ASS_EQ(idx,tbl.size());
    }

    deleteLayersIn(old_f_layers,old_p_layers); // the reencoding is done; the old layers can go
  }

  // let's do predicates now
  for(unsigned i = 0; i<sortPredicates.size(); i++) {
    unsigned elim_p = sortPredicates[i];
    const Signature::Symbol* elim_symb = env.signature->getPredicate(elim_p);
    ASS_EQ(elim_symb->arity(),1)
    unsigned srt = elim_symb->type()->arg(0).term()->functor();

    // cout << "Eliminate p = " << elim_p << endl;

    DHMap<unsigned,unsigned, FnvHash, IdentityHash> new_to_old;
    DHMap<unsigned,unsigned, FnvHash, IdentityHash> old_to_new;

    unsigned origSize = _sizes[srt];
    unsigned newSize = 0;

    // srt's domain is getting reduced to those elements for which p is true
    {
      ASS(predRepresented(elim_p)); // the sort predicates occur in the added sort-predicate axioms
      const DArray<char>& elim_tbl = predTable(elim_p)->raw();
      for(unsigned j = 1; j<=origSize; j++) {
        char res = elim_tbl[j-1];
        // cout << "p(" << j << ")=" << (unsigned)res << endl;
        if (res == INTP_TRUE) {
          newSize++;
          new_to_old.insert(newSize,j);
          old_to_new.insert(j,newSize);
        }
      }
    }

    if (origSize == newSize)
      continue;

    // we will need to reencode everything

    // save the old stuff (the moved-from arrays are left empty, so initTables below
    // starts from scratch and the old layers stay ours to read from -- and to delete)
    auto old_f_layers = std::move(_f_layers);
    auto old_p_layers = std::move(_p_layers);
    auto old_sizes = _sizes.clone();

    // update size of the affected sort
    _sizes[srt] = newSize;
    // cout << "origSize = " << origSize << " --> newSize = " << newSize << endl;

    initTables();

    // every function and predicate need to get reencoded
    // - arguments of sort srt now iterate over a different (likely smaller domain)

    for(unsigned f=0; f<env.signature->functions();f++){
      if (!funRepresented(f)) {
        ASS(!funTableIn(old_f_layers,f)); // the used-symbol arrays did not change, so neither did representedness
        continue;
      }
      const Signature::Symbol* symb = env.signature->getFunction(f);
      OperatorType* sig = symb->type();
      unsigned arity = symb->arity();

      DArray<unsigned>& tbl = funTable(f)->raw();
      const DArray<unsigned>& old_tbl = funTableIn(old_f_layers,f)->raw();

      DArray<unsigned> old_args(arity);
      size_t idx = 0; // ... will fly linearly through the new table
      ArgsEnumerator it(_sizes,sig,arity); // ... args will respect the (new) table encoding
      do {
        const DArray<unsigned>& args = it.args();
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        unsigned old_res = old_tbl[tableIndex(old_args,old_sizes,sig)];

        if (old_res) { // eliminated symbols don't have reasonable values
          unsigned res_srt = sig->result().term()->functor();
          // this should be stipulated by the extra sort-predicate axioms
          ASS(res_srt != srt || predTableIn(old_p_layers,elim_p)->raw()[old_res-1] == INTP_TRUE)

          unsigned res = (res_srt == srt) ? old_to_new.get(old_res) : old_res;
          tbl[idx] = res;
        }

        idx++;
      } while (it.next());
      ASS_EQ(idx,tbl.size());
    }

    for(unsigned p=1; p<env.signature->predicates();p++){
      if (!predRepresented(p)) {
        ASS(!predTableIn(old_p_layers,p)); // the used-symbol arrays did not change, so neither did representedness
        continue;
      }
      const Signature::Symbol* symb = env.signature->getPredicate(p);
      OperatorType* sig = symb->type();
      unsigned arity = symb->arity();

      // cout << "p = " << p << " arity= " << arity << endl;

      DArray<char>& tbl = predTable(p)->raw();
      const DArray<char>& old_tbl = predTableIn(old_p_layers,p)->raw();

      DArray<unsigned> old_args(arity);
      size_t idx = 0; // ... will fly linearly through the new table
      ArgsEnumerator it(_sizes,sig,arity); // ... args will respect the (new) table encoding
      do {
        const DArray<unsigned>& args = it.args();
        // encode args into old_args
        for(unsigned i=0;i<arity;i++){
          unsigned i_srt = sig->arg(i).term()->functor();
          old_args[i] = (i_srt == srt) ? new_to_old.get(args[i]) : args[i];
        }

        // reencode and store
        tbl[idx++] = old_tbl[tableIndex(old_args,old_sizes,sig)]; // no change for predicates
      } while (it.next());
      ASS_EQ(idx,tbl.size());
    }

    deleteLayersIn(old_f_layers,old_p_layers); // the reencoding is done; the old layers can go
  }
}

unsigned FiniteModelMultiSorted::applyFunDef(Problem::FunDef* fd, const DArray<unsigned>& args, Timestamp asOf)
{
  // a local substitution: evaluating the body may recurse into further definitions
  DHMap<unsigned,unsigned, FnvHash, IdentityHash> inner;
  for(unsigned i=0;i<args.size();i++){
    ASS(fd->_head->nthArgument(i)->isVar());
    inner.set(fd->_head->nthArgument(i)->var(),args[i]);
  }
  return evaluateTerm(TermList(fd->_body),inner,asOf);
}

bool FiniteModelMultiSorted::applyPredDef(Problem::PredDef* pd, const DArray<unsigned>& args, Timestamp asOf)
{
  DHMap<unsigned,unsigned, FnvHash, IdentityHash> inner;
  for(unsigned i=0;i<args.size();i++){
    ASS(pd->_head->nthArgument(i)->isVar());
    inner.set(pd->_head->nthArgument(i)->var(),args[i]);
  }
  return evaluateFormula(pd->_body,inner,asOf) == pd->_head->isPositive();
}

void FiniteModelMultiSorted::restoreViaCondFlip(Problem::CondFlip* cf)
{
  // cf->outputDefinition(cout);

  DHMap<unsigned,TermList, FnvHash, IdentityHash> sortMap;
  SortHelper::collectVariableSorts(cf->_val,sortMap);
  SortHelper::collectVariableSorts(cf->_cond,sortMap); // in bce, cond can have extra variables; we could treat them existentially, but this may be wrong for _fixedPoint-ers
  unsigned arity = sortMap.size();


  // The layer goes on before it is filled, and everything below is read as of _now + 1 --
  // i.e. as of the model this step transforms, *plus this layer itself*. That self-read is
  // deliberate and is what the old code got from writing into the table as it went: the
  // repair a blocked clause asks for ("while the clause is falsified, make its blocking
  // literal true") reads the model it is updating, and for a _fixedPoint flip, whose clause
  // carries both polarities of the predicate, iterating against a frozen model would reach no
  // repair at all. Nothing else can be affected: only this layer is born at _now.
  CondFlipPredLayer* layer = new CondFlipPredLayer(_now);
  _p_layers[cf->_val->functor()].push(layer);
  const Timestamp asOf = _now + 1;

  static DArray<unsigned> vars;
  vars.ensure(arity);
  static DArray<unsigned> sorts;
  sorts.ensure(arity);

  unsigned i = 0;
  DHMap<unsigned,TermList, FnvHash, IdentityHash>::Iterator it(sortMap); // non-deterministic order OK?
  while (it.hasNext()) {
    unsigned var;
    TermList srt;
    it.next(var,srt);
    vars[i] = var;
    sorts[i] = srt.term()->functor();
    i++;
  }

  bool flipped;
  do {
    flipped = false;

    static DHMap<unsigned,unsigned, FnvHash, IdentityHash> subst;

    unsigned p = cf->_val->functor();
    ASS_NEQ(p,0) // equality cannot be flipped!
    unsigned p_arity = env.signature->predicateArity(p);
    static DArray<unsigned> inner_args;
    inner_args.ensure(p_arity);

    DArray<unsigned> bounds(arity);
    for(unsigned i=0;i<arity;i++){ bounds[i] = _sizes[sorts[i]]; }
    ArgsEnumerator it(std::move(bounds));
    it.bindAll(vars,subst);
    do {
      if (evaluateFormula(cf->_cond,subst,asOf) != cf->_neg) {
        // do the flip
        for(unsigned j=0;j<p_arity;j++){
          inner_args[j] = evaluateTerm(*cf->_val->nthArgument(j),subst,asOf);
        }
        char before = evalPred(p,inner_args,asOf);
        char after = (cf->_val->isPositive() ? INTP_TRUE : INTP_FALSE);
        // Record only what changes. A tuple whose value already is after needs no entry: the
        // layers below are fixed while this one fills, and every entry of a flip is after, so
        // nothing can make that tuple read differently later
        if (before != after) {
          layer->prescribe(inner_args,after);
          flipped = true;
        }
      }
    } while (it.nextAndRebind(vars,subst));
  } while (cf->_fixedPoint && flipped);

  // A flip that changed nothing -- often so: the blocked clause it undoes may already hold
  // in the model it is replayed on -- has nothing to say about any tuple. It goes again, so
  // that it does not stand as a version of its own (toStringLayered); nothing else is born
  // at _now, so nothing can refer to it
  if (layer->prescribed().size() == 0) {
    ALWAYS(_p_layers[cf->_val->functor()].pop() == layer);
    delete layer;
  }
}

/**
 * Replay the recorded interferences in reverse (LIFO) order, turning the model of the fully
 * preprocessed problem into a model of the original one.
 *
 * Each step pushes one layer, so the sequence of models the replay walks through is the
 * sequence of stack heights: model_j is model_{j-1} plus whatever the layer born at j says.
 * Nothing is overwritten, and no step has to know what the steps after it will do.
 *
 * The LIFO order is what makes reading "as of the layer's own birth" the right thing. Birth
 * order is the *reverse* of preprocessing order, so for a definition recorded at preprocessing
 * step T and born at replay step j, and any symbol q in its body:
 *
 *  - q was still live at T, so if q is eliminated at all it is eliminated after T, hence
 *    replayed before j: its layer is born earlier and the definition sees it;
 *  - a flip on q recorded after T is likewise born before j and visible, correctly -- by the
 *    time we are rebuilding the state before T, that flip has already been undone;
 *  - a flip on q recorded before T is born after j and invisible, also correctly -- in the
 *    state before T it has not been undone yet. This is the case that used to need a
 *    definition to be frozen into a table before a flip could be replayed.
 *
 * Shuffling::polarityFlip runs last in preprocessing and so replays first; it records a flip
 * for much of the signature whether or not the predicate still occurs, and a definition
 * arriving later simply covers such a vacuous flip up.
 */
void FiniteModelMultiSorted::restoreEliminatedDefinitions(Kernel::Problem* prob)
{
  auto ii = prob->interferences.iter(); // LIFO is the key here!
  while (ii.hasNext()) {
    Problem::Interference* i = ii.next();
    // one tick of the replay clock per step: whatever this step pushes belongs to model__now,
    // and reads as of _now therefore see model_{_now-1}, which is what this step transforms
    ASS_G(_now,MODEL_ZERO);
    switch (i->_kind) {
      case Problem::IntereferenceKind::FUN_DEF: {
        Problem::FunDef* fd = static_cast<Problem::FunDef*>(i);
        unsigned f = fd->_head->functor();
        // a definition is total, so pushing it hides everything the model said about f so far;
        // only a flip replayed earlier can have put a table underneath
        ASS(!funRepresented(f) || !funUsed(f));
        _f_layers[f].push(new DefFunLayer(fd,_now));
        break;
      }
      case Problem::IntereferenceKind::PRED_DEF: {
        Problem::PredDef* pd = static_cast<Problem::PredDef*>(i);
        unsigned p = pd->_head->functor();
        ASS(!predRepresented(p) || !predUsed(p));
        _p_layers[p].push(new DefPredLayer(pd,_now));
        break;
      }
      case Problem::IntereferenceKind::GLOB_FLIP: {
        Problem::GlobalFlip* gf = static_cast<Problem::GlobalFlip*>(i);
        ASS_NEQ(gf->_pred,0) // equality is protected from flipping
        _p_layers[gf->_pred].push(new GlobalFlipPredLayer(gf->_pred,_now));
        break;
      }
      case Problem::IntereferenceKind::COND_FLIP: {
        Problem::CondFlip* cf = static_cast<Problem::CondFlip*>(i);
        restoreViaCondFlip(cf);
        break;
      }

      default:
        ASSERTION_VIOLATION
    }
    _now++;
  }

}

bool FiniteModelMultiSorted::evaluable(TermList tl)
{
  if (tl.isVar()) return true;
  Term* t = tl.term();
  if (t->isSpecial()) {
    // keep this in step with the special-term switch in evaluateTerm: anything admitted
    // here must be evaluable there, and anything evaluable there is worth admitting here,
    // or the self-check and the model loader skip or reject the unit instead of checking it
    switch (t->specialFunctor()) {
      // a formula in term position -- that is where $true and $false at term level, and a
      // p(a) for a p declared with an $o result sort, end up
      case SpecialFunctor::FORMULA:
        return evaluable(t->getSpecialData()->getFormula());
      case SpecialFunctor::ITE:
        // the condition is off to the side; the branches are checked with the arguments below
        if (!evaluable(t->getSpecialData()->getITECondition())) return false;
        break;
      case SpecialFunctor::COND:
        // conditions and branches alike are ordinary arguments
        break;
      default: // $let and friends
        return false;
    }
  }
  for (unsigned i = 0; i < t->arity(); i++) {
    if (!evaluable(*t->nthArgument(i))) return false;
  }
  return true;
}

bool FiniteModelMultiSorted::evaluable(Formula* f)
{
  switch (f->connective()) {
    case LITERAL: {
      Literal* l = f->literal();
      for (unsigned i = 0; i < l->arity(); i++) {
        if (!evaluable(*l->nthArgument(i))) return false;
      }
      return true;
    }
    case AND:
    case OR: {
      FormulaList::Iterator it(f->args());
      while (it.hasNext()) {
        if (!evaluable(it.next())) return false;
      }
      return true;
    }
    case IMP:
    case IFF:
    case XOR:
      return evaluable(f->left()) && evaluable(f->right());
    case NOT:
      return evaluable(f->uarg());
    case FORALL:
    case EXISTS:
      return evaluable(f->qarg());
    case TRUE:
    case FALSE:
      return true;
    case BOOL_TERM:
      return evaluable(f->getBooleanTerm());
    default: // $ite, $let and friends
      return false;
  }
}

/**
 * Evaluate a unit in this model; throws UndefinedValueException as soon as the model
 * turns out not to say what some symbol is on the arguments at hand.
 */
bool FiniteModelMultiSorted::evaluate(Unit* unit)
{
  Formula* formula = (unit->isClause()) ?
    Formula::fromClause(unit->asClause()) : // universally closed by default
    Formula::quantify(static_cast<FormulaUnit*>(unit)->getFormula()); // close over any free variables (a no-op on closed formulas)

  DHMap<unsigned,unsigned, FnvHash, IdentityHash> subst;
  return evaluateFormula(formula,subst,_now);
}

/**
 *
 * TODO: This is recursive, which could be problematic in the long run
 *
 */
bool FiniteModelMultiSorted::evaluateFormula(Formula* formula, DHMap<unsigned,unsigned, FnvHash, IdentityHash>& subst, Timestamp asOf)
{
  bool isAnd = false;
  bool isImp = false;
  bool isXor = false;
  bool isForall = false;
  switch(formula->connective()){
    case FALSE:
      return false;
    case TRUE:
      return true;

    case LITERAL:
      return evaluateLiteral(formula->literal(),subst,asOf);

    // the dual of the FORMULA special term in evaluateTerm: a boolean term used as a formula
    case BOOL_TERM:
      return evaluateBooleanTerm(formula->getBooleanTerm(),subst,asOf);

    case NOT:
      return !evaluateFormula(formula->uarg(),subst,asOf);
    case AND:
      isAnd=true;
    case OR:
      {
        FormulaList* args = formula->args();
        FormulaList::Iterator fit(args);
        while(fit.hasNext()){
          Formula* arg = fit.next();
          bool res = evaluateFormula(arg,subst,asOf);
          if(isAnd && !res) return false;
          if(!isAnd && res) return true;
        }
        return isAnd;
      }

    case IMP:
      isImp=true;
    case XOR:
      isXor = !isImp;
    case IFF:
    {
      Formula* left = formula->left();
      Formula* right = formula->right();
      bool left_res = evaluateFormula(left,subst,asOf);
      if(isImp && !left_res) return true;
      bool right_res = evaluateFormula(right,subst,asOf);
      if(isImp) return right_res;

#if DEBUG_MODEL
      cout << "left_res is " << left_res << ", right_res is " << right_res << endl;
#endif

      if(isXor) return left_res != right_res;
      return left_res == right_res; // IFF
    }

    // Expand quantifications
    case FORALL:
      isForall = true;
    case EXISTS:
    {
      VSList* vs = formula->vars();

      // cout << "will do FORALL/EXISTS for " << formula->toString() << endl;

      unsigned arity = VSList::length(vs);
      DArray<unsigned> old_vals(arity);
      DArray<unsigned> vars(arity);
      DArray<unsigned> bounds(arity);

      // store old_vals, figure out bounds
      for(unsigned i=0;i<arity;i++){
        auto [var, srt] = vs->head();
        vs = vs->tail();
        vars[i] = var;
        bounds[i] = _sizes[srt.term()->functor()];
        old_vals[i] = subst.get(var,0);
      }

      ArgsEnumerator it(std::move(bounds));
      it.bindAll(vars,subst);

      bool res;
      bool early = false;
      do {
        res = evaluateFormula(formula->qarg(),subst,asOf);

        if((isForall && !res) || (!isForall && res)) {
          early = true;
          break;
        }
      } while (it.nextAndRebind(vars,subst));

      // undo the bindings in subst
      for(unsigned i=0;i<arity;i++){
        subst.set(vars[i],old_vals[i]);
      }

      if (early) {
        if(isForall && !res) return false;
        if(!isForall && res) return true;
      }

      return isForall;
    }
    default:
      USER_ERROR("Cannot evaluate " + formula->toString() + ", not supported");
  }
}

}
