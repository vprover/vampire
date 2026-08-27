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
#include "Lib/DHMap.hpp"

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

unsigned TableFunLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  size_t idx = m.tableIndexOf(_sig,args);
  ASS_L(idx,_tbl.size());
  return _tbl[idx]; // FUNV_UNDEF here means the model does not say, and falls through
}

char TablePredLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  size_t idx = m.tableIndexOf(_sig,args);
  ASS_L(idx,_tbl.size());
  return _tbl[idx]; // INTP_UNDEF here means the model does not say, and falls through
}

void FiniteModelMultiSorted::initTables()
{
  deleteAllLayers();

  _f_layers.ensure(env.signature->functions());
  _p_layers.ensure(env.signature->predicates());

  for(unsigned f=0; f<env.signature->functions();f++){
    Signature::Symbol* symb = env.signature->getFunction(f);
    if (symb->usageCnt()==0) {
      // the SAT solver skipped some functions as they are eliminated
      // (the model, on the other hand, should be prepared to give them values later)
      continue; // not represented: no layers at all
    }

    OperatorType* sig = symb->fnType();
    _f_layers[f].push(new TableFunLayer(sig,tableSize(sig,symb->arity(),_sizes),MODEL_ZERO));
  }

  // equality is never tabulated, so predicate 0 keeps an empty stack
  for(unsigned p=1; p<env.signature->predicates();p++){
    Signature::Symbol* symb = env.signature->getPredicate(p);
    if (symb->usageCnt()==0) {
      continue; // not represented
    }

    OperatorType* sig = symb->predType();
    _p_layers[p].push(new TablePredLayer(sig,tableSize(sig,symb->arity(),_sizes),MODEL_ZERO));
  }
}

void FiniteModelMultiSorted::installTrivialLayers()
{
  ASS_EQ(_now,MODEL_ZERO+1); // model_0 has to be complete before the replay touches it

  for(unsigned f=0; f<env.signature->functions();f++){
    if (_f_layers[f].isEmpty()) {
      _f_layers[f].push(new TrivialFunLayer(MODEL_ZERO));
    }
  }
  // predicate 0 is equality, which evaluateLiteral answers without consulting the model
  for(unsigned p=1; p<env.signature->predicates();p++){
    if (_p_layers[p].isEmpty()) {
      _p_layers[p].push(new TrivialPredLayer(MODEL_ZERO));
    }
  }

  // The two boolean domain elements have to be genuinely represented, and are: FOOL
  // elimination puts them in the problem, so they have a usage count and hence a table. A
  // trivial layer would give both the same value, collapsing $true and $false onto one
  // element -- boolValue would stop distinguishing them and toString's domain print would
  // name the same element twice.
  ASS(!env.signature->foolConstantsDefined() ||
      (funRepresented(env.signature->getFoolConstantSymbol(true)) &&
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

void FiniteModelMultiSorted::addFunctionDefinition(unsigned f, const DArray<unsigned>& args, unsigned res)
{
  ASS_EQ(env.signature->functionArity(f),args.size());

  OperatorType* tp = env.signature->getFunction(f)->fnType();
  // a function's value must be a domain element of its result sort
  ASS_G(res,0); ASS_LE(res,domainSize(_sizes,tp->result().term()->functor()));

  DArray<unsigned>& tbl = funTable(f)->raw();
  size_t idx = tableIndex(args,_sizes,tp);

  ASS_L(idx, tbl.size());
  tbl[idx] = res;
}

void FiniteModelMultiSorted::addPredicateDefinition(unsigned p, const DArray<unsigned>& args, bool res)
{
  ASS_EQ(env.signature->predicateArity(p),args.size());

  DArray<char>& tbl = predTable(p)->raw();
  size_t idx = tableIndex(args,_sizes,env.signature->getPredicate(p)->predType());

  ASS_L(idx, tbl.size());
  tbl[idx] = (res ? INTP_TRUE : INTP_FALSE);
}

// how Vampire spells the i-th variable, matching TermList::var(i).toString()
static std::string varName(unsigned i)
{
  return "X"+Int::toString(i);
}

// "name(X0,...,X_{arity-1})", or just "name" for a constant or proposition
static std::string linearHead(const std::string& name, unsigned arity)
{
  if (arity == 0) {
    return name;
  }
  std::string res = name+"(";
  for(unsigned i=0;i<arity;i++){
    if (i) res += ",";
    res += varName(i);
  }
  return res+")";
}

/**
 * A definition layer computes its value from the model as it stood when the definition
 * arrived, which is what makes it right. Printing its body as it stands, though, says
 * something about the model as *printed* -- the topmost version of every symbol. The two
 * agree unless some symbol in the body has acquired a layer since, which in practice means a
 * flip replayed after this definition. Where they disagree, the body must not be printed; the
 * extensional rendering, which reads through the whole stack, is right in every case.
 *
 * (The eventual fix is to print the older version under a name of its own, rather than to
 * fall back on spelling the extension out. Until then this is at least no coarser than the
 * freezing it replaces, which flattened every direct reader of every flip target.)
 */
bool FiniteModelMultiSorted::bodyStillCurrent(Term* body, Timestamp born)
{
  NonVariableNonTypeIterator it(body,true);
  while (it.hasNext()) {
    Term* t = it.next();
    if (t->isSpecial()) {
      // a formula in term position; the special data is not walked by the iterator
      if (t->specialFunctor() != SpecialFunctor::FORMULA ||
          !bodyStillCurrent(t->getSpecialData()->getFormula(),born)) {
        return false;
      }
      continue;
    }
    if (!symbolStillCurrent(_f_layers[t->functor()],born)) {
      return false;
    }
  }
  return true;
}

bool FiniteModelMultiSorted::bodyStillCurrent(Formula* body, Timestamp born)
{
  SubformulaIterator sfit(body);
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    if (sf->connective() != LITERAL) {
      continue;
    }
    Literal* lit = sf->literal();
    if (!lit->isEquality()) { // equality is not in the model
      const Stack<PredLayer*>& st = _p_layers[lit->functor()];
      if (st.isNonEmpty() && st.top()->_born >= born) {
        return false;
      }
    }
    for (unsigned i = 0; i < lit->arity(); i++) {
      TermList arg = *lit->nthArgument(i);
      if (arg.isTerm() && !bodyStillCurrent(arg.term(),born)) {
        return false;
      }
    }
  }
  return true;
}

bool FiniteModelMultiSorted::symbolStillCurrent(const Stack<FunLayer*>& st, Timestamp born) const
{
  return st.isEmpty() || st.top()->_born < born;
}

std::string FiniteModelMultiSorted::toString()
{
  std::ostringstream modelStm;

  bool printIntroduced = false;

  static DArray<DArray<std::string>> cnames;
  cnames.ensure(env.signature->typeCons());

  //Output sorts and their sizes
  for(unsigned s=0;s<env.signature->typeCons();s++){
    unsigned size = _sizes[s];
    if(size==0) continue;

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

    cnames[s].ensure(size+1);

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
        cnames[s][boolValue(isTrue)] =
          env.signature->functionName(env.signature->getFoolConstantSymbol(isTrue));
      }
      ASS_NEQ(cnames[s][1],cnames[s][2]);
    } else {
      // Domain constant declarations
      for(unsigned i=1;i<=size;i++){
        modelStm << "tff(" << append(prepend("declare_", sortNameLabel), Int::toString(i).c_str()) << ",type,";
        std::string cname = append(prepend("fmb_", sortNameLabel),(std::string("_")+Lib::Int::toString(i)).c_str());
        cnames[s][i]=cname;
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
      modelStm << "(X = " << cnames[s][i] << ")";
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
        modelStm << cnames[s][i] <<" != " << cnames[s][j];
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

  // Functions (including constants)
  for(unsigned f=0;f<env.signature->functions();f++){
    Signature::Symbol* symb = env.signature->getFunction(f);
    unsigned arity = symb->arity();
    if(!printIntroduced && symb->introduced()) continue;
    // the boolean domain elements are named after these two, so their definitions
    // would just be the tautologies $true = $true and $false = $false
    if(env.signature->isFoolConstantSymbol(true,f) || env.signature->isFoolConstantSymbol(false,f)) continue;
    std::string name = symb->name();

    OperatorType* ot = symb->fnType();
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

    // A definition or a trivial value prints as a formula; anything else -- a table, or a
    // flip stacked on one -- has to be spelled out cell by cell. Note this is not the same
    // question as funRepresented: a flip layer has no table of its own, but what it computes
    // has no shorter rendering either.
    Stack<FunLayer*>& st = _f_layers[f];
    LayerKind topKind = st.isNonEmpty() ? st.top()->_kind : LayerKind::TRIVIAL;
    if (topKind == LayerKind::DEF &&
        !bodyStillCurrent(static_cast<DefFunLayer*>(st.top())->def()->_body,st.top()->_born)) {
      topKind = LayerKind::TABLE; // the body no longer describes the printed model; spell it out
    }
    if (topKind == LayerKind::DEF || topKind == LayerKind::TRIVIAL) {
      // either a recorded definition speaks for f, or nothing does and the trivial layer's
      // value has to be spelled out
      Problem::FunDef* fd = (topKind == LayerKind::DEF) ?
        static_cast<DefFunLayer*>(st.top())->def() : nullptr;

      modelStm << "tff("<<append(name,"_symbolic_definition")<<",axiom,";
      if (arity>0) { // quantify
        modelStm << "![";
        for(unsigned i=0;i<arity;i++){
          modelStm << (fd ? fd->_head->nthArgument(i)->toString() : varName(i));
          modelStm << ":" << ot->arg(i).toString();
          if(i+1 < arity) modelStm << ", ";
        }
        modelStm << "]: ";
      }
      if (fd) {
        modelStm << fd->_head->toString() << " = " << fd->_body->toString();
      } else {
        modelStm << linearHead(name,arity) << " = ";
        unsigned srt = ot->result().term()->functor();
        modelStm << cnames[srt][1]; // the trivial layer's value
      }

      modelStm << ")." <<endl;
      continue;
    }

    if (arity == 0) {
      unsigned res = evalFun(f,DArray<unsigned>(0),_now);
      ASS_G(res,0)

      TermList srtT = ot->result();
      unsigned srt = srtT.term()->functor();
      std::string cname = cnames[srt][res];

      modelStm << "tff("<<append(name,"_definition")<<",axiom,"<<name<<" = " << cname << ")."<<endl;
    } else {
      modelStm << "tff("<<prepend("function_", name)<<",axiom,"<<endl;

      bool first=true;
      ArgsEnumerator it(_sizes,ot,arity);
      do {
        const DArray<unsigned>& args = it.args();
        unsigned res = evalFun(f,args,_now);
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
          modelStm << cnames[argSort][args[j]];
        }
        TermList resultSortT = ot->result();
        unsigned resultSort = resultSortT.term()->functor();
        modelStm << ") = " << cnames[resultSort][res] << endl;
      } while (it.next());
      modelStm << ")." << endl << endl;
    }
  }

  //Predicates (including propositions)
  for(unsigned p=1;p<env.signature->predicates();p++){
    Signature::Symbol* symb = env.signature->getPredicate(p);
    unsigned arity = symb->arity();
    if(!printIntroduced && symb->introduced()) continue;
    std::string name = symb->name();
    OperatorType* ot = symb->predType();
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

    Stack<PredLayer*>& st = _p_layers[p];
    LayerKind topKind = st.isNonEmpty() ? st.top()->_kind : LayerKind::TRIVIAL;
    if (topKind == LayerKind::DEF &&
        !bodyStillCurrent(static_cast<DefPredLayer*>(st.top())->def()->_body,st.top()->_born)) {
      topKind = LayerKind::TABLE;
    }
    if (topKind == LayerKind::DEF || topKind == LayerKind::TRIVIAL) {
      Problem::PredDef* pd = (topKind == LayerKind::DEF) ?
        static_cast<DefPredLayer*>(st.top())->def() : nullptr;

      modelStm << "tff("<<append(name,"_symbolic_definition")<<",axiom,";
      if (arity>0) { // quantify
        modelStm << "![";
        for(unsigned i=0;i<arity;i++){
          modelStm << (pd ? pd->_head->nthArgument(i)->toString() : varName(i));
          modelStm << ":" << ot->arg(i).toString();
          if(i+1 < arity) modelStm << ", ";
        }
        modelStm << "]: (";
      }
      if (pd) {
        modelStm << pd->_head->toString() << " <=> " << pd->_body->toString();
      } else {
        modelStm << linearHead(name,arity) << " <=> $false"; // the trivial layer's value
      }
      if (arity>0)
        modelStm << ")";
      modelStm << ")." <<endl;

      continue;
    }

    if (arity==0) {
      char res = evalPred(p,DArray<unsigned>(0),_now);
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
        char res = evalPred(p,args,_now);
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
          modelStm << cnames[argSort][args[j]];
        }
        modelStm << ")";
        modelStm << endl;
      } while (it.next());
      modelStm << ")." << endl << endl;
    }
  }

  return modelStm.str();
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
  DHMap<unsigned,unsigned> noSubst;
  return evaluateTerm(TermList(Term::createConstant(env.signature->getFoolConstantSymbol(isTrue))),noSubst,asOf);
}

unsigned FiniteModelMultiSorted::evaluateTerm(TermList tl, const DHMap<unsigned,unsigned>& subst, Timestamp asOf)
{
  if (tl.isVar()) {
    // TODO: maybe error, if the variable is not in the map?

    // cout << "looking up for " << tl.var() << " returning " << subst.get(tl.var()) << endl;
    return subst.get(tl.var());
  }

  Term* term = tl.term();

  if (term->isSpecial()) {
    // A formula in term position; to a model that is just a boolean value, so evaluate it and
    // return the domain element the corresponding FOOL constant sits on. Both $true / $false at
    // term level and, say, p(a) for a p declared with an $o result sort (which the parser turns
    // into a predicate) arrive here. The remaining FOOL constructs we cannot evaluate.
    if (term->specialFunctor() != SpecialFunctor::FORMULA) {
      USER_ERROR("Cannot evaluate " + tl.toString() + ", not supported");
    }
    DHMap<unsigned,unsigned> inner(subst); // evaluateFormula wants to bind quantified variables
    return boolValue(evaluateFormula(term->getSpecialData()->getFormula(),inner,asOf),asOf);
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

bool FiniteModelMultiSorted::evaluateLiteral(Literal* lit, const DHMap<unsigned,unsigned>& subst, Timestamp asOf)
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

  // throws if the model does not say what p is on these arguments
  return (evalPred(p,args,asOf)==INTP_TRUE) == (lit->polarity());
}

void FiniteModelMultiSorted::eliminateSortFunctionsAndPredicates(const Stack<unsigned> &sortFunctions, const Stack<unsigned> &sortPredicates)
{
  // let's do functions first
  for(unsigned i = 0; i<sortFunctions.size(); i++) {
    unsigned elim_f = sortFunctions[i];
    Signature::Symbol* elim_symb = env.signature->getFunction(elim_f);
    ASS_EQ(elim_symb->arity(),1)
    unsigned srt = elim_symb->fnType()->result().term()->functor();

    DHSet<unsigned> f_range;
    DHMap<unsigned,unsigned> new_to_old;
    DHMap<unsigned,unsigned> old_to_new;

    unsigned origSize = _sizes[srt];
    unsigned newSize = 0;

    // srt's domain is getting reduced to the range of f
    {
      ASS(funRepresented(elim_f)); // Monotonicity bumps usageCnt of the sort functions it introduces
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
        ASS(!funTableIn(old_f_layers,f)); // usageCnt did not change, so neither did representedness
        continue;
      }
      Signature::Symbol* symb = env.signature->getFunction(f);
      OperatorType* sig = symb->fnType();
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
        ASS(!predTableIn(old_p_layers,p)); // usageCnt did not change, so neither did representedness
        continue;
      }
      Signature::Symbol* symb = env.signature->getPredicate(p);
      OperatorType* sig = symb->predType();
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
    Signature::Symbol* elim_symb = env.signature->getPredicate(elim_p);
    ASS_EQ(elim_symb->arity(),1)
    unsigned srt = elim_symb->predType()->arg(0).term()->functor();

    // cout << "Eliminate p = " << elim_p << endl;

    DHMap<unsigned,unsigned> new_to_old;
    DHMap<unsigned,unsigned> old_to_new;

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
        ASS(!funTableIn(old_f_layers,f)); // usageCnt did not change, so neither did representedness
        continue;
      }
      Signature::Symbol* symb = env.signature->getFunction(f);
      OperatorType* sig = symb->fnType();
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
        ASS(!predTableIn(old_p_layers,p)); // usageCnt did not change, so neither did representedness
        continue;
      }
      Signature::Symbol* symb = env.signature->getPredicate(p);
      OperatorType* sig = symb->predType();
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
  DHMap<unsigned,unsigned> inner;
  for(unsigned i=0;i<args.size();i++){
    ASS(fd->_head->nthArgument(i)->isVar());
    inner.set(fd->_head->nthArgument(i)->var(),args[i]);
  }
  return evaluateTerm(TermList(fd->_body),inner,asOf);
}

bool FiniteModelMultiSorted::applyPredDef(Problem::PredDef* pd, const DArray<unsigned>& args, Timestamp asOf)
{
  DHMap<unsigned,unsigned> inner;
  for(unsigned i=0;i<args.size();i++){
    ASS(pd->_head->nthArgument(i)->isVar());
    inner.set(pd->_head->nthArgument(i)->var(),args[i]);
  }
  return evaluateFormula(pd->_body,inner,asOf) == pd->_head->isPositive();
}

unsigned DefFunLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  ArgsKey key(args);
  unsigned v;
  if (_memo.find(key,v)) {
    return v;
  }
  v = m.applyFunDef(_fd,args,_born); // the model as it stood when this definition arrived
  _memo.set(key,v); // set, not insert: the evaluation above may have come back round here
  return v;
}

char DefPredLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  ArgsKey key(args);
  char v;
  if (_memo.find(key,v)) {
    return v;
  }
  v = m.applyPredDef(_pd,args,_born) ? INTP_TRUE : INTP_FALSE;
  _memo.set(key,v);
  return v;
}

char GlobalFlipPredLayer::value(const DArray<unsigned>& args, FiniteModelMultiSorted& m)
{
  // exactly the opposite of what stood below us, and nothing else changes anywhere
  return (m.evalPred(_pred,args,_born) == INTP_TRUE) ? INTP_FALSE : INTP_TRUE;
}

void FiniteModelMultiSorted::restoreViaCondFlip(Problem::CondFlip* cf)
{
  // cf->outputDefinition(cout);

  DHMap<unsigned,TermList> sortMap;
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
  DHMap<unsigned,TermList>::Iterator it(sortMap); // non-deterministic order OK?
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

    static DHMap<unsigned,unsigned> subst;

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
        layer->prescribe(inner_args,after);
        flipped |= (before != after);
      }
    } while (it.nextAndRebind(vars,subst));
  } while (cf->_fixedPoint && flipped);
  // cout << endl;
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
        ASS(!funRepresented(f) || env.signature->getFunction(f)->usageCnt()==0);
        _f_layers[f].push(new DefFunLayer(fd,_now));
        break;
      }
      case Problem::IntereferenceKind::PRED_DEF: {
        Problem::PredDef* pd = static_cast<Problem::PredDef*>(i);
        unsigned p = pd->_head->functor();
        ASS(!predRepresented(p) || env.signature->getPredicate(p)->usageCnt()==0);
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

/**
 * Evaluate a unit in this model; throws UndefinedValueException as soon as the model
 * turns out not to say what some symbol is on the arguments at hand.
 */
bool FiniteModelMultiSorted::evaluate(Unit* unit)
{
  Formula* formula = (unit->isClause()) ?
    Formula::fromClause(unit->asClause()) : // universally closed by default
    Formula::quantify(static_cast<FormulaUnit*>(unit)->getFormula()); // close over any free variables (a no-op on closed formulas)

  DHMap<unsigned,unsigned> subst;
  return evaluateFormula(formula,subst,_now);
}

/**
 *
 * TODO: This is recursive, which could be problematic in the long run
 *
 */
bool FiniteModelMultiSorted::evaluateFormula(Formula* formula, DHMap<unsigned,unsigned>& subst, Timestamp asOf)
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
      return evaluateTerm(formula->getBooleanTerm(),subst,asOf) == boolValue(true,asOf);

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
