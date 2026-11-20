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
 * @file ModelCheck.hpp
 * Defines checking of finite models
 *
 * @since 6/10/2015 Manchester
 * @author Giles
 */

#ifndef __ModelCheck__
#define __ModelCheck__

#include "Lib/DHMap.hpp"
#include "Lib/Set.hpp"
#include "Lib/Environment.hpp"
#include "Lib/StringUtils.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Term.hpp"

#include "Parse/TPTP.hpp"

#include "FiniteModelMultiSorted.hpp"

#include <memory>

namespace FMB{

using namespace Lib;
using namespace Kernel;

using std::cout;
using std::endl;

class ModelCheck{

  // hashed by Term::getId(), not by address: the iteration order of this set is what
  // numbers the domain elements, and so decides the whole output (cf. Kernel/Term.hpp).
  // Deliberately not FnvHash, which is what the rest of FMB spells out for a Term* key:
  // that one hashes the pointer, which is the reproducibility hazard this avoids
  using DomainConstantSet = Set<Term*,SharedTermHash>;

public:
/**
 * Refuse, naming it, a unit the evaluator cannot evaluate ($let, say), model and formulas to
 * check alike: a check that has to leave a formula out has not checked the model.
 *
 * Called before anything else looks at the problem -- in particular before the refusal of
 * polymorphic input, which a $let would otherwise trip over with a misleading message, as
 * the parser writes its bindings with the polymorphic := (Signature::getDefPred).
 */
static void refuseUnsupported(UnitList* units)
{
  UnitList::Iterator uit(units);
  while (uit.hasNext()) {
    Unit* u = uit.next();
    if (!u->isClause() && !FiniteModelMultiSorted::evaluable(u->getFormula())) {
      USER_ERROR("Cannot check " + u->toString() + ": it contains a construct the model checker does not support (such as $let)");
    }
  }
}

static void doCheck(UnitList* units)
{
  // find model size
  // looking for a domain axiom with a name starting 'finite_domain' (TODO search for something of the right shape)

  DHMap<unsigned,unsigned, FnvHash, IdentityHash> sortSizes;
  DHMap<unsigned,std::unique_ptr<DomainConstantSet>, FnvHash, IdentityHash> domainConstantsPerSort;

  // first just search for finite_domain axiom (TODO: do this for every sort!)
  {
    UnitList::Iterator uit(units);
    while(uit.hasNext()){
      Unit* u = uit.next();
      if(!Parse::TPTP::isModelDefinition(u)) continue;
      std::string name;
      std::filesystem::path path;
      ALWAYS(Parse::TPTP::findAxiomName(u,name,path));
      if(StringUtils::starts_with(name,"finite_domain")){
        std::cout << "Finite domain axiom found:" << std::endl << u->toString() << std::endl;
        // Set model size and domainConstants
        // And check it is a finite domain axiom
        if(u->isClause()) USER_ERROR("finite_domain in cnf (use fof/tff instead)");

        Formula* formula = u->getFormula();
        if(formula->connective()!=Connective::FORALL) USER_ERROR("finite_domain is not a domain axiom");
        Formula* subformula = formula->qarg();

        if (VSList::length(formula->vars()) != 1) USER_ERROR("finite_domain must start with forall over a single variable");
        unsigned curSort = formula->vars()->head().second.term()->functor();

        unsigned curModelSize = 0;
        auto curDomainConstants = std::make_unique<DomainConstantSet>();

        int single_var = -1;
        if (subformula->connective()==Connective::OR) {
          FormulaList* args = subformula->args();
          FormulaList::Iterator fit(args);
          while(fit.hasNext()){
            curModelSize++;
            Formula* arg = fit.next();
            if(arg->connective()!=Connective::LITERAL) USER_ERROR("finite_domain is not a domain axiom");
            Literal* l = arg->literal();
            checkIsDomainLiteral(l,single_var,*curDomainConstants);
          }
        } else if (subformula->connective()==Connective::LITERAL) {
          curModelSize = 1;
          checkIsDomainLiteral(subformula->literal(),single_var,*curDomainConstants);
        } else USER_ERROR("finite_domain is not a domain axiom");

        sortSizes.set(curSort,curModelSize);
        domainConstantsPerSort.set(curSort,std::move(curDomainConstants));
      }
    }
  }

  // A model with no domain at all is fine as long as there is a model: a propositional one
  // (checks/fmb/propositional-collapsed.p) has nothing else to say
  bool anyModelDefinition = false;
  {
    UnitList::Iterator uit(units);
    while (uit.hasNext()) {
      anyModelDefinition |= Parse::TPTP::isModelDefinition(uit.next());
    }
  }
  if (!anyModelDefinition) {
    USER_ERROR("No model found!\n Use vampire(model_check,model_start). MODEL_DEFINITION_FORMULAS. vampire(model_check,model_end).");
  }

  std::cout << "Loading model..." << std::endl;

  DomainConstantSet domainConstants; // union of all the perSort ones
  {
    auto it = domainConstantsPerSort.items();
    while (it.hasNext()) {
      DomainConstantSet::Iterator dit(*it.next().second);
      while (dit.hasNext()) {
        domainConstants.insert(dit.next());
      }
    }
  }

  // The symbolic definitions first, since a symbol defined by one gets no table. They own
  // their Problem::FunDef / PredDef, which the model's layers point to, so they have to
  // outlive the model -- hence declared before it.
  Stack<SymbolicDefinition> symbolic;
  DArray<int> funDefinedBy, predDefinedBy; // index into symbolic, or -1
  readSymbolicDefinitions(units,domainConstants,symbolic,funDefinedBy,predDefinedBy);

  // Which symbols the model is about: the ones its own definitions mention. A symbol that
  // only occurs in the formulas to be checked deliberately gets no table -- the model
  // saying nothing about it is exactly the partiality evaluate() is to report.
  DArray<bool> usedFunctions, usedPredicates;
  collectModelSymbols(units,usedFunctions,usedPredicates);
  for (const SymbolicDefinition& sd : symbolic) {
    // a symbolic definition is the whole interpretation of its head: no table under it
    (sd.pred ? usedPredicates : usedFunctions)[sd.symbol()] = false;
  }

  DArray<unsigned> sortSizesArray;
  // a sort the model file does not mention gets no domain (a well-formed model only
  // describes the sorts it talks about); without the init the entry stayed uninitialised
  sortSizesArray.init(env.signature->typeCons(),0);
  {
    auto it = sortSizes.items();
    while (it.hasNext()) {
      auto [sort,curModelSize] = it.next();
      sortSizesArray[sort] = curModelSize;
    }
  }
  // TODO can we pass a reference here instead of clone()ing?
  FiniteModelMultiSorted model(sortSizesArray.clone(),std::move(usedFunctions),std::move(usedPredicates));

  // a pure lookup, never enumerated, so hashing it by address is harmless here
  DHMap<Term*,unsigned, FnvHash, PtrIdentityHash> domainConstantNumber;

  // which symbols have at least one table cell, so that a definition mentioning a symbol
  // the model says nothing about can be reported up front
  TableCells cells;
  cells.fun.init(env.signature->functions(),false);
  cells.pred.init(env.signature->predicates(),false);

  std::cout << "Detected model with " << sortSizes.size() << " sorts." << std::endl;
  auto it = sortSizes.items();
  while (it.hasNext()) {
    auto [sort,curModelSize] = it.next();
    auto& curDomainConstants = *domainConstantsPerSort.get(sort);
    ASS_EQ(curModelSize,(unsigned)curDomainConstants.size());

    std::cout << "  domain for " + env.signature->getTypeCon(sort)->name() + " of size " << curModelSize;
    std::cout << ", domain elements are:" << std::endl;

    // number the domain constants
    DomainConstantSet::Iterator dit(curDomainConstants);
    unsigned count=1;
    while(dit.hasNext()){
      Term* con = dit.next();
      std::cout << "    " << con->toString() << std::endl;
      domainConstantNumber.insert(con,count);
      model.addFunctionDefinition(con->functor(),DArray<unsigned>(0),count);
      cells.fun[con->functor()] = true;
      count++;
    }
  }

  {
    UnitList::Iterator uit(units);
    while(uit.hasNext()){
      Unit* u = uit.next();
      if(!Parse::TPTP::isModelDefinition(u)) continue;
      if(isDomainAxiom(u)) continue;

      // All model formulas should be conjunctions of definitions
      // TODO allow for unit clause definitions in the future
      if(u->isClause()) USER_ERROR("Expecting model to use formulas i.e. fof/tff");
      Formula* formula = u->getFormula();
      if(isSymbolicDefinition(formula,domainConstants)) continue; // read above

      TableContext ctx{u,domainConstants,domainConstantNumber,symbolic,funDefinedBy,predDefinedBy,cells};
      if(formula->connective()==Connective::NOT){
        Formula* inner = formula->uarg();
        if(inner->connective()==Connective::LITERAL){
          addDefinition(model,inner->literal(),true,ctx);
        }
        else USER_ERROR("Unexpected negation in "+formula->toString());
      }
      else if(formula->connective()==Connective::LITERAL){
        addDefinition(model,formula->literal(),false,ctx);
      }
      else{
        if(formula->connective()!=Connective::AND)
          USER_ERROR("Expecting conjunction of definitions in model:\n"+formula->toString());
        FormulaList* defs = formula->args();
        FormulaList::Iterator fit(defs);
        while(fit.hasNext()){
          unsigned negated = false;
          Formula* def = fit.next();
          if(def->connective()==Connective::NOT){
            def = def->uarg();
            negated=true;
          }
          if(def->connective()!=Connective::LITERAL) USER_ERROR("Badly formed definition");
          Literal* lit = def->literal();
          addDefinition(model,lit,negated,ctx);
        }
      }
    }

    addSymbolicDefinitions(model,symbolic,funDefinedBy,predDefinedBy,cells,domainConstants,domainConstantNumber);

    std::cout << "Model loaded" << std::endl;
    std::cout << "Checking formulas..." << std::endl;
    {
      bool allTrue = true;
      UnitList::Iterator uit(units);
      while(uit.hasNext()){
        Unit* u = uit.next();
        if(Parse::TPTP::isModelDefinition(u)) continue;

        std::cout << "Checking " << u->toString() << "..." << std::endl;
        bool res;
        try {
          res = model.evaluate(u);
        } catch (UndefinedValueException& e) {
          USER_ERROR("The loaded model is partial: " + e.msg() + " (needed to evaluate the above)");
        }
        allTrue &= res;
        std::cout << "Evaluates to " << (res ? "True" : "False") << std::endl;
      }
      if (allTrue) {
        std::cout << "All formulas evaluated to True!" << std::endl;
      } else {
        std::cout << "There was a false formula!" << std::endl;
      }
    }
  }
}

private:

/**
 * Mark every function and predicate the model definitions among @b units mention.
 *
 * Deliberately not a Property scan: symbol usage is no longer recorded on the signature,
 * and the question here is narrower anyway -- which symbols this *model* speaks about,
 * not which ones the whole file mentions.
 *
 * Model formulas are read as parsed, so they may contain unshared terms and FOOL special
 * terms; hence no visited set (which would want Term::getId()) and an explicit descent
 * into a formula sitting in term position.
 */
static void collectModelSymbols(UnitList* units, DArray<bool>& usedFunctions, DArray<bool>& usedPredicates)
{
  usedFunctions.init(env.signature->functions(),false);
  usedPredicates.init(env.signature->predicates(),false);

  // $true and $false may occur in term position, in the model as well as in the units to
  // check, and are then the two elements of the boolean domain -- so the model needs a
  // table for them. The parser only ever builds them as special terms (see
  // FiniteModelMultiSorted::deFool), so walking the terms would not find them.
  if (env.signature->foolConstantsDefined()) {
    for (unsigned i = 0; i < 2; i++) {
      usedFunctions[env.signature->getFoolConstantSymbol(i > 0)] = true;
    }
  }

  Stack<TermList> todo;
  auto collectTerm = [&usedFunctions,&todo](TermList tl) {
    todo.push(tl);
    while (todo.isNonEmpty()) {
      TermList cur = todo.pop();
      if (!cur.isTerm()) {
        continue;
      }
      Term* t = cur.term();
      if (t->isSort()) {
        continue; // sorts are built from type constructors, not from function symbols
      }
      if (!t->isSpecial()) { // a special term's head is not a function symbol
        usedFunctions[t->functor()] = true;
      }
      for (unsigned i = 0; i < t->arity(); i++) {
        todo.push(*t->nthArgument(i));
      }
    }
  };

  UnitList::Iterator uit(units);
  while (uit.hasNext()) {
    Unit* u = uit.next();
    if (!Parse::TPTP::isModelDefinition(u)) continue;
    if (u->isClause()) continue; // rejected later, with a message
    SubformulaIterator sfit(u->getFormula());
    while (sfit.hasNext()) {
      Formula* sf = sfit.next();
      if (sf->connective() == Connective::BOOL_TERM) {
        collectTerm(sf->getBooleanTerm());
        continue;
      }
      if (sf->connective() != Connective::LITERAL) continue;
      Literal* lit = sf->literal();
      if (!lit->isEquality()) { // equality is never tabulated
        usedPredicates[lit->functor()] = true;
      }
      for (unsigned i = 0; i < lit->arity(); i++) {
        collectTerm(*lit->nthArgument(i));
      }
    }
  }
}

static void checkIsDomainLiteral(Literal* l, int& single_var, DomainConstantSet& domainConstants)
{
  if(!l->isEquality()) USER_ERROR("finite_domain is not a domain axiom");

  // put var in left and constant in right
  // (deFool, because the domain of $o is spelled with $true and $false)
  TermList left = FiniteModelMultiSorted::deFool(*l->nthArgument(0));
  TermList right = FiniteModelMultiSorted::deFool(*l->nthArgument(1));
  if(right.isVar()){
    std::swap(left,right);
  }
  // a leftover special term is a FOOL construct we cannot read (deFool covers $true / $false)
  if(left.isTerm() || right.isVar() || right.term()->isSpecial())
    USER_ERROR("finite_domain is not a domain axiom:\n"+l->toString());

  // store and check the single variable used
  if(single_var<0) single_var=left.var();
  if(left.var()!=(unsigned)single_var) USER_ERROR("finite_domain is not a domain axiom");

  // store and check the ground constant used
  Term* constant = right.term();
  unsigned f = constant->functor();
  if(env.signature->functionArity(f)!=0) USER_ERROR("finite_domain is not a domain axiom");
  if(domainConstants.contains(constant)) USER_ERROR("finite_domain is not a domain axiom");

  domainConstants.insert(constant);
}

/**
 * Is @b t one of the model's domain constants?
 *
 * Ask this rather than domainConstants.contains(t.term()) directly. That set hashes a term
 * by Term::getId(), which only a shared term has, and the terms reaching addDefinition need
 * not be shared: deFool only rewrites the top of a term, so a definition's left-hand side is
 * still unshared whenever an argument is a FOOL special term -- "g($false,'fmb_$i_1')" in
 * checks/fmb/bool.check.p, whose arguments are deFooled only further down. Nothing is lost
 * by answering no: every domain constant is an ordinary shared constant.
 */
static bool isDomainConstant(const DomainConstantSet& domainConstants, TermList t)
{
  return t.isTerm() && t.term()->shared() && domainConstants.contains(t.term());
}

/**
 * A model formula that defines its head symbol by a formula rather than cell by cell:
 * ![Xs]: (f(Xs) = t) or ![Xs]: (p(Xs) <=> F), and for a constant or a proposition the
 * unquantified c = t (with neither side a domain constant, or it would be a table cell) and
 * q <=> F. The head is on the left, as FMB prints it.
 */
struct SymbolicDefinition {
  Unit* unit;
  bool pred;
  std::unique_ptr<Problem::FunDef> fd; // exactly one of these two is set
  std::unique_ptr<Problem::PredDef> pd;
  // for a predicate definition loaded as cases (see readCases): the definition of its fall-back
  std::unique_ptr<Problem::PredDef> fallBack;

  unsigned symbol() const { return pred ? pd->_head->functor() : fd->_head->functor(); }
  std::string symbolName() const {
    return pred ? env.signature->predicateName(symbol()) : env.signature->functionName(symbol());
  }
};

struct TableCells {
  DArray<bool> fun;
  DArray<bool> pred;
};

// what addDefinition needs to know besides the literal
struct TableContext {
  Unit* unit;
  const DomainConstantSet& domainConstants;
  DHMap<Term*,unsigned, FnvHash, PtrIdentityHash>& domainConstantNumber;
  const Stack<SymbolicDefinition>& symbolic;
  const DArray<int>& funDefinedBy;
  const DArray<int>& predDefinedBy;
  TableCells& cells;
};

static std::string unitName(Unit* u)
{
  std::string name;
  std::filesystem::path path;
  return Parse::TPTP::findAxiomName(u,name,path) ? name : u->toString();
}

static bool isDomainAxiom(Unit* u)
{
  std::string name = unitName(u);
  return StringUtils::starts_with(name,"finite_domain") || StringUtils::starts_with(name,"distinct_domain");
}

// is this model formula a symbolic definition (see SymbolicDefinition), as opposed to table cells?
static bool isSymbolicDefinition(Formula* f, const DomainConstantSet& domainConstants)
{
  switch (f->connective()) {
    case Connective::FORALL:
    case Connective::IFF:
      return true;
    case Connective::LITERAL: {
      Literal* l = f->literal();
      return l->isEquality() && l->polarity() &&
        !isDomainConstant(domainConstants,FiniteModelMultiSorted::deFool(*l->nthArgument(0))) &&
        !isDomainConstant(domainConstants,FiniteModelMultiSorted::deFool(*l->nthArgument(1)));
    }
    default:
      return false;
  }
}

/**
 * Read one symbolic definition, rejecting on the spot what is malformed: the head must be a
 * symbol applied to pairwise distinct variables, exactly the quantified ones, the body may
 * have no other free variables, and the evaluator must be able to evaluate it.
 */
static SymbolicDefinition readSymbolicDefinition(Unit* u, const DomainConstantSet& domainConstants)
{
  auto reject = [u](const std::string& why) {
    USER_ERROR("Cannot read the model definition " + unitName(u) + ": " + why + "\n" + u->toString());
  };

  Formula* core = u->getFormula();
  DHSet<unsigned, FnvHash, IdentityHash> quantified;
  unsigned numQuantified = 0;
  while (core->connective() == Connective::FORALL) {
    for (VSList* vs = core->vars(); vs; vs = vs->tail()) {
      quantified.insert(vs->head().first);
      numQuantified++;
    }
    core = core->qarg();
  }

  SymbolicDefinition sd;
  sd.unit = u;
  Term* head = nullptr;
  if (core->connective() == Connective::LITERAL && core->literal()->isEquality() && core->literal()->polarity()) {
    Literal* eq = core->literal();
    // the head is the side written on the left; sharing may have swapped the two, and the
    // parser records when it did (AtomicFormula::flipForPrinting)
    bool flipped = static_cast<AtomicFormula*>(core)->flipForPrinting;
    TermList lhs = *eq->nthArgument(flipped ? 1 : 0);
    TermList rhs = *eq->nthArgument(flipped ? 0 : 1);
    if (lhs.isVar() || lhs.term()->isSpecial() || isDomainConstant(domainConstants,lhs)) {
      reject("the left-hand side must be the defined symbol applied to the quantified variables");
    }
    if (rhs.isVar()) {
      reject("a variable as the whole right-hand side is not supported");
    }
    sd.pred = false;
    sd.fd.reset(new Problem::FunDef(lhs.term(),rhs.term()));
    head = lhs.term();
  } else if (core->connective() == Connective::IFF && core->left()->connective() == Connective::LITERAL &&
             !core->left()->literal()->isEquality() && core->left()->literal()->polarity()) {
    sd.pred = true;
    sd.pd.reset(new Problem::PredDef(core->left()->literal(),core->right()));
    head = core->left()->literal();
  } else {
    reject("expected ![X0,...]: (f(X0,...) = t) or ![X0,...]: (p(X0,...) <=> F)");
  }

  DHSet<unsigned, FnvHash, IdentityHash> headVars;
  for (unsigned i = 0; i < head->arity(); i++) {
    TermList arg = *head->nthArgument(i);
    if (!arg.isVar() || !quantified.contains(arg.var())) {
      reject("the arguments of " + head->toString() + " must be the quantified variables");
    }
    if (!headVars.insert(arg.var())) {
      reject("the arguments of " + head->toString() + " must be pairwise distinct");
    }
  }
  if (headVars.size() != numQuantified) {
    reject("every quantified variable must be an argument of " + head->toString());
  }
  VList::Iterator fvit(freeVariables(core));
  while (fvit.hasNext()) {
    if (!headVars.contains(fvit.next())) {
      reject("the body has a free variable that is not an argument of " + head->toString());
    }
  }
  if (!FiniteModelMultiSorted::evaluable(core)) {
    reject("the body contains a construct the model checker cannot evaluate");
  }
  return sd;
}

static void readSymbolicDefinitions(UnitList* units, const DomainConstantSet& domainConstants,
                                    Stack<SymbolicDefinition>& symbolic,
                                    DArray<int>& funDefinedBy, DArray<int>& predDefinedBy)
{
  funDefinedBy.init(env.signature->functions(),-1);
  predDefinedBy.init(env.signature->predicates(),-1);

  UnitList::Iterator uit(units);
  while (uit.hasNext()) {
    Unit* u = uit.next();
    if (!Parse::TPTP::isModelDefinition(u) || u->isClause() || isDomainAxiom(u)) continue;
    if (!isSymbolicDefinition(u->getFormula(),domainConstants)) continue;

    symbolic.push(readSymbolicDefinition(u,domainConstants));
    const SymbolicDefinition& sd = symbolic.top();
    int& definedBy = (sd.pred ? predDefinedBy : funDefinedBy)[sd.symbol()];
    if (definedBy >= 0) {
      USER_ERROR(sd.symbolName() + " is defined twice in the model, by " +
                 unitName(symbolic[definedBy].unit) + " and by " + unitName(u));
    }
    definedBy = symbolic.size()-1;
  }
}

/**
 * Is the definition p(Xs) <=> $cond(c1, v1, ..., cn, vn, else) one of cases, as FMB prints a
 * conditional flip: every ci a conjunction of equations Xj = e, one for each of the head's
 * variables, e a domain constant, and every vi $true or $false? Then collect the cases, in
 * order, as the tuples they select with their values, and the fall-back else.
 */
static bool readCases(Problem::PredDef* pd, const DomainConstantSet& domainConstants,
                      DHMap<Term*,unsigned, FnvHash, PtrIdentityHash>& domainConstantNumber,
                      Stack<std::pair<DArray<unsigned>,bool>>& cases, TermList& fallBack)
{
  Literal* head = pd->_head;
  if (!head->isPositive() || pd->_body->connective() != Connective::BOOL_TERM) return false;
  TermList body = pd->_body->getBooleanTerm();
  if (!body.isTerm() || !body.term()->isSpecial() || body.term()->specialFunctor() != SpecialFunctor::COND) return false;
  Term* cond = body.term();
  unsigned arity = head->arity();
  if (arity == 0) return false;

  auto formulaOf = [](TermList t) -> Formula* {
    return (t.isTerm() && t.term()->isSpecial() && t.term()->specialFunctor() == SpecialFunctor::FORMULA) ?
      t.term()->getSpecialData()->getFormula() : nullptr;
  };
  // the position of each head variable
  auto position = [head,arity](unsigned var) -> int {
    for (unsigned j = 0; j < arity; j++) {
      if (head->nthArgument(j)->var() == var) return j;
    }
    return -1;
  };

  for (unsigned i = 0; i+1 < cond->arity(); i += 2) {
    Formula* c = formulaOf(*cond->nthArgument(i));
    Formula* v = formulaOf(*cond->nthArgument(i+1));
    if (!c || !v || (v->connective() != Connective::TRUE && v->connective() != Connective::FALSE)) return false;

    Stack<Formula*> eqs;
    if (c->connective() == Connective::AND) {
      FormulaList::Iterator it(c->args());
      while (it.hasNext()) eqs.push(it.next());
    } else {
      eqs.push(c);
    }
    if (eqs.size() != arity) return false;
    DArray<unsigned> args;
    args.init(arity,0);
    for (unsigned k = 0; k < eqs.size(); k++) {
      if (eqs[k]->connective() != Connective::LITERAL) return false;
      Literal* l = eqs[k]->literal();
      if (!l->isEquality() || !l->isPositive()) return false;
      TermList x = *l->nthArgument(0);
      TermList e = FiniteModelMultiSorted::deFool(*l->nthArgument(1));
      if (!x.isVar()) {
        x = *l->nthArgument(1);
        e = FiniteModelMultiSorted::deFool(*l->nthArgument(0));
      }
      if (!x.isVar() || !isDomainConstant(domainConstants,e)) return false;
      int j = position(x.var());
      if (j < 0 || args[j] != 0) return false; // not a head variable, or one twice
      args[j] = domainConstantNumber.get(e.term());
    }
    cases.push({std::move(args),v->connective() == Connective::TRUE});
  }
  fallBack = *cond->nthArgument(cond->arity()-1);
  return true;
}

/**
 * Check what the symbolic definitions mention and add them to the model, each after the
 * definitions its body uses: a definition layer reads the model as it stands when it is
 * added (DefFunLayer::value). The order in the file does not matter; a cycle, of any
 * length, is an error.
 */
static void addSymbolicDefinitions(FiniteModelMultiSorted& model, Stack<SymbolicDefinition>& symbolic,
                                   const DArray<int>& funDefinedBy, const DArray<int>& predDefinedBy,
                                   const TableCells& cells, const DomainConstantSet& domainConstants,
                                   DHMap<Term*,unsigned, FnvHash, PtrIdentityHash>& domainConstantNumber)
{
  // the edges: which definitions each definition's body uses
  DArray<Stack<unsigned>> uses(symbolic.size());
  for (unsigned i = 0; i < symbolic.size(); i++) {
    const SymbolicDefinition& sd = symbolic[i];
    FiniteModelMultiSorted::BodySymbols syms;
    ALWAYS(sd.pred ? FiniteModelMultiSorted::collectBodySymbols(sd.pd->_body,syms)
                   : FiniteModelMultiSorted::collectBodySymbols(TermList(sd.fd->_body),syms));
    for (unsigned j = 0; j < syms.funs.size(); j++) {
      unsigned f = syms.funs[j];
      if (funDefinedBy[f] >= 0) {
        uses[i].push(funDefinedBy[f]);
      } else if (!cells.fun[f]) {
        USER_ERROR("The model definition " + unitName(sd.unit) + " mentions " + env.signature->functionName(f) +
                   ", which the model neither tabulates nor defines");
      }
    }
    for (unsigned j = 0; j < syms.preds.size(); j++) {
      unsigned p = syms.preds[j];
      if (predDefinedBy[p] >= 0) {
        uses[i].push(predDefinedBy[p]);
      } else if (!cells.pred[p]) {
        USER_ERROR("The model definition " + unitName(sd.unit) + " mentions " + env.signature->predicateName(p) +
                   ", which the model neither tabulates nor defines");
      }
    }
  }

  // depth-first, iteratively (a chain of definitions can be long); a definition is added
  // once everything it uses has been
  enum : char { UNSEEN, ON_PATH, ADDED };
  DArray<char> state;
  state.init(symbolic.size(),UNSEEN);
  struct Frame { unsigned def; unsigned next; };
  Stack<Frame> path;
  for (unsigned root = 0; root < symbolic.size(); root++) {
    if (state[root] != UNSEEN) continue;
    state[root] = ON_PATH;
    path.push({root,0});
    while (path.isNonEmpty()) {
      Frame& fr = path.top();
      if (fr.next < uses[fr.def].size()) {
        unsigned used = uses[fr.def][fr.next++];
        if (state[used] == ON_PATH) {
          // the cycle is the part of the path from used on
          std::string chain;
          bool onCycle = false;
          for (unsigned k = 0; k < path.size(); k++) {
            onCycle |= (path[k].def == used);
            if (onCycle) chain += unitName(symbolic[path[k].def].unit) + " -> ";
          }
          USER_ERROR("The model's definitions are cyclic: " + chain + unitName(symbolic[used].unit));
        }
        if (state[used] == UNSEEN) {
          state[used] = ON_PATH;
          path.push({used,0});
        }
        continue;
      }
      SymbolicDefinition& sd = symbolic[fr.def];
      Stack<std::pair<DArray<unsigned>,bool>> cases;
      TermList fallBack;
      if (!sd.pred) {
        model.addSymbolicDefinition(sd.fd.get());
      } else if (readCases(sd.pd.get(),domainConstants,domainConstantNumber,cases,fallBack)) {
        // p <=> $cond(cases..., else): p := else, with the cases on top, as the flip it was
        // printed from -- a lookup is then a hash probe, not a walk through the cases
        Formula* fallBackFormula = (fallBack.isTerm() && fallBack.term()->isSpecial() &&
                                    fallBack.term()->specialFunctor() == SpecialFunctor::FORMULA) ?
          fallBack.term()->getSpecialData()->getFormula() : new BoolTermFormula(fallBack);
        sd.fallBack.reset(new Problem::PredDef(sd.pd->_head,fallBackFormula));
        model.addSymbolicDefinition(sd.fallBack.get());
        CondFlipPredLayer* layer = model.addCasesLayer(sd.symbol());
        for (unsigned k = 0; k < cases.size(); k++) {
          char v;
          if (layer->prescribed().find(ArgsKey(cases[k].first),v)) continue; // the first case wins
          layer->prescribe(cases[k].first,cases[k].second ? INTP_TRUE : INTP_FALSE);
        }
      } else {
        model.addSymbolicDefinition(sd.pd.get());
      }
      state[fr.def] = ADDED;
      path.pop();
    }
  }
}

static void addDefinition(FiniteModelMultiSorted& model,Literal* lit,bool negated,TableContext& ctx)
{
  const DomainConstantSet& domainConstants = ctx.domainConstants;
  DHMap<Term*,unsigned, FnvHash, PtrIdentityHash>& domainConstantNumber = ctx.domainConstantNumber;

  // a symbolically defined symbol has no table, and must not get cells either
  auto checkNotSymbolic = [&ctx](int definedBy, const std::string& name) {
    if (definedBy >= 0) {
      USER_ERROR(name + " is defined twice in the model, by " + unitName(ctx.symbolic[definedBy].unit) +
                 " and by table cells in " + unitName(ctx.unit));
    }
  };
  auto conflict = [&ctx,lit]() {
    USER_ERROR("The model gives two different values to a cell, the second time in " + unitName(ctx.unit) +
               ":\n" + lit->toString());
  };

  if(lit->isEquality()){
    if(!lit->polarity() || negated) USER_ERROR("Cannot have negated function definition");
    // Defining a function or constant
    // (deFool, because the elements of $o are spelled with $true and $false)
    TermList left = FiniteModelMultiSorted::deFool(*lit->nthArgument(0));
    TermList right = FiniteModelMultiSorted::deFool(*lit->nthArgument(1));
    if(isDomainConstant(domainConstants,left)){
      std::swap(left,right);
    }

    if(left.isVar()) USER_ERROR("Expect term on left of definition");
    // a leftover special term is a FOOL construct we cannot read (deFool covers $true / $false)
    if(left.term()->isSpecial())
      USER_ERROR("Cannot read the definition:\n"+lit->toString());
    if(isDomainConstant(domainConstants,left))
      USER_ERROR("Cannot have equality between domain elements:\n"+lit->toString());
    if(!isDomainConstant(domainConstants,right))
      USER_ERROR("Expect a domain constant on the right of definition:\n"+lit->toString());
    unsigned res = domainConstantNumber.get(right.term());
    Term* fun = left.term();
    unsigned f = fun->functor();
    checkNotSymbolic(ctx.funDefinedBy[f],env.signature->functionName(f));
    unsigned arity = env.signature->functionArity(f);
    DArray<unsigned> args(arity);
    for(unsigned i=0;i<arity;i++){
      TermList arg = FiniteModelMultiSorted::deFool(*fun->nthArgument(i));
      if(!isDomainConstant(domainConstants,arg))
        USER_ERROR("Expect term on left of definition to be grounded with domain constants");
      args[i] = domainConstantNumber.get(arg.term());
    }
    unsigned old = model.addFunctionDefinition(f,args,res);
    if (old != FUNV_UNDEF && old != res) conflict();
    ctx.cells.fun[f] = true;
  }else{
    // not sure this makes sense but...
    if(!lit->polarity()) negated=!negated;
    // Defining a predicate or proposition
    unsigned p = lit->functor();
    checkNotSymbolic(ctx.predDefinedBy[p],env.signature->predicateName(p));
    unsigned arity = env.signature->predicateArity(p);

    DArray<unsigned> args(arity);
    for(unsigned i=0;i<arity;i++){
      TermList arg = FiniteModelMultiSorted::deFool(*lit->nthArgument(i));
      if(!isDomainConstant(domainConstants,arg))
        USER_ERROR("Expect term on left of definition to be grounded with domain constants");
      args[i] = domainConstantNumber.get(arg.term());
    }
    char old = model.addPredicateDefinition(p,args,!negated);
    if (old != INTP_UNDEF && old != (negated ? INTP_FALSE : INTP_TRUE)) conflict();
    ctx.cells.pred[p] = true;
  }
}

};

} // namespace FMB
#endif
