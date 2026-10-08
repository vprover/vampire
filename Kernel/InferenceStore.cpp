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
 * @file InferenceStore.cpp
 * Implements class InferenceStore.
 */

#include "Debug/Assertion.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/SMTCheck.hpp"

#include "Parse/TPTP.hpp"
#include "SAT/SATInference.hpp"

#include "Saturation/Splitter.hpp"

#include "HOL/HOL.hpp"
#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "FormulaVarIterator.hpp"
#include "Inference.hpp"
#include "NumTraits.hpp"
#include "Signature.hpp"
#include "SortHelper.hpp"

#include "InferenceStore.hpp"
#include "TPTPProofPrinter.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"
#include "Theory.hpp"
#include "Unit.hpp"

#include <set>
#include <string>
#include <vector>
//TODO: when we delete clause, we should also delete all its records from the inference store

namespace Kernel
{

using namespace std;
using namespace Lib;
using namespace Shell;
using namespace SAT;

/**
 * Records information needed for outputting proofs of general splitting
 */
void InferenceStore::recordSplittingNameLiteral(Unit* us, Literal* lit)
{
  //each clause is result of a splitting only once
  ALWAYS(_splittingNameLiterals.insert(us->number(), lit));
}


/**
 * Record the introduction of a new symbol
 */
void InferenceStore::recordIntroducedSymbol(Unit* u, const Signature::Symbol* sym)
{
  ASS_REP(sym->introduced(), sym->name());

  SymbolStack* pStack;
  _introducedSymbols.getValuePtr(u->number(),pStack);
  pStack->push(sym);
}

void InferenceStore::recordIntroducedSkolemSymbol(Unit* u, const Signature::Symbol* sym, unsigned replacedVar, Term* symTerm)
{
  ASS_REP(sym->introduced(), sym->name());

  SymbolStack* pStack;
  _introducedSymbols.getValuePtr(u->number(),pStack);
  _introducedSymbolReplacedVars.insert(sym, replacedVar);
  _introducedSkolemSymTerms.insert(sym, symTerm);
  pStack->emplace(sym);
}

/**
 * Record the introduction of a split name
 */
void InferenceStore::recordIntroducedSplitName(Unit* u, std::string name)
{
  ALWAYS(_introducedSplitNames.insert(u->number(),name));
}

bool InferenceStore::AbstractProofPrinter::CompareUnits::operator()(Unit* left, Unit* right) const
{
  return left->number() < right->number();
}

// compute closure of `us`' ancestors for printing and insert into `proof`
void InferenceStore::AbstractProofPrinter::scheduleForPrinting(Unit* us)
{
  std::vector<Unit *> todo = { us };
  while(!todo.empty()) {
    Unit *next = todo.back();
    todo.pop_back();

    // check if this step should be printed
    InferenceRule rule = next->inference().rule();
    if(!hideProofStep(rule)) {
      // check if already processed (proofs are DAGs, not trees)
      auto [_, inserted] = proof.insert(next);
      if(!inserted)
        continue;
    }
    // NB step may be hidden, but its parents are not
    // TODO not sure this is desirable, but it was the old behaviour

    // process premise parents
    UnitIterator parents = next->getParents();
    while(parents.hasNext()) {
      Unit* prem = parents.next();
      ASS_NEQ(prem, next)
      todo.push_back(prem);
    }
  }
}

void InferenceStore::AbstractProofPrinter::print()
{
  for (Unit* unit : proof) { printStep(unit); }
}

struct InferenceStore::ProofPrinter : public InferenceStore::AbstractSATProofPrinter
{
  using AbstractSATProofPrinter::AbstractSATProofPrinter;

protected:
  void printStep(Unit* cs) override
  {
    if (cs->isClause()) {
      Clause* cl=cs->asClause();
      out << cl->toString() << "\n";
    } else {
      InferenceRule rule = cs->inference().rule();
      UnitIterator parents= cs->getParents();

      out << cs->number() << ". ";
      FormulaUnit* fu=static_cast<FormulaUnit*>(cs);
      if (env.colorUsed && fu->inheritedColor() != COLOR_INVALID) {
        out << " IC" << fu->inheritedColor() << " ";
      }
      out << fu->formula()->toString() << ' ';

      out <<"["<<cs->inference().name();

      if (rule==InferenceRule::INPUT) {
        ASS(!parents.hasNext()); //input clauses don't have parents
        std::string name;
        std::filesystem::path path;
        if (Parse::TPTP::findAxiomName(cs, name, path)) {
          out << " " << name << " " << path;
        }
      }

      bool first=true;
      while(parents.hasNext()) {
        Unit* prem=parents.next();
        out << (first ? ' ' : ',');
        out << prem->number();
        first=false;
      }

      if(env.options->proofExtra() == Options::ProofExtra::FULL) {
        auto *extra = env.proofExtra.find(cs);
        if(extra)
          out
            << (first ? ' ' : ',')
            << *extra;
      }

      out << "]" << endl;
    }
  }

  void printSATStep(SATClause *cl) override {
    out << *cl << '\n';
  }

};

namespace {

struct CompareSATClauses {
  bool operator()(SATClause *l, SATClause *r) const { return l->number < r->number; }
};

// produce a topological sort of the SAT proof starting at `root`
std::set<SATClause *, CompareSATClauses> topological_sort(SATClause *root) {
  // things inserted in here will be topologically sorted,
  // because it's an ordered set and the clauses are numbered
  std::set<SATClause *, CompareSATClauses> topological;

  // compute closure of root and insert into `topological`
  std::vector<SATClause *> todo = { root };
  while(!todo.empty()) {
    SATClause *next = todo.back();
    todo.pop_back();

    // check if already processed (proofs are DAGs, not trees)
    auto [_, inserted] = topological.insert(next);
    if(!inserted)
      continue;

    // process premise parents
    SATInference *inference = next->inference();
    if(inference->getType() != SATInference::InfType::PROP_INF)
      continue;
    SATClauseList *parents =
      static_cast<PropInference *>(inference)->getPremises();
    for(SATClause *parent : iterTraits(parents->iter()))
      todo.push_back(parent);
  }

  return topological;
}
} // namespace

void InferenceStore::AbstractSATProofPrinter::print()
{
  for (Unit* unit : proof) {
    if (SATClause* sat = unit->inference().satPremise()) {
      for (SATClause* clause : topological_sort(sat)) { printSATStep(clause); }
    }
    printStep(unit);
  }
}

struct InferenceStore::ProofPropertyPrinter
: public InferenceStore::AbstractProofPrinter
{
  ProofPropertyPrinter(std::ostream& out, InferenceStore* is) : AbstractProofPrinter(out,is)
  {
    max_theory_clause_depth = 0;
    for(unsigned i=0;i<11;i++){ buckets.push(0); }
    last_one = false;
  }

  void print() override
  {
    AbstractProofPrinter::print();
    for(unsigned i=0;i<11;i++){ out << buckets[i] << " ";}
    out << endl;
    if(last_one){ out << "yes" << endl; }
    else{ out << "no" << endl; }
  }

protected:

  void printStep(Unit* us) override
  {
    static unsigned lastP = Unit::getLastParsingNumber();
    static float chunk = lastP / 10.0;
    if(us->number() <= lastP){
      if(us->number() == lastP){
        last_one = true;
      }
      unsigned bucket = (unsigned)(us->number() / chunk);
      buckets[bucket]++;
    }

    // TODO we could make clauses track this information, but I am not sure that that's worth it
    if(us->isClause() && us->isPureTheoryDescendant()){
      //cout << "HERE with " << us->toString() << endl;
      Inference* inf = &us->inference();
      while(inf->rule() == InferenceRule::EVALUATION){
        Inference::Iterator piit = inf->iterator();
        inf = &inf->next(piit)->inference();
      }
      Stack<Inference*> current;
      current.push(inf);
      unsigned level = 0;
      while(!current.isEmpty()){
        //cout << current.size() << endl;
        Stack<Inference*> next;
        Stack<Inference*>::Iterator it(current);
        while(it.hasNext()){
          Inference* inf = it.next();
          Inference::Iterator iit=inf->iterator();
          while(inf->hasNext(iit)) {
            Unit* premUnit=inf->next(iit);
            Inference* premInf = &premUnit->inference();
            while(premInf->rule() == InferenceRule::EVALUATION){
              Inference::Iterator piit = premInf->iterator();
              premUnit = premInf->next(piit);
              premInf = &premUnit->inference();
            }

//for(unsigned i=0;i<level;i++){ cout << ">";}; cout << premUnit->toString() << endl;
            next.push(premInf);
          }
        }
        level++;
        current = next;
      }
      level--;
      //cout << "level is " << level << endl;

      if(level > max_theory_clause_depth){
        max_theory_clause_depth=level;
      }
    }
  }

  unsigned max_theory_clause_depth;
  bool last_one;
  Stack<unsigned> buckets;

};


struct InferenceStore::ProofCheckPrinter
: public InferenceStore::AbstractProofPrinter
{
  ProofCheckPrinter(std::ostream& out, InferenceStore* is)
  : AbstractProofPrinter(out, is) {}

protected:
  void printStep(Unit* cs) override
  {
    InferenceRule rule = cs->inference().rule();
    UnitIterator parents= cs->getParents();

    //an fof proof needs no type declarations, see TPTPProofPrinter::print
    if(env.initiallyHasNonDefaultSorts() || env.initiallyHigherOrder()){
      //outputSymbolDeclarations also deals with sorts for now
      //UIHelper::outputSortDeclarations(out);
      UIHelper::outputSymbolDeclarations(out);
    }

    // fragment of the unpreprocessed input, see the comment in getFofString
    std::string kind = "fof";
    if(env.initiallyHasNonDefaultSorts()){ kind="tff"; }
    if(env.initiallyHigherOrder()){ kind="thf"; }

    out << kind
        << "(r"<< cs->number()
    	<< ",conjecture, "
      << getQuantifiedStr(cs)
    	<< " ). %"<<ruleName(rule)<<"\n";

    while(parents.hasNext()) {
      Unit* prem=parents.next();
      out << kind
        << "(pr"<<prem->number()
  	<< ",axiom, "
    << getQuantifiedStr(prem);
      out << " ).\n";
    }
    out << "%#\n";
  }

  bool hideProofStep(InferenceRule rule) override
  {
    switch(rule) {
    case InferenceRule::INPUT:
    case InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    case InferenceRule::INEQUALITY_SPLITTING:
    case InferenceRule::SKOLEMIZE:
    case InferenceRule::SKOLEM_SYMBOL_INTRODUCTION:
    case InferenceRule::EQUALITY_PROXY_REPLACEMENT:
    case InferenceRule::EQUALITY_PROXY_DEFINITION:
    case InferenceRule::EQUALITY_PROXY_AXIOM:
    case InferenceRule::NEGATED_CONJECTURE:
    case InferenceRule::RECTIFY:
    case InferenceRule::FLATTEN:
    case InferenceRule::ENNF:
    case InferenceRule::NNF:
    case InferenceRule::CLAUSIFY:
    case InferenceRule::AVATAR_DEFINITION:
    case InferenceRule::AVATAR_COMPONENT:
    case InferenceRule::AVATAR_REFUTATION:
    case InferenceRule::AVATAR_REFUTATION_SMT:
    case InferenceRule::AVATAR_SPLIT_CLAUSE:
    case InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
    case InferenceRule::FOOL_ELIMINATION:
    case InferenceRule::BOOLEAN_TERM_ENCODING:
    case InferenceRule::PREDICATE_DEFINITION:
      return true;
    default:
      return false;
    }
  }

  void print() override
  {
    AbstractProofPrinter::print();
    out << "%#\n";
  }
};
struct InferenceStore::Smt2ProofCheckPrinter
: public InferenceStore::AbstractProofPrinter
{
  USE_ALLOCATOR(InferenceStore::Smt2ProofCheckPrinter);
  
  Smt2ProofCheckPrinter(std::ostream& out, InferenceStore* is)
  : AbstractProofPrinter(out, is) {}

protected:

  static bool isBuiltInSort(std::ostream& out, unsigned sortCons) {
    auto& sig = *env.signature;
    auto arity = sig.typeConArity(sortCons);
    auto args = range(0, arity)
              .map([](auto _a) { return AtomicSort::intSort(); })
              .template collect<Stack>();
    auto sortInstance = TermList(AtomicSort::create(sortCons, arity, args.begin()));
    if (env.signature->isTermAlgebraSort(sortInstance)) {
      out << "=== warning term algebras are not yet implemented for proof checking ==" << std::endl;
    }
    return sig.isArrayCon(sortCons)
      || sortInstance == AtomicSort::intSort()
      || sortInstance == AtomicSort::realSort()
      || sortInstance == AtomicSort::rationalSort();
  }

  static void outputSymbolDeclarations(std::ostream& out)
  {
    auto& sig = *env.signature;

    for (unsigned i=0; i < sig.typeCons(); ++i) {
      if (!isBuiltInSort(/* may output warning */ out, i)) {
        out << "(declare-sort ";
        outputQuoted(out, sig.typeConName(i));
        out << " "
            << sig.typeConArity(i) << ")" 
            << std::endl;
      }
    }
    for (unsigned i = 0; i < sig.functions(); ++i) {
      if ( env.signature->isFoolConstantSymbol(true,i) 
        || env.signature->isFoolConstantSymbol(false,i)
        || theory->isInterpretedFunction(i)
        || theory->isInterpretedConstant(i))  {
        /* don't output */
      } else {
        out << "(declare-fun ";
        outputFunctionName(out, i);
        out << " (";
        auto fty = sig.getFunction(i)->type();
        for (auto a : range(0, sig.functionArity(i))) {
          out << " ";
          outputSort(out, fty->arg(a));
        }
        out << " )";
        outputSort(out, fty->result());
        out << ")" 
            << std::endl;
      }
    }
    for (unsigned i = 0; i < sig.predicates(); ++i) {
      auto fty = sig.getPredicate(i)->type();
      // we might introduce an equality proxy for rationals, which 
      // we cannot translate to smt2 as there are no rationals there
      // therefore we skip that
      auto hasRatArg = range(0, sig.predicateArity(i))
          .any([&](auto a)
              { return fty->arg(a) == AtomicSort::rationalSort(); });
      if (!theory->isInterpretedPredicate(i) && !hasRatArg) {

        out << "(declare-fun ";
        outputPredicateName(out, i);
        out << " (";
        for (auto a : range(0, sig.predicateArity(i))) {
          out << " ";
          auto s = fty->arg(a);
          outputSort(out, s);
        }
        out << " ) Bool)"
            << std::endl;
      }
    }

    out   << "(define-fun |$floor| ((x Real)) Real " << std::endl
          << "   (to_real (to_int x)))             " << std::endl
          <<                                            std::endl;

    auto defRemainderInTermsOfQuotient = [&](auto kind, auto definition) {
      out << "(declare-fun |$quotient_"  << kind << "0| (Int) Int)         " << std::endl
          << "(declare-fun |$remainder_" << kind << "0| (Int) Int)         " << std::endl
          <<                                                                    std::endl
          << "(define-fun |$quotient_" << kind << "| ((m Int) (n Int)) Int " << std::endl
          << "   (ite (= n 0)                                              " << std::endl
          << "     (|$quotient_" << kind << "0| m)                         " << std::endl
          << definition 
          << "   )"                                                          << std::endl
          << ")"                                                             << std::endl
          <<                                                                    std::endl
          << "(define-fun |$remainder_" << kind << "| ((m Int) (n Int)) Int" << std::endl
          << "   (ite (= n 0)                                              " << std::endl
          << "    (|$remainder_" << kind << "0| m)                         " << std::endl
          << "    (- m (* n (|$quotient_" << kind << "| m n)))))           " << std::endl;
    };

    defRemainderInTermsOfQuotient("f",
           // definition: floor( m/n)
           //           = -ceil(-m/n)
           //
           // smtlib standard for div:
           // Regardless of sign of m, 
           // when n is positive, (div m n) is the floor of the rational number m/n;
           // when n is negative, (div m n) is the ceiling of m/n.
           "    (ite (> n 0)                            \n"
           //       n > 0 => div(m,n) = floor(m/n)
           "        (div m n)                           \n"
           //       n < 0 =>  div(-m,n) =  ceil(-m/n)
           //             => -div(-m,n) = -ceil(-m/n)
           //             => -div(-m,n) =   floor(m/n)
           "        (-(div (- m) n))                      \n"
           "    )                                       \n"
           );


    defRemainderInTermsOfQuotient("t",
           // definition: truncate(m/n)
           //          = if (m/n > 0) floor(m/n)
           //            else         ceil(m/n)
           // smtlib standard for div:
           // Regardless of sign of m, 
           // when n is positive, (div m n) is the floor of the rational number m/n;
           // when n is negative, (div m n) is the ceiling of m/n.
           "    (ite (> n 0)                             \n"
           "       (ite (> m 0)                             \n"
           //            m/n > 0 => we need floor(m/n)
           //                    => n is potitive
           //                    => div(m, n) = floor(m/n)
           "            (div m n)                           \n"
           //            m/n <= 0 => we need ceiling(m/n)
           //                     => -n is negative
           //                     => div(-m,-n) = floor(-m/-n)
           "            (div (- m) (- n))                   \n"
           "       )                                        \n"
           "       (ite (> m 0)                             \n"
           //            m/n < 0 => we need ceiling(m/n)
           //                    => n is negative
           //                    => div(m, n) = ceil(m/n)
           "            (div m n)                           \n"
           //            m/n > 0 => we need floor(m/n)
           //                    => -n is positive
           //                    => div(-m, -n) = floor(-m / -n)
           "            (div (- m) (- n))                   \n"
           "       )                                        \n"
           "    )                                           \n");


  }

  static void outputVar(std::ostream& out, unsigned var)
  { out << "x" << var; }


#define INTERPRETATION_BY_TRANSLATION                                                     \
           Theory::INT_QUOTIENT_T:                                                        \
      case Theory::INT_QUOTIENT_F:                                                        \
      case Theory::REAL_FLOOR:                                                            \
      case Theory::RAT_FLOOR:                                                             \
      case Theory::INT_REMAINDER_T:                                                       \
      case Theory::INT_REMAINDER_F


#define ALL_NUM(SUFFIX)                                                                   \
           Theory::INT_ ## SUFFIX:                                                        \
      case Theory::RAT_ ## SUFFIX:                                                        \
      case Theory::REAL_ ## SUFFIX


#define UNSUPPORTED_INTERPRETATIONS                                                       \
           Theory::RAT_IS_RAT:                                                            \
      case Theory::RAT_IS_REAL:                                                           \
      case Theory::REAL_IS_RAT:                                                           \
      case Theory::REAL_IS_REAL:                                                          \
      case Theory::INT_DIVIDES:                                                           \
      case Theory::INT_CEILING:                                                           \
      case Theory::INT_TRUNCATE:                                                          \
      case Theory::INT_ROUND:                                                             \
      case Theory::RAT_QUOTIENT:                                                          \
      case Theory::RAT_QUOTIENT_E:                                                        \
      case Theory::RAT_QUOTIENT_T:                                                        \
      case Theory::RAT_QUOTIENT_F:                                                        \
      case Theory::RAT_REMAINDER_E:                                                       \
      case Theory::RAT_REMAINDER_T:                                                       \
      case Theory::RAT_REMAINDER_F:                                                       \
      case Theory::RAT_CEILING:                                                           \
      case Theory::RAT_TRUNCATE:                                                          \
      case Theory::RAT_ROUND:                                                             \
      case Theory::REAL_QUOTIENT_E:                                                       \
      case Theory::REAL_QUOTIENT_T:                                                       \
      case Theory::REAL_QUOTIENT_F:                                                       \
      case Theory::REAL_REMAINDER_E:                                                      \
      case Theory::REAL_REMAINDER_T:                                                      \
      case Theory::REAL_REMAINDER_F:                                                      \
      case Theory::REAL_CEILING:                                                          \
      case Theory::REAL_TRUNCATE:                                                         \
      case Theory::REAL_ROUND:                                                            \
      case Theory::RAT_TO_RAT:                                                            \
      case Theory::REAL_TO_RAT:                                                           \
      case Theory::INT_IS_RAT:                                                            \
      case Theory::INT_IS_REAL:                                                           \
      case Theory::INT_TO_RAT

  static void outputInterpretationName(std::ostream& out, Theory::Interpretation itp) 
  {

    switch (itp) {
      case ALL_NUM(IS_INT):        out << "is_int";  return;
      case ALL_NUM(TO_REAL):       out << "to_real"; return;
      case ALL_NUM(TO_INT):        out << "to_int";  return;
      case ALL_NUM(GREATER):       out << ">";       return;
      case ALL_NUM(GREATER_EQUAL): out << ">=";      return;
      case ALL_NUM(LESS):          out << "<";       return;
      case ALL_NUM(LESS_EQUAL):    out << "<=";      return;
      case ALL_NUM(PLUS):          out << "+";       return;
      case ALL_NUM(MINUS):         out << "-";       return;
      case ALL_NUM(UNARY_MINUS):   out << "-";       return;
      case ALL_NUM(MULTIPLY):      out << "*";       return;
      case Theory::RAT_FLOOR:      out << "|$floor|";       return;
      case Theory::REAL_FLOOR:     out << "|$floor|";       return;

      case Theory::EQUAL: out << "="; return;
      case UNSUPPORTED_INTERPRETATIONS:
         throw UserErrorException("divides function ", itp, " does not exist in SMT2");

      case Theory::INT_SUCCESSOR: out << "+ 1"; return;
      case Theory::INT_ABS: out << "abs"; return;

      case Theory::INT_QUOTIENT_E: out << "div"; return;
      case Theory::INT_REMAINDER_E: out << "mod"; return;

      case Theory::INT_QUOTIENT_T:  out << "|$quotient_t|"; return;
      case Theory::INT_REMAINDER_T: out << "|$remainder_t|"; return;

      case Theory::INT_QUOTIENT_F:  out << "|$quotient_f|"; return;
      case Theory::INT_REMAINDER_F: out << "|$remainder_f|"; return;

      case Theory::INT_FLOOR: out << "to_int"; return;

      case Theory::REAL_QUOTIENT: out << "/"; return;

      // array functions
      case Theory::ARRAY_SELECT: out << "select"; return;
      case Theory::ARRAY_STORE: out << "store"; return;

      case Theory::INVALID_INTERPRETATION: {ASSERTION_VIOLATION}
    }
    ASSERTION_VIOLATION


  }


  static void outputPredicateName(std::ostream& out, unsigned p) 
  {
    if (theory->isInterpretedPredicate(p)) {
      outputInterpretationName(out, theory->interpretPredicate(p));
    } else {
      outputQuoted(out, env.signature->predicateName(p));
    }
  }

  static void outputQuoted(std::ostream& out, std::string const& name) 
  {
    if (   name == "exp"
        || name == "log"
        || name == "cos"
        || name == "sin"
        || name == "tan"
        || name == "sqrt"
        || name == "const"
        ) {
        out << "_" << name;
    } else if ( name[0] == '\'' || name[0] == '$') {
      // add one more level of quoting
      out << '|' << name << "|";
    } else  {
      out << name;
    }
  }

  static void outputFunctionName(std::ostream& out, unsigned f) 
  {
    if (theory->isInterpretedFunction(f)) {
      outputInterpretationName(out, theory->interpretFunction(f));
    } else if (theory->isInterpretedConstant(f)) {
      IntegerConstantType i;
      RealConstantType r;
      if (theory->tryInterpretConstant(f, i)) {
        if (i < IntegerConstantType(0)) {
          out << "(- " << i.abs() << ")";
        } else {
          out << i;
        }

      } else if (theory->tryInterpretConstant(f, r)) {
        if (r < RealConstantType(0)) {
          out << "(-";
        }
        if (r.denominator() != IntegerConstantType(1)) {
          out << r.numerator().abs() << ".0";
        } else {
          out << "(/ " << r.numerator().abs() << ".0 " << r.denominator() << ".0)";
        }
        if (r < RealConstantType(0)) {
          out << ")";
        }

      } else {
        throw UserErrorException("only reals and integers are allowed in smt2");
      }

    } else if (env.signature->isFoolConstantSymbol(true, f)) {
      out << "true";

    } else if (env.signature->isFoolConstantSymbol(false, f)) {
      out << "false";

    } else {
      auto& name = env.signature->functionName(f);
      outputQuoted(out, name);
    }
  }


#define DIRECT_SMT2_INTERPRETATION                                                        \
            Theory::EQUAL:                                                                \
      case ALL_NUM(IS_INT):                                                               \
      case ALL_NUM(TO_REAL):                                                              \
      case ALL_NUM(TO_INT):                                                               \
      case ALL_NUM(GREATER):                                                              \
      case ALL_NUM(GREATER_EQUAL):                                                        \
      case ALL_NUM(LESS):                                                                 \
      case ALL_NUM(LESS_EQUAL):                                                           \
      case ALL_NUM(PLUS):                                                                 \
      case ALL_NUM(MINUS):                                                                \
      case ALL_NUM(UNARY_MINUS):                                                          \
      case ALL_NUM(MULTIPLY):                                                             \
      case Theory::INT_SUCCESSOR:                                                         \
      case Theory::INT_ABS:                                                               \
      case Theory::INT_QUOTIENT_E:                                                        \
      case Theory::INT_REMAINDER_E:                                                       \
      case Theory::INT_FLOOR:                                                             \
      case Theory::REAL_QUOTIENT:                                                         \
      case Theory::ARRAY_SELECT:                                                          \
      case Theory::ARRAY_STORE


  bool isInterpretedByTranslation(Term* t)
  {
    if (theory->isInterpretedFunction(t)) {
      switch (theory->interpretFunction(t)) {
        case INTERPRETATION_BY_TRANSLATION:
          return true;
        default:
          return false;
      }
    } else {
      return false;
    }
  }

  static void outputAppl(std::ostream& out, Term* t)
  {

    if (t->isSpecial()) {
      auto f = t->specialFunctor();
      const Term::SpecialTermData* sd = t->getSpecialData();
      switch(f) {
        case SpecialFunctor::FORMULA: outputFormula(out, sd->getFormula()); return;
        case SpecialFunctor::LET: {
          auto binding = sd->getLetBinding();
          if (binding->connective() != Connective::LITERAL)
            throw UserErrorException("bindings with variables are not supperted in smt2 proofcheck");

          out << "(let ((";
          outputFormula(out, binding);
          out << "))";

          ASS_EQ(t->numTermArguments(), 1)
          outputTerm(out, t->termArg(0));
          out << ")";
          return;
        }

        case SpecialFunctor::ITE: {
          out << "(ite ";
          outputFormula(out, sd->getITECondition());
          ASS_EQ(t->numTermArguments(), 2)
          outputTerm(out, t->termArg(0));
          outputTerm(out, t->termArg(1));
          out << ")";
          return;
        }

        case SpecialFunctor::LAMBDA:
            throw UserErrorException("lambdas are not supperted in smt2 proofcheck");

        case SpecialFunctor::MATCH:
            throw UserErrorException("&match are not supperted in smt2 proofcheck");
      }


    } else {
      // if (isInterpretedByTranslation(t)) {
      //   outputTranslation(out, t);
      //
      // } else {

        if (t->numTermArguments() != 0) {
          out << "(";
        }
        if (t->isLiteral()) {
          outputPredicateName(out, t->functor());
        } else {
          if (theory->isInterpretedFunction(t->functor(), Theory::INT_DIVIDES) 
              && IntTraits::isNumeral(t->termArg(0) )) {
            out << "( (_ divisible " << *IntTraits::tryNumeral(t->termArg(0)) << ") " << t->termArg(1) << " )";
          } else {
            outputFunctionName(out, t->functor());
          }
        }

        for (unsigned i = 0; i < t->numTermArguments(); i++) {
          out << " ";
          outputTerm(out, t->termArg(i));
        }
        if (t->numTermArguments() != 0) {
          out << ")";
        }
      // }
    }
  }


  static void outputLiteral(std::ostream& out, Literal* lit) 
  {
    if (lit->isNegative()) {
      out << "(not ";
    }
    outputAppl(out, lit);
    if (lit->isNegative()) {
      out << ")";
    }
  }
  static void outputTerm(std::ostream& out, TermList t) 
  {
    if (t.isVar()) {
      outputVar(out, t.var());
    } else {
      outputAppl(out, t.term());
    }
  }

  static void outputFormula(std::ostream& out, Formula* f)
  {
    auto outputBin = [&](const char* name) {
      out << "(" << name << " ";
      outputFormula(out, f->left());
      outputFormula(out, f->right());
      out << ")";
    };
    auto outputCon = [&](const char* name) {
      const FormulaList* fs = f->args();
      ASS (FormulaList::length(fs) >= 2);

      out << "(" << name;
      
      while (FormulaList::isNonEmpty(fs)) {
        out << " ";
        outputFormula(out, fs->head());
        fs = fs->tail();
      }
      out << ")";
    };
    auto outputQuant = [&](const char* name) {
      out << "("<< name << "(";
      VSList::Iterator vs(f->vars());
      while (vs.hasNext()) {
        auto [var, sort] = vs.next();
        out << "(";
        outputVar(out, var);
        out << " ";
        outputSort(out, sort);
        out << ")";
      }
      out << ")";
      outputFormula(out, f->qarg());
      out << ")";
    };
    switch (f->connective()) {
      case NAME:
        out << static_cast<const NamedFormula*>(f)->name();
        return;

      case LITERAL:
        outputLiteral(out, f->literal());
        return;

      case NOT:
        out << "(not ";
        outputFormula(out, f->uarg());
        out  << ")";
        return;

      case AND: outputCon("and"); return;
      case OR : outputCon("or" ); return;
      case IFF: outputBin("=" ); return;
      case XOR: outputBin("distinct"); return;
      case IMP: outputBin("=>"); return;
      case FORALL: outputQuant("forall"); return;
      case EXISTS: outputQuant("exists"); return;
      case BOOL_TERM: outputTerm(out, f->getBooleanTerm()); return;
      case TRUE: out << "true"; return;
      case FALSE: out << "false"; return;
      case NOCONN: ASSERTION_VIOLATION_REP(*f);
    }
    ASSERTION_VIOLATION_REP(*f)
  }

  static void outputSort(std::ostream& out, TermList sort)
  { 
    ASS(sort.isTerm())
    if (AtomicSort::intSort() == sort) {
      out << "Int"; 
    } else if (AtomicSort::rationalSort() == sort) {
      throw UserErrorException("smtlib2 does not have rational sorts");
    } else if (AtomicSort::realSort() == sort) {
      out << "Real";
    } else if (AtomicSort::boolSort() == sort) {
      out << "Bool";
    } else {
      auto term = sort.term();
      if (term->arity() == 0) {
        outputQuoted(out, env.signature->typeConName(term->functor()));

      } else {
        out << "(";
        if (sort.isArraySort()){
          out << "Array";
        } else {
          outputQuoted(out, env.signature->typeConName(term->functor()));
        }
        for (unsigned a = 0; a < term->arity(); a++) {
           out << " ";
           outputSort(out, *term->nthArgument(a));
        }
        out << ")";
      }
    }
  }

  static void output(std::ostream& out, Unit* unit)
  {
    using Sort = TermList;
    DHMap<unsigned, Sort, FnvHash, IdentityHash> vars;
    SortHelper::collectVariableSorts(unit, vars);
    decltype(vars)::Iterator iter(vars);
    if (vars.size() != 0) {
      out << "(forall (";
      while (iter.hasNext()) {
        unsigned var;
        Sort sort;
        iter.next(var, sort);
        out << "(";
        outputVar(out, var);
        out << " ";
        outputSort(out, sort);
        out << ")";
      }
      out << ")";
    }

    if (unit->isClause()) {
      Clause* cl=static_cast<Clause*>(unit);
      out << "(or false " << std::endl;
      for(auto lit : iterTraits(cl->iterLits())) {
        out << "  ";
        outputLiteral(out, lit);
        out << std::endl;
      }
      out << "  )";
    } else {
      outputFormula(out, static_cast<FormulaUnit*>(unit)->formula());
    }


    if (vars.size() != 0) {
      out << ")";
    }
  }

  void printStep(Unit* concl) override
  {
    auto prems = iterTraits(concl->getParents());
 
    outputSymbolDeclarations(out);
    out        << std::endl;
    out        << std::endl;

    for (auto prem : prems) {
      out << ";- unit id: " << prem->number() << std::endl;
      out << "(assert ";
      output(out, prem);
      out << ")" << std::endl;
      out        << std::endl;
    }

    out << std::endl;
    out << ";- rule: " << ruleName(concl->inference().rule()) << std::endl;
    out << std::endl;
    out << ";- unit id: " << concl->number() << std::endl;
    out << "(assert (not ";
    output(out, concl);
    out  << "))" << std::endl;

    out << "(check-sat)" << std::endl;
    out << "%#" << std::endl;
  }


  bool hideProofStep(InferenceRule rule) override
  {
    switch(rule) {
    case InferenceRule::INPUT:
    case InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    case InferenceRule::INEQUALITY_SPLITTING:
    case InferenceRule::SKOLEMIZE:
    case InferenceRule::SKOLEM_SYMBOL_INTRODUCTION:
    case InferenceRule::EQUALITY_PROXY_REPLACEMENT:
    case InferenceRule::EQUALITY_PROXY_DEFINITION:
    case InferenceRule::EQUALITY_PROXY_AXIOM:
    case InferenceRule::NEGATED_CONJECTURE:
    case InferenceRule::RECTIFY:
    case InferenceRule::FLATTEN:
    case InferenceRule::ENNF:
    case InferenceRule::NNF:
    case InferenceRule::CLAUSIFY:
    case InferenceRule::AVATAR_DEFINITION:
    case InferenceRule::AVATAR_COMPONENT:
    case InferenceRule::AVATAR_REFUTATION:
    case InferenceRule::AVATAR_SPLIT_CLAUSE:
    case InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
    case InferenceRule::FOOL_LET_DEFINITION:
    case InferenceRule::FOOL_ITE_DEFINITION:
    case InferenceRule::FOOL_ELIMINATION:
    case InferenceRule::BOOLEAN_TERM_ENCODING:
    case InferenceRule::PREDICATE_DEFINITION:
      return true;
    default:
      return false;
    }
  }

  void print() override
  {
    AbstractProofPrinter::print();
    out << "%#\n";
  }
};

struct InferenceStore::SMTCheckPrinter
: public InferenceStore::AbstractProofPrinter
{
  SMTCheckPrinter(ostream& out, InferenceStore* is)
  : AbstractProofPrinter(out, is) {}

  void print() override
  {
    SMTCheck::outputSignature(out);
    AbstractProofPrinter::print();
  }

  void printStep(Unit* u) override
  {
    SMTCheck::outputStep(out, u);
  }
};

InferenceStore::AbstractProofPrinter* InferenceStore::createProofPrinter(std::ostream& out)
{
  switch(env.options->proof()) {
  case Options::Proof::ON:
    return new ProofPrinter(out, this);
  case Options::Proof::SMT2_PROOFCHECK:
    return new Smt2ProofCheckPrinter(out, this);
  case Options::Proof::PROOFCHECK:
    return new ProofCheckPrinter(out, this);
  case Options::Proof::TPTP:
    return new TPTPProofPrinter(out, this);
  case Options::Proof::PROPERTY:
    return new ProofPropertyPrinter(out,this);
  case Options::Proof::OFF:
    return 0;
  case Shell::Options::Proof::SMTCHECK:
    return new SMTCheckPrinter(out, this);
  }
  ASSERTION_VIOLATION;
}

/**
 * Output a proof of refutation to out
 *
 *
 */
void InferenceStore::outputUnsatCore(std::ostream& out, Unit* refutation)
{
  out << "(" << endl;

  Stack<Unit*> todo;
  todo.push(refutation);
  Set<unsigned, FnvHash> visited;
  while(!todo.isEmpty()){

    Unit* u = todo.pop();
    visited.insert(u->number());

    if(u->inference().rule() ==  InferenceRule::INPUT){
      if(!u->isClause()){
        if(u->getFormula()->hasLabel()){
          std::string label =  u->getFormula()->getLabel();
          out << label << endl;
        }
        else{
          ASS(env.options->ignoreMissingInputsInUnsatCore() || u->getFormula()->hasLabel());
          if(!(env.options->ignoreMissingInputsInUnsatCore() || u->getFormula()->hasLabel())){
            cout << "ERROR: There is a problem with the unsat core. There is an input formula in the proof" <<  endl;
            cout << "that does not have a label. We expect all  input formulas to have labels as this  is what" << endl;
            cout << "smtcomp does. If you don't want this then use the ignore_missing_inputs_in_unsat_core option" << endl;
            cout << "The unlabelled  input formula is " << endl;
            cout << u->toString() << endl;
          }
        }
      }
      else{
        //Currently ignore clauses as they cannot come from SMT-LIB as input formulas
      }
    }
    else{
      UnitIterator parents = u->getParents();
      while(parents.hasNext()){
        Unit* parent = parents.next();
        if(!visited.contains(parent->number())){
          todo.push(parent);
        }
      }
    }
  }

  out << ")" << endl;
}



/**
 * Output a proof of refutation to out
 *
 *
 */
void InferenceStore::outputProof(std::ostream& out, Unit* refutation)
{
  AbstractProofPrinter* p = createProofPrinter(out);
  if (!p) {
    return;
  }
  ScopedPtr<AbstractProofPrinter> pp(p);
  pp->scheduleForPrinting(refutation);
  pp->print();
}

/**
 * Output a proof of units to out
 *
 */
void InferenceStore::outputProof(std::ostream& out, UnitList* units)
{
  AbstractProofPrinter* p = createProofPrinter(out);
  if (!p) {
    return;
  }
  ScopedPtr<AbstractProofPrinter> pp(p);
  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    pp->scheduleForPrinting(u);
  }
  pp->print();
}

InferenceStore* InferenceStore::instance()
{
  static ScopedPtr<InferenceStore> inst(new InferenceStore());

  return inst.ptr();
}

#undef ALL_NUM
}
