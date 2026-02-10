#ifndef __LEAN__PRINTER__
#define __LEAN__PRINTER__

#include <ostream>
#include <vector>
#include "Forwards.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Lib/Environment.hpp"

using namespace Kernel;
using SortMap = DHMap<unsigned, TermList>;

namespace Shell {
namespace LeanPrinter {

template <bool real>
struct SMTNumeral {
  const IntegerConstantType &constant;
};

struct DoSubst {
  Substitution const &subst;
  DoSubst(Substitution const &subst) : subst(subst) {}
  Literal *operator()(Literal *l) { return SubstHelper::apply(l, subst); }
  TermList operator()(unsigned int var) { return subst.apply(var); }
};


template <bool real>
std::ostream &operator<<(std::ostream &out, SMTNumeral<real> num)
{
  if (num.constant.sign() == Sign::Neg)
    return out << "(- " << num.constant.abs() << (real ? " : ℝ" : "") << ")";
  else
    return out << (real ? "(" : "") << num.constant << (real ? " : ℝ)" : "");
}

struct Escaped {
  const char *name;
};

std::ostream &operator<<(std::ostream &out, Escaped escaped);

struct FunctionName {
  FunctionName(Signature::Symbol *symbol) : symbol(symbol) {}
  FunctionName(Term *t) : FunctionName(env.signature->getFunction(t->functor())) {}
  Signature::Symbol *symbol;
};

std::ostream &operator<<(std::ostream &out, FunctionName name);

struct PredicateName {
  PredicateName(Signature::Symbol *symbol) : symbol(symbol) {}
  PredicateName(Literal *l) : PredicateName(env.signature->getPredicate(l->functor())) {}
  Signature::Symbol *symbol;
};

std::ostream &operator<<(std::ostream &out, PredicateName name);

bool isInfix(const Signature::InterpretedSymbol *sym);

struct Blank {};
std::ostream &operator<<(std::ostream &out, Blank);
struct Inhabit {};
std::ostream &operator<<(std::ostream &out, Inhabit);

template <typename Prefix = Blank>
struct SortName {
  SortName(unsigned functor) : functor(functor) {}
  SortName(AtomicSort *s) : functor(s->functor()) {}
  unsigned functor;
};

template <typename Prefix>
std::ostream &operator<<(std::ostream &out, SortName<Prefix> name)
{
  Prefix prefix;
  switch (name.functor) {
    case Signature::DEFAULT_SORT_CON:
      return out << prefix << "ι";
    case Signature::BOOL_SRT_CON:
      return out << prefix << "Bool";
    case Signature::INTEGER_SRT_CON:
      return out << prefix << "ℤ";
    case Signature::RATIONAL_SRT_CON:
    case Signature::REAL_SRT_CON:
      return out << prefix << "ℝ";
  }
  return out << "«" << prefix << env.signature->getTypeCon(name.functor)->name() << "»";
}

struct Args {
  TermList *start;
  SortMap &conclSorts;
  SortMap &otherSorts;
};

inline bool isSkolemTerm(Term *term)
{
  unsigned int fun = term->functor();
  if (fun >= env.signature->functions()) {
    return false;
  }
  Signature::Symbol *sym = env.signature->getFunction(fun);
  return sym->skolem();
}

void printArgs(std::ostream &out, Args args, bool variablesAsPattern = false, bool recurse = false);

std::ostream &operator<<(std::ostream &out, Args args);

struct Lit {
  Literal *literal;
  SortMap &conclSorts;
  SortMap &otherSorts;
};

void printLiteral(std::ostream &out, Lit lit, bool variablesAsPattern = false);

std::ostream &operator<<(std::ostream &out, Lit lit);

struct Sort {
  TermList sort;
};

std::ostream &operator<<(std::ostream &out, Sort print);

void outputSortsWithQuantor(std::ostream &out, SortMap &sorts, std::string quantor = "∀", std::string end = ", ");

void printFormula(std::ostream &out, Formula *f, SortMap &conclSorts, SortMap &otherSorts, bool variablesAsPattern = false);

struct Identity {
  Literal *operator()(Literal *l) { return l; }
  TermList operator()(unsigned int var) { return TermList::var(var); }
};

template <typename Transform = Identity>
void outputVariablesFromStack(std::ostream &out, Kernel::VStack vars, SortMap &conclSorts, SortMap &varSorts, Transform trans = Transform{}, int sort = 1, bool printSorts = false)
{
  if (sort!=0) {
    vars.sort();
  }
  if(sort==-1){
    std::reverse(vars.begin(), vars.end());
  }
  for (unsigned x =0; x < vars.size(); x++) {
    unsigned var = vars[x];
    TermList translatedTerm = trans(var);
    SortMap newVarSorts;
    if (translatedTerm.isVar()) {
      newVarSorts.insert(translatedTerm.var(), varSorts.get(var));
    }
    else if (translatedTerm.isTerm()) {
      SortHelper::collectVariableSorts(translatedTerm.term(), newVarSorts);
    }
    else {
      ASSERTION_VIOLATION
    }
    if (printSorts) {
      out << "(";
    }
    printArgs(out, Args{&translatedTerm, conclSorts, newVarSorts}, false, true);
    if(x != vars.size() -1){
      out << " ";
    }
    if (printSorts) {
      if (translatedTerm.isVar()) {
        out << ": " << Sort{newVarSorts.get(translatedTerm.var())};
      }
      else {
        ASSERTION_VIOLATION
      }
      out << ") ";
    }
  }
}

template <typename itertype, typename Transform = Identity>
void outputVariablesGen(std::ostream &out, itertype &iterator, SortMap &conclSorts, SortMap &varSorts, Transform trans = Transform{}, int sort = true, bool printSorts = false)
{
  Kernel::VStack vars;
  while(iterator.hasNext()) {
    vars.push(iterator.next());
  }
  outputVariablesFromStack<Transform>(out, vars, conclSorts, varSorts, trans, sort, printSorts);
}

template <typename Transform = Identity>
void outputVariables(std::ostream &out, VirtualIterator<unsigned int> &iterator , SortMap &conclSorts, SortMap &varSorts, Transform trans = Transform{}, int sort = true, bool printSorts = false)
{
  outputVariablesGen<VirtualIterator<unsigned int>, Transform>(out, iterator, conclSorts, varSorts, trans, sort, printSorts);
}

template <typename Transform = Identity>
void outputVariables(std::ostream &out, std::vector<unsigned int>* variables, SortMap &conclSorts, SortMap &varSorts, Transform trans = Transform{}, int sort = true, bool printSorts = false)
{
  Kernel::VStack vars;
  for (unsigned int x : *variables) {
    vars.push(x);
  }
  outputVariablesFromStack(out, vars, conclSorts, varSorts, trans, sort, printSorts);
}

} // namespace LeanPrinter
} // namespace Shell

#endif // __LEAN__PRINTER__