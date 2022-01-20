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
 * @file Z3Interfacing.cpp
 * Implements class Z3Interfacing
 */

#if VZ3
#define UNIMPLEMENTED ASSERTION_VIOLATION

#include "Forwards.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"

#include "Lib/Environment.hpp"
#include "Lib/System.hpp"

#include "Kernel/NumTraits.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TermList.hpp"
#include "Lib/Coproduct.hpp"

#include "Shell/UIHelper.hpp"
#include "Indexing/TermSharing.hpp"
#include "Z3Interfacing.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)
#define TRACE_Z3 0
namespace Lib {
using SortId = TermList;

template<>
struct BottomUpChildIter<z3::expr>
{
  unsigned _idx;
  z3::expr _self;

  /** constructs an iterator over the children of the current node */
  BottomUpChildIter(z3::expr a) : _idx(0), _self(a) {}

  /** returns the node this iterator was constructed with */
  z3::expr self() { return _self; }

  /** returns the next child of the node this this object was constructed with */
  z3::expr next() { return _self.arg(_idx++); }

  /** returns the next child of the current node in the structure to be traversed */
  bool hasNext() { return _self.is_app() && _idx < _self.num_args(); }

  /** returns how many children this node has */
  unsigned nChildren() { return _self.is_app() ? _self.num_args() : 0; }
};

} // namespace Lib

namespace SAT
{

using namespace Shell;
using namespace Lib;

//using namespace z3;

Z3Interfacing::Z3Interfacing(const Shell::Options& opts, SAT2FO& s2f, bool unsatCoresForAssumptions, vstring const& exportSmtlib):
  Z3Interfacing(s2f, opts.showZ3(), /* unsatCoresForAssumptions = */ unsatCoresForAssumptions, exportSmtlib)
{ }

const char* errToString(Z3_error_code code)
{
  switch (code) {
    case Z3_OK: return "Z3_OK";
    case Z3_SORT_ERROR: return "Z3_SORT_ERROR";
    case Z3_IOB: return "Z3_IOB";
    case Z3_INVALID_ARG: return "Z3_INVALID_ARG";
    case Z3_PARSER_ERROR: return "Z3_PARSER_ERROR";
    case Z3_NO_PARSER: return "Z3_NO_PARSER";
    case Z3_INVALID_PATTERN: return "Z3_INVALID_PATTERN";
    case Z3_MEMOUT_FAIL: return "Z3_MEMOUT_FAIL";
    case Z3_FILE_ACCESS_ERROR: return "Z3_FILE_ACCESS_ERROR";
    case Z3_INTERNAL_FATAL: return "Z3_INTERNAL_FATAL";
    case Z3_INVALID_USAGE: return "Z3_INVALID_USAGE";
    case Z3_DEC_REF_ERROR: return "Z3_DEC_REF_ERROR";
    case Z3_EXCEPTION: return "Z3_EXCEPTION";
    default: ASSERTION_VIOLATION; return "UNKNOWN ERROR";
  }
}

void handleZ3Error(Z3_context ctxt, Z3_error_code code)
{
  DEBUG(errToString(code))
  throw z3::exception(errToString(code));
}

#define STATEMENTS_TO_EXPRESSION(...) [&]() { __VA_ARGS__; return 0; }()

Z3Interfacing::Z3Interfacing(SAT2FO& s2f, bool showZ3, bool unsatCoresForAssumptions, vstring const& exportSmtlib):
  _hasSeenArrays(false),
  _varCnt(0),
  _sat2fo(s2f),
  _status(SATISFIABLE),
  _config(),
  _context(_config),
  _solver(_context),
  _model((STATEMENTS_TO_EXPRESSION(
            BYPASSING_ALLOCATOR;
            _solver.check();
          ),
         _solver.get_model())),
  _assumptions(),
  _showZ3(showZ3),
  _unsatCore(unsatCoresForAssumptions),
  _out()
{
  CALL("Z3Interfacing::Z3Interfacing");
  BYPASSING_ALLOCATOR
  _out = exportSmtlib == "" ? Option<std::ofstream>()
                            : Option<std::ofstream>(std::ofstream(exportSmtlib.c_str())) ;
  if (_out.isSome() && _out.unwrap().fail()) {
    throw UserErrorException("Failed to open file: ", exportSmtlib);
  }

  _solver.reset();
  outputln("(check-sat)");
  outputln("(get-model)");
  outputln("(reset)");

  z3::params p(_context);
  auto setOption = [&](auto k, auto v){
    p.set(k,v);
    outputln(";- z3 parameter: ", k, "=", v);
  };
  setOption("rewriter.expand_store_eq", true);
  setOption("model.compact", true);
  if (_unsatCore) {
    setOption(":unsat-core", true);
  }
  // Z3_set_error_handler(_context, handleZ3Error); // MS: a handled error only reveals Z3_error_code, a propragated z3::exception is typically more informative

#if TRACE_Z3
  setOption("trace", "true");
  Z3_enable_trace("memory");
  Z3_enable_trace("datatype");
#endif // TRACE_Z3

  _solver.set(p);
  // TODO some way to serizalize the params for z3 to an smtlib file
}

char const* Z3Interfacing::z3_full_version()
{
  CALL("Z3Interfacing::z3_version");
  return Z3_get_full_version();
}

unsigned Z3Interfacing::newVar()
{
  CALL("Z3Interfacing::newVar");

  ++_varCnt;

  // to make sure all the literals we will ask about later have allocated counterparts internally
  getRepresentation(SATLiteral(_varCnt,1));

  return _varCnt;
}

void Z3Interfacing::addClause(SATClause* cl)
{
  CALL("Z3Interfacing::addClause");
  BYPASSING_ALLOCATOR;
  ASS(cl);

  // store to later generate the refutation
  PrimitiveProofRecordingSATSolver::addClause(cl);

  auto z3clause = getRepresentation(cl);

  if(_showZ3){
    env.beginOutput();
    env.out() << "[Z3] add (clause): " << z3clause.expr << std::endl;
    env.endOutput();
  }

  auto add = [&](auto x) {
    outputln("(assert ", x, ")");
    _solver.add(x);
  };

  for (auto def : z3clause.defs)  {
    DEBUG("adding def: ", def)
    add(def);
  }

  add(z3clause.expr);
  DEBUG("adding expr: ", z3clause.expr)
}

void Z3Interfacing::retractAllAssumptions()
{
  _assumptionLookup.clear();
  _assumptions.truncate(0);
}

void Z3Interfacing::addAssumption(SATLiteral lit)
{
  CALL("Z3Interfacing::addAssumption");

  auto pushAssumption = [&](SATLiteral lit) -> z3::expr
  {
    auto repr = getRepresentation(lit);
    for (auto& def : repr.defs)
      _assumptions.push(def);

    _assumptions.push(repr.expr);
    return repr.expr;
  };

  if (_unsatCore) {
    _assumptionLookup.getOrInit(lit, [&]() { return pushAssumption(lit); });
  } else {
    pushAssumption(lit);
  }
}

Z3Interfacing::Representation Z3Interfacing::getRepresentation(SATClause* cl)
{

  z3::expr z3clause = _context.bool_val(false);

  Stack<z3::expr> defs;

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++){
    SATLiteral l = (*cl)[i];
    auto repr = getRepresentation(l);

    defs.loadFromIterator(repr.defs.iterFifo());

    z3clause = z3clause || repr.expr;
  }

  return Representation(std::move(z3clause), std::move(defs));
}

SATSolver::Status Z3Interfacing::solve()
{
  CALL("Z3Interfacing::solve()");
  BYPASSING_ALLOCATOR;
  DEBUG("assumptions: ", _assumptions);

  output("(check-sat-assuming (");
  for (auto const& a : _assumptions) {
    outputln(" ", a);
  }
  outputln(" ))");

  /* The purpose of this class is to conditionally disable variable elimination inside Z3's _solver.check,
   * which results in some literals not being evaluated to either true and false, that we need for AVATAR.
   * Why a class? To be able to rely on RAII for the call to pop() (via the destructor) and thus not forget about it.
   * Why conditional? Because push/pop slightly decreases z3's performance and so we want to do it only in
   * the cases where the problem has been observed - namely, when arrays are involved.
  */
  class ScopedPushAndPop {
    z3::solver& _s;
    bool _dpp;
  public:
    ScopedPushAndPop(z3::solver& s, bool doPushPop) : _s(s), _dpp(doPushPop) { if (_dpp) {_s.push();} }
    ~ScopedPushAndPop() { if (_dpp) {_s.pop();} }
  } _maybePushAndPop(_solver,_hasSeenArrays);

  z3::check_result result = _solver.check(_assumptions.size(), _assumptions.begin());

  if(_showZ3){
    env.beginOutput();
    env.out() << "[Z3] solve result: " << result << std::endl;
    env.endOutput();
  }

  if (_unsatCore) {
    auto core = _solver.unsat_core();
    outputln("(get-unsat-core)");
    for (auto phi : core) {
      _assumptionLookup
             .tryGet(phi)
             .andThen([this](SATLiteral l)
                 { _failedAssumptionBuffer.push(l); });
    }
  }

  switch (result) {
    case z3::check_result::unsat:
      _status = UNSATISFIABLE;
      break;
    case z3::check_result::sat:
      _status = SATISFIABLE;
      _model = _solver.get_model();
      outputln("(get-model)");
      break;
    case z3::check_result::unknown:
      _status = UNKNOWN;
      break;
    default: ASSERTION_VIOLATION;
  }
  
  return _status;
}

SATSolver::Status Z3Interfacing::solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool onlyProperSubusets)
{
  CALL("Z3Interfacing::solveUnderAssumptions");

  if (!_unsatCore) {
    return SATSolverWithAssumptions::solveUnderAssumptions(assumps,conflictCountLimit,onlyProperSubusets);
  }

  ASS(!hasAssumptions());

  for (auto a: assumps) {
    addAssumption(a);
  }
  auto result = solve();
  retractAllAssumptions();
  return result;
}

SATSolver::VarAssignment Z3Interfacing::getAssignment(unsigned var)
{
  CALL("Z3Interfacing::getAssignment");
  BYPASSING_ALLOCATOR;

  ASS_EQ(_status,SATISFIABLE);
  bool named = isNamedExpr(var);
  z3::expr rep = named ? getNameExpr(var) : getRepresentation(SATLiteral(var,1)).expr;
  outputln("(get-value (", rep, "))");
  z3::expr assignment = _model.eval(rep, true /*model_completion*/);

  if(assignment.bool_value()==Z3_L_TRUE){
    return TRUE;
  } else if(assignment.bool_value()==Z3_L_FALSE){
    return FALSE;
  } else {
#if VDEBUG
    std::cout << rep << std::endl;
    ASSERTION_VIOLATION_REP(assignment);
#endif
    return NOT_KNOWN;
  }
}

OperatorType* operatorType(Z3Interfacing::FuncOrPredId f)
{
  return f.isPredicate
    ? env.signature->getPredicate(f.id)->predType()
    : env.signature->getFunction (f.id)->fnType();
}


Term* createTermOrPred(Z3Interfacing::FuncOrPredId f, unsigned arity, TermList* ts)
{
  return f.isPredicate
    ? Literal::create(f.id, arity, true, false, ts)
    : Term::create(f.id, arity, ts);
}

struct EvaluateInModel
{

  Z3Interfacing& self;
  using Copro = Coproduct<Term*, RationalConstantType, IntegerConstantType>;

  using Arg    = z3::expr;
  using Result = Option<Copro>;

  static Term* toTerm(Copro const& co, SortId sort) {
    return co.match(
            [&](Term* t)
            { return t; },

            [&](RationalConstantType c)
            {
              return sort == RealTraits::sort()
                ? theory->representConstant(RealConstantType(c))
                : theory->representConstant(c);
            },

            [&](IntegerConstantType c)
            { return theory->representConstant(c); }
            );
  }

  Result operator()(z3::expr expr, Result* evaluatedArgs)
  {
    CALL("EvaluateInModel::operator()")
    DEBUG("in: ", expr)
    auto intVal = [](z3::expr e) -> Option<int> {
      int val;
      return e.is_numeral_i(val)
        ? Option<int>(val)
        : Option<int>();
    };

    if (expr.is_int()) {
      return intVal(expr)
        .map([](int i) { return Copro(IntTraits::constantT(i)); });

    } else if(expr.is_real()) {
      auto toFrac = [&](int l, int r)  { return Copro(RatTraits::constant(l,r)); };

      auto nonFractional = intVal(expr).map([&](int i) { return toFrac(i,1); });
      if (nonFractional.isSome()) {
        return nonFractional;
      } else {
        auto num = intVal(expr.numerator());
        auto den = intVal(expr.denominator());
        if (num.isSome() && den.isSome()) {
          return Result(Copro(toFrac(num.unwrap(), den.unwrap())));
        } else {
          return Result();
        }
      }

    } else if (expr.is_app()) {
      auto f = expr.decl();
      auto vfunc = self._fromZ3.get(f);
      Stack<TermList> args(f.arity());
      for (unsigned i = 0; i < f.arity(); i++) {
        if (evaluatedArgs[i].isNone()) {
          // evaluation failed somewhere in a recursive call
          return Result();
        } else {
          auto argSort = operatorType(vfunc)->arg(i);
          auto t = TermList(toTerm(evaluatedArgs[i].unwrap(), argSort));
          args.push(t);
        }
      }
      return Result(Copro(createTermOrPred(vfunc, args.size(), args.begin())));

    } else {

      return Result();
    }
  }
};

Term* Z3Interfacing::evaluateInModel(Term* trm)
{
  CALL("evaluateInModel(Term*)")
  DEBUG("in: ", *trm)
  DEBUG("model: \n", _model)
  ASS(!trm->isLiteral());

  z3::expr rep = getRepresentation(trm).expr;
  output("(get-value (", rep, "))");
  z3::expr ev = _model.eval(rep,true); // true means "model_completion"
  SortId sort = SortHelper::getResultSort(trm);

  DEBUG("z3 expr: ", ev)
  auto result = evaluateBottomUp(ev, EvaluateInModel { *this })
    .map([&](EvaluateInModel::Copro co) {
        return co.match(
            [&](Term* t)
            { return t; },

            [&](RationalConstantType c)
            {
              return sort == RealTraits::sort()
                ? theory->representConstant(RealConstantType(c))
                : theory->representConstant(c);
            },

            [&](IntegerConstantType c)
            { return theory->representConstant(c); }
            );
      })
    .unwrapOrElse([](){ return nullptr; });
  DEBUG("vampire expr: ", ev)
  return result;

}

bool Z3Interfacing::isZeroImplied(unsigned var)
{
  CALL("Z3Interfacing::isZeroImplied");

  // Safe. TODO consider getting zero-implied
  return false;
}

void Z3Interfacing::collectZeroImplied(SATLiteralStack& acc)
{
  CALL("Z3Interfacing::collectZeroImplied");
  NOT_IMPLEMENTED;
}

SATClause* Z3Interfacing::getZeroImpliedCertificate(unsigned)
{
  CALL("Z3Interfacing::getZeroImpliedCertificate");
  NOT_IMPLEMENTED;

  return 0;
}

z3::sort Z3Interfacing::getz3sort(SortId s)
{
  CALL("Z3Interfacing::getz3sort");

  BYPASSING_ALLOCATOR;
  auto srt = _sorts.tryGet(s);
  if (srt.isSome()) {
    return srt.unwrap();
  } else {
    auto insert = [&](z3::sort x) { _sorts.insert(s, x); };
    // TODO what about built-in tuples?

    // Deal with known sorts differently
         if(s == AtomicSort::boolSort()) insert(_context.bool_sort());
    else if(s ==  IntTraits::sort()) insert( _context.int_sort());
    else if(s == RealTraits::sort()) insert(_context.real_sort());
    else if(s ==  RatTraits::sort()) insert(_context.real_sort()); // Drops notion of rationality
    // TODO: are we really allowed to do this ???                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^
    else if(s.isArraySort()) {
      _hasSeenArrays = true;

      z3::sort index_sort = getz3sort(SortHelper::getIndexSort(s));
      z3::sort value_sort = getz3sort(SortHelper::getInnerSort(s));

      insert(_context.array_sort(index_sort,value_sort));

    } else if (env.signature->isTermAlgebraSort(s)) {
      createTermAlgebra(*env.signature->getTermAlgebraOfSort(s));

    } else {
      auto sort = _context.uninterpreted_sort(_context.str_symbol(s.toString().c_str()));
      outputln("(declare-sort ", sort, " 0)");
      insert(sort);
    }
  }
  return _sorts.get(s);
}

template<class A>
vstring to_vstring(A const& a)
{
  vstringstream out;
  out << a;
  return out.str();
}

void Z3Interfacing::createTermAlgebra(TermAlgebra& start)
{
  CALL("createTermAlgebra(TermAlgebra&)")
  if (_createdTermAlgebras.contains(start.sort())) return;

  Stack<TermAlgebra*> tas;        // <- stack of term algebra sorts
  Map<SortId, unsigned> recSorts; // <- mapping term algeba -> index

  auto subsorts = start.subSorts();
  for (auto s : subsorts.iter()) {
    if (env.signature->isTermAlgebraSort(s)
        && !_createdTermAlgebras.contains(s)) {
      auto ta = env.signature->getTermAlgebraOfSort(s);
      auto idx = tas.size();
      tas.push(ta);
      recSorts.insert(s, idx);
    }
  }

  auto new_string_symobl = [&](vstring const& str)
  { return Z3_mk_string_symbol(_context, str.c_str()); };

  // create the data needed for Z3_mk_datatypes(...)
  Stack<Stack<Z3_constructor>> ctorss(tas.size());
  Stack<Z3_constructor_list> ctorss_z3(tas.size());
  Stack<Z3_symbol> sortNames(tas.size());
  // create the data needed to serialize the declare-datatypes to smtlib
  struct SerDtor { z3::symbol name; SortId sort; };
  struct SerCtor { z3::symbol name; Stack<SerDtor> dtors; };
  struct SerDtype { SortId name; Stack<SerCtor> ctors; };
  Stack<SerDtype> toSerialize;

  DEBUG("creating constructors: ");
  for (auto ta : tas) {
    _createdTermAlgebras.insert(ta->sort());
    Stack<Z3_constructor> ctors(ta->nConstructors());
    Stack<SerCtor> serCtors;

    for (auto cons : ta->iterCons()) {
      // data needed for the  Z3_mk_constructor call
      Stack<SerDtor> serDtors;
      Stack<Z3_sort> argSorts(cons->arity());
      Stack<unsigned> argSortRefs(cons->arity());
      Stack<Z3_symbol> argNames(cons->arity());

      auto i = 0;
      for (auto argSort : cons->iterArgSorts()) {
        auto dtorName = new_string_symobl(env.signature->getFunction(cons->functor())->name() + "_arg" + to_vstring(i++));
        if (_out.isSome())
          serDtors.push(SerDtor {
              .name = z3::symbol(_context, dtorName),
              .sort = argSort,
          });
        argNames.push(dtorName);
        recSorts.tryGet(argSort)
          .match([&](unsigned idx) {
                // for sorts that are to be generated with the call of Z3_mk_datatypes we need to push their index, and a nullptr
                argSortRefs.push(idx);
                argSorts.push(nullptr);
              },
              [&]() {
                // for other sorts, we need to push the sort, and an arbitrary index
                argSortRefs.push(0);  // <- 0 will never be read
                argSorts.push(getz3sort(argSort));
              });
      }

      cons->createDiscriminator();
      vstring discrName = cons->discriminatorName();

      DEBUG("\t", ta->sort().toString(), "::", env.signature->getFunction(cons->functor())->name(), ": ", env.signature->getFunction(cons->functor())->fnType()->toString());

      Z3_symbol ctorName = Z3_mk_string_symbol(_context, env.signature->getFunction(cons->functor())->name().c_str());

      ASS_EQ(argSortRefs.size(), cons->arity())
      ASS_EQ(   argSorts.size(), cons->arity())
      ASS_EQ(   argNames.size(), cons->arity())
      if (_out.isSome())
        serCtors.push(SerCtor{
            .name = z3::symbol(_context, ctorName),
            .dtors = std::move(serDtors),
        });
      ctors.push(Z3_mk_constructor(_context,
          ctorName,
          Z3_mk_string_symbol(_context, discrName.c_str()),
          cons->arity(),
          cons->arity() == 0 ? nullptr : argNames.begin(),
          cons->arity() == 0 ? nullptr : argSorts.begin(),
          cons->arity() == 0 ? nullptr : argSortRefs.begin()
      ));

    }
    ASS_EQ(ctors.size(), ta->nConstructors());

    ctorss.push(std::move(ctors));
    ASS_EQ(ctorss.top().size(), ta->nConstructors());
    ctorss_z3.push(Z3_mk_constructor_list(_context, ctorss.top().size(),  ctorss.top().begin()));
    sortNames.push(Z3_mk_string_symbol(_context, ta->sort().toString().c_str()));
    if (_out.isSome())
      toSerialize.push(SerDtype {
        .name = ta->sort(),
        .ctors = std::move(serCtors),
      });
  }

  ASS_EQ(sortNames.size(), tas.size())
  ASS_EQ(ctorss.size()   , tas.size())
  ASS_EQ(ctorss_z3.size(), tas.size())

  Array<Z3_sort> sorts(tas.size());

  // actually created the datatypes
  Z3_mk_datatypes(_context, tas.size(), sortNames.begin(), sorts.begin(), ctorss_z3.begin());

  // register the `z3::func_decl`s created by `Z3_mk_datatypes` in indices to be queried when needed
  for (unsigned iSort = 0; iSort < sorts.size(); iSort++) {
    _sorts.insert(tas[iSort]->sort(), z3::sort(_context, sorts[iSort]));
    auto ta = tas[iSort];
    auto& ctors = ctorss[iSort];
    for (unsigned iCons = 0; iCons < ta->nConstructors(); iCons++) {
      auto ctor = ta->constructor(iCons);

      Z3_func_decl constr_;
      Z3_func_decl discr_;
      Array<Z3_func_decl> destr(ctor->arity());

      Z3_query_constructor(_context,
                           ctors[iCons],
                           ctor->arity(),
                           &constr_,
                           &discr_,
                           destr.begin());

      auto discr = z3::func_decl(_context, discr_);
      auto constr = z3::func_decl(_context, constr_);

      auto ctorId = FuncOrPredId::monomorphicFunction(ctor->functor());
      _toZ3.insert(ctorId, constr);
      _fromZ3.insert(constr, ctorId);

      if (ctor->hasDiscriminator()) {
        auto discrId = FuncOrPredId::monomorphicPredicate(ctor->discriminator());
        _toZ3.insert(discrId, discr);
        // _fromZ3.insert(discr, discrId);
      }
      for (unsigned iDestr = 0; iDestr < ctor->arity(); iDestr++)  {
        auto dtor = z3::func_decl(_context, destr[iDestr]);
        // careful: datatypes can have boolean fields!
        auto id = FuncOrPredId(
          ctor->destructorFunctor(iDestr),
          dtor.range().is_bool()
        );
        _toZ3.insert(id, dtor);
        _fromZ3.insert(dtor, id);
      }
    }
  }

  // clean up
  for (auto clist : ctorss_z3) {
    Z3_del_constructor_list(_context, clist);
  }

  for (auto ctors : ctorss) {
    for (auto ctor : ctors) {
      Z3_del_constructor(_context, ctor);
    }
  }

  // serizalize to z3
  output("(declare-datatypes (");
  for (auto& s : toSerialize) {
    output(" (", getz3sort(s.name), " 0)");
  }
  outputln(" ) (");

  auto quote = [&](auto x){
    vstringstream s;
    s << x;
    auto str = s.str();
    if (str[0] == '\'') {
      return "|" + str + "|";
    } else {
      return str;
    }
  };

  for (auto& dty : toSerialize) {
    outputln("    ( ;-- datatype ", getz3sort(dty.name));
    for (auto& ctor : dty.ctors) {
      output("        ( ", quote(ctor.name));
      for (auto& dtor : ctor.dtors) {
        output(" ( ", quote(dtor.name), " ", getz3sort(dtor.sort), " )");
      }
      outputln(" )");
    }
    outputln("    )");
  }
  outputln("))");

}

z3::func_decl const& Z3Interfacing::findConstructor(FuncId id_)
{
  CALL("Z3Interfacing::findConstructor(FuncId id)")
  auto id = FuncOrPredId::monomorphicFunction(id_);
  auto f = _toZ3.tryGet(id);
  if (f.isSome()) {
    return f.unwrap();
  } else {
    auto sym = env.signature->getFunction(id_);
    auto domain = sym->fnType()->result();
    createTermAlgebra(*env.signature->getTermAlgebraOfSort(domain));
    return _toZ3.get(id);
  }
}


z3::expr to_int(z3::expr e)
{ return z3::expr(e.ctx(), Z3_mk_real2int(e.ctx(), e)); }

namespace tptp {

  z3::expr floor(z3::expr e)
  { return to_real(to_int(e)); }

  z3::expr ceiling(z3::expr x)
  { return -tptp::floor(-x); }

  z3::expr truncate(z3::expr x)
  { return ite(x >= 0, tptp::floor(x), tptp::ceiling(x)); }

  z3::expr quotient_e(z3::expr n, z3::expr d)
  { return ite(d >= 0, floor(n / d), ceiling(n / d)); }

  z3::expr quotient_t(z3::expr l, z3::expr r)
  { return tptp::truncate(l / r); }

  z3::expr quotient_f(z3::expr l, z3::expr r)
  { return tptp::floor(l / r); }

  template<class F>
  struct LiftInt
  {
    F bin_real_func;

    z3::expr operator()(z3::expr l, z3::expr r)
    { return to_int(bin_real_func(to_real(l), to_real(r))); }
  };
  template<class F> LiftInt<F> liftInt(F f) { return LiftInt<F>{ f }; }

  template<class F>
  struct RemainderOp
  {
    F quotient;

    z3::expr operator()(z3::expr l, z3::expr r)
    { return l / r - quotient(l,r); }
  };
  template<class F> RemainderOp<F> remainder(F f) { return RemainderOp<F>{ f }; }
}


struct ToZ3Expr
{
  Z3Interfacing& self;
  Stack<z3::expr> _defs;

  using Arg    = TermList;
  using Result = z3::expr;

  z3::expr operator()(TermList toEval, z3::expr* args)
  {
    CALL("ToZ3Expr::operator()");
    // DEBUG("in: ", toEval)
    ASS(toEval.isTerm())
    auto trm = toEval.term();
    bool isLit = trm->isLiteral();

    Signature::Symbol* symb;
    SortId range_sort;
    bool is_equality = false;
    if (isLit) {
      symb = env.signature->getPredicate(trm->functor());
      range_sort = AtomicSort::boolSort();
      // check for equality
      if(trm->functor()==0){
         is_equality=true;
         ASS(trm->arity()==2);
      }
      if(symb->equalityProxy()) {
        is_equality=true;
        ASS_EQ(trm->arity(), symb->fnType()->typeArgsArity() + 2);
      }
    } else {
      symb = env.signature->getFunction(trm->functor());
      OperatorType* ftype = symb->fnType();
      range_sort = ftype->result();
      if (env.signature->isTermAlgebraSort(range_sort) &&  !self._createdTermAlgebras.contains(range_sort) ) {
        self.createTermAlgebra(*env.signature->getTermAlgebraOfSort(range_sort));
      }
    }

    //if constant treat specially
    if(trm->arity()==0) {
      if(symb->integerConstant()){
        IntegerConstantType value = symb->integerValue();
        return self._context.int_val(value.toInner());
      }
      if(symb->realConstant()) {
        RealConstantType value = symb->realValue();
        return self._context.real_val(value.numerator().toInner(),value.denominator().toInner());
      }
      if(symb->rationalConstant()) {
        RationalConstantType value = symb->rationalValue();
        return self._context.real_val(value.numerator().toInner(),value.denominator().toInner());
      }
      if(!isLit && env.signature->isFoolConstantSymbol(true,trm->functor())) {
        return self._context.bool_val(true);
      }
      if(!isLit && env.signature->isFoolConstantSymbol(false,trm->functor())) {
        return self._context.bool_val(false);
      }
      if(symb->termAlgebraCons()) {
        auto ctor = self.findConstructor(trm->functor());
        return ctor();
      }
      // TODO do we really have overflownConstants ?? not in evaluation(s) at least
      if (symb->overflownConstant()) {
        // too large for native representation, but z3 should cope
        auto s = symb->fnType()->result();
        if (s == IntTraits::sort()) {
          return self._context.int_val(symb->name().c_str());
        } else if (s == RatTraits::sort()) {
          return self._context.real_val(symb->name().c_str());
        } else if (s == RealTraits::sort()) {
          return self._context.real_val(symb->name().c_str());
        } else {
          ; // intentional fallthrough; the input is fof (and not tff), so let's just treat this as a constant
        }
      }

      // If not value then create constant symbol
      return self.getConst(symb, self.getz3sort(range_sort));
    }
    ASS(trm->arity()>0);

   //Check for equality
    if(is_equality){
      // both equality and equality proxy translated as z3 equality
      return args[0] == args[1];
    }

    // Currently do not deal with all intepreted operations, should extend
    // - constants dealt with above
    // - unary funs/preds like is_rat interpretation unclear
    if(symb->interpreted()){
      Interpretation interp = static_cast<Signature::InterpretedSymbol*>(symb)->getInterpretation();

      if (Theory::isPolymorphic(interp)) {
        switch(interp){
          case Theory::ARRAY_SELECT:
          case Theory::ARRAY_BOOL_SELECT:
            // select(array,index)
            return select(args[0],args[1]);

          case Theory::ARRAY_STORE:
            // store(array,index,value)
            return store(args[0],args[1],args[2]);

          default:
            {}//skip it and treat the function as uninterpretted
        }

      } else {
        auto int_zero = self._context.int_val(0);
        auto real_zero = self._context.real_val(0);

        switch(interp){
        // Numerical operations
        case Theory::INT_DIVIDES:
          {
          auto k = self.getNamingConstantFor(toEval, self._context.int_sort());
          // a divides b <-> k * a ==  b
          return k * args[0] == args[1];
          }

        case Theory::INT_UNARY_MINUS:
        case Theory::RAT_UNARY_MINUS:
        case Theory::REAL_UNARY_MINUS:
          return -args[0];

        case Theory::INT_PLUS:
        case Theory::RAT_PLUS:
        case Theory::REAL_PLUS:
          return args[0] + args[1];

        // Don't really need as it's preprocessed away
        case Theory::INT_MINUS:
        case Theory::RAT_MINUS:
        case Theory::REAL_MINUS:
          return args[0] - args[1];

        case Theory::INT_MULTIPLY:
        case Theory::RAT_MULTIPLY:
        case Theory::REAL_MULTIPLY:
          return args[0] * args[1];

        case Theory::RAT_QUOTIENT:
        case Theory::REAL_QUOTIENT:
          return args[0] / args[1];

        /** TPTP's ${quotient,remainder}_e */
        case Theory::INT_QUOTIENT_E:  return args[0] / args[1];          /* <--- same semantics of tptp and smtlib2 for int */
        case Theory::INT_REMAINDER_E: return z3::mod(args[0], args[1]);  /* <---                                            */
        case Theory::RAT_QUOTIENT_E:
        case Theory::REAL_QUOTIENT_E:  return                 tptp::quotient_e (args[0], args[1]);
        case Theory::RAT_REMAINDER_E:
        case Theory::REAL_REMAINDER_E: return tptp::remainder(tptp::quotient_e)(args[0], args[1]);

         /** {quotient,remainder}_t */
        case Theory::INT_QUOTIENT_T:  return tptp::liftInt(                tptp::quotient_t )(args[0],args[1]);
        case Theory::INT_REMAINDER_T: return tptp::liftInt(tptp::remainder(tptp::quotient_t))(args[0],args[1]);
        case Theory::RAT_QUOTIENT_T:
        case Theory::REAL_QUOTIENT_T: return                 tptp::quotient_t (args[0], args[1]);
        case Theory::REAL_REMAINDER_T:
        case Theory::RAT_REMAINDER_T: return tptp::remainder(tptp::quotient_t)(args[0], args[1]);

        /** {quotient,remainder}_f */
        case Theory::INT_QUOTIENT_F:  return tptp::liftInt(                tptp::quotient_f )(args[0], args[1]);
        case Theory::INT_REMAINDER_F: return tptp::liftInt(tptp::remainder(tptp::quotient_f))(args[0],args[1]);
        case Theory::RAT_QUOTIENT_F:
        case Theory::REAL_QUOTIENT_F: return                 tptp::quotient_f (args[0], args[1]);
        case Theory::REAL_REMAINDER_F:
        case Theory::RAT_REMAINDER_F: return tptp::remainder(tptp::quotient_f)(args[0], args[1]);


        case Theory::RAT_TO_INT:
        case Theory::REAL_TO_INT:
        case Theory::INT_FLOOR:
        case Theory::RAT_FLOOR:
        case Theory::REAL_FLOOR:
          return to_real(to_int(args[0]));

        case Theory::RAT_TO_REAL:
          return args[0];

        case Theory::INT_TO_REAL:
        case Theory::INT_TO_RAT:
          return to_real(args[0]);

        case Theory::INT_CEILING:
        case Theory::RAT_CEILING:
        case Theory::REAL_CEILING:
          return tptp::ceiling(args[0]);

        case Theory::INT_TRUNCATE:
        case Theory::RAT_TRUNCATE:
        case Theory::REAL_TRUNCATE:
          return tptp::truncate(args[0]);

        case Theory::INT_ROUND:
        case Theory::RAT_ROUND:
        case Theory::REAL_ROUND: {
            z3::expr t = args[0];
            z3::expr i = to_int(t);
            z3::expr i2 = i + self._context.real_val(1,2);
            return ite(t > i2, i+1, ite(t==i2, ite(z3::mod(i, 2),i ,i+1 ),i));
          }

        case Theory::INT_ABS: {
            z3::expr t = args[0];
            return ite(t > 0, t, -t);
          }

        case Theory::INT_IS_INT:
        case Theory::RAT_IS_INT:
        case Theory::REAL_IS_INT:
          return z3::is_int(args[0]);

        case Theory::INT_LESS:
        case Theory::RAT_LESS:
        case Theory::REAL_LESS:
          return args[0] < args[1];

        case Theory::INT_GREATER:
        case Theory::RAT_GREATER:
        case Theory::REAL_GREATER:
          return args[0] > args[1];

        case Theory::INT_LESS_EQUAL:
        case Theory::RAT_LESS_EQUAL:
        case Theory::REAL_LESS_EQUAL:
          return args[0] <= args[1];

        case Theory::INT_GREATER_EQUAL:
        case Theory::RAT_GREATER_EQUAL:
        case Theory::REAL_GREATER_EQUAL:
          return args[0] >= args[1];

        default:
          {}//skip it and treat the function as uninterpretted
        }
      }
    }

    // uninterpretd function
    auto f = self.z3Function(Z3Interfacing::FuncOrPredId(trm));
    return f(f.arity(), args);
  }
};



z3::func_decl Z3Interfacing::z3Function(FuncOrPredId functor)
{
  CALL("Z3Interfacing::z3Function");
  auto& self = *this;

  auto found = self._toZ3.tryGet(functor);
  if (found.isSome()) {
    return found.unwrap();
  } else {
    // function does not yet exist, create it
    auto symb = functor.isPredicate ? env.signature->getPredicate(functor.id)
                                    : env.signature->getFunction(functor.id);
    auto type = functor.isPredicate ? symb->predType() : symb->fnType();

    // polymorphic symbol application: treat f(<sorts>, ...) as f<sorts>(...) for Z3
    vstring namebuf = symb->name();
    Substitution typeSubst;
    if(functor.forSorts) {
      SortHelper::getTypeSub(functor.forSorts, typeSubst);
      namebuf += '$';
      for(unsigned i = 0; i < functor.forSorts->numTypeArguments(); i++)
        namebuf += functor.forSorts->nthArgument(i)->toString();
    }

    z3::sort_vector domain_sorts = z3::sort_vector(self._context);
    for (unsigned i=type->typeArgsArity(); i<type->arity(); i++) {
      TermList arg = SubstHelper::apply(type->arg(i), typeSubst);
      domain_sorts.push_back(self.getz3sort(arg));
    }

    z3::symbol name = self._context.str_symbol(namebuf.c_str());
    auto range_sort = functor.isPredicate
      ? self._context.bool_sort()
      : self.getz3sort(SubstHelper::apply(type->result(), typeSubst));
    auto decl = self._context.function(name,domain_sorts,range_sort);
    outputln(decl);
    self._toZ3.insert(functor, decl); // (declare-fun ...)
    return decl;
  }
}

/**
 * Translate a Vampire term into a Z3 term
 * - Assumes term is ground
 * - Translates the ground structure
 * - Some interpreted functions/predicates are handled
 */
Z3Interfacing::Representation Z3Interfacing::getRepresentation(Term* trm)
{
  CALL("Z3Interfacing::getRepresentation(Term*)");
  Stack<z3::expr> defs;
  auto expr = evaluateBottomUp(TermList(trm), ToZ3Expr{ *this, defs });
  return Representation(expr, std::move(defs));
}

Z3Interfacing::Representation Z3Interfacing::getRepresentation(SATLiteral slit)
{
  CALL("Z3Interfacing::getRepresentation(SATLiteral)");
  BYPASSING_ALLOCATOR;


  //First, does this represent a ground literal
  Literal* lit = _sat2fo.toFO(slit);
  if(lit && lit->ground()){
    //cout << "getRepresentation of " << lit->toString() << endl;
    // Now translate it into an SMT object
    try{
      auto repr = getRepresentation(lit);

      /* we name all literals in order to make z3 cache their truth values.
       * this gives a massive performance boost in many cases.              */

      z3::expr bname = getNameExpr(slit.var());
      z3::expr naming = (bname == repr.expr);
      repr.defs.push(naming);
      repr.expr = bname;

      if(_showZ3){
        env.beginOutput();
        env.out() << "[Z3] add (naming): " << naming << std::endl;
        env.endOutput();
      }

      if(slit.isNegative()) {
        repr.expr = !repr.expr;
      }

      return repr;
    }catch(z3::exception& exception){
     reportSpiderFail();
     cout << "Z3 exception:\n" << exception.msg() << endl;
     ASSERTION_VIOLATION_REP("Failed to create Z3 rep for " + lit->toString());
    }
  } else {
    //if non ground then just create a propositional variable
    z3::expr e = getNameExpr(slit.var());
    return Representation(slit.isPositive() ? e : !e,
                          Stack<z3::expr>());
  }
}

SATClause* Z3Interfacing::getRefutation()
{
  CALL("Z3Interfacing::getRefutation");

  return PrimitiveProofRecordingSATSolver::getRefutation();

  // TODO: optionally, we could try getting an unsat core from Z3 (could be smaller than all the added clauses so far)
  // NOTE: this will not (necessarily) be the same option as _unsatCore, which takes care of minimization of added assumptions
  // also ':core.minimize' might need to be set to get some effect
}

Z3Interfacing::~Z3Interfacing()
{
  CALL("~Z3Interfacing")
  _sorts.clear();
  _toZ3.clear();
  _fromZ3.clear();
  outputln(); // flush the output file
}



bool Z3Interfacing::isNamedExpr(unsigned var) const
{ return _varNames.find(var); }

z3::expr Z3Interfacing::getNameExpr(unsigned var)
{
  return _varNames.getOrInit(var, [&](){
      // this method is called very often in runs with a lot of avatar reasoning. Cache the constants to avoid that z3 has to search for the string name in its function index
      vstring name = "v"+Lib::Int::toString(var);
      outputln("(declare-fun ", name, " () Bool)");
      return _context.bool_const(name.c_str());
  });
}


z3::expr Z3Interfacing::getNamingConstantFor(TermList toName, z3::sort sort)
{
  return _termIndexedConstants.getOrInit(toName, [&](){
      auto name = "n" + toName.toString();
      outputln("(declare-fun ", name, " () ", sort, ")");
      return _context.constant(name.c_str(), sort);
  });
}

z3::expr Z3Interfacing::getConst(Signature::Symbol* symb, z3::sort sort)
{
  return _constantNames.getOrInit(symb, [&]() {
    // careful: keep native constants' names distinct from the above ones (hence the "c"-prefix below)
    vstring name("c" + symb->name());
    outputln("(declare-fun ", name, " () ", sort, ")");
    return _context.constant(name.c_str(), sort);
  });
}

} // namespace SAT

#endif /** if VZ3 **/
