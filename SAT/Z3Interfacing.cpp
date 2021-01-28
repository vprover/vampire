
/*
 * File Z3Interfacing.cpp.
 *
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
#define TODO ASSERTION_VIOLATION

#include "Forwards.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"

#include "Lib/Environment.hpp"
#include "Lib/System.hpp"

#include "Kernel/NumTraits.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TermList.hpp"
#include "Lib/Coproduct.hpp"

#include "Shell/UIHelper.hpp"
#include "Indexing/TermSharing.hpp"
#include "Z3Interfacing.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)
namespace Lib {

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

Z3Interfacing::Z3Interfacing(const Shell::Options& opts,SAT2FO& s2f, bool unsatCoresForAssumptions):
  Z3Interfacing(s2f, opts.showZ3(), opts.z3UnsatCores(), unsatCoresForAssumptions)
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

Z3Interfacing::Z3Interfacing(SAT2FO& s2f, bool showZ3, bool unsatCoreForRefutations, bool unsatCoresForAssumptions):
  _varCnt(0), 
  _sat2fo(s2f),
  _status(SATISFIABLE), 
  _config(),
  _context(_config),
  _solver(_context),
  _model((STATEMENTS_TO_EXPRESSION(
            BYPASSING_ALLOCATOR; 
            _solver.check(); ),
         _solver.get_model())), 
  _assumptions(_context), _unsatCoreForAssumptions(unsatCoresForAssumptions),
  _showZ3(showZ3),
  _unsatCoreForRefutations(unsatCoreForRefutations),
  // TODO makes z3::solver::get_model way faster. gives a 400% overall speed up in some cases where there is a lot of avatar reasoning. should we remoe this as option?
  _nameAllLiterals(true)
{
  CALL("Z3Interfacing::Z3Interfacing");
  BYPASSING_ALLOCATOR
  _solver.reset();

  z3::set_param("rewriter.expand_store_eq", "true");
  //z3::set_param("trace", "true");

    z3::params p(_context);
    p.set("model.compact", false); // keeps z3 from compressing its model. ~50% of the runtime of get_model is spent doing that otherwise
  if (_unsatCoreForAssumptions) {
    p.set(":unsat-core", true);
  }
    //p.set(":smtlib2-compliant",true);
  _solver.set(p);
  Z3_set_error_handler(_context, handleZ3Error);
  //Z3_enable_trace("memory");
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

  z3::expr z3clause = _context.bool_val(false);

  PRINT_CPP("exprs.push_back(c.bool_val(false)); // starting a clause")

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++){
    SATLiteral l = (*cl)[i];
    auto repr = getRepresentation(l);

    for (auto def : repr.defs) 
      _solver.add(def);

    z3clause = z3clause || repr.expr;

    PRINT_CPP("{ expr e = exprs.back(); exprs.pop_back(); expr cl = exprs.back(); exprs.pop_back(); exprs.push_back(cl || e); } // append a literal");
  }

  PRINT_CPP("{ expr cl = exprs.back(); exprs.pop_back(); cout << \"clause: \" << cl << endl; solver.add(cl); }")
  
  if(_showZ3){
    env.beginOutput();
    env.out() << "[Z3] add (clause): " << z3clause << std::endl;
    env.endOutput();
  }

  _solver.add(z3clause);
}

void Z3Interfacing::addAssumption(SATLiteral lit)
{
  CALL("Z3Interfacing::addAssumption");

  auto repr = getRepresentation(lit);
  for (auto def : repr.defs)
    _assumptions.push_back(def);

  _assumptions.push_back(repr.expr);
}

SATSolver::Status Z3Interfacing::solveWithAssumptions(Stack<SATLiteral> const& assumptions) 
{
  CALL("Z3Interfacing::solve");
  BYPASSING_ALLOCATOR;
  auto all_assumptions = _assumptions;
  for (auto a : assumptions) {
    auto repr = getRepresentation(a);
    for (auto d : repr.defs) all_assumptions.push_back(d);
    all_assumptions.push_back(repr.expr);
  }

  z3::check_result result = all_assumptions.empty() ? _solver.check() : _solver.check(all_assumptions);

  if(_showZ3){
    env.beginOutput();
    env.out() << "[Z3] solve result: " << result << std::endl;
    env.endOutput();
  }

  switch(result){
    case z3::check_result::unsat:
      _status = UNSATISFIABLE; 
      break;
    case z3::check_result::sat:
      _status = SATISFIABLE;
      _model = _solver.get_model();
      /*
      cout << "model : " << endl;
      for(unsigned i=0; i < _model.size(); i++){
        z3::func_decl v = _model[i];
        cout << v.name() << " = " << _model.get_const_interp(v) << endl;
      }
      */
      break;
    case z3::check_result::unknown:
      _status = UNKNOWN;
      break;
#if VDEBUG
    default: ASSERTION_VIOLATION;
#endif
  }
  return _status;
}

SATSolver::Status Z3Interfacing::solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool onlyProperSubusets)
{
  CALL("Z3Interfacing::solveUnderAssumptions");

  if (!_unsatCoreForAssumptions) {
    return SATSolverWithAssumptions::solveUnderAssumptions(assumps,conflictCountLimit,onlyProperSubusets);
  }

  ASS(!hasAssumptions());

  _solver.push();

  // load assumptions:
  SATLiteralStack::ConstIterator it(assumps);

  static DHMap<vstring,SATLiteral> lookup;
  lookup.reset();
  unsigned n=0;
  vstring ps="$_$_$";

  while (it.hasNext()) {
    SATLiteral v_assump = it.next();
    auto z_assump = getRepresentation(v_assump);
    for (auto d : z_assump.defs) 
      _solver.add(d);

    vstring p = ps+Int::toString(n++);
    _solver.add(z_assump.expr,p.c_str());
    lookup.insert(p,v_assump);
  }

  z3::check_result result = _solver.check();

  _solver.pop();

  if (result == z3::check_result::unsat) {

    _failedAssumptionBuffer.reset();

    z3::expr_vector  core = _solver.unsat_core();
    for (unsigned i = 0; i < core.size(); i++) {
      z3::expr ci = core[i];
      vstring cip = vstring(ci.to_string().c_str());
      SATLiteral v_assump = lookup.get(cip);
      _failedAssumptionBuffer.push(v_assump);
    }

    return UNSATISFIABLE;
  } else if (result == z3::check_result::sat) {
    _model = _solver.get_model();
    return SATISFIABLE;
  } else {
    return UNKNOWN;
  }
}

SATSolver::VarAssignment Z3Interfacing::getAssignment(unsigned var) 
{
  CALL("Z3Interfacing::getAssignment");
  BYPASSING_ALLOCATOR;

  ASS_EQ(_status,SATISFIABLE);
  bool named = isNamedExpr(var);
  z3::expr rep = named ? getNameExpr(var) : getRepresentation(SATLiteral(var,1)).expr;
  z3::expr assignment = _model.eval(rep,true /*model_completion*/);

  if(assignment.bool_value()==Z3_L_TRUE){
    return TRUE;
  }
  if(assignment.bool_value()==Z3_L_FALSE){
    return FALSE;
  }

#if VDEBUG
  std::cout << rep << std::endl;
  ASSERTION_VIOLATION_REP(assignment);
#endif
  return NOT_KNOWN;
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

  static Term* toTerm(Copro const& co, unsigned sort) {
    return co.match(
            [&](Term* t) 
            { return t; },

            [&](RationalConstantType c) 
            { 
              return sort == RealTraits::sort 
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

  bool name; //TODO what do we do about naming?
  z3::expr rep = getz3expr(trm, name).expr;
  z3::expr ev = _model.eval(rep,true); // true means "model_completion"
  unsigned sort = SortHelper::getResultSort(trm);

  DEBUG("z3 expr: ", ev)
  auto result = evaluateBottomUp(ev, EvaluateInModel { *this })
    .map([&](EvaluateInModel::Copro co) { 
        return co.match(
            [&](Term* t) 
            { return t; },

            [&](RationalConstantType c) 
            { 
              return sort == RealTraits::sort 
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

//TODO: should handle function/predicate types really
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
         if(s == Sorts::SRT_BOOL    ) insert(_context.bool_sort());
    else if(s == Sorts::SRT_INTEGER ) insert(_context.int_sort());
    else if(s == Sorts::SRT_REAL    ) insert(_context.real_sort());
    else if(s == Sorts::SRT_RATIONAL) insert(_context.real_sort()); // Drop notion of rationality 
    // TODO: are we really allowed to do this ???                      ^^^^^^^^^^^^^^^^^^^^^^^^^^
    else if(env.sorts->isOfStructuredSort(s, Sorts::StructuredSort::ARRAY)) {
      
      z3::sort index_sort = getz3sort(env.sorts->getArraySort(s)->getIndexSort());
      z3::sort value_sort = getz3sort(env.sorts->getArraySort(s)->getInnerSort());
   
      insert(_context.array_sort(index_sort,value_sort));

    } else if (env.signature->isTermAlgebraSort(s)) {
      createTermAlgebra(*env.signature->getTermAlgebraOfSort(s));

    } else {
      insert(_context.uninterpreted_sort(_context.str_symbol(env.sorts->sortName(s).c_str())));
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
#define INT_IDENTS 0
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

#if !INT_IDENTS
  auto new_string_symobl = [&](vstring str) 
  { return Z3_mk_string_symbol(_context, str.c_str()); };
#endif

  // create the data needed for Z3_mk_datatypes(...)
  Stack<Stack<Z3_constructor>> ctorss(tas.size());
  Stack<Z3_constructor_list> ctorss_z3(tas.size());
  Stack<Z3_symbol> sortNames(tas.size());
  DEBUG("creating constructors: ");
  for (auto ta : tas) {
    _createdTermAlgebras.insert(ta->sort());
    Stack<Z3_constructor> ctors(ta->nConstructors());

    for (auto cons : ta->iterCons()) {
      Stack<Z3_sort> argSorts(cons->arity());
      Stack<unsigned> argSortRefs(cons->arity());
      Stack<Z3_symbol> argNames(cons->arity());
      auto i = 0;
      for (auto argSort : cons->iterArgSorts()) {
#if INT_IDENTS
        argNames.push(Z3_mk_int_symbol(_context, i++));
#else 
        argNames.push(new_string_symobl(env.signature->getFunction(cons->functor())->name() + "_arg" + to_vstring(i++)));
#endif
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
      auto discrName = cons->discriminatorName().c_str();
      
      DEBUG("\t", env.sorts->sortName(ta->sort()), "::", env.signature->getFunction(cons->functor())->name());

      ASS_EQ(argSortRefs.size(), cons->arity())
      ASS_EQ(   argSorts.size(), cons->arity())
      ASS_EQ(   argNames.size(), cons->arity())

      ctors.push(Z3_mk_constructor(_context,
#if INT_IDENTS
          Z3_mk_int_symbol(_context, cons->functor()),
#else
          Z3_mk_string_symbol(_context, env.signature->getFunction(cons->functor())->name().c_str()), 
#endif
          Z3_mk_string_symbol(_context, discrName),
          cons->arity(),
          argNames.begin(),
          argSorts.begin(),
          argSortRefs.begin()
      ));
    }
    ASS_EQ(ctors.size(), ta->nConstructors());

    ctorss.push(std::move(ctors));
    ASS_EQ(ctorss.top().size(), ta->nConstructors());
    ctorss_z3.push(Z3_mk_constructor_list(_context, ctorss.top().size(),  ctorss.top().begin()));
    sortNames.push(Z3_mk_string_symbol(_context, env.sorts->sortName(ta->sort()).c_str()));
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

      auto ctorId = FuncOrPredId::function(ctor->functor());
      _toZ3.insert(ctorId, Z3FuncEntry::plain(constr));
      ASS(_toZ3.find(ctorId))
      _fromZ3.insert(constr, ctorId);

      if (ctor->hasDiscriminator()) {
        auto discrId = FuncOrPredId::predicate(ctor->discriminator());
        _toZ3.insert(discrId, Z3FuncEntry::plain(discr));
        // _fromZ3.insert(discr, discrId);
      }
      for (unsigned iDestr = 0; iDestr < ctor->arity(); iDestr++)  {
        auto dtor = z3::func_decl(_context, destr[iDestr]);
        auto id = FuncOrPredId::function(ctor->destructorFunctor(iDestr));
        _toZ3.insert(id, Z3FuncEntry::destructor(dtor, discr));
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
}

z3::func_decl const& Z3Interfacing::findConstructor(FuncId id_) 
{
  CALL("Z3Interfacing::findConstructor(FuncId id)")
  auto id = FuncOrPredId::function(id_);
  auto f = _toZ3.tryGet(id);
  if (f.isSome()) {
    return f.unwrap().decl;
  } else {
    auto sym = env.signature->getFunction(id_);
    auto domain = sym->fnType()->result(); 
    createTermAlgebra(*env.signature->getTermAlgebraOfSort(domain));
    return _toZ3.get(id).decl;
  }
}




struct ToZ3Expr 
{
  using Z3FuncEntry = Z3Interfacing::Z3FuncEntry;
  using DestructorMeta = Z3Interfacing::DestructorMeta;
  Z3Interfacing& self;
  bool& _nameExpression;

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
    unsigned range_sort;
    bool is_equality = false;
    if (isLit) {
      symb = env.signature->getPredicate(trm->functor());
      range_sort = Sorts::SRT_BOOL;
      // check for equality
      if(trm->functor()==0){
         is_equality=true;
         ASS(trm->arity()==2);
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

        switch (symb->fnType()->result()) {
        case Sorts::SRT_INTEGER:
          return self._context.int_val(symb->name().c_str());
        case Sorts::SRT_RATIONAL:
          return self._context.real_val(symb->name().c_str());
        case Sorts::SRT_REAL:
          return self._context.real_val(symb->name().c_str());
        default:
          ; // intentional fallthrough; the input is fof (and not tff), so let's just treat this as a constant
        }
      }

      // If not value then create constant symbol
      return self.getNameConst(symb->name(), self.getz3sort(range_sort));
    }
    ASS(trm->arity()>0);

   //Check for equality
    if(is_equality){
      return args[0] == args[1]; 
    }

    // Currently do not deal with all intepreted operations, should extend 
    // - constants dealt with above
    // - unary funs/preds like is_rat interpretation unclear
    if(symb->interpreted()){
      Interpretation interp = static_cast<Signature::InterpretedSymbol*>(symb)->getInterpretation();

      if (Theory::isPolymorphic(interp)) {
        _nameExpression = true;
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
          auto k = self.constantFor(toEval, self._context.int_sort());
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

        case Theory::INT_QUOTIENT_E: 
          return args[0] / args[1];

        // The z3 header must be wrong
        //case Theory::RAT_QUOTIENT_E: 
        //case Theory::REAL_QUOTIENT_E: 
           //TODO

        case Theory::RAT_TO_INT:
        case Theory::REAL_TO_INT:
        case Theory::INT_FLOOR:
        case Theory::RAT_FLOOR:
        case Theory::REAL_FLOOR:
          return self.to_real(self.to_int(args[0])); 

        case Theory::INT_TO_REAL:
        case Theory::RAT_TO_REAL:
        case Theory::INT_TO_RAT: //I think this works also
          return self.to_real(args[0]);

        case Theory::INT_CEILING:
        case Theory::RAT_CEILING:
        case Theory::REAL_CEILING:
          return self.ceiling(args[0]);

        case Theory::INT_TRUNCATE:
        case Theory::RAT_TRUNCATE:
        case Theory::REAL_TRUNCATE:
          return self.truncate(args[0]); 

        case Theory::INT_ROUND:
        case Theory::RAT_ROUND:
        case Theory::REAL_ROUND:
          {
            z3::expr t = args[0];
            z3::expr i = self.to_int(t);
            z3::expr i2 = i + self._context.real_val(1,2);
            return ite(t > i2, i+1, ite(t==i2, ite(self.is_even(i),i,i+1),i));
          }

        case Theory::INT_ABS:
          {
            z3::expr t = args[0];
            return ite(t > 0, t, -t);
          }

         case Theory::INT_QUOTIENT_T:
         case Theory::INT_REMAINDER_T:
// TODO joe undestand this
           // leave as uninterpreted
           self.addTruncatedOperations(args[0],args[1],Theory::INT_QUOTIENT_T,Theory::INT_REMAINDER_T,range_sort);
           break;
         case Theory::RAT_QUOTIENT_T:
           self.addTruncatedOperations(args[0],args[1],Theory::RAT_QUOTIENT_T,Theory::RAT_REMAINDER_T,range_sort);
           return self.truncate(args[0]/args[1]);

         case Theory::RAT_REMAINDER_T:
           self.addTruncatedOperations(args[0],args[1],Theory::RAT_QUOTIENT_T,Theory::RAT_REMAINDER_T,range_sort);
           break;
         case Theory::REAL_QUOTIENT_T:
           self.addTruncatedOperations(args[0],args[1],Theory::REAL_QUOTIENT_T,Theory::REAL_REMAINDER_T,range_sort);
           return self.truncate(args[0]/args[1]);

         case Theory::REAL_REMAINDER_T:
           self.addTruncatedOperations(args[0],args[1],Theory::REAL_QUOTIENT_T,Theory::REAL_REMAINDER_T,range_sort);
           break;

         case Theory::INT_QUOTIENT_F:
         case Theory::INT_REMAINDER_F:
           // leave as uninterpreted
           self.addFloorOperations(args[0],args[1],Theory::INT_QUOTIENT_F,Theory::INT_REMAINDER_F,range_sort);
           break;

         case Theory::RAT_QUOTIENT_F:
           self.addFloorOperations(args[0],args[1],Theory::RAT_QUOTIENT_F,Theory::RAT_REMAINDER_F,range_sort);
           return self.to_real(self.to_int(args[0] / args[1]));

         case Theory::RAT_REMAINDER_F:
           self.addFloorOperations(args[0],args[1],Theory::RAT_QUOTIENT_F,Theory::RAT_REMAINDER_F,range_sort);
           break;

         case Theory::REAL_QUOTIENT_F:
           self.addFloorOperations(args[0],args[1],Theory::REAL_QUOTIENT_F,Theory::REAL_REMAINDER_F,range_sort);
           return self.to_real(self.to_int(args[0] / args[1]));

         case Theory::REAL_REMAINDER_F:
           self.addFloorOperations(args[0],args[1],Theory::REAL_QUOTIENT_F,Theory::REAL_REMAINDER_F,range_sort);
           break;

         case Theory::RAT_REMAINDER_E:
         case Theory::REAL_REMAINDER_E:
           _nameExpression = true; 
           return z3::mod(args[0], args[1]);

         case Theory::INT_REMAINDER_E:
           _nameExpression = true;
           return z3::mod(args[0], args[1]);

       // Numerical comparisons
       // is_rat and to_rat not supported

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
          //skip it and treat the function as uninterpretted
          break;
      }
      }
    }

    // uninterpretd function

    auto entry = self.z3Function(Z3Interfacing::FuncOrPredId(trm));

    if (entry.metadata.is<DestructorMeta>()) {
      auto selector = entry.metadata.unwrap<DestructorMeta>().selector;
      _nameExpression = true;
    }

    z3::func_decl f = entry.decl;
    // Finally create expr
    z3::expr e = f(trm->arity(), args); 

    return e;
  }
};



Z3Interfacing::Z3FuncEntry Z3Interfacing::z3Function(Theory::Interpretation itp)
{
  return z3Function(Theory::isFunction(itp)  
    ? FuncOrPredId::function(env.signature->getInterpretingSymbol(itp))
    : FuncOrPredId::predicate(env.signature->getInterpretingSymbol(itp)));
}

Z3Interfacing::Z3FuncEntry Z3Interfacing::z3Function(FuncOrPredId functor)
{
  auto& self = *this;
  return self._toZ3.tryGet(functor).toOwned()
    .unwrapOrElse([&]() {
        auto symb = functor.isPredicate ? env.signature->getPredicate(functor.id) 
                                        : env.signature->getFunction(functor.id);
        auto type = functor.isPredicate ? symb->predType() : symb->fnType();

        // Does not yet exits. initialize it!
        z3::sort_vector domain_sorts = z3::sort_vector(self._context);
        for (unsigned i=0; i<type->arity(); i++) {
          domain_sorts.push_back(self.getz3sort(type->arg(i)));
        }
        z3::symbol name = self._context.str_symbol(symb->name().c_str());
        auto range_sort = functor.isPredicate ? self._context.bool_sort() : self.getz3sort(type->result());
        return Z3FuncEntry::plain(self._context.function(name,domain_sorts,range_sort));
    });
}

/**
 * Translate a Vampire term into a Z3 term
 * - Assumes term is ground
 * - Translates the ground structure
 * - Some interpreted functions/predicates are handled
 */
Z3Interfacing::Representation Z3Interfacing::getz3expr(Term* trm, bool& nameExpression)
{
  CALL("Z3Interfacing::getz3expr");
  DEBUG("in: ", *trm);
  nameExpression = false;
  Stack<z3::expr> defs;
  auto expr = evaluateBottomUp(TermList(trm), ToZ3Expr{ *this, nameExpression,  });
  if (_nameAllLiterals)
    nameExpression = true;
  DEBUG("out: ", expr);
  return Representation(expr, std::move(defs));
}

Z3Interfacing::Representation Z3Interfacing::getRepresentation(SATLiteral slit)
{
  CALL("Z3Interfacing::getRepresentation");
  BYPASSING_ALLOCATOR;


  //First, does this represent a ground literal
  Literal* lit = _sat2fo.toFO(slit);
  if(lit && lit->ground()){
    //cout << "getRepresentation of " << lit->toString() << endl;
    // Now translate it into an SMT object 
    try{
      bool nameExpression;
      auto repr = getz3expr(lit,nameExpression);

      if(nameExpression) {
        z3::expr bname = getNameExpr(slit.var()); 
        z3::expr naming = (bname == repr.expr);
        repr.defs.push(naming);
        repr.expr = bname;
        if(_showZ3){
          env.beginOutput();
          env.out() << "[Z3] add (naming): " << naming << std::endl;
          env.endOutput();
        }
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

SATClause* Z3Interfacing::getRefutation() {

    if(!_unsatCoreForRefutations)
      return PrimitiveProofRecordingSATSolver::getRefutation(); 

    ASS_EQ(_solver.check(),z3::check_result::unsat);

    z3::solver solver(_context);
    z3::params p(_context);
    p.set(":unsat-core", true);
    solver.set(p);

    SATClauseList* added = PrimitiveProofRecordingSATSolver::getRefutationPremiseList();
    SATClauseList::Iterator cit(added);
    unsigned n=0;
    vstring ps="$_$_$";

    DHMap<vstring,SATClause*> lookup;

    while(cit.hasNext()){
      SATClause* cl = cit.next();
      z3::expr z3clause = _context.bool_val(false);
      unsigned clen=cl->length();
      for(unsigned i=0;i<clen;i++){
        SATLiteral l = (*cl)[i];
        auto repr = getRepresentation(l); 
        for (auto def : repr.defs) {
          solver.add(def);
        }
        z3clause = z3clause || repr.expr;
      }
      vstring p = ps+Int::toString(n++);
      //cout << p << ": " << cl->toString() << endl;
      solver.add(z3clause,p.c_str());
      lookup.insert(p,cl);
    }

    // the new version of Z3 does not suppot unsat-cores?
    ALWAYS(solver.check() == z3::check_result::unsat);

    SATClauseList* prems = 0;

    z3::expr_vector  core = solver.unsat_core();
    for (unsigned i = 0; i < core.size(); i++) {
        z3::expr ci = core[i];
        vstring cip = Z3_ast_to_string(_context,ci);
        SATClause* cl = lookup.get(cip);
        SATClauseList::push(cl,prems);
        //std::cout << cl->toString() << "\n";
    }

    SATClause* refutation = new(0) SATClause(0);
    refutation->setInference(new PropInference(prems));

    return refutation; 
}



/**
 * Add axioms for quotient_t and remainder_t that will be treated
 * uninterpreted
 *
 **/
void Z3Interfacing::addTruncatedOperations(z3::expr e1, z3::expr e2, Interpretation qi, Interpretation ri, unsigned srt) 
{
  CALL("Z3Interfacing::addTruncatedOperations");
  
  z3::func_decl rem = z3Function(ri).decl;

  if (srt == Sorts::SRT_INTEGER) {
    z3::func_decl quot = z3Function(qi).decl;

    // e1 >= 0 & e2 > 0 -> e2 * quot(e1,e2) <= e1 & e2 * quot(e1,e2) > e1 - e2
    // e1 >= 0 & e2 < 0 -> e2 * quot(e1,e2) <= e1 & e2 * quot(e1,e2) > e1 + e2
    // e1  < 0 & e2 > 0 -> e2 * quot(e1,e2) >= e1 & e2 * quot(e1,e2) < e1 + e2
    // e1  < 0 & e2 < 0 -> e2 * quot(e1,e2) >= e1 & e2 * quot(e1,e2) < e1 - e2
    _solver.add(implies(e1 >= 0 && e2 > 0, e2 * quot(e1,e2) <= e1 && e2 * quot(e1,e2) > e1 - e2 ));
    _solver.add(implies(e1 >= 0 && e2 < 0, e2 * quot(e1,e2) <= e1 && e2 * quot(e1,e2) > e1 + e2 ));
    _solver.add(implies(e1 <  0 && e2 > 0, e2 * quot(e1,e2) >= e1 && e2 * quot(e1,e2) < e1 + e2 ));
    _solver.add(implies(e1 <  0 && e2 < 0, e2 * quot(e1,e2) >= e1 && e2 * quot(e1,e2) < e1 - e2 ));

    // e2 != 0 -> e2 * quot(e1,e2) + rem(e1,e2) = e1
    _solver.add(implies( e2 != 0, e2 * quot(e1,e2) + rem(e1,e2) == e1 ));
  } else {
    // e2 != 0 -> e2 * quot(e1,e2) + rem(e1,e2) = e1
    _solver.add(implies( e2!=0, e2 * truncate(e1/e2) + rem(e1,e2) == e1 ));
  }
} // void Z3Interfacing::addTruncatedOperations

void Z3Interfacing::addFloorOperations(z3::expr e1, z3::expr e2, Interpretation qi, Interpretation ri, unsigned srt)
{
  CALL("Z3Interfacing::addFloorOperations");
  

  z3::func_decl rem = z3Function(ri).decl;

  if (srt == Sorts::SRT_INTEGER) {
    z3::func_decl quot = z3Function(qi).decl;

    // e2 != 0 -> e2 * quot(e1,e2) <= e1 & e2*quot(e1,e2) > e1 - e2 
    // e2 != 0 -> e2 * quot(e1,e2) + rem(e1,e2) = e1
    _solver.add(implies(e2!=0, e2 * quot(e1,e2) <= e1 && e2 * quot(e1,e2) > e1 - e2 ));
    _solver.add(implies(e2!=0, e2 * quot(e1,e2) + rem(e1,e2) == e1 ));
  } else {
    // e2 != 0 -> e2 * quot(e1,e2) + rem(e1,e2) = e1
    _solver.add(implies( e2!=0, e2 * to_real(to_int(e1/e2)) + rem(e1,e2) == e1 ));
  }
}

Z3Interfacing::~Z3Interfacing()
{
  CALL("~Z3Interfacing")
  _sorts.clear();
  _toZ3.clear();
  _fromZ3.clear();
}


} // namespace SAT

#endif /** if VZ3 **/
