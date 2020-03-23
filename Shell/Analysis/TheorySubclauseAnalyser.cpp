
#include <iostream>
#include <algorithm>
#include <type_traits>
#include <unordered_map>
#include <functional>

#include "Debug/Assertion.hpp"

#include "Shell/Analysis/TheorySubclauseAnalyser.hpp"
#include "Lib/Allocator.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

using namespace Shell::Analysis;
using namespace std;
using namespace Kernel;
/* ================================================= */
/* =================== utilities =================== */
/* ================================================= */
//_LIBCPP_INLINE_VISIBILITY
//size_t operator()(const bitset<_Size>& __bs) const _NOEXCEPT
//{return __bs.__hash_code();}

#define DBG(...) cout << "[ dbg ]\t" << __VA_ARGS__ << endl;

/* begin macro_magic */
#define FIRST(a, ...) a
#define SECOND(a, b, ...) b

#define EMPTY()

#define EVAL(...) EVAL1024(__VA_ARGS__)
#define EVAL1024(...) EVAL512(EVAL512(__VA_ARGS__))
#define EVAL512(...) EVAL256(EVAL256(__VA_ARGS__))
#define EVAL256(...) EVAL128(EVAL128(__VA_ARGS__))
#define EVAL128(...) EVAL64(EVAL64(__VA_ARGS__))
#define EVAL64(...) EVAL32(EVAL32(__VA_ARGS__))
#define EVAL32(...) EVAL16(EVAL16(__VA_ARGS__))
#define EVAL16(...) EVAL8(EVAL8(__VA_ARGS__))
#define EVAL8(...) EVAL4(EVAL4(__VA_ARGS__))
#define EVAL4(...) EVAL2(EVAL2(__VA_ARGS__))
#define EVAL2(...) EVAL1(EVAL1(__VA_ARGS__))
#define EVAL1(...) __VA_ARGS__

#define DEFER1(m) m EMPTY()
#define DEFER2(m) m EMPTY EMPTY()()
#define DEFER3(m) m EMPTY EMPTY EMPTY()()()
#define DEFER4(m) m EMPTY EMPTY EMPTY EMPTY()()()()

#define IS_PROBE(...) SECOND(__VA_ARGS__, 0)
#define PROBE() ~, 1

#define CAT(a,b) a ## b

#define NOT(x) IS_PROBE(CAT(_NOT_, x))
#define _NOT_0 PROBE()

#define BOOL(x) NOT(NOT(x))

#define IF_ELSE(condition) _IF_ELSE(BOOL(condition))
#define _IF_ELSE(condition) CAT(_IF_, condition)

#define _IF_1(...) __VA_ARGS__ _IF_1_ELSE
#define _IF_0(...)             _IF_0_ELSE

#define _IF_1_ELSE(...)
#define _IF_0_ELSE(...) __VA_ARGS__

#define HAS_ARGS(...) BOOL(FIRST(_END_OF_ARGUMENTS_ __VA_ARGS__)())
#define _END_OF_ARGUMENTS_() 0

#define MAP(m, first, ...)           \
  m(first)                           \
  IF_ELSE(HAS_ARGS(__VA_ARGS__))(    \
    DEFER2(_MAP)()(m, __VA_ARGS__)   \
  )(                                 \
    /* Do nothing, just terminate */ \
  )
#define _MAP() MAP
/* end macro_magic */

#define HASH_CODE(item) \
  code ^= std::hash<decltype(item)>{}(item);

#define TIE_CMP(CLASS, ...) \
  inline friend bool operator<(const CLASS& l, const CLASS& r) { \
    auto toTup = [](const CLASS& x) {return std::tie(__VA_ARGS__);}; \
    return toTup(l) < toTup(r); \
  } \
    \
  inline friend bool operator==(const CLASS& l, const CLASS& r) { \
    auto toTup = [](const CLASS& x) {return std::tie(__VA_ARGS__);}; \
    return toTup(l) == toTup(r); \
  } \
  _IMPL_HASH(CLASS, __VA_ARGS__)

#define HASH_BODY(CLASS, ...) \
  auto code = 786532; \
  EVAL(MAP(HASH_CODE,__VA_ARGS__)) \
  return code; \

#define _IMPL_HASH(CLASS, ...) \
  size_t hash_code() const { \
      const CLASS& x = *this; \
      HASH_BODY(CLASS, __VA_ARGS__) \
  } \
  \
  friend struct std::hash<CLASS>;

#define IMPL_HASH(CLASS, ...) \
  namespace std \
  { \
      template<> struct hash<CLASS> \
      { \
          std::size_t operator()(CLASS const& x) const noexcept \
          { HASH_BODY(CLASS, __VA_ARGS__) } \
      }; \
  }

template<class A>
struct std::hash<vvec<refw<A>>>
{
    size_t operator()(const vvec<refw<A>>& xs) const noexcept {
        size_t code = 827471209;
        for (auto x : xs) {
            code ^= std::hash<A>{}(x.get());
        }
        return code;
    }

};



class AbsSymbol {
protected:
    unsigned functor;

    explicit AbsSymbol(unsigned functor) : functor(functor) {}

    virtual Signature::Symbol &symbol() const = 0;

public:
    friend ostream &operator<<(ostream &out, const AbsSymbol &s);

    TIE_CMP(AbsSymbol, x.functor)
};
IMPL_HASH(AbsSymbol, x.functor)

ostream &operator<<(ostream &out, const AbsSymbol &s) {
    out << s.symbol().name();
    return out;
}

Theory::Interpretation interpretation(Signature::Symbol &sym) {
    return sym.getInterpretation();
//    return sym.interpreted()
//           ? (static_cast<Signature::InterpretedSymbol &>(sym).getInterpretation())
//           : Interpretation::INVALID_INTERPRETATION;
}

class Predicate : public AbsSymbol {
public:
    explicit Predicate(unsigned functor) : AbsSymbol(functor) {}

    Signature::Symbol &symbol() const override {
        return *env.signature->getPredicate(functor);
    }
    TIE_CMP(Predicate, x.functor)
};
IMPL_HASH(Predicate, x.functor)



class Function : public AbsSymbol {
public:
    explicit Function(unsigned functor) : AbsSymbol(functor) {}

    Signature::Symbol &symbol() const override {
        return *env.signature->getFunction(functor);
    }


    Theory::Interpretation interpret() const {
        Signature::Symbol &sym = symbol();
        ASS(!sym.numericConstant())
        return sym.interpreted()
               ? (static_cast<Signature::InterpretedSymbol &>(sym).getInterpretation())
               : Interpretation::INVALID_INTERPRETATION;
    }

    bool isPlus() const {
        return Theory::isPlus(interpret());
    }

    bool isTimes() const {
        return Theory::isTimes(interpret());
    }

    bool isAssoc() const {
        auto i = interpret();
        return Theory::isPlus(i) || Theory::isTimes(i);
    }

    bool isCommut() const {
        auto i = interpret();
        return Theory::isPlus(i) || Theory::isTimes(i);
    }

    bool leftDistributiveOver(const Function &other) const {
        return Theory::isTimes(this->interpret()) && Theory::isPlus(other.interpret());
    }

    bool isInterpretedConstant() const {
        return Theory::instance()->isInterpretedConstant(functor);
    }

    bool isUnaryMinus() const {
        return Theory::isUnaryMinus(this->interpret());
    }
    TIE_CMP(Function, x.functor)
};
IMPL_HASH(Function, x.functor)

class AbsTerm {
public:
    static AbsTerm &from(TermList &t);

    friend ostream &operator<<(ostream &out, AbsTerm &t);

    virtual void normalize() = 0;

    virtual void distributeLeft() = 0;

    virtual void distributeRight() = 0;

    virtual void mergeAssoc() = 0;

    virtual void sortCommut() = 0;

    virtual void pushMinus() = 0;

private:
    virtual void write(ostream &out) const = 0;


};


class AbsVarTerm : public AbsTerm {
public:
    CLASS_NAME(AbsVarTerm);

    USE_ALLOCATOR(AbsVarTerm);

private:
    unsigned _var;

public:
    AbsVarTerm(unsigned var) : _var(var) {}

    void write(ostream &out) const override {
        out << "X" << _var;
    }

    void normalize() override {}

    void mergeAssoc() override {}

    void sortCommut() override {}

    void distributeLeft() override {}

    void distributeRight() override {}

    void pushMinus() override {}

    TIE_CMP(AbsVarTerm, x._var)
};
IMPL_HASH(AbsVarTerm, x._var)

/** Term of associative commutative function */
class ACTerm : public AbsTerm {
public:
    CLASS_NAME(ACTerm);

    USE_ALLOCATOR(ACTerm);

private:
    Function _fun;
    typedef vvec<refw<AbsTerm> > args_t;
    args_t _args;

public:

    ACTerm(Function fun, std::initializer_list<refw<AbsTerm> > ts)
            : _fun(fun), _args(args_t(ts)) {
    }

    ACTerm(Term &term)
            : _fun(term.functor()), _args(args_t()) {
        for (auto i = 0; i < term.arity(); i++) {
            auto &t = AbsTerm::from(*term.nthArgument(i));
            _args.push_back(t);
        }
        ASS(!term.isSpecial())
        ASS(!term.isLiteral())
        ASS_REP(!_fun.isUnaryMinus() || _args.size() == 1, term.functionName())
    }

    void integrityCheck() {
        for (auto a : _args) {

            if (auto x = dynamic_cast<ACTerm *>(&a.get())) {
                x->integrityCheck();
            }
//            a.get()
//             .match([](ACTerm&  t) -> void { t.integrityCheck(); },
//                    [](AbsTerm& t) -> void {} );

        }
        ASS(!_fun.isPlus() || _args.size() > 0)
    }

    void normalize() override {
        this->integrityCheck();
        pushMinus();
        this->integrityCheck();
        distributeLeft();
        this->integrityCheck();
        distributeRight();
        this->integrityCheck();
        mergeAssoc();
        this->integrityCheck();
        sortCommut();
        this->integrityCheck();
    }

    void pushMinus() override {
        CALL("ACTerm::pushMinus")
        if (_fun.isUnaryMinus()) {
            ASS(_args.size() == 1);
            if (auto x = dynamic_cast<ACTerm *>(&_args[0].get())) {
                auto minus = _fun;
                if (x->_fun.isPlus()) {
                    _fun = x->_fun;
                    /*  -(x + y + ..) => (-x) + (-y) + ...  */
                    _args.clear();
                    _args.reserve(x->_args.size());
                    for (AbsTerm &a : x->_args) {
                        _args.push_back(*new ACTerm(minus, {a}));
                    }
                    x->_args.clear();
                    delete x;

                } else if (x->_fun.isTimes()) {
                    /*  -(x * y * ..) => (-x) * y * ...  */
                    x->_args[0] = *new ACTerm(minus, {x->_args[0]}); // TODO: add * (-1) instead
                }
            }
        }
        for (auto a : _args) {
            a.get().pushMinus();
        }
    }

    void sortCommut() override {
        CALL("ACTerm::sortCommut")
        for (auto a : _args) {
            a.get().sortCommut();
        }
        if (_fun.isCommut())
            sort(_args.begin(), _args.end());
    }

    void mergeAssoc() override {
        CALL("ACTerm::mergeAssoc")
        for (auto arg : _args) {
            arg.get().mergeAssoc();
        }

        if (_fun.isAssoc()) { //TODO performance
            vvec<refw<AbsTerm> > new_args;
            new_args.reserve(_args.size());
            for (int i = 0; i < _args.size(); i++) {
                auto arg = dynamic_cast<ACTerm *>(&_args[i].get());
                if (arg && arg->_fun == _fun) {
                    /* merge */
                    new_args.reserve(new_args.capacity() + arg->_args.size() - 1);
                    for (auto arg_ : arg->_args) {
                        new_args.push_back(arg_);
                    }
                    arg->_args.clear();
//                    delete arg;
                } else {
                    /* do not merge */
                    new_args.push_back(_args[i]);
                }
            }
            _args.clear();
            _args = new_args;
        }
    }

    void distributeLeft() override {
        CALL("ACTerm::distributeLeft")
        distribute(0, 1, [](AbsTerm &x) { x.distributeLeft(); });
    }

    void distributeRight() override {
        CALL("ACTerm::distributeRight")
        distribute(1, 0, [](AbsTerm &x) { x.distributeRight(); });
    }

    template<class Fn>
    void distribute(size_t fst, size_t snd, Fn rec) {
        if (_args.size() == 2) {
            AbsTerm &l = _args[fst];
            AbsTerm &r_ = _args[snd];
            auto r = dynamic_cast<ACTerm *>(&r_);

            if (r && _fun.leftDistributiveOver(r->_fun)) {
                /*   a * (b + c)  => (a * b) + (a * c)
                 *   l   -- r --     -- x --   -- r --
                 *   -- this ---     ------ this -----
                 */
                ASS(r->_args.size() == 2);
                auto mul = _fun;
                auto add = r->_fun;
                auto &a = l;
                auto &b = r->_args[fst];
                auto &c = r->_args[snd];

                auto &x = *new ACTerm(mul, {a, b});
                x._args[fst] = a;
                x._args[snd] = b;

                r->_fun = mul;
                r->_args[fst] = a;
                r->_args[snd] = c;

                this->_fun = add;
                this->_args[fst] = x;
                this->_args[snd] = *r;

                rec(x);
                rec(*r);
            } else {

                rec(l);
                rec(r_);
            }
        } else {
            for (AbsTerm &a : _args) {
                rec(a);
            }
        }
    }


public:
    virtual void write(ostream &out) const override {
        out << _fun;
        if (_args.size() > 0) {
            out << "(";
            auto iter = _args.begin();
            out << *iter;
            iter++;
            while (iter != _args.end()) {
                out << ", " << *iter;
                iter++;
            }
            out << ")";
        }
    }
    TIE_CMP(ACTerm, x._fun, x._args)
};
IMPL_HASH(ACTerm, x._fun, x._args)


IMPL_HASH(AbsTerm,
          size_t( dynamic_cast<const AbsVarTerm*>(&x) ? (static_cast<const AbsVarTerm&>(x).hash_code())
        : dynamic_cast<const ACTerm*>(&x) ? (static_cast<const ACTerm&>(x).hash_code())
                                                                                                                                        : 0)
)

Signature::Symbol &fnSym(const Term &t) {
    return *env.signature->getFunction(t.functor());
}

bool interpretedFun(const Term &t) {
    return fnSym(t).interpreted();
}

AbsTerm &AbsTerm::from(TermList &t) {
    if (t.isVar()) {
        t.var();
        return *new AbsVarTerm(t.var());
    } else {
        return *new ACTerm(*t.term());
    }
}


#define TRY_CMP(OP, CLASS) \
  { \
    if (auto l = dynamic_cast<const CLASS*>(&lhs)) { \
      if (auto r = dynamic_cast<const CLASS*>(&rhs)) { \
        const CLASS& l_ = *l; \
        const CLASS& r_ = *r; \
        if( l_ < r_) \
          return true; \
      } else { \
        return true; \
      } \
    } \
  }

bool operator<(const AbsTerm &lhs, const AbsTerm &rhs) {
    TRY_CMP(<, AbsVarTerm)
    TRY_CMP(<, ACTerm)
    return false;
}

bool operator==(const AbsTerm &lhs, const AbsTerm &rhs) {
    TRY_CMP(==, AbsVarTerm)
    TRY_CMP(==, ACTerm)
    return false;
}

ostream &operator<<(ostream &out, AbsTerm &t) {
    t.write(out);
    return out;
}

/* utility datatypes */
struct AbsLiteral {
    CLASS_NAME(AbsLiteral)
    USE_ALLOCATOR(AbsLiteral)

    bool positive;
    Predicate predicate;
    vvec<refw<AbsTerm> > terms; // TODO destructor

    explicit AbsLiteral(Literal *l)
            : positive(l->isPositive()), predicate(l->functor()), terms(vvec<refw<AbsTerm> >()) {
        terms.reserve(l->arity());
        for (auto i = 0; i < l->arity(); i++) {
            auto &t = AbsTerm::from(*l->nthArgument(i));
            t.normalize();
            terms.push_back(t);
        }
    }

    TIE_CMP(AbsLiteral, x.predicate, x.positive, x.terms);
};
IMPL_HASH(AbsLiteral, x.predicate, x.positive, x.terms);


ostream& operator<<(ostream &out, AbsLiteral &lit) {
    out << lit.predicate << "( ";
    for (auto t : lit.terms) {
        out << t << " ";
    }
    out << ")";
    return out;
}

class AbsTheoryClause {
    vvec<rc<AbsLiteral> > _lits;
public:
    CLASS_NAME(AbsTheoryClause)
    USE_ALLOCATOR(AbsTheoryClause)

    AbsTheoryClause(vvec<Literal *> &ls) : _lits(vvec<rc<AbsLiteral> >()) {
        CALL("AbsTheoryClause::AbsTheoryClause()")
        _lits.reserve(ls.size());
        for (auto l : ls) {
            _lits.push_back(rc<AbsLiteral>(new AbsLiteral(l)));
        }
    }

    AbsTheoryClause(AbsTheoryClause &&c) : _lits(std::move(c._lits)) {
    }

    AbsTheoryClause &operator=(AbsTheoryClause &&other) {
        _lits = std::move(other._lits);
        return *this;
    }

    const vvec<rc<AbsLiteral> > &literals() const { return _lits; }
};

ostream &operator<<(ostream &out, AbsTheoryClause const &t) {
    for (auto x : t.literals()) {
        out << x << " ";
    }
    return out;
}


/**
 * returns whether @b t points to a theory term. A theory term is a term where the outer most function symbol is an interpreted one.
 *
 * Note that the typename TermList is deceptive here. t is actually a pointer (~= iterator pointing to) to an element in a TermList.
 */
bool isTheoryTerm_L(const TermList &t) {
    if (t.isTerm()) {
        return interpretedFun(*t.term());
        // Signature::Symbol& sym = *env.signature->getFunction(t.term()->functor());
        // return sym.interpreted();
    } else {
        ASS(t.isVar());
        return false;
    }
}

/**
 * returns whether @b lit is a theory literal. A literal @b lit is a theory literal iff (any of)
 * - the predicate symbol is interpreted
 * - it is an equality literal with at least on theory term
 */
bool isTheoryLiteral(Literal &lit) {
    Signature::Symbol &sym = *env.signature->getPredicate(lit.functor());
    const TermList *args = lit.args();
    return sym.interpreted() && (!lit.isEquality() || isTheoryTerm_L(*args) || isTheoryTerm_L(*args->next()));
}

/**
 * Returns the maximum theory subclause. The maximum theory subclause consists of all theory literals (see @b isTheoryLiteral)
 * that are contained in @b c.
 */
AbsTheoryClause &maxTheorySubclause(Clause const &c) {
    vvec<Literal *> lits;
    for (int i = 0; i < c.length(); i++) {
        if (isTheoryLiteral(*c[i]))
            lits.push_back(c[i]);
    }
    return *new AbsTheoryClause(lits);
}

/* TheorySubclauseAnalyser implementation */

TheorySubclauseAnalyser::TheorySubclauseAnalyser()
        : _literals(literals_type())
        {}


TheorySubclauseAnalyser::~TheorySubclauseAnalyser() {

}

void TheorySubclauseAnalyser::addClause(Clause &c) {
    CALL("TheorySubclauseAnalyser::addClause")
    if (!c.isTheoryAxiom() && !c.isTheoryDescendant()) {
        auto &scl = maxTheorySubclause(c);
        for (auto l : scl.literals()) {
            _literals.insert(l);
        }
    }

}

void TheorySubclauseAnalyser::dumpStats(ostream &out) const {
  auto& mymap = _literals._content;
    for ( auto it = mymap.begin(); it != mymap.end(); ++it ) {
        auto pair = *it;
        auto size = pair.second.size();
        ASS_REP(size > 0, size);
        out << size << ":\t" << *pair.first << endl;
    }
}

