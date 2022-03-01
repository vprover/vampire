#include "QKbo.hpp"
#include "Term.hpp"
#include "NumTraits.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Lib/Option.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/OrderingUtils.hpp"
#include "Theory.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel {


QKbo::QKbo(Precedence prec) 
  : _prec(std::move(prec))
  , _shared(nullptr)
  , _kbo(
      KboWeightMap<FuncSigTraits>::dflt(),
      KboWeightMap<PredSigTraits>::dflt(),
      _prec.funPrec(),
      _prec.predPrec(),
        DArray<int>(), /* <- pred levels will never be used */
        /* reverseLCM */ false
      )
{
}

class SummandIter 
{
  unsigned _plus;
  Stack<TermList> _work;
public:
  SummandIter(TermList t) 
    : _plus(t.isVar() ? 0 
                      : tryNumTraits([&](auto numTraits) { 
                        if (numTraits.sort() == SortHelper::getResultSort(t.term())) {
                          return Option<unsigned>(numTraits.addF());
                        } else {
                          return Option<unsigned>();
                        } }).unwrap())
    , _work({ t }) {  }

  DECL_ELEMENT_TYPE(TermList);

  bool hasNext() const 
  { return !_work.isEmpty(); }

  TermList next() 
  {
    while (_work.top().isTerm() && _work.top().term()->functor() == _plus) {
      auto t = _work.pop();
      _work.push(*t.term()->nthArgument(0));
      _work.push(*t.term()->nthArgument(1));
    }
    return _work.pop();
  }
};


auto iterSummands(TermList t)
{ return iterTraits(SummandIter(t)); }


using MulExtMemo = DArray<Option<Ordering::Result>>;

RationalConstantType rat(IntegerConstantType n) { return RationalConstantType(n, 1); };
template<class T> RationalConstantType rat(T n) { return RationalConstantType(n);    };

QKbo::Result QKbo::compare(Literal* l1_, Literal* l2_) const 
{
  CALL("QKbo::compare(Literal* l1_, Literal* l2_) const")
  auto l1 = LaLpo::Lit(l1_);
  auto l2 = LaLpo::Lit(l2_);


  if (!l1.interpreted() && l2.interpreted()) {
    return Ordering::Result::GREATER;

  } else if (l1.interpreted() && !l2.interpreted()) {
    return Ordering::Result::LESS;

  } else if (!l1.interpreted() && !l2.interpreted()) {

    if (l1.orig->functor() != l2.orig->functor()) {
      return Ordering::fromComparison(_prec.cmpPred(l1.orig->functor(), l2.orig->functor()));

    } else {
      auto lex = OrderingUtils::lexExt(argIter(l1.orig), argIter(l2.orig), [&](auto& l, auto& r) { return compare(l,r); } );
      if (lex == Result::EQUAL) {
        return l1.orig->isPositive() == l2.orig->isPositive() 
          ? Result::EQUAL
          : (l1.orig->isPositive() ? Result::LESS 
                                   : Result::GREATER);
      } else {
        return lex;
      }
    }

  } else {

    ASS(l1.interpreted() && l2.interpreted())

    auto cmpPreds =  [](auto l, auto r) 
    { 
      auto cmpSorts = [](auto l, auto r) {
        return l.sort() == r.sort() ? Result::EQUAL
             : l.sort() <  r.sort() ? Result::LESS
             :                        Result::GREATER;
      };
      auto unsorted = Ordering::fromComparison(Int::compare((int)l.pred, (int)r.pred));
      return unsorted == Ordering::EQUAL ? cmpSorts(l,r) 
                                         : unsorted; 
    };

    auto terms = [&](auto s) {
      return tryNumTraits([&](auto numTraits) { 
            if (numTraits.sort() == s.sort()) {
             auto sum = *s.orig->nthArgument(0) == numTraits.constantTl(0) 
               ? *s.orig->nthArgument(1) 
               : *s.orig->nthArgument(0);
             return Option<FlatSum>(flatWithCoeffs(sum));
            } else {
              return Option<FlatSum>();
            }
        })
      || FlatSum {
          make_pair(some(*s.orig->nthArgument(0)), rat(1)), 
          make_pair(some(*s.orig->nthArgument(1)), rat(1)), 
        };
    };

    auto cmp = cmpSum(terms(l1), terms(l2));
    if (cmp != Ordering::EQUAL) return cmp;
    else return cmpPreds(l1, l2);
  }
}

bool uninterpretedFun(Term* t) {
  auto f = t->functor();
  return !forAnyNumTraits([&](auto numTraits) -> bool {
      return f == numTraits.addF()
      || (f == numTraits.mulF() && numTraits.isNumeral(*t->nthArgument(0)))
      || numTraits.isNumeral(t);
  });
}


auto toNumeralMul(TermList t) -> std::tuple<Option<TermList>, RationalConstantType> {
  CALL("toNumeralMul(TermList t)")
  if (t.isVar()) {
    return make_tuple(Option<TermList>(t), rat(1));
  } else {
    auto term = t.term();
    auto f = term->functor();
    auto sort = SortHelper::getResultSort(term);
    return tryNumTraits([&](auto numTraits) {
        if (sort != numTraits.sort()) {
          return Option<std::tuple<Option<TermList>, RationalConstantType>>();

        } else if (f == numTraits.mulF() && numTraits.isNumeral(*term->nthArgument(0))) {
          /* t = k * t' ( for some numeral k ) */
          return some(make_tuple(
                some(*term->nthArgument(1)),  /* <- t' */
                rat(numTraits.tryNumeral(*term->nthArgument(0)).unwrap()) /* <- k */
                ));

        } else if (numTraits.isNumeral(t)) {
          /* t is a numeral */
          return some(make_tuple(
                Option<TermList>(), 
                rat(numTraits.tryNumeral(t).unwrap())
                ));

        } else {
          /* t is uninterpreted */
          return some( make_tuple(Option<TermList>(t), RationalConstantType(1)));
        }
    }).unwrap();
  }
}


Stack<TermList> flatWithoutCoeffs(TermList t) 
{
  Stack<TermList> out;
  for (auto ti : iterSummands(t)) {
    auto term = std::get<0>(toNumeralMul(ti));
    if (term.isSome()) {
      out.push(term.unwrap());
    }
  }
  return out;
}


QKbo::FlatSum QKbo::flatWithCoeffs(TermList t) const
{ 
  CALL("QKbo::flatWithCoeffs(TermList t) const")

  Stack<std::tuple<Option<TermList>, RationalConstantType>> out;
  for (auto ti : iterSummands(t)) {
    out.push(toNumeralMul(ti));
  }
  return out;
}


Ordering::Result QKbo::compare(TermList s, TermList t) const 
{
  CALL("QKbo::compare(TermList, TermList) const")
  if (s.isVar() && t.isVar()) 
    return s == t ? Ordering::EQUAL : Ordering::INCOMPARABLE;

  auto as = abstr(s);
  auto at = abstr(t);
  if (as.isNone() || at.isNone()) {
    return Ordering::Result::INCOMPARABLE;

  } else {
    auto cmp = _kbo.compare(as.unwrap(), at.unwrap());
    switch (cmp) {
      case Ordering::GREATER:      return Ordering::GREATER;
      case Ordering::LESS:         return Ordering::LESS;
      case Ordering::INCOMPARABLE: return Ordering::INCOMPARABLE;
      case Ordering::EQUAL: 
        ASS_EQ(as.unwrap(), at.unwrap())
        return cmpNonAbstr(s,t);
      default:;
    }
    ASSERTION_VIOLATION
  }
}


Ordering::Result QKbo::cmpSum(FlatSum const& l, FlatSum const& r) const {

  auto cmpUnint = [&](auto l_, auto r_) { 
    auto l = std::get<0>(l_);
    auto r = std::get<0>(r_);
         if (l.isNone() && r.isNone()) return Ordering::EQUAL;
    else if (l.isNone() && r.isSome()) return Ordering::LESS;
    else if (l.isSome() && r.isNone()) return Ordering::GREATER;
    else return this->compare(l.unwrap(), r.unwrap()); 
  };
  auto cmpWithCoeffs = [&](auto l, auto r) -> Ordering::Result { 
    auto c  = cmpUnint(l,r);
    if (c != Ordering::EQUAL) return c;
    return fromComparison(RationalConstantType::comparePrecedence(std::get<1>(l), std::get<1>(r)));
  };

  auto cmp = OrderingUtils::mulExt(l, r, cmpUnint);

  if (cmp != Ordering::EQUAL) {
    // 2.b)i. interpreted stuff
    return cmp;

  } else {
    // 2.b)ii. interpreted stuff
    return OrderingUtils::mulExt(l, r, cmpWithCoeffs);
  }
}


/// case 2. precondition: we know that abstr(s) == abstr(t)
Ordering::Result QKbo::cmpNonAbstr(TermList s, TermList t) const 
{
  CALL("QKbo::cmpNonAbstr(TermList, TermList) const")
  if (s.isTerm() && t.isTerm() 
      && s.term()->functor() == t.term()->functor() 
      && uninterpretedFun(s.term())) {
    // 2.a) LEX
    return OrderingUtils::lexExt(argIter(s.term()), argIter(t.term()), 
          [&](auto l, auto r) { return this->compare(l,r); });

  } else {
    // 2.b) interpreted stuff
    return cmpSum(flatWithCoeffs(s), flatWithCoeffs(t));
  }
}
Option<TermList> QKbo::abstr(TermList t) const 
{
  CALL("QKbo::abstr(TermList t) const ")
  using Out = Option<TermList>;
  if (t.isVar()) {
    return Option<TermList>(t);
  } else {
    auto term = t.term();
    auto f = term->functor();
    auto res = tryNumTraits([&](auto numTraits) -> Option<Out> {
        if (numTraits.addF() == f) {
          /* t = t1 + ... + tn */
          auto flat = flatWithoutCoeffs(t);
          auto strictMax = OrderingUtils::strictlyMax(flat, [&](auto l, auto r) { return _kbo.compare(l,r); });
          return Option<Out>(strictMax);

        } else if (numTraits.mulF() == f && numTraits.isNumeral(*term->nthArgument(0))) {
          /* t = k * t' */
          return some(abstr(*term->nthArgument(1)));

        } else if (numTraits.isNumeral(t)) {
          /* t is a numeral */
          return some(some(numTraits.zero()));

        } else {
          return Option<Out>();
        }
    });
    if (res.isSome()) {
      return res.unwrap();
    } else {
      Stack<TermList> args(term->arity());
      for (auto a : argIter(term)) {
        auto abs = abstr(a);
        if (abs.isNone()) {
          return abs;
        } else {
          args.push(abs.unwrap());
        }
      }
      return Out(TermList(Term::create(term, args.begin())));
    }
  }
}

void QKbo::show(ostream& out) const 
{ _prec.show(out); }

} // Kernel
