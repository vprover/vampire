/***********************************************************************************[SolverTypes.h]
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/


#ifndef SMTSubsumption_Minisat_SolverTypes_h
#define SMTSubsumption_Minisat_SolverTypes_h

#include "SMTSubsumption/minisat/Global.h"


namespace SMTSubsumption { namespace Minisat {

//=================================================================================================
// Variables, literals, clause IDs:


// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef int Var;
#define var_Undef (-1)


class Lit {
    // Values:
    // lit_Undef: -2
    // lit_Error: -1
    //  Lit(0): 0
    // ~Lit(0): 1
    //  Lit(1): 2
    // ~Lit(1): 3
    //    :
    //    :
    int     x;
public:
    Lit() : x(2*var_Undef) {}   // (lit_Undef)
    explicit Lit(Var var, bool negative = false) : x((var+var) + (int)negative) {}
    friend Lit operator ~ (Lit p);

    friend bool sign  (Lit p);
    friend int  var   (Lit p);
    friend int  index (Lit p);
    friend Lit  toLit (int i);
    friend Lit  unsign(Lit p);
    friend Lit  id    (Lit p, bool sgn);

    friend bool operator == (Lit p, Lit q);
    friend bool operator <  (Lit p, Lit q);

    bool isNegative() const { return sign(*this); }
    bool isPositive() const { return !isNegative(); }

    uint hash() const { return (uint)x; }
};
inline Lit operator ~ (Lit p) { Lit q; q.x = p.x ^ 1; return q; }
inline bool sign  (Lit p) { return p.x & 1; }   // true iff negative
inline int  var   (Lit p) { return p.x >> 1; }
inline int  index (Lit p) { return p.x; }                // A "toInt" method that guarantees small, positive integers suitable for array indexing.
inline Lit  toLit (int i) { Lit p; p.x = i; return p; }  // Inverse of 'index()'.
inline Lit  unsign(Lit p) { Lit q; q.x = p.x & ~1; return q; }
inline Lit  id    (Lit p, bool sgn) { Lit q; q.x = p.x ^ (int)sgn; return q; }
inline bool operator == (Lit p, Lit q) { return index(p) == index(q); }
inline bool operator != (Lit p, Lit q) { return !(p == q); }
inline bool operator <  (Lit p, Lit q) { return index(p)  < index(q); }  // '<' guarantees that p, ~p are adjacent in the ordering.

const Lit lit_Undef(var_Undef, false);  // }- Useful special constants.
const Lit lit_Error(var_Undef, true );  // }

inline int toDimacs(Lit p) { return sign(p) ? -var(p) - 1 : var(p) + 1; }

inline std::ostream& operator<<(std::ostream& o, Lit l)
{
  if (l.isNegative()) {
    o << '~';
  }
  o << var(l);
  return o;
}


//=================================================================================================
// Clause -- a simple class for representing a clause:


class Clause {
    uint    size_learnt;
    Lit     data[1];

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    Clause(bool learnt, const vec<Lit>& ps)
    {
        size_learnt = (ps.size() << 1) | (int)learnt;
        for (int i = 0; i < ps.size(); i++) data[i] = ps[i];
        if (learnt) activity() = 0;
    }

    Clause(Clause&) = delete;
    Clause(Clause&&) = delete;
    Clause& operator=(Clause&) = delete;
    Clause& operator=(Clause&&) = delete;

public:
    // -- use this function instead:
    friend Clause* Clause_new(bool learnt, const vec<Lit>& ps);

    int       size        ()      const { return size_learnt >> 1; }
    bool      learnt      ()      const { return size_learnt & 1; }
    Lit       operator [] (int i) const { return data[i]; }
    Lit&      operator [] (int i)       { return data[i]; }
    float&    activity    ()      const { return *((float*)&data[size()]); }  // TODO remove activity? since we are not doing any clause deletion
};

inline Clause* Clause_new(bool learnt, const vec<Lit>& ps)
{
    static_assert(sizeof(Lit)   == sizeof(uint), "unexpected size of Lit");
    static_assert(sizeof(float) == sizeof(uint), "unexpected size of float");
    void* mem = xmalloc<char>(sizeof(Clause) - sizeof(Lit) + sizeof(uint)*(ps.size() + (int)learnt));
    return new (mem) Clause(learnt, ps);
}



/// AtMostOne constraint
class AtMostOne
{
  private:
    int m_size;
    Lit m_data[1];

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    AtMostOne(vec<Lit> const& ls)
      : m_size{ls.size()}
    {
      for (int i = 0; i < ls.size(); ++i) {
        m_data[i] = ls[i];
      }
    }

    AtMostOne(AtMostOne&) = delete;
    AtMostOne(AtMostOne&&) = delete;
    AtMostOne& operator=(AtMostOne&) = delete;
    AtMostOne& operator=(AtMostOne&&) = delete;

  public:
    /// Create new AtMostOne constraint over the given literals.
    /// The given vector should contain at least two literals,
    /// and the variables of the given literals should be pairwise distinct.
    static AtMostOne* from_literals(vec<Lit> const& ls)
    {
      assert(ls.size() >= 2);  // otherwise this constraint is somewhat useless
      void* mem = xmalloc<char>(sizeof(AtMostOne) + sizeof(Lit)*(ls.size() - 1));
      return new (mem) AtMostOne(ls);
    }

    int size() const
    {
      return m_size;
    }

    Lit operator[](int i) const
    {
      assert(0 <= i && i < m_size);
      return m_data[i];
    }

    Lit& operator[](int i)
    {
      assert(0 <= i && i < m_size);
      return m_data[i];
    }
};


//=================================================================================================
// GClause -- Generalize clause:


// Either a pointer to a clause or a literal.
class GClause {
  private:
    using data_t = uintptr_t;

    // We discriminate on the lowest bits of data.
    // This works because pointers are word-aligned,
    // which means the 3 lowest bits are always 0 (on 64-bit architectures),
    // and thus can be used for additional information (cf. 'pointer tagging').
    data_t data;

    // TODO maybe we can do with 2-bit tags instead
    static_assert(sizeof(void*) >= 8, "3-bit tags only work on 64-bit architectures");

  public:
    enum Tag : data_t
    {
      Tag_Clause    = 0b000,
      Tag_Lit       = 0b001,
      Tag_AtMostOne = 0b011,

      Tag_Mask      = 0b111,
    };

    Tag tag() const
    {
      return static_cast<Tag>(data & Tag_Mask);
    }

    bool operator == (GClause c) const { return data == c.data; }
    bool operator != (GClause c) const { return data != c.data; }

    bool isNull() const { return data == 0; }

    explicit GClause(nullptr_t)
      : data{0}
    { }


    // Literals

    explicit GClause(Lit l)
      : data{(static_cast<data_t>(index(l)) << 3) + Tag_Lit}
    {
      static_assert(
        (std::numeric_limits<data_t>::max() >> 3) > std::numeric_limits<decltype(index(l))>::max(),
        "data_t is not large enough to hold all Lit values");
      assert(index(l) >= 0);
      assert(isLit());
      assert(lit() == l);
    }

    bool isLit() const
    {
      return tag() == Tag_Lit;
    }

    Lit lit() const
    {
      assert(isLit());
      return toLit(data >> 3);
    }


    // Clauses

    explicit GClause(Clause* cl)
      : data{reinterpret_cast<data_t>(cl) + Tag_Clause}
    {
      assert((reinterpret_cast<data_t>(cl) & Tag_Mask) == 0);
      assert(isClause());
      assert(clause() == cl);
    }

    bool isClause() const
    {
      return tag() == Tag_Clause;
    }

    Clause* clause() const
    {
      static_assert(Tag_Clause == 0, "Need to add mask if clause tag is changed to non-zero");
      assert(isClause());
      return reinterpret_cast<Clause*>(data & ~Tag_Clause);  // TODO: check if that is optimized away
    }


    // AtMostOne

    explicit GClause(AtMostOne* x)
      : data{reinterpret_cast<data_t>(x) + Tag_AtMostOne}
    {
      assert((reinterpret_cast<data_t>(x) & Tag_Mask) == 0);
      assert(isAtMostOne());
      assert(atMostOne() == x);
    }

    bool isAtMostOne() const
    {
      return tag() == Tag_AtMostOne;
    }

    AtMostOne* atMostOne() const
    {
      assert(isAtMostOne());
      return reinterpret_cast<AtMostOne*>(data & ~Tag_Mask);
    }
};

inline GClause GClause_new(Lit p)     { return GClause(p); }
inline GClause GClause_new(Clause* c) { return GClause(c); }

#define GClause_NULL GClause(nullptr)


} }

//=================================================================================================
#endif
