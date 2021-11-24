inline DArray<int> funcPrec() {
  unsigned num = env.signature->functions();
  DArray<int> out(num);
  out.initFromIterator(getRangeIterator(0u, num));
  return out;
}

inline DArray<int> predPrec() {
  unsigned num = env.signature->predicates();
  DArray<int> out(num);
  out.initFromIterator(getRangeIterator(0u, num));
  return out;
}

inline DArray<int> predLevels() {
  DArray<int> out(env.signature->predicates());
  out.init(out.size(), 1);
  return out;
}

using namespace Kernel;

template<class SigTraits>
inline KboWeightMap<SigTraits> toWeightMap(unsigned introducedSymbolWeight, KboSpecialWeights<SigTraits> ws, const Map<unsigned, KboWeight>& xs, unsigned sz) 
{
  auto df = KboWeightMap<SigTraits>::dflt();
  df._specialWeights = ws;

  DArray<KboWeight> out(sz);
  for (unsigned i = 0; i < sz; i++) {
    auto w = xs.getPtr(i);
    out[i] = w == NULL ? df.symbolWeight(i) : *w;
  }
  return  {
    ._weights = out,
    ._introducedSymbolWeight = introducedSymbolWeight,
    ._specialWeights         = ws,
  };
}

inline void __weights(Map<unsigned, KboWeight>& ws) {
}

template<class A, class... As>
inline void __weights(Map<unsigned, KboWeight>& ws, pair<A, KboWeight> a, pair<As, KboWeight>... as) {
  ws.insert(get<0>(a).functor(), get<1>(a));
  __weights(ws, as...);
}

template<class... As>
inline Map<unsigned, KboWeight> weights(pair<As, KboWeight>... as) {
  Map<unsigned, KboWeight> out;
  __weights(out, as...);
  return out;
}