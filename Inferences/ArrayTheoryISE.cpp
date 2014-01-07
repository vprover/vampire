/**
 * @file ArrayTheoryISE.cpp
 * Implements class ArrayTheoryISE.
 */

#include "Inferences/ArrayTheoryISE.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Statistics.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

ArrayTermTransformer::ArrayTermTransformer() :
	_select1Functor(env.signature->getInterpretingSymbol(Theory::SELECT1_INT)),
	_store1Functor(env.signature->getInterpretingSymbol(Theory::STORE1_INT)),
	_array1Sort(Sorts::SRT_ARRAY1),
	_intSort(Sorts::SRT_INTEGER),
	_array1SkolemFunction(theory->getArrayExtSkolemFunction(Sorts::SRT_ARRAY1))
{}

ArrayTermTransformer::~ArrayTermTransformer() {}

TermList ArrayTermTransformer::transformSubterm(TermList trm)
{
	if (!trm.isTerm()) {
		return trm;
	}
	
	Term* term = trm.term();

	if(term->functor() == _select1Functor) {
		TermList* array = term->nthArgument(0);
		
		if (array->isTerm() && array->term()->functor() == _store1Functor) {
			// r(w(A,I,V),I) => V
			Term* store = term->nthArgument(0)->term();

			TermList* selectIndex = term->nthArgument(1);
			TermList* storeIndex = store->nthArgument(1);

			if (selectIndex->sameContent(storeIndex)) {
				return *store->nthArgument(2);
			}
		}
	} else if(term->functor() == _store1Functor) {
		TermList* array = term->nthArgument(0);
		TermList* value = term->nthArgument(2);
		
		if (array->isTerm() && array->term()->functor() == _store1Functor) {
			// w(w(A,I,V1),I,V2) => w(A,I,V2)
			Term* store = array->term();
			TermList* outerIndex = term->nthArgument(1);
			TermList* innerIndex = store->nthArgument(1);

			if (outerIndex->sameContent(innerIndex)) {
				TermList args[3];
				args[0] = *store->nthArgument(0);
				args[1] = *outerIndex;
				args[2] = *value;
				return TermList(Term::create(term, args));
			}
		} else if (value->isTerm() && value->term()->functor() == _select1Functor) {
			// w(A,I,r(A,I)) => A
			TermList* selectArray = value->term()->nthArgument(0);
			TermList* selectIndex = value->term()->nthArgument(1);
			TermList* storeIndex = term->nthArgument(1);

			if (selectArray->sameContent(array) &&
				selectIndex->sameContent(storeIndex)) {
				return *array;
			}
		}
	}
	
	return trm;
}

Literal* ArrayTermTransformer::rewriteNegEqByExtensionality(Literal* l) {
	if (l->isEquality() && l->isNegative() && SortHelper::getEqualityArgumentSort(l) == _array1Sort) {
		//cout << l->toString() << endl;
		TermList* lhs = l->nthArgument(0);
		TermList* rhs = l->nthArgument(1);

		// unsigned skolemFunction = Skolem::addSkolemFunction(0, 0, _intSort, "adiff");
		// TermList skolemTerm(Term::create(skolemFunction, 0, 0));
		TermList params[] = {*lhs, *rhs};
		TermList skolemTerm(Term::create(_array1SkolemFunction, 2, params));
		
		TermList sel1(Term::create2(_select1Functor, *lhs, skolemTerm));
		TermList sel2(Term::create2(_select1Functor, *rhs, skolemTerm));
		
		return Literal::createEquality(false, sel1, sel2, _intSort);
	}

	return l;
}

ArrayTheoryISE::ArrayTheoryISE() :
	_transformer(ArrayTermTransformer()) {}

Clause* ArrayTheoryISE::simplify(Clause* c)
{
	CALL("ArrayTheoryISE::simplify");

	if (c->inputType() == Unit::AXIOM) {
		return c;
	}
	
	static DArray<Literal*> lits(32);
	int length = c->length();
	lits.ensure(length);
	bool modified = false;

	// BK: is there a (performance, ...) reason for the decreasing counter?
	//for (int i = length-1; i >= 0;i--) {
	for (int i = 0; i < length; ++i) {
		Literal* l = (*c)[i];
		bool done = false;
		Literal* transformed;

		// BK: is there already a "deep" simplifier? i.e. one that performs
		// recursive simplification also on the arguments of already simplified
		// terms.
		while (!done) {
			//cout << "before: " << l->toString() << endl;
			transformed = _transformer.transform(l);
			//cout << "after:  " << transformed->toString() << endl;

			if (l != transformed) {
				modified = true;
				l = transformed;
			} else {
				done = true;
			}
		}

		Literal* transformed2 = _transformer.rewriteNegEqByExtensionality(transformed);
		if (transformed2 != transformed) {
			modified = true;
		}
		
		lits[i] = transformed2;
	}

	if (modified) {
		// BK: inference rule?
		Clause* d = new(length)
			Clause(length,
				   c->inputType(),
				   new Inference1(Inference::INTERPRETED_SIMPLIFICATION, c));
		for (int i = 0; i < length; ++i) {
			(*d)[i] = lits[i];
		}
		d->setAge(c->age());
		// BK: should we keep some statistics?
		//cout << "before: " << c->toString() << endl;
		//cout << "after:  " << d->toString() << endl;
		return d;
	}
	
	return c;
}

}
