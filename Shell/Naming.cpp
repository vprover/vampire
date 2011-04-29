/**
 * @file Naming.cpp
 * Implements the naming technique
 * @since 05/05/2005 Manchester
 * @since 07/07/2007 Manchester, changed to new datastructures
 */

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Statistics.hpp"

#include "Indexing/TermSharing.hpp"

#include "Naming.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * Initialise a naming.
 * @param threshold Must be between 1 and 32767. If a non-unit clause is
 *   going to be used the number of times greater than the threshold,
 *   it will be named.
 * @param preserveEpr If true, names will not be introduced if it would
 *   lead to introduction of non-constant Skolem functions.
 */
Naming::Naming (int threshold, bool preserveEpr)
  : _threshold(threshold+1), _preserveEpr(preserveEpr), _varsInScope(false)
{
  ASS(threshold < 32768);
} // Naming::Naming


/**
 * Apply naming to a unit.
 *
 * @warning @b unit must not be a clause
 * @warning @b unit must not have any free variables
 * @since 13/07/2005 Haifa
 * @since 14/07/2005 Tel-Aviv airport, changed to replace the unit
 */
Unit* Naming::apply (Unit* unit,UnitList*& defs)
{
  CALL("Naming::apply(Unit*)");
  ASS(! unit->isClause());
  ASS(static_cast<FormulaUnit*>(unit)->formula()->freeVariables()==0);
  ASS(!_varsInScope); //_varsInScope can be true only when traversing inside a formula

  Formula* f = static_cast<FormulaUnit*>(unit)->formula();
  switch (f->connective()) {
  case TRUE:
  case FALSE:
    defs = UnitList::empty();
    return unit;
  default:
    break;
  }

  int pos;
  int neg;
  _defs = UnitList::empty();
  Formula* g = apply(f,ON_TOP,pos,neg);
  if (f == g) { // not changed
    ASS(_defs->isEmpty());
    defs = UnitList::empty();
    return unit;
  }
  ASS(! _defs->isEmpty());
  defs = _defs;
  UnitList* premises = _defs->copy();
  UnitList::push(unit, premises);
  return new FormulaUnit(g,
			 new InferenceMany(Inference::DEFINITION_FOLDING,premises),
			 unit->inputType());
} // Naming::apply



/**
 * Apply naming to a subformula.
 *
 * @param f the subformula, it must be in ENNF and different from TRUE
 *    and FALSE
 * @param where describes the position of the subformula
 * @param pos return the number of clauses resulting in converting f to CNF
 * @param neg return the number of clauses resulting in converting ~f to CNF
 * @since 01/07/2005 Manchester
 * @since 11/07/2005 flight Barcelona-Tel-Aviv
 */
Formula* Naming::apply (Formula* f,Where where,int& pos,int& neg)
{
  CALL("Naming::apply(Formula* ...)");

  switch (f->connective()) {
  case LITERAL:
    pos = 1;
    neg = 1;
    return f;

  case AND: {
    FormulaList* fs = f->args();
    int length = fs->length();
    void* mem = ALLOC_UNKNOWN(length*sizeof(int),"Naming::apply");
    int* cls = array_new<int>(mem, length);
    int* negCls = 0;
    if (where == UNDER_IFF) {
      mem = ALLOC_UNKNOWN(length*sizeof(int),"Naming::apply");
      negCls = array_new<int>(mem, length);
    }
    fs = apply(fs,where,cls,negCls);
    bool split = false;
    // formula array, initialised only upon demand
    Formula** gs = 0;
    // WARNING: QUADRATIC ALGORITHM BELOW, SHOULD BE IMPROVED
    for (;;) {
      int sum = 0; // result: the sum of all members
      int product = 1;
      int maxPos = 0;
      int maxNeg = 0;
      int maxPosIndex = 0;
      int maxNegIndex = 0;
      FormulaList* currArg = f->args();
      for (int i = 0;i < length;i++) {
	int c = cls[i];
	sum = Int::min(_threshold,sum+c);
	bool canBeDefEvaluated=false;
	bool canBeDef;
	if (c > maxPos) {
	  canBeDefEvaluated=true;
	  canBeDef=canBeInDefinition(currArg->head(), where);
	  if(canBeDef) {
	    maxPos = c;
	    maxPosIndex=i;
	  }
	}
	if (where == UNDER_IFF) {
	  int d = negCls[i];
	  product = Int::min(_threshold,product*d);
	  if (d > maxNeg) {
	    if(!canBeDefEvaluated) {
	      canBeDef=canBeInDefinition(currArg->head(), where);
	    }
	    if(canBeDef) {
	      maxNeg = d;
	      maxNegIndex=i;
	    }
	  }
	}
	currArg=currArg->tail();
      }
      ASS(currArg==0);
      ASS(maxPos > 0 || _preserveEpr);
      ASS(where != UNDER_IFF || maxNeg > 0);
      // splitWhat & 1 => split due to the positive part
      // splitWhat & 2 => split due to the negative part
      int splitWhat = 0;
      if (where != UNDER_IFF || product > 1) { // not all formulas are atomic
	if (where != ON_TOP && maxPos > 1 && sum >= _threshold) {
	  splitWhat |= 1;
	}
	if (where == UNDER_IFF && product >= _threshold && maxNeg > 1) {
	  splitWhat |= 2;
	}
      }
      if (! splitWhat) { // no more splits
	if (split) {
	  FormulaList* rs = FormulaList::empty();
	  for (int i = length-1;i >= 0;i--) {
	    FormulaList::push(gs[i],rs);
	  }
	  f = new JunctionFormula(AND,rs);
 	  DEALLOC_UNKNOWN(gs,"Naming::apply");
	}
	else if (fs != f->args()) {
	  f = new JunctionFormula(AND,fs);
	}
 	DEALLOC_UNKNOWN(cls,"Naming::apply");
	if (negCls) {
 	  DEALLOC_UNKNOWN(negCls,"Naming::apply");
	}
	neg = product;
	pos = sum;
	return f;
      }

      // conjunction under disjunction or IFF, should be split
      split = true;
      if (! gs) {
	void* mem = ALLOC_UNKNOWN(length*sizeof(Formula*),"Naming::apply");
	gs = array_new<Formula*>(mem, length);
	int j = 0;
	FormulaList::Iterator hs(fs);
	while (hs.hasNext()) {
	  gs[j] = hs.next();
	  j++;
	}
      }
      // gs has been initialised
      int maxIndex = splitWhat == 1 ||
                     (splitWhat == 3 && sum > product) ||
                     maxNeg == 1
                       ? maxPosIndex
	               : maxNegIndex;
      Formula* nm = introduceDefinition(gs[maxIndex],where==UNDER_IFF);
      gs[maxIndex] = nm;
      cls[maxIndex] = 1;
      if (where == UNDER_IFF) {
	negCls[maxIndex] = 1;
      }
    } // for (;;)
  } // case AND

  case OR: {
    FormulaList* fs = f->args();
    int length = fs->length();
    void* mem = ALLOC_UNKNOWN(length*sizeof(int),"Naming::apply");
    int* cls = array_new<int>(mem, length);
    int* negCls = 0;
    if (where == UNDER_IFF) {
      mem = ALLOC_UNKNOWN(length*sizeof(int),"Naming::apply");
      negCls = array_new<int>(mem, length);
    }
    if(where==ON_TOP) {
      where=OTHER;
    }
    fs = apply(fs,where,cls,negCls);
    bool split = false;
    // formula array, initialised only upon demand
    Formula** gs = 0;
    // WARNING: QUADRATIC ALGORITHM BELOW, SHOULD BE IMPROVED
    for (;;) {
      int sum = 0; // result: the sum of all members
      int product = 1;
      int maxPos = 0;
      int maxNeg = 0;
      int maxPosIndex = 0;
      int maxNegIndex = 0;
      FormulaList* currArg = f->args();
      for (int i = 0;i < length;i++) {
	int c = cls[i];
	product = Int::min(_threshold,product*c);
	bool canBeDefEvaluated=false;
	bool canBeDef;
	if (c > maxPos) {
	  canBeDefEvaluated=true;
	  canBeDef=canBeInDefinition(currArg->head(), where);
	  if(canBeDef) {
	    maxPos = c;
	    maxPosIndex=i;
	  }
	}
	if (where == UNDER_IFF) {
	  int d = negCls[i];
	  sum = Int::min(_threshold,sum+d);
	  if (d > maxNeg) {
	    if(!canBeDefEvaluated) {
	      canBeDef=canBeInDefinition(currArg->head(), where);
	    }
	    if(canBeDef) {
	      maxNeg = d;
	      maxNegIndex=i;
	    }
	  }
	}
	currArg = currArg->tail();
      }
      ASS(currArg==0);
      ASS(maxPos > 0 || _preserveEpr);
      ASS(where != UNDER_IFF || maxNeg > 0);
      // splitWhat & 1 => split due to the positive part
      // splitWhat & 2 => split due to the negative part
      int splitWhat = 0;
      if ( maxPos>0 && (where != UNDER_IFF || product > 1) ) { // not all formulas are atomic
	if (product >= _threshold && maxPos>1) {
	  splitWhat |= 1;
	}
	if (where == UNDER_IFF && sum >= _threshold && maxNeg>1) {
	  splitWhat |= 2;
	}
      }
      if (! splitWhat) { // no more splits
	if (split) {
	  FormulaList* rs = FormulaList::empty();
	  for (int i = length-1;i >= 0;i--) {
	    FormulaList::push(gs[i],rs);
	  }
	  f = new JunctionFormula(OR,rs);
 	  DEALLOC_UNKNOWN(gs,"Naming::apply");
	}
	else if (fs != f->args()) {
	  f = new JunctionFormula(OR,fs);
	}
 	DEALLOC_UNKNOWN(cls,"Naming::apply");
 	if (negCls) {
 	  DEALLOC_UNKNOWN(negCls,"Naming::apply");
	}
	neg = sum;
	pos = product;
	return f;
      }

      // splitWhat != 0
      split = true;
      if (! gs) {
	void* mem = ALLOC_UNKNOWN(length*sizeof(Formula*),"Naming::apply");
	gs = array_new<Formula*>(mem, length);
	int j = 0;
	FormulaList::Iterator hs(fs);
	while (hs.hasNext()) {
	  gs[j] = hs.next();
	  j++;
	}
      }
      // gs has been initialised
      int maxIndex = splitWhat == 1 ||
	             (splitWhat == 3 && product > sum) ||
	             maxNeg == 1
                       ? maxPosIndex
	               : maxNegIndex;
      Formula* nm = introduceDefinition(gs[maxIndex],where==UNDER_IFF);
      gs[maxIndex] = nm;
      cls[maxIndex] = 1;
      if (where == UNDER_IFF) {
	negCls[maxIndex] = 1;
      }
    } // for (;;)
  } // case OR

  case IFF:
  case XOR: {
    //there is no need to call the canBeInDefinition function here, since
    //the arguments will in the end appear both positive and negative anyway

    int negl;
    int posl;
    int negr;
    int posr;
    Connective con = f->connective();
    Formula* l;
    Formula* r;
    if (con == IFF) {
      l = apply(f->left(),UNDER_IFF,posl,negl);
      r = apply(f->right(),UNDER_IFF,posr,negr);
    }
    else {
      l = apply(f->left(),UNDER_IFF,negl,posl);
      r = apply(f->right(),UNDER_IFF,negr,posr);
    }
    if (where == ON_TOP && ((posl == 1 && posr == 1) ||
			    (negl == 1 && negr == 1))) {
      if (l != f->left() || r != f->right()) {
 	f = new BinaryFormula(con,l,r);
      }
      pos = Int::min(_threshold,Int::max(posl,posr));
      return f;
    }
    pos = Int::min(negl*posr + negr*posl,_threshold);
    neg = Int::min(posl*posr+negl*negr,_threshold);
    bool left; // name left
    if (pos < _threshold) {
      if (where != UNDER_IFF || neg < _threshold) {
	if (l != f->left() || r != f->right()) {
	  f = new BinaryFormula(con,l,r);
	}
	return f;
      }
      // must be split because of the neg
      left = posl*posr > negl*negr
             ? (posl >= posr)
	     : (negl >= negr);
    }
    else { // pos == threshold
      left = negl*posr > negr*posl
	     ? (negl >= posr)
	     : (posl >= negr);
      // checking if both must be named
      bool splitBoth = left
	               ? (posr+negr >= _threshold)
	               : (posl+negl >= _threshold);
      if (splitBoth) {
	Formula* newl = introduceDefinition(l,true);
	Formula* newr = introduceDefinition(r,true);
	f = new BinaryFormula(con,newl,newr);
	neg = 2;
	pos = 2;
	return f;
      }
    }

    if (left) {
      Formula* newl = introduceDefinition(l,true);
      f = new BinaryFormula(con,newl,r);
      neg = Int::min(posr+negr,_threshold);
      pos = neg;
      return f;
    }

    Formula* newr = introduceDefinition(r,true);
    f = new BinaryFormula(con,l,newr);
    neg = Int::min(posl+negl,_threshold);
    pos = neg;
    return f;
  }

  case FORALL:
  case EXISTS: {
    bool varFlagSet=f->connective()==FORALL && !_varsInScope;
    if(varFlagSet) {
      _varsInScope=true;
    }
    Formula* g = apply(f->qarg(),where,pos,neg);
    ASS (pos <= _threshold || _preserveEpr);
    if (g != f->qarg()) {
      f = new QuantifiedFormula(f->connective(),f->vars(),g);
    }
    if(varFlagSet) {
      _varsInScope=false;
    }
    return f;
  }

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // Naming::apply

/**
 * Return true if a definition for the formula @b f may be introduced
 */
bool Naming::canBeInDefinition(Formula* f, Where where)
{
  CALL("Naming::canBeInDefinition");

  if(!_preserveEpr) {
    return true;
  }

  bool unQuant=false;
  bool exQuant=false;
  SubformulaIterator sfit(f);
  while(sfit.hasNext()) {
    Formula* sf=sfit.next();
    if(sf->connective()==FORALL) {
      unQuant=true;
    }
    if(sf->connective()==EXISTS) {
      exQuant=true;
    }
  }


  Formula::VarList* fvars=f->freeVariables();
  bool freeVars=fvars;
  fvars->destroy();

  if(!_varsInScope && freeVars && (exQuant|| (unQuant && where==UNDER_IFF))) {
    return false;
  }

  return true;
}

Literal* Naming::getDefinitionLiteral(Formula* f, Formula::VarList* freeVars)
{
  CALL("Naming::getDefinitionLiteral");

  int length = freeVars->length();
  unsigned pred = env.signature->addNamePredicate(length);
  Signature::Symbol* predSym = env.signature->getPredicate(pred);

  if(env.colorUsed) {
    Color fc=f->getColor();
    if(fc!=COLOR_TRANSPARENT) {
      predSym->addColor(fc);
    }
    if(f->getSkip()) {
      predSym->markSkip();
    }
  }

  static Stack<unsigned> domainSorts;
  static Stack<TermList> predArgs;
  static DHMap<unsigned,unsigned> varSorts;
  domainSorts.reset();
  predArgs.reset();
  varSorts.reset();

  SortHelper::collectVariableSorts(f, varSorts);

  Formula::VarList::Iterator vit(freeVars);
  while(vit.hasNext()) {
    unsigned uvar = vit.next();
    domainSorts.push(varSorts.get(uvar, Sorts::SRT_DEFAULT));
    predArgs.push(TermList(uvar, false));
  }

  predSym->setType(new PredicateType(length, domainSorts.begin()));

  return Literal::create(pred, length, true, false, predArgs.begin());
}

/**
 * Introduce definition (A X)(p(X) &lt;-&gt; f), where X are all variables
 * of f and add it to _definitions. If @b iff is false, then the
 * definition is the ENNF of (A X)(~p(X) -&gt; f).
 *
 * @param f formula for which a name should be introduced
 * @param iff if true then the definition is an iff-definition
 * @returns placeholder for p(X)
 *
 * @since 01/07/2005 Manchester
 */
Formula* Naming::introduceDefinition (Formula* f,bool iff)
{
  CALL("Naming::introduceDefinition");
  ASS_NEQ(f->connective(), LITERAL);
  ASS_NEQ(f->connective(), NOT);

  Formula::VarList* vs;
  vs = f->freeVariables();
  Literal* atom = getDefinitionLiteral(f, vs);
  Formula* name = new AtomicFormula(atom);
  Formula* def;
  if (iff) {
    def = new BinaryFormula(IFF,name,f);
  }
  // iff = false
  else {
    FormulaList* fs = f->connective() == OR
  		      ? f->args()
                      : new FormulaList(f);
    Formula* nameFormula = new NegatedFormula(name);
    FormulaList::push(nameFormula,fs);
    def = new JunctionFormula(OR,fs);
  }
  if (vs->isNonEmpty()) {
    def = new QuantifiedFormula(FORALL,vs,def);
  }
  Inference* inf = new Inference(Inference::PREDICATE_DEFINITION);
  Unit* definition = new FormulaUnit(def,inf,Unit::AXIOM);
  env.statistics->formulaNames++;
  UnitList::push(definition,_defs);
  return name;
} // Naming::introduceDefinition


/**
 * Apply naming to a list of subformulas.
 *
 * @param fs the list
 * @param results placeholder for results
 * @param where the position of the list in the top formula
 * @param negResults placeholder for results for a negative occurrence
 *        of the list
 *
 * @returns the number of clauses
 * @since 01/07/2005 Manchester
 */
FormulaList* Naming::apply (FormulaList* fs,Where where,
			    int* results,int* negResults)
{
  CALL("Naming::apply (FormulaList*...)");

  if (fs->isEmpty()) {
    return fs;
  }

  int neg;
  Formula* g = apply(fs->head(),where,results[0],neg);
  if (where == UNDER_IFF) {
    negResults[0] = neg;
  }
  FormulaList* gs = apply(fs->tail(),where,results+1,negResults+1);
  if (g == fs->head() && gs == fs->tail()) {
    return fs;
  }
  return new FormulaList(g,gs);
} // Naming::apply (FormulaList&...)


