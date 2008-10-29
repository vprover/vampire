/**
 * @file Rule/Index.cpp
 * Implements class Index for a rule index
 * @since 28/07/2008 train London-Manchester
 */

#include "../Lib/Stack.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"

#include "Index.hpp"

using namespace Kernel;
using namespace Rule;

/**
 * Class used in compilation.
 * @since 03/08/2008 Torrevieja
 */
class Index::TRule {
public:
  /** A term argument */
  TermList arg;
  /** Rule */
  const Rule* rule;

  /** the header: -1 for variables and the functor number for complex terms */
  inline int header() const
  {
    return arg.isVar() ? -1 : arg.term()->functor();
  }
  /** the arity: 0 for variables and the arity for complex terms */
  inline unsigned arity() const
  {
    return arg.isVar() ? 0 : arg.term()->arity();
  }

  /**
   * Compare the term headers.
   * @since 06/08/2008 Manchester
   */
  static inline int compare(const TRule* tr1,const TRule* tr2)
  {
    int h1 = tr1->header();
    int h2 = tr2->header();
    return h1 < h2 ? -1 : h1 == h2 ? 0 : 1;
  } // compare
};

/**
 * Class used in compilation.
 * @since 03/08/2008 Torrevieja
 */
class Index::LRule {
public:
  /** Literal */
  const Literal* literal;
  /** Rule */
  const Rule* rule;

  /**
   * Compare the literal headers.
   * @since 03/08/2008 Torrevieja
   */
  static inline int compare(const LRule* l1,const LRule* l2)
  {
    const Literal* lit1 = l1->literal;
    const Literal* lit2 = l2->literal;
    unsigned h1 = lit1->header();
    unsigned h2 = lit2->header();
    return h1 < h2 ? -1 : h1 == h2 ? 0 : 1;
  } // compare
};

/**
 * Create an empty index for the given signature.
 */
Index::Index(const Signature* sig)
  : _signature(sig),
    _headers(2*sig->predicates())
{
  _entries = new(ALLOC_KNOWN(_headers*sizeof(Entry),"Index::entries"))
                  Entry[_headers];
} // Index::Index

/**
 * Create an empty index for the given signature.
 */
Index::~Index()
{
  DEALLOC_KNOWN(_entries,
		2*_signature->predicates()*sizeof(Entry),
		"Index::entries");
} // Index::~Index

/**
 * Create the index from the list of units and save into @b goals the list of goals in
 * it.
 * @since 06/08/2008 Manchester
 */
void Index::compile(UnitList* units,Stack<Unit*>& goals)
{
  CALL("Index::compile-1");

  // first round: just count the total number of rules
  _numberOfRules = 0;
  UnitList::Iterator uit(units);
  while (uit.hasNext()) {
    Clause* cls = static_cast<Clause*>(uit.next());
    switch (cls->inputType()) {
    case Unit::AXIOM:
    case Unit::ASSUMPTION:
    case Unit::LEMMA:
      _numberOfRules += cls->length();
      break;
    case Unit::CONJECTURE:
      _numberOfRules += cls->length();
      goals.push(cls);
      break;
    }
  }

  ASS(_numberOfRules > 0);

  cout << "Rules: " << _numberOfRules << "\n";
  cout << "Goals: " << goals.length() << "\n";

  _rules = new(ALLOC_KNOWN(sizeof(Rule)*_numberOfRules,"Index::RuleArray")) Rule[_numberOfRules];
  LRule* lrules = new(ALLOC_KNOWN(sizeof(LRule)*_numberOfRules,"Index::LRuleArray")) LRule[_numberOfRules];
  int r = 0;
  // compiling rules
  uit.reset(units);
  while (uit.hasNext()) {
    Clause& cls = *static_cast<Clause*>(uit.next());
    for (int i = cls.length()-1;i >= 0;i--) {
      Rule& rule = _rules[r];
      rule.clause=&cls;
      rule.literal=cls[i];
      LRule& lrule = lrules[r];
      lrule.literal = rule.literal;
      lrule.rule = &rule;
      r++;
    }
  }
  sort(lrules,0,_numberOfRules-1);

  // initialising entries
  int currentHeader = lrules[0].literal->header();
  int arity = lrules[0].literal->arity(); // of current header
  int previousHeader = -2;
  int numberOfRulesWithCurrentHeader = 0;
  for (int i = 0;i < _numberOfRules;i++) {
    LRule& lr = lrules[i];
    int header = lr.literal->header();
    if (currentHeader == header) {
      numberOfRulesWithCurrentHeader++;
      if (i < _numberOfRules-1) {
	continue;
      }
      else {
	i++;
      }
    }
    // either currentHeader != header or i == numberOfRules
    for (int j = previousHeader+1;j < currentHeader;j++) {
      _entries[j].rules = 0;
    }
    ASS(numberOfRulesWithCurrentHeader > 0);
    Entry& entry = _entries[currentHeader];
    entry.rules = numberOfRulesWithCurrentHeader;
    entry.fun = header;
    entry.arity = arity;
    int firstRule = i-numberOfRulesWithCurrentHeader;
    ASS(firstRule >= 0);
    ASS(firstRule < _numberOfRules);
    if (arity == 0) {
      entry.leaf = new(ALLOC_KNOWN(sizeof(Rule*)*numberOfRulesWithCurrentHeader,
				   "Index::Leaf"))
	const Rule*[numberOfRulesWithCurrentHeader];
      for (int k = 0;k < numberOfRulesWithCurrentHeader;k++) {
	entry.leaf[k] = lrules[firstRule+k].rule;
      }
    }
    else {
      entry.entries = new(ALLOC_KNOWN(sizeof(EntryArray)*arity,
				      "Index::EntryArray"))
	EntryArray[arity];
      TRule* trules = new(ALLOC_KNOWN(sizeof(TRule)*numberOfRulesWithCurrentHeader,
				      "Index::TRuleArray"))
	TRule[numberOfRulesWithCurrentHeader];
      for (int k = 0;k < arity;k++) {
	for (int m = 0;m < numberOfRulesWithCurrentHeader;m++) {
	  LRule& nextRule = lrules[firstRule+m];
	  trules[m].rule = nextRule.rule;
	  trules[m].arg = *nextRule.literal->nthArgument(k);
	}
	compile(trules,numberOfRulesWithCurrentHeader,entry.entries[k]);
      }
      DEALLOC_KNOWN(trules,sizeof(TRule)*numberOfRulesWithCurrentHeader,"Index::TRuleArray");
    }
    if (i == _numberOfRules-1) {
      for (int j = currentHeader+1;j < _headers;j++) {
	_entries[j].rules = 0;
      }
      break;
    }
    // going to the next header
    previousHeader = currentHeader;
    currentHeader = lr.literal->header();
    arity = lr.literal->arity(); // of current header
    numberOfRulesWithCurrentHeader = 1;
  }

  DEALLOC_KNOWN(lrules,sizeof(LRule)*_numberOfRules,"Index::LRuleArray");
} // Index::compile

/**
 * Create the index from the list of TRule and save the resulting array
 * of entries.
 * @param trules array of TRules having non-variable terms
 * @param numberOfRules the length of this array
 * @param saveTo the entry array record to save
 * @since 06/08/2008 Manchester
 */ 
void Index::compile(TRule* trules,int numberOfRules,Index::EntryArray& saveTo)
{
  CALL("Index::compile-2");
  ASS(numberOfRules > 0);

  sort(trules,0,numberOfRules-1);

  // checking the number of different headers
  int numberOfHeaders = 1;
  int currentHeader = trules[0].header();
  for (int i = 1;i < numberOfRules;i++) {
    int h = trules[i].header();
    ASS(h >= currentHeader);
    if (h > currentHeader) {
      numberOfHeaders++;
      currentHeader = h;
    }
  }

  Entry* entries = new(ALLOC_KNOWN(numberOfHeaders*sizeof(Entry),
				  "Index::entries")) Entry[numberOfHeaders];
  saveTo.array = entries;
  saveTo.length = numberOfHeaders;
  // initialising entries
  currentHeader = trules[0].header();
  int arity = trules[0].arity(); // of current header
  int previousHeader = -2;
  int numberOfRulesWithCurrentHeader = 0;
  int j = 0; // entry number
  for (int i = 0;i < numberOfRules;i++) {
    TRule& tr = trules[i];
    int header = tr.header();
    if (currentHeader == header) {
      numberOfRulesWithCurrentHeader++;
      if (i < numberOfRules-1) {
	continue;
      }
      else {
	i++;
      }
    }

    ASS(numberOfRulesWithCurrentHeader > 0);
    ASS(j < numberOfHeaders);
    Entry& entry = entries[j++];
    entry.rules = numberOfRulesWithCurrentHeader;
    entry.fun = header;
    entry.arity = arity;
    int firstRule = i-numberOfRulesWithCurrentHeader;
    ASS(firstRule >= 0);
    ASS(firstRule < numberOfRules);
    if (arity == 0) {
      entry.leaf = new(ALLOC_KNOWN(sizeof(Rule*)*numberOfRulesWithCurrentHeader,
				    "Index::Leaf"))
	            const Rule*[numberOfRulesWithCurrentHeader];
      cerr << (void*)&entry << " A: " << numberOfRulesWithCurrentHeader << "\n";
      for (int k = 0;k < numberOfRulesWithCurrentHeader;k++) {
	entry.leaf[k] = trules[firstRule+k].rule;
      }
    }
    else {
      entry.entries = new(ALLOC_KNOWN(sizeof(EntryArray)*arity,
 				      "Index::EntryArray"))
 	EntryArray[arity];
      TRule* nrules = new(ALLOC_KNOWN(sizeof(TRule)*numberOfRulesWithCurrentHeader,
 				      "Index::TRuleArray"))
 	TRule[numberOfRulesWithCurrentHeader];
      for (int k = 0;k < arity;k++) {
 	for (int m = 0;m < numberOfRulesWithCurrentHeader;m++) {
 	  TRule& nextRule = trules[firstRule+m];
 	  nrules[m].rule = nextRule.rule;
 	  nrules[m].arg = *nextRule.arg.term()->nthArgument(k);
	}
 	compile(nrules,numberOfRulesWithCurrentHeader,entry.entries[k]);
      }
      DEALLOC_KNOWN(nrules,sizeof(TRule)*numberOfRulesWithCurrentHeader,"Index::TRuleArray");
    }
    // going to the next header
    previousHeader = currentHeader;
    currentHeader = tr.header();
    arity = tr.arity(); // of current header
    numberOfRulesWithCurrentHeader = 1;
  }
} // Index::compile

/**
 * Sorting an array of LRule between and inclusive of indexes p and r.
 * Copied from the generic Sort module for efficiency
 * @since 03/08/2008 Torrevieja
 */
void Index::sort(LRule* lrules,int p,int r) 
{
  CALL("Index::Sort::sort(LRule*,...)");

  if (p >= r) {
    return;
  }
  int m = (p+r)/2;
  int i = p;
  int j = r;
  LRule a = lrules[m];
  while (i < m) {
    LRule b = lrules[i];
    if (LRule::compare(&a,&b) != -1) { // a[i] <= a[m]
      i++;
      continue;
    }
    if (m < j) {
      lrules[i] = lrules[j];
      lrules[j] = b;
      j--;
      continue;
    }
    lrules[m] = b;
    lrules[i] = lrules[m-1];
    m--;
    j--;
  }
  while (m < j) {
    LRule b = lrules[j];
    if (LRule::compare(&b,&a) != -1) { // a[m] <= a[j]
      j--;
      continue;
    }
    lrules[m] = b;
    lrules[j] = lrules[m+1];
    m++;
  }
  lrules[m] = a;
  sort(lrules,p,m-1);
  sort(lrules,m+1,r);
} // Index::sort


/**
 * Sorting an array of LRule between and inclusive of indexes p and r.
 * Copied from the generic Sort module for efficiency
 * @since 03/08/2008 Torrevieja
 */
void Index::sort(TRule* trules,int p,int r) 
{
  CALL("Index::Sort::sort(TRule*,...)");

  if (p >= r) {
    return;
  }
  int m = (p+r)/2;
  int i = p;
  int j = r;
  TRule a = trules[m];
  while (i < m) {
    TRule b = trules[i];
    if (TRule::compare(&a,&b) != -1) { // a[i] <= a[m]
      i++;
      continue;
    }
    // a[i] > a[m]
    if (m < j) {
      trules[i] = trules[j];
      trules[j] = b;
      j--;
      continue;
    }
    // a[i] > a[m], m == j
    trules[m] = b;
    trules[i] = trules[m-1];
    m--;
    j--;
  }
  // i == m
  while (m < j) {
    TRule b = trules[j];
    if (TRule::compare(&b,&a) != -1) { // a[m] <= a[j]
      j--;
      continue;
    }
    // a[m] > a[j]
    trules[m] = b;
    trules[j] = trules[m+1];
    m++;
  }
  trules[m] = a;
  sort(trules,p,m-1);
  sort(trules,m+1,r);
} // Index::sort


/**
 * A candidate set is a set of candidates for unification.
 * @since 07/08/2008 train London-Manchester.
 */
Index::CandidateSet* Index::retrieve(const Literal* queryLiteral)
{
//   CALL("Index::retrieve");

//   int header = queryLiteral->complementaryHeader();
//   Entry& entry = _entries[header];
//   if (entry.rules == 0) {
//     return 0;
//   }
//   return retrieve(queryLiteral,&entry,0);
  return 0;
} // Index::retrieve


/**
 * Return a candidate set for unification with the query term.
 * @param queryTerm the query term
 * @param entry the Entry in the index corresponding to the term
 * @param otherCandidates previously obtained candidates, should be
 *   appended to the resulting candidate set
 * @since 07/08/2008 train London-Manchester.
 */
Index::CandidateSet* Index::retrieve(const Term* queryTerm,
				     Entry* entry,
				     CandidateSet* otherCandidates)
{
  return 0;
//   CALL("Index::retrieve-2");

//   int arity = queryTerm->arity();
//   if (arity == 0) { // constant
//     return new CandidateSet(entry,otherCandidates);
//   }

//   // arity > 0
//   CandidateSet* previous = 0;
//   int k = -1; // argument number
//   for (const TermList* args = queryTerm->args();
//        ! args->isEmpty();
//        args = args->next()) {
//     k++;
//     if (args->isVar()) {
//       continue;
//     }
//     CandidateSet* next = retrieve(args->term(),
// 				  entry->entries + k,
// 				  otherCandidates);
//     if (! next) { // no candidates
//       if (previous) {
// 	previous->cutUpTo(0);
//       }
//       return 0;
//     }
//     // next != 0, so next contains a candidate
//     if (! previous) {
//       previous = next;
//       continue;
//     }
//     // both next and previous != 0
//     if (previous->total() <= next->total()) {
//       next->cutUpTo(previous);
//       continue;
//     }
//     // previous->total() > next->total(), so next is better
//     previous->cutUpTo(next);
//     previous = next;
//   }
//   if (previous) { // at least one argument is non-variable
//     return previous;
//   }
//   // all arguments are variables
//   return new CandidateSet(entry,otherCandidates);
} // Index::retrieve


/**
 * Create a new candidate set obtained by adding an entry @b entry to the
 * candidate set @b prev
 * @since 07/08/2008 Manchester
 */
Index::CandidateSet::CandidateSet(Entry* entry,CandidateSet* prev)
  : _entry(entry),
    _length(entry->rules),
    _next(prev)
{
  CALL("Index::CandidateSet::CandidateSet");

  _total = entry->rules;
  if (prev) {
    _total += prev->_total;
  }
} // Index::CandidateSet::CandidateSet

/**
 * Delete from memory all parts of this candidate set up to @b upTo.
 * @since 07/08/2008 Manchester
 */
void Index::CandidateSet::cutUpTo(CandidateSet* upTo)
{
  CALL("Index::CandidateSet::cutUpTo");
  ASS(this != upTo);

  CandidateSet* current = this;
  for (;;) {
    CandidateSet* next = current->_next;
    delete current;
    if (next == upTo) {
      return;
    }
    current = next;
  }
} // Index::CandidateSet::cutUpTo

/**
 * Return a candidate set for unification with the query term.
 * @param queryTerm the query term
 * @param entryArray the EntryArray in the index corresponding to the term
 * @param otherCandidates previously obtained candidates, should be
 *   appended to the resulting candidate set
 * @since 07/08/2008 Manchester
 */
// Index::CandidateSet* Index::CandidateSet::retrieve(const Term* query,
// 						   EntryArray* entryArray,
// 						   CandidateSet* previous)
// {
//   CALL("Index::retrieve-3");
// } 

