
#include <iostream>
#include "ManCSPassiveClauseContainer.hpp"
#include "Lib/VirtualIterator.hpp"

namespace Saturation
{
using namespace Lib;
using namespace Kernel;

/*
 * this class wraps the iterator of std::vector into IteratorCore required by Vampire.
 */
class VectorIteratorWrapper : public IteratorCore<Clause*>
{
public:
	CLASS_NAME(VectorIteratorWrapper);
	USE_ALLOCATOR(VectorIteratorWrapper);
  
	explicit VectorIteratorWrapper(const std::vector<Clause*>& v) : curr(v.begin()), end(v.end()) {}
	bool hasNext() { return curr != end; };
	Clause* next() { auto cl = *curr; curr = std::next(curr); return cl;};

private:
	std::vector<Clause*>::const_iterator curr;
	const std::vector<Clause*>::const_iterator end;
};


ClauseIterator ManCSPassiveClauseContainer::iterator()
{
	return vi( new VectorIteratorWrapper(clauses));
}

void ManCSPassiveClauseContainer::add(Clause* cl)
{
	clauses.push_back(cl);
	addedEvent.fire(cl);
}

void ManCSPassiveClauseContainer::remove(Clause* cl)
{
	ASS(cl->store()==Clause::PASSIVE);
	
	auto it = std::find(clauses.begin(),clauses.end(),cl);
	ASS(it != clauses.end();)
	clauses.erase(it);

	removedEvent.fire(cl);
	ASS(cl->store()!=Clause::PASSIVE);
}

Clause* ManCSPassiveClauseContainer::popSelected()
{
  	ASS(!clauses.empty());

	// print existing clauses
	std::cout << "Pick a clause from: ";
	for (const auto& cl : clauses)
	{
		std::cout << cl->number() << ",";
	}
	std::cout << std::endl;

	// let user pick a clause id
	std::string id;
	std::cin >> id;
	unsigned selectedId = std::stoi(id);

	// find clause with that id
	auto selectedClauseIt = std::find_if(clauses.begin(), clauses.end(), 
		[&](Clause* c) -> bool { return c->number() == selectedId; });	
	ASS(selectedClauseIt != clauses.end());

	auto selectedClause	= *selectedClauseIt;
	clauses.erase(selectedClauseIt);
	selectedEvent.fire(selectedClause);
	
	return selectedClause;
}

unsigned ManCSPassiveClauseContainer::size() const { return clauses.size(); }
bool ManCSPassiveClauseContainer::isEmpty() const { return clauses.empty(); }
}
