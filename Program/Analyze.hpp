/**
 * @file Analyze.hpp
 * Defines class Program::Analyze
 *
 * @since 21/08/2010, Torrevieja
 */

#ifndef __ProgramAnalyze__
#define __ProgramAnalyze__

#include "Lib/Map.hpp"
#include "Statement.hpp"

namespace Program {

/** Structure representing variable properties collected by analysis */
struct VariableProperty
{
	/** true if constant */
	bool isConstant;
	/** true if counter (increased or decreased only by constant values) */
	bool isCounter;

	/** initialise */
	VariableProperty()
		: isConstant(false),
			isCounter(true)
	{}
}; // class VariableProperty

/**
 * Defines utilities for program analysis
 * @since 21/08/2010, Torrevieja
 */
class Analyze
{
public:
	void analyze(const Statement* program);
private:
	Map<Variable*,VariableProperty*> _variableProperties;
}; // class Analyze

}

#endif // __ProgramVariable__
