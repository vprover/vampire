#include <iostream>

#include "Shell/Analysis/TheorySubclauseAnalyser.hpp"

using namespace Shell::Analysis;
using namespace std;

TheorySubclauseAnalyser::TheorySubclauseAnalyser() {

}

TheorySubclauseAnalyser::~TheorySubclauseAnalyser() {

}

void TheorySubclauseAnalyser::addClause(Clause& c) {
  cout << c << endl;
}
