/**
 * @file Resolution/ProofAttempt.hpp
 * Defines class ProofAttempt implementing a resolution proof attempt.
 * @since 30/12/2007 Manchester
 */

#ifndef __ProofAttempt__
#define __ProofAttemp__

#include "Active.hpp"
#include "Passive.hpp"
#include "Unprocessed.hpp"

namespace Resolution {

/**
 * Class ProofAttempt implementing a resolution proof attempt.
 * @since 30/12/2007 Manchester
 */
class ProofAttempt
{
public:
  void initialClause(Clause* c);
  void saturate();
  /** Return the active clause queue */
  Active& active() { return _active; }
  /** Return the unprocessed clause queue */
  Unprocessed& unprocessed() { return _unprocessed; };
private:
  /** The queue of unprocessed clauses */
  Unprocessed _unprocessed;
  /** Passive clauses */
  Passive _passive;
  /** Active clauses */
  Active _active;
  Clause* processUnprocessed(Clause*);
  bool retained(Clause*);
  void addToPassive(Clause*);
  Clause* removeDuplicateLiterals(Clause*);
  Clause* removeTrivialInequalities(Clause*);
  Clause* processPassive(Clause*);
  void generatingInferences(Clause*);
}; // class ProofAttempt

}

#endif
