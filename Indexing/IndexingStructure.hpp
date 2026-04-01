/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file IndexingStructure.hpp
 * Defines class IndexingStructure.
 */

#ifndef __IndexingStructure__
#define __IndexingStructure__

#include "Lib/Option.hpp"
#include <ostream>

namespace Indexing {

template<typename Data>
class IndexingStructure {
public:
  virtual ~IndexingStructure() {}

  virtual void handle(Data data, bool insert) = 0;
  void insert(Data data) { handle(std::move(data), /* insert */ true ); }
  void remove(Data data) { handle(std::move(data), /* insert */ false); }

  virtual void output(std::ostream& out, Lib::Option<unsigned> multilineIndent) const = 0;

  friend std::ostream& operator<<(std::ostream& out, IndexingStructure const& self) { self.output(out, {}); return out; }
  friend std::ostream& operator<<(std::ostream& out, Lib::Output::Multiline<IndexingStructure> const& self) { self.self.output(out, some(self.indent)); return out; }
};

}

#endif /* __IndexingStructure__ */
