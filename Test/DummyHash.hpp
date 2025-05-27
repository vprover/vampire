/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

class DummyHash {
public:
  template<typename T> static bool equals(T o1, T o2) { return o1 == o2; }
  template<typename T> static unsigned hash(T val) { return 0; }
};
