#ifndef __SHELL__SEARCH_SPACE_DUMPER_H__
#define __SHELL__SEARCH_SPACE_DUMPER_H__
#include "Forwards.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Stack.hpp"

namespace Shell {

  class SearchSpaceDumper {
    Stack<Kernel::Clause*> _clauses;
    static SearchSpaceDumper* _instance;
  public:
    CLASS_NAME(SearchSpaceDumper)
    USE_ALLOCATOR(SearchSpaceDumper)

    SearchSpaceDumper(SearchSpaceDumper&) = delete;
    SearchSpaceDumper(SearchSpaceDumper&&) = default;
    SearchSpaceDumper();
    ~SearchSpaceDumper();

    void add(Kernel::Clause* clause);
    void dumpFile(const vstring& file) const;
    static void init();
    static SearchSpaceDumper* instance();
  };

} // namespace Shell

#endif // __SHELL__SEARCH_SPACE_DUMPER_H__
