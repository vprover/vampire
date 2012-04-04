/**
 * @file Log_TagDecls.hpp
 * Defines class Log_TagDecls.
 */

#ifndef __Log_TagDecls__
#define __Log_TagDecls__

#include "Log.hpp"

#if LOGGING

#define DECL(name,...) \
  do {								\
    const char* t = name;					\
    Debug::Logging::declareTag(t);				\
    __VA_ARGS__;						\
  } while(false)
#define DOC(doc) Debug::Logging::addDoc(t,doc)
#define PARENT(parent, depth) Debug::Logging::addParent(t,parent,depth)
#define UNIT_TAG Debug::Logging::markUnitTag(t)
#define INT_TAG Debug::Logging::markIntTag(t)

#endif

#endif // __Log_TagDecls__
