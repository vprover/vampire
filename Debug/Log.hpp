/**
 * @file Log.hpp
 * Defines class Log.
 */


//command for interactive replacing cout<<something<<endl; by LOG()
//vim -c '%s/^\([\t /]*\)cout<<\(.*\)<<endl; */\1LOG(\2);/gc' -c 'w' -c 'q' filename.cpp
//(y - replace, n - don't replace, q - stop replacing, a - replace all

/*
Enabling/disabling depends on the position in the file.
E.g.:

#include <Log.hpp>

void f()
{
  LOG("f called");
}

#undef LOGGING
#define LOGGING 0

void g()
{
  LOG("disabled");
}

int main(int argc, char* argv [])
{
  CALL ("main");

  LOG("still disabled");
  f();
  g();
#undef LOGGING
#define LOGGING 1

  LOG("reenabled "<<123<<'a'<<"bcd"<<argc);
  f();
  g();
}

outputs:
f called
reenabled 123abcd2
f called

*/

#ifndef __Debug_Log__
#define __Debug_Log__

#ifndef GLOBAL_LOGGING
#define GLOBAL_LOGGING 1
#endif

/**
Controls whether logs sould be output.

Lines

#undef LOGGING
#define LOGGING 0

disable logging for code below it, and 

#undef LOGGING
#define LOGGING 1

enable it again.

*/

#define LOGGING 1

#if GLOBAL_LOGGING

# include<iostream>

# define LOG_TARGET std::cout

/**
Outputs X if logging is enabled.

To toutput value of multiple variables v1,v2, one should write
LOG(v1<<v2)

Expressions must be enclosed in parentheses:
LOG((1+1))
rather than
LOG(1+1)
*/
# define LOG(X) if(LOGGING) { LOG_TARGET<<X<<endl; }

#else // GLOBAL_LOGGING

# define LOG(X)

#endif

#endif // __Debug_Log__
