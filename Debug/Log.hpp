/**
 * @file Log.hpp
 * Defines class Log.
 */


//command for interactive replacing cout<<something<<endl; by LOG()
//vim -c '%s/^\([\t /]*\)cout<<\(.*\)<<endl; */\1LOG(\2);/gc' -c 'w' -c 'q' filename.cpp
//(y - replace, n - don't replace, q - stop replacing, a - replace all

/*

example:
int main(int argc, char* argv [])
{
  LOG("enabled "<<123<<'a'<<"bcd"<<argc);

#undef LOGGING
#define LOGGING 0
  LOG("disabled");

#undef LOGGING
#define LOGGING 1

  LOG("enabled again");
}


*/

#ifndef __Debug_Log__
#define __Debug_Log__

#ifndef GLOBAL_LOGGING
#define GLOBAL_LOGGING 1
#endif

#define LOGGING 1

#if GLOBAL_LOGGING

# include<iostream>

# define LOG_TARGET std::cout

# define LOG(X) if(LOGGING) { LOG_TARGET<<X<<endl; }

#else // GLOBAL_LOGGING

# define LOG(X)

#endif

#endif // __Debug_Log__
