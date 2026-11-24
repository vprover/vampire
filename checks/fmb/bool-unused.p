% SYN983_8 without its conjecture: nothing but declarations, one of a symbol over $o. FMB
% prints p, and with it the domain of $o, which it used to print as a one-element domain
% without FOOL constants -- an assertion violation in a debug build, a SIGSEGV in release.
% Now $o is built in with its two elements (FMB/FiniteModelBuilder.cpp, onModelFound).
tff(a_const,type, a: $o ).
tff(b_const,type, b: $o ).
tff(p_const,type, p: $o > $o ).
