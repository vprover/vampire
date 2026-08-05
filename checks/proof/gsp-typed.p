% ax1 chains four literals through single shared variables, so -gsp on names
% part of it, and the proof contains a general splitting definition whose
% quantified variables must carry their $int sorts. Keep the predicates at
% most binary: the sanity check greps the definition for a bare variable, and
% an argument list with three or more variables would look like one.
tff(pp_decl,type, pp: $int > $o ).
tff(qq_decl,type, qq: ($int * $int) > $o ).
tff(rr_decl,type, rr: ($int * $int) > $o ).
tff(ss_decl,type, ss: $int > $o ).
tff(ax1,axiom, ![X:$int, Y:$int, Z:$int]: (pp(X) | qq(X,Y) | rr(Y,Z) | ss(Z)) ).
tff(ax2,axiom, ![X:$int]: ~pp(X) ).
tff(ax3,axiom, ![Z:$int]: ~ss(Z) ).
tff(ax4,axiom, ![Y:$int, Z:$int]: ~rr(Y,Z) ).
tff(c,conjecture, qq(1,2) ).
