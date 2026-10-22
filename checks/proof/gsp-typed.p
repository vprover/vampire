% expected: with -gsp on, the proof contains a general splitting definition
% whose quantified variables carry their $int sorts.
tff(pp_decl,type, pp: $int > $o ).
tff(qq_decl,type, qq: ($int * $int) > $o ).
tff(rr_decl,type, rr: ($int * $int) > $o ).
tff(ss_decl,type, ss: $int > $o ).
tff(ax1,axiom, ![X:$int, Y:$int, Z:$int]: (pp(X) | qq(X,Y) | rr(Y,Z) | ss(Z)) ).
tff(ax2,axiom, ![X:$int]: ~pp(X) ).
tff(ax3,axiom, ![Z:$int]: ~ss(Z) ).
tff(ax4,axiom, ![Y:$int, Z:$int]: ~rr(Y,Z) ).
tff(c,conjecture, qq(1,2) ).
