%------------------------------------------------------------------------------
%----These are used in the TPTP and need to exist before the 
%----transformations and formats are loaded. They are also declared at 
%----runtime in tptp2X/4.
:-op(70,fx,'$$').
:-op(80,fx,'$').
:-op(80,fx,'#').
:-op(90,xfx,/).     %----Rationals need to bind tighter than =
:-op(100,fx,++).
:-op(100,fx,--).
%----Postfix for !=
:-op(100,xf,'!').
%---- .. used for range in tptp2X. Needs to be stronger than :
:-op(400,xfx,'..').
%----! and ? are of higher precedence than : so ![X]:p(X) is :(![X],p(X))
%----Otherwise ![X]:![Y]:p(X,Y) cannot be parsed.
%----! is fy so Prolog can read !! (blah) as !(!(blah)) and it gets fixed
:-op(400,fy,!).
:-op(400,fx,?).
:-op(400,fx,^).
:-op(400,fx,'!>').
:-op(400,fx,'?*').
:-op(400,fx,'@-').
:-op(400,fx,'@+').
:-op(401,fx,'@@-').
:-op(401,fx,'@@+').
:-op(402,fx,'!!').
:-op(402,fx,'??').
:-op(403,yfx,*).     %----X product
:-op(403,yfx,+).     %----Union
%----= must bind more tightly than : for ! [X] : a = X. = must binder looser
%----than quantifiers for otherwise X = ! [Y] : ... is a syntax error (the =
%----grabs the quantifier). That means for THF it is necessary to bracket 
%----formula terms, e.g., a = (! [X] : p(X))
:-op(405,xfx,'=').
%---!= not possible because ! is special - see postfix cheat :-op(405,xfx,'!=').
:-op(440,xfy,>).     %----Type arrow
%----Made @ stronger than : for TH1 type construction, e.g., rs: stream @ rule
%----Need : stronger than binary connectives for ! [X] : p(X) <=> !Y ...
%----Need ~ and : equal and right-assoc for ![X] : ~p and for ~![X] : ...
:-op(450,fy,~).      %----Logical negation
:-op(450,xfy,:).
:-op(501,yfx,@).
:-op(1102,xfy,'|').
:-op(1102,xfx,'~|').
:-op(1103,xfy,&).
:-op(1103,xfx,~&).
:-op(1104,xfx,=>).
:-op(1104,xfx,<=).
:-op(1105,xfx,<=>).
:-op(1105,xfx,<~>).
:-op(1110,xfx,-->).
:-op(1150,xfx,:=).
