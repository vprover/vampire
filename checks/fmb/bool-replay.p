% SEU502_8 without its conjecture, plus in(emptyset,emptyset). FOOL elimination turns the
% definition into emptysetE <=> ! [Xx] : (in(Xx,emptyset) => ! [Xphi:$o] : ($true = Xphi)),
% preprocessing removes it as unused, and the clauses left never mention $o. FMB used to
% leave $o a one-element domain, replay the definition there, find ! [Xphi:$o] : ... true
% and so make emptysetE true -- while it is false, as in(emptyset,emptyset) holds. Now $o
% is built in with its two elements (FMB/FiniteModelBuilder.cpp, onModelFound).
% Under -newcnf on, the definition is taken out before FOOL is eliminated, so not even the
% FOOL constants exist when the model is built: that used to stop the replay with "this
% model does not have a boolean domain" (-fmbmp explicit) or "FMB constructed a partial
% model: no value for $false" (-fmbmp layered). (SEU527_8 without its conjecture.)
tff(in_type,type, in: ( $i * $i ) > $o ).
tff(emptyset_type,type, emptyset: $i ).
tff(emptysetE_type,type, emptysetE: $o ).
tff(emptysetE,definition,
    ( emptysetE = ( ! [Xx: $i] : ( in(Xx,emptyset) => ! [Xphi: $o] : (Xphi) ) ) ) ).
tff(ax,axiom, in(emptyset,emptyset) ).
