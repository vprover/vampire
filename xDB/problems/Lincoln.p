fof(a1,external,![Arg2]:?[Arg1]:s__instance(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a2,external,![Arg1]:?[Arg2]:s__instance(Arg1,Arg2),"$XDB/scripts/externSql.py").

fof(kb_SUMO_28,axiom,(
    ! [V__X,V__Y,V__Z] :
      ( ( s__instance(V__Y,s__SetOrClass)
        & s__instance(V__X,s__SetOrClass) )
     => ( ( s__subclass(V__X,V__Y)
          & s__instance(V__Z,V__X) )
       => s__instance(V__Z,V__Y) ) ) )).

fof(kb_SUMO_5811,axiom,(
    s__instance(s__Mammal,s__SetOrClass) )).

fof(kb_SUMO_5813,axiom,(
    s__subclass(s__Primate,s__Mammal) )).

fof(kb_SUMO_5818,axiom,(
    s__instance(s__Primate,s__SetOrClass) )).

fof(kb_SUMO_5823,axiom,(
    s__subclass(s__Hominid,s__Primate) )).

fof(kb_SUMO_5824,axiom,(
    s__instance(s__Hominid,s__SetOrClass) )).

fof(kb_SUMO_5826,axiom,(
    s__subclass(s__Human,s__Hominid) )).

fof(kb_SUMO_5836,axiom,(
    s__instance(s__Human,s__SetOrClass) )).

% fof(cheat,axiom,s__instance(s__AbrahamLincoln,s__Human)).

fof(abe_mammal,conjecture,(
    s__instance(s__AbrahamLincoln,s__Mammal) )).
