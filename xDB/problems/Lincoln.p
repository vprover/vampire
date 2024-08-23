fof(a1,external,![Arg2]:?[Arg1]:instance(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a2,external,![Arg1]:?[Arg2]:instance(Arg1,Arg2),"$XDB/scripts/externSql.py").

fof(kb_SUMO_28,axiom,(
    ! [V__X,V__Y,V__Z] :
      ( ( instance(V__Y,setOrClass)
        & instance(V__X,setOrClass) )
     => ( ( subclass(V__X,V__Y)
          & instance(V__Z,V__X) )
       => instance(V__Z,V__Y) ) ) )).

fof(kb_SUMO_5811,axiom,(
    instance(mammal,setOrClass) )).

fof(kb_SUMO_5813,axiom,(
    subclass(primate,mammal) )).

fof(kb_SUMO_5818,axiom,(
    instance(primate,setOrClass) )).

fof(kb_SUMO_5823,axiom,(
    subclass(hominid,primate) )).

fof(kb_SUMO_5824,axiom,(
    instance(hominid,setOrClass) )).

fof(kb_SUMO_5826,axiom,(
    subclass(human,hominid) )).

fof(kb_SUMO_5836,axiom,(
    instance(human,setOrClass) )).

% fof(cheat,axiom,instance(abrahamLincoln,human)).

fof(abe_mammal,conjecture,(
    instance(abrahamLincoln,mammal) )).
