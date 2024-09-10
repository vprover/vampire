fof(a1,external,![Arg2:$i]:?[Arg1:$i]:s__familyName(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a2,external,![Arg1:$i]:?[Arg2:$i]:s__familyName(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a3,external,![Arg2:$int]:?[Arg1:$i]:s__wonPrize(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a4,external,![Arg1:$i]:?[Arg2:$int]:s__wonPrize(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a5,external,![Arg2:$int]:?[Arg1:$i]:s__givenName(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a6,external,![Arg1:$i]:?[Arg2:$int]:s__givenName(Arg1,Arg2),"$XDB/scripts/externSql.py").

fof(who,conjecture,
    ? [FullName,GivenName,Prize] :
      ( s__familyName('Curie',FullName)
      & s__wonPrize(FullName,Prize)
      & s__givenName(GivenName,FullName))).
