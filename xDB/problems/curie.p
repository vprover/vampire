fof(a1,external,![Arg2]:?[Arg1]:s__familyName(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a2,external,![Arg1]:?[Arg2]:s__familyName(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a3,external,![Arg2]:?[Arg1]:s__wonPrize(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a4,external,![Arg1]:?[Arg2]:s__wonPrize(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a5,external,![Arg2]:?[Arg1]:s__givenName(Arg1,Arg2),"$XDB/scripts/externSql.py").
fof(a6,external,![Arg1]:?[Arg2]:s__givenName(Arg1,Arg2),"$XDB/scripts/externSql.py").

fof(who,conjecture,
    ? [FullName,GivenName,Prize] :
      ( s__familyName(s__Curie,FullName)
      & s__wonPrize(FullName,Prize)
      & s__givenName(GivenName,FullName))).
