fof(a1,external,![Arg2]:?[Arg1]:attribute(Arg1,Arg2),"externSql.py").
fof(a2,external,![Arg1]:?[Arg2]:attribute(Arg1,Arg2),"externSql.py").
fof(a3,external,![Arg2]:?[Arg1]:birthdate(Arg1,Arg2),"externSql.py").
fof(a4,external,![Arg1]:?[Arg2]:birthdate(Arg1,Arg2),"externSql.py").

fof(who,conjecture,
    ? [Composer,BirthDay,BirthMonth,BirthYear] :
      ( attribute(Composer,composer)
      & birthdate(Composer,BirthYear)
      & $greatereq(BirthYear,1700)
      & $lesseq(BirthYear,1750) ) ).
