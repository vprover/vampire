%----A tcf() (typed clause form) problem: clauses carrying an explicit universal
%----prefix that spells out the sort of each variable. Without it, the sort of the
%----variables of "X = Y" below would be anybody's guess in this two-sorted setting.
%----Type declarations may be given in tcf() as well (<tff_atom_typing> in the TCF
%----grammar); our parser is equally happy with tff() ones.
tcf(colour_type,type,
    colour: $tType ).

tcf(red_type,type,
    red: colour ).

tcf(green_type,type,
    green: colour ).

tcf(blue_type,type,
    blue: colour ).

tcf(paint_type,type,
    paint: ( $i * colour ) > $o ).

%----any three colours have two of them equal
tcf(only_two_colours,axiom,
    ! [X: colour,Y: colour,Z: colour] :
      ( X = Y
      | X = Z
      | Y = Z ) ).

%----but here are three that are not: a ground clause needs no prefix
tcf(red_is_not_green,axiom,
    red != green ).

tcf(red_is_not_blue,axiom,
    red != blue ).

tcf(green_is_not_blue,axiom,
    green != blue ).

%----and some clauses over the default type, once with the type left implicit
tcf(everything_is_blue,axiom,
    ! [W] : paint(W,blue) ).

tcf(nothing_is_red,axiom,
    ! [W: $i] : ~ paint(W,red) ).
