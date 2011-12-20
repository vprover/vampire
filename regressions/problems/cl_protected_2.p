%if not protected, the content of this file would get eliminated
%by pure predicate removal

% params: --mode clausify --protected_prefix aa_
% grep: aa_p

fof(a,axiom,aa_p(a)).
