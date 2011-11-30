% params: --epr_restoring_inlining on
% res: sat

fof(axiom_404,axiom,(
    ! [X,Y] :
      ( ihasTopping(X,Y)
    <=> iisToppingOf(Y,X) ) )).

fof(axiom_420,axiom,(
    ! [X,Y] :
      ( iisToppingOf(X,Y)
    <=> ihasTopping(Y,X) ) )).
