% The (empty) model FMB prints for fmb/no-symbols.p, read back: an empty model block is a
% model, unlike none at all.
%
% A problem without a single symbol (Problems/SYN/SYN916-1.p). Its model is empty -- no sorts,
% nothing to define -- and must still be printed, between the SZS FiniteModel markers, rather
% than taken for no model at all (an empty string used to mean that). model_check reads the
% empty model back (fmb/no-symbols.check.p).

cnf(true_clause,negated_conjecture,
    $true ).

vampire(model_check,model_start).
vampire(model_check,model_end).
