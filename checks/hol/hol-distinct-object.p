% A distinct object still parses in thf, so a higher-order problem can carry a
% distinct group. DistinctGroupExpansion cannot run here (it would descend into the
% lambda and hit NOT_IMPLEMENTED), and skipping it would silently drop the
% disequalities the group stands for -- so this must be rejected, not answered.

thf(x_decl, type, "x": $i ).
thf(y_decl, type, "y": $i ).
thf(q_type, type, q: $i > $o ).
thf(p_type, type, p: ( $i > $o ) > $o ).
thf(ax_lam, axiom, ( p @ ( ^ [X: $i] : ( q @ X ) ) ) ).
thf(thm, conjecture, ? [F: $i > $o] : ( p @ F ) ).
