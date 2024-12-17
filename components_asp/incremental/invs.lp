#program invs(n, r, v, p).
valid_inv(n, r, v, p).

% #program clause_inv(r, v, p).
% clause_valid_inv(r, v, p).

% TODO: inv in dnf

% Tautology

:- subst(S),clause(C),inv_length(N,L), #count{Head,Tuple,Pos:ands(C,Head,Tuple,Pos), valid_inv(N,Head,Tuple,1-Pos)}==L.

