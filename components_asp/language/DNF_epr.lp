length_of_dnf(3).
length_of_ands(3). % cubes
max_literals(4).

{dnf(X)}:-length_of_dnf(N), X=1..N.

dnf(1).

:- dnf(X), X>1, not dnf(X-1).

{ands(D,Head,Tuple,Pos)}:-dnf(D), all_term(Head,Tuple), Pos = 0..1.

:- max_literals(L), #count{D,Head,Tuple,Pos:ands(D,Head,Tuple,Pos)} > L.

% EPR

% TODO: partial order, function symbols