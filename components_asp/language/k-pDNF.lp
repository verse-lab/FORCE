length_of_k_pdnf(3).
length_of_ands(3). % cubes
max_literals(4).

{pdnf(X)}:-length_of_k_pdnf(N), X=1..N.

pdnf(1).

:- pdnf(X), X>1, not pdnf(X-1).

{ands(D,Head,Tuple,Pos)}:-pdnf(D), all_term(Head,Tuple), Pos = 0..1.

:- max_literals(L), #count{D,Head,Tuple,Pos:ands(D,Head,Tuple,Pos)} > L.