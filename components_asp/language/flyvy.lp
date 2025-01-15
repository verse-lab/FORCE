
E{exists(Var):possible_exist(Var),var_used(Var)}E:-exists_length(E), flyvy.

:- not exists(Var1), var_type(Var1,Type), Var1<Var2, exists(Var2), var_type(Var2,Type), var_used(Var1), flyvy. % EPR

more_type(T):-var_used(Var1),var_type(Var1,T),var_used(Var2),var_type(Var2,T),Var1<Var2,to_type(T).
more_type_num(N):-N=0..3,#count{T:more_type(T)}=N.
:- #count{Pred,Vars,Pos:output(Pred,Vars,Pos)}!=L-N, my_length(L),more_type_num(N), flyvy.

:- flyvy, output(Pred,_,_),individual(Pred), nesting(_). %nesting

:- never_used(Var),var_used(Var),flyvy.