#external flyvy.
more_type(T):-var_used(Var1),var_type(Var1,T),var_used(Var2),var_type(Var2,T),Var1<Var2.
more_type_num(N):-N=0..3,#count{T:more_type(T)}=N.
:- #count{Pred,Vars,Pos:output(Pred,Vars,Pos)}!=L-N, my_length(L),more_type_num(N), flyvy.

:- flyvy, output(Pred,_,_),individual(Pred). %nesting