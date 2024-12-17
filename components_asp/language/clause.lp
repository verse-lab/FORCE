% All possible literals are restricted to be restricted by (1) signatures, (2) predicates. Clauses are once more restricted by quantifier alternations.
% TODO: extend this to support functions

#include "utils.lp".
#include "../redundant/clause_level.lp".
#include "../incremental/clause.lp".
% #include "tmp.lp".
#const length = 3.

#external my_length(1..length).
:- #count{Pred,Vars,Pos:output(Pred,Vars,Pos)}!=L, my_length(L).

pos(0;1).
#show output/3.
% TODO: why not length to length?
literal(Pred,Vars):-pred_vars_no(_,Pred,Vars).
1{output(Pred,Vars,Pos):literal(Pred,Vars),pos(Pos)}length.

output_no(No,Pos):-output(Pred,Vars,Pos),pred_vars_no(No,Pred,Vars).
#show output_no/2.

#external type_num(T,N):possible_type_num(T,N).
:- type_num(Type,Num),#count{Var:var_type(Var,Type),var_used(Var)}>Num.
% The prefix of formulas

#external exists_length(0;1).
#show exists_length/1.
% exists(4):-exists_length(1).
E{exists(Var):var_used(Var)}E:-exists_length(E).
:- exists(Var1), var_type(Var1,Type), not exists(Var2), var_type(Var2,Type), var_used(Var2).

#show exists/1.


var_used_time(Var,Times):-var_type(Var,_),Times=1..length,#count{Pred,Vars,Pos:output(Pred,Vars,Pos),var_in(Var,Vars)}=Times.
var_used(Var):-var_used_time(Var,Times),Times>0.
var_used_more(Var):-var_used_time(Var,Times),Times>1.
#show var_used/1.

% #external duoai.
duoai.

max_pos_exists(3):-duoai.
:- max_pos_exists(Max), exists(Var0), var_type(Var0,Type0), #count{Type:var_type(Var,Type), Var>Var0, Type!=Type0}>=Max.


% subtemplate(Var1,Var2):-var_used(Var1),var_used(Var2),Var1<Var2,duoai, var_type(Var1,Type),var_type(Var2,Type), not exists(Var1),not exists(Var2).
% #show subtemplate/2.


% #program dynamic_vars(r,v,q,n).

