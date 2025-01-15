#include "utils.lp".
#include "../redundant/clause_level.lp".
#include "../incremental/clause.lp".
#include "DuoAI.lp".
#include "flyvy.lp".

#const length = 4. % The length of clauses, can be increased with very little extra grounding effort

#external my_length(1..length).
:- #count{Pred,Vars,Pos:output(Pred,Vars,Pos)}!=L, my_length(L), not flyvy.

% duoai.

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
E{exists(Var):var_used(Var)}E:-exists_length(E), not flyvy.
:- exists(Var1), var_type(Var1,Type), not exists(Var2), var_type(Var2,Type), var_used(Var2), not flyvy.



#show exists/1.


var_used_time(Var,Times):-var_type(Var,_),Times=1..length,#count{Pred,Vars,Pos:output(Pred,Vars,Pos),var_in(Var,Vars)}=Times.
var_used(Var):-var_used_time(Var,Times),Times>0.
var_used_more(Var):-var_used_time(Var,Times),Times>1.
#show var_used/1.

one_to_one:-my_length(2),exists_length(0), not to_deal_with.
to_more:-to_type(T),var_used(Var1),var_type(Var1,T),var_used(Var2),var_type(Var2,T),Var1<Var2.

% to_deal_with:- var_type(_,Type), #count{Var:var_used(Var),var_type(Var,T)}>2.
to_deal_with:- output(_,Vars,_), var_type(_,Type), #count{Var:var_in(Var,Vars),var_type(Var,T)}>1.
% opt: this is to be generalised

% var_compress(Var2,Var1):-var_used(Var1),var_used(Var2),Var1<Var2, var_type(Var1,Type),var_type(Var2,Type).

one2one(2*No1_new+(1-Pos1),2*No2_new+Pos2):- one_to_one, output_no(No1,Pos1),output_no(No2,Pos2),No1!=No2, atom_subst(No1,No1_new,St),atom_subst(No2,No2_new,St), not to_more.
one2one(2*No1_new+(1-Pos1),2*No2_new+Pos2):- one_to_one, output_no(No1,Pos1),output_no(No2,Pos2),No1!=No2, atom_subst(No1,No1_new,St),atom_subst(No2,No2_new,St), to_more, not to_subst(St).

#show one2one/2.


to_type(to_hide_warning).
individual(to_hide_warning).

