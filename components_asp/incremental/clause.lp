% TODO: check whether to_type is correctly handled

#program correct_inv2(n,np1,pos1,np2,pos2).
correct(n,Pred,Vars,pos1):-pred_vars_no(np1,Pred,Vars).
correct(n,Pred,Vars,pos2):-pred_vars_no(np2,Pred,Vars).

% #show correct/4.


:- all_subst(St), #count{Pred,Vars,Pos: output(Pred,Vars,Pos),correct(n,Pred,Vars0,Pos),subst(Vars0,Vars,St)}=2.

#program correct_inv3(n,np1,pos1,np2,pos2,np3,pos3).
correct(n,Pred,Vars,pos1):-pred_vars_no(np1,Pred,Vars).
correct(n,Pred,Vars,pos2):-pred_vars_no(np2,Pred,Vars).
correct(n,Pred,Vars,pos3):-pred_vars_no(np3,Pred,Vars).

% #show correct/4.


:- all_subst(St), #count{Pred,Vars,Pos: output(Pred,Vars,Pos),correct(n,Pred,Vars0,Pos),subst(Vars0,Vars,St)}=3.



#program correct_inv1_exi(n,np1,pos1,var). %TODO: more vars
% inv_exist(n,var).
correct(n,Pred,Vars,pos1):-pred_vars_no(np1,Pred,Vars).


% debug_exists(n,Var):- inv_exist(n,Var).
% #show debug_exists/2.

:- all_subst(St), #count{Pred,Vars,Pos: output(Pred,Vars,Pos),correct(n,Pred,Vars0,Pos),subst(Vars0,Vars,St)}=1,exists(V), var_subst(St,var,V).

#program correct_inv2_exi(n,np1,pos1,np2,pos2,var).
% inv_exist(n,var).
correct(n,Pred,Vars,pos1):-pred_vars_no(np1,Pred,Vars).
correct(n,Pred,Vars,pos2):-pred_vars_no(np2,Pred,Vars).


:- all_subst(St), #count{Pred,Vars,Pos: output(Pred,Vars,Pos),correct(n,Pred,Vars0,Pos),subst(Vars0,Vars,St)}=2,exists(V), var_subst(St,var,V).



% #program correct_inv(n,np1,pos1,sz).
% #external inv_exist(n,Var): var_used(Var).
% correct(n,Pred,Vars,pos1):-pred_vars_no(np1,Pred,Vars).

% debug_exists(N,Var):- inv_exist(N,Var). % TODO: understand why this is needed
% % #show debug_exists/2.

% :- all_subst(St,_), #count{Pred,Vars,Pos: output(Pred,Vars,Pos),correct(n,Pred,Vars0,Pos),subst(Vars0,Vars,St)}=sz, not debug_exists(n,_).
% :- all_subst(St,_), #count{Pred,Vars,Pos: output(Pred,Vars,Pos),correct(n,Pred,Vars0,Pos),subst(Vars0,Vars,St)}=sz, debug_exists(n,V0), exists(V), var_subst(St,V0,V).
