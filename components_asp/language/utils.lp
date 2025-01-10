% Variable tuple substitution

% Temp implementation: assume the number of each sort <= 2, then represented as swapped or not.
% For more, orbit is needed.

var_in(X1,(X1,)):-pred_vars_no(_,_,(X1,)).
var_in(X1,(X1,X2)):-pred_vars_no(_,_,(X1,X2)).
var_in(X2,(X1,X2)):-pred_vars_no(_,_,(X1,X2)).
var_in(X1,(X1,X2,X3)):-pred_vars_no(_,_,(X1,X2,X3)).
var_in(X2,(X1,X2,X3)):-pred_vars_no(_,_,(X1,X2,X3)).
var_in(X3,(X1,X2,X3)):-pred_vars_no(_,_,(X1,X2,X3)).
var_in(X1,(X1,X2,X3,X4)):-pred_vars_no(_,_,(X1,X2,X3,X4)).
var_in(X2,(X1,X2,X3,X4)):-pred_vars_no(_,_,(X1,X2,X3,X4)).
var_in(X3,(X1,X2,X3,X4)):-pred_vars_no(_,_,(X1,X2,X3,X4)).
var_in(X4,(X1,X2,X3,X4)):-pred_vars_no(_,_,(X1,X2,X3,X4)).

atom_subst(L1,L2,St):-pred_vars_no(L1,Pred,Vars1),pred_vars_no(L2,Pred,Vars2),subst(Vars1,Vars2,St).

% #show lit_subst/3.

% TODO: this should be used for better pruning
min_var_subst(St0,Var1,Var2):-var_subst(St0,Var1,Var2),#count{St:var_subst(St,Var1,Var2),all_subst_sum(St,N),all_subst_sum(St0,N0),N<N0}=0.
min_subst(Vars1,Vars2,St0):-subst(Vars1,Vars2,St0),#count{St:subst(Vars1,Vars2,St),all_subst_sum(St,N),all_subst_sum(St0,N0),N<N0}=0.

to_subst(St):-var_subst(St,Var1,Var2),Var1<Var2, to_type(Type),var_type(Var1,Type).
