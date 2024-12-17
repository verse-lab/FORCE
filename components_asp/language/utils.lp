% Variable tuple substitution

% Temp implementation: assume the number of each sort <= 2, then represented as swapped or not.

% #defined subst/3.

% For more, orbit is needed.

var_in(X1,(X1,)):-pred_vars_no(_,_,(X1,)).
var_in(X1,(X1,X2)):-pred_vars_no(_,_,(X1,X2)).
var_in(X2,(X1,X2)):-pred_vars_no(_,_,(X1,X2)).
var_in(X1,(X1,X2,X3)):-pred_vars_no(_,_,(X1,X2,X3)).
var_in(X2,(X1,X2,X3)):-pred_vars_no(_,_,(X1,X2,X3)).
var_in(X3,(X1,X2,X3)):-pred_vars_no(_,_,(X1,X2,X3)).

lit_subst(L1,L2,St):-pred_vars_no(L1,Pred,Vars1),pred_vars_no(L2,Pred,Vars2),subst(Vars1,Vars2,St).

% #show lit_subst/3.
