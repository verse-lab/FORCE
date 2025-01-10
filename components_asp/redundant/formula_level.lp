:-var_type(Var1,Type),var_type(Var2,Type),Var1<Var2, var_used(Var2),not var_used(Var1).

% symmetry breaking

% Relations

min_pick(P,L):- pick(P,L,_), #count{L0:pick(P,L0,_),L0<L}==0.

:- pick_num(P1,N),pick_num(P2,N),P1<P2, min_pick(P1,L1),min_pick(P2,L2),L1>L2.

pred_pick_po(Pred1,P1,Pred2,P2):-pick(P1,_,_),pick(P2,_,_),pred_vars_no(_,Pred1,_),pred_vars_no(_,Pred2,_),Pred1<Pred2.
pred_pick_po(Pred,P1,Pred,P2):-pred_vars_no(_,Pred,_), pick(P1,_,_),pick(P2,_,_),P1<P2.


var_min_in(Var,Pred,P):-pick(P,L,_),pred_vars_no(L,Pred,Vars),var_in(Var,Vars),#count{P0,Pred0:pick(P0,L0,_),pred_vars_no(L0,Pred0,Vars0),var_in(Var,Vars0),pred_pick_po(Pred0,P0,Pred,P)}==0.


% Warning: EPR only (since no different quantifiers within a single type)

:- var_type(Var,Type),var_min_in(Var,Pred,P),not to_type(Type), #count{Var0:var_min_in(Var0,Pred0,P0),var_type(Var0,Type),Var0>Var,pred_pick_po(Pred0,P0,Pred,P)}!=0.


:-individual(Pred), output(_,Pred,(Var,),_),not var_used_more(Var).

% tauto or redundant

:- pick(P1,L,_), pick(P2,L,_), P1<P2.
:- pick(P,L,0),pick(P,L,1).

% Lemma 6 (amended version)

:- pick_num(P,N),N>1, pick(P,L,_),pred_vars_no(L,_,Vars), #count{Var:var_in(Var,Vars), not forall_leading(Var)}=0.

% TODO: see if encoding the original lemma 6 is cheap



% :- exists(0).

% prefix. (f(X1)/\f(X2))\/g(X) where X contains no X1 or X2, then it is subsumed by f(X1)\/g(X).

:- pick(P0,_,_),P0!=P,pick(P,L1,Pos),pick(P,L2,Pos),L1<L2,pred_vars_no(L1,Pred,Vars1),pred_vars_no(L2,Pred,Vars2),min_subst(Vars1,Vars2,St0),all_subst_sum(St0,N),#count{Var1,Var2: Var1!=Var2,var_used_time(Var1,P,1),var_used_time(Var2,P,1),var_subst(St0,Var1,Var2),var_in(Var1,Vars1),var_in(Var2, Vars2),not var_used_p(Var1,P0),not var_used_p(Var2,P0)}==N.

% TODO: bagged_simplified



% Q1 forall X1. Q2 A== Q1 forall X1!=X2. Q2 A and A(X2/X1).


:- pick(P,L1,Pos),pick(P,L2,Pos),pred_vars_no(L1,Pred,Vars1),pred_vars_no(L2,Pred,Vars2), L1<L2, min_subst(Vars1,Vars2,St),all_subst_sum(St,N), #count{Var1,Var2: Var1!=Var2,var_in(Var1,Vars1),var_in(Var2,Vars2),var_subst(St,Var1,Var2),not to_type(Var1),not exists(Var1)}==N.

% remove_redundancy_in_anded_literal
% Maybe not valid since we have clauses for pruning
:- pick(P1,L1,Pos),pick(P2,L2,1-Pos),P1<P2,pred_vars_no(L1,Pred,Vars1),pred_vars_no(L2,Pred,Vars2), all_subst_sum(St,N), min_subst(Vars1,Vars2,St), #count{Var1,Var2: Var1!=Var2,var_in(Var1,Vars1),var_in(Var2,Vars2),var_subst(St,Var1,Var2),not to_type(Var1),not exists(Var1)}==N.

% TODO: did I ensure that subst is unique? e.g. a subst is changing no var

% TODO: generalize_exists_xpxx_invs