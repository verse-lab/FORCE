% #include "../incremental/formula.lp".
#include "utils.lp".

% #external max_cube(2;3;4).
% max_cube(2).
% #external max_lit(4;5;6).

{var(Var)}:- var_type(Var,_).
:-var_type(Var1,Type),var_type(Var2,Type),Var1<Var2, var(Var2),not var(Var1).

#show var/1.

% TODO: PO
1{exists(Var):var(Var)}1.
:- exists(Var1), var_type(Var1,Type), not exists(Var2), var_type(Var2,Type), var(Var2).

#show exists/1.

forall_leading(Var):-exists(Var0),var(Var),Var<Var0.

% :- formula_subst(_,G,H,_), cube_length(G,L1), cube_length(H,L2), L1+L2!=L, max_cube(L).
% :- #count{F,G,H,St:formula_subst(F,G,H,St)} !=1.



% cube(X):-pred_vars_no(X,_,_).
% lit_in(X,2*X, 0):-pred_vars_no(X,_,_).
% lit_in(X,2*X+1,1):-pred_vars_no(X,_,_).
% cube_length(2*X,1):- pred_vars_no(X,_,_).
% cube_length(2*X+1,1):- pred_vars_no(X,_,_).
cube_subst(2*X,2*Y,St):-lit_subst(X,Y,St).
cube_subst(2*X+1,2*Y+1,St):-lit_subst(X,Y,St).

var_in_cube(Var,2*Lit):-pred_vars_no(Lit,_,Vars), var_in(Var,Vars).
var_in_cube(Var,2*Lit+1):-pred_vars_no(Lit,_,Vars), var_in(Var,Vars).

% #show cube_subst/3.

% R1: G0 \/ F0..  R2: (F..) \/ H, that is F .. can be from genearlisation instead of in the rule (to check whether the po is enough for this case). F -subst-> F0
% To use: var_used, exists, varnum
po_rule(R1,R2):-rule_varnum(R1,N1),rule_varnum(R2,N2),N1>N2.
po_rule(R1,R2):-rule_varnum(R1,N1),rule_varnum(R2,N2),N1=N2,R1<R2.

1{pick_rule(R1,R2):po_rule(R1,R2)}1.
#show pick_rule/2.

rule1(R1):-pick_rule(R1,_).
rule2(R2):-pick_rule(_,R2).

1{the_subst(St):all_subst(St)}1.

#show the_subst/1.

% Vars in formula should be selected; selected vars should be used in the formula; exists should be used in the formula

var_in_formula(V):-rule1(R1),rule_used(R1,V).
var_in_formula(V):-rule2(R2),rule_used(R2,V0),the_subst(St),var_subst(St,V0,V).

:- var(V), not var_in_formula(V).
:- var_in_formula(V), not var(V).

exists_in_formula1(V):-rule1(R1),rule_exists(R1,V).
exists_in_formula2(V):-rule2(R2),rule_exists(R2,V0),the_subst(St),var_subst(St,V0,V).
% #show exists_in_formula/1.
exists_in_formula(V):-exists_in_formula1(V), exists_in_formula2(V).
:- #count{V:exists_in_formula(V)}!=1.
:- exists_in_formula(V), not exists(V).

% TODO
% :- exists(0).

% The substitution shouldn't contain invalid subst
:- rule2(R2), the_subst(St), all_subst_sum(St,N), #count{Type: rule_used(R2,V), var_subst(St,V,V0), V!=V0, var_type(V0,Type)}!=N.


conjunction(G0,H):-pick_rule(R1,R2),the_subst(St),rule(R1,G0),rule(R2,H),#count{F: cube_subst(F,F0,St),rule(R2,F), F!=H, not rule(R1,F0)}==0.
% conjunction(G0,H):-pick_rule(R1,R2),the_subst(St),rule(R1,G0),rule(R2,H),#count{F: cube_subst(F,F0,St),rule(R2,F), F!=H, not rule(R1,F0)}==0, var_in_cube(Var1,G0), not forall_leading(Var1), var_in_cube(Var2,H), var_subst(St,Var2,Var0), not forall_leading(Var0).

% #show conjunction/2.
:- not conjunction(_,_).


% lemma 6's amendment: not all vars in G0 should be leading (can be encoded in conjunction as var_in_cube(Var,G0), not forall_leading(Var)
:- conjunction(G0,_), #count{Var: var_in_cube(Var,G0), not forall_leading(Var)}=0.
:- conjunction(_,H), the_subst(St), #count{Var: var_in_cube(Var,H), var_subst(St,Var,Var0), not forall_leading(Var0)}=0.


% #show formula_subst/6.

% TODO: exist . member  -> exist (member/\?)\/?