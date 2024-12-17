#include "../incremental/formula.lp".
% #include "tmp.lp".
#include "utils.lp".
#include "../redundant/formula_level.lp".

% #external max_cube(2;3;4).
% max_cube(2).
% #external max_lit(4;5;6).

% {var(Var)}:- var_type(Var,_).
% :-var_type(Var1,Type),var_type(Var2,Type),Var1<Var2, var(Var2),not var(Var1).

% #show var/1.

% TODO: deal with multiple existential variables!
1{exists(Var):var_used(Var)}1.
:- exists(Var1), var_type(Var1,Type), not exists(Var2), var_type(Var2,Type), var_used(Var2).

#show exists/1.

forall_leading(Var):-exists(Var0),var_used(Var),Var<Var0.

pos(0;1).
lit_num(X):- pred_vars_no(X,_,_).

oppcube(2*X,2*X+1):-lit_num(X).
oppcube(2*X+1,2*X):-lit_num(X).

#external pick_num_in(1,2;1,3).
#external pick_num_in(2,0;2,1;2,2).
#external pick_num_in(3,0;3,1).

% #show pick_num_in/2.

pick_num(P,N):-pick_num_in(P,N).

% pick_num(1,3).
% pick_num(2,1).
% pick_num(3,0).

N{pick(P,L,Pos):lit_num(L),pos(Pos)}N:-pick_num(P,N).

output_no(P,2*L+Pos):-pick(P,L,Pos).
#show output_no/2.



output(P,Pred,Vars,Pos):-pick(P,L,Pos),pred_vars_no(L,Pred,Vars).
#show output/4.

var(Var):-var_type(Var,_).
var_in_lit(Var,Lit):-pred_vars_no(Lit,_,Vars),var_in(Var,Vars).

var_used_time(Var,P,Times):-pick_num(P,N),var(Var),Times = 1..N, #count{L,Pos:pick(P,L,Pos),var_in_lit(Var,L)}=Times.
var_used_more(Var):-var_used_time(Var,P,Times),Times>1.
var_used(Var):-var_used_time(Var,P1,1),var_used_time(Var,P2,1),P1<P2.
var_used_p(Var,P):-var_used_time(Var,P,_).
var_used(Var):-var_used_p(Var,_).
#show var_used/1.

% Now we start to modulo the clauses

% First, we need to extract all subsumed clauses
pick3(2*L1+Pos1,2*L2+Pos2,2*L3+Pos3):-pick(1,L1,Pos1),pick(2,L2,Pos2),pick(3,L3,Pos3), not pick_num(3,0).
pick2(2*L1+Pos1,2*L2+Pos2):-pick(1,L1,Pos1),pick(2,L2,Pos2), not pick(3,_,_), pick_num(3,0).
pick1(2*L1+Pos1):-pick(1,L1,Pos1), not pick(2,_,_), pick_num(2,0).

cube_subst(2*X,2*Y,St):-lit_subst(X,Y,St).
cube_subst(2*X+1,2*Y+1,St):-lit_subst(X,Y,St).

% There should be an existing clause that entails the subsumed clause
% From clauses: rule, rule_varnum, rule_used, rule_len, rule_exists, forall_rule

entail3_11(R,P1,P2,P3):- pick3(P1,P2,P3),all_subst(St), rule_len(R,1), rule(R,C),cube_subst(C,P1,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var).
p_used(P1):- entail3_11(_,P1,_,_).
entail3(R,P1,P2,P3):- entail3_11(R,P1,P2,P3).
entail3_12(R,P1,P2,P3):- pick3(P1,P2,P3),all_subst(St), rule_len(R,1), rule(R,C),cube_subst(C,P2,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var).
p_used(P2):- entail3_12(_,_,P2,_).
entail3(R,P1,P2,P3):- entail3_12(R,P1,P2,P3).
entail3_13(R,P1,P2,P3):- pick3(P1,P2,P3),all_subst(St), rule_len(R,1), rule(R,C),cube_subst(C,P3,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var).
p_used(P3):- entail3_13(_,_,_,P3).
entail3(R,P1,P2,P3):- entail3_13(R,P1,P2,P3).

% TODO: generating the entailment predicates by parameters

entail3_21(R,P1,P2,P3):- pick3(P1,P2,P3),all_subst(St), rule_len(R,2),rule(R,C1),cube_subst(C1,P1,St),rule(R,C2),cube_subst(C2,P2,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var).
p_used(P1):- entail3_21(_,P1,_,_).
p_used(P2):- entail3_21(_,_,P2,_).
entail3(R,P1,P2,P3):- entail3_21(R,P1,P2,P3).
entail3_22(R,P1,P2,P3):- pick3(P1,P2,P3),all_subst(St), rule_len(R,2), rule(R,C1),cube_subst(C1,P1,St),rule(R,C2),cube_subst(C2,P3,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var).
p_used(P1):- entail3_22(_,P1,_,_).
p_used(P3):- entail3_22(_,_,_,P3).
entail3(R,P1,P2,P3):- entail3_22(R,P1,P2,P3).
entail3_23(R,P1,P2,P3):- pick3(P1,P2,P3),all_subst(St), rule_len(R,2), rule(R,C1),cube_subst(C1,P2,St),rule(R,C2),cube_subst(C2,P3,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var).
p_used(P2):- entail3_23(_,_,P2,_).
p_used(P3):- entail3_23(_,_,_,P3).

entail3_30(R,P1,P2,P3):- pick3(P1,P2,P3),all_subst(St), rule_len(R,3),rule(R,C1),cube_subst(C1,P1,St),rule(R,C2),cube_subst(C2,P2,St),rule(R,C3),cube_subst(C3,P3,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var).
p_used(P1):- entail3_30(_,P1,_,_).
p_used(P2):- entail3_30(_,_,P2,_).
p_used(P3):- entail3_30(_,_,_,P3).
entail3(R,P1,P2,P3):- entail3_30(R,P1,P2,P3).

:-pick3(P1,P2,P3), not p_used(P1).
:-pick3(P1,P2,P3), not p_used(P2).
:-pick3(P1,P2,P3), not p_used(P3).

% #show entail3/4.

:- not entail3(_,P1,P2,P3),pick3(P1,P2,P3).

% cannot have A\/B\/(C/\D) if A\/B is correct TODO: more general
:- rule(R,_),not 0{entail3(R,P1,P2,P3)}1.

% TODO: check the body of entailment to avoid cube of length 1

% entail3(R,P1,P2,P3):- pick3(P1,P2,P3),all_subst(St), rule_len(R,N), N>1, N<=3, #count{C:rule(R,C),cube_subst(C,P1,St);C:rule(R,C),cube_subst(C,P2,St);C:rule(R,C),cube_subst(C,P3,St)}=N, rule_exists(R,V), var_subst(St,V,Var), exists(Var).

entail2_11(R,P1,P2):- pick2(P1,P2),all_subst(St), rule_len(R,1), rule(R,C),cube_subst(C,P1,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var), not pick_num(1,1).
p_used(P1):- entail2_11(_,P1,_).
entail2(R,P1,P2):- entail2_11(R,P1,P2).
entail2_12(R,P1,P2):- pick2(P1,P2),all_subst(St), rule_len(R,1), rule(R,C),cube_subst(C,P2,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var), not pick_num(2,1).
p_used(P2):- entail2_12(_,_,P2).
entail2(R,P1,P2):- entail2_12(R,P1,P2).

entail2_20(R,P1,P2):- pick2(P1,P2),all_subst(St), rule_len(R,2),rule(R,C1),cube_subst(C1,P1,St),rule(R,C2),cube_subst(C2,P2,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var).
p_used(P1):- entail2_20(_,P1,_).
p_used(P2):- entail2_20(_,_,P2).
entail2(R,P1,P2):- entail2_20(R,P1,P2).

:-pick2(P1,P2), not p_used(P1).
:-pick2(P1,P2), not p_used(P2).

% #show entail2/3.

:- not entail2(_,P1,P2),pick2(P1,P2).


entail1(R,P1):- pick1(P1),all_subst(St), rule_len(R,1), rule(R,C),cube_subst(C,P1,St), rule_exists(R,V), var_subst(St,V,Var), exists(Var).
p_used(P1):- entail1(_,P1).

:-pick1(P1), not p_used(P1).

#show entail1/2.

:- not entail1(_,P1),pick1(P1).

% deal with forall rule. Basically, forall X implies exists X, but check_if_inv_is_FOCAEI_redundant. (exists->forall?)

% If we need the existing one to prune, the length of cube need to be the same, but for forall, subset is okay
:- rule_len(R,N),forall_rule(R),all_subst(St), pick_num(P,Num), Num>=N, output_no(P,C0), rule(R,C), cube_subst(C,C0,St), #count{C1:output_no(P,C1),C1!=C0,oppcube(C1,C2),cube_subst(C2,Cr,St),rule(R,Cr)}=N-1.

:- rule_len(R,N),forall_rule(R),all_subst(St), pick_num(P,N), #count{C:output_no(P,C),oppcube(C,C1),cube_subst(C1,Cr,St),rule(R,Cr)}=N. % TODO: whether this is useful

