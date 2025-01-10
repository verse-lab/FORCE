% TODO:generalize_invs?
% add_inv_with_permutations_and_subsets

% rule(1,3).
% rule(1,4).

% rule(2,3).
% rule(2,6).

% rule(3,5).
% rule(3,10).

% ...

% formula 3 \/ (4 /\ 6) is subsumed by 3 \/ 4, 3 \/ 6
% expressed by merging rule(1) and rule(2)
% mergable(1,2). 
% Should result in which vars are shared or not

% rule(Num,Cube1). rule(Num, Cube2). means that Cube1 \/ Cube2.




% Q X. F \/ (G /\ H) subsumes F \/ G, F \/ H, TODO: should be generalised to any number of conjunctions, and the size is to be restricted during grounding (by input the config). After pass the model checking , G /\ H becomes a new cube.

% {formula_subst(R1,G,H,0)}:-rule(R1,G),rule(R2,H),#count{F: rule(R1,F),not rule(R2,F);F:rule(R2,F),not rule(R1,F)}==0,G<H. 
% {formula_subst(F,G0,H,St)}:-rule(R1,F0),rule(R1,G0),rule(R2,F),rule(R2,H),partial_le(F0,F),cube_subst(F0,F,St).


% Second case: % Q X. F1 \/ F2 \/ (G /\ H) subsumes F1 \/ F2 \/ G, F1 \/ F2 \/ H, and F1 \/ H entails F1 \/ F2 \/ H.

% {formula(Rule, Cube_ori, Cube_new)}:-rule(Rule, Cube_ori),cube(Cube_new), cube_length(Cube_ori,L1), cube_length(Cube_new,L2),L1+L2<=max_cube.

outcube_entailed(C,Cube,St):- pick_num(C,1),all_subst(St),output_no(C,Lit),cube_subst(Lit,Cube,St).

% TODO: check whether to_type is correctly handled

#program cube2(n, lit1, lit2).

% cube(n).
cube_length(n,2).
lit_in(lit1, n).
lit_in(lit2, n).

% exist a subst, forall lit in C, lit*subst in n
outcube_entailed(C,n,St):-pick_num(C,N),N!=0,all_subst(St),#count{Lit:output_no(C,Lit),cube_subst(Lit,Lit1,St), not lit_in(Lit1,n)}=0.
% opt: see whether conditional rules are more efficient


#program cube3(n, lit1, lit2, lit3).

cube_length(n,3).
lit_in(lit1, n).
lit_in(lit2, n).
lit_in(lit3, n).

outcube_entailed(C,n,St):-pick_num(C,N),N!=0,all_subst(St),#count{Lit:output_no(C,Lit),cube_subst(Lit,Lit1,St), not lit_in(Lit1,n)}=0.


% TODO: more exists
#program valid_formula1(e,c).
:- outcube_entailed(_,c,Subst),exists(Var),var_subst(Subst,e,Var).

#program valid_formula2(e,c1,c2).

:- outcube_entailed(C1,c1,Subst),outcube_entailed(C2,c2,Subst),C1!=C2,exists(Var),var_subst(Subst,e,Var).
