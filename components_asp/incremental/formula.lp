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
