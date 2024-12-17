%  Q X1,X2 B, X1 not in B.
:-var_type(Var1,Type),var_type(Var2,Type),Var1<Var2, var_used(Var2),not var_used(Var1).
% Symmetry breaking
diff_pred:-output(Pred1,_,_),output(Pred2,_,_),Pred1<Pred2.
:-diff_pred,var_type(Var1,Type),var_type(Var2,Type),not to_type(Type),Var1<Var2, output(Pred2,Vars2,_),var_in(Var2,Vars2), #count{Pred1:output(Pred1,Vars1,_),var_in(Var1,Vars1),Pred1<Pred2}=0.

:- not diff_pred, output(Pred,Vars1,_),output(Pred,Vars2,_),Vars1<Vars2, var_type(Var1,Type),var_type(Var2,Type),not to_type(Type), Var1>Var2, var_in(Var1,Vars1),var_in(Var2,Vars2).
%  Q X1,X2 f(X2) \/ g(X1). not prune since clause->formula!
% :- output(Pred,Vars,_), #count{Var:var_in(Var,Vars),var_used_more(Var)}==0.

:-individual(Pred), output(Pred,(Var,),_),not var_used_more(Var), not my_length(1).
% :-individual(Pred), output(Pred,(Var,),_), exists(Var). % TODO: make sure that this is theoretically correct for ivy
% 
:- output(Pred,V,0),output(Pred,V,1).


% TODO: with exist, but not in?

% TODO:DE?
% :- output(Pred,V1,_),output(Pred,V2,_),V1<V2, #count{Var:exists(Var),var_in(Var,V1),not var_in(Var,V2);Var:exists(Var), not var_in(Var,V1), var_in(Var,V2)}!=2.

% :- #count{Var:output(Pred1,Vars1,_),output(Pred2,Vars2,_),var_in(Var,Vars1),var_in(Var,Vars2),Pred1<Pred2}=0.