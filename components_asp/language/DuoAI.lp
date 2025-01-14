
max_pos_exists(3):-duoai.
#show max_pos_exists/1.
:- max_pos_exists(Max), exists(Var0), var_type(Var0,Type0), #count{Type:var_type(Var,Type), Var>Var0, Type!=Type0}>=Max.