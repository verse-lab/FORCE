to_type(round).
var_type(0,round).
var_type(1,round).
possible_type_num(round,1;round,2).
var_type(2,value).
var_type(3,value).
possible_type_num(value,1;value,2).
var_type(4,quorum).
possible_type_num(quorum,1).
var_type(5,node).
var_type(6,node).
possible_type_num(node,1;node,2).
to_type(round).
var_type(0,round).
var_type(1,round).
possible_type_num(round,1;round,2).
var_type(2,value).
var_type(3,value).
possible_type_num(value,1;value,2).
var_type(4,quorum).
possible_type_num(quorum,1).
var_type(5,node).
var_type(6,node).
possible_type_num(node,1;node,2).
all_subst((0, 0, 0, 0)).
all_subst_sum((0, 0, 0, 0),0).

all_subst((0, 0, 0, 1)).
all_subst_sum((0, 0, 0, 1),1).

all_subst((0, 1, 0, 0)).
all_subst_sum((0, 1, 0, 0),1).

all_subst((0, 1, 0, 1)).
all_subst_sum((0, 1, 0, 1),2).

all_subst((1, 0, 0, 0)).
all_subst_sum((1, 0, 0, 0),1).

all_subst((1, 0, 0, 1)).
all_subst_sum((1, 0, 0, 1),2).

all_subst((1, 1, 0, 0)).
all_subst_sum((1, 1, 0, 0),2).

all_subst((1, 1, 0, 1)).
all_subst_sum((1, 1, 0, 1),3).

var_subst((0, 0, 0, 0),0,0).
var_subst((0, 0, 0, 0),2,2).
var_subst((0, 0, 0, 0),4,4).
var_subst((0, 0, 0, 0),5,5).
var_subst((0, 0, 0, 1),0,0).
var_subst((0, 0, 0, 1),2,2).
var_subst((0, 0, 0, 1),4,4).
var_subst((0, 0, 0, 1),5,6).
var_subst((0, 0, 0, 1),6,5).
var_subst((0, 1, 0, 0),0,0).
var_subst((0, 1, 0, 0),2,3).
var_subst((0, 1, 0, 0),3,2).
var_subst((0, 1, 0, 0),4,4).
var_subst((0, 1, 0, 0),5,5).
var_subst((0, 1, 0, 1),0,0).
var_subst((0, 1, 0, 1),2,3).
var_subst((0, 1, 0, 1),3,2).
var_subst((0, 1, 0, 1),4,4).
var_subst((0, 1, 0, 1),5,6).
var_subst((0, 1, 0, 1),6,5).
var_subst((1, 0, 0, 0),0,1).
var_subst((1, 0, 0, 0),1,0).
var_subst((1, 0, 0, 0),2,2).
var_subst((1, 0, 0, 0),4,4).
var_subst((1, 0, 0, 0),5,5).
var_subst((1, 0, 0, 1),0,1).
var_subst((1, 0, 0, 1),1,0).
var_subst((1, 0, 0, 1),2,2).
var_subst((1, 0, 0, 1),4,4).
var_subst((1, 0, 0, 1),5,6).
var_subst((1, 0, 0, 1),6,5).
var_subst((1, 1, 0, 0),0,1).
var_subst((1, 1, 0, 0),1,0).
var_subst((1, 1, 0, 0),2,3).
var_subst((1, 1, 0, 0),3,2).
var_subst((1, 1, 0, 0),4,4).
var_subst((1, 1, 0, 0),5,5).
var_subst((1, 1, 0, 1),0,1).
var_subst((1, 1, 0, 1),1,0).
var_subst((1, 1, 0, 1),2,3).
var_subst((1, 1, 0, 1),3,2).
var_subst((1, 1, 0, 1),4,4).
var_subst((1, 1, 0, 1),5,6).
var_subst((1, 1, 0, 1),6,5).
subst((0,),(0,),(0, 0, 0, 0)).
subst((0,),(0,),(0, 0, 0, 1)).
subst((0,),(0,),(0, 1, 0, 0)).
subst((0,),(0,),(0, 1, 0, 1)).
subst((0,),(1,),(1, 0, 0, 0)).
subst((0,),(1,),(1, 0, 0, 1)).
subst((0,),(1,),(1, 1, 0, 0)).
subst((0,),(1,),(1, 1, 0, 1)).
subst((0, 2),(0, 2),(0, 0, 0, 0)).
subst((0, 2),(0, 2),(0, 0, 0, 1)).
subst((0, 2),(0, 3),(0, 1, 0, 0)).
subst((0, 2),(0, 3),(0, 1, 0, 1)).
subst((0, 2),(1, 2),(1, 0, 0, 0)).
subst((0, 2),(1, 2),(1, 0, 0, 1)).
subst((0, 2),(1, 3),(1, 1, 0, 0)).
subst((0, 2),(1, 3),(1, 1, 0, 1)).
subst((0, 3),(0, 3),(0, 0, 0, 0)).
subst((0, 3),(0, 3),(0, 0, 0, 1)).
subst((0, 3),(0, 2),(0, 1, 0, 0)).
subst((0, 3),(0, 2),(0, 1, 0, 1)).
subst((0, 3),(1, 3),(1, 0, 0, 0)).
subst((0, 3),(1, 3),(1, 0, 0, 1)).
subst((0, 3),(1, 2),(1, 1, 0, 0)).
subst((0, 3),(1, 2),(1, 1, 0, 1)).
subst((1,),(1,),(0, 0, 0, 0)).
subst((1,),(1,),(0, 0, 0, 1)).
subst((1,),(1,),(0, 1, 0, 0)).
subst((1,),(1,),(0, 1, 0, 1)).
subst((1,),(0,),(1, 0, 0, 0)).
subst((1,),(0,),(1, 0, 0, 1)).
subst((1,),(0,),(1, 1, 0, 0)).
subst((1,),(0,),(1, 1, 0, 1)).
subst((1, 2),(1, 2),(0, 0, 0, 0)).
subst((1, 2),(1, 2),(0, 0, 0, 1)).
subst((1, 2),(1, 3),(0, 1, 0, 0)).
subst((1, 2),(1, 3),(0, 1, 0, 1)).
subst((1, 2),(0, 2),(1, 0, 0, 0)).
subst((1, 2),(0, 2),(1, 0, 0, 1)).
subst((1, 2),(0, 3),(1, 1, 0, 0)).
subst((1, 2),(0, 3),(1, 1, 0, 1)).
subst((1, 3),(1, 3),(0, 0, 0, 0)).
subst((1, 3),(1, 3),(0, 0, 0, 1)).
subst((1, 3),(1, 2),(0, 1, 0, 0)).
subst((1, 3),(1, 2),(0, 1, 0, 1)).
subst((1, 3),(0, 3),(1, 0, 0, 0)).
subst((1, 3),(0, 3),(1, 0, 0, 1)).
subst((1, 3),(0, 2),(1, 1, 0, 0)).
subst((1, 3),(0, 2),(1, 1, 0, 1)).
subst((5, 0),(5, 0),(0, 0, 0, 0)).
subst((5, 0),(6, 0),(0, 0, 0, 1)).
subst((5, 0),(5, 0),(0, 1, 0, 0)).
subst((5, 0),(6, 0),(0, 1, 0, 1)).
subst((5, 0),(5, 1),(1, 0, 0, 0)).
subst((5, 0),(6, 1),(1, 0, 0, 1)).
subst((5, 0),(5, 1),(1, 1, 0, 0)).
subst((5, 0),(6, 1),(1, 1, 0, 1)).
subst((5, 0, 0, 2),(5, 0, 0, 2),(0, 0, 0, 0)).
subst((5, 0, 0, 2),(6, 0, 0, 2),(0, 0, 0, 1)).
subst((5, 0, 0, 2),(5, 0, 0, 3),(0, 1, 0, 0)).
subst((5, 0, 0, 2),(6, 0, 0, 3),(0, 1, 0, 1)).
subst((5, 0, 0, 2),(5, 1, 1, 2),(1, 0, 0, 0)).
subst((5, 0, 0, 2),(6, 1, 1, 2),(1, 0, 0, 1)).
subst((5, 0, 0, 2),(5, 1, 1, 3),(1, 1, 0, 0)).
subst((5, 0, 0, 2),(6, 1, 1, 3),(1, 1, 0, 1)).
subst((5, 0, 0, 3),(5, 0, 0, 3),(0, 0, 0, 0)).
subst((5, 0, 0, 3),(6, 0, 0, 3),(0, 0, 0, 1)).
subst((5, 0, 0, 3),(5, 0, 0, 2),(0, 1, 0, 0)).
subst((5, 0, 0, 3),(6, 0, 0, 2),(0, 1, 0, 1)).
subst((5, 0, 0, 3),(5, 1, 1, 3),(1, 0, 0, 0)).
subst((5, 0, 0, 3),(6, 1, 1, 3),(1, 0, 0, 1)).
subst((5, 0, 0, 3),(5, 1, 1, 2),(1, 1, 0, 0)).
subst((5, 0, 0, 3),(6, 1, 1, 2),(1, 1, 0, 1)).
subst((5, 0, 1, 2),(5, 0, 1, 2),(0, 0, 0, 0)).
subst((5, 0, 1, 2),(6, 0, 1, 2),(0, 0, 0, 1)).
subst((5, 0, 1, 2),(5, 0, 1, 3),(0, 1, 0, 0)).
subst((5, 0, 1, 2),(6, 0, 1, 3),(0, 1, 0, 1)).
subst((5, 0, 1, 2),(5, 1, 0, 2),(1, 0, 0, 0)).
subst((5, 0, 1, 2),(6, 1, 0, 2),(1, 0, 0, 1)).
subst((5, 0, 1, 2),(5, 1, 0, 3),(1, 1, 0, 0)).
subst((5, 0, 1, 2),(6, 1, 0, 3),(1, 1, 0, 1)).
subst((5, 0, 1, 3),(5, 0, 1, 3),(0, 0, 0, 0)).
subst((5, 0, 1, 3),(6, 0, 1, 3),(0, 0, 0, 1)).
subst((5, 0, 1, 3),(5, 0, 1, 2),(0, 1, 0, 0)).
subst((5, 0, 1, 3),(6, 0, 1, 2),(0, 1, 0, 1)).
subst((5, 0, 1, 3),(5, 1, 0, 3),(1, 0, 0, 0)).
subst((5, 0, 1, 3),(6, 1, 0, 3),(1, 0, 0, 1)).
subst((5, 0, 1, 3),(5, 1, 0, 2),(1, 1, 0, 0)).
subst((5, 0, 1, 3),(6, 1, 0, 2),(1, 1, 0, 1)).
subst((5, 0, 2),(5, 0, 2),(0, 0, 0, 0)).
subst((5, 0, 2),(6, 0, 2),(0, 0, 0, 1)).
subst((5, 0, 2),(5, 0, 3),(0, 1, 0, 0)).
subst((5, 0, 2),(6, 0, 3),(0, 1, 0, 1)).
subst((5, 0, 2),(5, 1, 2),(1, 0, 0, 0)).
subst((5, 0, 2),(6, 1, 2),(1, 0, 0, 1)).
subst((5, 0, 2),(5, 1, 3),(1, 1, 0, 0)).
subst((5, 0, 2),(6, 1, 3),(1, 1, 0, 1)).
subst((5, 0, 3),(5, 0, 3),(0, 0, 0, 0)).
subst((5, 0, 3),(6, 0, 3),(0, 0, 0, 1)).
subst((5, 0, 3),(5, 0, 2),(0, 1, 0, 0)).
subst((5, 0, 3),(6, 0, 2),(0, 1, 0, 1)).
subst((5, 0, 3),(5, 1, 3),(1, 0, 0, 0)).
subst((5, 0, 3),(6, 1, 3),(1, 0, 0, 1)).
subst((5, 0, 3),(5, 1, 2),(1, 1, 0, 0)).
subst((5, 0, 3),(6, 1, 2),(1, 1, 0, 1)).
subst((5, 1),(5, 1),(0, 0, 0, 0)).
subst((5, 1),(6, 1),(0, 0, 0, 1)).
subst((5, 1),(5, 1),(0, 1, 0, 0)).
subst((5, 1),(6, 1),(0, 1, 0, 1)).
subst((5, 1),(5, 0),(1, 0, 0, 0)).
subst((5, 1),(6, 0),(1, 0, 0, 1)).
subst((5, 1),(5, 0),(1, 1, 0, 0)).
subst((5, 1),(6, 0),(1, 1, 0, 1)).
subst((5, 1, 0, 2),(5, 1, 0, 2),(0, 0, 0, 0)).
subst((5, 1, 0, 2),(6, 1, 0, 2),(0, 0, 0, 1)).
subst((5, 1, 0, 2),(5, 1, 0, 3),(0, 1, 0, 0)).
subst((5, 1, 0, 2),(6, 1, 0, 3),(0, 1, 0, 1)).
subst((5, 1, 0, 2),(5, 0, 1, 2),(1, 0, 0, 0)).
subst((5, 1, 0, 2),(6, 0, 1, 2),(1, 0, 0, 1)).
subst((5, 1, 0, 2),(5, 0, 1, 3),(1, 1, 0, 0)).
subst((5, 1, 0, 2),(6, 0, 1, 3),(1, 1, 0, 1)).
subst((5, 1, 0, 3),(5, 1, 0, 3),(0, 0, 0, 0)).
subst((5, 1, 0, 3),(6, 1, 0, 3),(0, 0, 0, 1)).
subst((5, 1, 0, 3),(5, 1, 0, 2),(0, 1, 0, 0)).
subst((5, 1, 0, 3),(6, 1, 0, 2),(0, 1, 0, 1)).
subst((5, 1, 0, 3),(5, 0, 1, 3),(1, 0, 0, 0)).
subst((5, 1, 0, 3),(6, 0, 1, 3),(1, 0, 0, 1)).
subst((5, 1, 0, 3),(5, 0, 1, 2),(1, 1, 0, 0)).
subst((5, 1, 0, 3),(6, 0, 1, 2),(1, 1, 0, 1)).
subst((5, 1, 1, 2),(5, 1, 1, 2),(0, 0, 0, 0)).
subst((5, 1, 1, 2),(6, 1, 1, 2),(0, 0, 0, 1)).
subst((5, 1, 1, 2),(5, 1, 1, 3),(0, 1, 0, 0)).
subst((5, 1, 1, 2),(6, 1, 1, 3),(0, 1, 0, 1)).
subst((5, 1, 1, 2),(5, 0, 0, 2),(1, 0, 0, 0)).
subst((5, 1, 1, 2),(6, 0, 0, 2),(1, 0, 0, 1)).
subst((5, 1, 1, 2),(5, 0, 0, 3),(1, 1, 0, 0)).
subst((5, 1, 1, 2),(6, 0, 0, 3),(1, 1, 0, 1)).
subst((5, 1, 1, 3),(5, 1, 1, 3),(0, 0, 0, 0)).
subst((5, 1, 1, 3),(6, 1, 1, 3),(0, 0, 0, 1)).
subst((5, 1, 1, 3),(5, 1, 1, 2),(0, 1, 0, 0)).
subst((5, 1, 1, 3),(6, 1, 1, 2),(0, 1, 0, 1)).
subst((5, 1, 1, 3),(5, 0, 0, 3),(1, 0, 0, 0)).
subst((5, 1, 1, 3),(6, 0, 0, 3),(1, 0, 0, 1)).
subst((5, 1, 1, 3),(5, 0, 0, 2),(1, 1, 0, 0)).
subst((5, 1, 1, 3),(6, 0, 0, 2),(1, 1, 0, 1)).
subst((5, 1, 2),(5, 1, 2),(0, 0, 0, 0)).
subst((5, 1, 2),(6, 1, 2),(0, 0, 0, 1)).
subst((5, 1, 2),(5, 1, 3),(0, 1, 0, 0)).
subst((5, 1, 2),(6, 1, 3),(0, 1, 0, 1)).
subst((5, 1, 2),(5, 0, 2),(1, 0, 0, 0)).
subst((5, 1, 2),(6, 0, 2),(1, 0, 0, 1)).
subst((5, 1, 2),(5, 0, 3),(1, 1, 0, 0)).
subst((5, 1, 2),(6, 0, 3),(1, 1, 0, 1)).
subst((5, 1, 3),(5, 1, 3),(0, 0, 0, 0)).
subst((5, 1, 3),(6, 1, 3),(0, 0, 0, 1)).
subst((5, 1, 3),(5, 1, 2),(0, 1, 0, 0)).
subst((5, 1, 3),(6, 1, 2),(0, 1, 0, 1)).
subst((5, 1, 3),(5, 0, 3),(1, 0, 0, 0)).
subst((5, 1, 3),(6, 0, 3),(1, 0, 0, 1)).
subst((5, 1, 3),(5, 0, 2),(1, 1, 0, 0)).
subst((5, 1, 3),(6, 0, 2),(1, 1, 0, 1)).
subst((5, 4),(5, 4),(0, 0, 0, 0)).
subst((5, 4),(6, 4),(0, 0, 0, 1)).
subst((5, 4),(5, 4),(0, 1, 0, 0)).
subst((5, 4),(6, 4),(0, 1, 0, 1)).
subst((5, 4),(5, 4),(1, 0, 0, 0)).
subst((5, 4),(6, 4),(1, 0, 0, 1)).
subst((5, 4),(5, 4),(1, 1, 0, 0)).
subst((5, 4),(6, 4),(1, 1, 0, 1)).
subst((6, 0),(6, 0),(0, 0, 0, 0)).
subst((6, 0),(5, 0),(0, 0, 0, 1)).
subst((6, 0),(6, 0),(0, 1, 0, 0)).
subst((6, 0),(5, 0),(0, 1, 0, 1)).
subst((6, 0),(6, 1),(1, 0, 0, 0)).
subst((6, 0),(5, 1),(1, 0, 0, 1)).
subst((6, 0),(6, 1),(1, 1, 0, 0)).
subst((6, 0),(5, 1),(1, 1, 0, 1)).
subst((6, 0, 0, 2),(6, 0, 0, 2),(0, 0, 0, 0)).
subst((6, 0, 0, 2),(5, 0, 0, 2),(0, 0, 0, 1)).
subst((6, 0, 0, 2),(6, 0, 0, 3),(0, 1, 0, 0)).
subst((6, 0, 0, 2),(5, 0, 0, 3),(0, 1, 0, 1)).
subst((6, 0, 0, 2),(6, 1, 1, 2),(1, 0, 0, 0)).
subst((6, 0, 0, 2),(5, 1, 1, 2),(1, 0, 0, 1)).
subst((6, 0, 0, 2),(6, 1, 1, 3),(1, 1, 0, 0)).
subst((6, 0, 0, 2),(5, 1, 1, 3),(1, 1, 0, 1)).
subst((6, 0, 0, 3),(6, 0, 0, 3),(0, 0, 0, 0)).
subst((6, 0, 0, 3),(5, 0, 0, 3),(0, 0, 0, 1)).
subst((6, 0, 0, 3),(6, 0, 0, 2),(0, 1, 0, 0)).
subst((6, 0, 0, 3),(5, 0, 0, 2),(0, 1, 0, 1)).
subst((6, 0, 0, 3),(6, 1, 1, 3),(1, 0, 0, 0)).
subst((6, 0, 0, 3),(5, 1, 1, 3),(1, 0, 0, 1)).
subst((6, 0, 0, 3),(6, 1, 1, 2),(1, 1, 0, 0)).
subst((6, 0, 0, 3),(5, 1, 1, 2),(1, 1, 0, 1)).
subst((6, 0, 1, 2),(6, 0, 1, 2),(0, 0, 0, 0)).
subst((6, 0, 1, 2),(5, 0, 1, 2),(0, 0, 0, 1)).
subst((6, 0, 1, 2),(6, 0, 1, 3),(0, 1, 0, 0)).
subst((6, 0, 1, 2),(5, 0, 1, 3),(0, 1, 0, 1)).
subst((6, 0, 1, 2),(6, 1, 0, 2),(1, 0, 0, 0)).
subst((6, 0, 1, 2),(5, 1, 0, 2),(1, 0, 0, 1)).
subst((6, 0, 1, 2),(6, 1, 0, 3),(1, 1, 0, 0)).
subst((6, 0, 1, 2),(5, 1, 0, 3),(1, 1, 0, 1)).
subst((6, 0, 1, 3),(6, 0, 1, 3),(0, 0, 0, 0)).
subst((6, 0, 1, 3),(5, 0, 1, 3),(0, 0, 0, 1)).
subst((6, 0, 1, 3),(6, 0, 1, 2),(0, 1, 0, 0)).
subst((6, 0, 1, 3),(5, 0, 1, 2),(0, 1, 0, 1)).
subst((6, 0, 1, 3),(6, 1, 0, 3),(1, 0, 0, 0)).
subst((6, 0, 1, 3),(5, 1, 0, 3),(1, 0, 0, 1)).
subst((6, 0, 1, 3),(6, 1, 0, 2),(1, 1, 0, 0)).
subst((6, 0, 1, 3),(5, 1, 0, 2),(1, 1, 0, 1)).
subst((6, 0, 2),(6, 0, 2),(0, 0, 0, 0)).
subst((6, 0, 2),(5, 0, 2),(0, 0, 0, 1)).
subst((6, 0, 2),(6, 0, 3),(0, 1, 0, 0)).
subst((6, 0, 2),(5, 0, 3),(0, 1, 0, 1)).
subst((6, 0, 2),(6, 1, 2),(1, 0, 0, 0)).
subst((6, 0, 2),(5, 1, 2),(1, 0, 0, 1)).
subst((6, 0, 2),(6, 1, 3),(1, 1, 0, 0)).
subst((6, 0, 2),(5, 1, 3),(1, 1, 0, 1)).
subst((6, 0, 3),(6, 0, 3),(0, 0, 0, 0)).
subst((6, 0, 3),(5, 0, 3),(0, 0, 0, 1)).
subst((6, 0, 3),(6, 0, 2),(0, 1, 0, 0)).
subst((6, 0, 3),(5, 0, 2),(0, 1, 0, 1)).
subst((6, 0, 3),(6, 1, 3),(1, 0, 0, 0)).
subst((6, 0, 3),(5, 1, 3),(1, 0, 0, 1)).
subst((6, 0, 3),(6, 1, 2),(1, 1, 0, 0)).
subst((6, 0, 3),(5, 1, 2),(1, 1, 0, 1)).
subst((6, 1),(6, 1),(0, 0, 0, 0)).
subst((6, 1),(5, 1),(0, 0, 0, 1)).
subst((6, 1),(6, 1),(0, 1, 0, 0)).
subst((6, 1),(5, 1),(0, 1, 0, 1)).
subst((6, 1),(6, 0),(1, 0, 0, 0)).
subst((6, 1),(5, 0),(1, 0, 0, 1)).
subst((6, 1),(6, 0),(1, 1, 0, 0)).
subst((6, 1),(5, 0),(1, 1, 0, 1)).
subst((6, 1, 0, 2),(6, 1, 0, 2),(0, 0, 0, 0)).
subst((6, 1, 0, 2),(5, 1, 0, 2),(0, 0, 0, 1)).
subst((6, 1, 0, 2),(6, 1, 0, 3),(0, 1, 0, 0)).
subst((6, 1, 0, 2),(5, 1, 0, 3),(0, 1, 0, 1)).
subst((6, 1, 0, 2),(6, 0, 1, 2),(1, 0, 0, 0)).
subst((6, 1, 0, 2),(5, 0, 1, 2),(1, 0, 0, 1)).
subst((6, 1, 0, 2),(6, 0, 1, 3),(1, 1, 0, 0)).
subst((6, 1, 0, 2),(5, 0, 1, 3),(1, 1, 0, 1)).
subst((6, 1, 0, 3),(6, 1, 0, 3),(0, 0, 0, 0)).
subst((6, 1, 0, 3),(5, 1, 0, 3),(0, 0, 0, 1)).
subst((6, 1, 0, 3),(6, 1, 0, 2),(0, 1, 0, 0)).
subst((6, 1, 0, 3),(5, 1, 0, 2),(0, 1, 0, 1)).
subst((6, 1, 0, 3),(6, 0, 1, 3),(1, 0, 0, 0)).
subst((6, 1, 0, 3),(5, 0, 1, 3),(1, 0, 0, 1)).
subst((6, 1, 0, 3),(6, 0, 1, 2),(1, 1, 0, 0)).
subst((6, 1, 0, 3),(5, 0, 1, 2),(1, 1, 0, 1)).
subst((6, 1, 1, 2),(6, 1, 1, 2),(0, 0, 0, 0)).
subst((6, 1, 1, 2),(5, 1, 1, 2),(0, 0, 0, 1)).
subst((6, 1, 1, 2),(6, 1, 1, 3),(0, 1, 0, 0)).
subst((6, 1, 1, 2),(5, 1, 1, 3),(0, 1, 0, 1)).
subst((6, 1, 1, 2),(6, 0, 0, 2),(1, 0, 0, 0)).
subst((6, 1, 1, 2),(5, 0, 0, 2),(1, 0, 0, 1)).
subst((6, 1, 1, 2),(6, 0, 0, 3),(1, 1, 0, 0)).
subst((6, 1, 1, 2),(5, 0, 0, 3),(1, 1, 0, 1)).
subst((6, 1, 1, 3),(6, 1, 1, 3),(0, 0, 0, 0)).
subst((6, 1, 1, 3),(5, 1, 1, 3),(0, 0, 0, 1)).
subst((6, 1, 1, 3),(6, 1, 1, 2),(0, 1, 0, 0)).
subst((6, 1, 1, 3),(5, 1, 1, 2),(0, 1, 0, 1)).
subst((6, 1, 1, 3),(6, 0, 0, 3),(1, 0, 0, 0)).
subst((6, 1, 1, 3),(5, 0, 0, 3),(1, 0, 0, 1)).
subst((6, 1, 1, 3),(6, 0, 0, 2),(1, 1, 0, 0)).
subst((6, 1, 1, 3),(5, 0, 0, 2),(1, 1, 0, 1)).
subst((6, 1, 2),(6, 1, 2),(0, 0, 0, 0)).
subst((6, 1, 2),(5, 1, 2),(0, 0, 0, 1)).
subst((6, 1, 2),(6, 1, 3),(0, 1, 0, 0)).
subst((6, 1, 2),(5, 1, 3),(0, 1, 0, 1)).
subst((6, 1, 2),(6, 0, 2),(1, 0, 0, 0)).
subst((6, 1, 2),(5, 0, 2),(1, 0, 0, 1)).
subst((6, 1, 2),(6, 0, 3),(1, 1, 0, 0)).
subst((6, 1, 2),(5, 0, 3),(1, 1, 0, 1)).
subst((6, 1, 3),(6, 1, 3),(0, 0, 0, 0)).
subst((6, 1, 3),(5, 1, 3),(0, 0, 0, 1)).
subst((6, 1, 3),(6, 1, 2),(0, 1, 0, 0)).
subst((6, 1, 3),(5, 1, 2),(0, 1, 0, 1)).
subst((6, 1, 3),(6, 0, 3),(1, 0, 0, 0)).
subst((6, 1, 3),(5, 0, 3),(1, 0, 0, 1)).
subst((6, 1, 3),(6, 0, 2),(1, 1, 0, 0)).
subst((6, 1, 3),(5, 0, 2),(1, 1, 0, 1)).
subst((6, 4),(6, 4),(0, 0, 0, 0)).
subst((6, 4),(5, 4),(0, 0, 0, 1)).
subst((6, 4),(6, 4),(0, 1, 0, 0)).
subst((6, 4),(5, 4),(0, 1, 0, 1)).
subst((6, 4),(6, 4),(1, 0, 0, 0)).
subst((6, 4),(5, 4),(1, 0, 0, 1)).
subst((6, 4),(6, 4),(1, 1, 0, 0)).
subst((6, 4),(5, 4),(1, 1, 0, 1)).
pred_vars_no(0,member, (5, 4)).
pred_vars_no(1,member, (6, 4)).
pred_vars_no(2,one_a, (0,)).
pred_vars_no(3,one_a, (1,)).
pred_vars_no(4,one_b, (5, 0)).
pred_vars_no(5,one_b, (5, 1)).
pred_vars_no(6,one_b, (6, 0)).
pred_vars_no(7,one_b, (6, 1)).
pred_vars_no(8,left_rnd, (5, 0)).
pred_vars_no(9,left_rnd, (5, 1)).
pred_vars_no(10,left_rnd, (6, 0)).
pred_vars_no(11,left_rnd, (6, 1)).
pred_vars_no(12,proposal, (0, 2)).
pred_vars_no(13,proposal, (0, 3)).
pred_vars_no(14,proposal, (1, 2)).
pred_vars_no(15,proposal, (1, 3)).
pred_vars_no(16,vote, (5, 0, 2)).
pred_vars_no(17,vote, (5, 0, 3)).
pred_vars_no(18,vote, (5, 1, 2)).
pred_vars_no(19,vote, (5, 1, 3)).
pred_vars_no(20,vote, (6, 0, 2)).
pred_vars_no(21,vote, (6, 0, 3)).
pred_vars_no(22,vote, (6, 1, 2)).
pred_vars_no(23,vote, (6, 1, 3)).
pred_vars_no(24,decision, (5, 0, 2)).
pred_vars_no(25,decision, (5, 0, 3)).
pred_vars_no(26,decision, (5, 1, 2)).
pred_vars_no(27,decision, (5, 1, 3)).
pred_vars_no(28,decision, (6, 0, 2)).
pred_vars_no(29,decision, (6, 0, 3)).
pred_vars_no(30,decision, (6, 1, 2)).
pred_vars_no(31,decision, (6, 1, 3)).
individual(none).
pred_vars_no(32,none, (0,)).
individual(none).
pred_vars_no(33,none, (1,)).

rule(0,5).
rule(0,24).
rule_used(0,0).
rule_used(0,2).
rule_varnum(0,2).
rule_len(0,2).
forall_rule(0).

rule(1,48).
rule(1,64).
rule_used(1,0).
rule_used(1,2).
rule_used(1,5).
rule_varnum(1,3).
rule_len(1,2).
forall_rule(1).

rule(2,24).
rule(2,64).
rule_used(2,0).
rule_used(2,2).
rule_varnum(2,2).
rule_len(2,2).
forall_rule(2).

rule(3,25).
rule(3,32).
rule_used(3,0).
rule_used(3,2).
rule_used(3,5).
rule_varnum(3,3).
rule_len(3,2).
forall_rule(3).

rule(4,32).
rule(4,64).
rule_used(4,0).
rule_used(4,2).
rule_used(4,5).
rule_varnum(4,3).
rule_len(4,2).
forall_rule(4).

rule(5,5).
rule(5,32).
rule_used(5,0).
rule_used(5,2).
rule_used(5,5).
rule_varnum(5,3).
rule_len(5,2).
forall_rule(5).

rule(6,8).
rule(6,64).
rule_used(6,0).
rule_used(6,5).
rule_varnum(6,2).
rule_len(6,2).
forall_rule(6).

rule(7,4).
rule(7,64).
rule_used(7,0).
rule_varnum(7,1).
rule_len(7,2).
forall_rule(7).

rule(8,25).
rule(8,48).
rule_used(8,0).
rule_used(8,2).
rule_used(8,5).
rule_varnum(8,3).
rule_len(8,2).
forall_rule(8).

rule(9,5).
rule(9,48).
rule_used(9,0).
rule_used(9,2).
rule_used(9,5).
rule_varnum(9,3).
rule_len(9,2).
forall_rule(9).

rule(10,5).
rule(10,8).
rule_used(10,0).
rule_used(10,5).
rule_varnum(10,2).
rule_len(10,2).
forall_rule(10).

rule(11,26).
rule(11,48).
rule_used(11,0).
rule_used(11,2).
rule_used(11,3).
rule_used(11,5).
rule_varnum(11,4).
rule_len(11,2).
forall_rule(11).

rule(12,24).
rule(12,26).
rule_used(12,0).
rule_used(12,2).
rule_used(12,3).
rule_varnum(12,3).
rule_len(12,2).
forall_rule(12).

rule(13,48).
rule(13,50).
rule_used(13,0).
rule_used(13,2).
rule_used(13,3).
rule_used(13,5).
rule_varnum(13,4).
rule_len(13,2).
forall_rule(13).

rule(14,24).
rule(14,34).
rule_used(14,0).
rule_used(14,2).
rule_used(14,3).
rule_used(14,5).
rule_varnum(14,4).
rule_len(14,2).
forall_rule(14).

rule(15,34).
rule(15,48).
rule_used(15,0).
rule_used(15,2).
rule_used(15,3).
rule_used(15,5).
rule_varnum(15,4).
rule_len(15,2).
forall_rule(15).

rule(16,32).
rule(16,34).
rule_used(16,0).
rule_used(16,2).
rule_used(16,3).
rule_used(16,5).
rule_varnum(16,4).
rule_len(16,2).
forall_rule(16).

rule(17,48).
rule(17,58).
rule_used(17,0).
rule_used(17,2).
rule_used(17,3).
rule_used(17,5).
rule_used(17,6).
rule_varnum(17,5).
rule_len(17,2).
forall_rule(17).

rule(18,42).
rule(18,48).
rule_used(18,0).
rule_used(18,2).
rule_used(18,3).
rule_used(18,5).
rule_used(18,6).
rule_varnum(18,5).
rule_len(18,2).
forall_rule(18).

rule(19,32).
rule(19,42).
rule_used(19,0).
rule_used(19,2).
rule_used(19,3).
rule_used(19,5).
rule_used(19,6).
rule_varnum(19,5).
rule_len(19,2).
forall_rule(19).

rule(20,17).
rule(20,18).
rule_used(20,0).
rule_used(20,1).
rule_used(20,5).
rule_varnum(20,3).
rule_len(20,2).
forall_rule(20).

rule(21,10).
rule(21,17).
rule_used(21,0).
rule_used(21,1).
rule_used(21,5).
rule_varnum(21,3).
rule_len(21,2).
forall_rule(21).

rule(22,38).
rule(22,48).
rule_used(22,0).
rule_used(22,1).
rule_used(22,2).
rule_used(22,3).
rule_used(22,5).
rule_varnum(22,5).
rule_len(22,2).
forall_rule(22).

rule(23,48).
rule(23,54).
rule_used(23,0).
rule_used(23,1).
rule_used(23,2).
rule_used(23,3).
rule_used(23,5).
rule_varnum(23,5).
rule_len(23,2).
forall_rule(23).

rule(24,30).
rule(24,48).
rule_used(24,0).
rule_used(24,1).
rule_used(24,2).
rule_used(24,3).
rule_used(24,5).
rule_varnum(24,5).
rule_len(24,2).
forall_rule(24).

rule(25,48).
rule(25,62).
rule_used(25,0).
rule_used(25,1).
rule_used(25,2).
rule_used(25,3).
rule_used(25,5).
rule_used(25,6).
rule_varnum(25,6).
rule_len(25,2).
forall_rule(25).

rule(26,52).
rule(26,58).
rule_used(26,0).
rule_used(26,1).
rule_used(26,2).
rule_used(26,3).
rule_used(26,5).
rule_used(26,6).
rule_varnum(26,6).
rule_len(26,2).
forall_rule(26).

rule(27,46).
rule(27,48).
rule_used(27,0).
rule_used(27,1).
rule_used(27,2).
rule_used(27,3).
rule_used(27,5).
rule_used(27,6).
rule_varnum(27,6).
rule_len(27,2).
forall_rule(27).

rule(28,18).
rule(28,32).
rule(28,67).
rule_used(28,0).
rule_used(28,1).
rule_used(28,2).
rule_used(28,5).
rule_varnum(28,4).
rule_len(28,3).
forall_rule(28).

rule(29,10).
rule(29,18).
rule(29,32).
rule_used(29,0).
rule_used(29,1).
rule_used(29,2).
rule_used(29,5).
rule_varnum(29,4).
rule_len(29,3).
forall_rule(29).

rule(30,6).
rule(30,18).
rule(30,32).
rule_used(30,0).
rule_used(30,1).
rule_used(30,2).
rule_used(30,5).
rule_varnum(30,4).
rule_len(30,3).
forall_rule(30).

rule(31,18).
rule(31,28).
rule(31,32).
rule_used(31,0).
rule_used(31,1).
rule_used(31,2).
rule_used(31,5).
rule_varnum(31,4).
rule_len(31,3).
forall_rule(31).

rule(32,18).
rule(32,32).
rule(32,52).
rule_used(32,0).
rule_used(32,1).
rule_used(32,2).
rule_used(32,5).
rule_varnum(32,4).
rule_len(32,3).
forall_rule(32).

rule(33,18).
rule(33,32).
rule(33,36).
rule_used(33,0).
rule_used(33,1).
rule_used(33,2).
rule_used(33,5).
rule_varnum(33,4).
rule_len(33,3).
forall_rule(33).

rule(34,8).
rule(34,18).
rule(34,28).
rule_used(34,0).
rule_used(34,1).
rule_used(34,2).
rule_used(34,5).
rule_varnum(34,4).
rule_len(34,3).
forall_rule(34).

rule(35,8).
rule(35,18).
rule(35,52).
rule_used(35,0).
rule_used(35,1).
rule_used(35,2).
rule_used(35,5).
rule_varnum(35,4).
rule_len(35,3).
forall_rule(35).

rule(36,18).
rule(36,48).
rule(36,67).
rule_used(36,0).
rule_used(36,1).
rule_used(36,2).
rule_used(36,5).
rule_varnum(36,4).
rule_len(36,3).
forall_rule(36).

rule(37,18).
rule(37,28).
rule(37,48).
rule_used(37,0).
rule_used(37,1).
rule_used(37,2).
rule_used(37,5).
rule_varnum(37,4).
rule_len(37,3).
forall_rule(37).

rule(38,8).
rule(38,18).
rule(38,36).
rule_used(38,0).
rule_used(38,1).
rule_used(38,2).
rule_used(38,5).
rule_varnum(38,4).
rule_len(38,3).
forall_rule(38).

rule(39,18).
rule(39,48).
rule(39,52).
rule_used(39,0).
rule_used(39,1).
rule_used(39,2).
rule_used(39,5).
rule_varnum(39,4).
rule_len(39,3).
forall_rule(39).

rule(40,8).
rule(40,10).
rule(40,18).
rule_used(40,0).
rule_used(40,1).
rule_used(40,5).
rule_varnum(40,3).
rule_len(40,3).
forall_rule(40).

rule(41,6).
rule(41,18).
rule(41,48).
rule_used(41,0).
rule_used(41,1).
rule_used(41,2).
rule_used(41,5).
rule_varnum(41,4).
rule_len(41,3).
forall_rule(41).

rule(42,8).
rule(42,18).
rule(42,67).
rule_used(42,0).
rule_used(42,1).
rule_used(42,5).
rule_varnum(42,3).
rule_len(42,3).
forall_rule(42).

rule(43,4).
rule(43,18).
rule(43,36).
rule_used(43,0).
rule_used(43,1).
rule_used(43,2).
rule_used(43,5).
rule_varnum(43,4).
rule_len(43,3).
forall_rule(43).

rule(44,4).
rule(44,18).
rule(44,52).
rule_used(44,0).
rule_used(44,1).
rule_used(44,2).
rule_used(44,5).
rule_varnum(44,4).
rule_len(44,3).
forall_rule(44).

rule(45,6).
rule(45,8).
rule(45,18).
rule_used(45,0).
rule_used(45,1).
rule_used(45,5).
rule_varnum(45,3).
rule_len(45,3).
forall_rule(45).

rule(46,18).
rule(46,36).
rule(46,48).
rule_used(46,0).
rule_used(46,1).
rule_used(46,2).
rule_used(46,5).
rule_varnum(46,4).
rule_len(46,3).
forall_rule(46).

rule(47,4).
rule(47,10).
rule(47,18).
rule_used(47,0).
rule_used(47,1).
rule_used(47,5).
rule_varnum(47,3).
rule_len(47,3).
forall_rule(47).

rule(48,4).
rule(48,18).
rule(48,67).
rule_used(48,0).
rule_used(48,1).
rule_used(48,5).
rule_varnum(48,3).
rule_len(48,3).
forall_rule(48).

rule(49,10).
rule(49,18).
rule(49,48).
rule_used(49,0).
rule_used(49,1).
rule_used(49,2).
rule_used(49,5).
rule_varnum(49,4).
rule_len(49,3).
forall_rule(49).

rule(50,4).
rule(50,6).
rule(50,18).
rule_used(50,0).
rule_used(50,1).
rule_used(50,5).
rule_varnum(50,3).
rule_len(50,3).
forall_rule(50).

rule(51,4).
rule(51,18).
rule(51,28).
rule_used(51,0).
rule_used(51,1).
rule_used(51,2).
rule_used(51,5).
rule_varnum(51,4).
rule_len(51,3).
forall_rule(51).

rule(52,18).
rule(52,24).
rule(52,52).
rule_used(52,0).
rule_used(52,1).
rule_used(52,2).
rule_used(52,5).
rule_varnum(52,4).
rule_len(52,3).
forall_rule(52).

rule(53,6).
rule(53,18).
rule(53,24).
rule_used(53,0).
rule_used(53,1).
rule_used(53,2).
rule_used(53,5).
rule_varnum(53,4).
rule_len(53,3).
forall_rule(53).

rule(54,18).
rule(54,24).
rule(54,28).
rule_used(54,0).
rule_used(54,1).
rule_used(54,2).
rule_used(54,5).
rule_varnum(54,4).
rule_len(54,3).
forall_rule(54).

rule(55,18).
rule(55,24).
rule(55,67).
rule_used(55,0).
rule_used(55,1).
rule_used(55,2).
rule_used(55,5).
rule_varnum(55,4).
rule_len(55,3).
forall_rule(55).

rule(56,18).
rule(56,24).
rule(56,36).
rule_used(56,0).
rule_used(56,1).
rule_used(56,2).
rule_used(56,5).
rule_varnum(56,4).
rule_len(56,3).
forall_rule(56).

rule(57,10).
rule(57,18).
rule(57,24).
rule_used(57,0).
rule_used(57,1).
rule_used(57,2).
rule_used(57,5).
rule_varnum(57,4).
rule_len(57,3).
forall_rule(57).

rule(58,22).
rule(58,44).
rule(58,48).
rule_used(58,0).
rule_used(58,1).
rule_used(58,2).
rule_used(58,5).
rule_used(58,6).
rule_varnum(58,5).
rule_len(58,3).
forall_rule(58).

rule(59,22).
rule(59,28).
rule(59,48).
rule_used(59,0).
rule_used(59,1).
rule_used(59,2).
rule_used(59,5).
rule_used(59,6).
rule_varnum(59,5).
rule_len(59,3).
forall_rule(59).

rule(60,14).
rule(60,22).
rule(60,48).
rule_used(60,0).
rule_used(60,1).
rule_used(60,2).
rule_used(60,5).
rule_used(60,6).
rule_varnum(60,5).
rule_len(60,3).
forall_rule(60).

rule(61,4).
rule(61,18).
rule(61,44).
rule_used(61,0).
rule_used(61,1).
rule_used(61,2).
rule_used(61,5).
rule_used(61,6).
rule_varnum(61,5).
rule_len(61,3).
forall_rule(61).

rule(62,22).
rule(62,48).
rule(62,67).
rule_used(62,0).
rule_used(62,1).
rule_used(62,2).
rule_used(62,5).
rule_used(62,6).
rule_varnum(62,5).
rule_len(62,3).
forall_rule(62).

rule(63,18).
rule(63,44).
rule(63,48).
rule_used(63,0).
rule_used(63,1).
rule_used(63,2).
rule_used(63,5).
rule_used(63,6).
rule_varnum(63,5).
rule_len(63,3).
forall_rule(63).

rule(64,12).
rule(64,22).
rule(64,52).
rule_used(64,0).
rule_used(64,1).
rule_used(64,2).
rule_used(64,5).
rule_used(64,6).
rule_varnum(64,5).
rule_len(64,3).
forall_rule(64).

rule(65,18).
rule(65,24).
rule(65,44).
rule_used(65,0).
rule_used(65,1).
rule_used(65,2).
rule_used(65,5).
rule_used(65,6).
rule_varnum(65,5).
rule_len(65,3).
forall_rule(65).

rule(66,22).
rule(66,40).
rule(66,52).
rule_used(66,0).
rule_used(66,1).
rule_used(66,2).
rule_used(66,5).
rule_used(66,6).
rule_varnum(66,5).
rule_len(66,3).
forall_rule(66).

rule(67,18).
rule(67,32).
rule(67,44).
rule_used(67,0).
rule_used(67,1).
rule_used(67,2).
rule_used(67,5).
rule_used(67,6).
rule_varnum(67,5).
rule_len(67,3).
forall_rule(67).

rule(68,4).
rule(68,22).
rule(68,52).
rule_used(68,0).
rule_used(68,1).
rule_used(68,2).
rule_used(68,5).
rule_used(68,6).
rule_varnum(68,5).
rule_len(68,3).
forall_rule(68).

rule(69,8).
rule(69,18).
rule(69,44).
rule_used(69,0).
rule_used(69,1).
rule_used(69,2).
rule_used(69,5).
rule_used(69,6).
rule_varnum(69,5).
rule_len(69,3).
forall_rule(69).

rule(70,8).
rule(70,14).
rule(70,18).
rule_used(70,0).
rule_used(70,1).
rule_used(70,5).
rule_used(70,6).
rule_varnum(70,4).
rule_len(70,3).
forall_rule(70).

rule(71,22).
rule(71,48).
rule(71,52).
rule_used(71,0).
rule_used(71,1).
rule_used(71,2).
rule_used(71,5).
rule_used(71,6).
rule_varnum(71,5).
rule_len(71,3).
forall_rule(71).

rule(72,18).
rule(72,40).
rule(72,44).
rule_used(72,0).
rule_used(72,1).
rule_used(72,2).
rule_used(72,5).
rule_used(72,6).
rule_varnum(72,5).
rule_len(72,3).
forall_rule(72).

rule(73,8).
rule(73,22).
rule(73,52).
rule_used(73,0).
rule_used(73,1).
rule_used(73,2).
rule_used(73,5).
rule_used(73,6).
rule_varnum(73,5).
rule_len(73,3).
forall_rule(73).

rule(74,12).
rule(74,18).
rule(74,44).
rule_used(74,0).
rule_used(74,1).
rule_used(74,2).
rule_used(74,5).
rule_used(74,6).
rule_varnum(74,5).
rule_len(74,3).
forall_rule(74).

rule(75,14).
rule(75,18).
rule(75,48).
rule_used(75,0).
rule_used(75,1).
rule_used(75,2).
rule_used(75,5).
rule_used(75,6).
rule_varnum(75,5).
rule_len(75,3).
forall_rule(75).

rule(76,22).
rule(76,32).
rule(76,52).
rule_used(76,0).
rule_used(76,1).
rule_used(76,2).
rule_used(76,5).
rule_used(76,6).
rule_varnum(76,5).
rule_len(76,3).
forall_rule(76).

rule(77,4).
rule(77,14).
rule(77,18).
rule_used(77,0).
rule_used(77,1).
rule_used(77,5).
rule_used(77,6).
rule_varnum(77,4).
rule_len(77,3).
forall_rule(77).

rule(78,22).
rule(78,24).
rule(78,52).
rule_used(78,0).
rule_used(78,1).
rule_used(78,2).
rule_used(78,5).
rule_used(78,6).
rule_varnum(78,5).
rule_len(78,3).
forall_rule(78).

rule(79,6).
rule(79,12).
rule(79,18).
rule_used(79,0).
rule_used(79,1).
rule_used(79,5).
rule_used(79,6).
rule_varnum(79,4).
rule_len(79,3).
forall_rule(79).

rule(80,14).
rule(80,18).
rule(80,40).
rule_used(80,0).
rule_used(80,1).
rule_used(80,2).
rule_used(80,5).
rule_used(80,6).
rule_varnum(80,5).
rule_len(80,3).
forall_rule(80).

rule(81,10).
rule(81,22).
rule(81,48).
rule_used(81,0).
rule_used(81,1).
rule_used(81,2).
rule_used(81,5).
rule_used(81,6).
rule_varnum(81,5).
rule_len(81,3).
forall_rule(81).

rule(82,6).
rule(82,18).
rule(82,40).
rule_used(82,0).
rule_used(82,1).
rule_used(82,2).
rule_used(82,5).
rule_used(82,6).
rule_varnum(82,5).
rule_len(82,3).
forall_rule(82).

rule(83,18).
rule(83,40).
rule(83,52).
rule_used(83,0).
rule_used(83,1).
rule_used(83,2).
rule_used(83,5).
rule_used(83,6).
rule_varnum(83,5).
rule_len(83,3).
forall_rule(83).

rule(84,22).
rule(84,36).
rule(84,48).
rule_used(84,0).
rule_used(84,1).
rule_used(84,2).
rule_used(84,5).
rule_used(84,6).
rule_varnum(84,5).
rule_len(84,3).
forall_rule(84).

rule(85,18).
rule(85,28).
rule(85,40).
rule_used(85,0).
rule_used(85,1).
rule_used(85,2).
rule_used(85,5).
rule_used(85,6).
rule_varnum(85,5).
rule_len(85,3).
forall_rule(85).

rule(86,6).
rule(86,22).
rule(86,48).
rule_used(86,0).
rule_used(86,1).
rule_used(86,2).
rule_used(86,5).
rule_used(86,6).
rule_varnum(86,5).
rule_len(86,3).
forall_rule(86).

rule(87,18).
rule(87,36).
rule(87,40).
rule_used(87,0).
rule_used(87,1).
rule_used(87,2).
rule_used(87,5).
rule_used(87,6).
rule_varnum(87,5).
rule_len(87,3).
forall_rule(87).

rule(88,10).
rule(88,18).
rule(88,40).
rule_used(88,0).
rule_used(88,1).
rule_used(88,2).
rule_used(88,5).
rule_used(88,6).
rule_varnum(88,5).
rule_len(88,3).
forall_rule(88).

rule(89,12).
rule(89,14).
rule(89,18).
rule_used(89,0).
rule_used(89,1).
rule_used(89,5).
rule_used(89,6).
rule_varnum(89,4).
rule_len(89,3).
forall_rule(89).

rule(90,18).
rule(90,40).
rule(90,67).
rule_used(90,0).
rule_used(90,1).
rule_used(90,2).
rule_used(90,5).
rule_used(90,6).
rule_varnum(90,5).
rule_len(90,3).
forall_rule(90).

rule(91,10).
rule(91,12).
rule(91,18).
rule_used(91,0).
rule_used(91,1).
rule_used(91,5).
rule_used(91,6).
rule_varnum(91,4).
rule_len(91,3).
forall_rule(91).

rule(92,14).
rule(92,18).
rule(92,32).
rule_used(92,0).
rule_used(92,1).
rule_used(92,2).
rule_used(92,5).
rule_used(92,6).
rule_varnum(92,5).
rule_len(92,3).
forall_rule(92).

rule(93,12).
rule(93,18).
rule(93,28).
rule_used(93,0).
rule_used(93,1).
rule_used(93,2).
rule_used(93,5).
rule_used(93,6).
rule_varnum(93,5).
rule_len(93,3).
forall_rule(93).

rule(94,12).
rule(94,18).
rule(94,52).
rule_used(94,0).
rule_used(94,1).
rule_used(94,2).
rule_used(94,5).
rule_used(94,6).
rule_varnum(94,5).
rule_len(94,3).
forall_rule(94).

rule(95,14).
rule(95,18).
rule(95,24).
rule_used(95,0).
rule_used(95,1).
rule_used(95,2).
rule_used(95,5).
rule_used(95,6).
rule_varnum(95,5).
rule_len(95,3).
forall_rule(95).

rule(96,12).
rule(96,18).
rule(96,36).
rule_used(96,0).
rule_used(96,1).
rule_used(96,2).
rule_used(96,5).
rule_used(96,6).
rule_varnum(96,5).
rule_len(96,3).
forall_rule(96).

rule(97,12).
rule(97,18).
rule(97,67).
rule_used(97,0).
rule_used(97,1).
rule_used(97,5).
rule_used(97,6).
rule_varnum(97,4).
rule_len(97,3).
forall_rule(97).

rule(98,18).
rule(98,24).
rule(98,38).
rule_used(98,0).
rule_used(98,1).
rule_used(98,2).
rule_used(98,3).
rule_used(98,5).
rule_varnum(98,5).
rule_len(98,3).
forall_rule(98).

rule(99,18).
rule(99,28).
rule(99,34).
rule_used(99,0).
rule_used(99,1).
rule_used(99,2).
rule_used(99,3).
rule_used(99,5).
rule_varnum(99,5).
rule_len(99,3).
forall_rule(99).

rule(100,18).
rule(100,28).
rule(100,42).
rule_used(100,0).
rule_used(100,1).
rule_used(100,2).
rule_used(100,3).
rule_used(100,5).
rule_used(100,6).
rule_varnum(100,6).
rule_len(100,3).
forall_rule(100).

rule(101,18).
rule(101,24).
rule(101,46).
rule_used(101,0).
rule_used(101,1).
rule_used(101,2).
rule_used(101,3).
rule_used(101,5).
rule_used(101,6).
rule_varnum(101,6).
rule_len(101,3).
forall_rule(101).

rule(102,1).
rule_used(102,4).
rule_used(102,5).
rule_varnum(102,2).
rule_exists(102,5).
rule_len(102,1).

rule(103,48).
rule_used(103,0).
rule_used(103,2).
rule_used(103,5).
rule_varnum(103,3).
rule_exists(103,0).
rule_len(103,1).

rule(104,8).
rule_used(104,0).
rule_used(104,5).
rule_varnum(104,2).
rule_exists(104,0).
rule_len(104,1).

rule(105,24).
rule_used(105,0).
rule_used(105,2).
rule_varnum(105,2).
rule_exists(105,0).
rule_len(105,1).

rule(106,16).
rule_used(106,0).
rule_used(106,5).
rule_varnum(106,2).
rule_exists(106,0).
rule_len(106,1).

rule(107,65).
rule_used(107,0).
rule_varnum(107,1).
rule_exists(107,0).
rule_len(107,1).

rule(108,32).
rule_used(108,0).
rule_used(108,2).
rule_used(108,5).
rule_varnum(108,3).
rule_exists(108,0).
rule_len(108,1).

rule(109,4).
rule_used(109,0).
rule_varnum(109,1).
rule_exists(109,0).
rule_len(109,1).

rule(110,33).
rule(110,48).
rule_used(110,0).
rule_used(110,2).
rule_used(110,5).
rule_varnum(110,3).
rule_len(110,2).
rule_exists(110,5).

rule(111,9).
rule(111,32).
rule_used(111,0).
rule_used(111,2).
rule_used(111,5).
rule_varnum(111,3).
rule_len(111,2).
rule_exists(111,5).

rule(112,9).
rule(112,24).
rule_used(112,0).
rule_used(112,2).
rule_used(112,5).
rule_varnum(112,3).
rule_len(112,2).
rule_exists(112,5).

rule(113,9).
rule(113,48).
rule_used(113,0).
rule_used(113,2).
rule_used(113,5).
rule_varnum(113,3).
rule_len(113,2).
rule_exists(113,5).

rule(114,17).
rule(114,28).
rule_used(114,0).
rule_used(114,1).
rule_used(114,2).
rule_used(114,5).
rule_varnum(114,4).
rule_len(114,2).
rule_exists(114,5).

rule(115,17).
rule(115,36).
rule_used(115,0).
rule_used(115,1).
rule_used(115,2).
rule_used(115,5).
rule_varnum(115,4).
rule_len(115,2).
rule_exists(115,5).

rule(116,17).
rule(116,52).
rule_used(116,0).
rule_used(116,1).
rule_used(116,2).
rule_used(116,5).
rule_varnum(116,4).
rule_len(116,2).
rule_exists(116,5).

rule(117,28).
rule(117,34).
rule_used(117,0).
rule_used(117,1).
rule_used(117,2).
rule_used(117,3).
rule_used(117,5).
rule_varnum(117,5).
rule_len(117,2).
rule_exists(117,5).

rule(118,32).
rule(118,38).
rule_used(118,0).
rule_used(118,1).
rule_used(118,2).
rule_used(118,3).
rule_used(118,5).
rule_varnum(118,5).
rule_len(118,2).
rule_exists(118,5).

rule(119,0).
rule(119,9).
rule(119,48).
rule_used(119,0).
rule_used(119,2).
rule_used(119,4).
rule_used(119,5).
rule_varnum(119,4).
rule_len(119,3).
rule_exists(119,4).

rule(120,0).
rule(120,33).
rule(120,48).
rule_used(120,0).
rule_used(120,2).
rule_used(120,4).
rule_used(120,5).
rule_varnum(120,4).
rule_len(120,3).
rule_exists(120,4).

rule(121,0).
rule(121,9).
rule(121,32).
rule_used(121,0).
rule_used(121,2).
rule_used(121,4).
rule_used(121,5).
rule_varnum(121,4).
rule_len(121,3).
rule_exists(121,4).

rule(122,0).
rule(122,9).
rule(122,24).
rule_used(122,0).
rule_used(122,2).
rule_used(122,4).
rule_used(122,5).
rule_varnum(122,4).
rule_len(122,3).
rule_exists(122,4).

rule(123,2).
rule(123,41).
rule(123,48).
rule_used(123,0).
rule_used(123,2).
rule_used(123,4).
rule_used(123,5).
rule_used(123,6).
rule_varnum(123,5).
rule_len(123,3).
rule_exists(123,4).

rule(124,2).
rule(124,13).
rule(124,48).
rule_used(124,0).
rule_used(124,2).
rule_used(124,4).
rule_used(124,5).
rule_used(124,6).
rule_varnum(124,5).
rule_len(124,3).
rule_exists(124,4).

rule(125,0).
rule(125,9).
rule(125,40).
rule_used(125,0).
rule_used(125,2).
rule_used(125,4).
rule_used(125,5).
rule_used(125,6).
rule_varnum(125,5).
rule_len(125,3).
rule_exists(125,4).

rule(126,0).
rule(126,17).
rule(126,28).
rule_used(126,0).
rule_used(126,1).
rule_used(126,2).
rule_used(126,4).
rule_used(126,5).
rule_varnum(126,5).
rule_len(126,3).
rule_exists(126,4).

rule(127,0).
rule(127,17).
rule(127,36).
rule_used(127,0).
rule_used(127,1).
rule_used(127,2).
rule_used(127,4).
rule_used(127,5).
rule_varnum(127,5).
rule_len(127,3).
rule_exists(127,4).

rule(128,0).
rule(128,17).
rule(128,52).
rule_used(128,0).
rule_used(128,1).
rule_used(128,2).
rule_used(128,4).
rule_used(128,5).
rule_varnum(128,5).
rule_len(128,3).
rule_exists(128,4).

rule(129,0).
rule(129,17).
rule(129,44).
rule_used(129,0).
rule_used(129,1).
rule_used(129,2).
rule_used(129,4).
rule_used(129,5).
rule_used(129,6).
rule_varnum(129,6).
rule_len(129,3).
rule_exists(129,4).

rule(130,2).
rule(130,21).
rule(130,52).
rule_used(130,0).
rule_used(130,1).
rule_used(130,2).
rule_used(130,4).
rule_used(130,5).
rule_used(130,6).
rule_varnum(130,6).
rule_len(130,3).
rule_exists(130,4).

rule(131,0).
rule(131,28).
rule(131,34).
rule_used(131,0).
rule_used(131,1).
rule_used(131,2).
rule_used(131,3).
rule_used(131,4).
rule_used(131,5).
rule_varnum(131,6).
rule_len(131,3).
rule_exists(131,4).