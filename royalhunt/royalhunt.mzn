int: n; % number of court members
set of int: COURT = 1..n;
int: emperor = 1;
array[COURT] of int: rank;
array[COURT] of int: ability;

int: m; % number of horses
set of int: HORSE = 1..m;
array[HORSE] of int: beauty;
array[HORSE] of int: speed;

array[COURT,HORSE] of int: enjoy;



int: x = if n < m then n else m endif;
set of int: X = 1..x;

array[X] of var HORSE: h;
array[X] of var COURT: c;

array[X] of var X: horses;
array[X] of var X: riders;

constraint c[1] = emperor;

include "alldifferent.mzn";
constraint alldifferent(h);
constraint alldifferent(c);
constraint alldifferent(horses);
constraint alldifferent(riders);

% channeling of the two models
include "inverse.mzn";
constraint inverse(horses, riders);

% the emperor must enjoy more than anyone else
var int: max_enjoy;
constraint max_enjoy = enjoy[c[1], h[horses[1]]];
constraint forall(i in X)(
  (i != 1) -> (enjoy[c[i], h[horses[i]]] < max_enjoy)
);

% if court member A has higher rank than B, then either
% (a) the beauty of horse of A can be no less than of B
% (b) B does not ride
% (c) both A and B do not ride
constraint forall(i, j in X)(
  (rank[c[i]] > rank[c[j]]) -> (beauty[h[horses[i]]] >= beauty[h[horses[j]]])
);

% if a horse A is faster than another horse B, then either
% (a) rider of A has no less ability than rider of B
% (b) A has no rider
% (c) both A and B has no rider
var int: penalty;
constraint penalty = sum(i, j in X)(
  if ( (speed[h[i]] > speed[h[j]]) -> (ability[c[riders[i]]] >= ability[c[riders[j]]]) ) then 0 else 100 endif
);

% cannot assign if entry in enjoy is negative
constraint forall(i in X)(
  enjoy[c[i], h[horses[i]]] >= 0
);

% maximize total enjoyment of all riders
var int: obj;
constraint obj = sum(i in X)(
  enjoy[c[i], h[horses[i]]]
) - penalty;
solve maximize obj;

array[COURT] of var 0..m: horses_full;
constraint forall(i in X)(
  horses_full[c[i]] = h[horses[i]]
);
constraint forall(i in COURT where (not exists(j in X)(c[j] = i)))(
  horses_full[i] = 0
);



% output ["horse = ["] ++
%        [show(trace("horses_full[i] = \(horses_full[i])", horses_full[i])) ++ if i < n then ", " else "" endif | i in 1..n ] ++
%        ["];\n"] ++
%        ["obj = \(obj);"]
% output [show(horses_full)];