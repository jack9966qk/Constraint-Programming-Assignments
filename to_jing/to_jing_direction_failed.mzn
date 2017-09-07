% Liu Bei forsees that Yuan Shiu will be defeated by Cao Cao
% He needs to find a route to safety in Jin province before the defeat
% But Cao Cao's soldiers are everywhere

int: nrow;
set of int: ROW = 1..nrow;
int: ncol;
set of int: COL = 1..ncol;

% Plains, Mountain, Forest, City, River
enum TERRAIN = { P, M, F, C, R };
array[TERRAIN] of int: delay;
int: timelimit;

array[ROW,COL] of TERRAIN: terrain;
array[ROW,COL] of int: soldier;
array[ROW,COL] of bool: Jin;

int: start_row;
int: start_col;

int: maxstep;
set of int: STEP = 1..maxstep;
set of int: STEP0 = 0..maxstep;

var STEP: steps;

enum DIRECTION = { N, S, W, E };
array[DIRECTION] of DIRECTION: opposite = [S, N, E, W];

array[STEP] of var DIRECTION: directions;
array[STEP0] of var 0..nrow: rows;
array[STEP0] of var 0..ncol: cols;

set of int: DIFF = {-1, 0, 1};
array[DIRECTION] of DIFF: row_diff = [-1, 1, 0, 0];
array[DIRECTION] of DIFF: col_diff = [0, 0, -1, 1];

function var int: next_row(var int: curr, var DIRECTION: direction) = curr + row_diff[direction];
function var int: next_col(var int: curr, var DIRECTION: direction) = curr + col_diff[direction];

constraint rows[0] = start_row;
constraint cols[0] = start_col;
constraint forall(i in 1..steps)(rows[i] != 0 /\ cols[i] != 0);
constraint forall(i in 1..steps)(rows[i] = next_row(rows[i-1], directions[i]));
constraint forall(i in 1..steps)(cols[i] = next_col(cols[i-1], directions[i]));

constraint forall(i in steps+1..maxstep)(directions[i] = N);
constraint forall(i in steps+1..maxstep)(rows[i] = 0 /\ cols[i] = 0);

constraint forall(i in 1..steps-1)(directions[i] != opposite[directions[i+1]]);

include "alldifferent_except_0.mzn";
constraint alldifferent_except_0([rows[i] * ncol + cols[i] | i in STEP]);

% reach Jin province
constraint Jin[rows[steps], cols[steps]] = true;

% visit at most one city
constraint sum(s in 1..steps)(terrain[rows[s], cols[s]] = C) <= 1;

% can't enter mountain
constraint forall(s in 1..steps)(terrain[rows[s], cols[s]] != M);

% not too much delay
constraint time <= timelimit;
var int: time;
constraint time = sum(s in 1..steps)(delay[terrain[rows[s], cols[s]]]);

% minimize the number of soldiers traversed
solve minimize obj;
var int: obj;
constraint obj = sum(s in 0..steps)(soldier[rows[s], cols[s]]);



array[ROW,COL] of var STEP0: visit; % which step do we visit position or 0 if not visited
function var int: index(array[STEP0] of var 0..nrow: rows,
                        array[STEP0] of var 0..ncol: cols,
                        ROW: r, COL: c) =
  sum(i in 0..steps)(
    if (rows[i] = r /\ cols[i] = c) then i + 1 else 0 endif
  );

constraint forall(r in ROW, c in COL)(
  visit[r, c] = index(rows, cols, r, c)
);

constraint forall(i in 0..steps)(
  visit[rows[i], cols[i]] = i + 1
);

array[TERRAIN] of string: ter = [".", "#", "^", "C", "~"];

output 
       ["%"] ++
       [ " " ++ ter[fix(terrain[r,c])] ++ if c = ncol then "\n%" else "" endif
       | r in ROW, c in COL ]
       ++ ["\n%"] ++
       [ if soldier[r,c] > 0 then show_int(2,soldier[r,c]) else " ." endif
         ++ if c = ncol then "\n%" else "" endif
       | r in ROW, c in COL ] ++
       ["\n"] ++
       ["%"] ++
        [ if fix(visit[r,c]) > 0 then show_int(2,visit[r,c]) else " ." endif
          ++ if c = ncol then "\n%" else "" endif
        | r in ROW, c in COL ] ++
        ["\nvisit = array2d(ROW,COL,\(visit));\nsteps = \(steps);\ntime = \(time);\nobj = \(obj);"]
       ;