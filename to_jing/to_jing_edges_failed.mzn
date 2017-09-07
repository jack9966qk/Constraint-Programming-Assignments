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

int: maxpos = nrow * ncol;
set of int: POS = 1..maxpos;
set of int: POS0 = 0..maxpos;


function var ROW: get_row(var POS: pos) = (pos - 1) div ncol + 1;
function var COL: get_col(var POS: pos) = (pos - 1) mod ncol + 1;

function ROW: get_row(POS: pos) = (pos - 1) div ncol + 1;
function COL: get_col(POS: pos) = (pos - 1) mod ncol + 1;
function POS: get_pos(ROW: row, COL: col) = (row - 1) * ncol + (col - 1) + 1;


int: njings = sum(r in ROW, c in COL)(Jin[r, c] = true);
int: nedges = maxpos * 4 + 1;


array[1..nedges * 2] of POS0: edges1d = make_edges(1);
array[1..nedges, 1..2] of POS0: edges2d = array2d(1..nedges, 1..2, edges1d);

function array[int] of POS0: make_edges(int: pos) =
  if pos > maxpos then [0, 0] else
    let { int: row = get_row(pos), int: col = get_col(pos),
      bool: t = trace("\(row), \(col), \(pos), \(maxpos)\n", true) } in
    if Jin[row, col] then [pos, 0, pos, 0, pos, 0, pos, 0] else
      (if (row > 1 /\ terrain[row-1, col] != M) then [pos, get_pos(row-1, col)] else [0, 0] endif) ++
      (if (row < nrow /\ terrain[row+1, col] != M) then [pos, get_pos(row+1, col)] else [0, 0] endif) ++
      (if (col > 1 /\ terrain[row, col-1] != M) then [pos, get_pos(row, col-1)] else [0, 0] endif) ++
      (if (col < ncol /\ terrain[row, col+1] != M) then [pos, get_pos(row, col+1)] else [0, 0] endif)
    endif ++
    make_edges(pos + 1)
  endif;

array[STEP] of var POS0: positions;

include "table.mzn";
constraint forall(i in 1..maxstep-1)(
  table([positions[i], positions[i+1]], edges2d)
);

include "alldifferent_except_0.mzn";
constraint alldifferent_except_0(positions);

constraint positions[1] = get_pos(start_row, start_col);

% reach Jin province
constraint Jin[get_row(positions[steps]), get_col(positions[steps])] = true;

% visit at most one city
constraint sum(s in 1..steps)(
  terrain[get_row(positions[s]), get_col(positions[s])] = C
) <= 1;

% not too much delay
constraint time <= timelimit;
var int: time;
constraint time = sum(s in 1..steps)(
  delay[terrain[get_row(positions[s]), get_col(positions[s])]]
);

% minimize the number of soldiers traversed
solve minimize obj;
var int: obj;
constraint obj = sum(s in 1..steps)(
  soldier[get_row(positions[s]), get_col(positions[s])]
);



% array[POS] of var STEP0: visit;
array[ROW,COL] of var STEP0: visit; % which step do we visit position or 0 if not visited

% constraint forall(p in POS)(
%   visit[p] = sum(s in STEP)(if positions[s] = p then s else 0 endif)
% );

constraint forall(s in 1..steps)(
  visit[get_row(positions[s]), get_col(positions[s])] = s
);

% output ["%"] ++
%   [ if fix(visit[p]) > 0 then show_int(2, fix(visit[p])) else " ." endif ++
%   if (get_col(p) = ncol) then "\n%" else "" endif
%  | p in POS ];

% array[TERRAIN] of string: ter = [".", "#", "^", "C", "~"];

% output 
%        ["%"] ++
%        [ " " ++ ter[fix(terrain[r,c])] ++ if c = ncol then "\n%" else "" endif
%        | r in ROW, c in COL ]
%        ++ ["\n%"] ++
%        [ if soldier[r,c] > 0 then show_int(2,soldier[r,c]) else " ." endif
%          ++ if c = ncol then "\n%" else "" endif
%        | r in ROW, c in COL ]
%        ++ ["\n"] ++
%        ["%"] ++
%        [ if fix(visit[r,c]) > 0 then show_int(2,visit[r,c]) else " ." endif
%          ++ if c = ncol then "\n%" else "" endif
%        | r in ROW, c in COL ]
%        ++ ["\nvisit = array2d(ROW,COL,\(visit));\nsteps = \(steps);\ntime = \(time);\nobj = \(obj);"]
%        ;