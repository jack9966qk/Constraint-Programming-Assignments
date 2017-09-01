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
array[ROW,COL] of var STEP0: visit; % which step do we visit position or 0 if not visited

% constraint visit = array2d(ROW,COL,[1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 11, 12, 13, 14, 4, 0, 10, 0, 0, 15, 5, 0, 9, 0, 0, 16, 6, 7, 8, 0, 0, 17]);


% ========= added representation ==========
int: npos = nrow * ncol;
set of int: POS = 1..npos;
% set of int: POS0 = 0..npos;
array[STEP] of var POS: positions;

function var int: get_pos(var ROW: row, var COL: col) = (row - 1) * ncol + (col - 1) + 1;
function var int: get_row(var POS: pos) = (pos - 1) div ncol + 1;
function var int: get_col(var POS: pos) = (pos - 1) mod ncol + 1;
function var int: get_row_of_step(var STEP: s) = get_row(positions[s]);
function var int: get_col_of_step(var STEP: s) = get_col(positions[s]);


function POS: get_pos(ROW: row, COL: col) = (row - 1) * ncol + (col - 1) + 1;
function ROW: get_row(POS: pos) = (pos - 1) div ncol + 1;
function COL: get_col(POS: pos) = (pos - 1) mod ncol + 1;

function bool: is_mountain(POS: pos) = (terrain[get_row(pos), get_col(pos)] = M);
function bool: is_mountain(ROW: row, COL: col) = (terrain[row, col] = M);

function array[int] of int: make_edges(int: pos) = if pos <= npos
  then (if is_mountain(pos) then [] else make_edge(pos) endif) ++ make_edges(pos + 1)
  else []
  endif;

function array[int] of int: make_edge(int: pos) = let { int: row = get_row(pos), int: col = get_col(pos) } in
  (if row > 1 /\ (not is_mountain(row - 1, col)) then [pos, get_pos(row - 1, col)] else [] endif) ++
  (if col > 1 /\ (not is_mountain(row, col - 1)) then [pos, get_pos(row, col - 1)] else [] endif) ++
  (if row < nrow /\ (not is_mountain(row + 1, col)) then [pos, get_pos(row + 1, col)] else [] endif) ++
  (if col < ncol /\ (not is_mountain(row, col + 1)) then [pos, get_pos(row, col + 1)] else [] endif);
  
array[int] of POS: edges;
edges = make_edges(1);

array[int, int] of POS: edges2d;
edges2d = array2d(1..(length(edges) div 2), 1..2, edges);

% var int: r;
% var int: c;
% constraint get_col_of_step(1) = c;
% constraint get_row_of_step(1) = r;
% constraint positions[1] = 14;

% var STEP: arr_step;
% constraint arr_step = max(array1d(POS, visit));
% constraint forall(s in steps+1..maxstep)(visit[get_row_of_step(s), get_col_of_step(s)] = 0);

% ========= channel representations ==========
constraint forall(s in 1..steps)(
  visit[get_row_of_step(s), get_col_of_step(s)] = s
);

include "alldifferent_except_0.mzn";
constraint alldifferent_except_0(array1d(POS, visit));

% start at start position
constraint visit[start_row,start_col] = 1;
% =================
constraint positions[1] = get_pos(start_row, start_col);

% only use steps moves
constraint sum(r in ROW, c in COL)(visit[r,c] >= 1) <= steps;
% =================


% reach Jin province
% constraint exists(r in ROW, c in COL)(Jin[r,c] /\ visit[r,c] >= 1);
% =================
constraint Jin[get_row_of_step(steps), get_col_of_step(steps)] = true;

% visit at most one city
% constraint not exists(r1,r2 in ROW, c1,c2 in COL)
%                      ((r1 != r2 \/ c1 != c2) 
%                       /\ terrain[r1,c1] = C /\ terrain[r2,c2] = C 
%                       /\ visit[r1,c1] >= 1 /\ visit[r2,c2] >= 1);
% =================
constraint sum(s in 1..steps)(terrain[get_row_of_step(s), get_col_of_step(s)] = C) < 2;

% cant enter Mountain
constraint not exists(r in ROW, c in COL)(terrain[r,c] = M /\ visit[r,c] >= 1);
% =================
constraint not exists(s in 1..steps)(terrain[get_row_of_step(s), get_col_of_step(s)] = M);

% visit only one place in every step
% constraint forall(r1,r2 in ROW, c1,c2 in COL)
%                  (r1 != r2 \/ c1 != c2  
%                   -> (visit[r1,c1] = 0 
%                       \/ visit[r2,c2] != visit[r1,c1]));
% =================
% constraint forall(i, j in 1..steps where i < j)(positions[i] != positions[j]);
% constraint alldifferent_except_0([positions[s] | s in 1..steps]);

% steps form a path
% constraint forall(s in 1..steps-1)
%                  (exists(r1, r2 in ROW, c1, c2 in COL)
%                         (abs(r1-r2) + abs(c1-c2) = 1 
%                          /\ visit[r1,c1] = s /\ visit[r2,c2] = s+1));

% no shortcuts
% constraint forall(r1,r2 in ROW, c1,c2 in COL)
%                  (abs(r1-r2) + abs(c1-c2) = 1 ->
%                   visit[r1,c1] = 0 \/ visit[r2,c2] = 0 \/
%                   abs(visit[r1,c1] - visit[r2,c2]) = 1);
% =================
% array[STEP] of var int: step_rows;
% array[STEP] of var int: step_cols;
% constraint forall(s in STEP)(step_rows[s] = get_row_of_step(s));
% constraint forall(s in STEP)(step_cols[s] = get_col_of_step(s));
constraint forall(s in 1..steps-1)(
  abs(get_row_of_step(s) - get_row_of_step(s+1)) +
  abs(get_col_of_step(s) - get_col_of_step(s+1)) = 1
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% include "table.mzn";
% constraint forall(s in 1..steps - 1)(
%   table([positions[s], positions[s+1]], edges2d)
% );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% not too much delay
constraint time <= timelimit;
var int: time;
% var int: time = sum(r in ROW, c in COL)(delay[terrain[r,c]]*(visit[r,c] >= 1));
% =================
constraint time = sum(s in 1..steps)(delay[terrain[get_row_of_step(s), get_col_of_step(s)]]);

% minimize the number of soldiers traversed
solve minimize obj;
var int: obj;
% constraint obj = sum(r in ROW, c in COL)((visit[r,c] > 0)*soldier[r,c]);
constraint obj = sum(s in 1..steps)(soldier[get_row_of_step(s), get_col_of_step(s)]);
                         

array[TERRAIN] of string: ter = [".", "#", "^", "C", "~"];

output 
       ["%"] ++
       [ " " ++ ter[fix(terrain[r,c])] ++ if c = ncol then "\n%" else "" endif
       | r in ROW, c in COL ]
       ++ ["\n%"] ++
       [ if soldier[r,c] > 0 then show_int(2,soldier[r,c]) else " ." endif
         ++ if c = ncol then "\n%" else "" endif
       | r in ROW, c in COL ]
       ++ ["\n"] ++
       ["%"] ++
       [ if fix(visit[r,c]) > 0 then show_int(2,visit[r,c]) else " ." endif
         ++ if c = ncol then "\n%" else "" endif
       | r in ROW, c in COL ]
       ++ ["\nvisit = array2d(ROW,COL,\(visit));\nsteps = \(steps);\ntime = \(time);\nobj = \(obj);"]
       ;

% output ["\(npos)"]

array[1..(length(edges) div 2), 1..2] of var int: vedges;
constraint forall(i in 1..(length(edges) div 2), j in 1..2)(vedges[i, j] = edges2d[i, j]);
