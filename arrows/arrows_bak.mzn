int: length; % height of lake
set of int: LENGTH = 0..length-1;
int: width; % width of lake
set of int: WIDTH = 0..width-1;

int: ntypes;  % number of types of ship
set of int: TYPE = 1..ntypes;
array[TYPE] of int: number;         % number of each type of ship
array[TYPE] of set of SHAPE: config; % configs for each type of ship

int: nshapes; % number of shapes
set of int: SHAPE = 1..nshapes;
set of int: SHAPE0 = 0..nshapes;
array[SHAPE] of set of ROFF: shape;

int: nroff; % number of rectangle offsets
set of int: ROFF = 1..nroff;
array[ROFF,1..4] of int: rectoff; % x offset, y offset, width, height

int: total_ships = sum(number);
set of int: SHIP = 1..total_ships;
array[SHIP] of var LENGTH:  x;
array[SHIP] of var WIDTH:   y;

array[LENGTH] of WIDTH: mist; % mist starts at this width, goes downward
array[WIDTH] of int: arrow;  % number of arrows that arrive at this height
array[TYPE] of int: price;
int: budget;
enum STAGE = {A,B,C,D,E,F};
STAGE: stage;


var int: tarrows;



% ============= COMMON =============
function TYPE: get_type(SHIP: s, TYPE: from) =
    if s <= sum(i in 1..from)(number[i])
    then from
    else get_type(s, from+1)
    endif;

array[SHIP] of TYPE: types = [get_type(s, 1) | s in SHIP];
array[SHIP] of set of SHAPEp: valid_configs = [config[types[s]] union {nshapes+1} | s in SHIP];

set of int: SHAPEp = 1..nshapes+1;
array[SHAPEp] of set of ROFFp: shapep = shape ++ [{nroff+1}];
array[SHIP] of var SHAPEp: kp;

set of int: ROFFp = 1..nroff+1;

int: ndim = 2;
array[ROFFp, 1..ndim] of int: rect_size = array2d(ROFFp, 1..ndim, [rectoff[i, j] | i in ROFF, j in 3..4] ++ [0, 0]);
array[ROFFp, 1..ndim] of int: rect_offset = array2d(ROFFp, 1..ndim, [rectoff[i, j] | i in ROFF, j in 1..2] ++ [0, 0]);
array[SHIP, 1..ndim] of var int: pos;
constraint forall(s in SHIP)(
    pos[s, 1] = x[s] /\ pos[s, 2] = y[s]
);
array[1..ndim] of int: l = [0, 0];
array[1..ndim] of int: u = [length, width];

constraint trace("rect_size = \(rect_size)\n"); 

constraint trace("rect_offset = \(rect_offset)\n"); 

include "geost.mzn";
constraint geost_bb(
    ndim,
    rect_size,
    rect_offset,
    shapep,
    pos,
    kp,
    l,
    u
);

constraint forall(s in SHIP)(
    (kp[s] != nshapes + 1) -> (kp[s] in valid_configs[s])
);

% ============= STAGE A =============
constraint (stage in {A, B, C}) -> forall(s in SHIP)(kp[s] = 1);
constraint (stage in {A, B, C}) -> tarrows = 0;

array[SHIP] of int: dx = [rectoff[types[s], 3] | s in SHIP];
array[SHIP] of int: dy = [rectoff[types[s], 4] | s in SHIP];

% non-overlap
include "diffn.mzn";
constraint (stage == A) -> diffn(x, y, dx, dy);

% fit in width and length
constraint (stage == A) -> forall(s in SHIP)(x[s] + dx[s] <= length);
constraint (stage == A) -> forall(s in SHIP)(y[s] + dy[s] <= width);

% ============= STAGE B =============

% ============= STAGE C =============
% constraint (stage in {C, D, E, F}) -> forall(s in SHIP)(
%     let { var int: co = kind[s] } in
%     forall(sh in shape[co])(
%         let { var int: shape_x = x[s] + rectoff[sh, 1];
%                 var int: shape_y = y[s] + rectoff[sh, 2];
%                 int: shape_dx = rectoff[sh, 3] } in
%         forall(sx in shape_x..shape_x + shape_dx - 1)(
%             shape_y >= mist[sx]
%         )
%     )
% );

constraint (stage in {C, D, E, F}) -> forall(s in SHIP)(
    forall(co in config[types[s]])(
        forall(sh in shape[co])(
            let { var int: shape_x = x[s] + rectoff[sh, 1];
                  var int: shape_y = y[s] + rectoff[sh, 2];
                  int: shape_dx = rectoff[sh, 3] } in
            forall(sx in shape_x..shape_x + shape_dx - 1)(
                shape_y >= mist[sx]
            )
        )
    )
);

% ============= STAGE D =============
% constraint (stage in {C, D, E, F}) -> tarrows = sum(s in SHIP)(
%     let { var int: co = kind[s] } in
%     sum(sh in shape[co])(
%         let { var int: shape_y = y[s] + rectoff[sh, 2];
%               int: shape_dx = rectoff[sh, 3];
%               int: shape_dy = rectoff[sh, 4];
%               var WIDTH: sy_hi = shape_y+shape_dy-1 } in
%         sy_hi
%         % sum(sy in shape_y..sy_hi) (
%         %     arrow[sy] * shape_dx
%         % )
%     )
% );
constraint (stage in {C, D, E, F}) -> tarrows = sum(s in SHIP)(
    sum(co in config[types[s]])(
        sum(sh in shape[co])(
            let { var int: shape_y = y[s] + rectoff[sh, 2];
                  int: shape_dx = rectoff[sh, 3];
                  int: shape_dy = rectoff[sh, 4];
                  var WIDTH: sy_hi = shape_y+shape_dy-1 } in
            sum(sy in shape_y..sy_hi) (
                arrow[sy] * shape_dx
            )
        )
    )
);

% ============= STAGE E =============



% ============= STAGE F =============

constraint (stage == F) -> false;

solve maximize tarrows;

output
    ["x = ["] ++
    fix([if i < total_ships then "\(x[i]), " else "\(x[i])" endif | i in SHIP]) ++
    ["];\n"] ++
    ["y = ["] ++
    fix([if i < total_ships then "\(y[i]), " else "\(y[i])" endif | i in SHIP]) ++
    ["];\n"] ++
    ["k = ["] ++
    fix([if i < total_ships then "\(kp[i] - 1), " else "\(kp[i] - 1)" endif | i in SHIP]) ++
    ["];\n"] ++
    % ["dx = ["] ++
    % fix([if i < total_ships then "\(dx[i]), " else "\(dx[i])" endif | i in SHIP]) ++
    % ["];\n"] ++
    % ["dy = ["] ++
    % fix([if i < total_ships then "\(dy[i]), " else "\(dy[i])" endif | i in SHIP]) ++
    % ["];\n"] ++
    ["tarrows = \(tarrows);"];