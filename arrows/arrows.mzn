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




array[SHIP] of var SHAPE1: k;


set of int: SHAPE1 = 1..nshapes+1;
set of int: ROFF1 = 1..nroff+1;

array[SHAPE1] of set of ROFF1: shape1 = shape ++ [{nroff+1}];

array[ROFF1, 1..2] of int: rect_size = array2d(ROFF1, 1..2,
    [rectoff[i, j] | i in ROFF, j in 3..4] ++ [0, 0]);
array[ROFF1, 1..2] of int: rect_offset = array2d(ROFF1, 1..2,
    [rectoff[i, j] | i in ROFF, j in 1..2] ++ [0, 0]);

array[SHIP, 1..2] of var int: pos;
constraint forall(s in SHIP)(
    pos[s, 1] = x[s] /\ pos[s, 2] = y[s]
);

include "geost.mzn";
constraint geost_bb(
    2,
    rect_size,
    rect_offset,
    shape1,
    pos,
    k,
    [0, 0],
    [length, width]
);

function TYPE: get_type(SHIP: s, TYPE: from) =
    if s <= sum(i in 1..from)(number[i])
    then from
    else get_type(s, from+1)
    endif;

array[SHIP] of TYPE: types = [get_type(s, 1) | s in SHIP];
array[SHIP] of set of SHAPE1: valid_configs = [config[types[s]] union {nshapes+1} | s in SHIP];

constraint forall(s in SHIP)(
    k[s] in valid_configs[s]
);

var int: tarrows;
solve maximize tarrows;
% solve satisfy;

constraint (stage != F) -> forall(s in SHIP)(k[s] != nshapes+1);



constraint (stage in {C, D, E, F}) -> forall(s in SHIP)(
    forall(roff in shape[k[s]])(
        let { var int: shape_x = x[s] + rectoff[roff, 1];
              var int: shape_y = y[s] + rectoff[roff, 2];
              int: shape_dx = rectoff[roff, 3] } in
        forall(sx in shape_x..shape_x + shape_dx - 1)(
            shape_y >= mist[sx]
        )
    )
);

% array[SHIP] of var set of int: shapes;
% constraint forall(s in SHIP)(
%     shapes[s] = shape[k[s]]
% );
% % array[SHIP] of var int: sysums;
% % constraint forall(s in SHIP)(
% %     sysums[s] = sum(roff in shapes[s])(
% %         y[s] + rectoff[roff, 2]
% %     )
% % );
% array[SHIP] of var ROFF: roff_sums;
% constraint forall(s in SHIP)(
%     roff_sums[s] = max(shapes[s])
% );

% array[SHIP] of var int: y_sums;
% constraint forall(s in SHIP)(
%     y_sums[s] = sum(roff in shape[k[s]])(
%         y[s] + rectoff[roff, 2]
%     )
% );

% array[SHIP] of var int: offy_sums;
% constraint forall(s in SHIP)(
%     offy_sums[s] = sum(roff in shape[k[s]])(
%         rectoff[roff, 2]
%     )
% );

% array[SHIP] of var int: shape_cards;
% constraint forall(s in SHIP)(
%     shape_cards[s] = card(shape[k[s]])
% );

% array[SHIP] of var int: dx_sums;
% constraint forall(s in SHIP)(
%     dx_sums[s] = sum(roff in shape[k[s]])(
%         rectoff[roff, 3]
%     )
% );

% array[SHIP] of var int: dy_sums;
% constraint forall(s in SHIP)(
%     dy_sums[s] = sum(roff in shape[k[s]])(
%         rectoff[roff, 4]
%     )
% );

% constraint x = [15, 1, 4, 11, 0];
% constraint y = [7, 3, 6, 4, 5];

% constraint (stage in {D, E, F}) -> tarrows = sum(s in SHIP)(
%     sum(roff in shape[k[s]] where k[s] in SHAPE)(
%         let { var int: by = y[s] + rectoff[roff, 2];
%               int: dx = rectoff[roff, 3];
%               int: dy = rectoff[roff, 4] } in
%         sum(sy in by..by+dy-1) (
%             arrow[sy] * dx
%         )
%     )
% );

% function var int: get_arrows(var WIDTH: y, var ROFF: roff) =
    % sum(sy in y..y+rectoff[roff, 4]-1)(
    %     rectoff[roff, 3] * arrow[sy]
    % );

% array[SHIP, ROFF] of var int: off_ys;
% constraint forall(s in SHIP)(
%     forall(ro in ROFF)(
%         off_ys[s, ro] =
%         if ro in shape[k[s]]
%         then y[s] + rectoff[ro, 2]
%         else -1
%         endif
%     )
% );

% function var int: get_arrows(SHIP: s, ROFF: ro) =
%     let { var WIDTH: ylb = off_ys[s, ro];
%           LENGTH: dx = rectoff[ro, 3];
%           WIDTH: dy = rectoff[ro, 4];
%           var WIDTH: yub = ylb + dy - 1 } in
%     sum(sy in ylb..yub)(
%         arrow[sy] * dx
%     );

% array[SHIP, ROFF] of var int: arrows;
% constraint forall(s in SHIP)(
%     forall(ro in ROFF)(
%         arrows[s, ro] =
%         if ro in shape[k[s]]
%         then get_arrows(s, ro)
%         else -1
%         endif
%     )
% );


% function var set of int: get_yrange(SHIP: s, ROFF: ro) =
%     let { var WIDTH: ylb = off_ys[s, ro];
%           LENGTH: dx = rectoff[ro, 3];
%           WIDTH: dy = rectoff[ro, 4];
%           var WIDTH: yub = ylb + dy - 1 } in
%     ylb..yub;

% array[SHIP, ROFF] of var set of int: yranges;
% constraint forall(s in SHIP)(
%     forall(ro in ROFF)(
%         yranges[s, ro] =
%         if ro in shape[k[s]]
%         then get_yrange(s, ro)
%         else 0..0
%         endif
%     )
% );

% constraint trace("\(sum(i in 1..10)(i))", true);

% array[SHIP, ROFF] of var int: arrows;
% constraint forall(s in SHIP)(
%     forall(ro in ROFF)(
%         arrows[s, ro] =
%         if ro in shape[k[s]]
%         then sum(y in yranges[s, ro])(rectoff[ro, 3] * arrow[y])
%         else -1
%         endif
%     )
% )

% function int: get_arrows(SHIP: s) = 
%     sum(ro in ROFF)(
%         sum(sy in yranges[s, ro])(
%             rectoff[ro, 3] * arrow[sy]
%         )
%     );

function var int: arrow_safe(int: y) =
    if y in WIDTH
    then arrow[y]
    else 0
    endif;

constraint (stage in {D, E, F}) -> tarrows = sum(s in SHIP where k[s] in SHAPE)(
    sum(sh in shape[k[s]])(
        let { var WIDTH: shape_y = y[s] + rectoff[sh, 2];
                LENGTH: shape_dx = rectoff[sh, 3];
                WIDTH: shape_dy = rectoff[sh, 4];
                var WIDTH: sy_hi = shape_y+shape_dy-1 } in
        sum(sy in shape_y..sy_hi) (
            arrow_safe(sy) * shape_dx
        )
    )
);



output
    ["x = ["] ++
    fix([if i < total_ships then "\(x[i]), " else "\(x[i])" endif | i in SHIP]) ++
    ["];\n"] ++
    ["y = ["] ++
    fix([if i < total_ships then "\(y[i]), " else "\(y[i])" endif | i in SHIP]) ++
    ["];\n"] ++
    ["k = ["] ++
    fix([if i < total_ships then "\(if k[i] = nshapes+1 then 0 else k[i] endif), " else "\(if k[i] = nshapes+1 then 0 else k[i] endif)" endif | i in SHIP]) ++
    ["];\n"] ++
    ["tarrows = \(tarrows);"];