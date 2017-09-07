int: T; % maximum time allowed;
set of int: TIME = 1..T;

int: E; % weight of elephant in STONES;
set of int: STONE = 0..E;

int: G; % number of guards
set of int: GUARD = 1..G;
array[GUARD] of STONE: easy;   
array[GUARD] of STONE: hard;
array[GUARD] of TIME: tired;

GUARD: p; % maximum people on pier;
GUARD: b; % maximum people on boat;

set of int: ACT = -1..E; % -1 = goto bank, 0 = wait, > 0 carry stones  
int: wait = 0;
int: to_bank = -1;
array[GUARD,TIME] of var ACT: act;        % action at time t
var TIME: end;                            % end time;







array[TIME] of var int: boat; % num of stones on boat after action
array[GUARD, TIME] of var bool: onboat;

function var int: num_moved(TIME: t) = sum(g in GUARD)(max( act[g, t], 0 ));
function var int: moved_to(var ACT: action, var bool: before) =
  if action = 0 then before else action > 0 endif;

% fill onboat
constraint forall(g in GUARD)(
  onboat[g, 1] = moved_to(act[g, 1], false)
);
constraint forall(g in GUARD, t in 2..end)(
  onboat[g, t] = moved_to(act[g, t], onboat[g, t-1])
);
constraint forall(g in GUARD, t in end+1..T)(
  onboat[g, t] = false
);

% limit of num of guards on boat
constraint forall(t in 1..end)(
  sum(g in GUARD)(onboat[g, t]) <= b
);

% limit of num of guards on pier
constraint forall(t in 1..end)(
  sum(g in GUARD)(act[g, t] != 0) <= p
);

% have to move same direction each time
constraint forall(t in 1..end)(
  (forall(g in GUARD)(act[g, t] >= 0)) \/
  (forall(g in GUARD)(act[g, t] <= 0))
);

% correct number of stones boat
constraint boat[1] = num_moved(1);
constraint forall(t in 1..end)(boat[t] = boat[t-1] + num_moved(t));
constraint forall(t in end+1..T)(boat[t] = 0);

% has more or equal than E stones in the end
constraint boat[end] >= E;

% only wait after end
constraint forall(g in GUARD, t in end+1..T)(act[g, t] = 0);

solve minimize end;
% constraint end = 3;
% solve satisfy;

% constraint act = array2d(GUARD, TIME, [
%   10, 0, 0, 0, 0, 0, 0, 0, 0, 0,
%   5, -1, 10, 0, 0, 0, 0, 0, 0, 0,
%   5, -1, 10, 0, 0, 0, 0, 0, 0, 0,
%   0, 0, 10, 0, 0, 0, 0, 0, 0, 0,
% ]);

% onboat = array2d(1..4 ,1..10 ,[
%   true, true, true, false, false, false, false, false, false, false,
%   true, false, true, false, false, false, false, false, false, false,
%   true, false, true, false, false, false, false, false, false, false,
%   false, false, true, false, false, false, false, false, false, false]);

% boat = array1d(1..10 ,[20, 18, 48, 0, 0, 0, 0, 0, 0, 0]);