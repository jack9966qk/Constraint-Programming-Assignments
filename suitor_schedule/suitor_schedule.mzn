% scheduling suitors
enum SUITOR;
SUITOR: LiuBei; % which suitor is LiuBei
int: n; % number of meetings
set of int: MEETING = 1..n;
array[MEETING] of SUITOR: suitor;

enum ROOM = { Red, Gold, Blue };
array[SUITOR,ROOM] of int: mintime;
array[SUITOR,ROOM] of int: maxtime;
constraint forall(s in SUITOR, r in ROOM)
                 (assert(mintime[s,r] >= 1 /\ maxtime[s,r] >= mintime[s,r], 
                  "error in mintime/maxtime at [\(s),\(r)]\n"));

array[ROOM,ROOM] of int: move;
constraint forall(r in ROOM)(assert(move[r,r] = 0,"move[\(r),\(r)] != 0\n"));

int: ndays; % number of days
set of int: DAY = 1..ndays;
int: earliest; % time for earliest meeting start
int: latest;  % time for end of latest meeting

int: lessontime; % time for kung fu lesson;
int: minsep;     % minimum time between consecutive kung fu lessons

array[ROOM] of int: usedstart;  % time others use each room each day
array[ROOM] of int: useddur;    % durations of others use

enum STAGE = {A,B,C};
STAGE: stage;

set of int: TIME = 0..24*ndays;

array[MEETING] of var TIME: start;
array[MEETING] of var TIME: dur;    % duration in false schedule
array[MEETING] of var ROOM: room;
set of int: KUNGFU = 1..n;
int: unused = 24*ndays+1;
array[KUNGFU] of var 0..unused: kungfu;  % start time for each lesson
   % unused lessons have start times after 24*ndays

%%%%%%%%%%%%%%%%%% STAGE A

% no overlapping
include "disjunctive.mzn";
constraint disjunctive(start, dur);

% min and max meeting time
constraint forall(m in MEETING)(
    (dur[m] >= mintime[suitor[m], room[m]]) /\
    (dur[m] <= maxtime[suitor[m], room[m]])
);

% limit earlist start and latest end time
constraint forall(m in MEETING)(
    let { var int: day = start[m] div 24, var int: time = start[m] mod 24 } in
    (time >= earliest) /\
    (time + dur[m] <= latest)
);

% room not used when meeting
constraint forall(m in MEETING)(
    let { var TIME: mstart = start[m] mod 24;
          var TIME: mdur = dur[m];
          var ROOM: r = room[m] } in
    disjunctive([mstart, usedstart[r]], [mdur, useddur[r]])
);

% objective
var int: obj;
constraint obj = 100 * sum(i in KUNGFU)(kungfu[i] <= 24*ndays) +
                 sum(m in MEETING where suitor[m] = LiuBei)(truedur[m]);

solve maximize obj;

constraint (stage != C) -> forall(i in KUNGFU)(kungfu[i] = 24*ndays + 1);

output ["start = \(start);\n"] ++
       ["dur = \(dur);\n"] ++
       ["room = \(room);\n"] ++
       ["kungfu = \(kungfu);\n"] ++
    %    ["truedur = \(truedur);\n"] ++
       ["obj = \(obj);"];

%%%%%%%%%%%%%%%%%% STAGE B
array[MEETING] of var TIME: fulldur;

constraint (stage != A) -> forall(i in 1..n-1)(
    fulldur[i] = dur[i] + move[room[i], room[i+1]]
);
constraint (stage != A) -> fulldur[n] = dur[n];

constraint (stage != A) -> disjunctive(start, fulldur);

% constraint (stage != A) -> forall(i, j in MEETING where room[i] != room[j])(
%     (start[i] < start[j]) -> (
%         let { var ROOM: ri = room[i]; var ROOM: rj = room[j] } in
%         start[i] + dur[i] + move[ri, rj] <= start[j]
%     )
% );


%%%%%%%%%%%%%%%%%% STAGE C
array[MEETING] of var TIME: truedur;    % duration in true schedule

constraint (stage = C) -> forall(i in KUNGFU)(
    (kungfu[i] = unused) \/
    exists(m in MEETING)(kungfu[i] + lessontime = start[m] + dur[m])
);

include "increasing.mzn";
constraint (stage = C) -> increasing(kungfu);

constraint (stage = C) -> forall(i in 1..n-1)(
    (kungfu[i] = unused) \/ (kungfu[i+1] = unused) \/
    (kungfu[i] + lessontime + minsep <= kungfu[i+1])
);

function var TIME: get_truedur(MEETING: m, 1..n+1: k) =
    if k > n
    then dur[m]
    else
        if kungfu[k] > dur[m]
        then min(dur[m], kungfu[k] - start[m])
        else get_truedur(m, k+1)
        endif
    endif;

constraint (stage = C) -> forall(m in MEETING)(
    truedur[m] = get_truedur(m, 1)
);

constraint (stage = C) -> forall(m in MEETING)(
    truedur[m] >= mintime[suitor[m], room[m]]
);

constraint (stage != C) -> forall(i in KUNGFU)(kungfu[i] = unused);
constraint (stage != C) -> forall(m in MEETING)(truedur[m] = dur[m]);