% Beauty Trap
% Perform the most seductive dance

enum LEGS = {spin, leap, waltz, curtsey, prep, stand};
enum ARMS = {beckon, out, up, wrapped, neutral};
enum FACE = {smile, wink, batt, think, glow, blank};

int: maxlen;
set of int: STEP = 1..maxlen;
array[LEGS] of int: maxlegs;
array[ARMS] of int: maxarms;
array[FACE] of int: maxface;
constraint assert(maxlegs[stand] >= maxlen, "maxlegs[stand] smaller than maxlen");
constraint assert(maxarms[neutral] >= maxlen, "maxarms[neutral] smaller than maxlen");
constraint assert(maxface[blank] >= maxlen, "maxface[blank] smaller than maxlen");
array[LEGS,ARMS] of int: dance_value;
array[ARMS,FACE] of int: entice_value;
constraint assert(dance_value[stand,neutral] = 0, "incorrect dance_value array");
constraint assert(entice_value[neutral,blank] = 0, "incorrect entice_value array");
int: boredom; % how bored each step make the viewer

var STEP: len;
array[STEP] of var LEGS: legs;
array[STEP] of var ARMS: arms;
array[STEP] of var FACE: face;

% limit on how many times same move can be used
constraint forall(l in LEGS)(
  sum(s in STEP)(legs[s] = l) <= maxlegs[l]
);

constraint forall(a in ARMS)(
  sum(s in STEP)(arms[s] = a) <= maxarms[a]
);

constraint forall(f in FACE)(
  sum(s in STEP)(face[s] = f) <= maxface[f]
);

include "regular.mzn";

% must prep before leap
% after spin, can only curtsey, prep or stand
% after leap, can only spin, waltz or stand
% cannot prep directly after curtsey
constraint regular([legs[i] | i in STEP], card(LEGS) + 1, card(LEGS), legs_t, 1, {7});
array[1..card(LEGS)+1, 1..card(LEGS)] of 0..card(LEGS)+1: legs_t = 
  [| 2, 0, 4, 5, 6, 7 % start
   | 0, 0, 0, 5, 6, 7 % just did spin
   | 2, 0, 4, 0, 0, 7 % just did leap
   | 2, 0, 4, 5, 6, 7 % just did waltz
   | 2, 0, 4, 5, 0, 7 % just did curtsey
   | 2, 0, 4, 5, 6, 7 % just did prep
   | 2, 0, 4, 5, 6, 7 % just did stand
   |];

% can waltz at most 3 times in a row
constraint forall(i in 1..len-4)(
  sum(j in i..i+4)(legs[j] = waltz) <= 3
);

% must be a stand between waltz and curtsey
constraint forall(i in 1..len)(
  forall(j in i+1..len)(
    (legs[i] = waltz /\ legs[j] = curtsey) ->
      exists(k in i+1..j-1)(legs[k] = stand)
  )
);

% can beckon only directly after out or up
% wrapped only directly after beckon or neutral, first move wrapped ok
% cannot do any two same moves in a row except neutral
constraint regular([arms[i] | i in STEP], card(ARMS) + 1, card(ARMS), arms_t, 1, {6});
array[1..card(ARMS)+1, 1..card(ARMS)] of 0..card(ARMS)+1: arms_t = 
%    b, o, u, w, n
  [| 0, 3, 4, 5, 6 % 1: start
   | 0, 3, 4, 5, 6 % 2: just did beckon
   | 2, 0, 4, 0, 6 % 3: just did out
   | 2, 3, 0, 0, 6 % 4: just did up
   | 0, 3, 4, 0, 6 % 5: just did wrapped
   | 0, 3, 4, 5, 6 % 6: just did neutral
   |];

% no more two gestures in a row except blank
% cannot think directly after smile or batt
constraint regular([face[i] | i in STEP], card(FACE) + 1, card(FACE), face_t, 1, {7});
array[1..card(FACE)+1, 1..card(FACE)] of 0..card(FACE)+1: face_t = 
  [| 2, 3, 4, 5, 6, 7 % start
   | 0, 3, 4, 0, 6, 7 % just did smile
   | 2, 0, 4, 5, 6, 7 % just did wink
   | 2, 3, 0, 0, 6, 7 % just did batt
   | 2, 3, 4, 0, 6, 7 % just did think
   | 2, 3, 4, 5, 0, 7 % just did glow
   | 2, 3, 4, 5, 6, 7 % just did blank
   |];

% must end in stand, neutral, blank
constraint forall(i in len+1..maxlen)(
  (legs[i] = stand) /\ (arms[i] = neutral) /\ (face[i] = blank)
);

% forbid impossible moves
constraint forall(i in 1..len)(
  dance_value[legs[i], arms[i]] >= 0
);

constraint forall(i in 1..len)(
  entice_value[arms[i], face[i]] >= 0
);

% maximize seductive power, which is value + enticements - boredom * len
var int: obj;
constraint obj = sum(i in 1..len)(dance_value[legs[i], arms[i]]) +
                 sum(i in 1..len)(entice_value[arms[i], face[i]]) -
                 (boredom * len);
solve maximize obj;

output ["len = \(len);\n"] ++
       ["legs = ["] ++
       [show(legs[i]) ++ if i < maxlen then ", " else "" endif | i in 1..maxlen ] ++
       ["];\n"] ++
       ["arms = ["] ++
       [show(arms[i]) ++ if i < maxlen then ", " else "" endif | i in 1..maxlen ] ++
       ["];\n"] ++
       ["face = ["] ++
       [show(face[i]) ++ if i < maxlen then ", " else "" endif | i in 1..maxlen ] ++
       ["];\n"] ++
       ["obj = \(obj);"];