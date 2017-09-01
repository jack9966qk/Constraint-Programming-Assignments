% assignment 2
% select a set of raiding warrior
enum WARRIOR;
WARRIOR: dummy; 
enum CLAN; % the clan they belong too

int: l; % minimum raid party size
int: u; % maximum raid party size
int: m; % limit of hatreds

array[WARRIOR] of int: strength;
array[WARRIOR] of CLAN: clan;

array[CLAN,CLAN] of 0..1: hates;

array[1..u] of var WARRIOR: raidx;

constraint sum(i in 1..u)(raidx[i] != WARRIOR[1]) >= l;
constraint forall(i in 1..u-1)(raidx[i] >= (raidx[i] != 0) + raidx[i+1]);
constraint sum(i in 1..u)(
              sum(j in 1..u where j < i)(
                hates[clan[raidx[i]], clan[raidx[j]]]
              )
           ) <= m;



var int: obj;
constraint obj == sum(i in raidx)(strength[i]);
solve maximize obj;

output ["raid = {"] ++ [if fix(raidx[i]) != dummy then show(raidx[i])
                      ++ if i < u /\ fix(raidx[i+1]) != dummy then ", " else "" endif
                     else "" endif | i in 1..u ] ++ ["};\n"]
                     ++ ["obj = \(obj);"];
% output ["raid = \(raid)"];
% output ["raid = \(raid)" ++ "\n" ++ "obj = \(obj)"];