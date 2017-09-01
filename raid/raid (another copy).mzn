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
var set of WARRIOR: raid;

constraint card(raid) >= l;
constraint card(raid) <= u;
constraint sum(i in raid)(
              sum(j in raid where j < i)(
                hates[clan[i], clan[j]]
              )
           ) <= m;

constraint forall(i in raid)(
             i != WARRIOR[1]
           );

var int: obj;
constraint obj == sum(i in raid)(strength[i]);

solve maximize obj;

% output ["raid = \(raid)"];
% output ["raid = \(raid)" ++ "\n" ++ "obj = \(obj)"];