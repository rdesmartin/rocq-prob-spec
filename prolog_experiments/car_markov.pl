%%%%%%%%%%
% model
% - start(modelID,state) complete AD
% - trans(modelID,time,fromState,toState) possibly incomplete AD per fromState
% - emit(modelID,time,state,symbol) possibly incomplete AD per state
%%%%%%%%%%

% example 1: weather (with umbrella yes/no added)
0.99::start(car,clear); 0.01::start(car,collision).
0.7::trans(car,T,clear,clear); 0.3::trans(car,T,clear,collision).
0.01::trans(car,T,collision,clear); 0.99::trans(car,T,collision,collision).
0.9::emergency(car,T,clear,no); 0.1::emergency(car,T,clear,yes).
0.1::emergency(car,T,collision,no); 0.9::emergency(car,T,collision,yes).

%%%%%%%%%

%%%%%%%%%
% background: which state are we in at which time?
% state(modelID,time,state)
%%%%%%%%%
state(A,0,S) :- start(A,S).
state(A,T,S) :- T > 0, TT is T-1, state(A,TT,S2), trans(A,TT,S2,S).

%%%%%%%%%
% background: which symbol do we see at which time?
% observe(modelID,time,symbol)
%%%%%%%%%
observe(A,T,S) :- state(A,T,State),emergency(A,T,State,S).

%%%%%%%%%
% running the model to generate a sequence of labels
% observe_sequence(modelID,https://dtai.cs.kuleuven.be/problog/tutorial/various/06_hmm.html)
%%%%%%%%%
observe_sequence(TS,[First|List]) :-
     start(TS,State),
     emergency(TS,0,State,First),
     ob_seq(TS,State,List,0).
% stop
ob_seq(_,_,[],_).
% keep going: add H to output, go to next time and state
ob_seq(TS,State,[H|Tail],Time) :-
     trans(TS,Time,State,State2),
     TT is Time+1,
     emergency(TS,TT,State2,H),
     ob_seq(TS,State2,Tail,TT).

%%%%%%%%%
% running the model to generate a sequence of states
% state_sequence(modelID,list_of_states)
%%%%%%%%%
state_sequence(TS,[State|List]) :-
     start(TS,State),
     st_seq(TS,State,List,0).
% stop
st_seq(_,_,[],_).
% keep going: add H to output, go to next time and state
st_seq(TS,State,[State2|Tail],Time) :-
     trans(TS,Time,State,State2),
     TT is Time+1,
     st_seq(TS,State2,Tail,TT).

%%%%%%%%%
% queries
%%%%%%%%%

query(observe_sequence(car,L)) :- between(0,2,N),length(L,N).
query(state_sequence(car,L)) :- between(0,2,N),length(L,N).
query(state(car,T,_)) :- between(0,2,T).
query(observe(car,T,_)) :- between(0,2,T).
