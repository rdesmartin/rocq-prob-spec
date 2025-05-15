wet_road(X) :- rain(X).

rain(s1).
obstacle(s1,medium).
obstacle(s2,severe).

unsafe(X) :- wet_road(X), obstacle(X, medium).
unsafe(X) :- not(wet_road(X), obstacle(X, severe).

query(unsafe).
