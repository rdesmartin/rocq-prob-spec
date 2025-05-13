# Based on the coloured balls & coin example from the Luc de Raedt video (https://youtu.be/3lnVBqxjC88?si=PANrlwxpTCbAzN2o&t=458)

0.4 :: rain.
0.7 :: event(wet,none); 0.3 :: event(wet,medium).
0.5 :: event(fog,none); 0.3 :: event(fog,medium); 0.2 :: event(fog,severe).
0.1 :: off_road.

unsafe :- off_road.
unsafe :- rain, event(fog,severe).
unsafe :- not (event(wet,none), event(fog,none)).

query(unsafe).
