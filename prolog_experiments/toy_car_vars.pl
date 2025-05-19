/* based on the grading example from Luc De Raedt video https://youtu.be/3lnVBqxjC88?si=24pSYL8O4nWb697t&t=879 */
wet_road(X) :- rain(X).

rain(s1).
obstacle(s1,medium).
obstacle(s2,severe).

unsafe(X) :- wet_road(X), obstacle(X, medium).
unsafe(X) :- not(wet_road(X)), obstacle(X, severe).

?- unsafe(s1). /* true */
?- unsafe(s2). /* true */
