nat(zero).
nat(s(X)) :- nat(X).

list(cons(X,Y)) :- nat(X), list(Y)
list(nil ).

?- list(cons(zero,nil)).

