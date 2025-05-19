/* based on the grading example from Luc De Raedt video https://youtu.be/3lnVBqxjC88?si=24pSYL8O4nWb697t&t=879 */

/* Facts */
0.4 :: rain(S) :- scenario(S).
0.5 :: fog(S) :- scenario(S).

scenario(s1).
scenario(s2).

/* rules */
 driving_condition(S,good) :- not rain(S), not fog(S).
 0.5::driving_condition(S,good); 0.5::driving_condition(S,mid); 0.2::driving_condition(S,poor) :- not rain(S), fog(S).
 0.1::driving_condition(S,good); 0.6::driving_condition(S,mid); 0.3::driving_condition(S,poor) :- rain(S), not fog(S).
 driving_condition(S,poor) :- rain(S), fog(S).

/* queries */
rain(s1) :- scenario(s1).
query(driving_condition(s1,good),driving_condition(s1,mid)).
