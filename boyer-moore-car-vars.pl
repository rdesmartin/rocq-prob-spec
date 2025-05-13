/* based on the grading example from Luc De Raedt video https://youtu.be/3lnVBqxjC88?si=24pSYL8O4nWb697t&t=879 */

0.4 :: rain(W) :- weather_state(W).
  0.5 :: poor(R) :- road_state(R).

  weather_state(w1). weather_state(w2).
  road_state(r1). road_state(r2).

  driving_condition(W,R,good) :- not rain(W), not poor(R).
  0.3::driving_condition(W,R,good); 0.5::driving_condition(W,R,mid); 0.2::driving_condition(W,R,poor) :- not rain(W), poor(R).
  0.1::driving_condition(W,R,good); 0.6::driving_condition(W,R,mid); 0.3::driving_condition(W,R,poor) :- rain(W), not poor(R).
  driving_condition(W,R,poor) :- rain(W), poor(R).

  query(driving_condition(w1,r1,good)).
