Inductive Rain : bool -> Prop := rain: Rain true. 

Inductive ObstacleLevel := none | medium | severe.

Inductive Obstacle (l: ObstacleLevel): Prop := obstacle: Obstacle l. 

Inductive Unsafe: Prop :=
| unsafe_rain_obst_medium: Rain true -> Obstacle medium -> Unsafe
| unsafe_notrain_obst_severe: Rain false -> Obstacle severe -> Unsafe.

(* Facts *)
Definition obst := obstacle medium.

(* Query ?- unsafe = true. *)

Lemma query_unsafe: Unsafe.
  apply (unsafe_rain_obst_medium rain obst).
  Qed.

Let query_unsafe' := unsafe_rain_obst_medium rain obst.

Check query_unsafe'.
