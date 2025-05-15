Definition Sim := nat.

Inductive Rain : Sim -> Prop := rain: forall s, Rain s.

Inductive ObstacleLevel := none | medium | severe.

Inductive Obstacle (l: ObstacleLevel): Sim -> Prop := obstacle: forall s, Obstacle l s.

Inductive Wet_road: Sim -> Prop := from_rain: forall s, Rain s -> Wet_road s.

Inductive Unsafe (s: Sim): Prop :=
| unsafe_wet_obst_medium: Wet_road s -> Obstacle medium s  -> Unsafe s
| unsafe_notwet_obst_severe: ~Wet_road s -> Obstacle severe s -> Unsafe s.

(* Facts *)
Definition s1 := 1.
Definition obst_s1 := obstacle medium s1.
Definition rain_s1 := rain s1.

(* Query ?- unsafe(s1). *)

Lemma query_unsafe_s1: Unsafe s1.
Proof.
  apply unsafe_wet_obst_medium.
  apply (from_rain s1).
  apply rain_s1.
  apply obst_s1.
Qed.

(* Definition s2 := 2. *)
(* Definition obst_s2 := obstacle severe s2. *)
(* Axiom rain_s2 : Rain s2 -> False. *)

(* Lemma query_unsafe_s2: Unsafe s2. *)
(* Proof. *)
(*   apply unsafe_notwet_obst_severe. *)
(*   apply obst_s1. *)
(* Qed. *)
