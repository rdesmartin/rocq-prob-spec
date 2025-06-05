(*Definition Sim := nat.

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
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import measure reals ereal.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum lra.

Section car_crash.
Context d {A : measurableType d} {R : realType} {P : probability A R}.

Variable controller : R -> R -> R. 

Inductive Obstacle : Type := o1 | o2.
Inductive Prob (p : R) : Prop :=
  prob : Prob p.

Let _prob_collision (o : Obstacle) : R :=
    match o with
    | o1 => (2/10)%R
    | o2 => (2/10)%R
    end.

Let _prob_collisionb o b : R :=
    match o , b with
    |  o , true => _prob_collision o
    |  o , _ => 1 - _prob_collision o
    end.
    
Inductive Collision (o : Obstacle) (b : bool) : Prop :=
| collision : Prob (_prob_collisionb o b) -> Collision o b.

Inductive Crash: Type:=
| coll_o1: Collision o1 true -> Collision o2 false -> Crash
| coll_o2: Collision o2 true -> Collision o1 false -> Crash.

Inductive PossibleWorlds: Crash -> Crash -> Prop :=
| pw c1 c2 nc1 nc2 : PossibleWorlds (coll_o1 c1 nc2) (coll_o2 c2 nc1).

Inductive AllCrash : Type :=
| all_crash {c1} {c2} : PossibleWorlds c1 c2 -> AllCrash.

Let prob_to_real {r} (p : Prob r) : R := r.

Let prob_collision {o} {b} (c : Collision o b) : R :=
match c with
| collision p => prob_to_real p
end.

Let prob_crash (c : Crash) : R :=
    match c with
    | coll_o1 c1 nc2 => (prob_collision c1)*(prob_collision nc2)
    | coll_o2 c2 nc1 => (prob_collision c2)*(prob_collision nc1)
    end.
(*
P(c1 or c2) = P(c1) + P(c2) - P(c1 and c2)
*)
Let prob_all_crash (ac : AllCrash) : R :=
    match ac with
    all_crash c1 c2 _ => 
    prob_crash c1 + prob_crash c2 - (prob_crash c1)*(prob_crash c2)
end.
    
Goal forall (ac : AllCrash), prob_all_crash ac = (36/100)%R.
Proof.
  move=> [? ? [[[[]]] []]] //=.
  rewrite /prob_all_crash //= ! /prob_to_real;
  nra.
  (* move=>[c1 c2]. *)
  move=> [[c1t c2f p|c1f c2t p] [[[]] [[]] [[]] [[]]]]
  rewrite /prob_all_crash //= ! /prob_to_real;
  nra.
Qed.End car_crash.