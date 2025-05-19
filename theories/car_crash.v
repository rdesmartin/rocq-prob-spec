From mathcomp Require Import all_ssreflect.
From mathcomp Require Import measure reals ereal.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum lra.

Section car_crash.
Context d {A : measurableType d} {R : realType} {P : probability A R}.

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
| coll_o2: Collision o1 false -> Collision o2 true -> Crash.

End SectionName.

Inductive PossibleWorlds: Crash -> Crash -> Prop := 
| crash c1 c2 not_c1 not_c2 : PossibleWorlds (coll_o1 c1 not_c2) (coll_o2 not_c1 c2).

Inductive AllCrash : Type :=
| all_crash {c1} {c2} : PossibleWorlds c1 c2 -> AllCrash.

Let prob_to_real {r} (p : Prob r) : R := r.

Let prob_collision {o} {b} (c : Collision o b) : R :=  
match c with
| collision p => prob_to_real p
end.

Let prob_crash (c : Crash) : R := 
    match c with
    | coll_o1 c1 not_c2 => prob_collision c1 * prob_collision not_c2
    | coll_o2 not_c1 c2 => prob_collision not_c1 * prob_collision c2
    end.

Let prob_all_crash (ac : AllCrash) : R := 
    match ac with
    all_crash c1 c2 _ => prob_crash c1 + prob_crash c2
    end.

Goal forall (ac : AllCrash), 
    prob_all_crash ac = (32/100)%R.
Proof.
  (* move=>[c1 c2]. *)
  move=> [[c1t c2f p|c1f c2t p] [[[]] [[]] [[]] [[]]]]
  rewrite /prob_all_crash //= ! /prob_to_real;
  nra.
Qed.

End car_crash.

