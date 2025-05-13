(* Inductive list': (list nat) -> Prop := *)
(* | nat_cons: forall (x : nat) (y: list nat), list' y  ->  list' (cons x y) *)
(* | nat_nil: list' nil. *)


Axiom Obstacle: Type -> Prop.
Axiom Rain: Type -> Prop.
Axiom Fog: Type -> Prop.

Inductive unsafe: Type -> Prop :=
| Unsafe_from_obstacle : forall o, Obstacle o -> unsafe o
| Unsafe_from_rain_fog: forall r f, Rain r -> Fog f -> unsafe (r * f)%type.


Lemma unsafe_query: forall o, Obstacle o -> unsafe o.
Proof.
  intros o.
  apply Unsafe_from_obstacle.
Qed.
