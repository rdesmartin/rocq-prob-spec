Inductive nat' : forall x: nat, Prop :=
| zero_nat': nat' 0
| succ_nat': forall x, nat' x -> nat' (x + 1).

Inductive list': (list nat) -> Prop := 
| nat_cons: forall (x : nat) (y: list nat), nat' x -> list' y  ->  list' (cons x y) 
| nat_nil: list' nil.

Definition is_list_zero_nil := nat_cons 0 nil zero_nat' nat_nil.

Check is_list_zero_nil.

(* nat(zero). *)
(* nat(s(X)) :- nat(X). *)

(* list(cons(X,Y)) :- nat(X), list(Y) *)
(* list(nil ).*)
  (* ?- list(cons(zero,nil)). *)

(* Constants *)

Inductive eventType: Type := Obstacle | Fog.

Inductive level: Type := None | Medium | Severe.

Inductive event : eventType -> level -> Prop :=
    | Event_fog_none: forall e l, obstacle 
