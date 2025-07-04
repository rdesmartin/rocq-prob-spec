(*From Corelib Require Import ssreflect ssrfun ssrbool.*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
From mathcomp Require Import ssralg poly ssrnum ssrint interval archimedean finmap.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import sequences derive esum measure exp trigo realfun.
From mathcomp Require Import numfun lebesgue_measure lebesgue_integral kernel.
From mathcomp Require Import lra seq.
Require Import Coq.Lists.List.
From mathcomp Require Import classical_sets reals ereal.
From mathcomp Require Import normedtype real_interval.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Local Open Scope seq_scope.

(*Require Import Ltac2.Ltac2.*)
(*Import numFieldTopology.Exports.*)

(*
Section coin_toss.
Context d d' d'' {A : measurableType d} {C1 : measurableType d'} 
    {C2 : measurableType d''} {R : realType} {P : probability A R}.

(Facts)
Axiom head1 : C1.
Axiom coin1 : {RV P >-> C1}.
Let is_head1 := coin1 @^-1` [set head1].
Axiom prob_head1 : P is_head1 = (3/5)%:E. 

Axiom head2 : C2.
Axiom coin2 : {RV P >-> C2}.
Let is_head2 := coin2 @^-1` [set head2].
Axiom prob_head2 : P is_head2 = (1/2)%:E.

Axiom  independent_coins : 
forall (E1 : set C1) (E2 : set C2) ,
let e1 := coin1 @^-1` E1 in
let e2 := coin2 @^-1` E2 in
P(e1 & e2) = (P e1)*(P e2).

(Rules)
Let head1_and_head2 := is_head1 & is_head2.

(Queries)
Lemma prob_head1_and_head2 : (P head1_and_head2) = (3/10)%:E.
Proof.
rewrite /head1_and_head2 independent_coins prob_head1 prob_head2 -!EFinM.
apply /eqP; rewrite eqe //=; apply /eqP; nra.
Qed.

End coin_toss.
*)

(*
Section coin_toss.
Context d {A : measurableType d} {R : realType} {P : probability A R}.

Inductive Coin : Type := c1 | c2 .

Inductive Heads (c : Coin) : bool -> Prop := 
heads b : Heads c b.

Inductive SomeHeads: Type:= 
| h1_h2  : Heads c1 true -> Heads c2 true -> SomeHeads
| not_h2 : Heads c2 false -> SomeHeads.

Inductive AllSomeHeads: SomeHeads -> SomeHeads -> Prop := 
| ash nh2 h1 h2 : AllSomeHeads (not_h2 nh2) (h1_h2 h1 h2).

Let prob_head_aux (c : Coin) : R :=
    match c with
    | c1 => (6/10)%R
    | c2 => (6/10)%R
    end.

Let prob_head {c} {b} (h : Heads c b) : R :=
    match c , b with
    |  c , true => prob_head_aux c
    |  c , _ => 1 - prob_head_aux c
    end.

Let prob_someheads (sh : SomeHeads) : R :=
    match sh with
    | h1_h2 h1 h2 => prob_head(h1)*prob_head(h2)
    | not_h2 nh2 => prob_head(nh2)
    end.

Let prob_all_someheads {sh1} {sh2} (t : AllSomeHeads sh1 sh2) : R := 
    (prob_someheads sh1) + (prob_someheads sh2).

Goal forall a b (sh : SomeHeads), 
(sh = h1_h2 a b) -> (a = heads c1 true ) /\ (b = heads c2 true).
Proof.
    by [].
Qed.

Goal forall (sh : SomeHeads), 
(exists a b , (sh = h1_h2 a b)) -> (prob_someheads sh) = (36/100)%R.
Proof.
    by move=> sh [h1 [h2]] -> //=; nra.
Qed.

Goal forall (sh : SomeHeads), 
(exists a , (sh = not_h2 a)) -> (prob_someheads sh) = (4/10)%R.
Proof.
    move=> sh [nh1] -> //=. nra.
Qed.

Goal forall sh1 sh2 (ash1 : AllSomeHeads sh1 sh2), 
(exists a b c, sh2 = h1_h2 a b /\ sh1 = not_h2 c) -> prob_all_someheads ash1 = (76/100)%R.
Proof.
    move=> sh1 sh2 + [hc1t [hc2t [hc2f]]] [] => /[swap] -> /[swap] ->.
    move=> [] nh2 h1 h2; rewrite /prob_all_someheads //=. nra. 
Qed.
End coin_toss.
*)

(*
Section coin_toss.
(*Context d {A : measurableType d} {R : realType} {P : probability A R}.*)
Context {R : realType}.

Inductive Coin : Type := c1 | c2.

Inductive Prob (p : R) : Prop := 
    prob : Prob p. 

Inductive IsHeads (c : Coin ): Type := 
| is_heads : bool ->  IsHeads c.

Let pw_heads c := 
    [ :: is_heads c true; is_heads c false].

Inductive Heads {c} (ih : IsHeads c) : Prop :=
| heads : Heads ih.

Inductive SomeHeads: Prop := 
| some_h : Heads (is_heads c2 false) \/ Heads (is_heads c1 true) -> SomeHeads.

Inductive PossibleWorlds: SomeHeads -> SomeHeads -> Prop := 
| posw sh1 sh2 : PossibleWorlds (some_h2 sh1) (some_h2 sh2).

Inductive AllSomeHeads : Type :=
| all_sh {sh1} {sh2} : PossibleWorlds sh1 sh2 -> AllSomeHeads.

Let prob_to_real {r} (p : Prob r) : R := r.

Let prob_head {c} {b} (h : Heads c b) : R :=  
match h with
| heads p => prob_to_real p
end.

Let prob_someheads (sh : SomeHeads) : R := 
    match sh with
    | some_h1 h1 => prob_head h1
    | some_h2 h2 => prob_head h2
    end.

Let prob_all_someheads (ash : AllSomeHeads) : R := 
    match ash with
    all_sh h1 h2 pw => 
        prob_someheads h1 + prob_someheads h2 
        - (prob_someheads h1)*(prob_someheads h2)
    end.

    (*
Goal forall h1 h2, prob_someheads (h1_h2 h1 h2) = (36/100)%R.
Proof.
    move=> [[]] [[]] //=.
    by rewrite /prob_to_real; nra.
Qed.

Goal forall nh2, prob_someheads (not_h2 nh2) = (4/10)%R.
Proof.
    move=> [[]] //=.
    by rewrite /prob_to_real; nra.
Qed.
*)
Goal forall (ash : AllSomeHeads), 
    prob_all_someheads ash = (84/100)%R.
Proof.
    move => [_ _ [[[]] [[]]]] //=.
    rewrite !/prob_to_real. nra.
Qed.

End coin_toss.
*)

Section coin_toss.
Context {R : realType}.

(*
% Probabilistic facts:
0.6 :: publish(cpp); 0.2 :: publish(etaps).

% Background information:
present(C) :- publish(C).

% Rules:
happy :- present(cpp).
happy :- present(etaps).

% Queries:
query(happy).
*)

Inductive Conference := cpp | etaps.

(*
For independent cases:
    Variable P : C -> R -> Prop.
    Axiom p1 : (P c1 (6/10)%R).
*)

Inductive Publish : Conference -> R -> Prop := 
| p1 : Publish cpp (6/10)%R 
| p2 : Publish etaps (2/10)%R. 

Inductive Present : Conference -> R -> Prop := 
| pre : forall {c} {p}, Publish c p -> Present c p.

Inductive Happy : R -> Prop := 
| happy : forall {p1} {p2}, 
            (Present cpp p1) -> (Present etaps p2) -> Happy (p1 + p2).

Goal (Happy (8/10)%R).
Proof.
    rewrite (_ : (8/10)%R = (6/10 + 2/10)%R); last by nra.
    (*repeat econstructor.*)
    apply /happy.
    - apply /pre /p1.
    - apply /pre /p2.
Qed.

End coin_toss.

Section car.
Context {R : realType}.
(*
0.9::start(car,clear); 0.1::start(car,collision).
0.7::trans(car,T,clear,clear); 0.3::trans(car,T,clear,collision).
0.2::trans(car,T,collision,clear); 0.8::trans(car,T,collision,collision).
*)
Inductive CarState : Prop := safe | collision.

Inductive Start : CarState -> R -> Prop := 
| start_s : Start safe (9/10)%R
| start_c : Start collision (1/10)%R.

Inductive Transition : nat -> CarState -> CarState -> R -> Prop := 
| trans_s_s : forall t, Transition t safe safe (7/10)%R
| trans_s_c : forall t, Transition t safe collision (3/10)%R
| trans_c_s : forall t, Transition t collision safe (2/10)%R
| trans_c_c : forall t, Transition t collision collision (8/10)%R.

(*
state(A,0,S) :- start(A,S).
state(A,T,S) :- T > 0, TT is T-1, state(A,TT,clear), trans(A,TT,clear,S).
state(A,T,S) :- T > 0, TT is T-1, state(A,TT,collision), trans(A,TT,collision,S).
*)

Inductive State : nat -> CarState -> R -> Prop :=
| state_0 :  forall {p} cs, Start cs p -> State O cs p
| state_st : forall {p1} {p2} {p3} {p4} (t : nat) cs, 
    State t safe p1 -> Transition t safe cs p2 ->
    State t collision p3 -> Transition t collision cs p4 -> 
    State (S t) cs ((p1 * p2) + (p3 * p4))%R.


(*query(state(car,1,clear)). 0.6931 *)
Lemma is_state_st : forall {p p1 p2 p3 p4: R} t cs, 
        (p = p1 * p2 + p3 * p4)%R -> 
        State t safe p1 -> Transition t safe cs p2 -> State t collision p3 ->
        Transition t collision cs p4 -> State (S t) cs p.
Proof.
    by (do 7 move=> ?)=> ->; apply state_st.
Qed.

Goal (State 1 safe (65/100)%R).
Proof.
    rewrite (_ : 65/100 = (9/10) * (7/10) + (1/10) * (2/10))%R; last by nra.
    apply /state_st.
    - apply /state_0 /start_s.
    - apply /trans_s_s.
    - apply /state_0 /start_c.
    - apply /trans_c_s.
Qed.

Goal (State 0 safe (9/10)%R).
Proof.
    by econstructor; apply /start_s.
Qed.

Goal (State 7 safe (517/1280)%R).
Proof.
    apply /is_state_st; repeat econstructor; nra.
Qed.

End car.