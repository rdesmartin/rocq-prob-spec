(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval archimedean finmap.
(*From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.*)
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
(*From mathcomp Require Import reals interval_inference ereal topology normedtype.*)
From mathcomp Require Import sequences derive esum measure exp trigo realfun.
From mathcomp Require Import numfun lebesgue_measure lebesgue_integral kernel.
(*From mathcomp Require Import ftc gauss_integral hoelder probability charge.*)
From mathcomp Require Import lra seq.
Require Import Coq.Lists.List.

From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
(*From mathcomp Require Import mathcomp_extra unstable boolp interval_inference.*)
From mathcomp Require Import classical_sets functions cardinality fsbigop reals.
From mathcomp Require Import ereal topology normedtype sequences real_interval.
(*From mathcomp Require Import esum measure ess_sup_inf lebesgue_measure.*)
From mathcomp Require Import lebesgue_integral numfun exp convex.


Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

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

Section coin_toss.
(*Context d {A : measurableType d} {R : realType} {P : probability A R}.*)
Context {R : realType}.

Inductive Coin : Type := c1 | c2.

Inductive Prob (p : R) : Prop := 
    prob : Prob p. 

Let _prob_head (c : Coin) : R :=
    match c with
    | c1 => (6/10)%R
    | c2 => (6/10)%R
    end.

Let _prob_headb c b : R :=
    match c , b with
    |  c , true => _prob_head c
    |  c , _ => 1 - _prob_head c
    end.

Inductive Heads (c : Coin) (b : bool) : Prop := 
| heads : Prob (_prob_headb c b) -> Heads c b.

Inductive SomeHeads: Type:= 
| h1_h2  : Heads c1 true -> Heads c2 true -> SomeHeads
| not_h2 : Heads c2 false -> SomeHeads.

Inductive PossibleWorlds: SomeHeads -> SomeHeads -> Prop := 
| ash nh2 h1 h2 : PossibleWorlds (not_h2 nh2) (h1_h2 h1 h2).

Inductive AllSomeHeads : Type :=
| all_sh {h1} {h2} : PossibleWorlds h1 h2 -> AllSomeHeads.

Let prob_to_real {r} (p : Prob r) : R := r.

Let prob_head {c} {b} (h : Heads c b) : R :=  
match h with
| heads p => prob_to_real p
end.

Let prob_someheads (sh : SomeHeads) : R := 
    match sh with
    | h1_h2 h1 h2 => prob_head h1 * prob_head h2
    | not_h2 nh2 => prob_head nh2
    end.

Let prob_all_someheads (ash : AllSomeHeads) : R := 
    match ash with
    all_sh h1 h2 pw => prob_someheads h1 + prob_someheads h2
    end.

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

Goal forall (ash : AllSomeHeads), 
    prob_all_someheads ash = (76/100)%R.
Proof.
    move=> //= [h1 h2 [[[]] [[]] [[]]]] //=.
    rewrite !/prob_to_real. nra.
Qed.

End coin_toss.