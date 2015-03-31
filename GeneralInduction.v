Require Import seq ssreflect ssrnat ssrbool eqtype.

Definition edges := seq (nat * nat).

Inductive orSet A B : Type :=
  | left  : A -> orSet A B 
  | right : B -> orSet A B.

Theorem boolOrSet x y : x || y -> orSet x y.
Proof.
case x; case y=> _ //.
- by left.
- by left.
by right.
Qed.

Theorem natEq (x y : nat): (x == y) -> x = y.
Proof.
move: y.
elim x; first case =>//.
move=> n H.
case=>// => y'.
rewrite eqSS => H'.
by apply: eq_S; apply: H.
Qed.

Definition eqtypeEq (T : eqType) := forall (x : T) (y : T), x == y -> x = y.

Theorem pairEq {T1 : eqType} {T2 : eqType} (p1 : T1 * T2) (p2 : T1 * T2) :
  eqtypeEq T1 -> eqtypeEq T2 -> p1 == p2 -> p1 = p2.
Proof.
move=> EQ1 EQ2.
move: p1 p2.
case=> a1 b1.
case=> a2 b2.
unfold eq_op=> /=.
move/andb_prop; case.
move/EQ1->.
by move/EQ2->.
Qed.

Theorem seqEq {T : eqType} (l1 : seq T) (l2 : seq T) : eqtypeEq T -> l1 == l2 -> l1 = l2.
Proof.
move => EQ.
move: l1 l2.
elim; first case =>//.
move=> a l1 H.
case=>// => b l2 /=.
unfold eq_op=> /=.
move/andb_prop; case.
move/EQ->.
by move/(H l2)->.
Qed. 

Theorem edgesEq (l1 : edges) (l2 : edges) : l1 == l2 -> l1 = l2.
Proof.
apply: seqEq.
unfold eqtypeEq.
unfold prod_eqType=> /=.
move=> x y.
apply: pairEq; unfold eqtypeEq=> /=; apply: natEq.
Qed.

Lemma leNLeN1 : forall (n : nat) (x : nat * nat),
   (fst x <= n) && (snd x <= n) -> (fst x <= n.+1) && (snd x <= n.+1).
Proof.
move=> n.
case=> a b /= H.
rewrite leqW=> //=.
- rewrite leqW=> //=.
  move: H; case (b <= n); case (a <= n)=> //=.
move: H; case (b <= n); case (a <= n)=> //=.
Qed.

Lemma allLeNLeN1 : forall (n : nat) (l : edges),
  all (fun x => (fst x <= n) && (snd x <= n)) l ->
  all (fun x => (fst x <= n.+1) && (snd x <= n.+1)) l.
Proof.
move=> n l H.
apply (fun x => @sub_all _ _ _ x _ H).
unfold subpred.
apply leNLeN1.
Qed.

Theorem allToPerm {T : eqType} {x : seq T} {y : seq T} {f} :
  perm_eq x y -> all f x -> all f y.
Proof.
admit.
Qed.

(* Generalized nat induction *)

Theorem genInd_nat' (P : nat -> Prop) :
  (forall n, (forall k, k < n -> P k) -> (forall k, k < n.+1 -> P k)) ->
  forall m n, n < m -> P n.
Proof.
move=> Ind m; move: Ind.
elim: m.
- move=> Ind.
  move: (Ind 0)=> H.
  move=> n.
  by move: (ltn0 n).
move=> m H1 H2.
apply H2.
apply H1.  
apply H2.
Qed.

Theorem genInd_nat (P : nat -> Prop) :
  (forall n, (forall k, k < n -> P k) -> P n) -> forall n, P n.
Proof.
move=> H1 n.
apply: genInd_nat'; last eapply ltnSn.
clear n.
move=> n H2 k.
rewrite (ltnS k n).
rewrite (leq_eqVlt k n). 
move/Bool.orb_prop; case => H3.
- apply: H1.
  by rewrite (natEq k n H3).
apply: (H2 k H3).
Qed.

Theorem genInd_nat_set' (P : nat -> Set) :
  (forall n, (forall k, k < n -> P k) -> (forall k, k < n.+1 -> P k)) ->
  forall m n, n < m -> P n.
Proof.
move=> Ind m; move: Ind.
elim: m.
- move=> Ind.
  move: (Ind 0)=> H.
  move=> n.
  by move: (ltn0 n).
move=> m H1 H2.
apply H2.
apply H1.  
apply H2.
Qed.

Theorem genInd_nat_set (P : nat -> Set) :
  (forall n, (forall k, k < n -> P k) -> P n) -> forall n, P n.
Proof.
move=> H1 n.
apply: genInd_nat_set'; last eapply ltnSn.
clear n.
move=> n H2 k.
rewrite (ltnS k n).
rewrite (leq_eqVlt k n). 
move/boolOrSet.
case => H3.
- apply: H1.
  by rewrite (natEq k n H3).
apply: (H2 k H3).
Qed.

