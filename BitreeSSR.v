Require Import ssreflect ssrnat ssrbool eqtype.

Inductive tree : Set :=
  leaf : tree
| node : forall (n : nat) (left right : tree), tree.

Fixpoint lt_tree (n : nat) (t : tree) : bool :=
  match t with
  | leaf => true
  | node x l r => (n > x) && lt_tree n l && lt_tree n r
  end.

Fixpoint gt_tree (n : nat) (t : tree) : bool :=
  match t with
  | leaf => true
  | node x l r => (n < x) && gt_tree n l && gt_tree n r
  end.

Fixpoint is_search_tree (t : tree) : bool :=
  match t with
  | leaf       => true
  | node x l r => lt_tree x l && is_search_tree l && gt_tree x r && is_search_tree r
  end.

Fixpoint contains (n : nat) (t : tree) : bool :=
  match t with
  | leaf => false
  | node x l r => (x == n) || contains n l || contains n r
  end.

Fixpoint height (t: tree) : nat := 
  match t with
  | leaf => 0
  | node _ l r => 1 + max (height l) (height r)
  end.

Require Import GeneralInduction.

Lemma containsInGT n t : gt_tree n t -> forall x, contains x t -> n < x.
Proof.
move: t n.
elim=> //.
move=> n l Hl r Hr m /=.
move/andb_prop; case; move/andb_prop; case.
move=> H1 H2 H3 x.
move/Bool.orb_prop; case.
- move/Bool.orb_prop; case.
  - by move/natEq<-.
  apply (Hl m H2).        
apply (Hr m H3).
Qed. 

Lemma containsSmall n t : (forall x, contains x t -> n < x) -> gt_tree n t.
Proof.
move: t n.
elim=> //.
move=> n l Hl r Hr m H1 /=.
assert (contains n (node n l r)) as X => /=.
- by rewrite eq_refl.
move: (H1 n X)=>->/=.
apply andb_true_intro; split.
- apply Hl=> p H2.
  apply H1=> /=.  
  rewrite H2.
  by rewrite Bool.orb_true_r.
apply Hr=> p H2.
apply H1=> /=.  
rewrite H2.
by rewrite Bool.orb_true_r.
Qed.

Lemma containsInLT n t : lt_tree n t -> forall x, contains x t -> n > x.
Proof.
move: t n.
elim=> //.
move=> n l Hl r Hr m /=.
move/andb_prop; case; move/andb_prop; case.
move=> H1 H2 H3 x.
move/Bool.orb_prop; case.
- move/Bool.orb_prop; case.
  - by move/natEq<-.
  apply (Hl m H2).        
apply (Hr m H3).
Qed. 

Lemma containsBig n t : (forall x, contains x t -> n > x) -> lt_tree n t.
Proof.
move: t n.
elim=> //.
move=> n l Hl r Hr m H1 /=.
assert (contains n (node n l r)) as X => /=.
- by rewrite eq_refl.
move: (H1 n X)=>->/=.
apply andb_true_intro; split.
- apply Hl=> p H2.
  apply H1=> /=.  
  rewrite H2.
  by rewrite Bool.orb_true_r.
apply Hr=> p H2.
apply H1=> /=.  
rewrite H2.
by rewrite Bool.orb_true_r.
Qed.

Definition contains_all n t t' :=
        contains n t' /\ (forall m, contains m t -> contains m t')
                      /\ (forall m, contains m t' -> (m == n) || contains m t).

Definition add_in_search_tree (t : tree) (n : nat) :
  is_search_tree t -> 
  { t' | is_search_tree t' & contains_all n t t' }.
Proof.
unfold contains_all.
elim t.
- move=> _.
  exists (node n leaf leaf)=> //.
  split=> //=.
  by rewrite eq_refl.
  split=>// m. 
  repeat (rewrite Bool.orb_false_r).
  by rewrite (@eq_sym _ n m).
move=> x l HL r HR Hs.
case H: (x == n).
- exists (node x l r)=> //=.
  rewrite H=> /=.
  split=> //. 
  split=> m.       
  - case ((x == m) || (contains m l) || (contains m r))=> //.
  case ((x == m) || (contains m l) || (contains m r))=> // _.
  by rewrite Bool.orb_true_r.
move: (Hs) => /=.
case isLT_L: (lt_tree x l)=> //=.
case isS_L: (is_search_tree l)=> //=.
case isGT_R: (gt_tree x r)=> //=.
case isS_R: (is_search_tree r)=> //= _.
move: (HL isS_L); clear HL=> HL.
move: (HR isS_R); clear HR=> HR.
move: (neq_ltn x n).
unfold negb.
rewrite H.
case H1: (x < n)=> /=.
- case: HR=> nr isS_NR.
  case=> NRcN NRcAll _.
  exists (node x l nr)=> /=.
  - rewrite isLT_L isS_L isS_NR=> /=.
    rewrite Bool.andb_true_r.
    apply containsSmall.
    move=> m.
    move/(proj2 NRcAll).
    case X: (m == n)=> /=.
    - move=> _.
      apply natEq in X. 
      by rewrite X.
    by apply containsInGT.
  - split. 
    - rewrite NRcN.
      by repeat (rewrite Bool.orb_true_r).
    split=> m; case ((x == m) || contains m l)=> //=.
    - apply (proj1 NRcAll).
    by rewrite Bool.orb_true_r.     
  apply (proj2 NRcAll).
move=> H2.
case: HL=> nl isS_NL.
case=> NLcN NLcAll.
exists (node x nl r)=> /=.
- rewrite isS_NL isGT_R isS_R=> /=. 
  repeat rewrite Bool.andb_true_r.
  apply containsBig.  
  move=> m.
  move/(proj2 NLcAll).
  case X: (m == n)=> /=.
  - move=> _.
    apply natEq in X.
    by rewrite X.
  apply containsInLT.
split.
- rewrite NLcN.
  by repeat (rewrite Bool.orb_true_r).
split=> m; case (x == m)=> //=; case (contains m r);
           repeat try (rewrite Bool.orb_true_r); try done.
- repeat (rewrite Bool.orb_false_r).
  apply (proj1 NLcAll).
repeat (rewrite Bool.orb_false_r).
apply (proj2 NLcAll).
Defined.

Extraction "insert.ml" add_in_search_tree.


