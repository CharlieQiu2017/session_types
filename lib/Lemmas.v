From Stdlib Require Import
  List
  Strings.String
  Sorting.Permutation.
Import
  ListNotations.

Lemma str_eq_dec : forall (s1 s2 : string), {s1 = s2} + {s1 <> s2}.
Proof.
  intros s1 s2.
  destruct (eqb_spec s1 s2); [left | right]; auto.
Qed.

Lemma NoDup_cons_inv : forall {T : Type} (x : T) l, NoDup (x :: l) -> NoDup l.
Proof.
  intros T x l Hnodup.
  rewrite NoDup_cons_iff in Hnodup.
  apply Hnodup.
Qed.

Lemma negb_eqb_true_iff : forall s t, negb (eqb s t) = true <-> s <> t.
Proof.
  intros s t.
  rewrite Bool.negb_true_iff.
  rewrite eqb_neq.
  split; auto.
Qed.

Lemma list_nin_helper : forall {T : Type} (x y : T) l, ~ In x l -> ~ ((x = y \/ In y l) /\ x <> y) -> ~ In y l.
Proof.
  intros T x y l Hnin1 Hnin2.
  intros Hin; apply Hnin2.
  split; auto.
  intros Heq; subst y.
  tauto.
Qed.

Lemma in_split_perm : forall {T : Type} (x : T) l, In x l -> exists l', Permutation l (x :: l').
Proof.
  intros T x l Hin.
  apply in_split in Hin.
  destruct Hin as (l1 & l2 & Hl).
  subst l.
  exists (l1 ++ l2).
  apply Permutation_sym; apply Permutation_middle.
Qed.

Lemma NoDup_disjoint {T : Type} : forall (l1 l2 : list T), NoDup (l1 ++ l2) -> forall x, In x l1 -> ~ In x l2.
Proof.
  intros l1.
  induction l1.
  - cbn; contradiction.
  - cbn.
    intros l2 Hnodup.
    inversion Hnodup.
    subst x l.
    intros x Hx.
    destruct Hx as [Hx | Hx].
    1: subst x; rewrite in_app_iff in H1; tauto.
    apply IHl1; auto.
Qed.

Lemma combine_map_fst :
  forall {T U : Type} (l : list T) (l' : list U), 
  List.length l = List.length l' ->
  map fst (combine l l') = l.
Proof.
  intros T U l.
  induction l.
  - cbn; auto.
  - cbn.
    intros l' Hl'.
    destruct l'.
    + cbn in Hl'; discriminate.
    + cbn in Hl'; injection Hl'.
      intros Heq.
      specialize (IHl _ Heq).
      cbn; rewrite IHl; auto.
Qed.

Lemma combine_map_snd :
  forall {T U : Type} (l : list T) (l' : list U), 
  List.length l = List.length l' ->
  map snd (combine l l') = l'.
Proof.
  intros T U l.
  induction l.
  - cbn.
    intros l'; destruct l'; cbn; try discriminate; auto.
  - cbn.
    intros l' Hl'.
    destruct l'.
    + cbn in Hl'; discriminate.
    + cbn in Hl'; injection Hl'.
      intros Heq.
      specialize (IHl _ Heq).
      cbn; rewrite IHl; auto.
Qed.

Lemma combine_map :
  forall {T U T' U' : Type} f (g1 : T -> T') (g2 : U -> U') (l1 : list T) (l2 : list U),
  (forall z, fst (f z) = g1 (fst z)) ->
  (forall z, snd (f z) = g2 (snd z)) ->
  map f (combine l1 l2) = combine (map g1 l1) (map g2 l2).
Proof.
  intros T U T' U' f g1 g2 l1 l2 Hg1 Hg2.
  revert l2.
  induction l1.
  - cbn; auto.
  - intros l2; cbn.
    destruct l2; cbn; auto.
    specialize (IHl1 l2).
    specialize (Hg1 (a, u)).
    specialize (Hg2 (a, u)).
    cbn in Hg1, Hg2.
    destruct (f (a, u)) eqn:Ef.
    cbn in Hg1, Hg2.
    subst t u0.
    rewrite IHl1; auto.
Qed.
