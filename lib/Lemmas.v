From Stdlib Require Import
  List
  Strings.String
  Sorting.Permutation
  Setoid
  Morphisms.
Import
  ListNotations.
Open Scope bool_scope.

Lemma false_true_False : false = true <-> False.
Proof. split; auto; discriminate. Qed.

Lemma true_false_False : true = false <-> False.
Proof. split; [discriminate | contradiction]. Qed.

Lemma str_eq_dec : forall (s1 s2 : string), {s1 = s2} + {s1 <> s2}.
Proof.
  intros s1 s2.
  destruct (s1 =? s2)%string eqn:Es.
  - left; destruct (eqb_spec s1 s2); try discriminate; auto.
  - right; destruct (eqb_spec s1 s2); try discriminate; auto.
Defined.

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
  tauto.
Qed.

Lemma in_dec_true_iff : forall {T : Type} {eq_dec : forall (x y : T), {x = y} + {x <> y}} x l, (if in_dec eq_dec x l then true else false) = true <-> In x l.
Proof.
  intros T eq_dec x l.
  destruct (in_dec eq_dec x l); split; try discriminate; tauto.
Qed.

Lemma neg_in_dec_true_iff : forall {T : Type} {eq_dec : forall (x y : T), {x = y} + {x <> y}} x l, (if in_dec eq_dec x l then false else true) = true <-> ~ In x l.
Proof.
  intros T eq_dec x l.
  destruct (in_dec eq_dec x l); split; try discriminate; tauto.
Qed.

Lemma negb_in_dec_true_iff : forall {T : Type} {eq_dec : forall (x y : T), {x = y} + {x <> y}} x l, negb (if in_dec eq_dec x l then true else false) = true <-> ~ In x l.
Proof.
  intros T eq_dec x l.
  destruct (in_dec eq_dec x l); split; try discriminate; auto.
Qed.

Lemma in_dec_false_iff : forall {T : Type} {eq_dec : forall (x y : T), {x = y} + {x <> y}} x l, (if in_dec eq_dec x l then true else false) = false <-> ~ In x l.
Proof.
  intros T eq_dec x l.
  rewrite <- Bool.negb_true_iff.
  apply negb_in_dec_true_iff.
Qed.

Lemma negb_neg_in_dec_true_iff : forall {T : Type} {eq_dec : forall (x y : T), {x = y} + {x <> y}} x l, negb (if in_dec eq_dec x l then false else true) = true <-> In x l.
Proof.
  intros T eq_dec x l.
  destruct (in_dec eq_dec x l); split; try discriminate; auto.
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

Lemma in_dup : forall {T : Type} (x : T) l, In x (l ++ l) <-> In x l.
Proof.
  intros T x l.
  rewrite in_app_iff.
  tauto.
Qed.

Hint Resolve <- in_dup : core.

Lemma NoDup_disjoint {T : Type} : forall (l1 l2 : list T) (x : T), NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros l1 l2 x; revert l2.
  induction l1.
  - cbn; contradiction.
  - cbn.
    intros l2 Hnodup.
    rewrite NoDup_cons_iff in Hnodup.
    destruct Hnodup as (Hnodup1 & Hnodup2).
    intros Hx.
    destruct Hx as [Hx | Hx].
    1: subst x; rewrite in_app_iff in Hnodup1; tauto.
    apply IHl1; auto.
Qed.

Lemma NoDup_disjoint' {T : Type} : forall (l1 l2 : list T) (x : T), NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
  intros l1 l2 x.
  rewrite Permutation_app_comm.
  apply NoDup_disjoint.
Qed.

Lemma nin_map_nin {T U : Type} {f : T -> U} x l : ~ In (f x) (map f l) -> ~ In x l.
Proof.
  intros Hnin Hin.
  apply Hnin; apply in_map; auto.
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

Lemma combine_fst_snd :
  forall {T U : Type} (l : list (T * U)),
  l = combine (map fst l) (map snd l).
Proof.
  intros T U l.
  induction l.
  - cbn; auto.
  - cbn; rewrite <- IHl.
    destruct a; auto.
Qed.

Lemma filter_filter {T : Type} :
forall (f g : T -> bool) l, filter f (filter g l) = filter (fun x => f x && g x) l.
Proof.
  intros f g l.
  induction l.
  - cbn; auto.
  - cbn; destruct (g a).
    + rewrite Bool.andb_true_r; cbn.
      rewrite IHl; auto.
    + rewrite Bool.andb_false_r; auto.
Qed.

Lemma map_filter_nodup {T U : Type} :
forall (f : T -> U) g (l : list T), NoDup (map f l) -> NoDup (map f (filter g l)).
Proof.
  intros f g l.
  induction l.
  - cbn; auto.
  - cbn.
    intros Hnodup.
    inversion Hnodup as [|? ? Hnodup1 Hnodup2]; subst.
    destruct (g a); [|auto].
    cbn; constructor; auto.
    intros Hin.
    apply Hnodup1.
    rewrite in_map_iff; rewrite in_map_iff in Hin.
    destruct Hin as (x & Hx1 & Hx2).
    rewrite filter_In in Hx2.
    exists x; split; tauto.
Qed.

Hint Resolve map_filter_nodup : core.

#[export] Instance filter_proper {T : Type} : Proper (Logic.eq ==> @Permutation T ==> @Permutation T) (fun f l => filter f l).
Proof.
  unfold Proper.
  intros f f' Heq; subst f'.
  intros l l' Hperm.
  induction Hperm; cbn; repeat match goal with |- context[if ?p then _ else _] => destruct p end; auto.
  - apply perm_swap.
  - rewrite IHHperm1; auto.
Qed.

Lemma NoDup_filter_one {T : Type} {eqb : T -> T -> bool} (eqb_spec : forall x y, reflect (x = y) (eqb x y)) : forall x l, NoDup (x :: l) -> filter (fun s => negb (eqb x s)) (x :: l) = l.
Proof.
  intros x l Hnodup.
  rewrite NoDup_cons_iff in Hnodup.
  cbn.
  destruct (eqb_spec x x); try contradiction; cbn.
  apply forallb_filter_id.
  rewrite forallb_forall; intros z Hz.
  destruct (eqb_spec x z); auto; subst z; tauto.
Qed.

Lemma NoDup_filter_two {T : Type} {eqb : T -> T -> bool} (eqb_spec : forall x y, reflect (x = y) (eqb x y)) : forall x y l, NoDup (x :: y :: l) -> filter (fun s => negb (eqb x s) && negb (eqb y s)) (x :: y :: l) = l.
Proof.
  intros x y l Hnodup.
  do 2 rewrite NoDup_cons_iff in Hnodup.
  cbn in Hnodup.
  cbn.
  destruct (eqb_spec x x); try contradiction; cbn.
  destruct (eqb_spec y y); try contradiction; cbn.
  rewrite Bool.andb_false_r.
  apply forallb_filter_id.
  rewrite forallb_forall; intros z Hz.
  destruct (eqb_spec x z); cbn.
  1: subst z; tauto.
  destruct (eqb_spec y z); cbn.
  1: subst z; tauto.
  auto.
Qed.

Lemma forallb_filter_nil {T : Type} : forall f (l : list T), forallb (fun x => negb (f x)) l = true -> filter f l = [].
Proof.
  intros f l.
  induction l.
  - cbn; auto.
  - cbn; intros Htrue.
    rewrite Bool.andb_true_iff in Htrue.
    destruct Htrue as (Htrue1 & Htrue2).
    rewrite Bool.negb_true_iff in Htrue1.
    specialize (IHl Htrue2).
    rewrite Htrue1; auto.
Qed.

Lemma NoDup_filter_app {T : Type} (eq_dec : forall x y, {x = y} + {x <> y}) : forall (l1 l2 : list T), NoDup (l1 ++ l2) -> filter (fun s => if in_dec eq_dec s l1 then false else true) (l1 ++ l2) = l2.
Proof.
  intros l1 l2 Hnodup.
  rewrite filter_app.
  rewrite forallb_filter_nil.
  2: rewrite forallb_forall; intros z Hz; rewrite negb_neg_in_dec_true_iff; auto.
  cbn; apply forallb_filter_id.
  rewrite forallb_forall.
  intros z Hz.
  rewrite neg_in_dec_true_iff.
  eapply NoDup_disjoint'; [apply Hnodup | auto].
Qed.

Lemma NoDup_filter_app' {T : Type} (eq_dec : forall x y, {x = y} + {x <> y}) : forall (l1 l2 : list T), NoDup (l1 ++ l2) -> filter (fun s => if in_dec eq_dec s l2 then false else true) (l1 ++ l2) = l1.
Proof.
  intros l1 l2 Hnodup.
  rewrite filter_app.
  rewrite (forallb_filter_nil _ l2).
  2: rewrite forallb_forall; intros z Hz; rewrite negb_neg_in_dec_true_iff; auto.
  rewrite app_nil_r.
  cbn; apply forallb_filter_id.
  rewrite forallb_forall.
  intros z Hz.
  rewrite neg_in_dec_true_iff.
  eapply NoDup_disjoint; [apply Hnodup | auto].
Qed.

Lemma filter_split {T : Type} (f : T -> bool) l : Permutation l ((filter f l) ++ (filter (fun x => negb (f x)) l)).
Proof.
  induction l.
  - cbn; auto.
  - cbn.
    destruct (f a).
    + cbn; auto.
    + cbn; rewrite <- Permutation_middle; auto.
Qed.

Lemma map_permutation_ex {T U : Type} (f : T -> U) L l : Permutation (map f L) l -> exists L', Permutation L L' /\ l = map f L'.
Proof.
  intros Hperm.
  remember (map f L) as l'.
  revert L Heql'.
  induction Hperm as [ | x l l' | x y l | l l'].
  - intros L HL; symmetry in HL.
    apply map_eq_nil in HL; subst L.
    exists []; split; auto.
  - intros L HL.
    destruct L; cbn in HL; try discriminate.
    injection HL; intros; subst l x; clear HL.
    specialize (IHHperm _ ltac:(reflexivity)).
    destruct IHHperm as (L' & HL'1 & HL'2); subst l'; clear Hperm.
    exists (t :: L'); split; auto.
  - intros L HL.
    do 2 (destruct L; cbn in HL; try discriminate).
    injection HL; intros; subst.
    exists (t0 :: t :: L).
    split; auto; apply perm_swap.
  - intros L HL; subst l.
    specialize (IHHperm1 _ ltac:(reflexivity)).
    destruct IHHperm1 as (L' & HL'1 & HL'2); subst l'.
    specialize (IHHperm2 _ ltac:(reflexivity)).
    destruct IHHperm2 as (L'' & HL''1 & HL''2); subst l''.
    exists L''; split; auto.
    rewrite HL'1; auto.
Qed.

Lemma in_app_app_iff {T : Type} (l1 l2 l3 : list T) : forall x, In x ((l1 ++ l2) ++ (l1 ++ l3)) <-> In x (l1 ++ l2 ++ l3).
Proof.
  intros x.
  rewrite <- app_assoc.
  rewrite (app_assoc l2).
  rewrite (Permutation_app_comm l2).
  rewrite <- (app_assoc l1).
  rewrite app_assoc.
  rewrite in_app_iff.
  rewrite in_dup.
  rewrite <- in_app_iff.
  tauto.
Qed.
