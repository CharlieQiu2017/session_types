(* Implementation of session types as in Wadler 2012 *)
(* We want to understand what is exactly wrong with this theory, and why extensions like HCP are necessary *)

From Stdlib Require Import
  List
  Structures.Equalities
  Sorting.Permutation
  Setoid
  Morphisms.
From Session.lib Require Import
  Lemmas.
Import
  ListNotations.
Open Scope bool_scope.

Module Type Wadler_Types (PropVarName : UsualDecidableType).

  #[local] Notation pvn := PropVarName.t.

  Definition pvn_eqb := fun x y => if PropVarName.eq_dec x y then true else false.
  Definition pvn_eq_dec := PropVarName.eq_dec.
  Definition pvn_eqb_spec x y : reflect (x = y) (pvn_eqb x y).
  Proof. unfold pvn_eqb; destruct (PropVarName.eq_dec x y); constructor; auto. Qed.
  Lemma pvn_eqb_refl : forall x, pvn_eqb x x = true.
  Proof. intros x; destruct (pvn_eqb_spec x x); auto; try contradiction. Qed.

  #[local] Notation eqb := pvn_eqb.
  #[local] Notation eq_dec := pvn_eq_dec.
  #[local] Notation eqb_spec := pvn_eqb_spec.
  #[local] Notation eqb_refl := pvn_eqb_refl.

  (* Session Types *)
  Inductive STyp :=
  | STyp_Var (x : pvn)
  | STyp_VarDual (x : pvn)
  | STyp_Const (x : pvn)
  | STyp_ConstDual (x : pvn)
  | STyp_Times (t1 t2 : STyp)
  | STyp_Par (t1 t2 : STyp)
  | STyp_Plus (t1 t2 : STyp)
  | STyp_With (t1 t2 : STyp)
  | STyp_Excl (t : STyp)
  | STyp_Ques (t : STyp)
  | STyp_Exists (v : pvn) (t : STyp)
  | STyp_Forall (v : pvn) (t : STyp)
  | STyp_One
  | STyp_Bot
  | STyp_Zero
  | STyp_Top.

  (* Dual of type *)
  Fixpoint dual (t : STyp) :=
  match t with
  | STyp_Var x => STyp_VarDual x
  | STyp_VarDual x => STyp_Var x
  | STyp_Const x => STyp_ConstDual x
  | STyp_ConstDual x => STyp_Const x
  | STyp_Times t1 t2 => STyp_Par (dual t1) (dual t2)
  | STyp_Par t1 t2 => STyp_Times (dual t1) (dual t2)
  | STyp_Plus t1 t2 => STyp_With (dual t1) (dual t2)
  | STyp_With t1 t2 => STyp_Plus (dual t1) (dual t2)
  | STyp_Excl t => STyp_Ques (dual t)
  | STyp_Ques t => STyp_Excl (dual t)
  | STyp_Exists v t => STyp_Forall v (dual t)
  | STyp_Forall v t => STyp_Exists v (dual t)
  | STyp_One => STyp_Bot
  | STyp_Bot => STyp_One
  | STyp_Zero => STyp_Top
  | STyp_Top => STyp_Zero
  end.

  (* Dual is involutive *)
  Lemma dual_involute : forall t, dual (dual t) = t.
  Proof.
    induction t.
    all: cbn; auto; congruence.
  Qed.

  Hint Rewrite dual_involute : styp_simpl.

  (* Substitution *)
  Fixpoint styp_subst (x' : pvn) (t : STyp) (t' : STyp) :=
  match t with
  | STyp_Var x => if eqb x x' then t' else STyp_Var x
  | STyp_VarDual x => if eqb x x' then dual t' else STyp_VarDual x
  | STyp_Const x => STyp_Const x
  | STyp_ConstDual x => STyp_ConstDual x
  | STyp_Times t1 t2 => STyp_Times (styp_subst x' t1 t') (styp_subst x' t2 t')
  | STyp_Par t1 t2 => STyp_Par (styp_subst x' t1 t') (styp_subst x' t2 t')
  | STyp_Plus t1 t2 => STyp_Plus (styp_subst x' t1 t') (styp_subst x' t2 t')
  | STyp_With t1 t2 => STyp_With (styp_subst x' t1 t') (styp_subst x' t2 t')
  | STyp_Excl t => STyp_Excl (styp_subst x' t t')
  | STyp_Ques t => STyp_Ques (styp_subst x' t t')
  | STyp_Exists v t => if eqb v x' then STyp_Exists v t else STyp_Exists v (styp_subst x' t t')
  | STyp_Forall v t => if eqb v x' then STyp_Forall v t else STyp_Forall v (styp_subst x' t t')
  | STyp_One => STyp_One
  | STyp_Bot => STyp_Bot
  | STyp_Zero => STyp_Zero
  | STyp_Top => STyp_Top
  end.

  (* Substitution preserves duality *)
  Lemma styp_subst_dual :
  forall x' t t',
  dual (styp_subst x' t t') = styp_subst x' (dual t) t'.
  Proof.
    intros x' t.
    induction t.
    all: cbn; auto; try congruence.
    all: intros t'.
    1,2: destruct (eqb x x'); auto; apply dual_involute.
    all: destruct (eqb v x'); auto; cbn; rewrite IHt; auto.
  Qed.

  Hint Rewrite styp_subst_dual : styp_simpl.

  (* Compute the list of free variables in a type *)
  (* bvar is the list of variables that are already bound *)
  (* Initially, we set bvar = [], and add variables to it as we recurse deeper into the expression *)
  Fixpoint fvar' (t : STyp) (bvar : list pvn) :=
  match t with
  | STyp_Var x => if in_dec eq_dec x bvar then [] else [x]
  | STyp_VarDual x => if in_dec eq_dec x bvar then [] else [x]
  | STyp_Const x => []
  | STyp_ConstDual x => []
  | STyp_Times t1 t2 => (fvar' t1 bvar) ++ (fvar' t2 bvar)
  | STyp_Par t1 t2 => (fvar' t1 bvar) ++ (fvar' t2 bvar)
  | STyp_Plus t1 t2 => (fvar' t1 bvar) ++ (fvar' t2 bvar)
  | STyp_With t1 t2 => (fvar' t1 bvar) ++ (fvar' t2 bvar)
  | STyp_Excl t => fvar' t bvar
  | STyp_Ques t => fvar' t bvar
  | STyp_Exists v t => fvar' t (v :: bvar)
  | STyp_Forall v t => fvar' t (v :: bvar)
  | STyp_One => []
  | STyp_Bot => []
  | STyp_Zero => []
  | STyp_Top => []
  end.

  (* fvar' t l is simply fvar' t [] with variables in l removed *)
  Lemma fvar'_prop :
  forall t l,
  fvar' t l = filter (fun x => if in_dec eq_dec x l then false else true) (fvar' t []).
  Proof.
    intros t.
    induction t; auto; intros l; cbn.
    1,2 : destruct (in_dec eq_dec x l); auto.
    1,2,3,4 : specialize (IHt1 l); specialize (IHt2 l); rewrite IHt1, IHt2; rewrite filter_app; auto.
    all: specialize (IHt (v :: l)) as IHt1; specialize (IHt [v]) as IHt2; rewrite IHt1, IHt2; rewrite filter_filter.
    all: apply filter_ext; intros z; destruct (in_dec eq_dec z (v :: l)); destruct (in_dec eq_dec z l); destruct (in_dec eq_dec z [v]); cbn [In] in *.
    all: tauto.
  Qed.

  Lemma var_free_dual : forall t l, fvar' (dual t) l = fvar' t l.
  Proof.
    intros t; induction t; cbn; auto.
    all: intros l; specialize (IHt1 l); specialize (IHt2 l); congruence.
  Qed.

  Hint Rewrite var_free_dual : styp_simpl.

  Definition fvar (t : STyp) := fvar' t [].

  Lemma var_free_subst :
  forall v v' t t',
  In v' (fvar (styp_subst v t t')) ->
  In v' (fvar t) /\ v <> v' \/ In v' (fvar t').
  Proof.
    intros v v' t t'.
    induction t.

    3,4,5,6,7,8,9,10,13,14,15,16: cbn; repeat rewrite in_app_iff; tauto.

    1,2: cbn; destruct (eqb_spec x v).
    1,3: subst v; autorewrite with styp_simpl; auto.
    1,2: cbn; intros Hin; replace v' with x by tauto; auto.

    1,2: cbn; destruct (eqb_spec v0 v).
    1,3: subst v; cbn;
         rewrite (fvar'_prop t [v0]); rewrite filter_In, neg_in_dec_true_iff; cbn; tauto.
    1,2: cbn; rewrite (fvar'_prop (styp_subst v t t') [v0]); rewrite (fvar'_prop t [v0]);
         do 2 rewrite filter_In, neg_in_dec_true_iff; cbn; tauto.
  Qed.

  (* If a variable does not appear free in a type, then substituion has no effect *)
  Lemma styp_subst_no_free_ident :
  forall v' t t', ~ In v' (fvar t) -> styp_subst v' t t' = t.
  Proof.
    intros v' t.
    induction t; cbn [styp_subst]; auto; intros t'.
    1,2: destruct (eqb_spec x v'); auto; cbn; tauto.
    7,8: destruct (eqb_spec v v'); auto; cbn;
         intros Hnin; rewrite IHt; auto;
         intros Hin; rewrite fvar'_prop, filter_In, neg_in_dec_true_iff in Hnin; cbn in Hnin; tauto.
    5,6: intros Hnin; cbn; rewrite IHt; auto.
    all: cbn; intros Hnin; rewrite in_app_iff in Hnin; specialize (IHt1 t'); specialize (IHt2 t').
    all: rewrite IHt1; [rewrite IHt2|]; tauto.
  Qed.

  (* If s is the name of a free variable in t,
     return the list of variables that would be captured if s is substituted with that variable.
     Otherwise, return [].
     l is the list of currently bound variables.
   *)
  Fixpoint styp_forbidden' (t : STyp) (s : pvn) (l : list pvn) :=
  match t with
  | STyp_Var x => if eqb x s then l else []
  | STyp_VarDual x => if eqb x s then l else []
  | STyp_Const x => []
  | STyp_ConstDual x => []
  | STyp_Times t1 t2 => (styp_forbidden' t1 s l) ++ (styp_forbidden' t2 s l)
  | STyp_Par t1 t2 => (styp_forbidden' t1 s l) ++ (styp_forbidden' t2 s l)
  | STyp_Plus t1 t2 => (styp_forbidden' t1 s l) ++ (styp_forbidden' t2 s l)
  | STyp_With t1 t2 => (styp_forbidden' t1 s l) ++ (styp_forbidden' t2 s l)
  | STyp_Excl t => styp_forbidden' t s l
  | STyp_Ques t => styp_forbidden' t s l
  | STyp_Exists v t => if eqb v s then [] else styp_forbidden' t s (v :: l)
  | STyp_Forall v t => if eqb v s then [] else styp_forbidden' t s (v :: l)
  | STyp_One => []
  | STyp_Bot => []
  | STyp_Zero => []
  | STyp_Top => []
  end.

  Lemma styp_forbidden'_prop :
  forall t s s' l,
  In s' (styp_forbidden' t s l) <-> In s' (styp_forbidden' t s []) \/ (In s (fvar t) /\ In s' l).
  Proof.
    intros t s s'.
    induction t; auto.
    all: intros l; cbn.
    1,2: destruct (eqb_spec x s); cbn; tauto.
    1,2,9,10,11,12: tauto.
    1,2,3,4: repeat rewrite in_app_iff; rewrite IHt1, IHt2; tauto.
    all: destruct (eqb_spec v s); cbn.
    1,3: rewrite fvar'_prop, filter_In, neg_in_dec_true_iff; cbn; tauto.
    all: rewrite IHt, fvar'_prop, filter_In, neg_in_dec_true_iff; cbn.
    all: rewrite (IHt [v]); cbn; tauto.
  Qed.

  Lemma styp_forbidden_empty :
  forall v t l,
  ~ In v (fvar t) ->
  styp_forbidden' t v l = [].
  Proof.
    intros v t l.
    revert l; induction t.
    1,2: cbn; destruct (eqb_spec x v); [subst v; tauto | tauto].
    1,2: cbn; auto.
    1,2,3,4,5,6,9,10,11,12: cbn; intros l; try rewrite in_app_iff; intros Hnin; try (rewrite (IHt1 l), (IHt2 l)); try (rewrite (IHt l)); auto.
    all: cbn; intros l Hnin;
         destruct (eqb_spec v0 v); auto;
         rewrite fvar'_prop, filter_In, neg_in_dec_true_iff in Hnin; cbn in Hnin;
         specialize (IHt (v0 :: l)); tauto.
  Qed.

  Lemma styp_forbidden_dual :
  forall t v l, styp_forbidden' (dual t) v l = styp_forbidden' t v l.
  Proof.
    intros t; induction t; cbn; auto.
    1,2,3,4: intros v l; specialize (IHt1 v l); specialize (IHt2 v l); congruence.
    1,2: intros v' l; specialize (IHt v' (v :: l)); rewrite IHt; auto.
  Qed.

  Hint Rewrite styp_forbidden_dual : styp_simpl.

  Lemma styp_forbidden_subst_no_free :
  forall v v' t e l,
  v' <> v ->
  ~ In v (fvar e) ->
  styp_forbidden' (styp_subst v' t e) v l = styp_forbidden' t v l.
  Proof.
    intros v v' t e l Hneq.
    revert l.
    induction t.
    1,2: intros l; cbn; destruct (eqb_spec x v'); [subst v'; destruct (eqb_spec x v); try contradiction; autorewrite with styp_simpl; try apply styp_forbidden_empty; auto | cbn; destruct (eqb_spec x v); auto].

    1,2,3,4,5,6,7,8,11,12,13,14: cbn; intros l; intros Hnin; try (specialize (IHt1 l Hnin); specialize (IHt2 l Hnin)); try specialize (IHt l Hnin); congruence.

    1,2: cbn; intros l Hnin;
         destruct (eqb_spec v0 v').
    1,3: subst v';
         destruct (eqb_spec v0 v); try contradiction;
         cbn; destruct (eqb_spec v0 v); try contradiction; auto.
    1,2: destruct (eqb_spec v0 v).
    1,3: subst v; cbn; rewrite eqb_refl; auto.
    1,2: cbn; destruct (eqb_spec v0 v); try contradiction; apply (IHt (v0 :: l) Hnin).
  Qed.

  Definition styp_forbidden (t : STyp) (s : pvn) := styp_forbidden' t s [].

  (* If v can be replaced by v'' in t, and v' can be replaced by v'' in both t and t', then v' can be replaced by v'' in t{t'/v}. *)
  Lemma styp_subst_forbidden (t : STyp) (v : pvn) (t' : STyp) (v' : pvn) (v'' : pvn) :
  ~ In v'' (styp_forbidden t v) ->
  ~ In v'' (styp_forbidden t v') ->
  ~ In v'' (styp_forbidden t' v') ->
  ~ In v'' (styp_forbidden (styp_subst v t t') v').
  Proof.
    induction t.
    1,2: cbn; intros _ _;
         destruct (eqb x v); [autorewrite with styp_simpl; auto | cbn; destruct (eqb x v'); auto].

    1,2: cbn; auto.

    1,2,3,4: cbn; intros Hnin1 Hnin2 Hnin3;
             rewrite in_app_iff in Hnin1, Hnin2;
             specialize (IHt1 ltac:(tauto) ltac:(tauto) Hnin3);
             specialize (IHt2 ltac:(tauto) ltac:(tauto) Hnin3);
             rewrite in_app_iff; tauto.

    1,2: cbn; intros Hnin1 Hnin2 Hnin3;
         specialize (IHt Hnin1 Hnin2 Hnin3); auto.

    3,4,5,6: cbn; auto.

    1,2: cbn; destruct (eqb_spec v0 v).
    1,3: (* The variable getting replaced is v0. This has not effect *)
         subst v; cbn; destruct (eqb_spec v0 v'); auto.
    1,2: (* The variable getting replaced is not v0. *)
         cbn; destruct (eqb_spec v0 v'); auto.
    1,2: rewrite (styp_forbidden'_prop t v v'' [v0]);
         rewrite (styp_forbidden'_prop t v' v'' [v0]);
         rewrite (styp_forbidden'_prop (styp_subst v t t') v' v'' [v0]);
         intros Hnin1 Hnin2 Hnin3; cbn;
         specialize (IHt ltac:(tauto) ltac:(tauto) ltac:(tauto)).
    1,2: destruct (eqb_spec v0 v'').
    1,3: cbn in Hnin1, Hnin2; rewrite styp_subst_no_free_ident; tauto.
    1,2: tauto.
  Qed.

  Lemma styp_subst_distr1 :
  forall v v' a b e,
  v <> v' ->
  Forall (fun v'' => ~ In v'' (styp_forbidden' b v' [v])) (fvar e) ->
  Forall (fun v' => ~ In v' (styp_forbidden b v)) (fvar a) ->
  styp_subst v (styp_subst v' b e) (styp_subst v' a e) = styp_subst v' (styp_subst v b a) e.
  Proof.
    intros v v' a b e Hneq.
    induction b.

    3,4,5,6,7,8,9,10,13,14,15,16:
         cbn; intros Hnin1 Hnin2;
         rewrite Forall_forall in Hnin1, Hnin2;
         try (repeat rewrite Forall_forall in IHb1, IHb2;
              specialize (IHb1 ltac:(intros x Hx; apply Hnin1 in Hx; rewrite in_app_iff in Hx; tauto) ltac:(intros x Hx; apply Hnin2 in Hx; rewrite in_app_iff in Hx; tauto));
              specialize (IHb2 ltac:(intros x Hx; apply Hnin1 in Hx; rewrite in_app_iff in Hx; tauto) ltac:(intros x Hx; apply Hnin2 in Hx; rewrite in_app_iff in Hx; tauto))
         );
         try (repeat rewrite Forall_forall in IHb;
              specialize (IHb ltac:(intros x Hx; apply Hnin1 in Hx; tauto) ltac:(intros x Hx; apply Hnin2 in Hx; tauto))
         );
         congruence.

    1,2: cbn; destruct (eqb_spec x v').
    1,3: subst v';
         destruct (eqb_spec x v); [subst; contradiction|];
         cbn; rewrite eqb_refl;
         intros Hnin1 _;
         rewrite Forall_forall in Hnin1;
         rewrite styp_subst_no_free_ident; auto;
         try (unfold fvar; rewrite var_free_dual);
         specialize (Hnin1 v); tauto.
    1,2: destruct (eqb_spec x v).
    1,3: subst v; cbn; rewrite eqb_refl; autorewrite with styp_simpl; auto.
    1,2: cbn; destruct (eqb_spec x v); try contradiction;
         destruct (eqb_spec x v'); try contradiction; auto.

    1,2: cbn; destruct (eqb_spec v0 v').
    1,3: subst v'; cbn;
         destruct (eqb_spec v0 v).
    1,3: subst v; contradiction.
    1,2: cbn; rewrite eqb_refl;
         intros _ Hnin2; clear IHb;
         destruct (in_dec eq_dec v (fvar b)).
    1,3: rewrite (styp_subst_no_free_ident v0); auto;
         rewrite Forall_forall in Hnin2;
         intros Hin; apply Hnin2 in Hin; apply Hin;
         rewrite styp_forbidden'_prop; cbn; tauto.
    1,2: do 2 (rewrite styp_subst_no_free_ident; auto).

    1,2: destruct (eqb_spec v0 v).
    1,3: subst v; intros _; cbn;
         rewrite eqb_refl;
         destruct (eqb_spec v0 v'); try contradiction; auto.
    1,2: intros Hnin1 Hnin2;
         rewrite Forall_forall in Hnin1, Hnin2;
         cbn; destruct (eqb_spec v0 v); try contradiction;
         destruct (eqb_spec v0 v'); try contradiction;
         rewrite IHb; auto.
    all: rewrite Forall_forall; intros x Hx; try specialize (Hnin1 x Hx); try specialize (Hnin2 x Hx).
    all: unfold styp_forbidden; rewrite styp_forbidden'_prop;
         try rewrite styp_forbidden'_prop in Hnin1;
         try rewrite styp_forbidden'_prop in Hnin2;
         cbn in Hnin1, Hnin2; tauto.
  Qed.

  Lemma styp_subst_distr2 :
  forall v a b e,
  styp_subst v b (styp_subst v a e) = styp_subst v (styp_subst v b a) e.
  Proof.
    intros v a b e.
    induction b.

    3,4,5,6,7,8,9,10,13,14,15,16: cbn; congruence.

    1,2: cbn; destruct (eqb_spec x v); autorewrite with styp_simpl; auto.
    1,2: cbn; destruct (eqb_spec x v); try contradiction; auto.

    1,2: cbn; destruct (eqb_spec v0 v).
    1,3: subst v; cbn; rewrite eqb_refl; auto.
    1,2: rewrite IHb; cbn; destruct (eqb_spec v0 v); try contradiction; auto.
  Qed.

  (* If v' can be replaced by v'' in t, and t' does not contain variable v', then v' can be replaced by v'' in t{t'/v}.
     Compared to the theorem above, this one relaxes the condition that v can be replaced by v'' in t.
   *)
  Lemma styp_subst_forbidden_2 (t : STyp) (v : pvn) (t' : STyp) (v' : pvn) (v'' : pvn) :
  ~ In v'' (styp_forbidden t v') ->
  ~ In v' (fvar t') ->
  ~ In v'' (styp_forbidden (styp_subst v t t') v').
  Proof.
    induction t; cbn.
    1,2: repeat match goal with |- context[eqb ?a ?b] => destruct (eqb a b); cbn end; try tauto.
    1,2: intros _ Hnin; rewrite styp_forbidden_empty; auto.
    1,2: rewrite styp_forbidden_dual; intros _ Hnin; rewrite styp_forbidden_empty; auto.
    1,2: tauto.
    1,2,3,4: repeat rewrite in_app_iff; intros Hnin1 Hnin2; specialize (IHt1 ltac:(tauto) ltac:(tauto)); specialize (IHt2 ltac:(tauto) ltac:(tauto)); tauto.
    1,2: apply IHt.
    3,4,5,6: tauto.
    all: destruct (eqb_spec v0 v); cbn.
    1,3: destruct (eqb v0 v'); tauto.
    all: destruct (eqb v0 v'); [tauto|].
    all: intros Hnin1 Hnin2; rewrite styp_forbidden'_prop in Hnin1; specialize (IHt ltac:(tauto) ltac:(tauto)).
    all: rewrite styp_forbidden'_prop; intros Hin;
         destruct Hin as [Hin | Hin]; [tauto|];
         destruct Hin as (Hin1 & Hin2);
         apply var_free_subst in Hin1;
         tauto.
  Qed.

  (* The following lemmas are used for quantifier variable renaming *)

  Lemma var_free_after_rename :
  forall t v v' w,
  In w (fvar t) ->
  v <> w ->
  In w (fvar (styp_subst v t (STyp_Var v'))).
  Proof.
    intros t v v' w.
    induction t.
    all: cbn.
    1,2: destruct (eqb_spec x v); [subst v|]; cbn; tauto.
    1,2: tauto.
    1,2,3,4: repeat rewrite in_app_iff; intros Hpre1 Hpre2; destruct Hpre1 as [Hpre1 | Hpre1]; [specialize (IHt1 ltac:(tauto) ltac:(tauto)) | specialize (IHt2 ltac:(tauto) ltac:(tauto))]; tauto.
    1,2: apply IHt.
    3,4,5,6: tauto.
    all: destruct (eqb v0 v); cbn; [tauto|].
    all: rewrite fvar'_prop; rewrite (fvar'_prop _ [v0]); repeat rewrite filter_In, neg_in_dec_true_iff; cbn.
    all: tauto.
  Qed.

  Lemma var_rename_forbidden :
  forall t v v' w w',
  ~ In v' (fvar t) ->
  ~ In v' (styp_forbidden t v) ->
  w <> v ->
  w <> v' ->
  In w' (styp_forbidden (styp_subst v t (STyp_Var v')) w) <-> In w' (styp_forbidden t w).
  Proof.
    intros t v v' w.
    induction t.
    all: cbn.
    1,2: repeat match goal with |- context[eqb ?a ?b] => destruct (eqb a b); cbn end; tauto.
    1,2: tauto.
    1,2,3,4: intros w'; repeat rewrite in_app_iff; intros Hpre1 Hpre2 Hpre3 Hpre4;
             specialize (IHt1 w' ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto));
             specialize (IHt2 w' ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto));
             unfold styp_forbidden in IHt1, IHt2; rewrite IHt1, IHt2; tauto.
    1,2: apply IHt.
    3,4,5,6: tauto.
    all: destruct (eqb_spec v0 v); cbn; [tauto|].
    all: intros w'; rewrite fvar'_prop, styp_forbidden'_prop, filter_In, neg_in_dec_true_iff; cbn.
    all: destruct (in_dec eq_dec v (fvar t)).
    2,4: rewrite styp_subst_no_free_ident; auto; destruct (eqb v0 w); tauto.
    all: intros Hpre1 Hpre2 Hpre3 Hpre4;
         specialize (IHt w' ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto));
         destruct (eqb_spec v0 w); [tauto|];
         rewrite styp_forbidden'_prop;
         rewrite (styp_forbidden'_prop t w); cbn;
         unfold styp_forbidden in IHt; rewrite IHt; split.
    2,4: intros Hpre;
         destruct Hpre as [Hpre | Hpre]; [auto|];
         destruct Hpre as (Hpre & Hpre'); right; split; auto;
         apply (var_free_after_rename t v v' w Hpre ltac:(intros Heq; symmetry in Heq; tauto)).
    all: intros Hpre;
         destruct Hpre as [Hpre | (Hpre & Hpre')]; [auto | right; split; auto];
         destruct Hpre'; [subst | tauto];
         pose proof (var_free_subst v w t (STyp_Var v') Hpre) as Hfree; cbn in Hfree;
         destruct Hfree as [(? & _) | [Hfalse | Hfalse]]; auto; try subst v'; tauto.
  Qed.

  Lemma rename_subst_parallel :
  forall t v e w w',
  v <> w ->
  v <> w' ->
  ~ In w (fvar e) ->
  styp_subst v (styp_subst w t (STyp_Var w')) e = styp_subst w (styp_subst v t e) (STyp_Var w').
  Proof.
    intros t v e w w' Hneq1 Hneq2 Hnin.
    induction t; cbn.
    1,2: repeat match goal with |- context[eqb ?a ?b] => destruct (eqb_spec a b); try subst; cbn end; try tauto.
    1,2: rewrite styp_subst_no_free_ident; auto.
    1: unfold fvar; rewrite var_free_dual; auto.
    1,2: auto.
    1,2,3,4: rewrite IHt1, IHt2; auto.
    1,2: rewrite IHt; auto.
    3,4,5,6: auto.

    all: destruct (eqb_spec v0 w).
    1,3: subst w; cbn; destruct (eqb_spec v0 v); cbn; rewrite eqb_refl; auto.
    all: cbn; destruct (eqb_spec v0 v); [subst|]; cbn.
    1,3: destruct (eqb_spec v w); [tauto|]; auto.
    all: destruct (eqb_spec v0 w); [tauto | rewrite IHt; auto].
  Qed.

  Lemma subst_after_rename :
  forall t v v' e,
  ~ In v' (fvar t) ->
  ~ In v' (styp_forbidden t v) ->
  styp_subst v t e = styp_subst v' (styp_subst v t (STyp_Var v')) e.
  Proof.
    intros t v v' e.
    induction t; cbn.
    1,2: repeat match goal with |- context[eqb ?a ?b] => destruct (eqb_spec a b); try subst; cbn end; tauto.
    1,2: tauto.
    1,2,3,4: repeat rewrite in_app_iff; intros Hpre1 Hpre2;
             specialize (IHt1 ltac:(tauto) ltac:(tauto));
             specialize (IHt2 ltac:(tauto) ltac:(tauto));
             rewrite IHt1, IHt2; tauto.
    1,2: intros Hpre1 Hpre2; specialize (IHt Hpre1 Hpre2); rewrite IHt; tauto.
    3,4,5,6: tauto.

    all: destruct (eqb_spec v0 v).
    1,3: intros Hpre _; rewrite styp_subst_no_free_ident; auto.
    all: destruct (in_dec eq_dec v (fvar t)).
    2,4: intros Hpre1 Hpre2; do 2 (rewrite styp_subst_no_free_ident; cbn; auto).
    2,3: rewrite fvar'_prop, filter_In, neg_in_dec_true_iff in Hpre1; cbn in Hpre1;
         destruct (eqb_spec v0 v'); auto;
         rewrite styp_subst_no_free_ident; tauto.
    all: cbn; intros Hpre1 Hpre2; rewrite fvar'_prop, filter_In, neg_in_dec_true_iff in Hpre1; cbn in Hpre1.
    all: rewrite styp_forbidden'_prop in Hpre2; cbn in Hpre2.
    all: destruct (eqb_spec v0 v'); [tauto|].
    all: specialize (IHt ltac:(tauto) ltac:(tauto)); rewrite IHt; auto.
  Qed.

  Lemma reverse_rename :
  forall t v v',
  v <> v' ->
  ~ In v' (fvar t) ->
  ~ In v' (styp_forbidden t v) ->
  ~ In v (styp_forbidden (styp_subst v t (STyp_Var v')) v').
  Proof.
    intros t v v' Hneq.
    induction t; cbn.
    1,2: repeat match goal with |- context[eqb ?a ?b] => destruct (eqb_spec a b); try subst; cbn end; tauto.
    1,2: tauto.
    1,2,3,4: repeat rewrite in_app_iff; intros Hpre1 Hpre2;
             specialize (IHt1 ltac:(tauto) ltac:(tauto));
             specialize (IHt2 ltac:(tauto) ltac:(tauto));
             tauto.
    1,2: apply IHt.
    3,4,5,6: tauto.

    all: destruct (eqb_spec v0 v).
    1,3: subst v; cbn; destruct (eqb_spec v0 v'); [tauto|].
    1,2: intros Hpre _; rewrite fvar'_prop, filter_In, neg_in_dec_true_iff in Hpre; cbn in Hpre.
    1,2: rewrite styp_forbidden_empty; tauto.
    all: destruct (in_dec eq_dec v (fvar t)).
    2,4: rewrite styp_subst_no_free_ident; auto; cbn.
    2,3: rewrite styp_subst_no_free_ident in IHt; auto;
         destruct (eqb_spec v0 v'); [tauto|].
    2,3: intros Hpre1 Hpre2;
         rewrite fvar'_prop, filter_In, neg_in_dec_true_iff in Hpre1;
         rewrite styp_forbidden'_prop in Hpre2;
         cbn in Hpre1, Hpre2.
    2,3: specialize (IHt ltac:(tauto) ltac:(tauto));
         rewrite styp_forbidden'_prop; cbn; tauto.
    all: intros Hpre1 Hpre2;
         rewrite fvar'_prop, filter_In, neg_in_dec_true_iff in Hpre1;
         rewrite styp_forbidden'_prop in Hpre2;
         cbn in Hpre1, Hpre2; cbn.
    all: destruct (eqb_spec v0 v'); [tauto|].
    all: specialize (IHt ltac:(tauto) ltac:(tauto)).
    all: rewrite styp_forbidden'_prop; cbn; tauto.
  Qed.

  Lemma var_rename_ident :
  forall v t,
  styp_subst v t (STyp_Var v) = t.
  Proof.
    intros v t.
    induction t; cbn.
    1,2: repeat match goal with |- context[eqb ?a ?b] => destruct (eqb_spec a b); try subst; cbn end; tauto.
    all: try congruence.
    all: destruct (eqb v0 v); congruence.
  Qed.

End Wadler_Types.

Module Wadler_Types_M (PropVarName : UsualDecidableType).
Include (Wadler_Types PropVarName).
End Wadler_Types_M.
