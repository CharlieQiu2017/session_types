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

  (* If a variable is bound then it is not in the free variable list *)
  Lemma var_bound_not_free :
  forall x' t l l',
  incl l l' ->
  In x' (fvar' t l') -> ~ In x' l.
  Proof.
    intros x' t.
    induction t; auto; intros l l'.
    1,2: cbn; destruct (in_dec eq_dec x l'); firstorder; subst x'; firstorder.
    5,6: cbn; intros Hincl; apply IHt; clear IHt; firstorder.
    all: cbn; intros Hincl Hin; apply in_app_or in Hin.
    all: specialize (IHt1 l l'); specialize (IHt2 l l'); tauto.
  Qed.

  (* A variable that occurs in a nested expression is either a free variable of the whole expression, or is bound by some outer quantifier *)
  Lemma var_free_or_bound :
  forall x' t l l',
  incl l l' ->
  In x' (fvar' t l) -> In x' (fvar' t l') \/ In x' l'.
  Proof.
    intros x' t.
    induction t; auto; intros l l'.
    1,2: cbn; destruct (in_dec eq_dec x l); [contradiction|]; cbn.
    1,2: destruct (in_dec eq_dec x l'); auto; intros ? Heq; right.
    1,2: destruct Heq; [subst x'; auto | contradiction].

    5,6: cbn; intros Hincl Hin.
    5,6: pose proof (var_bound_not_free x' t (v :: l) (v :: l) ltac:(apply incl_refl) Hin) as Hnin; cbn in Hnin.
    5,6: specialize (IHt (v :: l) (v :: l') ltac:(clear IHt; firstorder) Hin); firstorder.
    all: cbn; intros Hincl Hin; rewrite in_app_iff; apply in_app_or in Hin; specialize (IHt1 _ _ Hincl); specialize (IHt2 _ _ Hincl); tauto.
  Qed.

  Lemma var_free_incl :
  forall t l l',
  incl l l' ->
  incl (fvar' t l') (fvar' t l).
  Proof.
    intros t.
    induction t; auto; intros l l'.
    1,2: cbn; destruct (in_dec eq_dec x l'); [intros; apply incl_nil_l|];
         intros Hincl; destruct (in_dec eq_dec x l); [|apply incl_refl]; unfold incl in Hincl; exfalso; firstorder.
    1,2: cbn; intros; apply incl_refl.
    1,2,3,4: cbn; intros Hincl; specialize (IHt1 _ _ Hincl); specialize (IHt2 _ _ Hincl); unfold incl in *; intros x; repeat rewrite in_app_iff; firstorder.
    3,4,5,6: cbn; intros; apply incl_refl.
    1,2: cbn; intros Hincl; apply IHt; unfold incl in *; clear IHt; cbn; firstorder.
  Qed.

  Lemma var_free_dual : forall t l, fvar' t l = fvar' (dual t) l.
  Proof.
    intros t; induction t; cbn; auto.
    all: intros l; specialize (IHt1 l); specialize (IHt2 l); congruence.
  Qed.

  Definition fvar (t : STyp) := fvar' t [].

  Lemma var_free_subst :
  forall v v' t t',
  In v' (fvar (styp_subst v t t')) ->
  In v' (fvar t) /\ v' <> v \/ In v' (fvar t').
  Proof.
    intros v v' t t'.
    induction t.

    3,4,5,6,7,8,9,10,13,14,15,16: cbn; repeat rewrite in_app_iff; tauto.

    - cbn.
      destruct (eqb_spec x v).
      + subst v; auto.
      + cbn; intros Hin.
        replace v' with x by tauto.
        auto.

    - cbn.
      destruct (eqb_spec x v).
      + subst v.
        rewrite <- var_free_dual.
        auto.
      + cbn; intros Hin.
        replace v' with x by tauto.
        auto.

    - cbn.
      destruct (eqb_spec v0 v).
      + subst v; cbn.
        intros Hin.
        pose proof (var_bound_not_free _ _ [v0] [v0] ltac:(apply incl_refl) Hin) as Hnin.
        cbn in Hnin.
        left; split; auto.
      + cbn.
        intros Hin.
        pose proof (var_bound_not_free _ _ [v0] [v0] ltac:(apply incl_refl) Hin) as Hnin.
        cbn in Hnin.
        pose proof (var_free_incl (styp_subst v t t') [] [v0] ltac:(apply incl_nil_l)) as Hincl.
        apply Hincl in Hin.
        specialize (IHt Hin).
        destruct IHt as [(IHt1 & IHt2) | IHt]; auto.
        left; split; auto.
        pose proof (var_free_or_bound v' t [] [v0] ltac:(apply incl_nil_l) IHt1) as Hbound.
        destruct Hbound; [auto | tauto].

    - cbn.
      destruct (eqb_spec v0 v).
      + subst v; cbn.
        intros Hin.
        pose proof (var_bound_not_free _ _ [v0] [v0] ltac:(apply incl_refl) Hin) as Hnin.
        cbn in Hnin.
        left; split; auto.
      + cbn.
        intros Hin.
        pose proof (var_bound_not_free _ _ [v0] [v0] ltac:(apply incl_refl) Hin) as Hnin.
        cbn in Hnin.
        pose proof (var_free_incl (styp_subst v t t') [] [v0] ltac:(apply incl_nil_l)) as Hincl.
        apply Hincl in Hin.
        specialize (IHt Hin).
        destruct IHt as [(IHt1 & IHt2) | IHt]; auto.
        left; split; auto.
        pose proof (var_free_or_bound v' t [] [v0] ltac:(apply incl_nil_l) IHt1) as Hbound.
        destruct Hbound; [auto | tauto].
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
         intros Hin;
         pose proof (var_free_or_bound v' t [] [v] ltac:(firstorder) Hin); firstorder.
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

  Lemma styp_forbidden_incl :
  forall t v l l',
  incl l l' ->
  incl (styp_forbidden' t v l) (styp_forbidden' t v l').
  Proof.
    intros t v.
    induction t.
    1,2: cbn; destruct (eqb x v); auto; intros; apply incl_refl.
    1,2: cbn; intros; apply incl_refl.
    1,2,3,4: cbn; intros l l' Hincl x Hx; rewrite in_app_iff in Hx; specialize (IHt1 _ _ Hincl); specialize (IHt2 _ _ Hincl); rewrite in_app_iff; unfold incl in IHt1, IHt2; clear Hincl; firstorder.
    1,2: cbn; auto.
    3,4,5,6: cbn; intros; apply incl_refl.
    all: cbn;
         destruct (eqb_spec v0 v); [intros; apply incl_refl|];
         intros l l' Hincl;
         apply IHt;
         clear IHt;
         unfold incl; unfold incl in Hincl; firstorder.
  Qed.

  Lemma styp_forbidden_bound :
  forall t v v' l,
  In v (fvar t) ->
  In v' l ->
  In v' (styp_forbidden' t v l).
  Proof.
    intros t v v'.
    induction t.
    1,2: cbn; destruct (eqb_spec x v); [auto | tauto].
    1,2: cbn; auto.
    1,2,3,4: intros l; cbn;
             repeat rewrite in_app_iff;
             specialize (IHt1 l); specialize (IHt2 l);
             tauto.
    1,2: cbn; auto.
    3,4,5,6: cbn; auto.
    1,2: intros l; cbn;
         intros Hin1 Hin2;
         eapply var_bound_not_free in Hin1 as Hneq; try apply incl_refl;
         cbn in Hneq;
         destruct (eqb_spec v0 v); [tauto|];
         specialize (IHt (v0 :: l));
         eapply var_free_incl in Hin1; [| apply incl_nil_l];
         apply (IHt ltac:(auto) ltac:(right; auto)).
  Qed.

  Lemma styp_forbidden_in :
  forall t v v' l l',
  incl l l' ->
  In v' (styp_forbidden' t v l') -> In v' (styp_forbidden' t v l) \/ (In v (fvar t) /\ In v' l').
  Proof.
    intros t v v'.
    induction t.
    1,2: intros l l' Hincl; cbn;
         destruct (eqb_spec x v); [subst v; auto | auto].
    1,2: cbn; auto.
    1,2,3,4: intros l l' Hincl; cbn;
             repeat rewrite in_app_iff;
             intros Hin;
             destruct Hin as [Hin | Hin]; [specialize (IHt1 _ _ Hincl Hin); clear IHt2 | specialize (IHt2 _ _ Hincl Hin); clear IHt1];
             tauto.
    1,2: cbn; auto.
    3,4,5,6: cbn; auto.
    1,2: intros l l' Hincl; cbn;
         destruct (eqb_spec v0 v); auto.
    1,2: specialize (IHt (v0 :: l) (v0 :: l') ltac:(unfold incl; unfold incl in Hincl; clear IHt; firstorder));
         intros Hin;
         specialize (IHt Hin);
         destruct IHt as [IHt | (IHt1 & IHt2)]; [auto|].
    1,2: cbn in IHt2;
         destruct IHt2 as [IHt2 | IHt2].
    1,3: subst v'; left; apply styp_forbidden_bound; auto; left; auto.
    1,2: right; split; auto;
         pose proof (var_free_or_bound v t [] [v0] ltac:(apply incl_nil_l) IHt1) as Hfree;
         cbn in Hfree; tauto.
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
    1,2: cbn; intros l Hin;
         destruct (eqb_spec v0 v); auto;
         pose proof (var_free_or_bound v t [] [v0] ltac:(apply incl_nil_l)) as Hbound;
         cbn in Hbound;
         apply (IHt (v0 :: l) ltac:(intros Hin'; tauto)).
  Qed.

  Lemma styp_forbidden_dual :
  forall t v l, styp_forbidden' t v l = styp_forbidden' (dual t) v l.
  Proof.
    intros t; induction t; cbn; auto.
    1,2,3,4: intros v l; specialize (IHt1 v l); specialize (IHt2 v l); congruence.
    1,2: intros v' l; specialize (IHt v' (v :: l)); rewrite IHt; auto.
  Qed.

  Lemma styp_forbidden_subst_no_free :
  forall v v' t e l,
  v' <> v ->
  ~ In v (fvar e) ->
  styp_forbidden' (styp_subst v' t e) v l = styp_forbidden' t v l.
  Proof.
    intros v v' t e l Hneq.
    revert l.
    induction t.
    1,2: intros l; cbn; destruct (eqb_spec x v'); [subst v'; destruct (eqb_spec x v); try contradiction; try rewrite <- styp_forbidden_dual; try apply styp_forbidden_empty; auto | cbn; destruct (eqb_spec x v); auto].

    1,2,3,4,5,6,7,8,11,12,13,14: cbn; intros l; intros Hnin; try (specialize (IHt1 l Hnin); specialize (IHt2 l Hnin)); try specialize (IHt l Hnin); congruence.

    - cbn; intros l Hnin.
      destruct (eqb_spec v0 v').
      + subst v'.
        destruct (eqb_spec v0 v); try contradiction.
        cbn; destruct (eqb_spec v0 v); try contradiction; auto.
      + destruct (eqb_spec v0 v).
        * subst v; cbn; rewrite eqb_refl; auto.
        * cbn; destruct (eqb_spec v0 v); try contradiction.
          apply (IHt (v0 :: l) Hnin).

    - cbn; intros l Hnin.
      destruct (eqb_spec v0 v').
      + subst v'.
        destruct (eqb_spec v0 v); try contradiction.
        cbn; destruct (eqb_spec v0 v); try contradiction; auto.
      + destruct (eqb_spec v0 v).
        * subst v; cbn; rewrite eqb_refl; auto.
        * cbn; destruct (eqb_spec v0 v); try contradiction.
          apply (IHt (v0 :: l) Hnin).
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
    1: cbn; intros _ _;
       destruct (eqb x v); [auto | cbn; destruct (eqb x v'); auto].
    1: cbn; intros _ _;
       destruct (eqb x v); [|cbn; destruct (eqb x v'); auto];
       rewrite <- styp_forbidden_dual; auto.

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
    1,2: intros Hnin1 Hnin2 Hnin3;
         pose proof (styp_forbidden_incl t v [] [v0] ltac:(unfold incl; contradiction)) as Hincl1;
         pose proof (styp_forbidden_incl t v' [] [v0] ltac:(unfold incl; contradiction)) as Hincl2;
         unfold incl in Hincl1, Hincl2;
         specialize (IHt ltac:(intros Hin; apply Hnin1; auto) ltac:(intros Hin; apply Hnin2; auto) Hnin3);
         intros Hin;
         pose proof (styp_forbidden_in (styp_subst v t t') v' v'' [] [v0] ltac:(apply incl_nil_l) Hin) as Hin';
         destruct Hin' as [Hin' | Hin']; [contradiction|];
         cbn in Hin';
         destruct Hin' as (_ & [Hin' | ?]); try contradiction;
         subst v'';
         assert (Hfree : ~ In v (fvar t)) by (intros Hfree; pose proof (styp_forbidden_bound t v v0 [v0] Hfree ltac:(left; auto)); contradiction);
         rewrite styp_subst_no_free_ident in IHt, Hin; auto.
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

    - cbn.
      destruct (eqb_spec x v').
      + subst v'.
        destruct (eqb_spec x v); [subst; contradiction |].
        cbn; rewrite eqb_refl.
        intros Hnin1 _.
        rewrite Forall_forall in Hnin1.
        rewrite styp_subst_no_free_ident; auto.
        intros Hin; apply Hnin1 in Hin; tauto.

      + destruct (eqb_spec x v).
        * subst v.
          cbn; rewrite eqb_refl; auto.
        * cbn; destruct (eqb_spec x v); try contradiction.
          destruct (eqb_spec x v'); try contradiction; auto.

    - cbn.
      destruct (eqb_spec x v').
      + subst v'.
        destruct (eqb_spec x v); [subst; contradiction |].
        cbn; rewrite eqb_refl.
        intros Hnin1 _.
        rewrite styp_subst_no_free_ident; auto; unfold fvar; rewrite var_free_dual; rewrite dual_involute.
        rewrite Forall_forall in Hnin1.
        intros Hin; apply Hnin1 in Hin; tauto.

      + destruct (eqb_spec x v).
        * subst v.
          cbn; rewrite eqb_refl.
          rewrite styp_subst_dual; auto.
        * cbn; destruct (eqb_spec x v); try contradiction.
          destruct (eqb_spec x v'); try contradiction; auto.

    - cbn.
      destruct (eqb_spec v0 v').
      + subst v'; cbn.
        destruct (eqb_spec v0 v).
        1: subst v; contradiction.
        cbn; rewrite eqb_refl.
        intros _ Hnin2; clear IHb.

        destruct (in_dec eq_dec v (fvar b)).
        * rewrite (styp_subst_no_free_ident v0); auto.
          rewrite Forall_forall in Hnin2.
          intros Hin; apply Hnin2 in Hin; apply Hin.
          apply styp_forbidden_bound; auto; left; auto.
        * do 2 (rewrite styp_subst_no_free_ident; auto).

      + destruct (eqb_spec v0 v).
        * subst v; intros _; cbn.
          rewrite eqb_refl.
          destruct (eqb_spec v0 v'); try contradiction.
          auto.
        * intros Hnin1 Hnin2.
          rewrite Forall_forall in Hnin1, Hnin2.
          cbn; destruct (eqb_spec v0 v); try contradiction.
          destruct (eqb_spec v0 v'); try contradiction.
          rewrite IHb; auto.
          all: unfold styp_forbidden.
          all: match goal with |- context[styp_forbidden' ?b ?v ?l] =>
                 rewrite Forall_forall; intros x Hx;
                 try specialize (Hnin1 _ Hx);
                 try specialize (Hnin2 _ Hx);
                 pose proof (styp_forbidden_incl b v l (v0 :: l) ltac:(apply incl_tl; apply incl_refl));
                 auto
               end.

    - cbn.
      destruct (eqb_spec v0 v').
      + subst v'; cbn.
        destruct (eqb_spec v0 v).
        1: subst v; contradiction.
        cbn; rewrite eqb_refl.
        intros _ Hnin2; clear IHb.

        destruct (in_dec eq_dec v (fvar b)).
        * rewrite (styp_subst_no_free_ident v0); auto.
          rewrite Forall_forall in Hnin2.
          intros Hin; apply Hnin2 in Hin; apply Hin.
          apply styp_forbidden_bound; auto; left; auto.
        * do 2 (rewrite styp_subst_no_free_ident; auto).

      + destruct (eqb_spec v0 v).
        * subst v; intros _; cbn.
          rewrite eqb_refl.
          destruct (eqb_spec v0 v'); try contradiction.
          auto.
        * intros Hnin1 Hnin2.
          rewrite Forall_forall in Hnin1, Hnin2.
          cbn; destruct (eqb_spec v0 v); try contradiction.
          destruct (eqb_spec v0 v'); try contradiction.
          rewrite IHb; auto.
          all: unfold styp_forbidden.
          all: match goal with |- context[styp_forbidden' ?b ?v ?l] =>
                 rewrite Forall_forall; intros x Hx;
                 try specialize (Hnin1 _ Hx);
                 try specialize (Hnin2 _ Hx);
                 pose proof (styp_forbidden_incl b v l (v0 :: l) ltac:(apply incl_tl; apply incl_refl));
                 auto
               end.
  Qed.

  Lemma styp_subst_distr2 :
  forall v a b e,
  styp_subst v b (styp_subst v a e) = styp_subst v (styp_subst v b a) e.
  Proof.
    intros v a b e.
    induction b.

    3,4,5,6,7,8,9,10,13,14,15,16: cbn; congruence.

    - cbn; destruct (eqb_spec x v); auto.
      cbn; destruct (eqb_spec x v); try contradiction; auto.

    - cbn; destruct (eqb_spec x v).
      + subst x.
        rewrite styp_subst_dual; auto.
      + cbn.
        destruct (eqb_spec x v); try contradiction; auto.

    - cbn.
      destruct (eqb_spec v0 v).
      + subst v.
        cbn; rewrite eqb_refl; auto.
      + rewrite IHb; cbn.
        destruct (eqb_spec v0 v); try contradiction; auto.

    - cbn.
      destruct (eqb_spec v0 v).
      + subst v.
        cbn; rewrite eqb_refl; auto.
      + rewrite IHb; cbn.
        destruct (eqb_spec v0 v); try contradiction; auto.
  Qed.

  (* When working with processes we often also need "process constants",
     i.e. processes with fixed names and typing information.
     The challenge is to incorporate them in a clean way into the ground logic system.

     Our current handling is to assume a relation from "process constants" to arity and type.
   *)

End Wadler_Types.

Module Wadler_Types_M (PropVarName : UsualDecidableType).
Include (Wadler_Types PropVarName).
End Wadler_Types_M.
