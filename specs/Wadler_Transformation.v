From Stdlib Require Import
  List
  Structures.Equalities
  Sorting.Permutation
  Setoid
  Morphisms.
From Session.lib Require Import
  Lemmas.
From Session.specs Require Import
  Wadler_Types
  Wadler_Proc.
Import
  ListNotations.
Open Scope bool_scope.

Module Type Wadler_Transformation (PropVarName : UsualDecidableType) (ChannelName : UsualDecidableType) (Import WT : Wadler_Types PropVarName) (Import WSE : Wadler_SEnv PropVarName ChannelName WT) (Import WPCS : Wadler_ProcConst_Sig PropVarName WT) (Import WP : Wadler_Proc PropVarName ChannelName WT WSE WPCS).

  #[local] Notation chn := ChannelName.t.
  #[local] Notation eqb := chn_eqb.
  #[local] Notation eq_dec := chn_eq_dec.
  #[local] Notation eqb_spec := chn_eqb_spec.
  #[local] Notation eqb_refl := chn_eqb_refl.
  #[local] Notation eqb_neq := chn_eqb_neq.

  #[export] Instance cp_proper : Proper (Logic.eq ==> @Permutation (chn * STyp) ==> iff) (fun p senv => cp p senv).
  Proof.
    unfold Proper.
    intros p p' Heq; subst p'.
    intros senv1 senv2 Hperm.
    split; intros Hcp; eapply cp_perm; try apply Hcp; auto; symmetry; auto.
  Qed.

  Lemma cp_inv_link :
  forall w x senv,
  cp (Proc_Link w x) senv ->
  exists a, Permutation [(w, dual a); (x, a)] senv.
  Proof.
    intros w x senv Hcp.
    remember (Proc_Link w x) as r.
    revert w x Heqr.
    induction Hcp; try discriminate.
    - intros w' x'; intros Heq; injection Heq; intros; subst w' x'.
      exists a; apply Permutation_refl.
    - intros w' x'; intros Heq; specialize (IHHcp _ _ Heq).
      destruct IHHcp as (a & IHHcp); exists a.
      rewrite IHHcp; auto.
  Qed.

  Lemma cp_inv_comp :
  forall x a p q senv,
  cp (Proc_Comp x a p q) senv ->
  exists gamma delta,
  senv_disjoint gamma delta /\
  cp p ((x, a) :: gamma) /\
  cp q ((x, dual a) :: delta) /\
  Permutation (gamma ++ delta) senv.
  Proof.
    intros x a p q senv Hcp.
    remember (Proc_Comp x a p q) as r.
    revert x a p q Heqr.
    induction Hcp; try discriminate.
    - intros x' a' p' q'; intros Heq; injection Heq; intros; subst x' a' p' q'.
      exists gamma; exists delta; repeat split; auto.
    - intros x' a' p' q'; intros Heq; specialize (IHHcp _ _ _ _ Heq).
      destruct IHHcp as (senv1 & senv2 & IHHcp); exists senv1; exists senv2.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_comp_and_split :
  forall x a l p q senv,
  cp (Proc_CompAndSplit x a l p q) senv ->
  exists gamma delta1 delta2,
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd gamma) /\
  l = map fst gamma /\
  senv_disjoint delta1 delta2 /\
  cp p ((x, a) :: gamma ++ delta1) /\
  cp q ((x, dual a) :: gamma ++ delta2) /\
  Permutation (gamma ++ delta1 ++ delta2) senv.
  Proof.
    intros x a l p q senv Hcp.
    remember (Proc_CompAndSplit x a l p q) as r.
    revert x a l p q Heqr.
    induction Hcp; try discriminate.
    - intros x' a' l' p' q'; intros Heq; injection Heq; intros; subst x' a' l' p' q'.
      exists gamma; exists delta1; exists delta2; repeat split; auto.
    - intros x' a' l' p' q'; intros Heq; specialize (IHHcp _ _ _ _ _ Heq).
      destruct IHHcp as (senv1 & senv2 & senv3 & IHHcp); exists senv1; exists senv2; exists senv3.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_outtyp :
  forall x a v b p senv,
  cp (Proc_OutTyp x a v b p) senv ->
  exists gamma,
    Forall (fun v' => ~ In v' (styp_forbidden b v)) (fvar a) /\
    cp p ((x, styp_subst v b a) :: gamma) /\
    Permutation ((x, STyp_Exists v b) :: gamma) senv.
  Proof.
    intros x a v b p senv Hcp.
    remember (Proc_OutTyp x a v b p) as r.
    revert x a v b p Heqr.
    induction Hcp; try discriminate.
    - intros x' a' v' b' p'; intros Heq; injection Heq; intros; subst x' a' v' b' p'.
      exists gamma; repeat split; auto.
    - intros x' a' v' b' p'; intros Heq; specialize (IHHcp _ _ _ _ _ Heq).
      destruct IHHcp as (senv & IHHcp); exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_intyp :
  forall x v a p senv,
  cp (Proc_InTyp x v a p) senv ->
  exists gamma,
    Forall (fun r => ~ In v (fvar r)) (map snd gamma) /\
    cp p ((x, a) :: gamma) /\
    Permutation ((x, STyp_Forall v a) :: gamma) senv.
  Proof.
    intros x v a p senv Hcp.
    remember (Proc_InTyp x v a p) as r.
    revert x v a p Heqr.
    induction Hcp; try discriminate.
    - intros x' v' a' p'; intros Heq; injection Heq; intros; subst x' v' a' p'.
      exists gamma; repeat split; auto.
    - intros x' v' a' p'; intros Heq; specialize (IHHcp _ _ _ _ Heq).
      destruct IHHcp as (senv & IHHcp); exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma proc_swap' :
  forall x a p q senv,
  cp (Proc_Comp x a p q) senv ->
  cp (Proc_Comp x (dual a) q p) senv.
  Proof.
    intros x a p q senv Hcp.
    destruct (cp_inv_comp _ _ _ _ _ Hcp) as (gamma & delta & Hcp1 & Hcp2 & Hcp3 & Hcp4).
    pose proof Hcp4 as Hcp5.
    rewrite Permutation_app_comm in Hcp5.
    eapply cp_perm.
    2: apply Hcp5.

    constructor; auto.
    - (* disjointness *)
      unfold senv_disjoint.
      unfold senv_disjoint in Hcp1.
      intros m Hin1 Hin2; eapply Hcp1; [apply Hin2 | apply Hin1].

    - (* cp q *)
      rewrite dual_involute; auto.
  Qed.

  Lemma proc_swap :
  forall x a p q senv,
  cp (Proc_Comp x a p q) senv <->
  cp (Proc_Comp x (dual a) q p) senv.
  Proof.
    split.
    1: apply proc_swap'.
    intros Hcp.
    apply proc_swap' in Hcp.
    rewrite dual_involute in Hcp.
    auto.
  Qed.

  Lemma proc_assoc_1 :
  forall x y a b p q r senv,
  In y (proc_channels q) ->
  ~ In x (proc_channels r) ->
  cp (Proc_Comp y b (Proc_Comp x a p q) r) senv ->
  cp (Proc_Comp x a p (Proc_Comp y b q r)) senv.
  Proof.
    intros x y a b p q r senv Hy1 Hy2 Hcp.
    destruct (cp_inv_comp _ _ _ _ _ Hcp) as (gamma_delta & theta & Hcp1 & Hcp2 & Hcp3 & Hcp4).
    destruct (cp_inv_comp _ _ _ _ _ Hcp2) as (gamma & delta_y & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4).

    (* y is in either gamma or delta_y *)
    assert (Hy3 : In (y, b) ((y, b) :: gamma_delta)) by (left; auto).
    rewrite <- Hcp'4 in Hy3.
    rewrite in_app_iff in Hy3.

    (* y cannot be same as x *)
    assert (Hy4 : x <> y).
    { apply cp_senv_valid in Hcp'2, Hcp'3.
      rewrite senv_valid_cons in Hcp'2, Hcp'3.
      intros Heq; subst y.
      destruct Hy3 as [Hy3 | Hy3].
      all: match type of Hy3 with In (?x, ?b) ?l => assert (Hx : In x (map fst l)) by (rewrite in_map_iff; eexists; split; try apply Hy3; auto) end.
      all: tauto.
    }

    (* Simplify Hy1 *)
    rewrite <- (cp_channels _ _ _ Hcp'3) in Hy1.
    cbn in Hy1.
    destruct Hy1 as [? | Hy1]; [tauto|].

    (* Since y is in delta_y, it cannot be in gamma *)
    destruct Hy3 as [Hy3 | Hy3].
    2: clear Hy1.
    1: { unfold senv_disjoint in Hcp'1.
         specialize (Hcp'1 y ltac:(rewrite in_map_iff; eexists; split; try apply Hy3; auto)).
         contradiction.
    }

    (* Simplify Hy2 *)
    rewrite <- (cp_channels _ _ _ Hcp3) in Hy2.
    cbn in Hy2.

    (* delta_y is a permutation of y :: delta *)
    pose proof (in_split_perm _ _ Hy3) as (delta & Hy5).

    (* gamma_delta is a permutation of gamma ++ delta *)
    eapply Permutation_app_head in Hy5 as Hy6.
    Unshelve.
    2: exact gamma.
    rewrite Hcp'4 in Hy6.
    rewrite <- Permutation_middle in Hy6.
    apply Permutation_cons_inv in Hy6.

    (* Permute signature of q to y :: x :: delta *)
    rewrite Hy5 in Hcp'3.
    rewrite perm_swap in Hcp'3.

    (* Now (Proc_Comp y b q r) can be typed as x :: delta ++ theta *)
    assert (Hcp''1 : cp (Proc_Comp y b q r) (((x, dual a) :: delta) ++ theta)).
    { constructor; auto.
      unfold senv_disjoint.
      cbn.
      intros m Hm.
      destruct Hm as [Hm | Hm].
      - subst m; tauto.
      - unfold senv_disjoint in Hcp1.
        apply Hcp1.
        rewrite Hy6.
        rewrite map_app; rewrite in_app_iff; right; auto.
    }
    cbn in Hcp''1.

    (* Now (Proc_Comp x a p (Proc_Comp y b q r)) can be typed as gamma ++ (delta ++ theta) *)
    assert (Hcp''2 : cp (Proc_Comp x a p (Proc_Comp y b q r)) (gamma ++ (delta ++ theta))).
    { constructor; auto.
      unfold senv_disjoint.
      intros m Hm1 Hm2.
      rewrite map_app in Hm2.
      rewrite in_app_iff in Hm2.
      destruct Hm2 as [Hm2 | Hm2].
      - (* m in both gamma, delta *)
        apply cp_senv_valid in Hcp2.
        rewrite senv_valid_cons in Hcp2.
        unfold senv_valid in Hcp2.
        destruct Hcp2 as (_ & Hcp2).
        rewrite Hy6 in Hcp2.
        rewrite map_app in Hcp2.
        eapply NoDup_disjoint in Hcp2.
        2: apply Hm1.
        contradiction.
      - (* m in both gamma, theta *)
        unfold senv_disjoint in Hcp1.
        revert Hm2; apply Hcp1.
        rewrite Hy6.
        rewrite map_app; rewrite in_app_iff; left; auto.
    }

    (* gamma ++ delta ++ theta is a permutation of senv *)
    eapply cp_perm.
    1: apply Hcp''2.
    rewrite app_assoc.
    rewrite <- Hy6.
    auto.
  Qed.

  Lemma proc_assoc_2 :
  forall x y a b p q r senv,
  In x (proc_channels q) ->
  ~ In y (proc_channels p) ->
  cp (Proc_Comp x a p (Proc_Comp y b q r)) senv ->
  cp (Proc_Comp y b (Proc_Comp x a p q) r) senv.
  Proof.
    intros x y a b p q r senv Hx1 Hx2 Hcp.
    destruct (cp_inv_comp _ _ _ _ _ Hcp) as (gamma & delta_theta & Hcp1 & Hcp2 & Hcp3 & Hcp4).
    destruct (cp_inv_comp _ _ _ _ _ Hcp3) as (delta_x & theta & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4).

    (* x is in either delta_x or theta *)
    assert (Hx3 : In (x, dual a) ((x, dual a) :: delta_theta)) by (left; auto).
    rewrite <- Hcp'4 in Hx3.
    rewrite in_app_iff in Hx3.

    (* x cannot be same as y *)
    assert (Hx4 : x <> y).
    { apply cp_senv_valid in Hcp'2, Hcp'3.
      rewrite senv_valid_cons in Hcp'2, Hcp'3.
      intros Heq; subst x.
      destruct Hx3 as [Hx3 | Hx3].
      all: match type of Hx3 with In (?x, ?b) ?l => assert (Hy : In y (map fst l)) by (rewrite in_map_iff; eexists; split; try apply Hx3; auto) end.
      all: tauto.
    }

    (* Simplify Hx1 *)
    rewrite <- (cp_channels _ _ _ Hcp'2) in Hx1.
    cbn in Hx1.
    destruct Hx1 as [Hx1 | Hx1]; [symmetry in Hx1; tauto|].

    (* Since x is in delta_x, it cannot be in theta *)
    destruct Hx3 as [Hx3 | Hx3].
    1: clear Hx1.
    2: { unfold senv_disjoint in Hcp'1.
         specialize (Hcp'1 x Hx1).
         exfalso; apply Hcp'1.
         rewrite in_map_iff; eexists; split; try apply Hx3; auto.
    }

    (* Simplify Hx2 *)
    rewrite <- (cp_channels _ _ _ Hcp2) in Hx2.
    cbn in Hx2.

    (* delta_x is a permutation of x :: delta *)
    pose proof (in_split_perm _ _ Hx3) as (delta & Hx5).

    (* delta_theta is a permutation of delta ++ theta *)
    eapply Permutation_app_tail in Hx5 as Hx6.
    Unshelve.
    2: exact theta.
    cbn in Hx6.
    rewrite Hcp'4 in Hx6.
    apply Permutation_cons_inv in Hx6.

    (* Permute signature of q to x :: y :: delta *)
    rewrite Hx5 in Hcp'2.
    rewrite perm_swap in Hcp'2.

    (* Now (Proc_Comp x a p q) can be typed as y :: gamma ++ delta *)
    assert (Hcp''1 : cp (Proc_Comp x a p q) (gamma ++ (y,b) :: delta)).
    { constructor; auto.
      unfold senv_disjoint.
      cbn.
      intros m Hm Hm'.
      destruct Hm' as [Hm' | Hm'].
      - subst m; tauto.
      - unfold senv_disjoint in Hcp1.
        eapply Hcp1.
        1: apply Hm.
        rewrite Hx6.
        rewrite map_app; rewrite in_app_iff; left; auto.
    }
    eapply cp_perm in Hcp''1.
    2: symmetry; apply Permutation_middle.

    (* Now (Proc_Comp y b (Proc_Comp x a p q) r) can be typed as (gamma ++ delta) ++ theta *)
    assert (Hcp''2 : cp (Proc_Comp y b (Proc_Comp x a p q) r) ((gamma ++ delta) ++ theta)).
    { constructor; auto.
      unfold senv_disjoint.
      intros m Hm1 Hm2.
      rewrite map_app in Hm1.
      rewrite in_app_iff in Hm1.
      destruct Hm1 as [Hm1 | Hm1].
      - (* m in both gamma, theta *)
        unfold senv_disjoint in Hcp1.
        eapply Hcp1.
        1: apply Hm1.
        rewrite Hx6.
        rewrite map_app; rewrite in_app_iff; right; auto.
      - (* m in both delta, theta *)
        apply cp_senv_valid in Hcp3.
        rewrite senv_valid_cons in Hcp3.
        unfold senv_valid in Hcp3.
        destruct Hcp3 as (_ & Hcp3).
        rewrite Hx6 in Hcp3.
        rewrite map_app in Hcp3.
        eapply NoDup_disjoint in Hcp3.
        2: apply Hm1.
        contradiction.
    }

    (* gamma ++ delta ++ theta is a permutation of senv *)
    eapply cp_perm.
    1: apply Hcp''2.
    rewrite <- app_assoc.
    rewrite <- Hx6.
    auto.
  Qed.

  Lemma proc_assoc_3 :
  forall x y a b p q r senv,
  In y (proc_channels p) ->
  ~ In x (proc_channels r) ->
  cp (Proc_Comp y b (Proc_Comp x a p q) r) senv ->
  cp (Proc_Comp x (dual a) q (Proc_Comp y b p r)) senv.
  Proof.
    intros x y a b p q r senv Hy1 Hy2 Hcp.

    apply proc_swap in Hcp as Hcp1.
    apply proc_assoc_2 in Hcp1 as Hcp2; auto.
    apply proc_swap in Hcp2 as Hcp3.

    destruct (cp_inv_comp _ _ _ _ _ Hcp3) as (gamma & delta & Hcp3_1 & Hcp3_2 & Hcp3_3 & Hcp3_4).
    rewrite dual_involute in Hcp3_3.
    apply proc_swap in Hcp3_3 as Hcp4.

    eapply cp_perm.
    2: apply Hcp3_4.
    constructor; auto.
    rewrite dual_involute; auto.
  Qed.

  Lemma proc_assoc_4 :
  forall x y a b p q r senv,
  In x (proc_channels r) ->
  ~ In y (proc_channels p) ->
  cp (Proc_Comp x a p (Proc_Comp y b q r)) senv ->
  cp (Proc_Comp y (dual b) (Proc_Comp x a p r) q) senv.
  Proof.
    intros x y a b p q r senv Hx1 Hx2 Hcp.

    apply proc_swap in Hcp as Hcp1.
    apply proc_assoc_1 in Hcp1 as Hcp2; auto.
    apply proc_swap in Hcp2 as Hcp3.

    destruct (cp_inv_comp _ _ _ _ _ Hcp3) as (gamma & delta & Hcp3_1 & Hcp3_2 & Hcp3_3 & Hcp3_4).
    rewrite dual_involute in Hcp3_3.
    apply proc_swap in Hcp3_2 as Hcp4.

    eapply cp_perm.
    2: apply Hcp3_4.
    constructor; auto.
    rewrite dual_involute; auto.
  Qed.

  Lemma proc_comp_and_split_empty :
  forall x a p q senv,
  cp (Proc_CompAndSplit x a [] p q) senv ->
  cp (Proc_Comp x a p q) senv.
  Proof.
    intros x a p q senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & _ & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5).
    symmetry in Hcp'1.
    apply map_eq_nil in Hcp'1; subst gamma.
    cbn in Hcp'3, Hcp'4, Hcp'5.
    rewrite <- Hcp'5.
    constructor; auto.
  Qed.

  Lemma proc_cut_forall_exists :
  forall x t a v b p v' a' q senv,
  cp (Proc_Comp x t (Proc_OutTyp x a v b p) (Proc_InTyp x v' a' q)) senv ->
  t = STyp_Exists v b /\
  v' = v /\
  a' = dual b /\
  (Forall (fun v'' => ~ In v'' (styp_forbidden a' v')) (fvar a) ->
   Forall (fun v'' => proc_var_subst_pre q v' v'') (fvar a) ->
   cp (Proc_Comp x (styp_subst v b a) p (proc_var_subst q v' a)) senv).
  Proof.
    intros x t a v b p v' a' q senv Hcp.
    destruct (cp_inv_comp _ _ _ _ _ Hcp) as (gamma & delta & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4).

    (* Invert Hcp'2 *)
    destruct (cp_inv_outtyp _ _ _ _ _ _ Hcp'2) as (gamma' & Hcp''1 & Hcp''2 & Hcp''3).
    pose proof Hcp'2 as Hcp''4.
    apply cp_senv_valid in Hcp''4.
    rewrite senv_valid_cons in Hcp''4.
    assert (Hcp''5 : In (x, STyp_Exists v b) ((x, t) :: gamma)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hcp''5.
    destruct Hcp''5 as [Hcp''5 | Hcp''5].
    2: apply (in_map fst) in Hcp''5; cbn in Hcp''5; tauto.
    injection Hcp''5; intros; subst t; clear Hcp''5.
    apply Permutation_cons_inv in Hcp''3.

    (* Invert Hcp'3 *)
    destruct (cp_inv_intyp _ _ _ _ _ Hcp'3) as (delta' & Hcp'''1 & Hcp'''2 & Hcp'''3).
    pose proof Hcp'3 as Hcp'''4.
    apply cp_senv_valid in Hcp'''4.
    rewrite senv_valid_cons in Hcp'''4.
    cbn in Hcp'''3.
    assert (Hcp'''5 : In (x, STyp_Forall v' a') ((x, STyp_Forall v (dual b)) :: delta)) by (rewrite <- Hcp'''3; left; auto).
    cbn in Hcp'''5.
    destruct Hcp'''5 as [Hcp'''5 | Hcp'''5].
    2: apply (in_map fst) in Hcp'''5; cbn in Hcp'''5; tauto.
    injection Hcp'''5; intros; subst v' a'; clear Hcp'''5.
    apply Permutation_cons_inv in Hcp'''3.

    repeat split; auto.
    intros Hpre1 Hpre2.
    pose proof (cp_var_subst _ v a _ Hcp'''2) as Hsubst.

    match type of Hsubst with ?P -> _ => assert (H : P) end.
    { cbn.
      apply Forall_cons; auto.
      rewrite Forall_forall.
      rewrite Forall_forall in Hcp'''1.
      intros z Hz.
      specialize (Hcp'''1 _ Hz).
      rewrite Forall_forall.
      intros w _ Hw2.
      unfold styp_forbidden in Hw2.
      rewrite styp_forbidden_empty in Hw2; auto.
    }
    specialize (Hsubst ltac:(auto) ltac:(auto)); clear H.
    cbn in Hsubst.

    erewrite map_ext_in in Hsubst.
    Unshelve.
    3: exact id.
    2: { intros z Hz.
         destruct z; cbn.
         rewrite Forall_forall in Hcp'''1.
         specialize (Hcp'''1 _ ltac:(rewrite in_map_iff; eexists; split; try apply Hz; auto)).
         cbn in Hcp'''1.
         rewrite styp_subst_no_free_ident; auto.
    }
    rewrite map_id in Hsubst.

    rewrite <- Hcp'4.
    rewrite <- Hcp''3, <- Hcp'''3.
    constructor; auto.
    - unfold senv_disjoint.
      intros m; rewrite Hcp''3, Hcp'''3; auto.
    - rewrite styp_subst_dual; auto.
  Qed.

End Wadler_Transformation.
