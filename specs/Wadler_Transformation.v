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

  (* Weaken a process by a list of channels *)
  Fixpoint weaken_list (l : list chn) (p : Process) :=
  match l with
  | [] => p
  | x :: rest => Proc_ClientNull x (weaken_list rest p)
  end.

  Lemma weaken_list_correct :
  forall p gamma delta,
  senv_valid gamma ->
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd gamma) ->
  senv_disjoint gamma delta ->
  cp p delta ->
  cp (weaken_list (map fst gamma) p) (gamma ++ delta).
  Proof.
    intros p gamma delta.
    induction gamma.
    - cbn; auto.
    - intros Hgamma1.
      unfold senv_valid in Hgamma1.
      cbn in Hgamma1.
      rewrite NoDup_cons_iff in Hgamma1.
      specialize (IHgamma ltac:(tauto)).
      destruct Hgamma1 as (Hgamma1 & _).

      intros Hgamma2.
      cbn in Hgamma2.
      rewrite Forall_cons_iff in Hgamma2.
      specialize (IHgamma ltac:(tauto)).
      destruct Hgamma2 as (Hgamma2 & _).

      intros Hgamma3.
      unfold senv_disjoint in Hgamma3.
      cbn in Hgamma3.
      specialize (IHgamma ltac:(intros x; specialize (Hgamma3 x); tauto)).
      specialize (Hgamma3 (fst a) ltac:(auto)).

      intros Hcp; specialize (IHgamma Hcp).

      cbn.
      destruct a as (x & t); cbn in *.
      destruct t; try contradiction.
      constructor; auto.
      rewrite map_app, in_app_iff; tauto.
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

  Lemma cp_inv_outleft :
  forall x p senv,
  cp (Proc_OutLeft x p) senv ->
  exists a b gamma,
    cp p ((x, a) :: gamma) /\
    Permutation ((x, STyp_Plus a b) :: gamma) senv.
  Proof.
    intros x p senv Hcp.
    remember (Proc_OutLeft x p) as r.
    revert x p Heqr.
    induction Hcp; try discriminate.
    - intros x' p'; intros Heq; injection Heq; intros; subst x' p'.
      exists a; exists b; exists gamma; repeat split; auto.
    - intros x' p'; intros Heq; specialize (IHHcp _ _ Heq).
      destruct IHHcp as (a & b & senv & IHHcp); exists a; exists b; exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_outright :
  forall x p senv,
  cp (Proc_OutRight x p) senv ->
  exists a b gamma,
    cp p ((x, b) :: gamma) /\
    Permutation ((x, STyp_Plus a b) :: gamma) senv.
  Proof.
    intros x p senv Hcp.
    remember (Proc_OutRight x p) as r.
    revert x p Heqr.
    induction Hcp; try discriminate.
    - intros x' p'; intros Heq; injection Heq; intros; subst x' p'.
      exists a; exists b; exists gamma; repeat split; auto.
    - intros x' p'; intros Heq; specialize (IHHcp _ _ Heq).
      destruct IHHcp as (a & b & senv & IHHcp); exists a; exists b; exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_incase :
  forall x p q senv,
  cp (Proc_InCase x p q) senv ->
  exists a b gamma,
    cp p ((x, a) :: gamma) /\
    cp q ((x, b) :: gamma) /\
    Permutation ((x, STyp_With a b) :: gamma) senv.
  Proof.
    intros x p q senv Hcp.
    remember (Proc_InCase x p q) as r.
    revert x p q Heqr.
    induction Hcp; try discriminate.
    - intros x' p' q'; intros Heq; injection Heq; intros; subst x' p' q'.
      exists a; exists b; exists gamma; repeat split; auto.
    - intros x' p' q'; intros Heq; specialize (IHHcp _ _ _ Heq).
      destruct IHHcp as (a & b & senv & IHHcp); exists a; exists b; exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_server :
  forall x y p senv,
  cp (Proc_Server x y p) senv ->
  exists a gamma,
    Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd gamma) /\
    cp p ((y, a) :: gamma) /\
    Permutation ((x, STyp_Excl a) :: gamma) senv.
  Admitted.

  Lemma cp_inv_client :
  forall x y p senv,
  cp (Proc_Client x y p) senv ->
  exists a gamma,
    cp p ((y, a) :: gamma) /\
    Permutation ((x, STyp_Ques a) :: gamma) senv.
  Admitted.

  Lemma cp_inv_client_null :
  forall x p senv,
  cp (Proc_ClientNull x p) senv ->
  exists a gamma,
    cp p gamma /\
    Permutation ((x, STyp_Ques a) :: gamma) senv.
  Admitted.

  Lemma cp_inv_client_split :
  forall x y p senv,
  cp (Proc_ClientSplit x y p) senv ->
  exists a gamma,
    cp p ((x, STyp_Ques a) :: (y, STyp_Ques a) :: gamma) /\
    Permutation ((x, STyp_Ques a) :: gamma) senv.
  Admitted.

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

  Lemma proc_comp_and_split_empty :
  forall x a p q senv,
  cp (Proc_CompAndSplit x a [] p q) senv <->
  cp (Proc_Comp x a p q) senv.
  Proof.
    intros x a p q senv.
    split; intros Hcp.
    - destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & _ & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5).
      symmetry in Hcp'1.
      apply map_eq_nil in Hcp'1; subst gamma.
      cbn in Hcp'3, Hcp'4, Hcp'5.
      rewrite <- Hcp'5.
      constructor; auto.
    - destruct (cp_inv_comp _ _ _ _ _ Hcp) as (gamma & delta & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4).
      rewrite <- Hcp'4.
      rewrite <- (app_nil_l gamma).
      rewrite <- app_assoc.
      eassert (Hnil : [] = _).
      2: rewrite Hnil.
      2: constructor; auto.
      cbn; auto.
  Qed.

  Lemma proc_swap' :
  forall x a l p q senv,
  cp (Proc_CompAndSplit x a l p q) senv ->
  cp (Proc_CompAndSplit x (dual a) l q p) senv.
  Proof.
    intros x a l p q senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6).
    subst l.
    rewrite (Permutation_app_comm delta1 delta2) in Hcp6.
    rewrite <- Hcp6.

    constructor; auto.
    - (* disjointness *)
      unfold senv_disjoint.
      unfold senv_disjoint in Hcp3.
      intros m Hin1 Hin2; eapply Hcp3; [apply Hin2 | apply Hin1].

    - (* cp p *)
      rewrite dual_involute; auto.
  Qed.

  Lemma proc_swap :
  forall x a l p q senv,
  cp (Proc_CompAndSplit x a l p q) senv <->
  cp (Proc_CompAndSplit x (dual a) l q p) senv.
  Proof.
    split.
    1: apply proc_swap'.
    intros Hcp.
    apply proc_swap' in Hcp.
    rewrite dual_involute in Hcp.
    auto.
  Qed.

  Section Proc_Assoc.

  (* In this section we prove the associative law of process composition.
     This proof is complex due to the support of simultaneous cut and contraction.
   *)

  Variable (x y : chn).
  Variable (a b : STyp).
  Variable (l1 l2 : list chn).
  Variable (p q r : Process).
  Variable (senv : SEnv).
  Hypothesis (Hcp : cp (Proc_CompAndSplit y b l2 (Proc_CompAndSplit x a l1 p q) r) senv).
  Hypothesis (Hy1 : In y (proc_channels q)).
  Hypothesis (Hy2 : ~ In y l1).

  Lemma proc_comp_and_split_nested_inv :
  exists L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2,
  l1 = map fst L1 /\
  l2 = map fst L2 /\
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1) /\
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2) /\
  Permutation senv (L2 ++ gamma_delta_no_L2 ++ theta_no_L2) /\
  Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2) /\
  cp p ((x, a) :: L1 ++ gamma_no_L1) /\
  cp q ((x, dual a) :: (y, b) :: L1 ++ delta_no_L1) /\
  cp r ((y, dual b) :: L2 ++ theta_no_L2) /\
  cp (Proc_CompAndSplit x a l1 p q) ((y, b) :: L1 ++ gamma_no_L1 ++ delta_no_L1).
  Proof.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (L2 & gamma_delta_no_L2 & theta_no_L2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6).
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp4) as (L1 & gamma_no_L1 & delta_y_no_L1 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l1 l2.

    (* y is in either gamma_no_L1 or delta_y_no_L1 *)
    assert (Hy3 : In (y, b) ((y, b) :: L2 ++ gamma_delta_no_L2)) by (left; auto).
    rewrite <- Hcp'6 in Hy3.
    do 2 rewrite in_app_iff in Hy3.
    destruct Hy3 as [Hy3 | Hy3].
    1: exfalso; apply Hy2; rewrite in_map_iff; eexists; split; try apply Hy3; auto.

    (* y cannot be same as x *)
    assert (Hy4 : x <> y).
    { apply cp_senv_valid in Hcp'4, Hcp'5.
      rewrite senv_valid_cons in Hcp'4, Hcp'5.
      rewrite map_app, in_app_iff in Hcp'4, Hcp'5.
      intros Heq; subst y.
      destruct Hy3 as [Hy3 | Hy3].
      all: match type of Hy3 with In (?x, ?b) ?l => assert (Hx : In x (map fst l)) by (rewrite in_map_iff; eexists; split; try apply Hy3; auto) end.
      all: tauto.
    }

    (* Simplify Hy1 *)
    rewrite <- (cp_channels _ _ _ Hcp'5) in Hy1.
    cbn in Hy1.
    destruct Hy1 as [? | Hy1']; [tauto|].
    rewrite map_app, in_app_iff in Hy1'.
    destruct Hy1' as [? | Hy1']; [tauto|].

    (* Since y is in delta_y_no_L1, it cannot be in gamma_no_L1 *)
    destruct Hy3 as [Hy3 | Hy3].
    2: clear Hy1.
    1: { unfold senv_disjoint in Hcp'3.
         specialize (Hcp'3 y ltac:(rewrite in_map_iff; eexists; split; try apply Hy3; auto)).
         contradiction.
    }

    (* delta_y_no_L1 is a permutation of y :: delta_no_L1 *)
    pose proof (in_split_perm _ _ Hy3) as (delta_no_L1 & Hy5).
    rewrite Hy5 in Hcp'5.
    rewrite <- Permutation_middle in Hcp'5.

    (* L2 ++ gamma_delta_no_L2 is a permutation of L1 ++ gamma_no_L1 ++ delta_no_L1 *)
    eapply Permutation_app_head in Hy5 as Hy6.
    Unshelve.
    2: exact (L1 ++ gamma_no_L1).
    rewrite <- app_assoc in Hy6.
    rewrite Hcp'6 in Hy6.
    rewrite <- Permutation_middle in Hy6.
    apply Permutation_cons_inv in Hy6.
    rewrite <- app_assoc in Hy6.

    exists L1; exists L2.
    exists gamma_no_L1; exists delta_no_L1.
    exists gamma_delta_no_L2; exists theta_no_L2.
    repeat split; auto.
    - symmetry; auto.
    - symmetry; auto.
    - rewrite <- Hy6; auto.
  Qed.

  Variable (L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 : SEnv).
  Hypothesis (Hcp1 : l1 = map fst L1).
  Hypothesis (Hcp2 : l2 = map fst L2).
  Hypothesis (Hcp3 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1)).
  Hypothesis (Hcp4 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2)).
  Hypothesis (Hcp5 : Permutation senv (L2 ++ gamma_delta_no_L2 ++ theta_no_L2)).
  Hypothesis (Hcp6 : Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hcp7 : cp p ((x, a) :: L1 ++ gamma_no_L1)).
  Hypothesis (Hcp8 : cp q ((x, dual a) :: (y, b) :: L1 ++ delta_no_L1)).
  Hypothesis (Hcp9 : cp r ((y, dual b) :: L2 ++ theta_no_L2)).
  Hypothesis (Hcp10 : cp (Proc_CompAndSplit x a l1 p q) ((y, b) :: L1 ++ gamma_no_L1 ++ delta_no_L1)).

  Definition gamma_channels := filter (fun s => negb (eqb x s)) (proc_channels p).

  Lemma gamma_channels_def : Permutation gamma_channels (map fst (L1 ++ gamma_no_L1)).
  Proof.
    unfold gamma_channels.
    rewrite <- (proc_channels_perm _ _ Hcp7).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp7).
  Qed.

  Definition delta_channels := filter (fun s => negb (eqb x s) && negb (eqb y s)) (proc_channels q).

  Lemma delta_channels_def : Permutation delta_channels (map fst (L1 ++ delta_no_L1)).
  Proof.
    unfold delta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp8).
    cbn [map fst].
    rewrite NoDup_filter_two; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp8).
  Qed.

  Definition theta_channels := filter (fun s => negb (eqb y s)) (proc_channels r).

  Lemma theta_channels_def : Permutation theta_channels (map fst (L2 ++ theta_no_L2)).
  Proof.
    unfold theta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp9).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp9).
  Qed.

  Lemma gamma_no_L1_delta_no_L1_disjoint : senv_disjoint gamma_no_L1 delta_no_L1.
  Proof.
    apply senv_app.
    apply cp_senv_valid in Hcp10.
    rewrite senv_valid_cons in Hcp10.
    destruct Hcp10 as (_ & Hcp10').
    apply senv_app in Hcp10'.
    apply Hcp10'.
  Qed.

  Lemma gamma_delta_no_L2_theta_no_L2_disjoint : senv_disjoint gamma_delta_no_L2 theta_no_L2.
  Proof.
    apply senv_app.
    rewrite Hcp5 in Hcp.
    apply cp_senv_valid in Hcp.
    apply senv_app in Hcp.
    apply Hcp.
  Qed.

  (* L1 is the intersection of gamma and delta. *)
  Lemma L1_prop_1 : forall x, In x (L1 ++ gamma_no_L1) -> In (fst x) (map fst (L1 ++ delta_no_L1)) -> In x L1.
  Proof.
    intros z.
    rewrite map_app.
    do 2 rewrite in_app_iff.
    intros Hin1 Hin2.
    destruct Hin1 as [Hin1 | Hin1]; auto.
    apply (in_map fst) in Hin1 as Hin3.
    apply cp_senv_valid in Hcp7.
    rewrite senv_valid_cons in Hcp7.
    destruct Hcp7 as (_ & Hcp7').
    apply senv_app in Hcp7'.
    destruct Hcp7' as (_ & _ & Hcp7').
    specialize (Hcp7' (fst z)).
    pose proof (gamma_no_L1_delta_no_L1_disjoint (fst z)).
    tauto.
  Qed.

  Lemma L1_prop_2 : forall x, In x (L1 ++ delta_no_L1) -> In (fst x) (map fst (L1 ++ gamma_no_L1)) -> In x L1.
  Proof.
    intros z.
    rewrite map_app.
    do 2 rewrite in_app_iff.
    intros Hin1 Hin2.
    destruct Hin1 as [Hin1 | Hin1]; auto.
    apply (in_map fst) in Hin1 as Hin3.
    apply cp_senv_valid in Hcp8.
    do 2 rewrite senv_valid_cons in Hcp8.
    destruct Hcp8 as (_ & _ & Hcp8').
    apply senv_app in Hcp8'.
    destruct Hcp8' as (_ & _ & Hcp8').
    specialize (Hcp8' (fst z)).
    pose proof (gamma_no_L1_delta_no_L1_disjoint (fst z)).
    tauto.
  Qed.

  Lemma L2_prop_1 : forall x, In x (L2 ++ gamma_delta_no_L2) -> In (fst x) (map fst (L2 ++ theta_no_L2)) -> In x L2.
  Proof.
    intros z.
    rewrite map_app.
    do 2 rewrite in_app_iff.
    intros Hin1 Hin2.
    destruct Hin1 as [Hin1 | Hin1]; auto.
    apply (in_map fst) in Hin1 as Hin3.
    rewrite Hcp6 in Hcp10.
    apply cp_senv_valid in Hcp10.
    rewrite senv_valid_cons in Hcp10.
    destruct Hcp10 as (_ & Hcp10').
    apply senv_app in Hcp10'.
    destruct Hcp10' as (_ & _ & Hcp10').
    specialize (Hcp10' (fst z)).
    pose proof (gamma_delta_no_L2_theta_no_L2_disjoint (fst z)).
    tauto.
  Qed.

  Lemma L2_prop_2 : forall x, In x (L2 ++ theta_no_L2) -> In (fst x) (map fst (L2 ++ gamma_delta_no_L2)) -> In x L2.
  Proof.
    intros z.
    rewrite map_app.
    do 2 rewrite in_app_iff.
    intros Hin1 Hin2.
    destruct Hin1 as [Hin1 | Hin1]; auto.
    apply (in_map fst) in Hin1 as Hin3.
    apply cp_senv_valid in Hcp9.
    rewrite senv_valid_cons in Hcp9.
    destruct Hcp9 as (_ & Hcp9').
    apply senv_app in Hcp9'.
    destruct Hcp9' as (_ & _ & Hcp9').
    specialize (Hcp9' (fst z)).
    pose proof (gamma_delta_no_L2_theta_no_L2_disjoint (fst z)).
    tauto.
  Qed.

  Lemma L2_prop_1_alt : forall x, In x (L1 ++ gamma_no_L1) \/ In x (L1 ++ delta_no_L1) -> In (fst x) (map fst (L2 ++ theta_no_L2)) -> In x L2.
  Proof.
    intros z Hz.
    rewrite <- in_app_iff in Hz.
    rewrite in_app_app_iff in Hz.
    rewrite Hcp6 in Hz.
    apply L2_prop_1; auto.
  Qed.

  Lemma L2_prop_2_alt : forall x, In x (L2 ++ theta_no_L2) -> In (fst x) (map fst (L1 ++ gamma_no_L1)) \/ In (fst x) (map fst (L1 ++ delta_no_L1)) -> In x L2.
  Proof.
    intros z Hz1 Hz2.
    do 2 rewrite map_app in Hz2.
    rewrite <- in_app_iff in Hz2.
    rewrite in_app_app_iff in Hz2.
    do 2 rewrite <- map_app in Hz2.
    rewrite Hcp6 in Hz2.
    apply L2_prop_2; auto.
  Qed.

  Lemma L2_prop_3 : forall x, In x (L2 ++ theta_no_L2) -> In (fst x) (map fst (L1 ++ gamma_no_L1)) -> In x (L1 ++ gamma_no_L1).
  Proof.
    intros z Hz1 Hz2.
    pose proof (L2_prop_2_alt z ltac:(auto) ltac:(auto)) as Hz3.
    assert (Hz4 : In z (L2 ++ gamma_delta_no_L2)).
    { rewrite in_app_iff; auto. }
    rewrite <- Hcp6 in Hz4.
    rewrite app_assoc in Hz4.
    rewrite in_app_iff in Hz4.
    destruct Hz4 as [Hz4 | Hz4]; auto.
    rewrite app_assoc in Hcp10.
    apply cp_senv_valid in Hcp10.
    rewrite senv_valid_cons in Hcp10.
    destruct Hcp10 as (_ & Hcp10').
    apply senv_app in Hcp10'.
    destruct Hcp10' as (_ & _ & Hcp10').
    specialize (Hcp10' (fst z)).
    apply (in_map fst) in Hz4.
    tauto.
  Qed.

  Lemma L2_prop_4 : forall x, In x (L2 ++ theta_no_L2) -> In (fst x) (map fst (L1 ++ delta_no_L1)) -> In x (L1 ++ delta_no_L1).
  Proof.
    intros z Hz1 Hz2.
    pose proof (L2_prop_2_alt z ltac:(auto) ltac:(auto)) as Hz3.
    assert (Hz4 : In z (L2 ++ gamma_delta_no_L2)).
    { rewrite in_app_iff; auto. }
    rewrite <- Hcp6 in Hz4.
    rewrite (Permutation_app_comm gamma_no_L1) in Hz4.
    rewrite app_assoc in Hz4.
    rewrite in_app_iff in Hz4.
    destruct Hz4 as [Hz4 | Hz4]; auto.
    rewrite (Permutation_app_comm gamma_no_L1) in Hcp10.
    rewrite app_assoc in Hcp10.
    apply cp_senv_valid in Hcp10.
    rewrite senv_valid_cons in Hcp10.
    destruct Hcp10 as (_ & Hcp10').
    unfold senv_valid in Hcp10'.
    apply senv_app in Hcp10'.
    destruct Hcp10' as (_ & _ & Hcp10').
    specialize (Hcp10' (fst z)).
    apply (in_map fst) in Hz4.
    tauto.
  Qed.

  (* We now define the new channel permutations.
     We first split the channels of Q into new_L1 and delta_no_new_L1.
     new_L1 contains channels that are in both Q and R.
   *)
  Definition delta_name_split_func := fun t => if in_dec eq_dec t theta_channels then true else false.
  Definition delta_split_func := fun (s : chn * STyp) => let f := delta_name_split_func in f (fst s).
  Definition new_L1 := filter delta_split_func (L1 ++ delta_no_L1).
  Definition delta_no_new_L1 := filter (fun s => negb (delta_split_func s)) (L1 ++ delta_no_L1).

  Lemma delta_split : Permutation (L1 ++ delta_no_L1) (new_L1 ++ delta_no_new_L1).
  Proof. unfold new_L1, delta_no_new_L1; apply filter_split. Qed.

  Definition new_l1 := filter delta_name_split_func delta_channels.

  Lemma new_l1_def : Permutation new_l1 (map fst new_L1).
  Proof.
    unfold new_l1.
    rewrite delta_channels_def.
    unfold new_L1.
    unfold delta_split_func.
    rewrite map_filter.
    auto.
  Qed.

  Lemma new_L1_prop : forall x, In x (L2 ++ theta_no_L2) -> In (fst x) (map fst (L1 ++ delta_no_L1)) -> In x new_L1.
  Proof.
    intros z Hin1 Hin2.
    pose proof (L2_prop_4 z ltac:(auto) ltac:(auto)) as Hin3.
    unfold new_L1, delta_split_func, delta_name_split_func.
    rewrite filter_In.
    split; auto.
    destruct (in_dec eq_dec (fst z) theta_channels); auto.
    rewrite theta_channels_def in n.
    apply (in_map fst) in Hin1.
    contradiction.
  Qed.

  (* The signature of Q can be permuted into y :: new_L1 ++ x :: delta_no_new_L1 *)
  Lemma proc_q_perm :
  cp q ((y, b) :: new_L1 ++ (x, dual a) :: delta_no_new_L1).
  Proof.
    rewrite delta_split in Hcp8.
    rewrite perm_swap in Hcp8.
    rewrite Permutation_middle in Hcp8.
    auto.
  Qed.

  (* Similarly, we split the channels of R into new_L1 and theta_no_new_L2 *)
  Definition theta_name_split_func := fun t => if in_dec eq_dec t delta_channels then true else false.
  Definition theta_split_func := fun (s : chn * STyp) => let f := theta_name_split_func in f (fst s).
  Definition new_L1' := filter theta_split_func (L2 ++ theta_no_L2).
  Definition theta_no_new_L1 := filter (fun s => negb (theta_split_func s)) (L2 ++ theta_no_L2).

  Lemma theta_split' : Permutation (L2 ++ theta_no_L2) (new_L1' ++ theta_no_new_L1).
  Proof. unfold new_L1', theta_no_new_L1; apply filter_split. Qed.

  Lemma new_L1_eq : forall x, In x new_L1' <-> In x new_L1.
  Proof.
    intros z.
    unfold new_L1', theta_split_func, theta_name_split_func.
    rewrite filter_In.
    split.
    - intros Hin.
      destruct Hin as (Hin1 & Hin2).
      destruct (in_dec eq_dec (fst z) delta_channels); try discriminate; clear Hin2.
      rewrite delta_channels_def in i.
      apply new_L1_prop; auto.
    - unfold new_L1, delta_split_func, delta_name_split_func.
      rewrite filter_In.
      intros Hin.
      destruct Hin as (Hin1 & Hin2).
      destruct (in_dec eq_dec (fst z) theta_channels); try discriminate; clear Hin2.
      rewrite theta_channels_def in i.
      destruct (in_dec eq_dec (fst z) delta_channels).
      2: rewrite delta_channels_def in n; apply (in_map fst) in Hin1; contradiction.
      split; auto.
      rewrite in_app_iff; left.
      apply L2_prop_1_alt; auto.
  Qed.

  Lemma new_L1_perm : Permutation new_L1' new_L1.
  Proof.
    apply NoDup_Permutation.
    3: apply new_L1_eq.
    1: unfold new_L1'.
    2: unfold new_L1.
    all: apply NoDup_filter.
    - apply cp_senv_valid in Hcp9; rewrite senv_valid_cons in Hcp9; eapply NoDup_map_inv; apply Hcp9.
    - apply cp_senv_valid in Hcp8; do 2 rewrite senv_valid_cons in Hcp8; eapply NoDup_map_inv; apply Hcp8.
  Qed.

  Lemma theta_split : Permutation (L2 ++ theta_no_L2) (new_L1 ++ theta_no_new_L1).
  Proof. pose proof theta_split' as H; rewrite new_L1_perm in H; auto. Qed.

  Lemma proc_r_perm :
  cp r ((y, dual b) :: new_L1 ++ theta_no_new_L1).
  Proof.
    pose proof Hcp9 as Hcp9'.
    rewrite theta_split in Hcp9'.
    auto.
  Qed.

  Lemma delta_no_new_L1_theta_no_new_L1_disjoint :
  senv_disjoint delta_no_new_L1 theta_no_new_L1.
  Proof.
    unfold senv_disjoint.
    intros z Hz1 Hz2.
    unfold delta_no_new_L1 in Hz1.
    unfold theta_no_new_L1 in Hz2.
    rewrite in_map_iff in Hz1, Hz2.
    destruct Hz1 as (w & Hw1 & Hw2); subst z.
    destruct Hz2 as (v & Hv1 & Hv2).
    rewrite filter_In in Hw2, Hv2.
    destruct Hw2 as (Hw1 & Hw2).
    rewrite Bool.negb_true_iff in Hw2.
    unfold delta_split_func, delta_name_split_func in Hw2.
    destruct Hv2 as (Hv2 & _).
    rewrite <- Hv1 in Hw2.
    destruct (in_dec eq_dec (fst v) theta_channels); try discriminate.
    rewrite theta_channels_def in n; apply (in_map fst) in Hv2; contradiction.
  Qed.

  Hypothesis (Hy3 : ~ In x (proc_channels r)).

  (* We are now ready to cut Q and R. *)
  Lemma cp_comp_q_r :
  cp (Proc_CompAndSplit y b new_l1 q r) (new_L1 ++ (x, dual a) :: delta_no_new_L1 ++ theta_no_new_L1).
  Proof.
    assert (Hnew_L1 : exists new_L1'', Permutation new_L1 new_L1'' /\ map fst new_L1'' = new_l1).
    { pose proof new_l1_def as Hperm.
      symmetry in Hperm.
      destruct (map_permutation_ex fst new_L1 _ Hperm) as (new_L1'' & Hperm1 & Hperm2).
      exists new_L1''; split; auto.
    }
    destruct Hnew_L1 as (new_L1'' & Hnew_L1_1 & Hnew_L1_2).
    rewrite <- Hnew_L1_2.
    rewrite Hnew_L1_1.

    pose proof proc_q_perm as Hcp8'.
    pose proof proc_r_perm as Hcp9'.
    rewrite Hnew_L1_1 in Hcp8', Hcp9'.
    rewrite app_comm_cons.
    constructor; auto.

    - rewrite <- Hnew_L1_1.
      rewrite Forall_forall.
      intros z Hz.
      unfold new_L1, delta_split_func, delta_name_split_func in Hz.
      rewrite in_map_iff in Hz.
      destruct Hz as (w & Hw1 & Hw2); subst z.
      rewrite filter_In in Hw2.
      destruct Hw2 as (Hw1 & Hw2).
      destruct (in_dec eq_dec (fst w) theta_channels); try discriminate; clear Hw2.
      rewrite theta_channels_def in i.
      pose proof (L2_prop_1_alt w ltac:(auto) ltac:(auto)) as Hw2.
      rewrite Forall_forall in Hcp4.
      apply (Hcp4 (snd w) ltac:(apply in_map; auto)).

    - unfold senv_disjoint.
      intros z Hz.
      cbn in Hz.
      destruct Hz as [Hz | Hz].
      + subst z.
        unfold theta_no_new_L1, theta_split_func.
        rewrite in_map_iff.
        intros Hex.
        destruct Hex as (w & Hw1 & Hw2).
        rewrite filter_In in Hw2.
        destruct Hw2 as (Hw2 & _).
        apply Hy3.
        rewrite <- (proc_channels_perm _ _ Hcp9).
        cbn; right.
        apply (in_map fst) in Hw2.
        rewrite Hw1 in Hw2; auto.

      + intros Hz2.
        apply (delta_no_new_L1_theta_no_new_L1_disjoint z); auto.
  Qed.

  (* We now split the channels of P into new_L2 and gamma_no_new_L2 *)
  Definition gamma_name_split_func := fun t => (if in_dec eq_dec t delta_channels then true else false) || (if in_dec eq_dec t theta_channels then true else false).
  Definition gamma_split_func := fun (s : chn * STyp) => let f := gamma_name_split_func in f (fst s).
  Definition new_L2 := filter gamma_split_func (L1 ++ gamma_no_L1).
  Definition gamma_no_new_L2 := filter (fun s => negb (gamma_split_func s)) (L1 ++ gamma_no_L1).

  Lemma gamma_split : Permutation (L1 ++ gamma_no_L1) (new_L2 ++ gamma_no_new_L2).
  Proof. unfold new_L2, gamma_no_new_L2; apply filter_split. Qed.

  Definition new_l2 := filter gamma_name_split_func gamma_channels.

  Lemma new_l2_def : Permutation new_l2 (map fst new_L2).
  Proof.
    unfold new_l2.
    rewrite gamma_channels_def.
    unfold new_L2.
    unfold gamma_split_func.
    rewrite map_filter.
    auto.
  Qed.

  Lemma new_L2_prop : forall x, In x (L1 ++ delta_no_L1) \/ In x (L2 ++ theta_no_L2) -> In (fst x) (map fst (L1 ++ gamma_no_L1)) -> In x new_L2.
  Proof.
    intros z Hin1 Hin2.
    unfold new_L2, gamma_split_func, gamma_name_split_func.
    rewrite filter_In.
    destruct Hin1 as [Hin1 | Hin1].
    - pose proof (L1_prop_2 z ltac:(auto) ltac:(auto)) as Hin3.
      split.
      1: rewrite in_app_iff; auto.
      apply (in_map fst) in Hin1 as Hin4.
      destruct (in_dec eq_dec (fst z) delta_channels); auto.
      rewrite delta_channels_def in n; contradiction.
    - pose proof (L2_prop_3 z ltac:(auto) ltac:(auto)).
      split; auto.
      destruct (in_dec eq_dec (fst z) theta_channels).
      1: rewrite Bool.orb_true_r; auto.
      rewrite theta_channels_def in n; apply (in_map fst) in Hin1; contradiction.
  Qed.

  Definition delta_theta_name_split_func := fun t => if in_dec eq_dec t gamma_channels then true else false.
  Definition delta_theta_split_func := fun (s : chn * STyp) => let f := delta_theta_name_split_func in f (fst s).
  Definition new_L2' := filter delta_theta_split_func (new_L1 ++ delta_no_new_L1 ++ theta_no_new_L1).
  Definition delta_theta_no_new_L2 := filter (fun s => negb (delta_theta_split_func s)) (new_L1 ++ delta_no_new_L1 ++ theta_no_new_L1).

  Lemma delta_theta_split' : Permutation (new_L1 ++ delta_no_new_L1 ++ theta_no_new_L1) (new_L2' ++ delta_theta_no_new_L2).
  Proof. unfold new_L2, delta_theta_no_new_L2. apply filter_split. Qed.

  Lemma new_L2_eq : forall x, In x new_L2' <-> In x new_L2.
  Proof.
    intros z.
    unfold new_L2', delta_theta_split_func, delta_theta_name_split_func.
    do 2 rewrite filter_app.
    rewrite <- in_app_app_iff.
    do 2 rewrite <- filter_app.
    rewrite <- delta_split, <- theta_split.
    rewrite <- filter_app.
    rewrite filter_In.
    rewrite in_app_iff.
    split.
    - intros Hin.
      destruct Hin as (Hin1 & Hin2).
      destruct (in_dec eq_dec (fst z) gamma_channels); try discriminate; clear Hin2.
      rewrite gamma_channels_def in i.
      apply new_L2_prop; auto.
    - intros Hin.
      unfold new_L2, gamma_split_func, gamma_name_split_func in Hin.
      rewrite filter_In in Hin.
      destruct Hin as (Hin1 & Hin2).
      destruct (in_dec eq_dec (fst z) gamma_channels).
      2: rewrite gamma_channels_def in n; apply (in_map fst) in Hin1; contradiction.
      split; auto.
      destruct (in_dec eq_dec (fst z) delta_channels).
      1: rewrite delta_channels_def in i0; pose proof (L1_prop_1 z ltac:(auto) ltac:(auto)); left; rewrite in_app_iff; auto.
      destruct (in_dec eq_dec (fst z) theta_channels); try discriminate.
      rewrite theta_channels_def in i0.
      pose proof (L2_prop_1_alt z ltac:(auto) ltac:(auto)).
      right; rewrite in_app_iff; auto.
  Qed.

  Lemma new_L2_perm : Permutation new_L2' new_L2.
  Proof.
    apply NoDup_Permutation.
    3: apply new_L2_eq.
    1: unfold new_L2'.
    2: unfold new_L2.
    all: apply NoDup_filter.
    - pose proof (cp_comp_q_r) as Hcp'.
      rewrite <- Permutation_middle in Hcp'.
      apply cp_senv_valid in Hcp'.
      rewrite senv_valid_cons in Hcp'.
      destruct Hcp' as (_ & Hcp').
      unfold senv_valid in Hcp'.
      apply NoDup_map_inv in Hcp'; auto.
    - apply cp_senv_valid in Hcp7; rewrite senv_valid_cons in Hcp7; eapply NoDup_map_inv; apply Hcp7.
  Qed.

  Lemma delta_theta_split : Permutation (new_L1 ++ delta_no_new_L1 ++ theta_no_new_L1) (new_L2 ++ delta_theta_no_new_L2).
  Proof. pose proof delta_theta_split' as H; rewrite new_L2_perm in H; auto. Qed.

  Lemma gamma_no_new_L2_delta_theta_no_new_L2_disjoint :
  senv_disjoint gamma_no_new_L2 delta_theta_no_new_L2.
  Proof.
    unfold senv_disjoint.
    intros z Hz1 Hz2.
    unfold gamma_no_new_L2 in Hz1.
    unfold delta_theta_no_new_L2 in Hz2.
    rewrite in_map_iff in Hz1, Hz2.
    destruct Hz1 as (w & Hw1 & Hw2); subst z.
    destruct Hz2 as (v & Hv1 & Hv2).
    rewrite filter_In in Hw2, Hv2.
    destruct Hw2 as (Hw1 & Hw2).
    rewrite Bool.negb_true_iff in Hw2.
    unfold gamma_split_func, gamma_name_split_func in Hw2.
    destruct Hv2 as (Hv2 & _).
    rewrite <- Hv1 in Hw2.
    rewrite <- in_app_app_iff in Hv2.
    rewrite in_app_iff in Hv2.
    destruct (in_dec eq_dec (fst v) delta_channels); try discriminate.
    destruct (in_dec eq_dec (fst v) theta_channels); try (rewrite Bool.orb_true_r in Hw2; discriminate).
    rewrite delta_channels_def in n.
    rewrite theta_channels_def in n0.
    rewrite delta_split in n.
    rewrite theta_split in n0.
    destruct Hv2 as [Hv2 | Hv2]; apply (in_map fst) in Hv2; contradiction.
  Qed.

  Lemma proc_p_perm :
  cp p ((x, a) :: new_L2 ++ gamma_no_new_L2).
  Proof.
    rewrite gamma_split in Hcp7; auto.
  Qed.

  Lemma proc_q_r_perm :
  cp (Proc_CompAndSplit y b new_l1 q r) ((x, dual a) :: new_L2 ++ delta_theta_no_new_L2).
  Proof.
    pose proof (cp_comp_q_r) as Hcp'.
    rewrite <- Permutation_middle in Hcp'.
    rewrite delta_theta_split in Hcp'.
    auto.
  Qed.

  (* We are now ready to cut P and (Q | R). *)
  Lemma cp_comp_p_q_r :
  cp (Proc_CompAndSplit x a new_l2 p (Proc_CompAndSplit y b new_l1 q r)) (new_L2 ++ gamma_no_new_L2 ++ delta_theta_no_new_L2).
    assert (Hnew_L2 : exists new_L2'', Permutation new_L2 new_L2'' /\ map fst new_L2'' = new_l2).
    { pose proof new_l2_def as Hperm.
      symmetry in Hperm.
      destruct (map_permutation_ex fst new_L2 _ Hperm) as (new_L2'' & Hperm1 & Hperm2).
      exists new_L2''; split; auto.
    }
    destruct Hnew_L2 as (new_L2'' & Hnew_L2_1 & Hnew_L2_2).
    rewrite <- Hnew_L2_2.
    rewrite Hnew_L2_1.

    pose proof proc_p_perm as Hcp'1.
    pose proof proc_q_r_perm as Hcp'2.
    rewrite Hnew_L2_1 in Hcp'1, Hcp'2.
    constructor; auto.

    - rewrite <- Hnew_L2_1.
      rewrite Forall_forall.
      intros z Hz.
      unfold new_L2, gamma_split_func, gamma_name_split_func in Hz.
      rewrite in_map_iff in Hz.
      destruct Hz as (w & Hw1 & Hw2); subst z.
      rewrite filter_In in Hw2.
      destruct Hw2 as (Hw1 & Hw2).
      rewrite Bool.orb_true_iff in Hw2.
      destruct Hw2 as [Hw2 | Hw2].
      + destruct (in_dec eq_dec (fst w) delta_channels); try discriminate; clear Hw2.
        rewrite delta_channels_def in i.
        pose proof (L1_prop_1 w ltac:(auto) ltac:(auto)) as Hw2.
        rewrite Forall_forall in Hcp3.
        apply (Hcp3 (snd w) ltac:(apply in_map; auto)).
      + destruct (in_dec eq_dec (fst w) theta_channels); try discriminate; clear Hw2.
        rewrite theta_channels_def in i.
        pose proof (L2_prop_1_alt w ltac:(auto) ltac:(auto)) as Hw2.
        rewrite Forall_forall in Hcp4.
        apply (Hcp4 (snd w) ltac:(apply in_map; auto)).

    - apply gamma_no_new_L2_delta_theta_no_new_L2_disjoint.
  Qed.

  Lemma proc_p_q_r_perm :
  cp (Proc_CompAndSplit x a (filter gamma_name_split_func gamma_channels) p (Proc_CompAndSplit y b (filter delta_name_split_func delta_channels) q r)) senv.
  pose proof cp_comp_p_q_r as Hcp'.
  eapply cp_perm.
  1: apply Hcp'.
  rewrite Hcp5.
  apply NoDup_Permutation.
  - apply cp_senv_valid in Hcp'.
    unfold senv_valid in Hcp'.
    apply NoDup_map_inv in Hcp'; auto.
  - rewrite Hcp5 in Hcp.
    apply cp_senv_valid in Hcp.
    apply NoDup_map_inv in Hcp; auto.
  - intros z.
    rewrite <- in_app_app_iff.
    rewrite <- (in_app_app_iff L2).
    rewrite in_app_iff.
    rewrite (in_app_iff (L2 ++ gamma_delta_no_L2)).
    rewrite <- gamma_split, <- delta_theta_split.
    rewrite <- in_app_app_iff.
    rewrite (in_app_iff (new_L1 ++ delta_no_new_L1)).
    pose proof delta_split as Hsplit3.
    pose proof theta_split as Hsplit4.
    rewrite <- Hsplit3, <- Hsplit4.
    rewrite <- Hcp6.
    rewrite <- in_app_app_iff.
    rewrite (in_app_iff (L1 ++ gamma_no_L1)).
    tauto.
  Qed.

  End Proc_Assoc.

  Lemma proc_assoc_1 :
  forall x y a b l1 l2 p q r senv,
  In y (proc_channels q) ->
  ~ In y l1 ->
  ~ In x (proc_channels r) ->
  cp (Proc_CompAndSplit y b l2 (Proc_CompAndSplit x a l1 p q) r) senv ->
  let new_l1 := filter (delta_name_split_func y r) (delta_channels x y q) in
  let new_l2 := filter (gamma_name_split_func x y q r) (gamma_channels x p) in
  cp (Proc_CompAndSplit x a new_l2 p (Proc_CompAndSplit y b new_l1 q r)) senv.
  Proof.
    intros x y a b l1 l2 p q r senv Hy1 Hy2 Hy3 Hcp.
    pose proof (proc_comp_and_split_nested_inv x y a b l1 l2 p q r senv Hcp Hy1 Hy2) as (L1 & L2 & gamma_no_L1 & delta_no_L1 & gamma_delta_no_L2 & theta_no_L2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6 & Hcp7 & Hcp8 & Hcp9 & Hcp10).
    pose proof (proc_p_q_r_perm x y a b l1 l2 p q r senv Hcp L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 Hcp3 Hcp4 Hcp5 Hcp6 Hcp7 Hcp8 Hcp9 Hcp10 Hy3) as Hcp'.
    cbn.
    apply Hcp'.
  Qed.

  Lemma proc_assoc_2 :
  forall x y a b l1 l2 p q r senv,
  In y (proc_channels p) ->
  ~ In y l1 ->
  ~ In x (proc_channels r) ->
  cp (Proc_CompAndSplit y b l2 (Proc_CompAndSplit x a l1 p q) r) senv ->
  let new_l1 := filter (delta_name_split_func y r) (delta_channels x y p) in
  let new_l2 := filter (gamma_name_split_func x y p r) (gamma_channels x q) in
  cp (Proc_CompAndSplit x (dual a) new_l2 q (Proc_CompAndSplit y b new_l1 p r)) senv.
  Proof.
    intros x y a b l1 l2 p q r senv Hy1 Hy2 Hy3 Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (old_cp_gamma & old_cp_delta1 & old_cp_delta2 & Hold_cp1 & Hold_cp2 & Hold_cp3 & Hold_cp4 & Hold_cp5 & Hold_cp6).
    rewrite proc_swap in Hold_cp4.
    assert (Hnew_cp : cp (Proc_CompAndSplit y b l2 (Proc_CompAndSplit x (dual a) l1 q p) r) senv).
    { rewrite <- Hold_cp6, Hold_cp2; constructor; auto. }
    pose proof (proc_comp_and_split_nested_inv x y (dual a) b l1 l2 q p r senv Hnew_cp Hy1 Hy2) as (L1 & L2 & gamma_no_L1 & delta_no_L1 & gamma_delta_no_L2 & theta_no_L2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6 & Hcp7 & Hcp8 & Hcp9 & Hcp10).
    pose proof (proc_p_q_r_perm x y (dual a) b l1 l2 q p r senv Hnew_cp L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 Hcp3 Hcp4 Hcp5 Hcp6 Hcp7 Hcp8 Hcp9 Hcp10 Hy3) as Hcp'.
    apply Hcp'.
  Qed.

  Lemma proc_assoc_3 :
  forall x y a b l1 l2 p q r senv,
  In x (proc_channels q) ->
  ~ In x l1 ->
  ~ In y (proc_channels p) ->
  cp (Proc_CompAndSplit x a l2 p (Proc_CompAndSplit y b l1 q r)) senv ->
  let new_l1 := filter (delta_name_split_func x p) (delta_channels y x q) in
  let new_l2 := filter (gamma_name_split_func y x q p) (gamma_channels y r) in
  cp (Proc_CompAndSplit y b new_l2 (Proc_CompAndSplit x a new_l1 p q) r) senv.
  Proof.
    intros x y a b l1 l2 p q r senv Hy1 Hy2 Hy3 Hcp.
    rewrite proc_swap in Hcp.
    apply proc_assoc_2 in Hcp; auto.
    rewrite <- proc_swap in Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (old_cp_gamma & old_cp_delta1 & old_cp_delta2 & Hold_cp1 & Hold_cp2 & Hold_cp3 & Hold_cp4 & Hold_cp5 & Hold_cp6).
    rewrite <- proc_swap in Hold_cp4.
    cbn.
    rewrite <- Hold_cp6, Hold_cp2; constructor; auto.
  Qed.

  Lemma proc_assoc_4 :
  forall x y a b l1 l2 p q r senv,
  In x (proc_channels r) ->
  ~ In x l1 ->
  ~ In y (proc_channels p) ->
  cp (Proc_CompAndSplit x a l2 p (Proc_CompAndSplit y b l1 q r)) senv ->
  let new_l1 := filter (delta_name_split_func x p) (delta_channels y x r) in
  let new_l2 := filter (gamma_name_split_func y x r p) (gamma_channels y q) in
  cp (Proc_CompAndSplit y (dual b) new_l2 (Proc_CompAndSplit x a new_l1 p r) q) senv.
  Proof.
    intros x y a b l1 l2 p q r senv Hy1 Hy2 Hy3 Hcp.
    rewrite proc_swap in Hcp.
    apply proc_assoc_1 in Hcp; auto.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (old_cp_gamma & old_cp_delta1 & old_cp_delta2 & Hold_cp1 & Hold_cp2 & Hold_cp3 & Hold_cp4 & Hold_cp5 & Hold_cp6).
    rewrite <- proc_swap in Hold_cp5.
    cbn.
    rewrite <- Hold_cp6, Hold_cp2.
    rewrite (Permutation_app_comm old_cp_delta1).
    constructor; auto.
    2: rewrite dual_involute; auto.
    unfold senv_disjoint in Hold_cp3; unfold senv_disjoint.
    intros m; specialize (Hold_cp3 m); tauto.
  Qed.

  Lemma proc_cut_left_case :
  forall x t l p q r senv,
  cp (Proc_CompAndSplit x t l (Proc_OutLeft x p) (Proc_InCase x q r)) senv ->
  let (a, b) := match t with STyp_Plus a b => (a, b) | _ => (STyp_Zero, STyp_Zero) end in
  t = STyp_Plus a b /\
  cp (Proc_CompAndSplit x a l p q) senv.
  Proof.
    intros x t l p q r senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l.

    (* Invert Hcp'4 *)
    destruct (cp_inv_outleft _ _ _ Hcp'4) as (a' & b' & gamma' & Hcp''1 & Hcp''2).
    pose proof Hcp'4 as Hcp''3.
    apply cp_senv_valid in Hcp''3.
    rewrite senv_valid_cons in Hcp''3.
    assert (Hcp''4 : In (x, STyp_Plus a' b') ((x, t) :: gamma ++ delta1)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hcp''4.
    destruct Hcp''4 as [Hcp''4 | Hcp''4].
    2: apply (in_map fst) in Hcp''4; cbn in Hcp''4; tauto.
    injection Hcp''4; intros; subst t; clear Hcp''4.
    apply Permutation_cons_inv in Hcp''2.

    (* Invert Hcp'5 *)
    destruct (cp_inv_incase _ _ _ _ Hcp'5) as (a'' & b'' & gamma'' & Hcp'''1 & Hcp'''2 & Hcp'''3).
    pose proof Hcp'5 as Hcp'''4.
    apply cp_senv_valid in Hcp'''4.
    rewrite senv_valid_cons in Hcp'''4.
    cbn in Hcp'''3.
    assert (Hcp'''5 : In (x, STyp_With a'' b'') ((x, STyp_With (dual a') (dual b')) :: gamma ++ delta2)) by (rewrite <- Hcp'''3; left; auto).
    cbn in Hcp'''5.
    destruct Hcp'''5 as [Hcp'''5 | Hcp'''5].
    2: apply (in_map fst) in Hcp'''5; cbn in Hcp'''5; tauto.
    injection Hcp'''5; intros; subst a'' b''; clear Hcp'''5.
    apply Permutation_cons_inv in Hcp'''3.

    split; auto.
    rewrite <- Hcp'6.
    rewrite Hcp''2 in Hcp''1.
    rewrite Hcp'''3 in Hcp'''1.
    constructor; auto.
  Qed.

  Lemma proc_cut_right_case :
  forall x t l p q r senv,
  cp (Proc_CompAndSplit x t l (Proc_OutRight x p) (Proc_InCase x q r)) senv ->
  let (a, b) := match t with STyp_Plus a b => (a, b) | _ => (STyp_Zero, STyp_Zero) end in
  t = STyp_Plus a b /\
  cp (Proc_CompAndSplit x b l p r) senv.
  Proof.
    intros x t l p q r senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l.

    (* Invert Hcp'4 *)
    destruct (cp_inv_outright _ _ _ Hcp'4) as (a' & b' & gamma' & Hcp''1 & Hcp''2).
    pose proof Hcp'4 as Hcp''3.
    apply cp_senv_valid in Hcp''3.
    rewrite senv_valid_cons in Hcp''3.
    assert (Hcp''4 : In (x, STyp_Plus a' b') ((x, t) :: gamma ++ delta1)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hcp''4.
    destruct Hcp''4 as [Hcp''4 | Hcp''4].
    2: apply (in_map fst) in Hcp''4; cbn in Hcp''4; tauto.
    injection Hcp''4; intros; subst t; clear Hcp''4.
    apply Permutation_cons_inv in Hcp''2.

    (* Invert Hcp'5 *)
    destruct (cp_inv_incase _ _ _ _ Hcp'5) as (a'' & b'' & gamma'' & Hcp'''1 & Hcp'''2 & Hcp'''3).
    pose proof Hcp'5 as Hcp'''4.
    apply cp_senv_valid in Hcp'''4.
    rewrite senv_valid_cons in Hcp'''4.
    cbn in Hcp'''3.
    assert (Hcp'''5 : In (x, STyp_With a'' b'') ((x, STyp_With (dual a') (dual b')) :: gamma ++ delta2)) by (rewrite <- Hcp'''3; left; auto).
    cbn in Hcp'''5.
    destruct Hcp'''5 as [Hcp'''5 | Hcp'''5].
    2: apply (in_map fst) in Hcp'''5; cbn in Hcp'''5; tauto.
    injection Hcp'''5; intros; subst a'' b''; clear Hcp'''5.
    apply Permutation_cons_inv in Hcp'''3.

    split; auto.
    rewrite <- Hcp'6.
    rewrite Hcp''2 in Hcp''1.
    rewrite Hcp'''3 in Hcp'''2.
    constructor; auto.
  Qed.

  Lemma proc_cut_server_client :
  forall x t l y p z q senv,
  cp (Proc_CompAndSplit x t l (Proc_Server x y p) (Proc_Client x z q)) senv ->
  ~ In y (proc_forbidden q z) ->
  let a := match t with STyp_Excl a => a | _ => STyp_Zero end in
  t = STyp_Excl a /\
  cp (Proc_CompAndSplit y a l p (proc_rename q z y)) senv.
  Proof.
    intros x t l y p z q senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l.

    (* Invert Hcp'4 *)
    destruct (cp_inv_server _ _ _ _ Hcp'4) as (a' & gamma' & Hcp''1 & Hcp''2 & Hcp''3).
    pose proof Hcp'4 as Hcp''4.
    apply cp_senv_valid in Hcp''4.
    rewrite senv_valid_cons in Hcp''4.
    assert (Hcp''5 : In (x, STyp_Excl a') ((x, t) :: gamma ++ delta1)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hcp''5.
    destruct Hcp''5 as [Hcp''5 | Hcp''5].
    2: apply (in_map fst) in Hcp''5; cbn in Hcp''5; tauto.
    injection Hcp''5; intros Heq; subst t; clear Hcp''5.
    apply Permutation_cons_inv in Hcp''3.

    (* Invert Hcp'5 *)
    destruct (cp_inv_client _ _ _ _ Hcp'5) as (a'' & gamma'' & Hcp'''1 & Hcp'''2).
    pose proof Hcp'5 as Hcp'''3.
    apply cp_senv_valid in Hcp'''3.
    rewrite senv_valid_cons in Hcp'''3.
    cbn in Hcp'''2.
    assert (Hcp'''4 : In (x, STyp_Ques a'') ((x, STyp_Ques (dual a')) :: gamma ++ delta2)) by (rewrite <- Hcp'''2; left; auto).
    cbn in Hcp'''4.
    destruct Hcp'''4 as [Hcp'''4 | Hcp'''4].
    2: apply (in_map fst) in Hcp'''4; cbn in Hcp'''4; tauto.
    injection Hcp'''4; intros Heq; subst a''; clear Hcp'''4.
    apply Permutation_cons_inv in Hcp'''2.

    intros Hallow.
    assert (Hrename : cp (proc_rename q z y) ((y, dual a') :: gamma'')).
    { eapply cp_proc_rename in Hallow.
      2: apply Hcp'''1.
      cbn in Hallow.
      rewrite eqb_refl in Hallow.
      destruct Hallow as [(_ & Hrename) | (H & _)].
      2: tauto.
      fold (senv_rename gamma'' z y) in Hrename.
      rewrite senv_rename_nin in Hrename.
      2: apply cp_senv_valid in Hcp'''1; rewrite senv_valid_cons in Hcp'''1; tauto.
      auto.
    }

    cbn; split; auto.
    rewrite <- Hcp'6.
    rewrite Hcp''3 in Hcp''2.
    rewrite Hcp'''2 in Hrename.
    constructor; auto.
  Qed.

  Lemma proc_cut_server_null :
  forall x t l y p q senv,
  cp (Proc_CompAndSplit x t l (Proc_Server x y p) (Proc_ClientNull x q)) senv ->
  cp (weaken_list (filter (fun s => if in_dec eq_dec s l then false else true) (filter (fun s => negb (eqb y s)) (proc_channels p))) q) senv.
  Proof.
    intros x t l y p q senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l.

    (* Invert Hcp'4 *)
    destruct (cp_inv_server _ _ _ _ Hcp'4) as (a' & gamma' & Hcp''1 & Hcp''2 & Hcp''3).
    pose proof Hcp'4 as Hcp''4.
    apply cp_senv_valid in Hcp''4.
    rewrite senv_valid_cons in Hcp''4.
    assert (Hcp''5 : In (x, STyp_Excl a') ((x, t) :: gamma ++ delta1)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hcp''5.
    destruct Hcp''5 as [Hcp''5 | Hcp''5].
    2: apply (in_map fst) in Hcp''5; cbn in Hcp''5; tauto.
    injection Hcp''5; intros Heq; subst t; clear Hcp''5.
    apply Permutation_cons_inv in Hcp''3.

    (* Invert Hcp'5 *)
    destruct (cp_inv_client_null _ _ _ Hcp'5) as (a'' & gamma'' & Hcp'''1 & Hcp'''2).
    pose proof Hcp'5 as Hcp'''3.
    apply cp_senv_valid in Hcp'''3.
    rewrite senv_valid_cons in Hcp'''3.
    cbn in Hcp'''2.
    assert (Hcp'''4 : In (x, STyp_Ques a'') ((x, STyp_Ques (dual a')) :: gamma ++ delta2)) by (rewrite <- Hcp'''2; left; auto).
    cbn in Hcp'''4.
    destruct Hcp'''4 as [Hcp'''4 | Hcp'''4].
    2: apply (in_map fst) in Hcp'''4; cbn in Hcp'''4; tauto.
    injection Hcp'''4; intros Heq; subst a''; clear Hcp'''4.
    apply Permutation_cons_inv in Hcp'''2.

    remember (filter (fun s => negb (eqb y s)) (proc_channels p)) as l.
    pose proof (proc_channels_perm _ _ Hcp''2) as Hl1.
    cbn in Hl1.
    pose proof (Permutation_refl l) as Hl2.
    rewrite Heql in Hl2 at 1.
    rewrite <- Hl1 in Hl2.
    rewrite NoDup_filter_one in Hl2.
    2: apply eqb_spec.
    2: apply cp_senv_valid in Hcp''2; auto.
    pose proof (map_permutation_ex _ _ _ Hl2) as (L & HL1 & HL2).
    rewrite HL2 in Heql; subst l; clear Hl2.
    rewrite Hcp''3 in HL1.

    remember (filter (fun s => if in_dec eq_dec s (map fst gamma) then false else true) (map fst L)) as l'.
    pose proof (Permutation_refl l') as Hl'1.
    rewrite Heql' in Hl'1 at 1.
    rewrite <- HL1 in Hl'1.
    rewrite map_app in Hl'1.
    rewrite NoDup_filter_app in Hl'1.
    2: rewrite <- map_app; rewrite Hcp''3 in Hcp''2; apply cp_senv_valid in Hcp''2; rewrite senv_valid_cons in Hcp''2; apply Hcp''2.
    pose proof (map_permutation_ex _ _ _ Hl'1) as (L' & HL'1 & HL'2).
    rewrite HL'2 in Heql'; subst l'.

    rewrite <- Hcp'6.
    rewrite Permutation_app_swap_app.
    rewrite HL'1.
    rewrite Hcp'''2 in Hcp'''1.
    rewrite Hcp''3 in Hcp''2.
    apply weaken_list_correct; auto.

    - unfold senv_valid.
      rewrite <- HL'1.
      apply cp_senv_valid in Hcp''2.
      rewrite senv_valid_cons in Hcp''2.
      destruct Hcp''2 as (_ & Hcp''2).
      apply senv_app in Hcp''2.
      apply Hcp''2.

    - rewrite <- HL'1.
      rewrite Hcp''3 in Hcp''1.
      rewrite map_app, Forall_app in Hcp''1.
      tauto.

    - unfold senv_disjoint.
      intros z.
      rewrite <- HL'1.
      rewrite <- Hcp'6 in Hcp.
      rewrite Permutation_app_swap_app in Hcp.
      apply cp_senv_valid in Hcp.
      apply senv_app in Hcp.
      destruct Hcp as (_ & _ & Hcp).
      apply (Hcp z).
  Qed.

  Lemma proc_cut_server_split :
  forall x t l y p z q senv,
  cp (Proc_CompAndSplit x t l (Proc_Server x y p) (Proc_ClientSplit x z q)) senv ->
  ~ In z (proc_forbidden (Proc_Server x y p) x) ->
  let l' := filter (fun s => negb (eqb x s)) (proc_channels (Proc_Server x y p)) in
  cp (Proc_CompAndSplit x t l' (Proc_Server x y p) (Proc_CompAndSplit z t l (proc_rename (Proc_Server x y p) x z) q)) senv.
  Proof.
    intros x t l y p' z q senv Hcp.
    remember (Proc_Server x y p') as p.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l.

    (* Invert Hcp'4 *)
    rewrite Heqp in Hcp'4.
    destruct (cp_inv_server _ _ _ _ Hcp'4) as (a' & gamma' & Hcp''1 & Hcp''2 & Hcp''3).
    pose proof Hcp'4 as Hcp''4.
    apply cp_senv_valid in Hcp''4.
    rewrite senv_valid_cons in Hcp''4.
    assert (Hcp''5 : In (x, STyp_Excl a') ((x, t) :: gamma ++ delta1)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hcp''5.
    destruct Hcp''5 as [Hcp''5 | Hcp''5].
    2: apply (in_map fst) in Hcp''5; cbn in Hcp''5; tauto.
    injection Hcp''5; intros Heq; subst t; clear Hcp''5.
    apply Permutation_cons_inv in Hcp''3.

    (* Invert Hcp'5 *)
    destruct (cp_inv_client_split _ _ _ _ Hcp'5) as (a'' & gamma'' & Hcp'''1 & Hcp'''2).
    pose proof Hcp'5 as Hcp'''3.
    apply cp_senv_valid in Hcp'''3.
    rewrite senv_valid_cons in Hcp'''3.
    cbn in Hcp'''2.
    assert (Hcp'''4 : In (x, STyp_Ques a'') ((x, STyp_Ques (dual a')) :: gamma ++ delta2)) by (rewrite <- Hcp'''2; left; auto).
    cbn in Hcp'''4.
    destruct Hcp'''4 as [Hcp'''4 | Hcp'''4].
    2: apply (in_map fst) in Hcp'''4; cbn in Hcp'''4; tauto.
    injection Hcp'''4; intros Heq; subst a''; clear Hcp'''4.
    apply Permutation_cons_inv in Hcp'''2.

    intros Hallow.
    assert (Hrename : cp (proc_rename p x z) ((z, STyp_Excl a') :: gamma ++ delta1)).
    { eapply cp_proc_rename in Hallow.
      2: rewrite Heqp; apply Hcp'4.
      cbn in Hallow.
      rewrite eqb_refl in Hallow.
      destruct Hallow as [(_ & Hrename) | (H & _)].
      2: tauto.
      fold (senv_rename (gamma ++ delta1) x z) in Hrename.
      rewrite senv_rename_nin in Hrename.
      2: apply cp_senv_valid in Hcp'4; rewrite senv_valid_cons in Hcp'4; tauto.
      auto.
    }

    remember (filter (fun s => negb (eqb x s)) (proc_channels p)) as l.
    rewrite Heqp in Heql.
    pose proof (proc_channels_perm _ _ Hcp'4) as Hl1.
    pose proof (Permutation_refl l) as Hl2.
    rewrite Heql in Hl2 at 1.
    rewrite <- Hl1 in Hl2.
    cbn [map fst] in Hl2.
    rewrite NoDup_filter_one in Hl2.
    2: apply eqb_spec.
    2: apply cp_senv_valid in Hcp'4; auto.
    pose proof (map_permutation_ex _ _ _ Hl2) as (L & HL1 & HL2).
    rewrite HL2 in Heql; subst l; clear Hl2.

    cbn.
    rewrite perm_swap in Hcp'''1.
    rewrite Hcp'''2 in Hcp'''1.
    rewrite Permutation_middle in Hcp'''1.

    assert (Hnew_cp : cp (Proc_CompAndSplit z (STyp_Excl a') (map fst gamma) (proc_rename p x z) q) (gamma ++ delta1 ++ (x, STyp_Ques (dual a')) :: delta2)).
    { constructor; auto.
      - unfold senv_disjoint.
        intros w Hw; cbn.
        intros Hin.
        destruct Hin as [Hin | Hin].
        + subst w.
          apply cp_senv_valid in Hcp'4.
          rewrite senv_valid_cons in Hcp'4.
          rewrite map_app, in_app_iff in Hcp'4.
          tauto.
        + rewrite <- Hcp'6 in Hcp.
          rewrite app_assoc in Hcp.
          apply cp_senv_valid in Hcp.
          apply senv_app in Hcp.
          destruct Hcp as (_ & _ & Hcp).
          specialize (Hcp w ltac:(rewrite map_app, in_app_iff; tauto)).
          tauto.
    }

    rewrite <- Hcp'6.
    rewrite app_assoc.
    rewrite HL1.
    rewrite app_assoc in Hnew_cp.
    rewrite Permutation_app_comm in Hnew_cp.
    cbn in Hnew_cp.
    rewrite Permutation_app_comm in Hnew_cp.
    rewrite HL1 in Hnew_cp.
    rewrite HL1 in Hcp'4.
    replace delta2 with ([] ++ delta2) by auto.

    constructor; auto.
    - rewrite <- HL1, <- Hcp''3; auto.
    - unfold senv_disjoint; intros; auto.
    - rewrite Heqp, app_nil_r; auto.
  Qed.

  Lemma proc_cut_forall_exists :
  forall x t l a v b p v' a' q senv,
  cp (Proc_CompAndSplit x t l (Proc_OutTyp x a v b p) (Proc_InTyp x v' a' q)) senv ->
  t = STyp_Exists v b /\
  v' = v /\
  a' = dual b /\
  (Forall (fun v'' => proc_var_subst_pre q v' v'') (fvar a) ->
   cp (Proc_CompAndSplit x (styp_subst v b a) l p (proc_var_subst q v' a)) senv).
  Proof.
    intros x t l a v b p v' a' q senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l.

    (* Invert Hcp'4 *)
    destruct (cp_inv_outtyp _ _ _ _ _ _ Hcp'4) as (gamma' & Hcp''1 & Hcp''2 & Hcp''3).
    pose proof Hcp'4 as Hcp''4.
    apply cp_senv_valid in Hcp''4.
    rewrite senv_valid_cons in Hcp''4.
    assert (Hcp''5 : In (x, STyp_Exists v b) ((x, t) :: gamma ++ delta1)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hcp''5.
    destruct Hcp''5 as [Hcp''5 | Hcp''5].
    2: apply (in_map fst) in Hcp''5; cbn in Hcp''5; tauto.
    injection Hcp''5; intros; subst t; clear Hcp''5.
    apply Permutation_cons_inv in Hcp''3.

    (* Invert Hcp'5 *)
    destruct (cp_inv_intyp _ _ _ _ _ Hcp'5) as (delta' & Hcp'''1 & Hcp'''2 & Hcp'''3).
    pose proof Hcp'5 as Hcp'''4.
    apply cp_senv_valid in Hcp'''4.
    rewrite senv_valid_cons in Hcp'''4.
    cbn in Hcp'''3.
    assert (Hcp'''5 : In (x, STyp_Forall v' a') ((x, STyp_Forall v (dual b)) :: gamma ++ delta2)) by (rewrite <- Hcp'''3; left; auto).
    cbn in Hcp'''5.
    destruct Hcp'''5 as [Hcp'''5 | Hcp'''5].
    2: apply (in_map fst) in Hcp'''5; cbn in Hcp'''5; tauto.
    injection Hcp'''5; intros; subst v' a'; clear Hcp'''5.
    apply Permutation_cons_inv in Hcp'''3.

    repeat split; auto.
    intros Hpre.
    pose proof (cp_var_subst _ v a _ Hcp'''2) as Hsubst.

    match type of Hsubst with ?P -> _ => assert (H : P) end.
    { cbn.
      apply Forall_cons.
      1: unfold styp_forbidden in Hcp''1; rewrite styp_forbidden_dual in Hcp''1; auto.
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

    rewrite <- Hcp'6.
    rewrite Hcp''3 in Hcp''2.
    rewrite Hcp'''3 in Hcp'''2.
    rewrite Hcp'''3 in Hsubst.
    constructor; auto.
    rewrite styp_subst_dual; auto.
  Qed.

End Wadler_Transformation.
