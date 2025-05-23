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

  (* Weaken a process by a list of channels *)
  Fixpoint weaken_list (L : SEnv) (p : Process) :=
  match L with
  | [] => p
  | (x, t) :: rest => Proc_ClientNull x (match t with STyp_Ques t => t | _ => STyp_Zero end) (weaken_list rest p)
  end.

  Lemma weaken_list_correct :
  forall p gamma delta,
  senv_valid gamma ->
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd gamma) ->
  senv_disjoint gamma delta ->
  cp p delta ->
  cp (weaken_list gamma p) (gamma ++ delta).
  Proof.
    intros p gamma delta.
    induction gamma.
    - cbn; auto.
    - intros Hgamma1.
      destruct a as [x t].
      specialize (IHgamma ltac:(eauto with senv_valid)).
      assert (Hx : ~ In x (map fst gamma)) by eauto with senv_valid.

      intros Hgamma2.
      cbn in Hgamma2.
      rewrite Forall_cons_iff in Hgamma2.
      specialize (IHgamma ltac:(tauto)).
      destruct Hgamma2 as (Hgamma2 & _).

      intros Hgamma3.
      unfold senv_disjoint in Hgamma3.
      cbn in Hgamma3.
      specialize (IHgamma ltac:(intros w; specialize (Hgamma3 w); tauto)).
      specialize (Hgamma3 x ltac:(auto)).

      intros Hcp; specialize (IHgamma Hcp).

      cbn.
      destruct t; try contradiction.
      constructor; auto.
      rewrite map_app, in_app_iff; tauto.
  Qed.

  Lemma cp_inv_link :
  forall w x a senv,
  cp (Proc_Link w x a) senv ->
  Permutation [(w, dual a); (x, a)] senv.
  Proof.
    intros w x a senv Hcp.
    remember (Proc_Link w x a) as r.
    revert w x a Heqr.
    induction Hcp; try discriminate.
    - intros w' x' a'; intros Heq; injection Heq; intros; subst w' x' a'.
      apply Permutation_refl.
    - intros w' x' a'; intros Heq; specialize (IHHcp _ _ _ Heq).
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

  Lemma cp_inv_outch :
  forall x y p q senv,
  cp (Proc_OutCh x y p q) senv ->
  exists a b gamma delta,
    ~ In x (map fst gamma) /\
    senv_disjoint gamma delta /\
    cp p ((y, a) :: gamma) /\
    cp q ((x, b) :: delta) /\
    Permutation ((x, STyp_Times a b) :: gamma ++ delta) senv.
  Proof.
    intros x y p q senv Hcp.
    remember (Proc_OutCh x y p q) as r.
    revert x y p q Heqr.
    induction Hcp; try discriminate.
    - intros x' y' p' q'; intros Heq; injection Heq; intros; subst x' y' p' q'.
      exists a; exists b; exists gamma; exists delta; repeat split; auto.
    - intros x' y' p' q'; intros Heq; specialize (IHHcp _ _ _ _ Heq).
      destruct IHHcp as (a & b & senv1 & senv2 & IHHcp); exists a; exists b; exists senv1; exists senv2.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_outch_and_split :
  forall x y l p q senv,
  cp (Proc_OutChAndSplit x y l p q) senv ->
  exists a b gamma delta1 delta2,
    Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd gamma) /\
    l = map fst gamma /\
    ~ In x (map fst delta1) /\
    senv_disjoint delta1 delta2 /\
    cp p ((y, a) :: gamma ++ delta1) /\
    cp q ((x, b) :: gamma ++ delta2) /\
    Permutation ((x, STyp_Times a b) :: gamma ++ delta1 ++ delta2) senv.
  Proof.
    intros x y l p q senv Hcp.
    remember (Proc_OutChAndSplit x y l p q) as r.
    revert x y l p q Heqr.
    induction Hcp; try discriminate.
    - intros x' y' l' p' q'; intros Heq; injection Heq; intros; subst x' y' l' p' q'.
      exists a; exists b; exists gamma; exists delta1; exists delta2; repeat split; auto.
    - intros x' y' l' p' q'; intros Heq; specialize (IHHcp _ _ _ _ _ Heq).
      destruct IHHcp as (a & b & senv1 & senv2 & senv3 & IHHcp); exists a; exists b; exists senv1; exists senv2; exists senv3.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_inch :
  forall x y p senv,
  cp (Proc_InCh x y p) senv ->
  exists a b gamma,
    cp p ((x, b) :: (y, a) :: gamma) /\
    Permutation ((x, STyp_Par a b) :: gamma) senv.
  Proof.
    intros x y p senv Hcp.
    remember (Proc_InCh x y p) as r.
    revert x y p Heqr.
    induction Hcp; try discriminate.
    - intros x' y' p'; intros Heq; injection Heq; intros; subst x' y' p'.
      exists a; exists b; exists gamma; repeat split; auto.
    - intros x' y' p'; intros Heq; specialize (IHHcp _ _ _ Heq).
      destruct IHHcp as (a & b & senv & IHHcp); exists a; exists b; exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_outleft :
  forall x b p senv,
  cp (Proc_OutLeft x b p) senv ->
  exists a gamma,
    cp p ((x, a) :: gamma) /\
    Permutation ((x, STyp_Plus a b) :: gamma) senv.
  Proof.
    intros x b p senv Hcp.
    remember (Proc_OutLeft x b p) as r.
    revert x b p Heqr.
    induction Hcp; try discriminate.
    - intros x' b' p'; intros Heq; injection Heq; intros; subst x' b' p'.
      exists a; exists gamma; repeat split; auto.
    - intros x' b' p'; intros Heq; specialize (IHHcp _ _ _ Heq).
      destruct IHHcp as (a & senv & IHHcp); exists a; exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_outright :
  forall x a p senv,
  cp (Proc_OutRight x a p) senv ->
  exists b gamma,
    cp p ((x, b) :: gamma) /\
    Permutation ((x, STyp_Plus a b) :: gamma) senv.
  Proof.
    intros x a p senv Hcp.
    remember (Proc_OutRight x a p) as r.
    revert x a p Heqr.
    induction Hcp; try discriminate.
    - intros x' a' p'; intros Heq; injection Heq; intros; subst x' a' p'.
      exists b; exists gamma; repeat split; auto.
    - intros x' a' p'; intros Heq; specialize (IHHcp _ _ _ Heq).
      destruct IHHcp as (b & senv & IHHcp); exists b; exists senv.
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
  Proof.
    intros x y p senv Hcp.
    remember (Proc_Server x y p) as r.
    revert x y p Heqr.
    induction Hcp; try discriminate.
    - intros x' y' p'; intros Heq; injection Heq; intros; subst x' y' p'.
      exists a; exists gamma; repeat split; auto.
    - intros x' y' p'; intros Heq; specialize (IHHcp _ _ _ Heq).
      destruct IHHcp as (a & senv & IHHcp); exists a; exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_client :
  forall x y p senv,
  cp (Proc_Client x y p) senv ->
  exists a gamma,
    cp p ((y, a) :: gamma) /\
    Permutation ((x, STyp_Ques a) :: gamma) senv.
  Proof.
    intros x y p senv Hcp.
    remember (Proc_Client x y p) as r.
    revert x y p Heqr.
    induction Hcp; try discriminate.
    - intros x' y' p'; intros Heq; injection Heq; intros; subst x' y' p'.
      exists a; exists gamma; repeat split; auto.
    - intros x' y' p'; intros Heq; specialize (IHHcp _ _ _ Heq).
      destruct IHHcp as (a & senv & IHHcp); exists a; exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_client_null :
  forall x a p senv,
  cp (Proc_ClientNull x a p) senv ->
  exists gamma,
    cp p gamma /\
    Permutation ((x, STyp_Ques a) :: gamma) senv.
  Proof.
    intros x a p senv Hcp.
    remember (Proc_ClientNull x a p) as r.
    revert x a p Heqr.
    induction Hcp; try discriminate.
    - intros x' a' p'; intros Heq; injection Heq; intros; subst x' a' p'.
      exists gamma; repeat split; auto.
    - intros x' a' p'; intros Heq; specialize (IHHcp _ _ _ Heq).
      destruct IHHcp as (senv & IHHcp); exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_client_split :
  forall x y p senv,
  cp (Proc_ClientSplit x y p) senv ->
  exists a gamma,
    cp p ((x, STyp_Ques a) :: (y, STyp_Ques a) :: gamma) /\
    Permutation ((x, STyp_Ques a) :: gamma) senv.
  Proof.
    intros x y p senv Hcp.
    remember (Proc_ClientSplit x y p) as r.
    revert x y p Heqr.
    induction Hcp; try discriminate.
    - intros x' y' p'; intros Heq; injection Heq; intros; subst x' y' p'.
      exists a; exists gamma; repeat split; auto.
    - intros x' y' p'; intros Heq; specialize (IHHcp _ _ _ Heq).
      destruct IHHcp as (a & senv & IHHcp); exists a; exists senv.
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
  forall x v p senv,
  cp (Proc_InTyp x v p) senv ->
  exists a gamma,
    Forall (fun r => ~ In v (fvar r)) (map snd gamma) /\
    cp p ((x, a) :: gamma) /\
    Permutation ((x, STyp_Forall v a) :: gamma) senv.
  Proof.
    intros x v p senv Hcp.
    remember (Proc_InTyp x v p) as r.
    revert x v p Heqr.
    induction Hcp; try discriminate.
    - intros x' v' p'; intros Heq; injection Heq; intros; subst x' v' p'.
      exists a; exists gamma; repeat split; auto.
    - intros x' v' p'; intros Heq; specialize (IHHcp _ _ _ Heq).
      destruct IHHcp as (a & senv & IHHcp); exists a; exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_intyp_rename :
  forall x v v' p senv,
  cp (Proc_InTypRename x v v' p) senv ->
  exists a gamma,
    ~ In v' (styp_forbidden a v) /\
    ~ In v' (fvar a) /\
    cp p ((x, STyp_Forall v a) :: gamma) /\
    Permutation ((x, STyp_Forall v' (styp_subst v a (STyp_Var v'))) :: gamma) senv.
  Proof.
    intros x v v' p senv Hcp.
    remember (Proc_InTypRename x v v' p) as r.
    revert x v v' p Heqr.
    induction Hcp; try discriminate.
    - intros x' w' w'' p'; intros Heq; injection Heq; intros; subst x' w' w'' p'.
      exists a; exists gamma; repeat split; auto.
    - intros x' w' w'' p'; intros Heq; specialize (IHHcp _ _ _ _ Heq).
      destruct IHHcp as (a & senv & IHHcp); exists a; exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_outunit :
  forall x senv,
  cp (Proc_OutUnit x) senv ->
  senv = [(x, STyp_One)].
  Proof.
    intros x senv Hcp.
    remember (Proc_OutUnit x) as r.
    revert x Heqr.
    induction Hcp; try discriminate.
    - intros x' Heq; injection Heq; intros; subst x'; auto.
    - intros x' Heq; specialize (IHHcp _ Heq).
      subst p gamma.
      apply Permutation_length in H as H'.
      cbn in H'.
      destruct gamma'; try discriminate.
      cbn in H'.
      destruct gamma'; try discriminate; clear H'.
      apply Permutation_length_1 in H; subst p.
      auto.
  Qed.

  Lemma cp_inv_inunit :
  forall x p senv,
  cp (Proc_InUnit x p) senv ->
  exists gamma,
    cp p gamma /\
    Permutation ((x, STyp_Bot) :: gamma) senv.
  Proof.
    intros x p senv Hcp.
    remember (Proc_InUnit x p) as r.
    revert x p Heqr.
    induction Hcp; try discriminate.
    - intros x' p'; intros Heq; injection Heq; intros; subst x' p'.
      exists gamma; repeat split; auto.
    - intros x' p'; intros Heq; specialize (IHHcp _ _ Heq).
      destruct IHHcp as (senv & IHHcp); exists senv.
      repeat split; try apply IHHcp.
      rewrite <- H; apply IHHcp.
  Qed.

  Lemma cp_inv_emptycase :
  forall x l senv,
  cp (Proc_EmptyCase x l) senv ->
  Permutation ((x, STyp_Top) :: l) senv.
  Proof.
    intros x l senv Hcp.
    remember (Proc_EmptyCase x l) as r.
    revert x l Heqr.
    induction Hcp; try discriminate.
    - intros x' l'; intros Heq; injection Heq; intros; subst x' l'.
      auto.
    - intros x' l'; intros Heq; specialize (IHHcp _ _ Heq).
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

  Lemma proc_outch_and_split_empty :
  forall x y p q senv,
  cp (Proc_OutChAndSplit x y [] p q) senv <->
  cp (Proc_OutCh x y p q) senv.
  Proof.
    intros x y p q senv.
    split; intros Hcp.
    - destruct (cp_inv_outch_and_split _ _ _ _ _ _ Hcp) as (a & b & gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6 & Hcp'7).
      symmetry in Hcp'2.
      apply map_eq_nil in Hcp'2; subst gamma.
      cbn in Hcp'5, Hcp'6, Hcp'7.
      rewrite <- Hcp'7.
      constructor; auto.
    - destruct (cp_inv_outch _ _ _ _ _ Hcp) as (a & b & gamma & delta & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5).
      rewrite <- Hcp'5.
      rewrite <- (app_nil_l gamma).
      rewrite <- app_assoc.
      eassert (Hnil : [] = _).
      2: rewrite Hnil.
      2: constructor; auto.
      cbn; auto.
  Qed.

  (* Two processes are typing-equivalent if whenever one process is typed by senv, the other process can also be typed by senv *)
  Definition proc_equiv p q : Prop := forall senv, cp p senv <-> cp q senv.

  #[export] Instance proc_equiv_Equivalence : Equivalence proc_equiv.
  Proof.
    constructor.
    - intros p senv; tauto.
    - intros p q; unfold proc_equiv; firstorder.
    - intros p q r; unfold proc_equiv; firstorder.
  Qed.

  #[export] Instance prov_equiv_proper : Proper (proc_equiv ==> @Logic.eq SEnv ==> iff) (fun p senv => cp p senv).
  Proof. intros p q Hequiv senv senv' Heq; subst; apply Hequiv. Qed.

  #[export] Instance cp_comp_and_split_proper : Proper (@Logic.eq (chn) ==> @Logic.eq (STyp) ==> @Permutation (chn) ==> @Logic.eq (Process) ==> @Logic.eq (Process) ==> proc_equiv) (fun x t l p q => Proc_CompAndSplit x t l p q).
  Proof.
    intros x x' Heq; subst x'.
    intros t t' Heq; subst t'.
    intros l l' Hperm.
    intros p p' Heq; subst p'.
    intros q q' Heq; subst q'.
    split; intros Hcp.
    all: destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6); subst.
    all: rewrite <- Hcp6.
    2: symmetry in Hperm.
    all: pose proof (map_permutation_ex _ _ _ Hperm) as (L' & HL'1 & HL'2); subst.
    all: rewrite HL'1; rewrite HL'1 in Hcp4, Hcp5.
    all: constructor; auto.
    all: rewrite <- HL'1; auto.
  Qed.

  #[export] Instance cp_outch_and_split_proper : Proper (@Logic.eq (chn) ==> @Logic.eq (chn) ==> @Permutation (chn) ==> @Logic.eq (Process) ==> @Logic.eq (Process) ==> proc_equiv) (fun x y l p q => Proc_OutChAndSplit x y l p q).
  Proof.
    intros x x' Heq; subst x'.
    intros y y' Heq; subst y'.
    intros l l' Hperm.
    intros p p' Heq; subst p'.
    intros q q' Heq; subst q'.
    split; intros Hcp.
    all: destruct (cp_inv_outch_and_split _ _ _ _ _ _ Hcp) as (a & b & gamma & delta1 & delta2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6 & Hcp7); subst.
    all: rewrite <- Hcp7.
    2: symmetry in Hperm.
    all: pose proof (map_permutation_ex _ _ _ Hperm) as (L' & HL'1 & HL'2); subst.
    all: rewrite HL'1; rewrite HL'1 in Hcp5, Hcp6.
    all: constructor; auto.
    all: rewrite <- HL'1; auto.
  Qed.

  #[export] Instance cp_emptycase_proper :
  Proper (@Logic.eq (chn) ==> @Permutation (chn * STyp) ==> proc_equiv) (fun y l => Proc_EmptyCase y l).
  Proof.
    intros y y' Heq; subst y'.
    intros l l' Hperm.
    split; intros Hcp.
    all: rewrite <- (cp_inv_emptycase _ _ _ Hcp).
    all: rewrite <- (cp_inv_emptycase _ _ _ Hcp) in Hcp.
    2: symmetry in Hperm.
    all: rewrite Hperm; constructor; auto.
    all: rewrite <- Hperm.
    all: eauto with senv_valid.
  Qed.

  #[export] Instance cp_cut_contract_proper :
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv ==> proc_equiv) (fun x a l p q => Proc_CompAndSplit x a l p q).
  Proof.
    intros x x' Heq; subst x'.
    intros a a' Heq; subst a'.
    intros l l' Heq; subst l'.
    intros p p' Hequiv1.
    intros q q' Hequiv2.
    unfold proc_equiv in Hequiv1, Hequiv2.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6); subst l.
      rewrite Hequiv1 in Hcp'4.
      rewrite Hequiv2 in Hcp'5.
      rewrite <- Hcp'6.
      constructor; auto.
    - destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6); subst l.
      rewrite <- Hequiv1 in Hcp'4.
      rewrite <- Hequiv2 in Hcp'5.
      rewrite <- Hcp'6.
      constructor; auto.
  Qed.

  #[export] Instance cp_cut_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv ==> proc_equiv) (fun x a p q => Proc_Comp x a p q).
  Proof.
    intros x x' Heq; subst x'.
    intros a a' Heq; subst a'.
    intros p p' Hequiv1.
    intros q q' Hequiv2.
    intros senv.
    do 2 rewrite <- proc_comp_and_split_empty.
    apply cp_cut_contract_proper; auto.
  Qed.

  #[export] Instance cp_times_contract_proper :
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv ==> proc_equiv) (fun x y l p q => Proc_OutChAndSplit x y l p q).
  Proof.
    intros x x' Heq; subst x'.
    intros y y' Heq; subst y'.
    intros l l' Heq; subst l'.
    intros p p' Hequiv1.
    intros q q' Hequiv2.
    unfold proc_equiv in Hequiv1, Hequiv2.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_outch_and_split _ _ _ _ _ _ Hcp) as (a & b & gamma & delta & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6 & Hcp'7 & Hcp'8); subst l.
      rewrite Hequiv1 in Hcp'6.
      rewrite Hequiv2 in Hcp'7.
      rewrite <- Hcp'8.
      constructor; auto.
    - destruct (cp_inv_outch_and_split _ _ _ _ _ _ Hcp) as (a & b & gamma & delta & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6 & Hcp'7 & Hcp'8); subst l.
      rewrite <- Hequiv1 in Hcp'6.
      rewrite <- Hequiv2 in Hcp'7.
      rewrite <- Hcp'8.
      constructor; auto.
  Qed.

  #[export] Instance cp_times_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv ==> proc_equiv) (fun x y p q => Proc_OutCh x y p q).
  Proof.
    intros x x' Heq; subst x'.
    intros y y' Heq; subst y'.
    intros p p' Hequiv1.
    intros q q' Hequiv2.
    intros senv.
    do 2 rewrite <- proc_outch_and_split_empty.
    apply cp_times_contract_proper; auto.
  Qed.

  #[export] Instance cp_inch_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x y p => Proc_InCh x y p).
  Proof.
    intros x x' Heq; subst x'.
    intros y y' Heq; subst y'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_inch _ _ _ _ Hcp) as (a & b & gamma & Hcp'1 & Hcp'2).
      rewrite Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
    - destruct (cp_inv_inch _ _ _ _ Hcp) as (a & b & gamma & Hcp'1 & Hcp'2).
      rewrite <- Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
  Qed.

  #[export] Instance cp_outleft_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x b p => Proc_OutLeft x b p).
  Proof.
    intros x x' Heq; subst x'.
    intros b b' Heq; subst b'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_outleft _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2).
      rewrite Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
    - destruct (cp_inv_outleft _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2).
      rewrite <- Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
  Qed.

  #[export] Instance cp_outright_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x a p => Proc_OutRight x a p).
  Proof.
    intros x x' Heq; subst x'.
    intros a a' Heq; subst a'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_outright _ _ _ _ Hcp) as (b & gamma & Hcp'1 & Hcp'2).
      rewrite Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
    - destruct (cp_inv_outright _ _ _ _ Hcp) as (b & gamma & Hcp'1 & Hcp'2).
      rewrite <- Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
  Qed.

  #[export] Instance cp_with_proper :
  Proper (Logic.eq ==> proc_equiv ==> proc_equiv ==> proc_equiv) (fun x p q => Proc_InCase x p q).
  Proof.
    intros x x' Heq; subst x'.
    intros p p' Hequiv1.
    intros q q' Hequiv2.
    unfold proc_equiv in Hequiv1, Hequiv2.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_incase _ _ _ _ Hcp) as (a & b & gamma & Hcp'1 & Hcp'2 & Hcp'3).
      rewrite Hequiv1 in Hcp'1.
      rewrite Hequiv2 in Hcp'2.
      rewrite <- Hcp'3.
      constructor; auto.
    - destruct (cp_inv_incase _ _ _ _ Hcp) as (a & b & gamma & Hcp'1 & Hcp'2 & Hcp'3).
      rewrite <- Hequiv1 in Hcp'1.
      rewrite <- Hequiv2 in Hcp'2.
      rewrite <- Hcp'3.
      constructor; auto.
  Qed.

  #[export] Instance cp_excl_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x y p => Proc_Server x y p).
  Proof.
    intros x x' Heq; subst x'.
    intros y y' Heq; subst y'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_server _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2 & Hcp'3).
      rewrite Hequiv in Hcp'2.
      rewrite <- Hcp'3.
      constructor; auto.
      rewrite <- Hcp'3 in Hcp; eauto with senv_valid.
    - destruct (cp_inv_server _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2 & Hcp'3).
      rewrite <- Hequiv in Hcp'2.
      rewrite <- Hcp'3.
      constructor; auto.
      rewrite <- Hcp'3 in Hcp; eauto with senv_valid.
  Qed.

  #[export] Instance cp_ques_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x y p => Proc_Client x y p).
  Proof.
    intros x x' Heq; subst x'.
    intros y y' Heq; subst y'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_client _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2).
      rewrite Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
      rewrite <- Hcp'2 in Hcp; eauto with senv_valid.
    - destruct (cp_inv_client _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2).
      rewrite <- Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
      rewrite <- Hcp'2 in Hcp; eauto with senv_valid.
  Qed.

  #[export] Instance cp_weaken_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x a p => Proc_ClientNull x a p).
  Proof.
    intros x x' Heq; subst x'.
    intros a a' Heq; subst a'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_client_null _ _ _ _ Hcp) as (gamma & Hcp'1 & Hcp'2).
      rewrite Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
      rewrite <- Hcp'2 in Hcp; eauto with senv_valid.
    - destruct (cp_inv_client_null _ _ _ _ Hcp) as (gamma & Hcp'1 & Hcp'2).
      rewrite <- Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
      rewrite <- Hcp'2 in Hcp; eauto with senv_valid.
  Qed.

  #[export] Instance cp_contract_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x y p => Proc_ClientSplit x y p).
  Proof.
    intros x x' Heq; subst x'.
    intros y y' Heq; subst y'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_client_split _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2).
      rewrite Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
    - destruct (cp_inv_client_split _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2).
      rewrite <- Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
  Qed.

  #[export] Instance cp_exists_proper :
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq  ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x a v b p => Proc_OutTyp x a v b p).
  Proof.
    intros x x' Heq; subst x'.
    intros a a' Heq; subst a'.
    intros v v' Heq; subst v'.
    intros b b' Heq; subst b'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_outtyp _ _ _ _ _ _ Hcp) as (gamma & Hcp'1 & Hcp'2 & Hcp'3).
      rewrite Hequiv in Hcp'2.
      rewrite <- Hcp'3.
      constructor; auto.
    - destruct (cp_inv_outtyp _ _ _ _ _ _ Hcp) as (gamma & Hcp'1 & Hcp'2 & Hcp'3).
      rewrite <- Hequiv in Hcp'2.
      rewrite <- Hcp'3.
      constructor; auto.
  Qed.

  #[export] Instance cp_forall_proper :
  Proper (Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x v p => Proc_InTyp x v p).
  Proof.
    intros x x' Heq; subst x'.
    intros v v' Heq; subst v'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_intyp _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2 & Hcp'3).
      rewrite Hequiv in Hcp'2.
      rewrite <- Hcp'3.
      constructor; auto.
    - destruct (cp_inv_intyp _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2 & Hcp'3).
      rewrite <- Hequiv in Hcp'2.
      rewrite <- Hcp'3.
      constructor; auto.
  Qed.

  #[export] Instance cp_forall_rename_proper :
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> proc_equiv ==> proc_equiv) (fun x v v' p => Proc_InTypRename x v v' p).
  Proof.
    intros x x' Heq; subst x'.
    intros v v' Heq; subst v'.
    intros v' v'' Heq; subst v''.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_intyp_rename _ _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4).
      rewrite Hequiv in Hcp'3.
      rewrite <- Hcp'4.
      constructor; auto.
    - destruct (cp_inv_intyp_rename _ _ _ _ _ Hcp) as (a & gamma & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4).
      rewrite <- Hequiv in Hcp'3.
      rewrite <- Hcp'4.
      constructor; auto.
  Qed.

  #[export] Instance cp_bot_proper :
  Proper (Logic.eq ==> proc_equiv ==> proc_equiv) (fun x p => Proc_InUnit x p).
  Proof.
    intros x x' Heq; subst x'.
    intros p p' Hequiv.
    unfold proc_equiv in Hequiv.
    intros senv; split; intros Hcp.
    - destruct (cp_inv_inunit _ _ _ Hcp) as (gamma & Hcp'1 & Hcp'2).
      rewrite Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
      rewrite <- Hcp'2 in Hcp; eauto with senv_valid.
    - destruct (cp_inv_inunit _ _ _ Hcp) as (gamma & Hcp'1 & Hcp'2).
      rewrite <- Hequiv in Hcp'1.
      rewrite <- Hcp'2.
      constructor; auto.
      rewrite <- Hcp'2 in Hcp; eauto with senv_valid.
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
      apply senv_disjoint_sym; auto.

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

  Lemma proc_swap_equiv :
  forall x a l p q,
  proc_equiv (Proc_CompAndSplit x a l p q) (Proc_CompAndSplit x (dual a) l q p).
  Proof. intros x a l p q senv; apply proc_swap. Qed.

  Lemma proc_ax_cut_1 :
  forall x a b l y q senv,
  cp (Proc_CompAndSplit x a l (Proc_Link x y b) q) senv ->
  In y l /\ cp (Proc_ClientSplit y x q) senv \/ ~ In y l /\ (~ In y (proc_forbidden q x) -> cp (proc_rename q x y) senv).
  Proof.
    intros x a b l y q senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6).
    pose proof (cp_inv_link _ _ _ _ Hcp4) as Hcp'.
    assert (Hx1 : ~ In x (map fst gamma)) by eauto with senv_valid.
    assert (Hx2 : ~ In x (map fst delta1)) by (rewrite Permutation_middle in Hcp4; eauto with senv_valid).
    assert (Hx3 : ~ In x (map fst delta2)) by (rewrite Permutation_middle in Hcp5; eauto with senv_valid).
    assert (Hx : In (x, dual b) ((x, a) :: gamma ++ delta1)) by (rewrite <- Hcp'; left; auto).
    cbn in Hx.
    destruct Hx as [Hx | Hx].
    2: rewrite in_app_iff in Hx; destruct Hx as [Hx | Hx]; apply (in_map fst) in Hx; tauto.
    injection Hx; intros ?; subst a; clear Hx.
    rewrite dual_involute in Hcp5.
    apply Permutation_cons_inv in Hcp'.

    assert (Hlen : length [(y, b)] = length (gamma ++ delta1)) by (rewrite Hcp'; auto).
    rewrite length_app in Hlen; cbn in Hlen.

    assert (Hy : In (y, b) (gamma ++ delta1)) by (rewrite <- Hcp'; left; auto).
    rewrite in_app_iff in Hy.
    destruct Hy as [Hy | Hy].
    - left.
      destruct gamma eqn:Egamma1; [tauto|].
      destruct l0; [|cbn in Hlen; discriminate].
      cbn in Hlen; destruct delta1 eqn:Edelta1; try discriminate; clear Hlen.
      subst gamma delta1 l; cbn in Hy.
      destruct Hy; [subst p | tauto].
      rewrite <- Hcp6; cbn.
      split; auto.
      cbn in Hcp5.
      rewrite perm_swap in Hcp5.
      cbn in Hcp1; rewrite Forall_cons_iff in Hcp1; destruct Hcp1 as (Hcp1 & _); destruct b; try contradiction.
      apply cp_contract in Hcp5.
      auto.

    - right.
      rewrite PeanoNat.Nat.add_comm in Hlen.
      destruct delta1 eqn:Edelta1; [tauto|].
      destruct s; [|cbn in Hlen; discriminate].
      cbn in Hlen; destruct gamma eqn:Egamma; try discriminate; clear Hlen.
      subst gamma delta1 l; cbn in Hy.
      destruct Hy; [subst p | tauto].
      rewrite <- Hcp6; cbn.
      split; auto.
      cbn in Hcp5.
      intros Hallow.
      pose proof (cp_proc_rename q x y _ Hcp5 Hallow) as Hrename.
      cbn in Hrename.
      rewrite eqb_refl in Hrename.
      fold (senv_rename delta2 x y) in Hrename.
      rewrite senv_rename_nin in Hrename.
      2: auto.
      destruct Hrename as [(_ & Hrename) | (? & _)]; [|tauto].
      auto.
  Qed.

  Lemma proc_ax_cut_2 :
  forall x a b l y q senv,
  cp (Proc_CompAndSplit y a l (Proc_Link x y b) q) senv ->
  In x l /\ cp (Proc_ClientSplit x y q) senv \/ ~ In x l /\ (~ In x (proc_forbidden q y) -> cp (proc_rename q y x) senv).
  Proof.
    intros x a b l y q senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6).
    pose proof (cp_inv_link _ _ _ _ Hcp4) as Hcp'.
    assert (Hy1 : ~ In y (map fst gamma)) by eauto with senv_valid.
    assert (Hy2 : ~ In y (map fst delta1)) by (rewrite Permutation_middle in Hcp4; eauto with senv_valid).
    assert (Hy3 : ~ In y (map fst delta2)) by (rewrite Permutation_middle in Hcp5; eauto with senv_valid).
    assert (Hy : In (y, b) ((y, a) :: gamma ++ delta1)) by (rewrite <- Hcp'; right; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    2: rewrite in_app_iff in Hy; destruct Hy as [Hy | Hy]; apply (in_map fst) in Hy; tauto.
    injection Hy; intros ?; subst b; clear Hy.
    rewrite perm_swap in Hcp'.
    apply Permutation_cons_inv in Hcp'.

    assert (Hlen : length [(x, dual a)] = length (gamma ++ delta1)) by (rewrite Hcp'; auto).
    rewrite length_app in Hlen; cbn in Hlen.

    assert (Hx : In (x, dual a) (gamma ++ delta1)) by (rewrite <- Hcp'; left; auto).
    rewrite in_app_iff in Hx.
    destruct Hx as [Hx | Hx].
    - left.
      destruct gamma eqn:Egamma1; [tauto|].
      destruct l0; [|cbn in Hlen; discriminate].
      cbn in Hlen; destruct delta1 eqn:Edelta1; try discriminate; clear Hlen.
      subst gamma delta1 l; cbn in Hx.
      destruct Hx; [subst p | tauto].
      rewrite <- Hcp6; cbn.
      split; auto.
      cbn in Hcp5.
      rewrite perm_swap in Hcp5.
      cbn in Hcp1; rewrite Forall_cons_iff in Hcp1; destruct Hcp1 as (Hcp1 & _); destruct a; try contradiction.
      cbn in Hcp5.
      apply cp_contract in Hcp5.
      auto.

    - right.
      rewrite PeanoNat.Nat.add_comm in Hlen.
      destruct delta1 eqn:Edelta1; [tauto|].
      destruct s; [|cbn in Hlen; discriminate].
      cbn in Hlen; destruct gamma eqn:Egamma; try discriminate; clear Hlen.
      subst gamma delta1 l; cbn in Hx.
      destruct Hx; [subst p | tauto].
      rewrite <- Hcp6; cbn.
      split; auto.
      cbn in Hcp5.
      intros Hallow.
      pose proof (cp_proc_rename q y x _ Hcp5 Hallow) as Hrename.
      cbn in Hrename.
      rewrite eqb_refl in Hrename.
      fold (senv_rename delta2 y x) in Hrename.
      rewrite senv_rename_nin in Hrename.
      2: auto.
      destruct Hrename as [(_ & Hrename) | (? & _)]; [|tauto].
      auto.
  Qed.

  Section Contraction_Redistr.

  (* When proving structural equivalence of proofs, one frequently encounters the situation where
     two typing environments Gamma and Delta are merged first, with some duplicate clients contracted,
     and (Gamma | Delta) is then merged with Theta, with some other duplicate clients contracted.
     One then hopes to rearrange the proof so that Delta and and Theta are merged first, and then
     (Delta | Theta) is merged with Gamma. In this case it is necessary to rearrage the contractions.
     This section provides algorithms and lemmas for dealing with this situation.
   *)

  Variable (L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 : SEnv).
  Hypothesis (Hcp3 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1)).
  Hypothesis (Hcp4 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2)).
  Hypothesis (Hcp6 : Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hcp7 : senv_valid (L1 ++ gamma_no_L1)).
  Hypothesis (Hcp8 : senv_valid (L1 ++ delta_no_L1)).
  Hypothesis (Hcp9 : senv_valid (L2 ++ theta_no_L2)).
  Hypothesis (Hcp10 : senv_valid (L1 ++ gamma_no_L1 ++ delta_no_L1)).
  Hypothesis (Hcp11 : senv_valid (L2 ++ gamma_delta_no_L2 ++ theta_no_L2)).

  Variable gamma_channels : list chn.
  Hypothesis gamma_channels_def : Permutation gamma_channels (map fst (L1 ++ gamma_no_L1)).

  Variable delta_channels : list chn.
  Hypothesis delta_channels_def : Permutation delta_channels (map fst (L1 ++ delta_no_L1)).

  Variable theta_channels : list chn.
  Hypothesis theta_channels_def : Permutation theta_channels (map fst (L2 ++ theta_no_L2)).

  Lemma gamma_no_L1_delta_no_L1_disjoint : senv_disjoint gamma_no_L1 delta_no_L1.
  Proof. eauto with senv_valid senv_disjoint. Qed.

  Lemma gamma_delta_no_L2_theta_no_L2_disjoint : senv_disjoint gamma_delta_no_L2 theta_no_L2.
  Proof. eauto with senv_valid senv_disjoint. Qed.

  (* L1 is the intersection of gamma and delta. *)
  Lemma L1_prop_1 : forall x, In x (L1 ++ gamma_no_L1) -> In (fst x) (map fst (L1 ++ delta_no_L1)) -> In x L1.
  Proof.
    assert (Hdisjoint1 : senv_disjoint L1 gamma_no_L1) by eauto with senv_valid senv_disjoint.
    assert (Hdisjoint2 : senv_disjoint L1 delta_no_L1) by eauto with senv_valid senv_disjoint.
    pose proof gamma_no_L1_delta_no_L1_disjoint as Hdisjoint3.
    eauto with senv_disjoint_app.
  Qed.

  Lemma L1_prop_2 : forall x, In x (L1 ++ delta_no_L1) -> In (fst x) (map fst (L1 ++ gamma_no_L1)) -> In x L1.
  Proof.
    assert (Hdisjoint1 : senv_disjoint L1 gamma_no_L1) by eauto with senv_valid senv_disjoint.
    assert (Hdisjoint2 : senv_disjoint L1 delta_no_L1) by eauto with senv_valid senv_disjoint.
    pose proof gamma_no_L1_delta_no_L1_disjoint as Hdisjoint3.
    eauto with senv_disjoint_app.
  Qed.

  Lemma L2_prop_1 : forall x, In x (L2 ++ gamma_delta_no_L2) -> In (fst x) (map fst (L2 ++ theta_no_L2)) -> In x L2.
  Proof.
    assert (Hdisjoint1 : senv_disjoint L2 gamma_delta_no_L2) by (rewrite app_assoc in Hcp11; eauto with senv_valid senv_disjoint).
    assert (Hdisjoint2 : senv_disjoint L2 theta_no_L2) by eauto with senv_valid senv_disjoint.
    pose proof gamma_delta_no_L2_theta_no_L2_disjoint as Hdisjoint3.
    eauto with senv_disjoint_app.
  Qed.

  Lemma L2_prop_2 : forall x, In x (L2 ++ theta_no_L2) -> In (fst x) (map fst (L2 ++ gamma_delta_no_L2)) -> In x L2.
  Proof.
    assert (Hdisjoint1 : senv_disjoint L2 gamma_delta_no_L2) by (rewrite app_assoc in Hcp11; eauto with senv_valid senv_disjoint).
    assert (Hdisjoint2 : senv_disjoint L2 theta_no_L2) by eauto with senv_valid senv_disjoint.
    pose proof gamma_delta_no_L2_theta_no_L2_disjoint as Hdisjoint3.
    eauto with senv_disjoint_app.
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
    assert (senv_disjoint (L1 ++ gamma_no_L1) delta_no_L1) by eauto with senv_valid senv_disjoint.
    assert (~ In z delta_no_L1) by eauto with senv_disjoint.
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
    assert (senv_disjoint (L1 ++ delta_no_L1) gamma_no_L1) by eauto with senv_valid senv_disjoint.
    assert (~ In z gamma_no_L1) by eauto with senv_disjoint.
    tauto.
  Qed.

  (* We now define the new channel permutations.
     We first split the channels of Q into new_L1 and delta_no_new_L1.
     new_L1 contains channels that are in both Q and R.
   *)
  Definition delta_name_split_func := fun t => if in_dec eq_dec t theta_channels then true else false.
  Definition delta_split_func := fun (s : chn * STyp) => delta_name_split_func (fst s).
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
    rewrite <- filter_map_swap.
    auto.
  Qed.

  Lemma new_L1_prop : forall x, In x (L2 ++ theta_no_L2) -> In (fst x) (map fst (L1 ++ delta_no_L1)) -> In x new_L1.
  Proof.
    intros z Hin1 Hin2.
    pose proof (L2_prop_4 z ltac:(auto) ltac:(auto)) as Hin3.
    unfold new_L1, delta_split_func, delta_name_split_func.
    rewrite filter_In.
    split; auto.
    rewrite in_dec_true_iff.
    rewrite theta_channels_def.
    auto with senv.
  Qed.

  Lemma new_L1_ques : Forall (fun t => match t with STyp_Ques _ => True | _ => False end) (map snd new_L1).
  Proof.
    rewrite Forall_forall.
    intros z Hz.
    unfold new_L1 in Hz.
    rewrite in_map_iff in Hz.
    destruct Hz as (w & ? & Hw); subst z.
    unfold delta_split_func, delta_name_split_func in Hw.
    rewrite filter_In in Hw.
    destruct Hw as (Hw1 & Hw2).
    rewrite in_dec_true_iff in Hw2.
    rewrite theta_channels_def in Hw2.
    pose proof (L2_prop_1_alt w ltac:(tauto) ltac:(auto)) as Hw3.
    rewrite Forall_forall in Hcp4.
    apply Hcp4.
    auto with senv.
  Qed.

  (* Similarly, we split the channels of R into new_L1 and theta_no_new_L2 *)
  Definition theta_name_split_func := fun t => if in_dec eq_dec t delta_channels then true else false.
  Definition theta_split_func := fun (s : chn * STyp) => theta_name_split_func (fst s).
  Definition new_L1' := filter theta_split_func (L2 ++ theta_no_L2).
  Definition theta_no_new_L1 := filter (fun s => negb (theta_split_func s)) (L2 ++ theta_no_L2).

  Lemma theta_split' : Permutation (L2 ++ theta_no_L2) (new_L1' ++ theta_no_new_L1).
  Proof. unfold new_L1', theta_no_new_L1; apply filter_split. Qed.

  Lemma new_L1_eq : forall x, In x new_L1' <-> In x new_L1.
  Proof.
    intros z.
    unfold new_L1', theta_split_func, theta_name_split_func.
    rewrite filter_In.
    rewrite in_dec_true_iff.
    split.
    - intros Hin.
      destruct Hin as (Hin1 & Hin2).
      rewrite delta_channels_def in Hin2.
      apply new_L1_prop; auto.
    - unfold new_L1, delta_split_func, delta_name_split_func.
      rewrite filter_In.
      intros Hin.
      destruct Hin as (Hin1 & Hin2).
      rewrite in_dec_true_iff in Hin2.
      rewrite theta_channels_def in Hin2.
      rewrite delta_channels_def.
      split; auto with senv.
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
    - eapply NoDup_map_inv; apply Hcp9.
    - eapply NoDup_map_inv; apply Hcp8.
  Qed.

  Lemma theta_split : Permutation (L2 ++ theta_no_L2) (new_L1 ++ theta_no_new_L1).
  Proof. pose proof theta_split' as H; rewrite new_L1_perm in H; auto. Qed.

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
    unfold delta_split_func, delta_name_split_func in Hw2.
    destruct Hw2 as (Hw1 & Hw2).
    destruct Hv2 as (Hv2 & _).
    rewrite negb_in_dec_true_iff in Hw2.
    rewrite theta_channels_def in Hw2.
    rewrite <- Hv1 in Hw2.
    auto with senv.
  Qed.

  Lemma new_L1_senv_valid :
  senv_valid (new_L1 ++ delta_no_new_L1 ++ theta_no_new_L1).
  Proof.
    unfold senv_valid.
    do 2 rewrite map_app.
    rewrite app_assoc.
    apply NoDup_app.
    - rewrite <- map_app, <- delta_split.
      apply Hcp8.
    - assert (Hcp9' : senv_valid (new_L1 ++ theta_no_new_L1)) by (rewrite <- theta_split; auto).
      apply senv_app_r in Hcp9'.
      apply Hcp9'.
    - intros z Hz1 Hz2.
      rewrite in_app_iff in Hz1.
      destruct Hz1 as [Hz1 | Hz1].
      * assert (Hcp9' : senv_valid (new_L1 ++ theta_no_new_L1)) by (rewrite <- theta_split; auto).
        assert (~ In z (map fst new_L1)) by eauto with senv_disjoint.
        tauto.
      * pose proof (delta_no_new_L1_theta_no_new_L1_disjoint z).
        tauto.
  Qed.

  (* We now split the channels of P into new_L2 and gamma_no_new_L2 *)
  Definition gamma_name_split_func := fun t => (if in_dec eq_dec t delta_channels then true else false) || (if in_dec eq_dec t theta_channels then true else false).
  Definition gamma_split_func := fun (s : chn * STyp) => gamma_name_split_func (fst s).
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
    rewrite <- filter_map_swap.
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
      rewrite Bool.orb_true_iff.
      do 2 rewrite in_dec_true_iff.
      rewrite delta_channels_def.
      left; auto with senv.
    - pose proof (L2_prop_3 z ltac:(auto) ltac:(auto)).
      split; auto.
      rewrite Bool.orb_true_iff.
      do 2 rewrite in_dec_true_iff.
      rewrite theta_channels_def.
      right; auto with senv.
  Qed.

  Lemma new_L2_ques : Forall (fun t => match t with STyp_Ques _ => True | _ => False end) (map snd new_L2).
  Proof.
    rewrite Forall_forall.
    intros z Hz.
    unfold new_L2 in Hz.
    rewrite in_map_iff in Hz.
    destruct Hz as (w & ? & Hw); subst z.
    unfold gamma_split_func, gamma_name_split_func in Hw.
    rewrite filter_In in Hw.
    destruct Hw as (Hw1 & Hw2).
    rewrite Bool.orb_true_iff in Hw2.
    do 2 rewrite in_dec_true_iff in Hw2.
    rewrite delta_channels_def, theta_channels_def in Hw2.
    destruct Hw2 as [Hw2 | Hw2].
    - pose proof (L1_prop_1 w ltac:(auto) ltac:(auto)) as Hw3.
      rewrite Forall_forall in Hcp3.
      apply Hcp3.
      auto with senv.
    - pose proof (L2_prop_1 w) as Hw3.
      rewrite <- Hcp6 in Hw3.
      do 2 rewrite in_app_iff in Hw3.
      rewrite in_app_iff in Hw1.
      specialize (Hw3 ltac:(tauto) ltac:(auto)).
      rewrite Forall_forall in Hcp4.
      apply Hcp4.
      auto with senv.
  Qed.

  Definition delta_theta_name_split_func := fun t => if in_dec eq_dec t gamma_channels then true else false.
  Definition delta_theta_split_func := fun (s : chn * STyp) => delta_theta_name_split_func (fst s).
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
    rewrite in_dec_true_iff.
    rewrite in_app_iff.
    split.
    - intros Hin.
      destruct Hin as (Hin1 & Hin2).
      rewrite gamma_channels_def in Hin2.
      apply new_L2_prop; auto.
    - intros Hin.
      unfold new_L2, gamma_split_func, gamma_name_split_func in Hin.
      rewrite filter_In in Hin.
      destruct Hin as (Hin1 & Hin2).
      rewrite Bool.orb_true_iff in Hin2.
      do 2 rewrite in_dec_true_iff in Hin2.
      split.
      2: rewrite gamma_channels_def; auto with senv.
      destruct Hin2 as [Hin2 | Hin2].
      + rewrite delta_channels_def in Hin2.
        pose proof (L1_prop_1 z ltac:(auto) ltac:(auto)).
        left; rewrite in_app_iff; auto.
      + rewrite theta_channels_def in Hin2.
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
    - pose proof new_L1_senv_valid as Hval.
      unfold senv_valid in Hval.
      apply NoDup_map_inv in Hval.
      auto.
    - eapply NoDup_map_inv; apply Hcp7.
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
    rewrite Bool.orb_false_iff in Hw2.
    do 2 rewrite in_dec_false_iff in Hw2.
    destruct Hv2 as (Hv2 & _).
    rewrite <- Hv1 in Hw2.
    rewrite <- in_app_app_iff in Hv2.
    rewrite in_app_iff in Hv2.
    rewrite delta_channels_def, theta_channels_def in Hw2.
    rewrite <- delta_split, <- theta_split in Hv2.
    destruct Hv2 as [Hv2 | Hv2]; apply (in_map fst) in Hv2; tauto.
  Qed.

  Lemma new_L2_senv_valid :
  senv_valid (new_L2 ++ gamma_no_new_L2 ++ delta_theta_no_new_L2).
  Proof.
    unfold senv_valid.
    do 2 rewrite map_app.
    rewrite app_assoc.
    apply NoDup_app.
    - rewrite <- map_app, <- gamma_split.
      apply Hcp7.
    - pose proof new_L1_senv_valid.
      assert (Hcp12 : senv_valid (new_L2 ++ delta_theta_no_new_L2)) by (rewrite <- delta_theta_split; auto).
      apply senv_app_r in Hcp12.
      apply Hcp12.
    - intros z Hz1 Hz2.
      rewrite in_app_iff in Hz1.
      destruct Hz1 as [Hz1 | Hz1].
      * assert (Hnodup : NoDup (map fst (new_L2 ++ delta_theta_no_new_L2))).
        { rewrite <- delta_theta_split; apply new_L1_senv_valid. }
        rewrite map_app in Hnodup.
        pose proof (NoDup_disjoint _ _ z Hnodup); tauto.
      * pose proof (gamma_no_new_L2_delta_theta_no_new_L2_disjoint z).
        tauto.
  Qed.

  Lemma new_L2_split :
  Permutation (L2 ++ gamma_delta_no_L2 ++ theta_no_L2) (new_L2 ++ gamma_no_new_L2 ++ delta_theta_no_new_L2).
  Proof.
    apply NoDup_Permutation.
  - unfold senv_valid in Hcp11.
    apply NoDup_map_inv in Hcp11; auto.
  - pose proof new_L2_senv_valid as Hval; apply NoDup_map_inv in Hval; auto.
  - intros z.
    rewrite <- in_app_app_iff.
    rewrite <- (in_app_app_iff new_L2).
    rewrite in_app_iff.
    rewrite (in_app_iff (new_L2 ++ gamma_no_new_L2)).
    rewrite <- gamma_split.
    rewrite <- delta_theta_split.
    rewrite <- in_app_app_iff.
    rewrite (in_app_iff (new_L1 ++ delta_no_new_L1)).
    rewrite <- delta_split.
    rewrite <- theta_split.
    rewrite <- Hcp6.
    rewrite <- in_app_app_iff.
    rewrite (in_app_iff (L1 ++ gamma_no_L1)).
    tauto.
  Qed.

  (* To prove cut reduction for channels duplicated by CompAndSplit and OutChAndSplit,
     we need a different kind of channel redistribution.
     This time, we need to first merge R with P and Q separately, and then merge (P | R) and (Q | R).
   *)
  Definition l3_theta_name_split_func := fun t => if in_dec eq_dec t gamma_channels then true else false.
  Definition l3_theta_split_func := fun (s : chn * STyp) => l3_theta_name_split_func (fst s).
  Definition new_L3 := filter l3_theta_split_func (L2 ++ theta_no_L2).
  Definition theta_no_new_L3 := filter (fun s => negb (l3_theta_split_func s)) (L2 ++ theta_no_L2).

  Lemma l3_theta_split : Permutation (L2 ++ theta_no_L2) (new_L3 ++ theta_no_new_L3).
  Proof. unfold new_L3, theta_no_new_L3; apply filter_split. Qed.

  Definition new_l3 := filter l3_theta_name_split_func theta_channels.

  Lemma new_l3_def : Permutation new_l3 (map fst new_L3).
  Proof.
    unfold new_l3.
    rewrite theta_channels_def.
    unfold new_L3.
    unfold l3_theta_split_func.
    rewrite <- filter_map_swap.
    auto.
  Qed.

  Lemma new_L3_prop : forall x, In x (L1 ++ gamma_no_L1) -> In (fst x) (map fst (L2 ++ theta_no_L2)) -> In x new_L3.
  Proof.
    intros z Hin1 Hin2.
    pose proof (L2_prop_1_alt z ltac:(tauto) ltac:(auto)) as Hz.
    unfold new_L3, l3_theta_split_func, l3_theta_name_split_func.
    rewrite filter_In, in_app_iff.
    rewrite in_dec_true_iff.
    split; auto.
    rewrite gamma_channels_def.
    auto with senv.
  Qed.

  Lemma new_L3_ques : Forall (fun t => match t with STyp_Ques _ => True | _ => False end) (map snd new_L3).
  Proof.
    rewrite Forall_forall.
    intros z Hz.
    unfold new_L3 in Hz.
    rewrite in_map_iff in Hz.
    destruct Hz as (w & ? & Hw); subst z.
    unfold l3_theta_split_func, l3_theta_name_split_func in Hw.
    rewrite filter_In in Hw.
    rewrite in_dec_true_iff in Hw.
    destruct Hw as (Hw1 & Hw2).
    rewrite gamma_channels_def in Hw2.
    pose proof (L2_prop_2_alt w ltac:(auto) ltac:(tauto)) as Hw3.
    rewrite Forall_forall in Hcp4.
    apply Hcp4.
    auto with senv.
  Qed.

  Definition l3_gamma_name_split_func := fun t => if in_dec eq_dec t theta_channels then true else false.
  Definition l3_gamma_split_func := fun (s : chn * STyp) => l3_gamma_name_split_func (fst s).
  Definition new_L3' := filter l3_gamma_split_func (L1 ++ gamma_no_L1).
  Definition gamma_no_new_L3 := filter (fun s => negb (l3_gamma_split_func s)) (L1 ++ gamma_no_L1).

  Lemma l3_gamma_split' : Permutation (L1 ++ gamma_no_L1) (new_L3' ++ gamma_no_new_L3).
  Proof. unfold new_L3', gamma_no_new_L3; apply filter_split. Qed.

  Lemma new_L3_eq : forall x, In x new_L3' <-> In x new_L3.
  Proof.
    intros z.
    unfold new_L3', l3_gamma_split_func, l3_gamma_name_split_func.
    rewrite filter_In.
    rewrite in_dec_true_iff.
    split.
    - intros Hin.
      destruct Hin as (Hin1 & Hin2).
      rewrite theta_channels_def in Hin2.
      apply new_L3_prop; auto.
    - unfold new_L3, l3_theta_split_func, l3_theta_name_split_func.
      rewrite filter_In.
      rewrite in_dec_true_iff.
      intros Hin.
      destruct Hin as (Hin1 & Hin2).
      rewrite gamma_channels_def in Hin2.
      rewrite theta_channels_def.
      split; auto.
      apply L2_prop_3; auto.
      auto with senv.
  Qed.

  Lemma new_L3_perm : Permutation new_L3' new_L3.
  Proof.
    apply NoDup_Permutation.
    3: apply new_L3_eq.
    1: unfold new_L3'.
    2: unfold new_L3.
    all: apply NoDup_filter.
    - eapply NoDup_map_inv; apply Hcp7.
    - eapply NoDup_map_inv; apply Hcp9.
  Qed.

  Lemma l3_gamma_split : Permutation (L1 ++ gamma_no_L1) (new_L3 ++ gamma_no_new_L3).
  Proof. pose proof l3_gamma_split' as H; rewrite new_L3_perm in H; auto. Qed.

  Lemma gamma_no_new_L3_theta_no_new_L3_disjoint :
  senv_disjoint gamma_no_new_L3 theta_no_new_L3.
  Proof.
    unfold senv_disjoint.
    intros z Hz1 Hz2.
    unfold gamma_no_new_L3 in Hz1.
    unfold theta_no_new_L3 in Hz2.
    rewrite in_map_iff in Hz1, Hz2.
    destruct Hz1 as (w & Hw1 & Hw2); subst z.
    destruct Hz2 as (v & Hv1 & Hv2).
    rewrite filter_In in Hw2, Hv2.
    destruct Hw2 as (Hw1 & Hw2).
    rewrite Bool.negb_true_iff in Hw2.
    unfold l3_gamma_split_func, l3_gamma_name_split_func in Hw2.
    rewrite in_dec_false_iff in Hw2.
    destruct Hv2 as (Hv2 & _).
    rewrite <- Hv1 in Hw2.
    rewrite theta_channels_def in Hw2.
    apply (in_map fst) in Hv2; tauto.
  Qed.

  Lemma new_L3_senv_valid :
  senv_valid (new_L3 ++ gamma_no_new_L3 ++ theta_no_new_L3).
  Proof.
    unfold senv_valid.
    do 2 rewrite map_app.
    rewrite app_assoc.
    apply NoDup_app.
    - rewrite <- map_app, <- l3_gamma_split.
      apply Hcp7.
    - unfold theta_no_new_L3.
      apply map_filter_nodup.
      apply Hcp9.
    - intros z Hz1 Hz2.
      rewrite in_app_iff in Hz1.
      destruct Hz1 as [Hz1 | Hz1].
      * rewrite l3_theta_split in Hcp9.
        assert (Hdisjoint : senv_disjoint new_L3 theta_no_new_L3) by eauto with senv_disjoint.
        apply (Hdisjoint z Hz1 Hz2).
      * pose proof (gamma_no_new_L3_theta_no_new_L3_disjoint z).
        tauto.
  Qed.

  (* Intersection of delta and theta is already defined as L1 above *)

  Definition l4_gamma_name_split_func := fun t => if in_dec eq_dec t delta_channels then true else false.
  Definition l4_gamma_split_func := fun (s : chn * STyp) => l4_gamma_name_split_func (fst s).
  Definition new_L4 := filter l4_gamma_split_func gamma_no_new_L3.
  Definition gamma_no_new_L3_no_new_L4 := filter (fun s => negb (l4_gamma_split_func s)) gamma_no_new_L3.

  Lemma l4_gamma_split : Permutation gamma_no_new_L3 (new_L4 ++ gamma_no_new_L3_no_new_L4).
  Proof. unfold new_L4, gamma_no_new_L3_no_new_L4; apply filter_split. Qed.

  Definition new_l4 := filter l4_gamma_name_split_func (filter (fun s => negb (l3_gamma_name_split_func s)) gamma_channels).

  Lemma new_l4_def : Permutation new_l4 (map fst new_L4).
  Proof.
    unfold new_l4.
    rewrite gamma_channels_def.
    unfold new_L4.
    unfold l4_gamma_split_func.
    rewrite <- filter_map_swap.
    unfold l4_gamma_name_split_func.
    apply filter_proper; auto.
    unfold gamma_no_new_L3.
    unfold l3_gamma_split_func, l3_gamma_name_split_func.
    rewrite filter_map_swap; auto.
  Qed.

  Lemma new_L4_prop : forall x, In x (L1 ++ delta_no_L1) -> In (fst x) (map fst gamma_no_new_L3) -> In x new_L4.
  Proof.
    intros z Hin1 Hin2.
    assert (Hin3 : In (fst z) (map fst (L1 ++ gamma_no_L1))).
    { rewrite l3_gamma_split; rewrite map_app, in_app_iff; auto. }
    pose proof (L1_prop_2 z ltac:(auto) ltac:(auto)) as Hin4.
    assert (Hin5 : In z (new_L3 ++ gamma_no_new_L3)).
    { rewrite <- l3_gamma_split; rewrite in_app_iff; auto. }
    rewrite in_app_iff in Hin5.
    destruct Hin5 as [Hin5 | Hin5].
    1: { rewrite l3_gamma_split in Hcp7.
         assert (Hdisjoint : senv_disjoint new_L3 gamma_no_new_L3) by eauto with senv_disjoint.
         specialize (Hdisjoint (fst z)).
         apply (in_map fst) in Hin5; tauto.
    }
    unfold new_L4, l4_gamma_split_func, l4_gamma_name_split_func.
    rewrite filter_In; split; auto.
    rewrite in_dec_true_iff.
    rewrite delta_channels_def.
    auto with senv.
  Qed.

  Lemma new_L4_ques : Forall (fun t => match t with STyp_Ques _ => True | _ => False end) (map snd new_L4).
  Proof.
    rewrite Forall_forall.
    intros z Hz.
    unfold new_L4 in Hz.
    rewrite in_map_iff in Hz.
    destruct Hz as (w & ? & Hw); subst z.
    unfold l4_gamma_split_func, l4_gamma_name_split_func in Hw.
    rewrite filter_In in Hw.
    destruct Hw as (Hw1 & Hw2).
    rewrite in_dec_true_iff in Hw2.
    rewrite delta_channels_def in Hw2.
    assert (Hw1' : In w (L1 ++ gamma_no_L1)).
    { rewrite l3_gamma_split; rewrite in_app_iff; auto. }
    pose proof (L1_prop_1 w ltac:(auto) ltac:(auto)) as Hw3.
    rewrite Forall_forall in Hcp3.
    apply Hcp3.
    auto with senv.
  Qed.

  Definition l4_delta_name_split_func := fun t => if in_dec eq_dec t gamma_channels then true else false.
  Definition l4_delta_split_func := fun (s : chn * STyp) => l4_delta_name_split_func (fst s).
  Definition new_L4' := filter l4_delta_split_func delta_no_new_L1.
  Definition delta_no_new_L1_no_new_L4 := filter (fun s => negb (l4_delta_split_func s)) delta_no_new_L1.

  Lemma l4_delta_split' : Permutation delta_no_new_L1 (new_L4' ++ delta_no_new_L1_no_new_L4).
  Proof. unfold new_L4', delta_no_new_L1_no_new_L4; apply filter_split. Qed.

  Lemma new_L4_eq : forall x, In x new_L4' <-> In x new_L4.
  Proof.
    intros z.
    unfold new_L4', l4_delta_split_func, l4_delta_name_split_func.
    rewrite filter_In.
    split.
    - intros Hin.
      destruct Hin as (Hin1 & Hin2).
      rewrite in_dec_true_iff in Hin2.
      rewrite gamma_channels_def in Hin2.
      unfold delta_no_new_L1 in Hin1.
      rewrite filter_In in Hin1.
      destruct Hin1 as (Hin1 & Hin3).
      unfold delta_split_func, delta_name_split_func in Hin3.
      rewrite negb_in_dec_true_iff in Hin3.
      pose proof (L1_prop_2 z ltac:(auto) ltac:(auto)) as Hin4.
      apply new_L4_prop; auto.
      unfold gamma_no_new_L3.
      apply in_map.
      rewrite filter_In; split.
      1: rewrite in_app_iff; auto.
      unfold l3_gamma_split_func, l3_gamma_name_split_func.
      rewrite negb_in_dec_true_iff; auto.
    - unfold new_L4, l4_gamma_split_func, l4_gamma_name_split_func.
      rewrite filter_In.
      do 2 rewrite in_dec_true_iff.
      intros Hin.
      destruct Hin as (Hin1 & Hin2).
      rewrite delta_channels_def in Hin2.
      unfold gamma_no_new_L3, l3_gamma_split_func, l3_gamma_name_split_func in Hin1.
      rewrite filter_In in Hin1.
      destruct Hin1 as (Hin1 & Hin3).
      rewrite negb_in_dec_true_iff in Hin3.
      pose proof (L1_prop_1 z ltac:(auto) ltac:(auto)) as Hin4.
      rewrite gamma_channels_def.
      split; auto with senv.
      unfold delta_no_new_L1.
      rewrite filter_In; split.
      1: rewrite in_app_iff; auto.
      unfold delta_split_func, delta_name_split_func.
      rewrite negb_in_dec_true_iff; auto.
  Qed.

  Lemma new_L4_perm : Permutation new_L4' new_L4.
  Proof.
    apply NoDup_Permutation.
    3: apply new_L4_eq.
    1: unfold new_L4'.
    2: unfold new_L4.
    all: apply NoDup_filter.
    - unfold delta_no_new_L1; apply NoDup_filter; eapply NoDup_map_inv; apply Hcp8.
    - unfold gamma_no_new_L3; apply NoDup_filter; eapply NoDup_map_inv; apply Hcp7.
  Qed.

  Lemma l4_delta_split : Permutation delta_no_new_L1 (new_L4 ++ delta_no_new_L1_no_new_L4).
  Proof. pose proof l4_delta_split' as H; rewrite new_L4_perm in H; auto. Qed.

  Lemma gamma_no_new_L3_no_new_L4_delta_no_new_L1_no_new_L4_disjoint :
  senv_disjoint gamma_no_new_L3_no_new_L4 delta_no_new_L1_no_new_L4.
  Proof.
    unfold senv_disjoint.
    intros z Hz1 Hz2.
    unfold gamma_no_new_L3_no_new_L4 in Hz1.
    unfold delta_no_new_L1_no_new_L4 in Hz2.
    rewrite in_map_iff in Hz1, Hz2.
    destruct Hz1 as (w & Hw1 & Hw2); subst z.
    destruct Hz2 as (v & Hv1 & Hv2).
    rewrite filter_In in Hw2, Hv2.
    destruct Hw2 as (Hw1 & Hw2).
    unfold l4_gamma_split_func, l4_gamma_name_split_func in Hw2.
    rewrite negb_in_dec_true_iff in Hw2.
    destruct Hv2 as (Hv2 & _).
    rewrite <- Hv1 in Hw2.
    rewrite delta_channels_def in Hw2.
    unfold delta_no_new_L1 in Hv2.
    rewrite filter_In in Hv2.
    destruct Hv2 as (Hv2 & _).
    apply (in_map fst) in Hv2; tauto.
  Qed.

  Lemma new_L4_senv_valid :
  senv_valid (new_L4 ++ gamma_no_new_L3_no_new_L4 ++ delta_no_new_L1_no_new_L4).
  Proof.
    unfold senv_valid.
    do 2 rewrite map_app.
    rewrite app_assoc.
    apply NoDup_app.
    - rewrite <- map_app, <- l4_gamma_split.
      unfold gamma_no_new_L3.
      apply map_filter_nodup.
      apply Hcp7.
    - unfold delta_no_new_L1_no_new_L4.
      apply map_filter_nodup.
      assert (Hnodup : NoDup (map fst (new_L1 ++ delta_no_new_L1))).
      { rewrite <- delta_split; apply Hcp8. }
      rewrite map_app in Hnodup.
      apply NoDup_app_remove_l in Hnodup; auto.
    - intros z Hz1 Hz2.
      rewrite in_app_iff in Hz1.
      destruct Hz1 as [Hz1 | Hz1].
      * pose proof Hcp8 as Hcp8'.
        rewrite delta_split in Hcp8'.
        rewrite l4_delta_split in Hcp8'.
        assert (Hdisjoint : senv_disjoint new_L4 delta_no_new_L1_no_new_L4) by eauto with senv_valid senv_disjoint.
        specialize (Hdisjoint z).
        tauto.
      * pose proof (gamma_no_new_L3_no_new_L4_delta_no_new_L1_no_new_L4_disjoint z).
        tauto.
  Qed.

  Lemma new_L4_split :
  Permutation gamma_delta_no_L2 (new_L4 ++ gamma_no_new_L3_no_new_L4 ++ delta_no_new_L1_no_new_L4).
  Proof.
    apply NoDup_Permutation.
    - assert (Hval : senv_valid gamma_delta_no_L2) by eauto with senv_valid.
      apply NoDup_map_inv in Hval.
      auto.
    - pose proof new_L4_senv_valid as Hval; apply NoDup_map_inv in Hval; auto.
    - intros z.
      rewrite <- in_app_app_iff.
      rewrite <- l4_gamma_split.
      rewrite <- l4_delta_split.

      assert (Hz1 : In z L2 -> ~ In z gamma_delta_no_L2).
      { intros Hz.
        rewrite app_assoc in Hcp11.
        assert (Hdisjoint : senv_disjoint L2 gamma_delta_no_L2) by eauto with senv_valid senv_disjoint.
        specialize (Hdisjoint (fst z)).
        auto with senv.
      }
      assert (Hz2 : In z gamma_delta_no_L2 -> ~ In z theta_no_L2).
      { intros Hin.
        pose proof (gamma_delta_no_L2_theta_no_L2_disjoint (fst z)) as Hz2.
        auto with senv.
      }
      assert (Hz3 : In z gamma_delta_no_L2 <-> In z (L2 ++ gamma_delta_no_L2) /\ ~ In z (L2 ++ theta_no_L2)).
      { do 2 rewrite in_app_iff; tauto. }
      rewrite <- Hcp6 in Hz3.
      rewrite <- in_app_app_iff in Hz3.
      rewrite in_app_iff in Hz3.

      assert (Hz4 : In z new_L3 -> ~ In z gamma_no_new_L3).
      { intros Hz.
        rewrite l3_gamma_split in Hcp7.
        assert (Hdisjoint : senv_disjoint new_L3 gamma_no_new_L3) by eauto with senv_disjoint.
        specialize (Hdisjoint (fst z)).
        auto with senv.
      }
      assert (Hz5 : In z gamma_no_new_L3 -> ~ In z theta_no_new_L3).
      { intros Hin.
        pose proof (gamma_no_new_L3_theta_no_new_L3_disjoint (fst z)) as Hz5.
        auto with senv.
      }
      assert (Hz6 : In z gamma_no_new_L3 <-> In z (new_L3 ++ gamma_no_new_L3) /\ ~ In z (L2 ++ theta_no_L2)).
      { rewrite l3_theta_split; do 2 rewrite in_app_iff; tauto. }
      rewrite <- l3_gamma_split in Hz6.

      assert (Hz7 : In z new_L1 -> ~ In z delta_no_new_L1).
      { intros Hz.
        rewrite delta_split in Hcp8.
        assert (Hdisjoint : senv_disjoint new_L1 delta_no_new_L1) by eauto with senv_disjoint.
        specialize (Hdisjoint (fst z)).
        auto with senv.
      }
      assert (Hz8 : In z delta_no_new_L1 -> ~ In z theta_no_new_L1).
      { intros Hin.
        pose proof (delta_no_new_L1_theta_no_new_L1_disjoint (fst z)) as Hz8.
        auto with senv.
      }
      assert (Hz9 : In z delta_no_new_L1 <-> In z (new_L1 ++ delta_no_new_L1) /\ ~ In z (L2 ++ theta_no_L2)).
      { rewrite theta_split; do 2 rewrite in_app_iff; tauto. }
      rewrite <- delta_split in Hz9.

      rewrite in_app_iff.
      rewrite Hz3, Hz6, Hz9.
      tauto.
  Qed.

  End Contraction_Redistr.

  Section Proc_Assoc.

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
    1: apply (in_map fst) in Hy3; tauto.

    (* y cannot be same as x *)
    assert (Hy4 : x <> y).
    { apply cp_senv_valid in Hcp'4, Hcp'5.
      rewrite senv_valid_cons in Hcp'4, Hcp'5.
      rewrite map_app, in_app_iff in Hcp'4, Hcp'5.
      intros Heq; subst y.
      destruct Hy3 as [Hy3 | Hy3].
      all: apply (in_map fst) in Hy3; tauto.
    }

    (* Simplify Hy1 *)
    rewrite <- (proc_channels_perm _ _ Hcp'5) in Hy1.
    cbn in Hy1.
    destruct Hy1 as [? | Hy1']; [tauto|].
    rewrite map_app, in_app_iff in Hy1'.
    destruct Hy1' as [? | Hy1']; [tauto|].

    (* Since y is in delta_y_no_L1, it cannot be in gamma_no_L1 *)
    destruct Hy3 as [Hy3 | Hy3].
    2: clear Hy1.
    1: { unfold senv_disjoint in Hcp'3.
         specialize (Hcp'3 y ltac:(apply (in_map fst) in Hy3; auto)).
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
  Hypothesis (Hcp3 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1)).
  Hypothesis (Hcp4 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2)).
  Hypothesis (Hcp5 : Permutation senv (L2 ++ gamma_delta_no_L2 ++ theta_no_L2)).
  Hypothesis (Hcp6 : Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hcp7 : cp p ((x, a) :: L1 ++ gamma_no_L1)).
  Hypothesis (Hcp8 : cp q ((x, dual a) :: (y, b) :: L1 ++ delta_no_L1)).
  Hypothesis (Hcp9 : cp r ((y, dual b) :: L2 ++ theta_no_L2)).
  Hypothesis (Hcp10 : cp (Proc_CompAndSplit x a l1 p q) ((y, b) :: L1 ++ gamma_no_L1 ++ delta_no_L1)).

  Lemma assoc_Hcp7' : senv_valid (L1 ++ gamma_no_L1).
  Proof. apply cp_senv_valid in Hcp7; rewrite senv_valid_cons in Hcp7; tauto. Qed.

  Lemma assoc_Hcp8' : senv_valid (L1 ++ delta_no_L1).
  Proof. apply cp_senv_valid in Hcp8; do 2 rewrite senv_valid_cons in Hcp8; tauto. Qed.

  Lemma assoc_Hcp9' : senv_valid (L2 ++ theta_no_L2).
  Proof. apply cp_senv_valid in Hcp9; rewrite senv_valid_cons in Hcp9; tauto. Qed.

  Lemma assoc_Hcp10' : senv_valid (L1 ++ gamma_no_L1 ++ delta_no_L1).
  Proof. apply cp_senv_valid in Hcp10; rewrite senv_valid_cons in Hcp10; tauto. Qed.

  Lemma assoc_Hcp11' : senv_valid (L2 ++ gamma_delta_no_L2 ++ theta_no_L2).
  Proof. rewrite Hcp5 in Hcp; apply cp_senv_valid in Hcp; auto. Qed.

  Hypothesis (Hy3 : ~ In x (proc_channels r)).

  Definition assoc_gamma_channels := filter (fun s => negb (eqb x s)) (proc_channels p).

  Lemma assoc_gamma_channels_def : Permutation assoc_gamma_channels (map fst (L1 ++ gamma_no_L1)).
  Proof.
    unfold assoc_gamma_channels.
    rewrite <- (proc_channels_perm _ _ Hcp7).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp7).
  Qed.

  Definition assoc_delta_channels := filter (fun s => negb (eqb x s) && negb (eqb y s)) (proc_channels q).

  Lemma assoc_delta_channels_def : Permutation assoc_delta_channels (map fst (L1 ++ delta_no_L1)).
  Proof.
    unfold assoc_delta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp8).
    cbn [map fst].
    rewrite NoDup_filter_two; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp8).
  Qed.

  Definition assoc_theta_channels := filter (fun s => negb (eqb y s)) (proc_channels r).

  Lemma assoc_theta_channels_def : Permutation assoc_theta_channels (map fst (L2 ++ theta_no_L2)).
  Proof.
    unfold assoc_theta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp9).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp9).
  Qed.

  Definition assoc_new_L1 := new_L1 L1 delta_no_L1 assoc_theta_channels.
  Definition assoc_delta_no_new_L1 := delta_no_new_L1 L1 delta_no_L1 assoc_theta_channels.
  Definition assoc_theta_no_new_L1 := theta_no_new_L1 L2 theta_no_L2 assoc_delta_channels.
  Definition assoc_new_L2 := new_L2 L1 gamma_no_L1 assoc_delta_channels assoc_theta_channels.
  Definition assoc_gamma_no_new_L2 := gamma_no_new_L2 L1 gamma_no_L1 assoc_delta_channels assoc_theta_channels.
  Definition assoc_delta_theta_no_new_L2 := delta_theta_no_new_L2 L1 L2 delta_no_L1 theta_no_L2 assoc_gamma_channels assoc_delta_channels assoc_theta_channels.
  Definition assoc_new_l1 := new_l1 assoc_delta_channels assoc_theta_channels.
  Definition assoc_new_l2 := new_l2 assoc_gamma_channels assoc_delta_channels assoc_theta_channels.

  (* Permute the signature of P, Q, and R *)
  Lemma proc_p_perm :
  cp p ((x, a) :: assoc_new_L2 ++ assoc_gamma_no_new_L2).
  Proof.
    rewrite (gamma_split _ _ assoc_delta_channels assoc_theta_channels) in Hcp7; auto.
  Qed.

  Lemma proc_q_perm :
  cp q ((y, b) :: assoc_new_L1 ++ (x, dual a) :: assoc_delta_no_new_L1).
  Proof.
    rewrite (delta_split _ _ assoc_theta_channels) in Hcp8.
    rewrite perm_swap in Hcp8.
    rewrite Permutation_middle in Hcp8.
    auto.
  Qed.

  Lemma proc_r_perm :
  cp r ((y, dual b) :: assoc_new_L1 ++ assoc_theta_no_new_L1).
  Proof.
    pose proof Hcp9 as Hcp12.
    rewrite (theta_split _ _ _ _ _ _ Hcp6 assoc_Hcp8' assoc_Hcp9' assoc_Hcp10' assoc_Hcp11' assoc_delta_channels assoc_delta_channels_def assoc_theta_channels assoc_theta_channels_def) in Hcp12.
    auto.
  Qed.

  (* We are now ready to cut Q and R. *)
  Lemma cp_comp_q_r :
  cp (Proc_CompAndSplit y b assoc_new_l1 q r) (assoc_new_L1 ++ (x, dual a) :: assoc_delta_no_new_L1 ++ assoc_theta_no_new_L1).
  Proof.
    pose proof (new_l1_def _ _ _ assoc_delta_channels_def assoc_theta_channels) as Hperm.
    rewrite Hperm; fold assoc_new_L1.
    pose proof proc_q_perm as Hcp12.
    pose proof proc_r_perm as Hcp13.
    rewrite app_comm_cons.
    constructor; auto.

    - pose proof (new_L1_ques) as H.
      specialize (H _ _ _ _ _ _ Hcp4 Hcp6 assoc_Hcp9' assoc_Hcp11' _ assoc_theta_channels_def).
      auto.

    - unfold senv_disjoint.
      intros z Hz.
      cbn in Hz.
      destruct Hz as [Hz | Hz].
      + subst z.
        unfold assoc_theta_no_new_L1, theta_no_new_L1, theta_split_func.
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
        pose proof delta_no_new_L1_theta_no_new_L1_disjoint as H.
        specialize (H L1 _ delta_no_L1 theta_no_L2 assoc_delta_channels _ assoc_theta_channels_def z).
        tauto.
  Qed.

  Lemma proc_q_r_perm :
  cp (Proc_CompAndSplit y b assoc_new_l1 q r) ((x, dual a) :: assoc_new_L2 ++ assoc_delta_theta_no_new_L2).
  Proof.
    pose proof (cp_comp_q_r) as Hcp'.
    rewrite <- Permutation_middle in Hcp'.
    unfold assoc_new_L1, assoc_delta_no_new_L1, assoc_theta_no_new_L1 in Hcp'.
    rewrite (delta_theta_split _ _ _ _ _ _ Hcp6 assoc_Hcp7' assoc_Hcp8' assoc_Hcp9' assoc_Hcp10' assoc_Hcp11' _ assoc_gamma_channels_def _ assoc_delta_channels_def _ assoc_theta_channels_def) in Hcp'.
    auto.
  Qed.

  (* We are now ready to cut P and (Q | R). *)
  Lemma cp_comp_p_q_r :
  cp (Proc_CompAndSplit x a assoc_new_l2 p (Proc_CompAndSplit y b assoc_new_l1 q r)) (assoc_new_L2 ++ assoc_gamma_no_new_L2 ++ assoc_delta_theta_no_new_L2).
  Proof.
    pose proof (new_l2_def _ _ _ assoc_gamma_channels_def assoc_delta_channels assoc_theta_channels) as Hperm.
    rewrite Hperm; fold assoc_new_L2.
    pose proof proc_p_perm as Hcp'1.
    pose proof proc_q_r_perm as Hcp'2.
    constructor; auto.

    - pose proof new_L2_ques as H.
      specialize (H _ _ _ _ _ _ Hcp3 Hcp4 Hcp6 assoc_Hcp7' assoc_Hcp8' assoc_Hcp9' assoc_Hcp10' assoc_Hcp11' _ assoc_delta_channels_def _ assoc_theta_channels_def).
      auto.

    - unfold senv_disjoint; intros z Hz1 Hz2.
      pose proof gamma_no_new_L2_delta_theta_no_new_L2_disjoint as H.
      specialize (H _ _ _ _ _ _ Hcp6 assoc_Hcp8' assoc_Hcp9' assoc_Hcp10' assoc_Hcp11' assoc_gamma_channels _ assoc_delta_channels_def _ assoc_theta_channels_def z).
      tauto.
  Qed.

  Lemma proc_p_q_r_perm :
  cp (Proc_CompAndSplit x a assoc_new_l2 p (Proc_CompAndSplit y b assoc_new_l1 q r)) senv.
  Proof.
    pose proof cp_comp_p_q_r as Hcp'.
    eapply cp_perm.
    1: apply Hcp'.
    rewrite Hcp5.
    symmetry.
    apply (new_L2_split _ _ _ _ _ _ Hcp6 assoc_Hcp7' assoc_Hcp8' assoc_Hcp9' assoc_Hcp10' assoc_Hcp11' _ assoc_gamma_channels_def _ assoc_delta_channels_def _ assoc_theta_channels_def).
  Qed.

  End Proc_Assoc.

  Lemma proc_assoc_1 :
  forall x y a b l1 l2 p q r senv,
  In y (proc_channels q) ->
  ~ In y l1 ->
  ~ In x (proc_channels r) ->
  cp (Proc_CompAndSplit y b l2 (Proc_CompAndSplit x a l1 p q) r) senv ->
  let new_l1 := (assoc_new_l1 x y q r) in
  let new_l2 := (assoc_new_l2 x y p q r) in
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
  let new_l1 := (assoc_new_l1 x y p r) in
  let new_l2 := (assoc_new_l2 x y q p r) in
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
  let new_l1 := (assoc_new_l1 y x q p) in
  let new_l2 := (assoc_new_l2 y x r q p) in
  cp (Proc_CompAndSplit y b new_l2 (Proc_CompAndSplit x a new_l1 p q) r) senv.
  Proof.
    intros x y a b l1 l2 p q r senv Hy1 Hy2 Hy3 Hcp.
    rewrite proc_swap in Hcp.
    apply proc_assoc_2 in Hcp; auto.
    rewrite <- proc_swap in Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (old_cp_gamma & old_cp_delta1 & old_cp_delta2 & Hold_cp1 & Hold_cp2 & Hold_cp3 & Hold_cp4 & Hold_cp5 & Hold_cp6).
    rewrite <- proc_swap in Hold_cp4.
    cbn.
    rewrite <- Hold_cp6, Hold_cp2. constructor; auto.
  Qed.

  Lemma proc_assoc_4 :
  forall x y a b l1 l2 p q r senv,
  In x (proc_channels r) ->
  ~ In x l1 ->
  ~ In y (proc_channels p) ->
  cp (Proc_CompAndSplit x a l2 p (Proc_CompAndSplit y b l1 q r)) senv ->
  let new_l1 := (assoc_new_l1 y x r p) in
  let new_l2 := (assoc_new_l2 y x q r p) in
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

  Section OutCh_Cut.

  Variable (x y : chn).
  Variable (t : STyp).
  Variable (l1 l2 : list chn).
  Variable (p q r : Process).
  Variable (senv : SEnv).
  Hypothesis (Hcp : cp (Proc_CompAndSplit x t l2 (Proc_OutChAndSplit x y l1 p q) (Proc_InCh x y r)) senv).
  Hypothesis (Hy1 : ~ In y (proc_channels q)).

  Lemma proc_outch_cut_inv :
  exists a b L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2,
  t = STyp_Times a b /\
  l1 = map fst L1 /\
  l2 = map fst L2 /\
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1) /\
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2) /\
  Permutation senv (L2 ++ gamma_delta_no_L2 ++ theta_no_L2) /\
  Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2) /\
  cp p ((y, a) :: L1 ++ gamma_no_L1) /\
  cp q ((x, b) :: L1 ++ delta_no_L1) /\
  cp r ((x, dual b) :: (y, dual a) :: L2 ++ theta_no_L2) /\
  cp (Proc_OutChAndSplit x y l1 p q) ((x, STyp_Times a b) :: L1 ++ gamma_no_L1 ++ delta_no_L1).
  Proof.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (L2 & gamma_delta_no_L2 & theta_no_L2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6).
    destruct (cp_inv_outch_and_split _ _ _ _ _ _ Hcp4) as (a' & b' & L1 & gamma_no_L1 & delta_no_L1 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6 & Hcp'7).
    destruct (cp_inv_inch _ _ _ _ Hcp5) as (a'' & b'' & theta & Hcp''1 & Hcp''2).
    subst l1 l2.

    (* t = STyp_Times a' b'*)
    assert (Hx : In (x, STyp_Times a' b') ((x, t) :: L2 ++ gamma_delta_no_L2)) by (rewrite <- Hcp'7; left; auto).
    cbn in Hx.
    destruct Hx as [Hx | Hx].
    2: { apply cp_senv_valid in Hcp4.
         rewrite senv_valid_cons in Hcp4.
         apply (in_map fst) in Hx; cbn in Hx; tauto.
    }
    injection Hx; intros; subst t; clear Hx.

    (* a'', b'' are dual to a', b' *)
    cbn in Hcp''2, Hcp5.
    assert (Hx : In (x, STyp_Par a'' b'') ((x, STyp_Par (dual a') (dual b')) :: L2 ++ theta_no_L2)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hx.
    destruct Hx as [Hx | Hx].
    2: { apply cp_senv_valid in Hcp5.
         rewrite senv_valid_cons in Hcp5.
         apply (in_map fst) in Hx; cbn in Hx; tauto.
    }
    injection Hx; intros; subst a'' b''; clear Hx.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.
    clear theta Hcp''2.

    apply Permutation_cons_inv in Hcp'7.

    exists a'; exists b'; exists L1; exists L2; exists gamma_no_L1; exists delta_no_L1; exists gamma_delta_no_L2; exists theta_no_L2.
    repeat split; auto.
    - symmetry; auto.
    - rewrite Hcp'7; auto.
  Qed.

  Variable (a b : STyp).
  Variable (L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 : SEnv).
  Hypothesis (Hcp3 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1)).
  Hypothesis (Hcp4 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2)).
  Hypothesis (Hcp5 : Permutation senv (L2 ++ gamma_delta_no_L2 ++ theta_no_L2)).
  Hypothesis (Hcp6 : Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hcp7 : cp p ((y, a) :: L1 ++ gamma_no_L1)).
  Hypothesis (Hcp8 : cp q ((x, b) :: L1 ++ delta_no_L1)).
  Hypothesis (Hcp9 : cp r ((x, dual b) :: (y, dual a) :: L2 ++ theta_no_L2)).
  Hypothesis (Hcp10 : cp (Proc_OutChAndSplit x y l1 p q) ((x, STyp_Times a b) :: L1 ++ gamma_no_L1 ++ delta_no_L1)).

  Lemma outch_Hcp7' : senv_valid (L1 ++ gamma_no_L1).
  Proof. apply cp_senv_valid in Hcp7; rewrite senv_valid_cons in Hcp7; tauto. Qed.

  Lemma outch_Hcp8' : senv_valid (L1 ++ delta_no_L1).
  Proof. apply cp_senv_valid in Hcp8; rewrite senv_valid_cons in Hcp8; tauto. Qed.

  Lemma outch_Hcp9' : senv_valid (L2 ++ theta_no_L2).
  Proof. apply cp_senv_valid in Hcp9; do 2 rewrite senv_valid_cons in Hcp9; tauto. Qed.

  Lemma outch_Hcp10' : senv_valid (L1 ++ gamma_no_L1 ++ delta_no_L1).
  Proof. apply cp_senv_valid in Hcp10; rewrite senv_valid_cons in Hcp10; tauto. Qed.

  Lemma outch_Hcp11' : senv_valid (L2 ++ gamma_delta_no_L2 ++ theta_no_L2).
  Proof. rewrite Hcp5 in Hcp; apply cp_senv_valid in Hcp; auto. Qed.

  Definition outch_gamma_channels := filter (fun s => negb (eqb y s)) (proc_channels p).

  Lemma outch_gamma_channels_def : Permutation outch_gamma_channels (map fst (L1 ++ gamma_no_L1)).
  Proof.
    unfold outch_gamma_channels.
    rewrite <- (proc_channels_perm _ _ Hcp7).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp7).
  Qed.

  Definition outch_delta_channels := filter (fun s => negb (eqb x s)) (proc_channels q).

  Lemma outch_delta_channels_def : Permutation outch_delta_channels (map fst (L1 ++ delta_no_L1)).
  Proof.
    unfold outch_delta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp8).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp8).
  Qed.

  Definition outch_theta_channels := filter (fun s => negb (eqb x s) && negb (eqb y s)) (proc_channels r).

  Lemma outch_theta_channels_def : Permutation outch_theta_channels (map fst (L2 ++ theta_no_L2)).
  Proof.
    unfold outch_theta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp9).
    cbn [map fst].
    rewrite NoDup_filter_two; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp9).
  Qed.

  Definition outch_new_L1 := new_L1 L1 delta_no_L1 outch_theta_channels.
  Definition outch_delta_no_new_L1 := delta_no_new_L1 L1 delta_no_L1 outch_theta_channels.
  Definition outch_theta_no_new_L1 := theta_no_new_L1 L2 theta_no_L2 outch_delta_channels.
  Definition outch_new_L2 := new_L2 L1 gamma_no_L1 outch_delta_channels outch_theta_channels.
  Definition outch_gamma_no_new_L2 := gamma_no_new_L2 L1 gamma_no_L1 outch_delta_channels outch_theta_channels.
  Definition outch_delta_theta_no_new_L2 := delta_theta_no_new_L2 L1 L2 delta_no_L1 theta_no_L2 outch_gamma_channels outch_delta_channels outch_theta_channels.
  Definition outch_new_l1 := new_l1 outch_delta_channels outch_theta_channels.
  Definition outch_new_l2 := new_l2 outch_gamma_channels outch_delta_channels outch_theta_channels.

  (* Cut Q and R. *)
  Lemma outch_cut_q_r :
  cp (Proc_CompAndSplit x b outch_new_l1 q r) (outch_new_L1 ++ outch_delta_no_new_L1 ++ (y, dual a) :: outch_theta_no_new_L1).
  Proof.
    pose proof (new_l1_def _ _ _ outch_delta_channels_def outch_theta_channels) as Hperm.
    rewrite Hperm; fold outch_new_L1.

    pose proof Hcp8 as Hcp8'.
    pose proof (delta_split L1 delta_no_L1 outch_theta_channels) as Hperm1.
    rewrite Hperm1 in Hcp8'.
    pose proof Hcp9 as Hcp9'.
    pose proof (theta_split _ _ _ _ _ _ Hcp6 outch_Hcp8' outch_Hcp9' outch_Hcp10' outch_Hcp11' _ outch_delta_channels_def _ outch_theta_channels_def) as Hperm2.
    rewrite Hperm2 in Hcp9'.
    rewrite Permutation_middle in Hcp9'.

    constructor; auto.
    - apply (new_L1_ques _ _ _ _ _ _ Hcp4 Hcp6 outch_Hcp9' outch_Hcp11' _ outch_theta_channels_def).
    - intros z Hz1 Hz2.
      cbn in Hz2.
      destruct Hz2 as [Hz2 | Hz2].
      + subst z.
        rewrite <- (proc_channels_perm _ _ Hcp8) in Hy1.
        cbn in Hy1.
        rewrite Hperm1 in Hy1.
        rewrite map_app, in_app_iff in Hy1.
        tauto.
      + pose proof (delta_no_new_L1_theta_no_new_L1_disjoint L1 _ delta_no_L1 theta_no_L2 outch_delta_channels _ outch_theta_channels_def z).
        tauto.
  Qed.

  Lemma outch_q_r_perm :
  cp (Proc_CompAndSplit x b outch_new_l1 q r) ((y, dual a) :: outch_new_L2 ++ outch_delta_theta_no_new_L2).
  Proof.
    pose proof outch_cut_q_r as Hcp'.
    do 2 rewrite <- Permutation_middle in Hcp'.
    rewrite (delta_theta_split _ _ _ _ _ _ Hcp6 outch_Hcp7' outch_Hcp8' outch_Hcp9' outch_Hcp10' outch_Hcp11' _ outch_gamma_channels_def _ outch_delta_channels_def _ outch_theta_channels_def) in Hcp'.
    auto.
  Qed.

  Lemma outch_cut_p_q_r :
  cp (Proc_CompAndSplit y a outch_new_l2 p (Proc_CompAndSplit x b outch_new_l1 q r)) (outch_new_L2 ++ outch_gamma_no_new_L2 ++ outch_delta_theta_no_new_L2).
  Proof.
    pose proof (new_l2_def _ _ _ outch_gamma_channels_def outch_delta_channels outch_theta_channels) as Hperm.
    rewrite Hperm; fold outch_new_L2.

    pose proof Hcp7 as Hcp7'.
    pose proof (gamma_split L1 gamma_no_L1 outch_delta_channels outch_theta_channels) as Hperm1.
    rewrite Hperm1 in Hcp7'.
    pose proof outch_q_r_perm as Hcp'2.

    constructor; auto.
    - apply (new_L2_ques _ _ _ _ _ _ Hcp3 Hcp4 Hcp6 outch_Hcp7' outch_Hcp8' outch_Hcp9' outch_Hcp10' outch_Hcp11' _ outch_delta_channels_def _ outch_theta_channels_def).
    - apply (gamma_no_new_L2_delta_theta_no_new_L2_disjoint _ _ _ _ _ _ Hcp6 outch_Hcp8' outch_Hcp9' outch_Hcp10' outch_Hcp11' outch_gamma_channels _ outch_delta_channels_def _ outch_theta_channels_def).
  Qed.

  Lemma outch_p_q_r_perm :
  cp (Proc_CompAndSplit y a outch_new_l2 p (Proc_CompAndSplit x b outch_new_l1 q r)) senv.
  Proof.
    pose proof outch_cut_p_q_r as Hcp'.
    eapply cp_perm.
    1: apply Hcp'.
    rewrite Hcp5.
    symmetry.
    apply (new_L2_split _ _ _ _ _ _ Hcp6 outch_Hcp7' outch_Hcp8' outch_Hcp9' outch_Hcp10' outch_Hcp11' _ outch_gamma_channels_def _ outch_delta_channels_def _ outch_theta_channels_def).
  Qed.

  End OutCh_Cut.

  Lemma proc_cut_outch_inch :
  forall x y t l1 l2 p q r senv,
  cp (Proc_CompAndSplit x t l2 (Proc_OutChAndSplit x y l1 p q) (Proc_InCh x y r)) senv ->
  let (a, b) := match t with STyp_Times a b => (a, b) | _ => (STyp_Zero, STyp_Zero) end in
  t = STyp_Times a b /\
  let new_l1 := outch_new_l1 x y q r in
  let new_l2 := outch_new_l2 x y p q r in
  (~ In y (proc_channels q) ->
   cp (Proc_CompAndSplit y a new_l2 p (Proc_CompAndSplit x b new_l1 q r)) senv).
  Proof.
    intros x y t l1 l2 p q r senv Hcp.
    pose proof (proc_outch_cut_inv x y t l1 l2 p q r senv Hcp) as (a & b & L1 & L2 & gamma_no_L1 & delta_no_L1 & gamma_delta_no_L2 & theta_no_L2 & Ht & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6 & Hcp7 & Hcp8 & Hcp9 & Hcp10).
    subst t; split; auto.
    cbn; intros Hy1.
    pose proof (outch_p_q_r_perm x y (STyp_Times a b) l1 l2 p q r senv Hcp Hy1 a b L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 Hcp3 Hcp4 Hcp5 Hcp6 Hcp7 Hcp8 Hcp9 Hcp10) as Hcp'.
    cbn.
    apply Hcp'.
  Qed.

  Lemma proc_cut_left_case :
  forall x t l b p q r senv,
  cp (Proc_CompAndSplit x t l (Proc_OutLeft x b p) (Proc_InCase x q r)) senv ->
  let (a, b) := match t with STyp_Plus a b => (a, b) | _ => (STyp_Zero, STyp_Zero) end in
  t = STyp_Plus a b /\
  cp (Proc_CompAndSplit x a l p q) senv.
  Proof.
    intros x t l b p q r senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l.

    (* Invert Hcp'4 *)
    destruct (cp_inv_outleft _ _ _ _ Hcp'4) as (a' & gamma' & Hcp''1 & Hcp''2).
    pose proof Hcp'4 as Hcp''3.
    apply cp_senv_valid in Hcp''3.
    rewrite senv_valid_cons in Hcp''3.
    assert (Hcp''4 : In (x, STyp_Plus a' b) ((x, t) :: gamma ++ delta1)) by (rewrite <- Hcp''2; left; auto).
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
    assert (Hcp'''5 : In (x, STyp_With a'' b'') ((x, STyp_With (dual a') (dual b)) :: gamma ++ delta2)) by (rewrite <- Hcp'''3; left; auto).
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
  forall x t l a p q r senv,
  cp (Proc_CompAndSplit x t l (Proc_OutRight x a p) (Proc_InCase x q r)) senv ->
  let (a, b) := match t with STyp_Plus a b => (a, b) | _ => (STyp_Zero, STyp_Zero) end in
  t = STyp_Plus a b /\
  cp (Proc_CompAndSplit x b l p r) senv.
  Proof.
    intros x t l a p q r senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l.

    (* Invert Hcp'4 *)
    destruct (cp_inv_outright _ _ _ _ Hcp'4) as (b' & gamma' & Hcp''1 & Hcp''2).
    pose proof Hcp'4 as Hcp''3.
    apply cp_senv_valid in Hcp''3.
    rewrite senv_valid_cons in Hcp''3.
    assert (Hcp''4 : In (x, STyp_Plus a b') ((x, t) :: gamma ++ delta1)) by (rewrite <- Hcp''2; left; auto).
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
    assert (Hcp'''5 : In (x, STyp_With a'' b'') ((x, STyp_With (dual a) (dual b')) :: gamma ++ delta2)) by (rewrite <- Hcp'''3; left; auto).
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
  let a := match t with STyp_Excl a => a | _ => STyp_Zero end in
  t = STyp_Excl a /\
  (~ In y (proc_forbidden q z) -> cp (Proc_CompAndSplit y a l p (proc_rename q z y)) senv).
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

    cbn; split; auto.

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

    rewrite <- Hcp'6.
    rewrite Hcp''3 in Hcp''2.
    rewrite Hcp'''2 in Hrename.
    constructor; auto.
  Qed.

  Lemma proc_cut_server_null :
  forall x t l y a p q senv,
  cp (Proc_CompAndSplit x t l (Proc_Server x y p) (Proc_ClientNull x a q)) senv ->
  cp (weaken_list (map (fun s => (s, proc_channel_type p s)) (filter (fun s => if in_dec eq_dec s l then false else true) (filter (fun s => negb (eqb y s)) (proc_channels p)))) q) senv.
  Proof.
    intros x t l y a p q senv Hcp.
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
    destruct (cp_inv_client_null _ _ _ _ Hcp'5) as (gamma'' & Hcp'''1 & Hcp'''2).
    pose proof Hcp'5 as Hcp'''3.
    apply cp_senv_valid in Hcp'''3.
    rewrite senv_valid_cons in Hcp'''3.
    cbn in Hcp'''2.
    assert (Hcp'''4 : In (x, STyp_Ques a) ((x, STyp_Ques (dual a')) :: gamma ++ delta2)) by (rewrite <- Hcp'''2; left; auto).
    cbn in Hcp'''4.
    destruct Hcp'''4 as [Hcp'''4 | Hcp'''4].
    2: apply (in_map fst) in Hcp'''4; cbn in Hcp'''4; tauto.
    injection Hcp'''4; intros Heq; subst a; clear Hcp'''4.
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

    assert (HL'2 : map (fun s => (s, proc_channel_type p s)) (map fst L') = L').
    { rewrite map_map; cbn.
      erewrite map_ext_in.
      1: apply map_id.
      cbn; intros z Hz.
      rewrite <- HL'1 in Hz.
      destruct z as [w t]; cbn.
      rewrite (proc_channel_type_correct p _ w t Hcp''2 ltac:(right; rewrite in_app_iff; auto)); auto.
    }

    rewrite HL'2; apply weaken_list_correct; auto.

    - rewrite <- HL'1; eauto with senv_valid.

    - rewrite <- HL'1.
      rewrite Hcp''3 in Hcp''1.
      rewrite map_app, Forall_app in Hcp''1.
      tauto.

    - unfold senv_disjoint.
      intros z.
      rewrite <- HL'1.
      rewrite <- Hcp'6 in Hcp.
      rewrite Permutation_app_swap_app in Hcp.
      assert (H : senv_disjoint delta1 (gamma ++ delta2)) by eauto with senv_valid senv_disjoint.
      specialize (H z); auto.
  Qed.

  (* The condition that process P is a server cannot be omitted.
     Otherwise it may introduce channels which are not clients.
   *)
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

    pose proof Hcp'4 as Hp; rewrite <- Heqp in Hp; cbn.
    rewrite (proc_channels_filter_one _ _ _ _ Hp); clear Hp.

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
          assert (H : senv_disjoint delta1 delta2) by eauto with senv_valid senv_disjoint.
          apply (H _ Hw Hin).
    }

    rewrite <- Hcp'6.
    rewrite app_assoc.
    rewrite app_assoc in Hnew_cp.
    rewrite Permutation_app_comm in Hnew_cp.
    cbn in Hnew_cp.
    rewrite Permutation_app_comm in Hnew_cp.
    replace delta2 with ([] ++ delta2) by auto.

    constructor; auto.
    - rewrite <- Hcp''3; auto.
    - unfold senv_disjoint; intros; auto.
    - rewrite Heqp, app_nil_r; auto.
  Qed.

  Section Proc_Server_Split_Comp.

  Variable (x y z : chn).
  Variable (t1 t2 : STyp).
  Variable (l1 l2 : list chn).
  Variable (p q r : Process).
  Variable (senv : SEnv).
  Hypothesis (Hcp : cp (Proc_CompAndSplit x t2 l2 (Proc_Server x y p) (Proc_CompAndSplit z t1 l1 q r)) senv).
  Hypothesis (Hx1 : In x l1).

  Lemma server_split_comp_inv :
  exists L1 L1' L2 t gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2,
    l1 = map fst L1' /\
    l2 = map fst L2 /\
    t2 = STyp_Excl t /\
    Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1) /\
    Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2) /\
    Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd theta_no_L2) /\
    Permutation L1' ((x, STyp_Ques (dual t)) :: L1) /\
    Permutation (L2 ++ theta_no_L2 ++ gamma_delta_no_L2) senv /\
    Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2) /\
    cp (Proc_Server x y p) ((x, STyp_Excl t) :: L2 ++ theta_no_L2) /\
    cp q ((z, t1) :: (x, STyp_Ques (dual t)) :: L1 ++ gamma_no_L1) /\
    cp r ((z, dual t1) :: (x, STyp_Ques (dual t)) :: L1 ++ delta_no_L1) /\
    cp (Proc_CompAndSplit z t1 l1 q r) ((x, STyp_Ques (dual t)) :: L2 ++ gamma_delta_no_L2).
  Proof.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (L2 & theta_no_L2 & gamma_delta_no_L2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6).
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp5) as (L1' & gamma_no_L1 & delta_no_L1 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l1 l2.

    (* t2 is STyp_Excl t *)
    pose proof (cp_inv_server _ _ _ _ Hcp4) as (t & theta & Hcp''1 & Hcp''2 & Hcp''3).
    assert (Hx : In (x, STyp_Excl t) ((x, t2) :: L2 ++ theta_no_L2)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hx.
    destruct Hx as [Hx | Hx].
    2: apply cp_senv_valid in Hcp4; rewrite senv_valid_cons in Hcp4; apply (in_map fst) in Hx; tauto.
    injection Hx; intros; subst t2; clear Hx.
    apply Permutation_cons_inv in Hcp''3.

    (* (x, STyp_Ques (dual t)) is in L1' *)
    cbn in Hcp'6.
    assert (Hx : In (x, STyp_Ques (dual t)) L1').
    { rewrite Permutation_middle in Hcp'4, Hcp'5.
      assert (Hdisjoint1 : senv_disjoint L1' ((z, t1) :: gamma_no_L1)) by eauto with senv_valid senv_disjoint.
      assert (Hdisjoint2 : senv_disjoint L1' ((z, dual t1) :: delta_no_L1)) by eauto with senv_valid senv_disjoint.
      specialize (Hdisjoint1 x Hx1).
      specialize (Hdisjoint2 x Hx1).
      cbn in Hdisjoint1, Hdisjoint2.
      assert (Hx2 : In (x, STyp_Ques (dual t)) (L1' ++ gamma_no_L1 ++ delta_no_L1)) by (rewrite Hcp'6; left; cbn; auto).
      do 2 rewrite in_app_iff in Hx2.
      destruct Hx2 as [Hx2 | [Hx2 | Hx2]]; auto.
      all: apply (in_map fst) in Hx2; tauto.
    }

    pose proof (in_split_perm _ _ Hx) as (L1 & HL1).
    rewrite HL1 in Hcp'6.
    cbn in Hcp'6.
    apply Permutation_cons_inv in Hcp'6.

    exists L1; exists L1'; exists L2; exists t; exists gamma_no_L1; exists delta_no_L1; exists gamma_delta_no_L2; exists theta_no_L2.
    repeat split; auto.
    2: rewrite Hcp''3 in Hcp''1; rewrite map_app, Forall_app in Hcp''1; apply Hcp''1.
    2,3: rewrite app_comm_cons, <- HL1; auto.
    eapply Forall_inv_tail.
    Unshelve.
    2: exact (snd (x, STyp_Ques (dual t))).
    rewrite <- map_cons.
    rewrite <- HL1; auto.
  Qed.

  Variable (L1 L1' L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 : SEnv).
  Variable (t : STyp).
  Hypothesis (Hcp2 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd theta_no_L2)).
  Hypothesis (Hcp3 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1)).
  Hypothesis (Hcp4 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2)).
  Hypothesis (Hcp5 : Permutation (L2 ++ theta_no_L2 ++ gamma_delta_no_L2) senv).
  Hypothesis (Hcp6 : Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hcp7 : cp q ((z, t1) :: (x, STyp_Ques (dual t)) :: L1 ++ gamma_no_L1)).
  Hypothesis (Hcp8 : cp r ((z, dual t1) :: (x, STyp_Ques (dual t)) :: L1 ++ delta_no_L1)).
  Hypothesis (Hcp9 : cp (Proc_Server x y p) ((x, STyp_Excl t) :: L2 ++ theta_no_L2)).
  Hypothesis (Hcp10 : cp (Proc_CompAndSplit z t1 l1 q r) ((x, STyp_Ques (dual t)) :: L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hx2 : ~ In z (proc_channels (Proc_Server x y p))).

  Lemma comp_split_Hcp7' : senv_valid (L1 ++ gamma_no_L1).
  Proof. apply cp_senv_valid in Hcp7; do 2 rewrite senv_valid_cons in Hcp7; tauto. Qed.

  Lemma comp_split_Hcp8' : senv_valid (L1 ++ delta_no_L1).
  Proof. apply cp_senv_valid in Hcp8; do 2 rewrite senv_valid_cons in Hcp8; tauto. Qed.

  Lemma comp_split_Hcp9' : senv_valid (L2 ++ theta_no_L2).
  Proof. apply cp_senv_valid in Hcp9; rewrite senv_valid_cons in Hcp9; tauto. Qed.

  Lemma comp_split_Hcp10' : senv_valid (L1 ++ gamma_no_L1 ++ delta_no_L1).
  Proof. rewrite <- Hcp6 in Hcp10; apply cp_senv_valid in Hcp10; rewrite senv_valid_cons in Hcp10; tauto. Qed.

  Lemma comp_split_Hcp11' : senv_valid (L2 ++ gamma_delta_no_L2 ++ theta_no_L2).
  Proof. rewrite <- Hcp5 in Hcp; apply cp_senv_valid in Hcp; rewrite (Permutation_app_comm gamma_delta_no_L2); auto. Qed.

  Definition comp_split_gamma_channels := filter (fun s => negb (eqb z s) && negb (eqb x s)) (proc_channels q).

  Lemma comp_split_gamma_channels_def : Permutation comp_split_gamma_channels (map fst (L1 ++ gamma_no_L1)).
  Proof.
    unfold comp_split_gamma_channels.
    rewrite <- (proc_channels_perm _ _ Hcp7).
    cbn [map fst].
    rewrite NoDup_filter_two; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp7).
  Qed.

  Definition comp_split_delta_channels := filter (fun s => negb (eqb z s) && negb (eqb x s)) (proc_channels r).

  Lemma comp_split_delta_channels_def : Permutation comp_split_delta_channels (map fst (L1 ++ delta_no_L1)).
  Proof.
    unfold comp_split_delta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp8).
    cbn [map fst].
    rewrite NoDup_filter_two; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp8).
  Qed.

  Definition comp_split_theta_channels := filter (fun s => negb (eqb x s)) (proc_channels (Proc_Server x y p)).

  Lemma comp_split_theta_channels_def : Permutation comp_split_theta_channels (map fst (L2 ++ theta_no_L2)).
  Proof.
    unfold comp_split_theta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp9).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp9).
  Qed.

  Definition comp_split_new_L3 := new_L3 L2 theta_no_L2 comp_split_gamma_channels.
  Definition comp_split_gamma_no_new_L3 := gamma_no_new_L3 L1 gamma_no_L1 comp_split_theta_channels.
  Definition comp_split_theta_no_new_L3 := theta_no_new_L3 L2 theta_no_L2 comp_split_gamma_channels.
  Definition comp_split_new_l3 := new_l3 comp_split_gamma_channels comp_split_theta_channels.

  Definition comp_split_new_L1 := new_L1 L1 delta_no_L1 comp_split_theta_channels.
  Definition comp_split_delta_no_new_L1 := delta_no_new_L1 L1 delta_no_L1 comp_split_theta_channels.
  Definition comp_split_theta_no_new_L1 := theta_no_new_L1 L2 theta_no_L2 comp_split_delta_channels.
  Definition comp_split_new_l1 := new_l1 comp_split_delta_channels comp_split_theta_channels.

  Definition comp_split_new_L4 := new_L4 L1 gamma_no_L1 comp_split_delta_channels comp_split_theta_channels.
  Definition comp_split_gamma_no_new_L3_no_new_L4 := gamma_no_new_L3_no_new_L4 L1 gamma_no_L1 comp_split_delta_channels comp_split_theta_channels.
  Definition comp_split_delta_no_new_L1_no_new_L4 := delta_no_new_L1_no_new_L4 L1 delta_no_L1 comp_split_gamma_channels comp_split_theta_channels.
  Definition comp_split_new_l4 := new_l4 comp_split_gamma_channels comp_split_delta_channels comp_split_theta_channels.

  Lemma comp_split_q_perm :
  cp q ((x, STyp_Ques (dual t)) :: comp_split_new_L3 ++ (z, t1) :: comp_split_gamma_no_new_L3).
  Proof.
    pose proof Hcp7 as Hcp12.
    rewrite perm_swap in Hcp12.
    rewrite (l3_gamma_split _ _ _ _ _ _ Hcp6 comp_split_Hcp7' comp_split_Hcp9' comp_split_Hcp10' comp_split_Hcp11' _ comp_split_gamma_channels_def _ comp_split_theta_channels_def) in Hcp12.
    rewrite Permutation_middle in Hcp12.
    apply Hcp12.
  Qed.

  Lemma comp_split_r_perm :
  cp r ((x, STyp_Ques (dual t)) :: comp_split_new_L1 ++ (z, dual t1) :: comp_split_delta_no_new_L1).
  Proof.
    pose proof Hcp8 as Hcp12.
    rewrite perm_swap in Hcp12.
    rewrite (delta_split L1 delta_no_L1 comp_split_theta_channels) in Hcp12.
    rewrite Permutation_middle in Hcp12.
    apply Hcp12.
  Qed.

  (* Cut P and Q *)
  Lemma comp_split_comp_p_q :
  cp (Proc_CompAndSplit x (STyp_Excl t) comp_split_new_l3 (Proc_Server x y p) q) (comp_split_new_L3 ++ comp_split_theta_no_new_L3 ++ (z, t1) :: comp_split_gamma_no_new_L3).
  Proof.
    pose proof (new_l3_def _ _ comp_split_gamma_channels _ comp_split_theta_channels_def) as Hperm.
    rewrite Hperm; fold comp_split_new_L3.

    pose proof Hcp9 as Hcp12.
    rewrite (l3_theta_split L2 theta_no_L2 comp_split_gamma_channels) in Hcp12.
    pose proof comp_split_q_perm as Hcp13.
    constructor; auto.

    - apply (new_L3_ques _ _ _ _ _ _ Hcp4 Hcp6 comp_split_Hcp9' comp_split_Hcp11' _ comp_split_gamma_channels_def).

    - intros w Hw1 Hw2.
      cbn in Hw2.
      destruct Hw2 as [Hw2 | Hw2].
      + subst w.
        rewrite <- (proc_channels_perm _ _ Hcp12) in Hx2.
        cbn in Hx2.
        rewrite map_app, in_app_iff in Hx2.
        tauto.
      + pose proof (gamma_no_new_L3_theta_no_new_L3_disjoint L1 L2 gamma_no_L1 theta_no_L2 comp_split_gamma_channels _ comp_split_theta_channels_def w).
        tauto.
  Qed.

  (* Cut P and R *)
  Lemma comp_split_comp_p_r :
  cp (Proc_CompAndSplit x (STyp_Excl t) comp_split_new_l1 (Proc_Server x y p) r) (comp_split_new_L1 ++ comp_split_theta_no_new_L1 ++ (z, dual t1) :: comp_split_delta_no_new_L1).
  Proof.
    pose proof (new_l1_def _ _ _ comp_split_delta_channels_def comp_split_theta_channels) as Hperm.
    rewrite Hperm; fold comp_split_new_L1.

    pose proof Hcp9 as Hcp12.
    rewrite (theta_split _ _ _ _ _ _ Hcp6 comp_split_Hcp8' comp_split_Hcp9' comp_split_Hcp10' comp_split_Hcp11' _ comp_split_delta_channels_def _ comp_split_theta_channels_def) in Hcp12.
    pose proof comp_split_r_perm as Hcp13.
    constructor; auto.

    - apply (new_L1_ques _ _ _ _ _ _ Hcp4 Hcp6 comp_split_Hcp9' comp_split_Hcp11' _ comp_split_theta_channels_def).

    - intros w Hw1 Hw2.
      cbn in Hw2.
      destruct Hw2 as [Hw2 | Hw2].
      + subst w.
        rewrite <- (proc_channels_perm _ _ Hcp12) in Hx2.
        cbn in Hx2.
        rewrite map_app, in_app_iff in Hx2.
        tauto.
      + pose proof (delta_no_new_L1_theta_no_new_L1_disjoint L1 L2 delta_no_L1 theta_no_L2 comp_split_delta_channels _ comp_split_theta_channels_def w).
        tauto.
  Qed.

  (* Cut (P | Q) and (P | R) *)

  Lemma comp_split_p_q_perm :
  cp (Proc_CompAndSplit x (STyp_Excl t) comp_split_new_l3 (Proc_Server x y p) q) ((z, t1) :: L2 ++ theta_no_L2 ++ comp_split_new_L4 ++ comp_split_gamma_no_new_L3_no_new_L4).
  Proof.
    pose proof comp_split_comp_p_q as Hcp12.
    rewrite app_assoc in Hcp12.
    rewrite <- (l3_theta_split L2 theta_no_L2 comp_split_gamma_channels) in Hcp12.
    rewrite <- Permutation_middle in Hcp12.
    rewrite <- app_assoc in Hcp12.
    rewrite (l4_gamma_split L1 gamma_no_L1 comp_split_delta_channels comp_split_theta_channels) in Hcp12.
    apply Hcp12.
  Qed.

  Lemma comp_split_p_r_perm :
  cp (Proc_CompAndSplit x (STyp_Excl t) comp_split_new_l1 (Proc_Server x y p) r) ((z, dual t1) :: L2 ++ theta_no_L2 ++ comp_split_new_L4 ++ comp_split_delta_no_new_L1_no_new_L4).
  Proof.
    pose proof comp_split_comp_p_r as Hcp12.
    rewrite app_assoc in Hcp12.
    rewrite <- (theta_split _ _ _ _ _ _ Hcp6 comp_split_Hcp8' comp_split_Hcp9' comp_split_Hcp10' comp_split_Hcp11' _ comp_split_delta_channels_def _ comp_split_theta_channels_def) in Hcp12.
    rewrite <- Permutation_middle in Hcp12.
    rewrite <- app_assoc in Hcp12.
    rewrite (l4_delta_split _ _ _ _ _ _ Hcp6 comp_split_Hcp7' comp_split_Hcp8' comp_split_Hcp9' comp_split_Hcp10' comp_split_Hcp11' _ comp_split_gamma_channels_def _ comp_split_delta_channels_def _ comp_split_theta_channels_def) in Hcp12.
    apply Hcp12.
  Qed.

  Lemma comp_split_comp_p_q_r :
  cp (Proc_CompAndSplit z t1 (comp_split_theta_channels ++ comp_split_new_l4) (Proc_CompAndSplit x (STyp_Excl t) comp_split_new_l3 (Proc_Server x y p) q) (Proc_CompAndSplit x (STyp_Excl t) comp_split_new_l1 (Proc_Server x y p) r)) (L2 ++ theta_no_L2 ++ comp_split_new_L4 ++ comp_split_gamma_no_new_L3_no_new_L4 ++ comp_split_delta_no_new_L1_no_new_L4).
  Proof.
    pose proof (new_l4_def _ _ _ comp_split_gamma_channels_def comp_split_delta_channels comp_split_theta_channels) as Hperm.
    rewrite Hperm; fold comp_split_new_L4.
    do 2 rewrite app_assoc.
    rewrite <- (app_assoc _ _ comp_split_new_L4).
    rewrite comp_split_theta_channels_def.
    rewrite <- map_app, <- app_assoc.
    pose proof comp_split_p_q_perm as Hcp12.
    pose proof comp_split_p_r_perm as Hcp13.
    do 2 rewrite app_assoc in Hcp12, Hcp13.
    rewrite <- (app_assoc L2) in Hcp12, Hcp13.
    constructor; auto.

    - do 2 rewrite map_app, Forall_app.
      repeat split; auto.
      apply (new_L4_ques _ _ _ _ _ _ Hcp3 Hcp6 comp_split_Hcp7' comp_split_Hcp8' comp_split_Hcp9' comp_split_Hcp10' comp_split_Hcp11' _ comp_split_gamma_channels_def _ comp_split_delta_channels_def _ comp_split_theta_channels_def).

    - intros w Hw1 Hw2.
      pose proof (gamma_no_new_L3_no_new_L4_delta_no_new_L1_no_new_L4_disjoint L1 gamma_no_L1 delta_no_L1 comp_split_gamma_channels _ comp_split_delta_channels_def comp_split_theta_channels w).
      tauto.
  Qed.

  Lemma comp_split_p_q_r_perm :
  cp (Proc_CompAndSplit z t1 (comp_split_theta_channels ++ comp_split_new_l4) (Proc_CompAndSplit x (STyp_Excl t) comp_split_new_l3 (Proc_Server x y p) q) (Proc_CompAndSplit x (STyp_Excl t) comp_split_new_l1 (Proc_Server x y p) r)) senv.
  Proof.
    eapply cp_perm.
    1: apply comp_split_comp_p_q_r.
    rewrite <- Hcp5.
    do 2 apply Permutation_app_head.
    symmetry; apply (new_L4_split _ _ _ _ _ _ Hcp6 comp_split_Hcp7' comp_split_Hcp8' comp_split_Hcp9' comp_split_Hcp10' comp_split_Hcp11' _ comp_split_gamma_channels_def _ comp_split_delta_channels_def _ comp_split_theta_channels_def).
  Qed.

  End Proc_Server_Split_Comp.

  Lemma proc_cut_server_split_comp :
  forall x t1 t2 l1 l2 y p z q r senv,
  cp (Proc_CompAndSplit x t2 l2 (Proc_Server x y p) (Proc_CompAndSplit z t1 l1 q r)) senv ->
  In x l1 ->
  ~ In z (proc_channels (Proc_Server x y p)) ->
  cp (Proc_CompAndSplit z t1 (comp_split_theta_channels x y p ++ comp_split_new_l4 x y z p q r) (Proc_CompAndSplit x t2 (comp_split_new_l3 x y z p q) (Proc_Server x y p) q) (Proc_CompAndSplit x t2 (comp_split_new_l1 x y z p r) (Proc_Server x y p) r)) senv.
  Proof.
    intros x t1 t2 l1 l2 y p z q r senv Hcp Hx1 Hx2.
    pose proof (server_split_comp_inv x y z t1 t2 l1 l2 p q r senv Hcp Hx1) as (L1 & _ & L2 & t & gamma_no_L1 & delta_no_L1 & gamma_delta_no_L2 & theta_no_L2 & _ & _ & Hcp1 & Hcp2 & Hcp3 & Hcp4 & _ & Hcp5 & Hcp6 & Hcp7 & Hcp8 & Hcp9 & Hcp10).
    subst t2.
    apply (comp_split_p_q_r_perm x y z t1 (STyp_Excl t) l1 l2 p q r senv Hcp L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 t Hcp4 Hcp2 Hcp3 Hcp5 Hcp6 Hcp8 Hcp9 Hcp7 Hcp10 Hx2).
  Qed.

  Section Proc_Server_Split_Outch.

  Variable (x y z w : chn).
  Variable (t' : STyp).
  Variable (l1 l2 : list chn).
  Variable (p q r : Process).
  Variable (senv : SEnv).
  Hypothesis (Hcp : cp (Proc_CompAndSplit x t' l2 (Proc_Server x y p) (Proc_OutChAndSplit z w l1 q r)) senv).
  Hypothesis (Hx1 : In x l1).

  Lemma server_split_outch_inv :
  exists a b L1 L1' L2 t gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2,
    l1 = map fst L1' /\
    l2 = map fst L2 /\
    t' = STyp_Excl t /\
    ~ In z (proc_channels (Proc_Server x y p)) /\
    ~ In z (map fst (L1 ++ gamma_no_L1)) /\
    Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1) /\
    Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2) /\
    Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd theta_no_L2) /\
    Permutation L1' ((x, STyp_Ques (dual t)) :: L1) /\
    Permutation ((z, STyp_Times a b) :: L2 ++ theta_no_L2 ++ gamma_delta_no_L2) senv /\
    Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2) /\
    cp (Proc_Server x y p) ((x, STyp_Excl t) :: L2 ++ theta_no_L2) /\
    cp q ((w, a) :: (x, STyp_Ques (dual t)) :: L1 ++ gamma_no_L1) /\
    cp r ((z, b) :: (x, STyp_Ques (dual t)) :: L1 ++ delta_no_L1) /\
    cp (Proc_OutChAndSplit z w l1 q r) ((z, STyp_Times a b) :: (x, STyp_Ques (dual t)) :: L2 ++ gamma_delta_no_L2).
  Proof.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (L2 & theta_no_L2 & gamma_delta_z_no_L2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6).
    destruct (cp_inv_outch_and_split _ _ _ _ _ _ Hcp5) as (a & b & L1' & gamma_no_L1 & delta_no_L1 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6 & Hcp'7).
    subst l1 l2.

    (* t2 is STyp_Excl t *)
    pose proof (cp_inv_server _ _ _ _ Hcp4) as (t & theta & Hcp''1 & Hcp''2 & Hcp''3).
    assert (Hx : In (x, STyp_Excl t) ((x, t') :: L2 ++ theta_no_L2)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hx.
    destruct Hx as [Hx | Hx].
    2: apply cp_senv_valid in Hcp4; rewrite senv_valid_cons in Hcp4; apply (in_map fst) in Hx; tauto.
    injection Hx; intros; subst t'; clear Hx.
    apply Permutation_cons_inv in Hcp''3.

    (* (x, STyp_Ques (dual t)) is in L1' *)
    cbn in Hcp'7.
    assert (Hx : In (x, STyp_Ques (dual t)) L1').
    { rewrite Permutation_middle in Hcp'5, Hcp'6.
      assert (Hdisjoint1 : senv_disjoint L1' ((w, a) :: gamma_no_L1)) by eauto with senv_valid senv_disjoint.
      assert (Hdisjoint2 : senv_disjoint L1' ((z, b) :: delta_no_L1)) by eauto with senv_valid senv_disjoint.
      specialize (Hdisjoint1 x Hx1).
      specialize (Hdisjoint2 x Hx1).
      cbn in Hdisjoint1, Hdisjoint2.
      assert (Hx2 : In (x, STyp_Ques (dual t)) ((z, STyp_Times a b) :: L1' ++ gamma_no_L1 ++ delta_no_L1)).
      { rewrite Hcp'7; left; auto. }
      cbn in Hx2.
      destruct Hx2 as [Hx2 | Hx2].
      1: injection Hx2; discriminate.
      do 2 rewrite in_app_iff in Hx2.
      destruct Hx2 as [Hx2 | [Hx2 | Hx2]]; auto.
      all: apply (in_map fst) in Hx2; tauto.
    }

    pose proof (in_split_perm _ _ Hx) as (L1 & HL1).
    rewrite HL1 in Hcp'7.
    cbn in Hcp'7.
    rewrite perm_swap in Hcp'7.
    apply Permutation_cons_inv in Hcp'7.

    (* z is part of gamma_delta_z_no_L2 *)
    assert (Hz : In (z, STyp_Times a b) (L2 ++ gamma_delta_z_no_L2)).
    { rewrite <- Hcp'7; left; auto. }
    rewrite in_app_iff in Hz.
    destruct Hz as [Hz | Hz].
    1: rewrite Forall_forall in Hcp1; specialize (Hcp1 _ ltac:(apply in_map; apply Hz)); cbn in Hcp1; contradiction.
    pose proof (in_split_perm _ _ Hz) as (gamma_delta_no_L2 & HL2).
    rewrite HL2 in Hcp'7.
    cbn in Hcp'7.
    rewrite <- Permutation_middle in Hcp'7.
    apply Permutation_cons_inv in Hcp'7.

    (* z not in L1 *)
    assert (Hcp'8 : ~ In z (map fst L1)).
    { apply cp_senv_valid in Hcp'6.
      rewrite senv_valid_cons in Hcp'6.
      rewrite HL1 in Hcp'6.
      cbn in Hcp'6.
      rewrite map_app, in_app_iff in Hcp'6.
      tauto.
    }

    exists a; exists b; exists L1; exists L1'; exists L2; exists t; exists gamma_no_L1; exists delta_no_L1; exists gamma_delta_no_L2; exists theta_no_L2.
    repeat split; auto.
    4: rewrite Hcp''3 in Hcp''1; rewrite map_app, Forall_app in Hcp''1; apply Hcp''1.
    5,6: rewrite app_comm_cons, <- HL1; auto.
    4: rewrite <- Hcp6, HL2; do 2 rewrite <- Permutation_middle; auto.
    4: rewrite HL2 in Hcp5; rewrite perm_swap; rewrite Permutation_middle; auto.
    3: eapply Forall_inv_tail; rewrite <- map_cons; rewrite <- HL1; auto.
    2: rewrite map_app, in_app_iff; tauto.

    rewrite <- (proc_channels_perm _ _ Hcp4); cbn.
    intros Hin.
    destruct Hin as [Hin | Hin].
    - rewrite  HL1 in Hcp'6.
      apply cp_senv_valid in Hcp'6.
      rewrite senv_valid_cons in Hcp'6.
      cbn in Hcp'6.
      tauto.
    - rewrite map_app, in_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      + assert (Hdisjoint : senv_disjoint L2 gamma_delta_z_no_L2) by eauto with senv_valid senv_disjoint.
        specialize (Hdisjoint z).
        apply (in_map fst) in Hz; cbn in Hz.
        tauto.
      + specialize (Hcp3 z ltac:(auto)).
        rewrite HL2 in Hcp3.
        cbn in Hcp3; tauto.
  Qed.

  Variable (L1 L1' L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 : SEnv).
  Variable (a b t : STyp).
  Hypothesis (Hcp0 : ~ In z (map fst (L1 ++ gamma_no_L1))).
  Hypothesis (Hcp1 : ~ In z (proc_channels (Proc_Server x y p))).
  Hypothesis (Hcp2 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd theta_no_L2)).
  Hypothesis (Hcp3 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1)).
  Hypothesis (Hcp4 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2)).
  Hypothesis (Hcp5 : Permutation ((z, STyp_Times a b) :: L2 ++ theta_no_L2 ++ gamma_delta_no_L2) senv).
  Hypothesis (Hcp6 : Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hcp7 : cp q ((w, a) :: (x, STyp_Ques (dual t)) :: L1 ++ gamma_no_L1)).
  Hypothesis (Hcp8 : cp r ((z, b) :: (x, STyp_Ques (dual t)) :: L1 ++ delta_no_L1)).
  Hypothesis (Hcp9 : cp (Proc_Server x y p) ((x, STyp_Excl t) :: L2 ++ theta_no_L2)).
  Hypothesis (Hcp10 : cp (Proc_OutChAndSplit z w l1 q r) ((z, STyp_Times a b) :: (x, STyp_Ques (dual t)) :: L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hx2 : ~ In w (proc_channels (Proc_Server x y p))).

  Lemma outch_split_Hcp7' : senv_valid (L1 ++ gamma_no_L1).
  Proof. apply cp_senv_valid in Hcp7; do 2 rewrite senv_valid_cons in Hcp7; tauto. Qed.

  Lemma outch_split_Hcp8' : senv_valid (L1 ++ delta_no_L1).
  Proof. apply cp_senv_valid in Hcp8; do 2 rewrite senv_valid_cons in Hcp8; tauto. Qed.

  Lemma outch_split_Hcp9' : senv_valid (L2 ++ theta_no_L2).
  Proof. apply cp_senv_valid in Hcp9; rewrite senv_valid_cons in Hcp9; tauto. Qed.

  Lemma outch_split_Hcp10' : senv_valid (L1 ++ gamma_no_L1 ++ delta_no_L1).
  Proof. rewrite <- Hcp6 in Hcp10; apply cp_senv_valid in Hcp10; do 2 rewrite senv_valid_cons in Hcp10; tauto. Qed.

  Lemma outch_split_Hcp11' : senv_valid (L2 ++ gamma_delta_no_L2 ++ theta_no_L2).
  Proof. rewrite <- Hcp5 in Hcp; apply cp_senv_valid in Hcp; rewrite senv_valid_cons in Hcp; rewrite (Permutation_app_comm gamma_delta_no_L2); tauto. Qed.

  Definition outch_split_gamma_channels := filter (fun s => negb (eqb w s) && negb (eqb x s)) (proc_channels q).

  Lemma outch_split_gamma_channels_def : Permutation outch_split_gamma_channels (map fst (L1 ++ gamma_no_L1)).
  Proof.
    unfold outch_split_gamma_channels.
    rewrite <- (proc_channels_perm _ _ Hcp7).
    cbn [map fst].
    rewrite NoDup_filter_two; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp7).
  Qed.

  Definition outch_split_delta_channels := filter (fun s => negb (eqb z s) && negb (eqb x s)) (proc_channels r).

  Lemma outch_split_delta_channels_def : Permutation outch_split_delta_channels (map fst (L1 ++ delta_no_L1)).
  Proof.
    unfold outch_split_delta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp8).
    cbn [map fst].
    rewrite NoDup_filter_two; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp8).
  Qed.

  Definition outch_split_theta_channels := filter (fun s => negb (eqb x s)) (proc_channels (Proc_Server x y p)).

  Lemma outch_split_theta_channels_def : Permutation outch_split_theta_channels (map fst (L2 ++ theta_no_L2)).
  Proof.
    unfold outch_split_theta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp9).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp9).
  Qed.

  Definition outch_split_new_L3 := new_L3 L2 theta_no_L2 outch_split_gamma_channels.
  Definition outch_split_gamma_no_new_L3 := gamma_no_new_L3 L1 gamma_no_L1 outch_split_theta_channels.
  Definition outch_split_theta_no_new_L3 := theta_no_new_L3 L2 theta_no_L2 outch_split_gamma_channels.
  Definition outch_split_new_l3 := new_l3 outch_split_gamma_channels outch_split_theta_channels.

  Definition outch_split_new_L1 := new_L1 L1 delta_no_L1 outch_split_theta_channels.
  Definition outch_split_delta_no_new_L1 := delta_no_new_L1 L1 delta_no_L1 outch_split_theta_channels.
  Definition outch_split_theta_no_new_L1 := theta_no_new_L1 L2 theta_no_L2 outch_split_delta_channels.
  Definition outch_split_new_l1 := new_l1 outch_split_delta_channels outch_split_theta_channels.

  Definition outch_split_new_L4 := new_L4 L1 gamma_no_L1 outch_split_delta_channels outch_split_theta_channels.
  Definition outch_split_gamma_no_new_L3_no_new_L4 := gamma_no_new_L3_no_new_L4 L1 gamma_no_L1 outch_split_delta_channels outch_split_theta_channels.
  Definition outch_split_delta_no_new_L1_no_new_L4 := delta_no_new_L1_no_new_L4 L1 delta_no_L1 outch_split_gamma_channels outch_split_theta_channels.
  Definition outch_split_new_l4 := new_l4 outch_split_gamma_channels outch_split_delta_channels outch_split_theta_channels.

  Lemma outch_split_q_perm :
  cp q ((x, STyp_Ques (dual t)) :: outch_split_new_L3 ++ (w, a) :: outch_split_gamma_no_new_L3).
  Proof.
    pose proof Hcp7 as Hcp12.
    rewrite perm_swap in Hcp12.
    rewrite (l3_gamma_split _ _ _ _ _ _ Hcp6 outch_split_Hcp7' outch_split_Hcp9' outch_split_Hcp10' outch_split_Hcp11' _ outch_split_gamma_channels_def _ outch_split_theta_channels_def) in Hcp12.
    rewrite Permutation_middle in Hcp12.
    apply Hcp12.
  Qed.

  Lemma outch_split_r_perm :
  cp r ((x, STyp_Ques (dual t)) :: outch_split_new_L1 ++ (z, b) :: outch_split_delta_no_new_L1).
  Proof.
    pose proof Hcp8 as Hcp12.
    rewrite perm_swap in Hcp12.
    rewrite (delta_split L1 delta_no_L1 outch_split_theta_channels) in Hcp12.
    rewrite Permutation_middle in Hcp12.
    apply Hcp12.
  Qed.

  Lemma outch_split_comp_p_q :
  cp (Proc_CompAndSplit x (STyp_Excl t) outch_split_new_l3 (Proc_Server x y p) q) (outch_split_new_L3 ++ outch_split_theta_no_new_L3 ++ (w, a) :: outch_split_gamma_no_new_L3).
  Proof.
    pose proof (new_l3_def _ _ outch_split_gamma_channels _ outch_split_theta_channels_def) as Hperm.
    rewrite Hperm; fold outch_split_new_L3.

    pose proof Hcp9 as Hcp12.
    rewrite (l3_theta_split L2 theta_no_L2 outch_split_gamma_channels) in Hcp12.
    pose proof outch_split_q_perm as Hcp13.
    constructor; auto.

    - apply (new_L3_ques _ _ _ _ _ _ Hcp4 Hcp6 outch_split_Hcp9' outch_split_Hcp11' _ outch_split_gamma_channels_def).

    - intros v Hv1 Hv2.
      cbn in Hv2.
      destruct Hv2 as [Hv2 | Hv2].
      + subst v.
        rewrite <- (proc_channels_perm _ _ Hcp12) in Hx2.
        cbn in Hx2.
        rewrite map_app, in_app_iff in Hx2.
        tauto.
      + pose proof (gamma_no_new_L3_theta_no_new_L3_disjoint L1 L2 gamma_no_L1 theta_no_L2 outch_split_gamma_channels _ outch_split_theta_channels_def v).
        tauto.
  Qed.

  Lemma outch_split_comp_p_r :
  cp (Proc_CompAndSplit x (STyp_Excl t) outch_split_new_l1 (Proc_Server x y p) r) (outch_split_new_L1 ++ outch_split_theta_no_new_L1 ++ (z, b) :: outch_split_delta_no_new_L1).
  Proof.
    pose proof (new_l1_def _ _ _ outch_split_delta_channels_def outch_split_theta_channels) as Hperm.
    rewrite Hperm; fold outch_split_new_L1.

    pose proof Hcp9 as Hcp12.
    rewrite (theta_split _ _ _ _ _ _ Hcp6 outch_split_Hcp8' outch_split_Hcp9' outch_split_Hcp10' outch_split_Hcp11' _ outch_split_delta_channels_def _ outch_split_theta_channels_def) in Hcp12.
    pose proof outch_split_r_perm as Hcp13.
    constructor; auto.

    - apply (new_L1_ques _ _ _ _ _ _ Hcp4 Hcp6 outch_split_Hcp9' outch_split_Hcp11' _ outch_split_theta_channels_def).

    - intros v Hv1 Hv2.
      cbn in Hv2.
      destruct Hv2 as [Hv2 | Hv2].
      + subst v.
        rewrite <- (proc_channels_perm _ _ Hcp12) in Hcp1.
        cbn in Hcp1.
        rewrite map_app, in_app_iff in Hcp1.
        tauto.
      + pose proof (delta_no_new_L1_theta_no_new_L1_disjoint L1 L2 delta_no_L1 theta_no_L2 outch_split_delta_channels _ outch_split_theta_channels_def v).
        tauto.
  Qed.

  Lemma outch_split_p_q_perm :
  cp (Proc_CompAndSplit x (STyp_Excl t) outch_split_new_l3 (Proc_Server x y p) q) ((w, a) :: L2 ++ theta_no_L2 ++ outch_split_new_L4 ++ outch_split_gamma_no_new_L3_no_new_L4).
  Proof.
    pose proof outch_split_comp_p_q as Hcp12.
    rewrite app_assoc in Hcp12.
    rewrite <- (l3_theta_split L2 theta_no_L2 outch_split_gamma_channels) in Hcp12.
    rewrite <- Permutation_middle in Hcp12.
    rewrite <- app_assoc in Hcp12.
    rewrite (l4_gamma_split L1 gamma_no_L1 outch_split_delta_channels outch_split_theta_channels) in Hcp12.
    apply Hcp12.
  Qed.

  Lemma outch_split_p_r_perm :
  cp (Proc_CompAndSplit x (STyp_Excl t) outch_split_new_l1 (Proc_Server x y p) r) ((z, b) :: L2 ++ theta_no_L2 ++ outch_split_new_L4 ++ outch_split_delta_no_new_L1_no_new_L4).
  Proof.
    pose proof outch_split_comp_p_r as Hcp12.
    rewrite app_assoc in Hcp12.
    rewrite <- (theta_split _ _ _ _ _ _ Hcp6 outch_split_Hcp8' outch_split_Hcp9' outch_split_Hcp10' outch_split_Hcp11' _ outch_split_delta_channels_def _ outch_split_theta_channels_def) in Hcp12.
    rewrite <- Permutation_middle in Hcp12.
    rewrite <- app_assoc in Hcp12.
    rewrite (l4_delta_split _ _ _ _ _ _ Hcp6 outch_split_Hcp7' outch_split_Hcp8' outch_split_Hcp9' outch_split_Hcp10' outch_split_Hcp11' _ outch_split_gamma_channels_def _ outch_split_delta_channels_def _ outch_split_theta_channels_def) in Hcp12.
    apply Hcp12.
  Qed.

  Lemma outch_split_comp_p_q_r :
  cp (Proc_OutChAndSplit z w (outch_split_theta_channels ++ outch_split_new_l4) (Proc_CompAndSplit x (STyp_Excl t) outch_split_new_l3 (Proc_Server x y p) q) (Proc_CompAndSplit x (STyp_Excl t) outch_split_new_l1 (Proc_Server x y p) r)) ((z, STyp_Times a b) :: L2 ++ theta_no_L2 ++ outch_split_new_L4 ++ outch_split_gamma_no_new_L3_no_new_L4 ++ outch_split_delta_no_new_L1_no_new_L4).
  Proof.
    pose proof (new_l4_def _ _ _ outch_split_gamma_channels_def outch_split_delta_channels outch_split_theta_channels) as Hperm.
    rewrite Hperm; fold outch_split_new_L4.
    do 2 rewrite app_assoc.
    rewrite <- (app_assoc _ _ outch_split_new_L4).
    rewrite outch_split_theta_channels_def.
    rewrite <- map_app, <- app_assoc.

    pose proof outch_split_p_q_perm as Hcp12.
    pose proof outch_split_p_r_perm as Hcp13.
    do 2 rewrite app_assoc in Hcp12, Hcp13.
    rewrite <- (app_assoc L2) in Hcp12, Hcp13.
    constructor; auto.

    - do 2 rewrite map_app, Forall_app.
      repeat split; auto.
      apply (new_L4_ques _ _ _ _ _ _ Hcp3 Hcp6 outch_split_Hcp7' outch_split_Hcp8' outch_split_Hcp9' outch_split_Hcp10' outch_split_Hcp11' _ outch_split_gamma_channels_def _ outch_split_delta_channels_def _ outch_split_theta_channels_def).

    - intros Hin1.
      assert (Hin2 : In z (map fst (outch_split_new_L4 ++ outch_split_gamma_no_new_L3_no_new_L4))) by (rewrite map_app, in_app_iff; auto).
      rewrite <- (l4_gamma_split L1 gamma_no_L1 outch_split_delta_channels outch_split_theta_channels) in Hin2.
      assert (Hin3 : In z (map fst (outch_split_new_L3 ++ outch_split_gamma_no_new_L3))) by (rewrite map_app, in_app_iff; auto).
      rewrite <- (l3_gamma_split _ _ _ _ _ _ Hcp6 outch_split_Hcp7' outch_split_Hcp9' outch_split_Hcp10' outch_split_Hcp11' _ outch_split_gamma_channels_def _ outch_split_theta_channels_def) in Hin3.
      tauto.

    - intros v Hv1 Hv2.
      pose proof (gamma_no_new_L3_no_new_L4_delta_no_new_L1_no_new_L4_disjoint L1 gamma_no_L1 delta_no_L1 outch_split_gamma_channels _ outch_split_delta_channels_def outch_split_theta_channels v).
      tauto.
  Qed.

  Lemma outch_split_p_q_r_perm :
  cp (Proc_OutChAndSplit z w (outch_split_theta_channels ++ outch_split_new_l4) (Proc_CompAndSplit x (STyp_Excl t) outch_split_new_l3 (Proc_Server x y p) q) (Proc_CompAndSplit x (STyp_Excl t) outch_split_new_l1 (Proc_Server x y p) r)) senv.
  Proof.
    eapply cp_perm.
    1: apply outch_split_comp_p_q_r.
    rewrite <- Hcp5.
    apply perm_skip.
    do 2 apply Permutation_app_head.
    symmetry; apply (new_L4_split _ _ _ _ _ _ Hcp6 outch_split_Hcp7' outch_split_Hcp8' outch_split_Hcp9' outch_split_Hcp10' outch_split_Hcp11' _ outch_split_gamma_channels_def _ outch_split_delta_channels_def _ outch_split_theta_channels_def).
  Qed.

  End Proc_Server_Split_Outch.

  Lemma proc_cut_server_split_outch :
  forall x t l1 l2 y p z w q r senv,
  cp (Proc_CompAndSplit x t l2 (Proc_Server x y p) (Proc_OutChAndSplit z w l1 q r)) senv ->
  In x l1 ->
  ~ In w (proc_channels (Proc_Server x y p)) ->
  cp (Proc_OutChAndSplit z w (outch_split_theta_channels x y p ++ outch_split_new_l4 x y z w p q r) (Proc_CompAndSplit x t (outch_split_new_l3 x y w p q) (Proc_Server x y p) q) (Proc_CompAndSplit x t (outch_split_new_l1 x y z p r) (Proc_Server x y p) r)) senv.
  Proof.
    intros x t l1 l2 y p z w q r senv Hcp Hx1 Hx2.
    pose proof (server_split_outch_inv x y z w t l1 l2 p q r senv Hcp Hx1) as (a & b & L1 & L1' & L2 & t' & gamma_no_L1 & delta_no_L1 & gamma_delta_no_L2 & theta_no_L2 & _ & _ & Ht & Hcp0 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & _ & Hcp5 & Hcp6 & Hcp7 & Hcp8 & Hcp9 & Hcp10).
    subst t.
    apply (outch_split_p_q_r_perm x y z w (STyp_Excl t') l1 l2 p q r senv Hcp L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 a b t' Hcp1 Hcp0 Hcp4 Hcp2 Hcp3 Hcp5 Hcp6 Hcp8 Hcp9 Hcp7 Hcp10 Hx2).
  Qed.

  Lemma proc_cut_forall_exists :
  forall x t l a v b p v' q senv,
  cp (Proc_CompAndSplit x t l (Proc_OutTyp x a v b p) (Proc_InTyp x v' q)) senv ->
  t = STyp_Exists v b /\
  v' = v /\
  (Forall (fun v'' => proc_var_subst_pre q v' v'') (fvar a) ->
   cp (Proc_CompAndSplit x (styp_subst v b a) l p (proc_var_subst q v' a)) senv).
  Proof.
    intros x t l a v b p v' q senv Hcp.
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
    destruct (cp_inv_intyp _ _ _ _ Hcp'5) as (a' & delta' & Hcp'''1 & Hcp'''2 & Hcp'''3).
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
      1: unfold styp_forbidden in Hcp''1; rewrite <- styp_forbidden_dual in Hcp''1; auto.
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
         specialize (Hcp'''1 s ltac:(apply (in_map snd) in Hz; auto)).
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

  Lemma proc_cut_forall_exists_rename :
  forall x t l a v b p w w' q senv,
  cp (Proc_CompAndSplit x t l (Proc_OutTyp x a v b p) (Proc_InTypRename x w w' q)) senv ->
  t = STyp_Exists v b /\
  w' = v /\
  cp (Proc_CompAndSplit x (STyp_Exists w (styp_subst w' b (STyp_Var w))) l (Proc_OutTyp x a w (styp_subst w' b (STyp_Var w)) p) q) senv.
  Proof.
    intros x t l a v b p w w' q senv Hcp.
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
    destruct (cp_inv_intyp_rename _ _ _ _ _ Hcp'5) as (a' & delta' & Hcp'''1 & Hcp'''2 & Hcp'''3 & Hcp'''4).
    pose proof Hcp'5 as Hcp'''5.
    apply cp_senv_valid in Hcp'''5.
    rewrite senv_valid_cons in Hcp'''5.
    cbn in Hcp'''4.
    assert (Hcp'''6 : In (x, STyp_Forall w' (styp_subst w a' (STyp_Var w'))) ((x, STyp_Forall v (dual b)) :: gamma ++ delta2)) by (rewrite <- Hcp'''4; left; auto).
    cbn in Hcp'''6.
    destruct Hcp'''6 as [Hcp'''6 | Hcp'''6].
    2: apply (in_map fst) in Hcp'''6; cbn in Hcp'''6; tauto.
    injection Hcp'''6; intros; subst v.
    assert (H0 : dual (dual b) = dual (styp_subst w a' (STyp_Var w'))) by (f_equal; auto).
    rewrite dual_involute in H0; subst b.
    clear H.
    rewrite dual_involute in Hcp'''4.
    apply Permutation_cons_inv in Hcp'''4.
    cbn in Hcp'''5.
    clear Hcp'''6.

    (* Simplify some propositions *)
    cbn in Hcp'5, Hcp'4, Hcp''4.
    rewrite dual_involute in Hcp'5.
    rewrite styp_subst_dual in Hcp'4, Hcp''1, Hcp''2.
    rewrite styp_subst_dual.

    repeat split; auto.

    assert (Hcp'''1_alt : ~ In w' (styp_forbidden (dual a') w)).
    { unfold styp_forbidden; rewrite styp_forbidden_dual; auto. }
    assert (Hcp'''2_alt : ~ In w' (fvar (dual a'))).
    { unfold fvar; rewrite var_free_dual; auto. }

    assert (Hp : styp_subst w' (styp_subst w (dual a') (STyp_Var w')) a = styp_subst w (dual a') a).
    { symmetry; apply subst_after_rename; auto. }
    rewrite Hp in Hcp''2.
    assert (Hex : styp_subst w' (styp_subst w (dual a') (STyp_Var w')) (STyp_Var w) = dual a').
    { rewrite <- subst_after_rename; auto.
      rewrite var_rename_ident; auto.
    }
    rewrite Hex.

    rewrite <- Hcp'6.
    constructor; auto.
    2: cbn; rewrite dual_involute; rewrite Hcp'''4 in Hcp'''3; auto.
    constructor.
    2: rewrite Hcp''3 in Hcp''2; auto.

    rewrite Forall_forall; rewrite Forall_forall in Hcp''1.
    intros z Hz; specialize (Hcp''1 _ Hz).
    destruct (pvn_eqb_spec w' w).
    1: subst w'; rewrite var_rename_ident in Hcp''1; auto.
    rewrite <- Hex.
    apply styp_subst_forbidden; auto.
    2: cbn; rewrite pvn_eqb_refl; auto.
    unfold styp_forbidden; rewrite styp_forbidden_empty; auto.
    intros Hin; apply var_free_subst in Hin; cbn in Hin; tauto.
  Qed.

  Lemma proc_cut_outunit_inunit :
  forall x t l p senv,
  cp (Proc_CompAndSplit x t l (Proc_OutUnit x) (Proc_InUnit x p)) senv ->
  l = [] /\
  cp p senv.
  Proof.
    intros x t l p senv Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    subst l.

    (* Invert Hcp'4 *)
    pose proof (cp_inv_outunit _ _ Hcp'4) as Hcp''.
    injection Hcp''; intros; subst t.
    destruct gamma; try discriminate.
    split; auto.
    destruct delta1; try discriminate; clear H Hcp''.
    cbn in Hcp'6.

    (* Invert Hcp'5 *)
    destruct (cp_inv_inunit _ _ _ Hcp'5) as (delta' & Hcp'''1 & Hcp'''2).
    pose proof Hcp'5 as Hcp'''3.
    apply cp_senv_valid in Hcp'''3.
    rewrite senv_valid_cons in Hcp'''3.
    cbn in Hcp'''2, Hcp'''3.
    apply Permutation_cons_inv in Hcp'''2.

    rewrite <- Hcp'6; rewrite <- Hcp'''2; auto.
  Qed.

  (* The two commuting conversions
     Cut (z, x[y].(P | Q), R) ==> x[y].(Cut (z, (P | R), Q), and
     Cut (z, x[y].(P | Q), R) ==> x[y].(Cut (z, P, (Q | R)).
     Ideally, we should prove only one of them,
     and convert the other case to the proven case.
     However, this is not possible because x[y].(P | Q) cannot always be converted to y[x].(Q | P), because y could be a channel in Q, and y[x].(Q | P) has a name clash.
   *)

  Section Proc_OutCh_Comm_1.

  Variable (x y z : chn).
  Variable (t : STyp).
  Variable (l1 l2 : list chn).
  Variable (p q r : Process).
  Variable (senv : SEnv).
  Hypothesis (Hcp : cp (Proc_CompAndSplit x t l2 (Proc_OutChAndSplit y z l1 p q) r) senv).
  Hypothesis (Hx1 : In x (proc_channels p)).
  Hypothesis (Hx2 : x <> z).
  Hypothesis (Hx3 : ~ In x l1).

  Lemma outch_comm_1_inv :
  exists a b L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2,
  l1 = map fst L1 /\
  l2 = map fst L2 /\
  ~ (In y (proc_channels p) /\ z <> y) /\
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1) /\
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2) /\
  Permutation ((y, STyp_Times a b) :: L2 ++ gamma_delta_no_L2 ++ theta_no_L2) senv /\
  Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2) /\
  cp q ((y, b) :: L1 ++ gamma_no_L1) /\
  cp p ((z, a) :: (x, t) :: L1 ++ delta_no_L1) /\
  cp r ((x, dual t) :: L2 ++ theta_no_L2) /\
  cp (Proc_OutChAndSplit y z l1 p q) ((x, t) :: (y, STyp_Times a b) :: L2 ++ gamma_delta_no_L2).
  Proof.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (L2 & gamma_delta_y_no_L2 & theta_no_L2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6).
    destruct (cp_inv_outch_and_split _ _ _ _ _ _ Hcp4) as (a & b & L1 & delta_x_no_L1 & gamma_no_L1 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6 & Hcp'7).
    subst l1 l2.

    (* x is in delta_x_no_L1 *)
    rewrite <- (proc_channels_perm _ _ Hcp'5) in Hx1.
    cbn in Hx1.
    rewrite map_app, in_app_iff in Hx1.
    destruct Hx1 as [Hx1' | [Hx1' | Hx1']]; [subst x; tauto | tauto | ].
    apply cp_senv_valid in Hcp4 as Hx4.
    rewrite <- Hcp'7 in Hx4.
    do 2 rewrite Permutation_middle in Hx4.
    rewrite Permutation_app_swap_app in Hx4.
    assert (Hdisjoint : senv_disjoint delta_x_no_L1 (L1 ++ (y, STyp_Times a b) :: gamma_no_L1)) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint _ Hx1').
    assert (Hx4' : ~ In (x, t) (L1 ++ (y, STyp_Times a b) :: gamma_no_L1)) by (intros Hin; apply (in_map fst) in Hin; tauto).
    rewrite in_app_iff in Hx4'; cbn in Hx4'.
    assert (Hx5 : In (x, t) ((y, STyp_Times a b) :: L1 ++ delta_x_no_L1 ++ gamma_no_L1)) by (rewrite Hcp'7; left; auto).
    cbn in Hx5; do 2 rewrite in_app_iff in Hx5.
    assert (Hx6 : In (x, t) delta_x_no_L1) by tauto.

    pose proof (in_split_perm _ _ Hx6) as (delta_no_L1 & HL1).
    rewrite HL1 in Hcp'7.
    cbn in Hcp'7.
    rewrite <- Permutation_middle in Hcp'7.
    rewrite perm_swap in Hcp'7.
    apply Permutation_cons_inv in Hcp'7.

    (* y is in gamma_delta_y_no_L2 *)
    assert (Hy1 : In (y, STyp_Times a b) (L2 ++ gamma_delta_y_no_L2)) by (rewrite <- Hcp'7; left; auto).
    rewrite in_app_iff in Hy1.
    destruct Hy1 as [Hy1 | Hy1].
    1: rewrite Forall_forall in Hcp1; specialize (Hcp1 (STyp_Times a b) ltac:(apply (in_map snd) in Hy1; auto)); contradiction.
    pose proof (in_split_perm _ _ Hy1) as (gamma_delta_no_L2 & HL2).
    rewrite HL2 in Hcp'7.
    rewrite <- Permutation_middle in Hcp'7.
    apply Permutation_cons_inv in Hcp'7.

    exists a; exists b; exists L1; exists L2; exists gamma_no_L1; exists delta_no_L1; exists gamma_delta_no_L2; exists theta_no_L2.
    repeat split; auto.
    - rewrite <- (proc_channels_perm _ _ Hcp'5).
      cbn.
      apply cp_senv_valid in Hcp'6.
      rewrite senv_valid_cons in Hcp'6.
      rewrite map_app, in_app_iff in Hcp'6.
      rewrite map_app, in_app_iff.
      tauto.
    - rewrite HL2 in Hcp6.
      cbn in Hcp6.
      rewrite <- Permutation_middle in Hcp6; auto.
    - rewrite (Permutation_app_comm delta_no_L1) in Hcp'7; auto.
    - rewrite HL1 in Hcp'5.
      rewrite <- Permutation_middle in Hcp'5; auto.
    - rewrite HL2 in Hcp4.
      rewrite <- Permutation_middle in Hcp4; auto.
  Qed.

  Variable (L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 : SEnv).
  Variable (a b : STyp).
  Hypothesis (Hcp3 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1)).
  Hypothesis (Hcp4 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2)).
  Hypothesis (Hcp5 : Permutation ((y, STyp_Times a b) :: L2 ++ gamma_delta_no_L2 ++ theta_no_L2) senv).
  Hypothesis (Hcp6 : Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hcp7 : cp q ((y, b) :: L1 ++ gamma_no_L1)).
  Hypothesis (Hcp8 : cp p ((z, a) :: (x, t) :: L1 ++ delta_no_L1)).
  Hypothesis (Hcp9 : cp r ((x, dual t) :: L2 ++ theta_no_L2)).
  Hypothesis (Hcp10 : cp (Proc_OutChAndSplit y z l1 p q) ((x, t) :: (y, STyp_Times a b) :: L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hx4 : ~ In z (proc_channels r)).

  Lemma outch_comm1_Hcp7' : senv_valid (L1 ++ gamma_no_L1).
  Proof. apply cp_senv_valid in Hcp7; rewrite senv_valid_cons in Hcp7; tauto. Qed.

  Lemma outch_comm1_Hcp8' : senv_valid (L1 ++ delta_no_L1).
  Proof. apply cp_senv_valid in Hcp8; do 2 rewrite senv_valid_cons in Hcp8; tauto. Qed.

  Lemma outch_comm1_Hcp9' : senv_valid (L2 ++ theta_no_L2).
  Proof. apply cp_senv_valid in Hcp9; rewrite senv_valid_cons in Hcp9; tauto. Qed.

  Lemma outch_comm1_Hcp10' : senv_valid (L1 ++ gamma_no_L1 ++ delta_no_L1).
  Proof. rewrite <- Hcp6 in Hcp10; apply cp_senv_valid in Hcp10; do 2 rewrite senv_valid_cons in Hcp10; tauto. Qed.

  Lemma outch_comm1_Hcp11' : senv_valid (L2 ++ gamma_delta_no_L2 ++ theta_no_L2).
  Proof. rewrite <- Hcp5 in Hcp; apply cp_senv_valid in Hcp; rewrite senv_valid_cons in Hcp; tauto. Qed.

  Definition outch_comm1_gamma_channels := filter (fun s => negb (eqb y s)) (proc_channels q).

  Lemma outch_comm1_gamma_channels_def : Permutation outch_comm1_gamma_channels (map fst (L1 ++ gamma_no_L1)).
  Proof.
    unfold outch_comm1_gamma_channels.
    rewrite <- (proc_channels_perm _ _ Hcp7).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp7).
  Qed.

  Definition outch_comm1_delta_channels := filter (fun s => negb (eqb z s) && negb (eqb x s)) (proc_channels p).

  Lemma outch_comm1_delta_channels_def : Permutation outch_comm1_delta_channels (map fst (L1 ++ delta_no_L1)).
  Proof.
    unfold outch_comm1_delta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp8).
    cbn [map fst].
    rewrite NoDup_filter_two; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp8).
  Qed.

  Definition outch_comm1_theta_channels := filter (fun s => negb (eqb x s)) (proc_channels r).

  Lemma outch_comm1_theta_channels_def : Permutation outch_comm1_theta_channels (map fst (L2 ++ theta_no_L2)).
  Proof.
    unfold outch_comm1_theta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp9).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp9).
  Qed.

  Definition outch_comm1_new_L1 := new_L1 L1 delta_no_L1 outch_comm1_theta_channels.
  Definition outch_comm1_delta_no_new_L1 := delta_no_new_L1 L1 delta_no_L1 outch_comm1_theta_channels.
  Definition outch_comm1_theta_no_new_L1 := theta_no_new_L1 L2 theta_no_L2 outch_comm1_delta_channels.
  Definition outch_comm1_new_L2 := new_L2 L1 gamma_no_L1 outch_comm1_delta_channels outch_comm1_theta_channels.
  Definition outch_comm1_gamma_no_new_L2 := gamma_no_new_L2 L1 gamma_no_L1 outch_comm1_delta_channels outch_comm1_theta_channels.
  Definition outch_comm1_delta_theta_no_new_L2 := delta_theta_no_new_L2 L1 L2 delta_no_L1 theta_no_L2 outch_comm1_gamma_channels outch_comm1_delta_channels outch_comm1_theta_channels.
  Definition outch_comm1_new_l1 := new_l1 outch_comm1_delta_channels outch_comm1_theta_channels.
  Definition outch_comm1_new_l2 := new_l2 outch_comm1_gamma_channels outch_comm1_delta_channels outch_comm1_theta_channels.

  (* Cut P and R *)
  Lemma outch_comm1_cut_p_r :
  cp (Proc_CompAndSplit x t outch_comm1_new_l1 p r) (outch_comm1_new_L1 ++ (z, a) :: outch_comm1_delta_no_new_L1 ++ outch_comm1_theta_no_new_L1).
  Proof.
    pose proof (new_l1_def _ _ _ outch_comm1_delta_channels_def outch_comm1_theta_channels) as Hperm.
    rewrite Hperm; fold outch_comm1_new_L1.

    pose proof Hcp8 as Hcp8'.
    rewrite perm_swap in Hcp8'.
    pose proof (delta_split L1 delta_no_L1 outch_comm1_theta_channels) as Hperm1.
    rewrite Hperm1 in Hcp8'.
    rewrite Permutation_middle in Hcp8'.
    pose proof Hcp9 as Hcp9'.
    pose proof (theta_split _ _ _ _ _ _ Hcp6 outch_comm1_Hcp8' outch_comm1_Hcp9' outch_comm1_Hcp10' outch_comm1_Hcp11' _ outch_comm1_delta_channels_def _ outch_comm1_theta_channels_def) as Hperm2.
    rewrite Hperm2 in Hcp9'.

    rewrite app_comm_cons.
    constructor; auto.
    - apply (new_L1_ques _ _ _ _ _ _ Hcp4 Hcp6 outch_comm1_Hcp9' outch_comm1_Hcp11' _ outch_comm1_theta_channels_def).
    - intros w Hw1 Hw2.
      cbn in Hw1.
      destruct Hw1 as [Hw1 | Hw1].
      + subst w.
        rewrite <- (proc_channels_perm _ _ Hcp9) in Hx4.
        cbn in Hx4.
        rewrite Hperm2 in Hx4.
        rewrite map_app, in_app_iff in Hx4.
        tauto.
      + pose proof (delta_no_new_L1_theta_no_new_L1_disjoint L1 _ delta_no_L1 theta_no_L2 outch_comm1_delta_channels _ outch_comm1_theta_channels_def w).
        tauto.
  Qed.

  Lemma outch_comm1_p_r_perm :
  cp (Proc_CompAndSplit x t outch_comm1_new_l1 p r) ((z, a) :: outch_comm1_new_L2 ++ outch_comm1_delta_theta_no_new_L2).
  Proof.
    pose proof outch_comm1_cut_p_r as Hcp'.
    rewrite <- Permutation_middle in Hcp'.
    rewrite (delta_theta_split _ _ _ _ _ _ Hcp6 outch_comm1_Hcp7' outch_comm1_Hcp8' outch_comm1_Hcp9' outch_comm1_Hcp10' outch_comm1_Hcp11' _ outch_comm1_gamma_channels_def _ outch_comm1_delta_channels_def _ outch_comm1_theta_channels_def) in Hcp'.
    auto.
  Qed.

  Lemma outch_comm1_cut_p_r_q :
  cp (Proc_OutChAndSplit y z outch_comm1_new_l2 (Proc_CompAndSplit x t outch_comm1_new_l1 p r) q) ((y, STyp_Times a b) :: outch_comm1_new_L2 ++ outch_comm1_delta_theta_no_new_L2 ++ outch_comm1_gamma_no_new_L2).
  Proof.
    pose proof (new_l2_def _ _ _ outch_comm1_gamma_channels_def outch_comm1_delta_channels outch_comm1_theta_channels) as Hperm.
    rewrite Hperm; fold outch_comm1_new_L2.

    pose proof Hcp7 as Hcp7'.
    pose proof (gamma_split L1 gamma_no_L1 outch_comm1_delta_channels outch_comm1_theta_channels) as Hperm1.
    rewrite Hperm1 in Hcp7'.
    pose proof outch_comm1_p_r_perm as Hcp'2.
    constructor; auto.
    - apply (new_L2_ques _ _ _ _ _ _ Hcp3 Hcp4 Hcp6 outch_comm1_Hcp7' outch_comm1_Hcp8' outch_comm1_Hcp9' outch_comm1_Hcp10' outch_comm1_Hcp11' _ outch_comm1_delta_channels_def _ outch_comm1_theta_channels_def).

    - intros Hin.
      assert (Hin' : In y (map fst (outch_comm1_new_L2 ++ outch_comm1_delta_theta_no_new_L2))) by (rewrite map_app, in_app_iff; auto).
      rewrite <- (delta_theta_split _ _ _ _ _ _ Hcp6 outch_comm1_Hcp7' outch_comm1_Hcp8' outch_comm1_Hcp9' outch_comm1_Hcp10' outch_comm1_Hcp11' _ outch_comm1_gamma_channels_def _ outch_comm1_delta_channels_def _ outch_comm1_theta_channels_def) in Hin'.
      do 2 rewrite map_app in Hin'.
      rewrite <- in_app_app_iff in Hin'.
      do 2 rewrite <- map_app in Hin'.
      rewrite <- (theta_split _ _ _ _ _ _ Hcp6 outch_comm1_Hcp8' outch_comm1_Hcp9' outch_comm1_Hcp10' outch_comm1_Hcp11' _ outch_comm1_delta_channels_def _ outch_comm1_theta_channels_def) in Hin'.
      rewrite <- (delta_split L1 delta_no_L1 outch_comm1_theta_channels) in Hin'.
      rewrite <- Hcp5 in Hcp.
      apply cp_senv_valid in Hcp.
      rewrite senv_valid_cons in Hcp.
      destruct Hcp as (Hcp' & _).
      rewrite (Permutation_app_comm gamma_delta_no_L2) in Hcp'.
      do 2 rewrite map_app in Hcp'.
      rewrite <- in_app_app_iff in Hcp'.
      do 2 rewrite <- map_app in Hcp'.
      rewrite in_app_iff in Hcp'.
      rewrite in_app_iff in Hin'.
      destruct Hin' as [Hin' | Hin'].
      2: tauto.
      apply Hcp'; right.
      rewrite <- Hcp6.
      do 2 rewrite map_app.
      rewrite <- in_app_app_iff.
      do 2 rewrite <- map_app.
      rewrite in_app_iff; auto.

    - intros w.
      pose proof (gamma_no_new_L2_delta_theta_no_new_L2_disjoint _ _ _ _ _ _ Hcp6 outch_comm1_Hcp8' outch_comm1_Hcp9' outch_comm1_Hcp10' outch_comm1_Hcp11' outch_comm1_gamma_channels _ outch_comm1_delta_channels_def _ outch_comm1_theta_channels_def w).
      tauto.
  Qed.

  Lemma outch_comm1_p_r_q_perm :
  cp (Proc_OutChAndSplit y z outch_comm1_new_l2 (Proc_CompAndSplit x t outch_comm1_new_l1 p r) q) senv.
  Proof.
    pose proof outch_comm1_cut_p_r_q as Hcp'.
    eapply cp_perm.
    1: apply Hcp'.
    rewrite <- Hcp5.
    apply Permutation_cons; auto.
    symmetry.
    rewrite (Permutation_app_comm outch_comm1_delta_theta_no_new_L2).
    apply (new_L2_split _ _ _ _ _ _ Hcp6 outch_comm1_Hcp7' outch_comm1_Hcp8' outch_comm1_Hcp9' outch_comm1_Hcp10' outch_comm1_Hcp11' _ outch_comm1_gamma_channels_def _ outch_comm1_delta_channels_def _ outch_comm1_theta_channels_def).
  Qed.

  End Proc_OutCh_Comm_1.

  Lemma proc_outch_comm1 :
  forall x y z t l1 l2 p q r senv,
  In x (proc_channels p) ->
  x <> z ->
  ~ In x l1 ->
  ~ In z (proc_channels r) ->
  cp (Proc_CompAndSplit x t l2 (Proc_OutChAndSplit y z l1 p q) r) senv ->
  cp (Proc_OutChAndSplit y z (outch_comm1_new_l2 x y z p q r) (Proc_CompAndSplit x t (outch_comm1_new_l1 x z p r) p r) q) senv.
  Proof.
    intros x y z t l1 l2 p q r senv Hx1 Hx2 Hx3 Hx4 Hcp.
    pose proof (outch_comm_1_inv x y z t l1 l2 p q r senv Hcp Hx1 Hx2 Hx3) as (a & b & L1 & L2 & gamma_no_L1 & delta_no_L1 & gamma_delta_no_L2 & theta_no_L2 & _ & _ & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6 & Hcp7 & Hcp8 & Hcp9 & Hcp10).
    apply (outch_comm1_p_r_q_perm x y z t l1 l2 p q r senv Hcp L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 a b Hcp3 Hcp4 Hcp5 Hcp6 Hcp7 Hcp8 Hcp9 Hcp10 Hx4).
  Qed.

  Section Proc_OutCh_Comm_2.

  Variable (x y z : chn).
  Variable (t : STyp).
  Variable (l1 l2 : list chn).
  Variable (p q r : Process).
  Variable (senv : SEnv).
  Hypothesis (Hcp : cp (Proc_CompAndSplit x t l2 (Proc_OutChAndSplit y z l1 p q) r) senv).
  Hypothesis (Hx1 : In x (proc_channels q)).
  Hypothesis (Hx2 : x <> y).
  Hypothesis (Hx3 : ~ In x l1).

  Lemma outch_comm_2_inv :
  exists a b L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2,
  l1 = map fst L1 /\
  l2 = map fst L2 /\
  ~ (In y (proc_channels p) /\ z <> y) /\
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1) /\
  Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2) /\
  Permutation ((y, STyp_Times a b) :: L2 ++ gamma_delta_no_L2 ++ theta_no_L2) senv /\
  Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2) /\
  cp p ((z, a) :: L1 ++ gamma_no_L1) /\
  cp q ((y, b) :: (x, t) :: L1 ++ delta_no_L1) /\
  cp r ((x, dual t) :: L2 ++ theta_no_L2) /\
  cp (Proc_OutChAndSplit y z l1 p q) ((x, t) :: (y, STyp_Times a b) :: L2 ++ gamma_delta_no_L2).
  Proof.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (L2 & gamma_delta_y_no_L2 & theta_no_L2 & Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6).
    destruct (cp_inv_outch_and_split _ _ _ _ _ _ Hcp4) as (a & b & L1 & gamma_no_L1 & delta_x_no_L1 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6 & Hcp'7).
    subst l1 l2.

    (* x is in delta_x_no_L1 *)
    rewrite <- (proc_channels_perm _ _ Hcp'6) in Hx1.
    cbn in Hx1.
    rewrite map_app, in_app_iff in Hx1.
    destruct Hx1 as [Hx1' | [Hx1' | Hx1']]; [subst x; tauto | tauto | ].
    apply cp_senv_valid in Hcp4 as Hx4.
    rewrite <- Hcp'7 in Hx4.
    do 2 rewrite Permutation_middle in Hx4.
    rewrite app_assoc in Hx4.
    rewrite Permutation_app_comm in Hx4.
    cbn in Hx4.
    rewrite Permutation_middle in Hx4.
    assert (Hdisjoint : senv_disjoint delta_x_no_L1 ((y, STyp_Times a b) :: L1 ++ gamma_no_L1)) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint _ Hx1').
    assert (Hx4' : ~ In (x, t) ((y, STyp_Times a b) :: L1 ++ gamma_no_L1)) by (intros Hin; apply (in_map fst) in Hin; tauto).
    cbn in Hx4'; rewrite in_app_iff in Hx4'.
    assert (Hx5 : In (x, t) ((y, STyp_Times a b) :: L1 ++ gamma_no_L1 ++ delta_x_no_L1)) by (rewrite Hcp'7; left; auto).
    cbn in Hx5; do 2 rewrite in_app_iff in Hx5.
    assert (Hx6 : In (x, t) delta_x_no_L1) by tauto.

    pose proof (in_split_perm _ _ Hx6) as (delta_no_L1 & HL1).
    rewrite HL1 in Hcp'7.
    cbn in Hcp'7.
    do 2 rewrite <- Permutation_middle in Hcp'7.
    rewrite perm_swap in Hcp'7.
    apply Permutation_cons_inv in Hcp'7.

    (* y is in gamma_delta_y_no_L2 *)
    assert (Hy1 : In (y, STyp_Times a b) (L2 ++ gamma_delta_y_no_L2)) by (rewrite <- Hcp'7; left; auto).
    rewrite in_app_iff in Hy1.
    destruct Hy1 as [Hy1 | Hy1].
    1: rewrite Forall_forall in Hcp1; specialize (Hcp1 (STyp_Times a b) ltac:(apply (in_map snd) in Hy1; auto)); contradiction.
    pose proof (in_split_perm _ _ Hy1) as (gamma_delta_no_L2 & HL2).
    rewrite HL2 in Hcp'7.
    rewrite <- Permutation_middle in Hcp'7.
    apply Permutation_cons_inv in Hcp'7.

    exists a; exists b; exists L1; exists L2; exists gamma_no_L1; exists delta_no_L1; exists gamma_delta_no_L2; exists theta_no_L2.
    repeat split; auto.
    - rewrite <- (proc_channels_perm _ _ Hcp'5).
      cbn.
      apply cp_senv_valid in Hcp'6.
      rewrite senv_valid_cons in Hcp'6.
      rewrite map_app, in_app_iff in Hcp'6.
      rewrite map_app, in_app_iff.
      tauto.
    - rewrite HL2 in Hcp6.
      cbn in Hcp6.
      rewrite <- Permutation_middle in Hcp6; auto.
    - rewrite HL1 in Hcp'6.
      rewrite <- Permutation_middle in Hcp'6; auto.
    - rewrite HL2 in Hcp4.
      rewrite <- Permutation_middle in Hcp4; auto.
  Qed.

  Variable (L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 : SEnv).
  Variable (a b : STyp).
  Hypothesis (Hcp2 : ~ (In y (proc_channels p) /\ z <> y)).
  Hypothesis (Hcp3 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L1)).
  Hypothesis (Hcp4 : Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd L2)).
  Hypothesis (Hcp5 : Permutation ((y, STyp_Times a b) :: L2 ++ gamma_delta_no_L2 ++ theta_no_L2) senv).
  Hypothesis (Hcp6 : Permutation (L1 ++ gamma_no_L1 ++ delta_no_L1) (L2 ++ gamma_delta_no_L2)).
  Hypothesis (Hcp7 : cp p ((z, a) :: L1 ++ gamma_no_L1)).
  Hypothesis (Hcp8 : cp q ((y, b) :: (x, t) :: L1 ++ delta_no_L1)).
  Hypothesis (Hcp9 : cp r ((x, dual t) :: L2 ++ theta_no_L2)).
  Hypothesis (Hcp10 : cp (Proc_OutChAndSplit y z l1 p q) ((x, t) :: (y, STyp_Times a b) :: L2 ++ gamma_delta_no_L2)).

  Lemma outch_comm2_Hcp7' : senv_valid (L1 ++ gamma_no_L1).
  Proof. apply cp_senv_valid in Hcp7; rewrite senv_valid_cons in Hcp7; tauto. Qed.

  Lemma outch_comm2_Hcp8' : senv_valid (L1 ++ delta_no_L1).
  Proof. apply cp_senv_valid in Hcp8; do 2 rewrite senv_valid_cons in Hcp8; tauto. Qed.

  Lemma outch_comm2_Hcp9' : senv_valid (L2 ++ theta_no_L2).
  Proof. apply cp_senv_valid in Hcp9; rewrite senv_valid_cons in Hcp9; tauto. Qed.

  Lemma outch_comm2_Hcp10' : senv_valid (L1 ++ gamma_no_L1 ++ delta_no_L1).
  Proof. rewrite <- Hcp6 in Hcp10; apply cp_senv_valid in Hcp10; do 2 rewrite senv_valid_cons in Hcp10; tauto. Qed.

  Lemma outch_comm2_Hcp11' : senv_valid (L2 ++ gamma_delta_no_L2 ++ theta_no_L2).
  Proof. rewrite <- Hcp5 in Hcp; apply cp_senv_valid in Hcp; rewrite senv_valid_cons in Hcp; tauto. Qed.

  Definition outch_comm2_gamma_channels := filter (fun s => negb (eqb z s)) (proc_channels p).

  Lemma outch_comm2_gamma_channels_def : Permutation outch_comm2_gamma_channels (map fst (L1 ++ gamma_no_L1)).
  Proof.
    unfold outch_comm2_gamma_channels.
    rewrite <- (proc_channels_perm _ _ Hcp7).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp7).
  Qed.

  Definition outch_comm2_delta_channels := filter (fun s => negb (eqb y s) && negb (eqb x s)) (proc_channels q).

  Lemma outch_comm2_delta_channels_def : Permutation outch_comm2_delta_channels (map fst (L1 ++ delta_no_L1)).
  Proof.
    unfold outch_comm2_delta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp8).
    cbn [map fst].
    rewrite NoDup_filter_two; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp8).
  Qed.

  Definition outch_comm2_theta_channels := filter (fun s => negb (eqb x s)) (proc_channels r).

  Lemma outch_comm2_theta_channels_def : Permutation outch_comm2_theta_channels (map fst (L2 ++ theta_no_L2)).
  Proof.
    unfold outch_comm2_theta_channels.
    rewrite <- (proc_channels_perm _ _ Hcp9).
    cbn [map fst].
    rewrite NoDup_filter_one; auto.
    1: apply eqb_spec.
    apply (cp_senv_valid _ _ Hcp9).
  Qed.

  Definition outch_comm2_new_L1 := new_L1 L1 delta_no_L1 outch_comm2_theta_channels.
  Definition outch_comm2_delta_no_new_L1 := delta_no_new_L1 L1 delta_no_L1 outch_comm2_theta_channels.
  Definition outch_comm2_theta_no_new_L1 := theta_no_new_L1 L2 theta_no_L2 outch_comm2_delta_channels.
  Definition outch_comm2_new_L2 := new_L2 L1 gamma_no_L1 outch_comm2_delta_channels outch_comm2_theta_channels.
  Definition outch_comm2_gamma_no_new_L2 := gamma_no_new_L2 L1 gamma_no_L1 outch_comm2_delta_channels outch_comm2_theta_channels.
  Definition outch_comm2_delta_theta_no_new_L2 := delta_theta_no_new_L2 L1 L2 delta_no_L1 theta_no_L2 outch_comm2_gamma_channels outch_comm2_delta_channels outch_comm2_theta_channels.
  Definition outch_comm2_new_l1 := new_l1 outch_comm2_delta_channels outch_comm2_theta_channels.
  Definition outch_comm2_new_l2 := new_l2 outch_comm2_gamma_channels outch_comm2_delta_channels outch_comm2_theta_channels.

  (* Cut P and R *)
  Lemma outch_comm2_cut_q_r :
  cp (Proc_CompAndSplit x t outch_comm2_new_l1 q r) (outch_comm2_new_L1 ++ (y, b) :: outch_comm2_delta_no_new_L1 ++ outch_comm2_theta_no_new_L1).
  Proof.
    pose proof (new_l1_def _ _ _ outch_comm2_delta_channels_def outch_comm2_theta_channels) as Hperm.
    rewrite Hperm; fold outch_comm2_new_L1.

    pose proof Hcp8 as Hcp8'.
    rewrite perm_swap in Hcp8'.
    pose proof (delta_split L1 delta_no_L1 outch_comm2_theta_channels) as Hperm1.
    rewrite Hperm1 in Hcp8'.
    rewrite Permutation_middle in Hcp8'.
    pose proof Hcp9 as Hcp9'.
    pose proof (theta_split _ _ _ _ _ _ Hcp6 outch_comm2_Hcp8' outch_comm2_Hcp9' outch_comm2_Hcp10' outch_comm2_Hcp11' _ outch_comm2_delta_channels_def _ outch_comm2_theta_channels_def) as Hperm2.
    rewrite Hperm2 in Hcp9'.

    rewrite app_comm_cons.
    constructor; auto.
    - apply (new_L1_ques _ _ _ _ _ _ Hcp4 Hcp6 outch_comm2_Hcp9' outch_comm2_Hcp11' _ outch_comm2_theta_channels_def).
    - intros w Hw1 Hw2.
      cbn in Hw1.
      destruct Hw1 as [Hw1 | Hw1].
      + subst w.
        assert (Hw2' : In y (map fst (outch_comm2_new_L1 ++ outch_comm2_theta_no_new_L1))) by (rewrite map_app, in_app_iff; auto).
        rewrite <- (theta_split _ _ _ _ _ _ Hcp6 outch_comm2_Hcp8' outch_comm2_Hcp9' outch_comm2_Hcp10' outch_comm2_Hcp11' _ outch_comm2_delta_channels_def _ outch_comm2_theta_channels_def) in Hw2'.
        rewrite <- Hcp5 in Hcp.
        apply cp_senv_valid in Hcp as Hcp'.
        rewrite senv_valid_cons in Hcp'.
        rewrite (Permutation_app_comm gamma_delta_no_L2) in Hcp'.
        rewrite app_assoc in Hcp'.
        rewrite map_app, in_app_iff in Hcp'.
        tauto.
      + pose proof (delta_no_new_L1_theta_no_new_L1_disjoint L1 _ delta_no_L1 theta_no_L2 outch_comm2_delta_channels _ outch_comm2_theta_channels_def w).
        tauto.
  Qed.

  Lemma outch_comm2_q_r_perm :
  cp (Proc_CompAndSplit x t outch_comm2_new_l1 q r) ((y, b) :: outch_comm2_new_L2 ++ outch_comm2_delta_theta_no_new_L2).
  Proof.
    pose proof outch_comm2_cut_q_r as Hcp'.
    rewrite <- Permutation_middle in Hcp'.
    rewrite (delta_theta_split _ _ _ _ _ _ Hcp6 outch_comm2_Hcp7' outch_comm2_Hcp8' outch_comm2_Hcp9' outch_comm2_Hcp10' outch_comm2_Hcp11' _ outch_comm2_gamma_channels_def _ outch_comm2_delta_channels_def _ outch_comm2_theta_channels_def) in Hcp'.
    auto.
  Qed.

  Lemma outch_comm2_cut_q_r_p :
  cp (Proc_OutChAndSplit y z outch_comm2_new_l2 p (Proc_CompAndSplit x t outch_comm2_new_l1 q r)) ((y, STyp_Times a b) :: outch_comm2_new_L2 ++ outch_comm2_gamma_no_new_L2 ++ outch_comm2_delta_theta_no_new_L2).
  Proof.
    pose proof (new_l2_def _ _ _ outch_comm2_gamma_channels_def outch_comm2_delta_channels outch_comm2_theta_channels) as Hperm.
    rewrite Hperm; fold outch_comm2_new_L2.

    pose proof Hcp7 as Hcp7'.
    pose proof (gamma_split L1 gamma_no_L1 outch_comm2_delta_channels outch_comm2_theta_channels) as Hperm1.
    rewrite Hperm1 in Hcp7'.
    pose proof outch_comm2_q_r_perm as Hcp'2.
    constructor; auto.
    - apply (new_L2_ques _ _ _ _ _ _ Hcp3 Hcp4 Hcp6 outch_comm2_Hcp7' outch_comm2_Hcp8' outch_comm2_Hcp9' outch_comm2_Hcp10' outch_comm2_Hcp11' _ outch_comm2_delta_channels_def _ outch_comm2_theta_channels_def).

    - intros Hin.
      assert (Hin' : In y (map fst (outch_comm2_new_L2 ++ outch_comm2_gamma_no_new_L2))) by (rewrite map_app, in_app_iff; auto).
      rewrite <- (gamma_split L1 gamma_no_L1 outch_comm2_delta_channels outch_comm2_theta_channels) in Hin'.
      rewrite <- (proc_channels_perm _ _ Hcp7) in Hcp2.
      cbn in Hcp2.
      apply Hcp2; split; auto.
      intros Heq; rewrite Heq in Hcp7.
      apply cp_senv_valid in Hcp7.
      rewrite senv_valid_cons in Hcp7.
      tauto.

    - intros w.
      pose proof (gamma_no_new_L2_delta_theta_no_new_L2_disjoint _ _ _ _ _ _ Hcp6 outch_comm2_Hcp8' outch_comm2_Hcp9' outch_comm2_Hcp10' outch_comm2_Hcp11' outch_comm2_gamma_channels _ outch_comm2_delta_channels_def _ outch_comm2_theta_channels_def w).
      tauto.
  Qed.

  Lemma outch_comm2_q_r_p_perm :
  cp (Proc_OutChAndSplit y z outch_comm2_new_l2 p (Proc_CompAndSplit x t outch_comm2_new_l1 q r)) senv.
  Proof.
    pose proof outch_comm2_cut_q_r_p as Hcp'.
    eapply cp_perm.
    1: apply Hcp'.
    rewrite <- Hcp5.
    apply Permutation_cons; auto.
    symmetry.
    apply (new_L2_split _ _ _ _ _ _ Hcp6 outch_comm2_Hcp7' outch_comm2_Hcp8' outch_comm2_Hcp9' outch_comm2_Hcp10' outch_comm2_Hcp11' _ outch_comm2_gamma_channels_def _ outch_comm2_delta_channels_def _ outch_comm2_theta_channels_def).
  Qed.

  End Proc_OutCh_Comm_2.

  Lemma proc_outch_comm2 :
  forall x y z t l1 l2 p q r senv,
  In x (proc_channels q) ->
  x <> y ->
  ~ In x l1 ->
  cp (Proc_CompAndSplit x t l2 (Proc_OutChAndSplit y z l1 p q) r) senv ->
  cp (Proc_OutChAndSplit y z (outch_comm2_new_l2 x y z p q r) p (Proc_CompAndSplit x t (outch_comm2_new_l1 x y q r) q r)) senv.
  Proof.
    intros x y z t l1 l2 p q r senv Hx1 Hx2 Hx3 Hcp.
    pose proof (outch_comm_2_inv x y z t l1 l2 p q r senv Hcp Hx1 Hx2 Hx3) as (a & b & L1 & L2 & gamma_no_L1 & delta_no_L1 & gamma_delta_no_L2 & theta_no_L2 & _ & _ & Hcp2 & Hcp3 & Hcp4 & Hcp5 & Hcp6 & Hcp7 & Hcp8 & Hcp9 & Hcp10).
    apply (outch_comm2_q_r_p_perm x y z t l1 l2 p q r senv Hcp L1 L2 gamma_no_L1 delta_no_L1 gamma_delta_no_L2 theta_no_L2 a b Hcp2 Hcp3 Hcp4 Hcp5 Hcp6 Hcp7 Hcp8 Hcp9 Hcp10).
  Qed.

  Lemma proc_inch_comm :
  forall x t l p y z q senv,
  x <> y ->
  cp (Proc_CompAndSplit x t l (Proc_InCh y z p) q) senv ->
  ~ In z (proc_channels q) ->
  cp (Proc_InCh y z (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l p y z q senv Hneq Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_inch _ _ _ _ Hcp'4) as (a & b & gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    (* y in gamma or delta1_y *)
    assert (Hy : In (y, STyp_Par a b) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    (* y not in gamma *)
    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''2.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.

    (* x in gamma_delta1_x *)
    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    (* y not in delta2 *)
    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros w Hw; apply Hcp'3; rewrite Hdelta1; cbn; auto. }

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    (* Cut P and Q *)
    intros Hz.
    rewrite <- (proc_channels_perm _ _ Hcp'5) in Hz.
    cbn in Hz.
    rewrite map_app, in_app_iff in Hz.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (y, b) :: (z, a) :: delta1 ++ delta2)).
    { rewrite (perm_swap (x, t)) in Hcp''1.
      rewrite perm_swap in Hcp''1.
      do 2 rewrite Permutation_middle in Hcp''1.
      do 2 rewrite app_comm_cons.
      constructor; auto.
      intros w Hw.
      cbn in Hw.
      destruct Hw as [Hw | [Hw | Hw]]; try subst w.
      1,2: tauto.
      apply Hdelta1''; auto.
    }

    do 2 rewrite <- Permutation_middle in Hcp'.
    rewrite <- Hcp'6.
    rewrite <- Permutation_middle.
    constructor; auto.
  Qed.

  Lemma proc_outleft_comm :
  forall x t l p b y q senv,
  x <> y ->
  cp (Proc_CompAndSplit x t l (Proc_OutLeft y b p) q) senv ->
  cp (Proc_OutLeft y b (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l p b y q senv Hneq Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_outleft _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    assert (Hy : In (y, STyp_Plus a b) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''2.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros w Hw; apply Hcp'3; rewrite Hdelta1; cbn; auto. }

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (y, a) :: delta1 ++ delta2)).
    { rewrite (perm_swap (x, t)) in Hcp''1.
      rewrite Permutation_middle in Hcp''1.
      rewrite app_comm_cons.
      constructor; auto.
      intros w Hw.
      cbn in Hw.
      destruct Hw as [Hw | Hw]; try subst w; auto.
    }

    rewrite <- Permutation_middle in Hcp'.
    eapply cp_plus_left in Hcp'.
    rewrite Permutation_middle in Hcp'.
    rewrite Hcp'6 in Hcp'.
    auto.
  Qed.

  Lemma proc_outright_comm :
  forall x t l p a y q senv,
  x <> y ->
  cp (Proc_CompAndSplit x t l (Proc_OutRight y a p) q) senv ->
  cp (Proc_OutRight y a (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l p a y q senv Hneq Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_outright _ _ _ _ Hcp'4) as (b & gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    assert (Hy : In (y, STyp_Plus a b) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''2.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros w Hw; apply Hcp'3; rewrite Hdelta1; cbn; auto. }

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (y, b) :: delta1 ++ delta2)).
    { rewrite (perm_swap (x, t)) in Hcp''1.
      rewrite Permutation_middle in Hcp''1.
      rewrite app_comm_cons.
      constructor; auto.
      intros w Hw.
      cbn in Hw.
      destruct Hw as [Hw | Hw]; try subst w; auto.
    }

    rewrite <- Permutation_middle in Hcp'.
    eapply cp_plus_right in Hcp'.
    rewrite Permutation_middle in Hcp'.
    rewrite Hcp'6 in Hcp'.
    auto.
  Qed.

  Lemma proc_incase_comm :
  forall x t l y p q r senv,
  x <> y ->
  cp (Proc_CompAndSplit x t l (Proc_InCase y p q) r) senv ->
  cp (Proc_InCase y (Proc_CompAndSplit x t l p r) (Proc_CompAndSplit x t l q r)) senv.
  Proof.
    intros x t l y p q r senv Hneq Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_incase _ _ _ _ Hcp'4) as (a & b & gamma_delta1_x & Hcp''1 & Hcp''2 & Hcp''3).
    subst l.

    assert (Hy : In (y, STyp_With a b) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''3.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''3.
    rewrite perm_swap in Hcp''3.
    apply Permutation_cons_inv in Hcp''3.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''3; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2, Hcp''3.
    apply Permutation_cons_inv in Hcp''3.
    rewrite Hcp''3 in Hcp''1, Hcp''2.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros w Hw; apply Hcp'3; rewrite Hdelta1; cbn; auto. }

    clear gamma_delta1 Hcp''3 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p r) (gamma ++ (y, a) :: delta1 ++ delta2)).
    { rewrite perm_swap in Hcp''1.
      rewrite Permutation_middle in Hcp''1.
      rewrite app_comm_cons.
      constructor; auto.
      intros w Hw.
      cbn in Hw.
      destruct Hw as [Hw | Hw]; try subst w; auto.
    }

    assert (Hcp'' : cp (Proc_CompAndSplit x t (map fst gamma) q r) (gamma ++ (y, b) :: delta1 ++ delta2)).
    { rewrite perm_swap in Hcp''2.
      rewrite Permutation_middle in Hcp''2.
      rewrite app_comm_cons.
      constructor; auto.
      intros w Hw.
      cbn in Hw.
      destruct Hw as [Hw | Hw]; try subst w; auto.
    }

    rewrite <- Hcp'6.
    rewrite <- Permutation_middle.
    rewrite <- Permutation_middle in Hcp', Hcp''.
    constructor; auto.
  Qed.

  (* It turns out commutation for server is not so simple.
     The server rule requires that all other channels of P are clients.
     However, if P is cut with Q, Q may introduce channels which are not clients.
     Therefore, further structural analysis on Q is required.

     Since all channels of P other than y are clients, x must also be a client.
     Therefore, channel x of Q must be a server.

     If the principal constructor of Q is Proc_Server, then all channels other than the server channel must be clients.
     Therefore, x is the server channel of Q, and we can do the commutation.

     If the principal constructor of Q is not Proc_Server, can we do a commutation on the side of Q?
     Things become difficult if a const process exports both a server channel and a non-client channel.
   *)
  Lemma proc_server_comm' :
  forall x t l y z p q senv,
  x <> y ->
  Forall (fun r => fst r <> y -> match snd r with STyp_Ques _ => True | _ => False end) senv ->
  cp (Proc_CompAndSplit x t l (Proc_Server y z p) q) senv ->
  ~ In z (proc_channels q) ->
  cp (Proc_Server y z (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l y z p q senv Hneq Hques Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_server _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2 & Hcp''3).
    subst l.

    assert (Hy : In (y, STyp_Excl a) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''3.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''3.
    rewrite perm_swap in Hcp''3.
    apply Permutation_cons_inv in Hcp''3.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''3; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''2, Hcp''3.
    apply Permutation_cons_inv in Hcp''3.
    rewrite Hcp''3 in Hcp''2.
    rewrite Hdelta1', Hcp''3 in Hcp''1.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros w Hw; apply Hcp'3; rewrite Hdelta1; cbn; auto. }
    assert (Hy''' : ~ In y (map fst delta1)) by (rewrite perm_swap in Hcp''2; eauto with senv_valid).

    clear gamma_delta1 Hcp''3 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    intros Hz.
    rewrite <- (proc_channels_perm _ _ Hcp'5) in Hz.
    cbn in Hz.
    rewrite map_app, in_app_iff in Hz.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (z, a) :: delta1 ++ delta2)).
    { rewrite perm_swap in Hcp''2.
      rewrite Permutation_middle in Hcp''2.
      rewrite app_comm_cons.
      constructor; auto.
      intros w Hw.
      cbn in Hw.
      destruct Hw as [Hw | Hw]; try subst w; auto.
    }

    rewrite <- Hcp'6.
    rewrite <- Permutation_middle.
    rewrite <- Permutation_middle in Hcp'.
    rewrite <- Hcp'6 in Hcp; rewrite <- Permutation_middle in Hcp.
    constructor; auto.
    2: eauto with senv_valid.
    rewrite <- Hcp'6 in Hques.
    rewrite <- Permutation_middle in Hques.
    rewrite Forall_cons_iff in Hques.
    destruct Hques as (_ & Hques).
    rewrite Forall_forall; rewrite Forall_forall in Hques.
    intros w Hw.
    rewrite in_map_iff in Hw.
    destruct Hw as (v & Hv1 & Hv2); subst w.
    apply (Hques _ Hv2).
    do 2 rewrite in_app_iff in Hv2; destruct Hv2 as [Hv2 | [Hv2 | Hv2]]; intros Heq; apply (in_map fst) in Hv2; rewrite Heq in Hv2; tauto.
  Qed.

  Lemma proc_server_comm :
  forall x t l y z p u v q senv,
  x <> y ->
  cp (Proc_CompAndSplit x t l (Proc_Server y z p) (Proc_Server u v q)) senv ->
  x = u /\
  (~ In z (proc_channels (Proc_Server u v q)) ->
   cp (Proc_Server y z (Proc_CompAndSplit x t l p (Proc_Server u v q))) senv).
  Proof.
    intros x t l y z p u v q senv Hneq Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_server _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2 & Hcp''3).

    (* x must be a client *)
    assert (Hx : In (x, t) ((y, STyp_Excl a) :: gamma_delta1_x)) by (rewrite Hcp''3; left; auto).
    cbn in Hx.
    destruct Hx as [Hx | Hx].
    1: injection Hx; intros; subst y; contradiction.
    apply (in_map snd) in Hx.
    pose proof Hcp''1 as Hcp''1_x.
    rewrite Forall_forall in Hcp''1_x.
    specialize (Hcp''1_x _ Hx).
    cbn in Hcp''1_x.
    destruct t; try contradiction.
    clear Hcp''1_x.

    (* Hence, x is a server in Proc_Server u v q *)
    cbn in Hcp'5.
    destruct (cp_inv_server _ _ _ _ Hcp'5) as (a' & gamma_delta2 & Hcp'''1 & Hcp'''2 & Hcp'''3).
    assert (Hx' : In (x, STyp_Excl (dual t)) ((u, STyp_Excl a') :: gamma_delta2)) by (rewrite Hcp'''3; left; auto).
    cbn in Hx'.
    destruct Hx' as [Hx' | Hx'].
    2: apply (in_map snd) in Hx'; cbn in Hx'; rewrite Forall_forall in Hcp'''1; specialize (Hcp'''1 _ Hx'); cbn in Hcp'''1; contradiction.
    injection Hx'; intros; subst u a'.
    apply Permutation_cons_inv in Hcp'''3.
    split; auto.

    intros Hnin.
    apply proc_server_comm'; auto.
    rewrite <- Hcp'6.
    do 2 rewrite Forall_app.
    repeat split; rewrite Forall_forall.

    - rewrite Forall_forall in Hcp'1.
      intros w Hw _.
      apply (in_map snd) in Hw.
      specialize (Hcp'1 _ Hw); auto.

    - intros w Hw1 Hw2.
      assert (Hw3 : In w ((x, STyp_Ques t) :: gamma ++ delta1_y)) by (right; rewrite in_app_iff; auto).
      rewrite <- Hcp''3 in Hw3.
      cbn in Hw3.
      destruct Hw3 as [Hw3 | Hw3].
      1: subst w; contradiction.
      apply (in_map snd) in Hw3.
      rewrite Forall_forall in Hcp''1.
      specialize (Hcp''1 _ Hw3); auto.

    - intros w Hw1 _.
      assert (Hw2 : In w (gamma ++ delta2)) by (rewrite in_app_iff; auto).
      rewrite <- Hcp'''3 in Hw2.
      apply (in_map snd) in Hw2.
      rewrite Forall_forall in Hcp'''1.
      specialize (Hcp'''1 _ Hw2); auto.
  Qed.

  Lemma proc_client_comm_1 :
  forall x t l y z p q senv,
  x <> y ->
  ~ In y l ->
  cp (Proc_CompAndSplit x t l (Proc_Client y z p) q) senv ->
  ~ In z (proc_channels q) ->
  cp (Proc_Client y z (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l y z p q senv Hneq Hl Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_client _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    assert (Hy : In (y, STyp_Ques a) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map fst) in Hy; cbn in Hy; tauto.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''2.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros w Hw; apply Hcp'3; rewrite Hdelta1; cbn; auto. }
    assert (Hy''' : ~ In y (map fst delta1)) by eauto with senv_valid.

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    intros Hz.
    rewrite <- (proc_channels_perm _ _ Hcp'5) in Hz.
    cbn in Hz.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (z, a) :: delta1 ++ delta2)).
    { rewrite perm_swap in Hcp''1.
      rewrite Permutation_middle in Hcp''1.
      rewrite app_comm_cons.
      constructor; auto.
      intros w Hw.
      cbn in Hw.
      destruct Hw as [Hw | Hw].
      2: apply Hdelta1''; auto.
      subst w; rewrite map_app, in_app_iff in Hz; tauto.
    }

    rewrite <- Hcp'6.
    rewrite <- Permutation_middle.
    rewrite <- Permutation_middle in Hcp'.
    constructor; auto.
    do 2 rewrite map_app, in_app_iff; tauto.
  Qed.

  Lemma proc_client_comm_2 :
  forall x t l y z p q senv,
  x <> y ->
  In y l ->
  cp (Proc_CompAndSplit x t l (Proc_Client y z p) q) senv ->
  z <> y ->
  ~ In z (proc_channels q) ->
  cp (Proc_ClientSplit y z (Proc_Client z z (Proc_CompAndSplit x t (filter (fun s => negb (eqb y s)) l) p q))) senv.
  Proof.
    intros x t l y z p q senv Hneq Hl Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma_y & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_client _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    assert (Hy : In (y, STyp_Ques a) ((x, t) :: gamma_y ++ delta1)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    assert (Hdisjoint : senv_disjoint gamma_y delta1) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y Hl).
    destruct Hy as [Hy | Hy]; [|apply (in_map fst) in Hy; tauto].

    pose proof (in_split_perm _ _ Hy) as (gamma & Hgamma).
    rewrite Hgamma in Hcp, Hcp'1, Hcp'4, Hcp'5, Hcp'6, Hcp''2.
    cbn in Hcp, Hcp'1, Hcp'4, Hcp'5, Hcp'6, Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    clear Hl.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    assert (Hy'' : ~ In y (map fst (gamma ++ delta2))) by eauto with senv_valid senv_disjoint.
    rewrite map_app, in_app_iff in Hy''.
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { rewrite <- Hcp'6 in Hcp; eauto 6 with senv_valid senv_disjoint. }
    assert (Hy''' : ~ In y (map fst delta1)) by eauto with senv_valid.

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.

    rewrite perm_swap in Hcp''1.
    rewrite Permutation_middle in Hcp''1, Hcp'5.
    intros Hz1 Hz2.
    rewrite <- (proc_channels_perm _ _ Hcp'5) in Hz2.
    rewrite <- Permutation_middle in Hz2; cbn in Hz2.
    rewrite map_app, in_app_iff in Hz2.

    rewrite Hgamma; cbn; rewrite eqb_refl; cbn.
    rewrite forallb_filter_id.
    2: rewrite forallb_forall; intros w Hw; rewrite chn_negb_eqb_true_iff; intros Heq; subst w; tauto.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (z, a) :: delta1 ++ (y, STyp_Ques a) :: delta2)).
    { rewrite app_comm_cons.
      constructor; auto.
      1: rewrite Forall_cons_iff in Hcp'1; apply Hcp'1.
      unfold senv_disjoint; cbn; intros w Hw.
      destruct Hw as [Hw | Hw].
      - subst w; tauto.
      - intros Hin; destruct Hin as [Hin | Hin].
        1: subst w; tauto.
        apply (Hdelta1'' _ Hw Hin).
    }

    do 3 rewrite <- Permutation_middle in Hcp'.
    eapply cp_ques in Hcp'.
    Unshelve.
    3: exact z.
    2: { cbn; intros Hin; rewrite app_assoc in Hin.
         rewrite map_app, in_app_iff in Hin.
         rewrite <- Permutation_middle in Hcp''1.
         destruct Hin as [Hin | [Hin | Hin]].
         1: subst z; tauto.
         1: assert (~ In z (map fst (gamma ++ delta1))) by eauto with senv_valid; auto.
         tauto.
    }

    rewrite perm_swap in Hcp'.
    apply cp_contract in Hcp'.
    rewrite <- Hcp'6; auto.
  Qed.

  Lemma proc_client_null_comm_1 :
  forall x t l y a p q senv,
  x <> y ->
  ~ In y l ->
  cp (Proc_CompAndSplit x t l (Proc_ClientNull y a p) q) senv ->
  cp (Proc_ClientNull y a (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l y a p q senv Hneq Hl Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_client_null _ _ _ _ Hcp'4) as (gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    assert (Hy : In (y, STyp_Ques a) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map fst) in Hy; cbn in Hy; tauto.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''2.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros w Hw; apply Hcp'3; rewrite Hdelta1; cbn; auto. }
    assert (Hy''' : ~ In y (map fst delta1)) by eauto with senv_valid.

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ delta1 ++ delta2)).
    { constructor; auto. }

    eapply cp_weaken in Hcp'.
    1: rewrite <- Hcp'6; rewrite <- Permutation_middle; apply Hcp'.
    do 2 rewrite map_app, in_app_iff; tauto.
  Qed.

  Lemma proc_client_null_comm_2 :
  forall x t l y a p q senv,
  x <> y ->
  In y l ->
  cp (Proc_CompAndSplit x t l (Proc_ClientNull y a p) q) senv ->
  cp (Proc_CompAndSplit x t (filter (fun s => negb (eqb y s)) l) p q) senv.
  Proof.
    intros x t l y a p q senv Hneq Hl Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma_y & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_client_null _ _ _ _ Hcp'4) as (gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    assert (Hy : In (y, STyp_Ques a) ((x, t) :: gamma_y ++ delta1)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    assert (Hdisjoint : senv_disjoint gamma_y delta1) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y Hl).
    destruct Hy as [Hy | Hy]; [|apply (in_map fst) in Hy; tauto].

    pose proof (in_split_perm _ _ Hy) as (gamma & Hgamma).
    rewrite Hgamma in Hcp, Hcp'1, Hcp'4, Hcp'5, Hcp'6, Hcp''2.
    cbn in Hcp, Hcp'1, Hcp'4, Hcp'5, Hcp'6, Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    clear Hl.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    assert (Hy'' : ~ In y (map fst (gamma ++ delta2))) by eauto with senv_valid senv_disjoint.
    rewrite map_app, in_app_iff in Hy''.
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { rewrite <- Hcp'6 in Hcp; eauto 6 with senv_valid senv_disjoint. }
    assert (Hy''' : ~ In y (map fst delta1)) by eauto with senv_valid.

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.

    rewrite Hgamma; cbn.
    rewrite eqb_refl; cbn.
    rewrite forallb_filter_id.
    2: rewrite forallb_forall; intros w Hw; rewrite chn_negb_eqb_true_iff; intros Heq; subst w; tauto.
    rewrite <- Hcp'6.
    do 2 rewrite Permutation_middle.
    rewrite Permutation_middle in Hcp'5.
    constructor; auto.
    1: rewrite Forall_cons_iff in Hcp'1; apply Hcp'1.
    unfold senv_disjoint; cbn; intros w Hw1 Hw2.
    destruct Hw2 as [Hw2 | Hw2].
    - subst w; tauto.
    - apply (Hdelta1'' _ Hw1 Hw2).
  Qed.

  Lemma proc_client_split_comm_1 :
  forall x t l y z p q senv,
  x <> y ->
  ~ In y l ->
  cp (Proc_CompAndSplit x t l (Proc_ClientSplit y z p) q) senv ->
  ~ In z (proc_channels q) ->
  cp (Proc_ClientSplit y z (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l y z p q senv Hneq Hl Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_client_split _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    assert (Hy : In (y, STyp_Ques a) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map fst) in Hy; cbn in Hy; tauto.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''2.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros w Hw; apply Hcp'3; rewrite Hdelta1; cbn; auto. }
    assert (Hy''' : ~ In y (map fst delta1)) by eauto with senv_valid.

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    intros Hz.
    rewrite <- (proc_channels_perm _ _ Hcp'5) in Hz.
    cbn in Hz.
    rewrite map_app, in_app_iff in Hz.
    assert (Hz' : ~ In z (map fst delta1)).
    { rewrite (perm_swap (x, t)), Permutation_middle in Hcp''1; eauto 7 with senv_valid senv_disjoint. }
    do 2 rewrite (perm_swap (x, t)) in Hcp''1.
    do 2 rewrite Permutation_middle in Hcp''1.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (y, STyp_Ques a) :: (z, STyp_Ques a) :: delta1 ++ delta2)).
    { do 2 rewrite app_comm_cons; constructor; auto.
      intros w Hw; cbn in Hw.
      destruct Hw as [Hw | [Hw | Hw]].
      1,2: subst w; try tauto.
      apply (Hdelta1'' _ Hw).
    }

    do 2 rewrite <- Permutation_middle in Hcp'.
    apply cp_contract in Hcp'.
    rewrite <- Hcp'6.
    rewrite <- Permutation_middle; auto.
  Qed.

  Lemma proc_client_split_comm_2 :
  forall x t l y z p q senv,
  x <> y ->
  In y l ->
  cp (Proc_CompAndSplit x t l (Proc_ClientSplit y z p) q) senv ->
  ~ In z (proc_channels q) ->
  cp (Proc_ClientSplit y z (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l y z p q senv Hneq Hl Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma_y & delta1 & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_client_split _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    assert (Hy : In (y, STyp_Ques a) ((x, t) :: gamma_y ++ delta1)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    assert (Hdisjoint : senv_disjoint gamma_y delta1) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y Hl).
    destruct Hy as [Hy | Hy]; [|apply (in_map fst) in Hy; tauto].

    pose proof (in_split_perm _ _ Hy) as (gamma & Hgamma).
    rewrite Hgamma in Hcp, Hcp'1, Hcp'4, Hcp'5, Hcp'6, Hcp''2.
    cbn in Hcp, Hcp'1, Hcp'4, Hcp'5, Hcp'6, Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    clear Hl.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    assert (Hy'' : ~ In y (map fst (gamma ++ delta2))) by eauto with senv_valid senv_disjoint.
    rewrite map_app, in_app_iff in Hy''.
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { rewrite <- Hcp'6 in Hcp; eauto 6 with senv_valid senv_disjoint. }
    assert (Hy''' : ~ In y (map fst delta1)) by eauto with senv_valid.

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.

    rewrite perm_swap in Hcp''1.
    rewrite Permutation_middle in Hcp''1, Hcp'5.
    intros Hz.
    rewrite <- (proc_channels_perm _ _ Hcp'5) in Hz.
    rewrite <- Permutation_middle in Hz; cbn in Hz.
    rewrite map_app, in_app_iff in Hz.
    assert (Hz' : ~ In z (map fst delta1)).
    { rewrite perm_swap, Permutation_middle, perm_swap in Hcp''1; eauto 6 with senv_valid senv_disjoint. }

    rewrite <- Permutation_middle in Hcp''1.
    do 2 rewrite (perm_swap (x, t)) in Hcp''1.
    rewrite (perm_swap (y, STyp_Ques a)) in Hcp''1.
    rewrite Permutation_middle in Hcp''1.
    rewrite <- Permutation_middle in Hcp'5.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma_y) p q) ((y, STyp_Ques a) :: gamma ++ (z, STyp_Ques a) :: delta1 ++ delta2)).
    { rewrite Hgamma.
      rewrite (app_comm_cons delta1).
      rewrite app_comm_cons.
      constructor; auto.
      intros w Hw; cbn in Hw.
      destruct Hw as [Hw | Hw].
      1: subst w; tauto.
      apply (Hdelta1'' _ Hw).
    }

    rewrite <- Permutation_middle in Hcp'.
    apply cp_contract in Hcp'.
    rewrite <- Hcp'6; auto.
  Qed.

  Lemma proc_outtyp_comm :
  forall x t l y a w b p q senv,
  x <> y ->
  cp (Proc_CompAndSplit x t l (Proc_OutTyp y a w b p) q) senv ->
  cp (Proc_OutTyp y a w b (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l y a w b p q senv Hneq Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_outtyp _ _ _ _ _ _ Hcp'4) as (gamma_delta1_x & Hcp''1 & Hcp''2 & Hcp''3).
    subst l.

    assert (Hy : In (y, STyp_Exists w b) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''3.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''3.
    rewrite perm_swap in Hcp''3.
    apply Permutation_cons_inv in Hcp''3.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''3; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''2, Hcp''3.
    apply Permutation_cons_inv in Hcp''3.
    rewrite Hcp''3 in Hcp''2.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros z Hz; apply Hcp'3; rewrite Hdelta1; cbn; auto. }

    clear gamma_delta1 Hcp''3 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (y, styp_subst w b a) :: delta1 ++ delta2)).
    { rewrite perm_swap in Hcp''2.
      rewrite Permutation_middle in Hcp''2.
      rewrite app_comm_cons.
      constructor; auto.
      intros z Hz.
      cbn in Hz.
      destruct Hz as [Hz | Hz]; try subst z; auto.
    }

    rewrite <- Permutation_middle in Hcp'.
    apply cp_exists in Hcp'; auto.
    rewrite Permutation_middle in Hcp'.
    rewrite Hcp'6 in Hcp'.
    auto.
  Qed.

  (* Like server_comm above, this rule requires that Q does not introduce channels that contain w as a free variable.
     However this restriction can be worked around using intyp_rename.
   *)
  Lemma proc_intyp_comm' :
  forall x t l y w p q senv,
  x <> y ->
  Forall (fun r => fst r <> y -> ~ In w (fvar (snd r))) senv ->
  cp (Proc_CompAndSplit x t l (Proc_InTyp y w p) q) senv ->
  cp (Proc_InTyp y w (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l y w p q senv Hneq Hfree Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_intyp _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2 & Hcp''3).
    subst l.

    assert (Hy : In (y, STyp_Forall w a) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''3.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''3.
    rewrite perm_swap in Hcp''3.
    apply Permutation_cons_inv in Hcp''3.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''3; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2, Hcp''3.
    apply Permutation_cons_inv in Hcp''3.
    rewrite Hcp''3 in Hcp''1, Hcp''2.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros z Hz; apply Hcp'3; rewrite Hdelta1; cbn; auto. }
    assert (Hy''' : ~ In y (map fst delta1)) by (rewrite perm_swap in Hcp''2; eauto with senv_valid).

    clear gamma_delta1 Hcp''3 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    rewrite <- Hcp'6 in Hfree.
    rewrite <- Permutation_middle in Hfree.
    rewrite Forall_cons_iff in Hfree.
    destruct Hfree as (_ & Hfree).

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (y, a) :: delta1 ++ delta2)).
    { rewrite perm_swap in Hcp''2.
      rewrite Permutation_middle in Hcp''2.
      rewrite app_comm_cons.
      constructor; auto.
      intros z Hz.
      cbn in Hz.
      destruct Hz as [Hz | Hz]; try subst z; auto.
    }

    rewrite <- Permutation_middle in Hcp'.
    rewrite <- Hcp'6.
    rewrite <- Permutation_middle.
    constructor; auto.
    rewrite Forall_forall; rewrite Forall_forall in Hfree.
    intros z Hz.
    rewrite in_map_iff in Hz.
    destruct Hz as (v & Hv1 & Hv2); subst z.
    specialize (Hfree _ Hv2).
    apply Hfree.
    do 2 rewrite in_app_iff in Hv2; destruct Hv2 as [Hv2 | [Hv2 | Hv2]]; intros Heq; apply (in_map fst) in Hv2; rewrite Heq in Hv2; tauto.
  Qed.

  Lemma proc_intyp_comm :
  forall x t l y w w' p q senv,
  x <> y ->
  w <> w' ->
  proc_var_subst_pre p w w' ->
  ~ In w' (styp_forbidden (proc_channel_type p y) w) ->
  Forall (fun s => ~ In w' (fvar (proc_channel_type p s))) (proc_channels p) ->
  Forall (fun s => ~ In w' (fvar (proc_channel_type q s))) (proc_channels q) ->
  cp (Proc_CompAndSplit x t l (Proc_InTyp y w p) q) senv ->
  cp (Proc_InTypRename y w' w (Proc_InTyp y w' (Proc_CompAndSplit x t l (proc_var_subst p w (STyp_Var w')) q))) senv.
  Proof.
    intros x t l y w w' p q senv Hneq Hpre0 Hpre1 Hpre2 Hpre3 Hpre4 Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_intyp _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2 & Hcp''3).
    subst l.

    assert (Hy : In (y, STyp_Forall w a) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''3; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''3.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''3.
    rewrite perm_swap in Hcp''3.
    apply Permutation_cons_inv in Hcp''3.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''3; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2, Hcp''3.
    apply Permutation_cons_inv in Hcp''3.
    rewrite Hcp''3 in Hcp''1, Hcp''2.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros z Hz; apply Hcp'3; rewrite Hdelta1; cbn; auto. }
    assert (Hy''' : ~ In y (map fst delta1)) by (rewrite perm_swap in Hcp''2; eauto with senv_valid).

    clear gamma_delta1 Hcp''3 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    rewrite (proc_channel_type_correct p _ y a Hcp''2 ltac:(left; auto)) in Hpre2.

    assert (Hw : ~ In w' (fvar a)).
    { rewrite <- (proc_channels_perm _ _ Hcp''2) in Hpre3.
      rewrite Forall_forall in Hpre3.
      specialize (Hpre3 y ltac:(left; auto)).
      rewrite (proc_channel_type_correct p _ y a Hcp''2 ltac:(left; auto)) in Hpre3; auto.
    }

    assert (Hcp' : cp (proc_var_subst p w (STyp_Var w')) ((y, styp_subst w a (STyp_Var w')) :: (x, t) :: gamma ++ delta1)).
    { pose proof (cp_var_subst p w (STyp_Var w') _ Hcp''2) as Hsubst.
      match type of Hsubst with ?P -> _ => assert (Hsubst' : P) end.
      { cbn; rewrite Forall_cons_iff; split.
        - rewrite Forall_cons_iff; split; auto.
        - cbn in Hcp''1.
          rewrite Forall_forall; rewrite Forall_forall in Hcp''1.
          intros r Hr; specialize (Hcp''1 _ Hr).
          rewrite Forall_cons_iff; split; auto.
          unfold styp_forbidden; rewrite styp_forbidden_empty; auto.
      }
      specialize (Hsubst Hsubst'); clear Hsubst'.

      match type of Hsubst with ?P -> _ => assert (Hsubst' : P) end.
      { cbn; rewrite Forall_cons_iff; split; auto. }
      specialize (Hsubst Hsubst'); clear Hsubst'.

      cbn in Hsubst, Hcp''1.
      rewrite Forall_cons_iff in Hcp''1.
      destruct Hcp''1 as (Hfree1 & Hfree2).
      rewrite (styp_subst_no_free_ident w t) in Hsubst; auto.
      erewrite map_ext_in in Hsubst.
      1: rewrite map_id in Hsubst; auto.
      intros r Hr; destruct r as [s r]; cbn.
      rewrite Forall_forall in Hfree2.
      specialize (Hfree2 r ltac:(apply (in_map snd) in Hr; auto)).
      rewrite styp_subst_no_free_ident; auto.
    }

    rewrite perm_swap in Hcp'.
    rewrite Permutation_middle in Hcp'.
    assert (Hcp'' : cp (Proc_CompAndSplit x t (map fst gamma) (proc_var_subst p w (STyp_Var w')) q) (gamma ++ (y, styp_subst w a (STyp_Var w')) :: delta1 ++ delta2)).
    { rewrite app_comm_cons.
      constructor; auto.
      unfold senv_disjoint; cbn; intros z Hz.
      destruct Hz as [Hz | Hz].
      1: subst z; auto.
      apply Hdelta1''; auto.
    }

    rewrite <- Permutation_middle in Hcp''.
    eapply cp_forall in Hcp''.
    Unshelve.
    3: exact w'.
    2: { rewrite Forall_forall; rewrite Forall_forall in Hpre3, Hpre4.
         intros r; rewrite app_assoc, map_app, in_app_iff; intros Hr.
         destruct Hr as [Hr | Hr].
         - rewrite in_map_iff in Hr.
           destruct Hr as (s & Hr' & Hr); subst r; destruct s as [s r].
           specialize (Hpre3 s).
           rewrite <- (proc_channels_perm _ _ Hcp''2) in Hpre3.
           specialize (Hpre3 ltac:(cbn; right; right; apply (in_map fst) in Hr; auto)).
           rewrite (proc_channel_type_correct p _ s r Hcp''2 ltac:(right; right; auto)) in Hpre3.
           auto.
         - rewrite in_map_iff in Hr.
           destruct Hr as (s & Hr' & Hr); subst r; destruct s as [s r].
           specialize (Hpre4 s).
           rewrite <- (proc_channels_perm _ _ Hcp'5) in Hpre4.
           specialize (Hpre4 ltac:(cbn; right; rewrite map_app, in_app_iff; apply (in_map fst) in Hr; auto)).
           rewrite (proc_channel_type_correct q _ s r Hcp'5 ltac:(right; rewrite in_app_iff; auto)) in Hpre4.
           auto.
    }

    eapply cp_forall_rename in Hcp''.
    Unshelve.
    4: exact w.
    2: apply reverse_rename; auto.
    2: { intros Hin.
         apply var_free_subst in Hin.
         cbn in Hin.
         destruct Hin as [Hin | [Hin | Hin]]; [tauto | subst w'; tauto | tauto].
    }

    replace (styp_subst w' (styp_subst w a (STyp_Var w')) (STyp_Var w)) with a in Hcp''.
    1: rewrite <- Hcp'6; rewrite <- Permutation_middle; auto.

    rewrite <- subst_after_rename; auto.
    rewrite var_rename_ident; auto.
  Qed.

  Lemma proc_intyp_rename_comm :
  forall x t l y w w' p q senv,
  x <> y ->
  cp (Proc_CompAndSplit x t l (Proc_InTypRename y w w' p) q) senv ->
  cp (Proc_InTypRename y w w' (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l y w w' p q senv Hneq Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_intyp_rename _ _ _ _ _ Hcp'4) as (a & gamma_delta1_x & Hcp''1 & Hcp''2 & Hcp''3 & Hcp''4).
    subst l.

    assert (Hy : In (y, STyp_Forall w' (styp_subst w a (STyp_Var w'))) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''4; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''4.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''4.
    rewrite perm_swap in Hcp''4.
    apply Permutation_cons_inv in Hcp''4.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''4; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''3, Hcp''4.
    apply Permutation_cons_inv in Hcp''4.
    rewrite Hcp''4 in Hcp''3.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros z Hz; apply Hcp'3; rewrite Hdelta1; cbn; auto. }

    clear gamma_delta1 Hcp''4 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ (y, STyp_Forall w a) :: delta1 ++ delta2)).
    { rewrite perm_swap in Hcp''3.
      rewrite Permutation_middle in Hcp''3.
      rewrite app_comm_cons.
      constructor; auto.
      intros z Hz.
      cbn in Hz.
      destruct Hz as [Hz | Hz]; try subst z; auto.
    }

    rewrite <- Permutation_middle in Hcp'.
    eapply cp_forall_rename in Hcp'; auto.
    2: apply Hcp''1.
    2: apply Hcp''2.
    rewrite <- Hcp'6.
    rewrite <- Permutation_middle; auto.
  Qed.

  Lemma proc_inunit_comm :
  forall x t l y p q senv,
  x <> y ->
  cp (Proc_CompAndSplit x t l (Proc_InUnit y p) q) senv ->
  cp (Proc_InUnit y (Proc_CompAndSplit x t l p q)) senv.
  Proof.
    intros x t l y p q senv Hneq Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    destruct (cp_inv_inunit _ _ _ Hcp'4) as (gamma_delta1_x & Hcp''1 & Hcp''2).
    subst l.

    assert (Hy : In (y, STyp_Bot) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''2; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''2.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''2.
    rewrite perm_swap in Hcp''2.
    apply Permutation_cons_inv in Hcp''2.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''2; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''1, Hcp''2.
    apply Permutation_cons_inv in Hcp''2.
    rewrite Hcp''2 in Hcp''1.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros z Hz; apply Hcp'3; rewrite Hdelta1; cbn; auto. }

    assert (Hy''' : ~ In y (map fst delta1)) by eauto with senv_valid.

    clear gamma_delta1 Hcp''2 Hdelta1'.
    clear gamma_delta1_x Hx.
    clear delta1_y Hcp'3 Hy Hdisjoint Hdelta1.

    assert (Hcp' : cp (Proc_CompAndSplit x t (map fst gamma) p q) (gamma ++ delta1 ++ delta2)).
    { constructor; auto. }

    rewrite <- Permutation_middle in Hcp'6.
    eapply cp_bot in Hcp'.
    1: rewrite Hcp'6 in Hcp'; auto.
    do 2 rewrite map_app, in_app_iff; tauto.
  Qed.

  Lemma proc_emptycase_comm :
  forall x t l y l' q senv,
  x <> y ->
  cp (Proc_CompAndSplit x t l (Proc_EmptyCase y l') q) senv ->
  cp (Proc_EmptyCase y ((filter (fun s => negb (eqb x (fst s))) l') ++ (map (fun s => (s, proc_channel_type q s)) (filter (fun s => if in_dec eq_dec s l then false else true) (filter (fun s => negb (eqb x s)) (proc_channels q)))))) senv.
  Proof.
    intros x t l y l' q senv Hneq Hcp.
    destruct (cp_inv_comp_and_split _ _ _ _ _ _ Hcp) as (gamma & delta1_y & delta2 & Hcp'1 & Hcp'2 & Hcp'3 & Hcp'4 & Hcp'5 & Hcp'6).
    pose proof (cp_inv_emptycase _ _ _ Hcp'4) as Hcp''.
    subst l.
    rename l' into gamma_delta1_x.

    assert (Hy : In (y, STyp_Top) ((x, t) :: gamma ++ delta1_y)) by (rewrite <- Hcp''; left; auto).
    cbn in Hy.
    destruct Hy as [Hy | Hy].
    1: injection Hy; intros; subst y; contradiction.
    rewrite in_app_iff in Hy.

    destruct Hy as [Hy | Hy].
    1: apply (in_map snd) in Hy; rewrite Forall_forall in Hcp'1; specialize (Hcp'1 _ Hy); contradiction.
    assert (Hdisjoint : senv_disjoint gamma delta1_y) by eauto with senv_valid senv_disjoint.
    specialize (Hdisjoint y).
    assert (Hy' : ~ In y (map fst gamma)) by (apply (in_map fst) in Hy; tauto).

    pose proof (in_split_perm _ _ Hy) as (delta1 & Hdelta1).
    rewrite Hdelta1 in Hcp'4, Hcp'6, Hcp''.
    cbn in Hcp'6.
    rewrite <- Permutation_middle in Hcp''.
    rewrite perm_swap in Hcp''.
    apply Permutation_cons_inv in Hcp''.

    assert (Hx : In (x, t) gamma_delta1_x) by (rewrite Hcp''; left; auto).
    pose proof (in_split_perm _ _ Hx) as (gamma_delta1 & Hdelta1').
    rewrite Hdelta1' in Hcp''.
    apply Permutation_cons_inv in Hcp''.

    assert (Hy'' : ~ In y (map fst delta2)).
    { apply (in_map fst) in Hy; apply (Hcp'3 y ltac:(auto)). }
    assert (Hdelta1'' : senv_disjoint delta1 delta2).
    { intros z Hz; apply Hcp'3; rewrite Hdelta1; cbn; auto. }

    pose proof (proc_channels_filter_one_and_app _ _ _ _ _ Hcp'5) as Hq.

    assert (Hx' : ~ In x (map fst gamma)) by eauto with senv_valid.
    assert (Hx'' : ~ In x (map fst delta1)) by (rewrite Permutation_middle, perm_swap in Hcp'4; eauto with senv_valid).
    assert (Hy''' : ~ In y (map fst delta1)) by eauto with senv_valid.

    assert (Hp : Permutation (filter (fun s => negb (eqb x (fst s))) gamma_delta1_x) (gamma ++ delta1)).
    { rewrite Hdelta1'.
      cbn; rewrite eqb_refl; cbn.
      rewrite Hcp''; rewrite filter_app.
      rewrite forallb_filter_id.
      1: rewrite forallb_filter_id; auto.
      all: rewrite forallb_forall; intros z Hz; rewrite chn_negb_eqb_true_iff.
      all: intros Heq; subst; apply (in_map fst) in Hz; tauto.
    }

    rewrite <- Hcp'6.
    rewrite <- Permutation_middle.
    rewrite Hp, Hq.
    rewrite <- app_assoc.

    rewrite map_map; cbn.
    erewrite map_ext_in.
    1: rewrite map_id.
    2: { intros z Hz; destruct z as [w a]; cbn.
         rewrite (proc_channel_type_correct q _ w a Hcp'5 ltac:(right; rewrite in_app_iff; auto)); auto.
    }

    constructor.
    - do 2 rewrite map_app, in_app_iff; tauto.
    - rewrite <- Hcp'6 in Hcp; rewrite <- Permutation_middle in Hcp; eauto with senv_valid.
  Qed.

End Wadler_Transformation.

Module Wadler_Transformation_M (PropVarName : UsualDecidableType) (ChannelName : UsualDecidableType) (Import WT : Wadler_Types PropVarName) (Import WSE : Wadler_SEnv PropVarName ChannelName WT) (Import WPCS : Wadler_ProcConst_Sig PropVarName WT) (Import WP : Wadler_Proc PropVarName ChannelName WT WSE WPCS).
Include Wadler_Transformation PropVarName ChannelName WT WSE WPCS WP.
End Wadler_Transformation_M.
