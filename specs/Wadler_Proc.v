From Stdlib Require Import
  List
  Structures.Equalities
  Sorting.Permutation.
From Session.lib Require Import
  Lemmas.
From Session.specs Require Import
  Wadler_Types.
Import
  ListNotations.
Open Scope bool_scope.

Module Type Wadler_SEnv (PropVarName : UsualDecidableType) (ChannelName : UsualDecidableType) (Import WT : Wadler_Types PropVarName).

  #[local] Notation chn := ChannelName.t.

  Definition chn_eqb := fun x y => if ChannelName.eq_dec x y then true else false.
  Definition chn_eq_dec := ChannelName.eq_dec.
  Definition chn_eqb_spec x y : reflect (x = y) (chn_eqb x y).
  Proof. unfold chn_eqb; destruct (ChannelName.eq_dec x y); constructor; auto. Qed.
  Definition chn_eqb_refl x : chn_eqb x x = true.
  Proof. unfold chn_eqb; destruct (ChannelName.eq_dec x x); auto. Qed.
  Definition chn_eqb_neq x y : chn_eqb x y = false <-> x <> y.
  Proof. destruct (chn_eqb_spec x y); split; try contradiction; try discriminate; auto. Qed.

  #[local] Notation eqb := chn_eqb.
  #[local] Notation eq_dec := chn_eq_dec.
  #[local] Notation eqb_spec := chn_eqb_spec.
  #[local] Notation eqb_refl := chn_eqb_refl.
  #[local] Notation eqb_neq := chn_eqb_neq.

  Lemma chn_negb_eqb_true_iff : forall x y, negb (eqb x y) = true <-> x <> y.
  Proof.
    intros x y; rewrite Bool.negb_true_iff.
    destruct (eqb_spec x y); split; intros.
    all: try contradiction; try discriminate; auto.
  Qed.

  #[local] Notation negb_eqb_true_iff := chn_negb_eqb_true_iff.

  (* An environment is a list of (channel_name, type) pairs *)
  Definition SEnv := list (chn * STyp).

  (* An environment is valid, if it does not type the same channel twice. *)
  Definition senv_valid (senv : SEnv) : Prop := NoDup (map fst senv).

  Lemma senv_valid_cons x a senv : senv_valid ((x, a) :: senv) <-> ~ In x (map fst senv) /\ senv_valid senv.
  Proof.
    unfold senv_valid; cbn; rewrite NoDup_cons_iff.
    split; auto.
  Qed.

  Lemma senv_tail_valid x (senv : SEnv) : senv_valid (x :: senv) -> senv_valid senv.
  Proof.
    destruct x; rewrite senv_valid_cons; tauto.
  Qed.

  (* Two environments are disjoint if their channel names are disjoint *)
  Definition senv_disjoint (senv1 senv2: SEnv) : Prop := forall m, In m (map fst senv1) -> ~ In m (map fst senv2).

  Lemma senv_disjoint_disjoint (senv1 senv2: SEnv) : senv_disjoint senv1 senv2 -> forall m, In m senv1 -> ~ In m senv2.
  Proof.
    intros Hdisjoint m Hm.
    specialize (Hdisjoint (fst m) ltac:(rewrite in_map_iff; eexists; split; auto)).
    intros Hin; apply Hdisjoint; rewrite in_map_iff; eexists; split; auto.
  Qed.

  Lemma senv_disjoint_in_app (senv2 senv3 : SEnv) : senv_disjoint senv2 senv3 -> forall senv1 x, In x senv1 <-> In x (senv1 ++ senv2) /\ In x (senv1 ++ senv3).
  Proof.
    intros Hdisjoint senv1 x.
    pose proof (senv_disjoint_disjoint _ _ Hdisjoint x).
    do 2 rewrite in_app_iff.
    tauto.
  Qed.

  Lemma senv_disjoint_in_cons (senv2 senv3 : SEnv) : senv_disjoint senv2 senv3 -> forall y x, y = x <-> In x (y :: senv2) /\ In x (y :: senv3).
  Proof.
    intros Hdisjoint y x.
    pose proof (senv_disjoint_disjoint _ _ Hdisjoint x).
    cbn; tauto.
  Qed.

  Lemma senv_disjoint_app_valid : forall senv1 senv2,
  senv_valid senv1 ->
  senv_valid senv2 ->
  senv_disjoint senv1 senv2 ->
  senv_valid (senv1 ++ senv2).
  Proof.
    intros senv1 senv2 Hv1 Hv2 Hdj.
    unfold senv_disjoint in Hdj.
    unfold senv_valid.
    rewrite map_app.
    apply NoDup_app; auto.
  Qed.

  Lemma senv_app : forall senv1 senv2,
  senv_valid (senv1 ++ senv2) ->
  senv_valid senv1 /\ senv_valid senv2 /\ senv_disjoint senv1 senv2.
  Proof.
    intros senv1 senv2 Hval.
    unfold senv_valid in Hval.
    rewrite map_app in Hval.
    repeat split.
    - eapply NoDup_app_remove_r; apply Hval.
    - eapply NoDup_app_remove_l; apply Hval.
    - unfold senv_disjoint; apply NoDup_disjoint; auto.
  Qed.

  Definition str_list_repl (l : list chn) (s : chn) (t : chn) :=
  map (fun x => if eqb x s then t else x) l.

  Definition senv_rename (senv : SEnv) (s : chn) (t : chn) :=
  map (fun z => match z with (x, a) => if eqb x s then (t, a) else (x, a) end) senv.

  Lemma str_list_repl_ident : forall l s, str_list_repl l s s = l.
  Proof.
    intros l s.
    unfold str_list_repl.
    rewrite <- map_id.
    apply map_ext.
    intros s0; destruct (eqb_spec s0 s); try subst; auto.
  Qed.

  Lemma senv_rename_ident : forall (senv : SEnv) (s : chn), senv_rename senv s s = senv.
  Proof.
    intros senv s.
    unfold senv_rename.
    rewrite <- map_id.
    apply map_ext.
    intros z; destruct z.
    destruct (eqb_spec t s); try subst; auto.
  Qed.

  Lemma senv_rename_repl : forall senv s t, map fst (senv_rename senv s t) = str_list_repl (map fst senv) s t.
  Proof.
    intros senv.
    unfold str_list_repl, senv_rename.
    intros s t.
    do 2 rewrite map_map.
    apply map_ext.
    intros z; destruct z; cbn.
    destruct (eqb_spec t0 s); cbn; auto.
  Qed.

  Lemma str_list_repl_nin : forall l s t,
  ~ In s l ->
  str_list_repl l s t = l.
  Proof.
    intros l s t Hnin.
    unfold str_list_repl.
    rewrite <- map_id.
    apply map_ext_in.
    intros s0 Hin.
    destruct (eqb_spec s0 s); auto.
    subst s0; contradiction.
  Qed.

  Lemma senv_rename_nin : forall senv s t,
  ~ In s (map fst senv) ->
  senv_rename senv s t = senv.
  Proof.
    intros senv s t Hnin.
    rewrite <- (map_id senv) at 2.
    unfold senv_rename.
    apply map_ext_in.
    intros z Hz; destruct z.
    destruct (eqb_spec t0 s); auto.
    subst t0.
    exfalso; apply Hnin; rewrite in_map_iff; eexists; split.
    2: apply Hz.
    auto.
  Qed.

  Lemma senv_rename_app : forall senv senv' s t,
  senv_rename (senv ++ senv') s t = senv_rename senv s t ++ senv_rename senv' s t.
  Proof.
    intros senv senv' s t.
    unfold senv_rename.
    apply map_app.
  Qed.

  Lemma str_list_repl_nodup : forall l s t,
  ~ In t l ->
  NoDup l ->
  NoDup (str_list_repl l s t).
  Proof.
    intros l s t Hnin.
    induction l.
    - cbn; constructor.
    - cbn; intros Hnodup.
      inversion Hnodup as [| ? ? Ha Hl]; subst.
      fold (str_list_repl l s t); destruct (eqb_spec a s).
      + subst s; constructor.
        2: cbn in Hnin; apply IHl; tauto.
        intros Hin; unfold str_list_repl in Hin.
        rewrite in_map_iff in Hin.
        destruct Hin as (x & Hx1 & Hx2).
        destruct (eqb_spec x a).
        * subst; contradiction.
        * subst; cbn in Hnin; tauto.
      + constructor.
        2: cbn in Hnin; apply IHl; tauto.
        intros Hin; unfold str_list_repl in Hin.
        rewrite in_map_iff in Hin.
        destruct Hin as (x & Hx1 & Hx2).
        destruct (eqb_spec x s).
        * subst; cbn in Hnin; tauto.
        * subst; contradiction.
  Qed.

  Lemma senv_rename_nin_valid : forall senv s t,
  senv_valid senv ->
  ~ In t (map fst senv) ->
  senv_valid (senv_rename senv s t).
  Proof.
    intros senv s t Hval Hnin.
    unfold senv_valid.
    unfold senv_valid in Hval.
    revert Hval Hnin.
    induction senv.
    - cbn; constructor.
    - intros Hval Hin.
      cbn in Hin.
      cbn in Hval.
      rewrite NoDup_cons_iff in Hval.
      specialize (IHsenv ltac:(tauto) ltac:(tauto)).

      unfold senv_rename.
      cbn [map fst].
      fold (senv_rename senv s t).

      constructor; auto.
      unfold senv_rename.
      rewrite map_map.
      destruct a; cbn in Hval, Hin.
      destruct (eqb_spec t0 s).
      + subst t0.
        cbn.
        intros Hin'.
        rewrite in_map_iff in Hin'.
        destruct Hin' as (z & Hz1 & Hz2).
        destruct z.
        destruct (eqb_spec t0 s); cbn in Hz1; try subst t.
        * subst t0.
          apply Hval; rewrite in_map_iff; eexists; split; try apply Hz2; auto.
        * apply Hin; right; rewrite in_map_iff; eexists; split; try apply Hz2; auto.
      + cbn.
        intros Hin'.
        rewrite in_map_iff in Hin'.
        destruct Hin' as (z & Hz1 & Hz2).
        destruct z.
        destruct (eqb_spec t1 s); cbn in Hz1; subst t0; try subst t1.
        * tauto.
        * apply Hval; rewrite in_map_iff; eexists; split; try apply Hz2; auto.
  Qed.

  Lemma senv_rename_snd :
  forall senv s t, map snd (senv_rename senv s t) = map snd senv.
  Proof.
    intros senv s t.
    unfold senv_rename.
    rewrite map_map.
    apply map_ext.
    intros z.
    destruct z.
    destruct (eqb t0 s); cbn; auto.
  Qed.

End Wadler_SEnv.

Module Wadler_SEnv_M (PropVarName : UsualDecidableType) (ChannelName : UsualDecidableType) (WT : Wadler_Types PropVarName).
Include (Wadler_SEnv PropVarName ChannelName WT).
End Wadler_SEnv_M.

Module Type Wadler_ProcConst_Sig (PropVarName : UsualDecidableType) (Import WT : Wadler_Types PropVarName).

  Parameter pcn : Type.
  Parameter pcn_sig : pcn -> list STyp -> Prop.
  Parameter pcn_sig_subst :
    forall c l v e,
    Forall (fun r => Forall (fun v' => ~ In v' (styp_forbidden r v)) (fvar e)) l ->
    pcn_sig c l ->
    pcn_sig c (map (fun r => styp_subst v r e) l).

End Wadler_ProcConst_Sig.

Module Type Wadler_Proc (PropVarName : UsualDecidableType) (ChannelName : UsualDecidableType) (Import WT : Wadler_Types PropVarName) (Import WSE : Wadler_SEnv PropVarName ChannelName WT) (Import WPCS : Wadler_ProcConst_Sig PropVarName WT).

  #[local] Notation pvn := PropVarName.t.
  #[local] Notation chn := ChannelName.t.

  #[local] Notation eqb := chn_eqb.
  #[local] Notation eq_dec := chn_eq_dec.
  #[local] Notation eqb_spec := chn_eqb_spec.
  #[local] Notation eqb_refl := chn_eqb_refl.
  #[local] Notation eqb_neq := chn_eqb_neq.
  #[local] Notation negb_eqb_true_iff := chn_negb_eqb_true_iff.

  (* Compared to Wadler's paper, the main difference here is the addition of Proc_ClientNull and Proc_ClientSplit.
     This is due to syntactical difficulties around implementing channel renaming.

     For example, consider the following derivation rule:
        P |- Gamma, y : A     Q |- Delta, x : B
     ---------------------------------------------
     x[y].(P | Q) |- Gamma, Delta, x : A \otimes B

     In this derivation, the channel name y appears in process P, but not in the composed process.
     If we only look at the composed environment, we could get the impression that a channel in Gamma (say, z) could be renamed into y.
     However this is incorrect, as renaming z into y would cause P to become invalid (due to channel name clashing).

     To implement channel renaming correctly, we need to keep track of the names of all channels a process may provide.
     The system presented in Wadler's paper does not support this feature: the Weaken rule adds a channel but does not mark it in the process.
     We thus had to add ClientNull and ClientSplit to explicitly keep track of channel names that are added and deleted.
   *)
  Inductive Process :=
  | Proc_Const (n : pcn) (l : list chn)
  | Proc_Link (x : chn) (y : chn)
  | Proc_Comp (x : chn) (a : STyp) (p : Process) (q : Process)
  | Proc_OutCh (x : chn) (y : chn) (p : Process) (q : Process)
  | Proc_OutChAndSplit (x : chn) (y : chn) (l : list chn) (p : Process) (q : Process)
  | Proc_InCh (x : chn) (y : chn) (p : Process)
  | Proc_OutLeft (x : chn) (p : Process)
  | Proc_OutRight (x : chn) (p : Process)
  | Proc_InCase (x : chn) (p : Process) (q : Process)
  | Proc_Server (x : chn) (y : chn) (p : Process)
  | Proc_Client (x : chn) (y : chn) (p : Process)
  | Proc_ClientNull (x : chn) (p : Process)
  | Proc_ClientSplit (x : chn) (y : chn) (p : Process)
  | Proc_CompAndSplit (x : chn) (a : STyp) (l : list chn) (p : Process) (q : Process)
  | Proc_OutTyp (x : chn) (a : STyp) (v : pvn) (t : STyp) (p : Process)
  | Proc_InTyp (x : chn) (v : pvn) (t : STyp) (p : Process)
  | Proc_OutUnit (x : chn)
  | Proc_InUnit (x : chn) (p : Process)
  | Proc_EmptyCase (x : chn) (l : list chn).

  (* List of names of channels provided by a process *)
  Fixpoint proc_channels (p : Process) :=
  match p with
  | Proc_Const _ l => l
  | Proc_Link x y => [x; y]
  | Proc_Comp x a p q => filter (fun s => negb (eqb x s)) ((proc_channels p) ++ (proc_channels q))
  | Proc_OutCh x y p q => filter (fun s => negb (eqb y s)) (proc_channels p) ++ (proc_channels q)
  | Proc_OutChAndSplit x y l p q => l ++ filter (fun s => if in_dec eq_dec s l then false else negb (eqb y s)) (proc_channels p) ++ filter (fun s => if in_dec eq_dec s l then false else true) (proc_channels q)
  | Proc_InCh x y p => filter (fun s => negb (eqb y s)) (proc_channels p)
  | Proc_OutLeft x p => proc_channels p
  | Proc_OutRight x p => proc_channels p
  | Proc_InCase x p q => proc_channels p
  | Proc_Server x y p => x :: filter (fun s => negb (eqb y s)) (proc_channels p)
  | Proc_Client x y p => x :: filter (fun s => negb (eqb y s)) (proc_channels p)
  | Proc_ClientNull x p => x :: (proc_channels p)
  | Proc_ClientSplit x y p => filter (fun s => negb (eqb y s)) (proc_channels p)
  | Proc_CompAndSplit x a l p q => l ++ filter (fun s => if in_dec eq_dec s l then false else negb (eqb x s)) (proc_channels p ++ proc_channels q)
  | Proc_OutTyp x a _ _ p => proc_channels p
  | Proc_InTyp x v t p => proc_channels p
  | Proc_OutUnit x => [x]
  | Proc_InUnit x p => x :: proc_channels p
  | Proc_EmptyCase x l => x :: l
  end.

  (* If s is the name of a channel provided by process p, returns the list of names that s must not be renamed into *)
  (* Otherwise, return [] *)
  Fixpoint proc_forbidden (p : Process) (s : chn) :=
  match p with
  | Proc_Const _ l => if in_dec eq_dec s l then l else []
  | Proc_Link x y => if eqb x s then [y] else if eqb y s then [x] else []
  | Proc_Comp x a p q =>
      let gamma := filter (fun s => negb (eqb x s)) (proc_channels p) in
      let delta := filter (fun s => negb (eqb x s)) (proc_channels q) in
      if eqb x s then [] else if in_dec eq_dec s gamma then (proc_forbidden p s) ++ delta else if in_dec eq_dec s delta then (proc_forbidden q s) ++ gamma else []
  | Proc_OutCh x y p q =>
      let gamma := filter (fun s => negb (eqb y s)) (proc_channels p) in
      let delta := filter (fun s => negb (eqb x s)) (proc_channels q) in
      if eqb x s then gamma ++ (proc_forbidden q s) else if in_dec eq_dec s gamma then x :: (proc_forbidden p s) ++ delta else if in_dec eq_dec s delta then (proc_forbidden q s) ++ gamma else []
  | Proc_OutChAndSplit x y l p q =>
      let delta1 := filter (fun s => if in_dec eq_dec s l then false else negb (eqb y s)) (proc_channels p) in
      let delta2 := filter (fun s => if in_dec eq_dec s l then false else negb (eqb x s)) (proc_channels q) in
      if eqb x s then l ++ delta1 ++ (proc_forbidden q s) else if in_dec eq_dec s l then (proc_forbidden p s) ++ (proc_forbidden q s) else if in_dec eq_dec s delta1 then x :: l ++ delta2 ++ (proc_forbidden p s) else if in_dec eq_dec s delta2 then l ++ delta1 ++ (proc_forbidden q s) else []
  | Proc_InCh x y p => if eqb y s then [] else proc_forbidden p s
  | Proc_OutLeft x p => proc_forbidden p s
  | Proc_OutRight x p => proc_forbidden p s
  | Proc_InCase x p q => proc_forbidden p s ++ proc_forbidden q s
  | Proc_Server x y p =>
      let gamma := filter (fun s => negb (eqb y s)) (proc_channels p) in
      if eqb x s then gamma else if in_dec eq_dec s gamma then x :: proc_forbidden p s else []
  | Proc_Client x y p =>
      let gamma := filter (fun s => negb (eqb y s)) (proc_channels p) in
      if eqb x s then gamma else if in_dec eq_dec s gamma then x :: proc_forbidden p s else []
  | Proc_ClientNull x p =>
      let gamma := proc_channels p in
      if eqb x s then gamma else if in_dec eq_dec s gamma then x :: proc_forbidden p s else []
  | Proc_ClientSplit x y p => if eqb y s then [] else proc_forbidden p s
  | Proc_CompAndSplit x a l p q =>
      let delta1 := filter (fun s => if in_dec eq_dec s l then false else true) (proc_channels p) in
      let delta2 := filter (fun s => if in_dec eq_dec s l then false else true) (proc_channels q) in
      if eqb x s then [] else if in_dec eq_dec s l then (proc_forbidden p s) ++ (proc_forbidden q s) else if in_dec eq_dec s delta1 then (proc_forbidden p s) ++ delta2 else if in_dec eq_dec s delta2 then delta1 ++ (proc_forbidden q s) else []
  | Proc_OutTyp x a _ _ p => proc_forbidden p s
  | Proc_InTyp x v _ p => proc_forbidden p s
  | Proc_OutUnit x => []
  | Proc_InUnit x p =>
      let gamma := proc_channels p in
      if eqb x s then gamma else if in_dec eq_dec s gamma then x :: proc_forbidden p s else []
  | Proc_EmptyCase x l =>
      if in_dec eq_dec s (x :: l) then (x :: l) else []
  end.

  Inductive cp : Process -> SEnv -> Prop :=
  | cp_const :
    forall c l l',
      NoDup l -> pcn_sig c l' -> length l = length l' -> cp (Proc_Const c l) (combine l l')
  | cp_ax :
    forall w x a, ~ w = x -> cp (Proc_Link w x) [(w, dual a); (x, a)]
  | cp_cut :
    forall x a p q gamma delta,
      senv_disjoint gamma delta ->
      cp p ((x, a) :: gamma) ->
      cp q ((x, dual a) :: delta) ->
      cp (Proc_Comp x a p q) (gamma ++ delta)
  | cp_times :
    forall x y a b p q gamma delta,
      ~ In x (map fst gamma) ->
      senv_disjoint gamma delta ->
      cp p ((y, a) :: gamma) ->
      cp q ((x, b) :: delta) ->
      cp (Proc_OutCh x y p q) ((x, STyp_Times a b) :: gamma ++ delta)
  | cp_times_contract :
    forall x y a b p q gamma delta1 delta2,
      Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd gamma) ->
      ~ In x (map fst delta1) ->
      senv_disjoint delta1 delta2 ->
      cp p ((y, a) :: gamma ++ delta1) ->
      cp q ((x, b) :: gamma ++ delta2) ->
      cp (Proc_OutChAndSplit x y (map fst gamma) p q) ((x, STyp_Times a b) :: gamma ++ delta1 ++ delta2)
  | cp_par :
    forall x y a b p gamma,
      cp p ((x, b) :: (y, a) :: gamma) ->
      cp (Proc_InCh x y p) ((x, STyp_Par a b) :: gamma)
  | cp_plus_left :
    forall x a b p gamma,
      cp p ((x, a) :: gamma) ->
      cp (Proc_OutLeft x p) ((x, STyp_Plus a b) :: gamma)
  | cp_plus_right :
    forall x a b p gamma,
      cp p ((x, b) :: gamma) ->
      cp (Proc_OutRight x p) ((x, STyp_Plus a b) :: gamma)
  | cp_with :
    forall x a b p q gamma,
      cp p ((x, a) :: gamma) ->
      cp q ((x, b) :: gamma) ->
      cp (Proc_InCase x p q) ((x, STyp_With a b) :: gamma)
  | cp_excl :
    forall x y a p gamma,
      Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd gamma) ->
      ~ In x (map fst gamma) ->
      cp p ((y, a) :: gamma) ->
      cp (Proc_Server x y p) ((x, STyp_Excl a) :: gamma)
  | cp_ques :
    forall x y a p gamma,
      ~ In x (map fst gamma) ->
      cp p ((y, a) :: gamma) ->
      cp (Proc_Client x y p) ((x, STyp_Ques a) :: gamma)
  | cp_weaken :
    forall x a p gamma,
      ~ In x (map fst gamma) ->
      cp p gamma ->
      cp (Proc_ClientNull x p) ((x, STyp_Ques a) :: gamma)
  | cp_contract :
    forall x y a p gamma,
      cp p ((x, STyp_Ques a) :: (y, STyp_Ques a) :: gamma) ->
      cp (Proc_ClientSplit x y p) ((x, STyp_Ques a) :: gamma)
  | cp_cut_contract :
    forall x a p q gamma delta1 delta2,
      Forall (fun r => match r with STyp_Ques _ => True | _ => False end) (map snd gamma) ->
      senv_disjoint delta1 delta2 ->
      cp p ((x, a) :: gamma ++ delta1) ->
      cp q ((x, dual a) :: gamma ++ delta2) ->
      cp (Proc_CompAndSplit x a (map fst gamma) p q) (gamma ++ delta1 ++ delta2)
  | cp_exists :
    forall x v a b p gamma,
      Forall (fun v' => ~ In v' (styp_forbidden b v)) (fvar a) ->
      cp p ((x, styp_subst v b a) :: gamma) ->
      cp (Proc_OutTyp x a v b p) ((x, STyp_Exists v b) :: gamma)
  | cp_forall :
    forall x v a p gamma,
      Forall (fun r => ~ In v (fvar r)) (map snd gamma) ->
      cp p ((x, a) :: gamma) ->
      cp (Proc_InTyp x v a p) ((x, STyp_Forall v a) :: gamma)
  | cp_one : forall x, cp (Proc_OutUnit x) [(x, STyp_One)]
  | cp_bot :
    forall x p gamma,
      ~ In x (map fst gamma) ->
      cp p gamma ->
      cp (Proc_InUnit x p) ((x, STyp_Bot) :: gamma)
  | cp_top :
    forall x gamma,
      ~ In x (map fst gamma) ->
      senv_valid gamma ->
      cp (Proc_EmptyCase x (map fst gamma)) ((x, STyp_Top) :: gamma)
  | cp_perm :
    forall p gamma gamma',
      cp p gamma ->
      Permutation gamma gamma' ->
      cp p gamma'.

  (* If cp p gamma holds, then gamma is a valid environment *)
  Lemma cp_senv_valid :
  forall p senv,
  cp p senv ->
  senv_valid senv.
  Proof.
    intros p senv Hcp.
    induction Hcp.
    - unfold senv_valid; rewrite combine_map_fst; auto.
    - unfold senv_valid; cbn; constructor; [firstorder | constructor; auto; constructor].
    - apply senv_disjoint_app_valid; auto; eapply NoDup_cons_inv; eauto.
    - rewrite senv_valid_cons.
      rewrite senv_valid_cons in IHHcp1, IHHcp2.
      split.
      2: apply senv_disjoint_app_valid; tauto.
      rewrite map_app; rewrite in_app_iff; tauto.
    - rewrite senv_valid_cons.
      rewrite senv_valid_cons in IHHcp1, IHHcp2.
      rewrite map_app, in_app_iff in IHHcp1, IHHcp2.
      do 2 rewrite map_app, in_app_iff.
      split; [tauto|].
      rewrite app_assoc.
      apply senv_disjoint_app_valid.
      + tauto.
      + destruct IHHcp2 as (_ & H2); apply senv_app in H2; tauto.
      + unfold senv_disjoint.
        intros z Hz.
        rewrite map_app, in_app_iff in Hz.
        destruct Hz as [Hz | Hz].
        * destruct IHHcp2 as (_ & H2); apply senv_app in H2; destruct H2 as (_ & _ & H2); specialize (H2 z); auto.
        * specialize (H1 z); auto.
    - rewrite senv_valid_cons in IHHcp; cbn in IHHcp.
      rewrite senv_valid_cons in IHHcp.
      rewrite senv_valid_cons; tauto.
    - rewrite senv_valid_cons in IHHcp; rewrite senv_valid_cons; auto.
    - rewrite senv_valid_cons in IHHcp; rewrite senv_valid_cons; auto.
    - rewrite senv_valid_cons in IHHcp1; rewrite senv_valid_cons; auto.
    - rewrite senv_valid_cons in IHHcp; rewrite senv_valid_cons; tauto.
    - rewrite senv_valid_cons in IHHcp; rewrite senv_valid_cons; tauto.
    - rewrite senv_valid_cons; tauto.
    - rewrite senv_valid_cons in IHHcp; cbn in IHHcp.
      rewrite senv_valid_cons in IHHcp.
      rewrite senv_valid_cons; tauto.
    - rewrite senv_valid_cons in IHHcp1, IHHcp2.
      destruct IHHcp1 as (_ & IHHcp1); destruct IHHcp2 as (_ & IHHcp2).
      apply senv_app in IHHcp1, IHHcp2.
      apply senv_disjoint_app_valid.
      2: apply senv_disjoint_app_valid.
      1,2,3,4: tauto.
      destruct IHHcp1 as (_ & _ & IHHcp1).
      destruct IHHcp2 as (_ & _ & IHHcp2).
      unfold senv_disjoint; unfold senv_disjoint in IHHcp1, IHHcp2.
      intros m Hm; specialize (IHHcp1 _ Hm); specialize (IHHcp2 _ Hm).
      rewrite map_app; rewrite in_app_iff; tauto.
    - rewrite senv_valid_cons in IHHcp; rewrite senv_valid_cons; auto.
    - rewrite senv_valid_cons in IHHcp; rewrite senv_valid_cons; auto.
    - cbn; constructor; auto; constructor.
    - rewrite senv_valid_cons; tauto.
    - rewrite senv_valid_cons; tauto.
    - unfold senv_valid; eapply Permutation_NoDup.
      1: eapply Permutation_map; apply H.
      apply IHHcp.
  Qed.

  Lemma proc_channels_perm :
  forall p senv, cp p senv -> Permutation (map fst senv) (proc_channels p).
  Proof.
    intros p senv Hcp.
    induction Hcp.
    all: cbn; auto.
    1: rewrite combine_map_fst; auto.
    all: try rewrite map_app; try rewrite filter_app.
    all: try rewrite <- IHHcp1, <- IHHcp2; try rewrite <- IHHcp; cbn.
    all: try rewrite eqb_refl; cbn.
    9: rewrite H; auto.
    all: try apply cp_senv_valid in Hcp1, Hcp2; try apply cp_senv_valid in Hcp.
    all: try repeat rewrite senv_valid_cons in Hcp1, Hcp2; try repeat rewrite senv_valid_cons in Hcp.
    1,2,4,5,6,7: try (repeat rewrite forallb_filter_id; auto; try (rewrite forallb_forall; intros z Hz; rewrite negb_eqb_true_iff; intros Heq; subst; tauto)).
    1: rewrite Permutation_middle; auto.
    1,2: cbn in Hcp; destruct (eqb_spec y x); try tauto; cbn; auto.

    1: rewrite map_app in Hcp1, Hcp2;
       rewrite in_app_iff in Hcp1, Hcp2;
       destruct (in_dec eq_dec y (map fst gamma)); [tauto|];
       destruct (in_dec eq_dec x (map fst gamma)); [tauto|];
       destruct Hcp1 as (? & Hcp1); destruct Hcp2 as (? & Hcp2);
       unfold senv_valid in Hcp1, Hcp2;
       rewrite map_app in Hcp1, Hcp2;
       pose proof (NoDup_disjoint _ _ Hcp1) as Hcp3;
       pose proof (NoDup_disjoint _ _ Hcp2) as Hcp4.

    2: rewrite map_app in Hcp1, Hcp2;
       rewrite in_app_iff in Hcp1, Hcp2;
       destruct (in_dec eq_dec x (map fst gamma)); [tauto|];
       destruct Hcp1 as (? & Hcp1); destruct Hcp2 as (? & Hcp2);
       unfold senv_valid in Hcp1, Hcp2;
       rewrite map_app in Hcp1, Hcp2;
       pose proof (NoDup_disjoint _ _ Hcp1) as Hcp3;
       pose proof (NoDup_disjoint _ _ Hcp2) as Hcp4.

    all: do 3 rewrite map_app.
    all: do 2 try match goal with |- context[filter ?f (?l1 ++ ?l2)] => replace (filter f (l1 ++ l2)) with l2 end; auto.
    1: do 2 rewrite <- Permutation_middle; auto.
    all: rewrite filter_app.
    1,3: rewrite (forallb_filter_id _ (map fst delta2)).
    1,3: rewrite forallb_filter_nil; auto.
    5,6: rewrite (forallb_filter_id _ (map fst delta1)).
    5,7: rewrite forallb_filter_nil; auto.
    all: rewrite forallb_forall; intros z Hz; specialize (Hcp3 z); specialize (Hcp4 z).
    all: destruct (in_dec eq_dec z (map fst gamma)); try tauto; auto.
    all: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
  Qed.

  Lemma cp_channels :
  forall p senv x',
  cp p senv ->
  In x' (map fst senv) <-> In x' (proc_channels p).
  Proof. intros p senv x' Hcp; rewrite (proc_channels_perm _ _ Hcp); tauto. Qed.

  (* If s is not a channel of p, then proc_forbidden returns [].
     This lemma is used to reason about the correctness of proc_rename.
     When proc_rename encounters a process composed of two subprocesses, it does not know which process provided the given channel.
     Of course we can inspect the structure of two processes to get this information, but that would too costly.
     Instead, we simply perform renaming on both subprocesses.
     To prove that this is correct (i.e. not resulting in name clashing), we need to show that renaming a nonexistent channel is not forbidden. 
   *)
  Lemma proc_forbidden_empty :
  forall p gamma s,
  cp p gamma ->
  ~ In s (map fst gamma) ->
  proc_forbidden p s = [].
  Proof.
    intros p gamma s Hcp.
    revert s.
    induction Hcp.
    - (* Proc_Const *)
      cbn; intros s Hin.
      rewrite combine_map_fst in Hin; auto.
      destruct (in_dec eq_dec s l); auto; contradiction.

    - (* Proc_Link w x *)
      cbn; intros s Hin.
      destruct (eqb_spec w s).
      1: tauto.
      destruct (eqb_spec x s).
      1: tauto.
      auto.

    - (* Proc_Comp x a p q *)
      cbn; intros s Hin.
      rewrite map_app, in_app_iff in Hin.

      (* Case 1: s = x *)
      destruct (eqb_spec x s); auto.

      (* Case 2: s in gamma *)
      match goal with |- context[if ?p then _ else _] => destruct p end.
      + (* s in gamma *)
        rewrite filter_In in i; destruct i as (i & _).
        rewrite <- (cp_channels _ _ _ Hcp1) in i.
        cbn in i.
        destruct i as [? | i]; [contradiction|].

        tauto.

      + (* Case 3: s in delta *)
        match goal with |- context[if ?p then _ else _] => destruct p end; auto.
        (* s in delta *)
        rewrite filter_In in i; destruct i as (i & _).
        rewrite <- (cp_channels _ _ _ Hcp2) in i.
        cbn in i.
        destruct i as [? | i]; [contradiction|].

        tauto.

    - (* Proc_OutCh x y p q *)
      cbn; intros s Hin.
      rewrite map_app, in_app_iff in Hin.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      1: subst s; tauto.

      (* Case 2: s in gamma *)
      match goal with |- context[if ?p then _ else _] => destruct p end.
      + (* s in gamma *)
        rewrite filter_In in i.
        rewrite negb_eqb_true_iff in i.
        rewrite <- (cp_channels _ _ _ Hcp1) in i.
        cbn in i.

        tauto.

      + clear n0.
        (* Case 3: s in delta *)
        match goal with |- context[if ?p then _ else _] => destruct p end; auto.
        (* s in delta *)
        rewrite filter_In in i.
        rewrite negb_eqb_true_iff in i.
        rewrite <- (cp_channels _ _ _ Hcp2) in i.
        cbn in i.

        tauto.

    - (* Proc_OutChAndSplit *)
      cbn; intros s Hin.
      do 2 rewrite map_app, in_app_iff in Hin.
      destruct (eqb_spec x s); [tauto|].
      destruct (in_dec eq_dec s (map fst gamma)); [tauto|].

      match goal with |- context[if ?p then _ else _] => destruct p end.
      + rewrite filter_In in i.
        rewrite <- (cp_channels _ _ _ Hcp1) in i.
        destruct (in_dec eq_dec s (map fst gamma)); [tauto|].
        rewrite negb_eqb_true_iff in i.
        cbn in i.
        rewrite map_app, in_app_iff in i.
        tauto.

      + match goal with |- context[if ?p then _ else _] => destruct p end; auto.
        rewrite filter_In in i.
        rewrite <- (cp_channels _ _ _ Hcp2) in i.
        destruct (in_dec eq_dec s (map fst gamma)); [tauto|].
        rewrite negb_eqb_true_iff in i.
        cbn in i.
        rewrite map_app, in_app_iff in i.
        tauto.

    - (* Proc_InCh x y p *)
      cbn; intros s Hin.
      destruct (eqb_spec y s); auto.
      apply IHHcp; cbn; tauto.

    - (* Proc_OutLeft x p *)
      cbn; apply IHHcp.
    - (* Proc OutRight x p *)
      cbn; apply IHHcp.
    - (* Proc_InCase x p q *)
      cbn; intros s Hin.
      cbn in IHHcp1, IHHcp2.
      rewrite IHHcp1, IHHcp2; auto.

    - (* Proc_Server x y p *)
      cbn; intros s Hin.
      (* Case 1: s = x *)
      destruct (eqb_spec x s); [tauto|].

      (* Case 2: s in gamma *)
      match goal with |- context[if ?p then _ else _] => destruct p end; auto.
      (* s in gamma *)
      rewrite filter_In in i.
      rewrite <- (cp_channels _ _ _ Hcp) in i.
      rewrite negb_eqb_true_iff in i.
      cbn in i.

      (* y not in gamma *)
      apply cp_senv_valid in Hcp.
      rewrite senv_valid_cons in Hcp.

      destruct i as ([i | i] & Hneq); [|tauto].
      contradiction.

    - (* Proc_Client x y p *)
      cbn; intros s Hin.
      (* Case 1: s = x *)
      destruct (eqb_spec x s); [tauto|].

      (* Case 2: s in gamma *)
      match goal with |- context[if ?p then _ else _] => destruct p end; auto.
      (* s in gamma *)
      rewrite filter_In in i.
      rewrite <- (cp_channels _ _ _ Hcp) in i.
      rewrite negb_eqb_true_iff in i.
      cbn in i.

      (* y not in gamma *)
      apply cp_senv_valid in Hcp.
      rewrite senv_valid_cons in Hcp.

      destruct i as ([i | i] & Hneq); [|tauto].
      contradiction.

    - (* Proc_ClientNull x p *)
      cbn; intros s Hin.

      (* Case 1: s = x *)
      destruct (eqb_spec x s); [tauto|].

      (* Case 2: s in gamma *)
      match goal with |- context[if ?p then _ else _] => destruct p end; auto.
      rewrite <- (cp_channels _ _ _ Hcp) in i.
      tauto.

    - (* Proc_ClientSplit x y p *)
      cbn; intros s Hin.

      (* Case 1: s = y *)
      destruct (eqb_spec y s); auto.

      (* Hin assumes s <> x and s not in gamma, thus apply IH directly *)
      apply IHHcp; cbn; tauto.

    - (* Proc_CompAndSplit *)
      cbn; intros s Hin.

      (* Simplify Hin *)
      do 2 rewrite map_app in Hin.
      do 2 rewrite in_app_iff in Hin.

      (* Case 1: x = s *)
      destruct (eqb_spec x s); auto.

      (* Case 2: s in gamma *)
      destruct (in_dec eq_dec s (map fst gamma)); [tauto|].

      (* Case 3: s in delta1 *)
      match goal with |- context[if ?p then _ else _] => destruct p end.
      + rewrite filter_In in i.
        rewrite <- (cp_channels _ _ _ Hcp1) in i.
        cbn in i.
        rewrite map_app, in_app_iff in i.
        tauto.

      + (* Case 4: s in delta2 *)
        match goal with |- context[if ?p then _ else _] => destruct p end; auto.
        rewrite filter_In in i.
        rewrite <- (cp_channels _ _ _ Hcp2) in i.
        cbn in i.
        rewrite map_app, in_app_iff in i.
        tauto.

    - (* Proc_OutTyp x a p *)
      cbn; apply IHHcp.
    - (* Proc_InTyp x v p *)
      cbn; apply IHHcp.
    - (* Proc_OutUnit x *)
      cbn; auto.

    - (* Proc_InUnit *)
      cbn; intros s Hin.
      (* Case 1: s = x *)
      destruct (eqb_spec x s); [tauto|].

      (* Case 2: s in gamma *)
      match goal with |- context[if ?p then _ else _] => destruct p end; auto.
      rewrite <- (cp_channels _ _ _ Hcp) in i.
      tauto.

    - (* Proc_EmptyCase x gamma *)
      cbn [map fst].
      unfold proc_forbidden.
      intros s Hin.
      match goal with |- context[if ?p then _ else _] => destruct p end; auto.
      contradiction.

    - (* Permutation *)
      intros s Hin; apply IHHcp.
      intros Hin'; apply Hin.
      rewrite <- H; auto.
  Qed.

  (* Channels provided by the same process are forbidden *)
  Lemma proc_forbidden_channel :
  forall p gamma s t,
  cp p gamma ->
  In s (map fst gamma) ->
  In t (map fst gamma) ->
  s <> t ->
  In t (proc_forbidden p s).
  Proof.
    intros p gamma s t Hcp.
    revert s t.
    induction Hcp.
    - (* Proc_Const *)
      cbn; intros s t.
      rewrite combine_map_fst; auto.
      intros Hin Hin' Hneq.
      destruct (in_dec eq_dec s l); try contradiction; auto.

    - (* Proc_Link *)
      cbn; intros s t.
      (* Case 1: s = w *)
      destruct (eqb_spec w s).
      + subst s; intros _ Hin Hin'.
        cbn; tauto.

      + (* Case 2: s = x *)
        destruct (eqb_spec x s).
        * subst s; intros _ Hin Hin'.
          cbn; tauto.

        * (* Case 3: otherwise *)
          cbn; tauto.

    - (* Proc_Comp *)
      cbn; intros s t.
      (* x not in gamma, delta *)
      apply cp_senv_valid in Hcp1 as Hcp1'.
      apply cp_senv_valid in Hcp2 as Hcp2'.
      rewrite senv_valid_cons in Hcp1', Hcp2'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        (* senv_valid *)
        apply cp_senv_valid in Hcp1, Hcp2.
        rewrite senv_valid_cons in Hcp1, Hcp2.

        (* Simplify goal *)
        rewrite map_app; rewrite in_app_iff; cbn.
        tauto.

      + (* Case 2: s in gamma *)
        match goal with |- context[if ?p then _ else _] => destruct p end.
        * (* s in gamma *)
          rewrite filter_In in i.
          rewrite negb_eqb_true_iff in i.
          rewrite <- (cp_channels _ _ _ Hcp1) in i.
          cbn in i.
          assert (i' : In s (map fst gamma)) by tauto.
          intros _.

          (* Apply this fact to IHHcp1 *)
          specialize (IHHcp1 s t ltac:(cbn; right; auto)).

          (* Simplify goal *)
          rewrite map_app.
          repeat rewrite in_app_iff.
          rewrite filter_In.
          rewrite negb_eqb_true_iff.
          rewrite <- (cp_channels _ _ _ Hcp2); cbn.

          (* If t in gamma then it is covered by IHHcp1, otherwise t in delta and it is covered by proc_channels *)
          intros Hin Hneq.
          destruct Hin as [Hin | Hin].
          -- specialize (IHHcp1 ltac:(cbn; right; auto) Hneq); auto.
          -- right; split; auto.
             intros Heq; subst t; tauto.

        * (* s not in gamma *)
          rewrite filter_In in n0.
          rewrite negb_eqb_true_iff in n0.
          rewrite <- (cp_channels _ _ _ Hcp1) in n0.
          cbn in n0.
          assert (n0' : ~ In s (map fst gamma)) by tauto.

          (* Case 3: s in delta *)
          match goal with |- context[if ?p then _ else _] => destruct p end.
          -- (* s in delta *)
             rewrite filter_In in i.
             rewrite negb_eqb_true_iff in i.
             rewrite <- (cp_channels _ _ _ Hcp2) in i.
             cbn in i.
             assert (i' : In s (map fst delta)) by tauto.
             intros _.

             (* Apply this fact to IHHcp2 *)
             specialize (IHHcp2 s t ltac:(cbn; right; auto)).

             (* Simplify goal *)
             rewrite map_app.
             repeat rewrite in_app_iff.
             rewrite filter_In.
             rewrite negb_eqb_true_iff.
             rewrite <- (cp_channels _ _ _ Hcp1); cbn.

             (* Symmetric to the case above *)
             intros Hin Hneq.
             destruct Hin as [Hin | Hin].
             ++ right; split; auto.
                intros Heq; subst t; tauto.
             ++ specialize (IHHcp2 ltac:(cbn; right; auto) Hneq); auto.

          -- (* Case 4: s not in gamma, delta *)
             rewrite filter_In in n1.
             rewrite negb_eqb_true_iff in n1.
             rewrite <- (cp_channels _ _ _ Hcp2) in n1.
             cbn in n1.

             rewrite map_app, in_app_iff.
             tauto.

    - (* Proc_OutCh *)
      cbn; intros s t.
      (* y not in gamma, x not in delta *)
      apply cp_senv_valid in Hcp1 as Hcp1'.
      apply cp_senv_valid in Hcp2 as Hcp2'.
      rewrite senv_valid_cons in Hcp1', Hcp2'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s; intros _.

        (* Simplify goal *)
        rewrite map_app.
        repeat rewrite in_app_iff.
        rewrite filter_In.
        rewrite negb_eqb_true_iff.
        rewrite <- (cp_channels _ _ _ Hcp1); cbn.

        (* Simplify IHHcp2 *)
        specialize (IHHcp2 x t ltac:(cbn; left; auto)).

        (* Since s <> t, either t in gamma or t in delta *)
        intros Hin Hneq.
        destruct Hin as [? | Hin]; [contradiction|].
        destruct Hin as [Hin | Hin].
        -- left; split; auto.
           intros Heq; subst t; tauto.
        -- right.
           apply (IHHcp2 ltac:(cbn; right; auto) Hneq).

      + intros Hin; destruct Hin as [? | Hin]; [contradiction|].
        rewrite map_app, in_app_iff in Hin.
        (* Case 2: s in gamma *)
        match goal with |- context[if ?p then _ else _] => destruct p end.
        * clear Hin.
          (* s in gamma *)
          rewrite filter_In in i.
          rewrite negb_eqb_true_iff in i.
          rewrite <- (cp_channels _ _ _ Hcp1) in i; cbn in i.
          assert (i' : In s (map fst gamma)) by tauto.

          (* Simplify goal *)
          cbn.
          rewrite map_app.
          repeat rewrite in_app_iff.
          rewrite filter_In.
          rewrite negb_eqb_true_iff.
          rewrite <- (cp_channels _ _ _ Hcp2); cbn.

          (* Simplify IHHcp1 *)
          specialize (IHHcp1 s t ltac:(cbn; right; auto)).

          intros Hin Hneq.
          destruct Hin as [Hin | [Hin | Hin]].
          -- auto.
          -- right; left; apply (IHHcp1 ltac:(cbn; right; auto) Hneq).
          -- right; right; split; auto.
             intros Heq; subst t; tauto.

        * (* Case 3: s not in gamma, but Hin assumes s in gamma or delta, so s in delta *)
          rewrite filter_In in n0.
          rewrite <- (cp_channels _ _ _ Hcp1) in n0.
          cbn in n0.
          rewrite negb_eqb_true_iff in n0.
          assert (n0' : ~ In s (map fst gamma)) by (revert n0; apply list_nin_helper; tauto).
          destruct Hin as [Hin | Hin]; [contradiction|].

          match goal with |- context[if ?p then _ else _] => destruct p end.
          2: { rewrite filter_In, negb_eqb_true_iff in n1.
               rewrite <- (cp_channels _ _ _ Hcp2) in n1.
               cbn in n1; tauto.
          }

          (* Simplify goal *)
          clear i.
          rewrite map_app.
          repeat rewrite in_app_iff.
          rewrite filter_In.
          rewrite negb_eqb_true_iff.
          rewrite <- (cp_channels _ _ _ Hcp1); cbn.

          (* Simplify IHHcp2 *)
          specialize (IHHcp2 s t ltac:(cbn; right; auto)).

          intros Hin' Hneq.
          destruct Hin' as [Hin' | [Hin' | Hin']].
          -- subst t.
             specialize (IHHcp2 ltac:(cbn; left; auto) Hneq).
             auto.
          -- right; split; auto.
             intros Heq; subst t; tauto.
          -- specialize (IHHcp2 ltac:(cbn; right; auto) Hneq).
             auto.

    - (* Proc_OutChAndSplit *)
      cbn; intros s t.
      (* senv_valid *)
      apply cp_senv_valid in Hcp1 as Hcp1'.
      apply cp_senv_valid in Hcp2 as Hcp2'.
      rewrite senv_valid_cons in Hcp1', Hcp2'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s; intros _.
        intros Hin Hneq.
        destruct Hin as [? | Hin]; [tauto|].
        do 2 rewrite map_app, in_app_iff in Hin.
        do 2 rewrite in_app_iff.
        rewrite map_app, in_app_iff in Hcp1', Hcp2'.

        (* Simplify goal *)
        rewrite <- (proc_channels_perm _ _ Hcp1); cbn.
        rewrite (eqb_refl y); cbn.
        destruct (in_dec eq_dec y (map fst gamma)); [tauto|].
        rewrite map_app, filter_app.
        rewrite forallb_filter_nil.
        1: rewrite forallb_filter_id.
        2,3: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
        2: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' z); tauto.
        2: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
        cbn.

        destruct Hin as [Hin | [Hin | Hin]].
        1,2: auto.
        specialize (IHHcp2 x t ltac:(cbn; left; auto) ltac:(cbn; right; rewrite map_app, in_app_iff; auto) Hneq).
        auto.

        + destruct (in_dec eq_dec s (map fst gamma)).
          * intros _.
            rewrite app_assoc.
            rewrite map_app.
            do 2 rewrite in_app_iff.
            intros Hin Hneq.
            destruct Hin as [Hin | [Hin | Hin]].
            -- subst t.
               specialize (IHHcp2 s x ltac:(cbn; right; rewrite map_app, in_app_iff; auto) ltac:(cbn; left; auto) Hneq).
               auto.
            -- specialize (IHHcp1 s t ltac:(cbn; right; rewrite map_app, in_app_iff; auto) ltac:(cbn; right; auto) Hneq).
               auto.
            -- specialize (IHHcp2 s t ltac:(cbn; right; rewrite map_app, in_app_iff; auto) ltac:(cbn; right; rewrite map_app, in_app_iff; auto) Hneq).
               auto.

          * (* Case 3: s in delta1 *)
            match goal with |- context[if ?p then _ else _] => destruct p end.
            -- rewrite <- (proc_channels_perm _ _ Hcp1) in i.
               cbn in i.
               rewrite eqb_refl in i; cbn in i.
               destruct (in_dec eq_dec y (map fst gamma)).
               1: rewrite map_app, in_app_iff in Hcp1'; tauto.

               rewrite <- (proc_channels_perm _ _ Hcp2); cbn.
               rewrite eqb_refl; cbn.
               destruct (in_dec eq_dec x (map fst gamma)).
               1: rewrite map_app, in_app_iff in Hcp2'; tauto.

               rewrite map_app, filter_app in i.
               rewrite (map_app fst gamma delta2), filter_app.
               rewrite forallb_filter_nil in i.
               1: rewrite forallb_filter_id in i.
               1: rewrite forallb_filter_nil.
               1: rewrite forallb_filter_id.
               2,3,4,5: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
               4: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' z); tauto.
               4: rewrite negb_eqb_true_iff; intros Heq; subst z; rewrite map_app, in_app_iff in Hcp1'; tauto.
               2: destruct Hcp2' as (_ & Hcp2'); apply senv_app in Hcp2'; destruct Hcp2' as (_ & _ & Hcp2'); specialize (Hcp2' z); tauto.
               2: rewrite negb_eqb_true_iff; intros Heq; subst z; rewrite map_app, in_app_iff in Hcp2'; tauto.
               cbn in i; cbn.

               intros _ Hin Hneq.
               rewrite Permutation_app_swap_app in Hin.
               rewrite map_app, in_app_iff in Hin.
               rewrite app_assoc, in_app_iff, <- map_app.
               destruct Hin as [Hin | [Hin | Hin]].
               1: auto.
               2: right; left; auto.
               right; right.
               apply IHHcp1; auto.
               1: right; rewrite map_app, in_app_iff; auto.
               1: right; rewrite map_app, in_app_iff; auto.

            -- (* Case 4: s in delta2 *)
               match goal with |- context[if ?p then _ else _] => destruct p end.
               ++ rewrite <- (proc_channels_perm _ _ Hcp2) in i.
                  cbn in i.
                  rewrite eqb_refl in i; cbn in i.
                  destruct (in_dec eq_dec x (map fst gamma)).
                  1: rewrite map_app, in_app_iff in Hcp2'; tauto.

                  rewrite <- (proc_channels_perm _ _ Hcp1); cbn.
                  rewrite eqb_refl; cbn.
                  destruct (in_dec eq_dec y (map fst gamma)).
                  1: rewrite map_app, in_app_iff in Hcp1'; tauto.

                  rewrite map_app, filter_app in i.
                  rewrite (map_app fst gamma delta1), filter_app.
                  rewrite forallb_filter_nil in i.
                  1: rewrite forallb_filter_id in i.
                  1: rewrite forallb_filter_nil.
                  1: rewrite forallb_filter_id.
                  2,3,4,5: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
                  2: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' z); tauto.
                  2: rewrite negb_eqb_true_iff; intros Heq; subst z; rewrite map_app, in_app_iff in Hcp1'; tauto.
                  2: destruct Hcp2' as (_ & Hcp2'); apply senv_app in Hcp2'; destruct Hcp2' as (_ & _ & Hcp2'); specialize (Hcp2' z); tauto.
                  2: rewrite negb_eqb_true_iff; intros Heq; subst z; rewrite map_app, in_app_iff in Hcp2'; tauto.
                  cbn in i; cbn.

                  intros _ Hin Hneq.
                  rewrite app_assoc in Hin.
                  rewrite map_app, in_app_iff in Hin.
                  rewrite app_assoc, in_app_iff, <- map_app.
                  destruct Hin as [Hin | [Hin | Hin]].
                  1: subst t; specialize (IHHcp2 s x ltac:(cbn; right; rewrite map_app, in_app_iff; auto) ltac:(cbn; left; auto) Hneq); auto.
                  1: left; auto.
                  right.
                  apply IHHcp2; auto.
                  1: right; rewrite map_app, in_app_iff; auto.
                  1: right; rewrite map_app, in_app_iff; auto.

               ++ (* Case 5: s not a channel *)
                  intros Hin _ _.
                  destruct Hin as [Hin | Hin]; [tauto|].
                  rewrite <- (proc_channels_perm _ _ Hcp1) in n1.
                  rewrite <- (proc_channels_perm _ _ Hcp2) in n2.
                  cbn in n1, n2.
                  rewrite eqb_refl in n1, n2; cbn in n1, n2.
                  rewrite map_app, in_app_iff in Hcp1', Hcp2'.
                  destruct (in_dec eq_dec y (map fst gamma)); [tauto|].
                  destruct (in_dec eq_dec x (map fst gamma)); [tauto|].
                  rewrite map_app, filter_app in n1, n2.
                  rewrite forallb_filter_nil in n1, n2.
                  1: rewrite forallb_filter_id in n1, n2.
                  2,3,4,5: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
                  2: destruct Hcp2' as (_ & Hcp2'); apply senv_app in Hcp2'; destruct Hcp2' as (_ & _ & Hcp2'); specialize (Hcp2' z); tauto.
                  3: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' z); tauto.
                  2,3: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
                  cbn in n1, n2.
                  do 2 rewrite map_app, in_app_iff in Hin.
                  tauto.

    - (* Proc_InCh *)
      cbn; intros s t.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      repeat rewrite senv_valid_cons in Hcp'.
      cbn in Hcp'.

      (* Case 1: s = y *)
      destruct (eqb_spec y s).
      + subst s.
        intros Hin.
        destruct Hin as [Hin | Hin]; [|tauto].
        subst y; tauto.

      (* Case 2: s = x or s in gamma *)
      + intros Hin Hin' Hneq.
        apply (IHHcp s t ltac:(cbn; clear IHHcp; tauto) ltac:(cbn; clear IHHcp; tauto) Hneq).

    - (* Proc_OutLeft *)
      cbn; auto.
    - (* Proc_OutRight *)
      cbn; auto.
    - (* Proc_InCase *)
      cbn; intros s t Hin Hin' Hneq.
      cbn in IHHcp1.
      specialize (IHHcp1 s t Hin Hin' Hneq).
      rewrite in_app_iff; auto.

    - (* Proc_Server *)
      cbn; intros s t.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      rewrite senv_valid_cons in Hcp'.

      (* Case 1: s = x *)
      intros Hin.
      destruct Hin as [Hin | Hin].
      + subst s.
        intros Hin' Hneq.
        destruct Hin' as [? | Hin']; [contradiction|].

        (* Simplify goal *)
        rewrite eqb_refl.
        rewrite filter_In.
        rewrite <- (cp_channels _ _ _ Hcp).
        rewrite negb_eqb_true_iff; cbn.

        split; auto.
        intros Heq; subst t.
        tauto.

      + destruct (eqb_spec x s).
        1: subst s; contradiction.

        (* Case 2: s in gamma *)
        match goal with |- context[if ?p then _ else _] => destruct p end.
        * clear i.
          intros Hin' Hneq.
          destruct Hin' as [Hin' | Hin'].
          1: left; auto.
          right.
          apply (IHHcp s t ltac:(cbn; right; auto) ltac:(cbn; right; auto) Hneq).

        * rewrite filter_In in n0.
          rewrite negb_eqb_true_iff in n0.
          rewrite <- (cp_channels _ _ _ Hcp) in n0.
          cbn in n0.
          apply list_nin_helper in n0.
          2: tauto.
          contradiction.

    - (* Proc_Server *)
      cbn; intros s t.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      rewrite senv_valid_cons in Hcp'.

      (* Case 1: s = x *)
      intros Hin.
      destruct Hin as [Hin | Hin].
      + subst s.
        intros Hin' Hneq.
        destruct Hin' as [? | Hin']; [contradiction|].

        (* Simplify goal *)
        rewrite eqb_refl.
        rewrite filter_In.
        rewrite <- (cp_channels _ _ _ Hcp).
        rewrite negb_eqb_true_iff; cbn.

        split; auto.
        intros Heq; subst t.
        tauto.

      + destruct (eqb_spec x s).
        1: subst s; contradiction.

        (* Case 2: s in gamma *)
        match goal with |- context[if ?p then _ else _] => destruct p end.
        * clear i.
          intros Hin' Hneq.
          destruct Hin' as [Hin' | Hin'].
          1: left; auto.
          right.
          apply (IHHcp s t ltac:(cbn; right; auto) ltac:(cbn; right; auto) Hneq).

        * rewrite filter_In in n0.
          rewrite negb_eqb_true_iff in n0.
          rewrite <- (cp_channels _ _ _ Hcp) in n0.
          cbn in n0.
          apply list_nin_helper in n0.
          2: tauto.
          contradiction.

    - (* Proc_Client Null *)
      cbn; intros s t.
      (* Case 1 : s = x *)
      destruct (eqb_spec x s).
      + subst s; intros _.
        intros Hin' Hneq.
        destruct Hin' as [? | Hin']; [contradiction|].
        rewrite <- (cp_channels _ _ _ Hcp); auto.

      + (* Case 2: s in gamma *)
        match goal with |- context[if ?p then _ else _] => destruct p end.
        * intros _ Hin Hneq.
          destruct Hin as [Hin | Hin].
          1: left; auto.
          right.
          rewrite <- (cp_channels _ _ _ Hcp) in i; auto.

        * rewrite <- (cp_channels _ _ _ Hcp) in n0.
          intros Hin; tauto.

    - (* Proc_ClientSplit *)
      cbn; intros s t.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      repeat rewrite senv_valid_cons in Hcp'; cbn in Hcp'.

      (* Case 1: s = y *)
      destruct (eqb_spec y s).
      + subst s.
        intros Hin; clear IHHcp; destruct Hin as [Hin | Hin]; [symmetry in Hin|]; tauto.

      + (* Case 2: s = x or s in gamma *)
        clear n.
        intros Hin Hin' Hneq.
        apply (IHHcp s t ltac:(cbn; clear IHHcp; tauto) ltac:(cbn; clear IHHcp; tauto) Hneq).

    - (* Proc_CompAndSplit *)
      cbn; intros s t Hin Hin' Hneq.
      (* x not in gamma, delta1, delta2 *)
      apply cp_senv_valid in Hcp1 as Hcp1'.
      apply cp_senv_valid in Hcp2 as Hcp2'.
      rewrite senv_valid_cons in Hcp1', Hcp2'.
      rewrite map_app, in_app_iff in Hcp1', Hcp2'.

      do 2 rewrite map_app in Hin, Hin'.
      do 2 rewrite in_app_iff in Hin, Hin'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      1: subst s; tauto.

      (* Case 2: s in gamma *)
      destruct (in_dec eq_dec s (map fst gamma)).
      + cbn.
        rewrite <- or_assoc in Hin'.
        destruct Hin' as [Hin' | Hin'].
        * specialize (IHHcp1 s t ltac:(cbn; right; rewrite map_app, in_app_iff; auto) ltac:(cbn; right; rewrite map_app, in_app_iff; auto) Hneq).
          rewrite in_app_iff; auto.
        * specialize (IHHcp2 s t ltac:(cbn; right; rewrite map_app, in_app_iff; auto) ltac:(cbn; right; rewrite map_app, in_app_iff; auto) Hneq).
          rewrite in_app_iff; auto.

      + (* Case 3: s in delta1 *)
        match goal with |- context[if ?p then _ else _] => destruct p end.
        * cbn.
          rewrite in_app_iff.
          rewrite filter_In.
          rewrite <- (cp_channels _ _ _ Hcp2); cbn.
          rewrite map_app, in_app_iff.
          (* rewrite (or_comm (In t (map fst delta1))) in Hin'. *)
          rewrite <- or_assoc in Hin'.

          (* Simplify i *)
          rewrite filter_In in i.
          rewrite <- (cp_channels _ _ _ Hcp1) in i; cbn in i.
          rewrite map_app, in_app_iff in i.

          destruct Hin' as [Hin' | Hin'].
          -- specialize (IHHcp1 s t ltac:(cbn; right; rewrite map_app, in_app_iff; tauto) ltac:(cbn; right; rewrite map_app, in_app_iff; tauto) Hneq).
             tauto.
          -- destruct Hcp2' as (_ & Hcp2').
             apply senv_app in Hcp2'.
             destruct Hcp2' as (_ & _ & Hcp2').
             unfold senv_disjoint in Hcp2'.
             assert (~ In t (map fst gamma)) by (clear IHHcp1 IHHcp2; firstorder).
             destruct (in_dec eq_dec t (map fst gamma)); tauto.

        * (* Case 4: s in delta 2 *)
          match goal with |- context[if ?p then _ else _] => destruct p end.
          -- cbn.
             rewrite in_app_iff.
             rewrite filter_In.
             rewrite <- (cp_channels _ _ _ Hcp1); cbn.
             rewrite map_app, in_app_iff.
             rewrite (or_comm (In t (map fst delta1))) in Hin'.
             rewrite <- or_assoc in Hin'.

             (* Simplify i *)
             rewrite filter_In in i.
             rewrite <- (cp_channels _ _ _ Hcp2) in i; cbn in i.
             rewrite map_app, in_app_iff in i.

             destruct Hin' as [Hin' | Hin'].
             ++ specialize (IHHcp2 s t ltac:(cbn; right; rewrite map_app, in_app_iff; tauto) ltac:(cbn; right; rewrite map_app, in_app_iff; tauto) Hneq).
                tauto.
             ++ destruct Hcp1' as (_ & Hcp1').
             apply senv_app in Hcp1'.
             destruct Hcp1' as (_ & _ & Hcp1').
             unfold senv_disjoint in Hcp1'.
             assert (~ In t (map fst gamma)) by (clear IHHcp1 IHHcp2; firstorder).
             destruct (in_dec eq_dec t (map fst gamma)); tauto.

          -- (* Case 5 : s not a channel *)
             rewrite filter_In in n1, n2.
             destruct (in_dec eq_dec s (map fst gamma)); try contradiction.
             rewrite <- (cp_channels _ _ _ Hcp1) in n1.
             rewrite <- (cp_channels _ _ _ Hcp2) in n2.
             cbn in n1, n2.
             rewrite map_app, in_app_iff in n1, n2.
             tauto.

    - (* Proc_OutTyp *)
      cbn; auto.
    - (* Proc_InTyp *)
      cbn; auto.

    - (* Proc_OutUnit *)
      cbn; intros s t H1 H2.
      destruct H1; destruct H2; try contradiction; subst s t; contradiction.

    - (* Proc_InUnit *)
      cbn; intros s t.
      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        intros _ Hin Hneq.
        destruct Hin as [Hin | Hin]; [contradiction|].
        rewrite <- (cp_channels _ _ _ Hcp); auto.

      + (* Case 2: s in gamma *)
        intros Hin.
        destruct Hin as [Hin | Hin]; [contradiction|].
        match goal with |- context[if ?p then _ else _] => destruct p end.
        2: rewrite <- (cp_channels _ _ _ Hcp) in n0; contradiction.
        clear i.
        intros Hin' Hneq.
        destruct Hin' as [Hin' | Hin'].
        1: left; auto.
        right; apply IHHcp; auto.

    - (* Proc_EmptyCase *)
      intros s t.
      unfold proc_forbidden.
      cbn [map fst].
      match goal with |- context[if ?p then _ else _] => destruct p end.
      2: contradiction.
      intros _ Hin Hneq.
      auto.

    - (* Permutation *)
      intros s t Hin1 Hin2 Hneq.
      rewrite <- H in Hin1, Hin2.
      auto.
  Qed.

  (* Replace channel name s with t *)
  (* If s is a channel of p, then we assume ~ In t (proc_forbidden p s) *)
  (* If s is not a channel of p, leave p unchanged *)
  Fixpoint proc_rename (p : Process) (s : chn) (t : chn) :=
  match p with
  | Proc_Const c l => Proc_Const c (str_list_repl l s t)
  | Proc_Link x y => Proc_Link (if eqb x s then t else x) (if eqb y s then t else y)
  | Proc_Comp x a p q => if eqb x s then Proc_Comp x a p q else Proc_Comp x a (proc_rename p s t) (proc_rename q s t)
  | Proc_OutCh x y p q => if eqb x s then Proc_OutCh t y p (proc_rename q s t) else if eqb y s then Proc_OutCh x y p (proc_rename q s t) else Proc_OutCh x y (proc_rename p s t) (proc_rename q s t)
  | Proc_OutChAndSplit x y l p q => if eqb x s then Proc_OutChAndSplit t y l p (proc_rename q s t) else if eqb y s then Proc_OutChAndSplit x y (str_list_repl l s t) p (proc_rename q s t) else Proc_OutChAndSplit x y (str_list_repl l s t) (proc_rename p s t) (proc_rename q s t)
  | Proc_InCh x y p => if eqb y s then Proc_InCh x y p else if eqb x s then Proc_InCh t y (proc_rename p s t) else Proc_InCh x y (proc_rename p s t)
  | Proc_OutLeft x p => Proc_OutLeft (if eqb x s then t else x) (proc_rename p s t)
  | Proc_OutRight x p => Proc_OutRight (if eqb x s then t else x) (proc_rename p s t)
  | Proc_InCase x p q => Proc_InCase (if eqb x s then t else x) (proc_rename p s t) (proc_rename q s t)
  | Proc_Server x y p => if eqb x s then Proc_Server t y p else if eqb y s then Proc_Server x y p else Proc_Server x y (proc_rename p s t)
  | Proc_Client x y p => if eqb x s then Proc_Client t y p else if eqb y s then Proc_Client x y p else Proc_Client x y (proc_rename p s t)
  | Proc_ClientNull x p => if eqb x s then Proc_ClientNull t p else Proc_ClientNull x (proc_rename p s t)
  | Proc_ClientSplit x y p => if eqb y s then Proc_ClientSplit x y p else if eqb x s then Proc_ClientSplit t y (proc_rename p s t) else Proc_ClientSplit x y (proc_rename p s t)
  | Proc_CompAndSplit x a l p q => if eqb x s then Proc_CompAndSplit x a l p q else Proc_CompAndSplit x a (str_list_repl l s t) (proc_rename p s t) (proc_rename q s t)
  | Proc_OutTyp x a v b p => if eqb x s then Proc_OutTyp t a v b (proc_rename p s t) else Proc_OutTyp x a v b (proc_rename p s t)
  | Proc_InTyp x v b p => if eqb x s then Proc_InTyp t v b (proc_rename p s t) else Proc_InTyp x v b (proc_rename p s t)
  | Proc_OutUnit x => if eqb x s then Proc_OutUnit t else Proc_OutUnit x
  | Proc_InUnit x p => if eqb x s then Proc_InUnit t p else Proc_InUnit x (proc_rename p s t)
  | Proc_EmptyCase x l => if eqb x s then Proc_EmptyCase t l else Proc_EmptyCase x (str_list_repl l s t)
  end.

  Lemma proc_rename_ident : forall p s, proc_rename p s s = p.
  Proof.
    intros p s.
    induction p.
    all: cbn; repeat match goal with |- context[eqb ?x ?y] => destruct (eqb_spec x y); try subst end; try congruence.
    all: rewrite str_list_repl_ident; auto; congruence.
  Qed.

  Lemma cp_proc_rename :
  forall p s t gamma,
  cp p gamma ->
  ~ In t (proc_forbidden p s) ->
  In s (map fst gamma) /\ cp (proc_rename p s t) (senv_rename gamma s t) \/
  ~ In s (map fst gamma) /\ proc_rename p s t = p.
  Proof.
    intros p s t gamma Hcp.
    (* We first handle the case where s = t. In this case the process remains unchanged *)
    destruct (eq_dec s t).
    1: { intros _; subst t.
         rewrite proc_rename_ident.
         rewrite senv_rename_ident.
         destruct (in_dec eq_dec s (map fst gamma)).
         - left; split; auto.
         - right; split; auto.
    }

    (* Now the difficult part *)
    revert s t n.
    induction Hcp.
    - (* Proc_Const *)
      cbn; intros s t Hneq Hallow.
      rewrite combine_map_fst; auto.
      destruct (in_dec eq_dec s l).
      + left; split; auto.
        unfold senv_rename.
        erewrite combine_map.
        Unshelve.
        4: exact (fun x => if eqb x s then t else x).
        4: exact id.
        2: intros z; destruct z; cbn; destruct (eqb t0 s); auto.
        2: intros z; destruct z; cbn; destruct (eqb t0 s); auto.
        fold (str_list_repl l s t).
        constructor.
        2,3: rewrite map_id; auto.
        2: unfold str_list_repl; rewrite length_map; auto.
        apply str_list_repl_nodup; auto.
      + right; split; auto.
        rewrite str_list_repl_nin; auto.

    - (* Proc_Link *)
      cbn; intros s t Hneq Hallow.
      (* Case 1: s = w *)
      destruct (eqb_spec w s).
      + subst s.
        replace (eqb x w) with false.
        2: symmetry; rewrite eqb_neq; auto.
        cbn in Hallow.
        left; split; auto.
        constructor; firstorder.

      + (* Case 2: s = x *)
        destruct (eqb_spec x s).
        * subst s.
          left; split; auto.
          constructor; firstorder.
        * right; split; auto; tauto.

    - (* Proc_Comp *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp1 as Hcp1'.
      apply cp_senv_valid in Hcp2 as Hcp2'.
      rewrite senv_valid_cons in Hcp1', Hcp2'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        right; split; auto.
        rewrite map_app; rewrite in_app_iff.
        tauto.

      + (* Case 2: s in gamma *)
        match type of Hallow with context[if ?p then _ else _] => destruct p end.
        * (* s in gamma *)
          rewrite filter_In in i.
          destruct i as (i & _).
          rewrite <- cp_channels in i.
          2: apply Hcp1.
          cbn in i.
          destruct i as [? | i]; [contradiction|].

          (* s in gamma -> s not in delta *)
          unfold senv_disjoint in H.
          specialize (H _ i) as i'.

          (* Simplify Hallow *)
          rewrite in_app_iff in Hallow.
          rewrite filter_In in Hallow.
          rewrite Bool.negb_true_iff in Hallow.
          rewrite eqb_neq in Hallow.
          rewrite <- (cp_channels _ _ _ Hcp2) in Hallow.
          cbn in Hallow.

          (* Simplify IHHcp1 *)
          specialize (IHHcp1 s t Hneq ltac:(tauto)).
          cbn [map fst] in IHHcp1.
          destruct IHHcp1 as [(_ & IHHcp1) | ?]; [|firstorder].
          cbn in IHHcp1; fold (senv_rename gamma s t) in IHHcp1.
          replace (eqb x s) with false in IHHcp1 by (symmetry; rewrite eqb_neq; auto).

          (* Simplify IHHcp2 *)
          specialize (IHHcp2 s t Hneq).
          erewrite proc_forbidden_empty in IHHcp2.
          2: apply Hcp2.
          2: cbn; tauto.
          specialize (IHHcp2 ltac:(auto)).
          cbn [map fst] in IHHcp2.
          destruct IHHcp2 as [? | (_ & IHHcp2)]; [firstorder|].

          left; split.
          1: rewrite map_app; rewrite in_app_iff; left; auto.
          rewrite IHHcp2.
          rewrite senv_rename_app.
          rewrite (senv_rename_nin delta); auto.
          constructor; auto.

          (* disjointness *)
          unfold senv_disjoint.
          intros m Hin.
          unfold senv_rename in Hin.
          rewrite map_map in Hin.
          rewrite in_map_iff in Hin.
          destruct Hin as (z & Hz1 & Hz2).
          destruct z.
          destruct (eqb_spec t0 s); cbn in Hz1; subst m.
          -- subst t0.
             intros Hin; apply Hallow; right.
             split; [tauto|].
             intros Heq; subst t; tauto.
          -- apply H.
             rewrite in_map_iff; eexists; split; try apply Hz2; auto.

        * rewrite filter_In in n0.
          rewrite negb_eqb_true_iff in n0.
          rewrite <- (cp_channels _ _ _ Hcp1) in n0.
          cbn in n0.
          assert (n0' : ~ In s (map fst gamma)) by tauto.

          (* Case 3: s in delta *)
          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          -- rewrite filter_In in i.
             destruct i as (i & _).
             rewrite <- cp_channels in i.
             2: apply Hcp2.
             cbn in i.
             destruct i as [? | i]; [contradiction|].

             (* Simplify Hallow *)
             rewrite in_app_iff in Hallow.
             rewrite filter_In in Hallow.
             rewrite Bool.negb_true_iff in Hallow.
             rewrite eqb_neq in Hallow.
             rewrite <- (cp_channels _ _ _ Hcp1) in Hallow.
             cbn in Hallow.

             (* Simplify IHHcp2 *)
             specialize (IHHcp2 s t Hneq ltac:(tauto)).
             cbn [map fst] in IHHcp2.
             destruct IHHcp2 as [(_ & IHHcp2) | ?]; [|firstorder].
             cbn in IHHcp2; fold (senv_rename delta s t) in IHHcp2.
             replace (eqb x s) with false in IHHcp2 by (symmetry; rewrite eqb_neq; auto).

             (* Simplify IHHcp1 *)
             specialize (IHHcp1 s t Hneq).
             erewrite proc_forbidden_empty in IHHcp1.
             2: apply Hcp1.
             2: cbn; tauto.
             specialize (IHHcp1 ltac:(auto)).
             cbn [map fst] in IHHcp1.
             destruct IHHcp1 as [? | (_ & IHHcp1)]; [tauto|].

             left; split.
             1: rewrite map_app; rewrite in_app_iff; right; auto.
             rewrite IHHcp1.
             rewrite senv_rename_app.
             rewrite (senv_rename_nin gamma); auto.
             constructor; auto.

             (* disjointness *)
             unfold senv_disjoint.
             intros m Hin.
             unfold senv_disjoint in H.
             specialize (H _ Hin) as Hm.
             unfold senv_rename.
             rewrite map_map.
             rewrite in_map_iff.
             intros Hin'.
             destruct Hin' as (z & Hz1 & Hz2).
             destruct z.
             destruct (eqb_spec t0 s); cbn in Hz1; subst m.
             ++ subst t0.
                apply Hallow; right.
                split; [auto|].
                intros Heq; subst t; tauto.
             ++ apply Hm; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

          -- (* Case 4: s not a channel *)
             rewrite filter_In in n1.
             rewrite Bool.negb_true_iff in n1.
             rewrite eqb_neq in n1.
             rewrite <- (cp_channels _ _ _ Hcp2) in n1.
             cbn in n1.
             assert (n1' : ~ In s (map fst delta)) by tauto.

             (* Simplify IHHcp1, IHHcp2 *)
             specialize (IHHcp1 s t Hneq).
             specialize (IHHcp2 s t Hneq).
             erewrite proc_forbidden_empty in IHHcp1, IHHcp2.
             2: apply Hcp2.
             3: apply Hcp1.
             2,3: cbn; tauto.
             specialize (IHHcp1 ltac:(auto)).
             specialize (IHHcp2 ltac:(auto)).
             cbn [map fst] in IHHcp1, IHHcp2.
             destruct IHHcp1 as [? | (_ & IHHcp1)]; [tauto|].
             destruct IHHcp2 as [? | (_ & IHHcp2)]; [tauto|].

             right; rewrite IHHcp1, IHHcp2; split; auto.
             rewrite map_app; rewrite in_app_iff; tauto.

    - (* Proc_OutCh *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp1 as Hcp1'.
      apply cp_senv_valid in Hcp2 as Hcp2'.
      rewrite senv_valid_cons in Hcp1', Hcp2'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.

        (* Simplify goal *)
        rewrite map_app.
        fold (senv_rename delta x t).
        rewrite senv_rename_nin; [|tauto].
        fold (senv_rename gamma x t).
        rewrite senv_rename_nin; auto.

        (* Simplify Hallow *)
        rewrite in_app_iff in Hallow.
        rewrite filter_In in Hallow.
        rewrite negb_eqb_true_iff in Hallow.
        rewrite <- (cp_channels _ _ _ Hcp1) in Hallow.
        cbn in Hallow.

        (* Simplify IHHcp2 *)
        specialize (IHHcp2 x t Hneq ltac:(tauto)).
        destruct IHHcp2 as [(_ & IHHcp2) | IHHcp2].
        2: cbn in IHHcp2; tauto.
        cbn in IHHcp2.
        rewrite eqb_refl in IHHcp2.
        fold (senv_rename delta x t) in IHHcp2.
        rewrite senv_rename_nin in IHHcp2; [|tauto].

        constructor; auto.
        intros Hin; apply Hallow; left; split; auto.
        intros Heq; subst t.
        tauto.

      + (* Case 2: s = y *)
        destruct (eqb_spec y s).
        * subst s.
          (* y cannot appear in gamma *)
          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          1: { rewrite filter_In in i.
               rewrite <- (cp_channels _ _ _ Hcp1) in i.
               rewrite eqb_refl in i.
               cbn in i; destruct i; discriminate.
          }

          clear n0.
          (* Case 2.1: y is part of delta *)
          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          -- rewrite filter_In in i.
             rewrite negb_eqb_true_iff in i.
             rewrite <- (cp_channels _ _ _ Hcp2) in i.
             cbn in i.
             assert (i' : In y (map fst delta)) by tauto.

             (* Simplify Hallow *)
             rewrite in_app_iff in Hallow.
             rewrite filter_In in Hallow.
             rewrite negb_eqb_true_iff in Hallow.
             rewrite <- (cp_channels _ _ _ Hcp1) in Hallow.
             cbn in Hallow.

             (* Simplify goal *)
             left; split.
             1: right; rewrite map_app; rewrite in_app_iff; right; auto.
             rewrite map_app.
             fold (senv_rename gamma y t).
             rewrite senv_rename_nin; [|tauto].
             fold (senv_rename delta y t).

             (* Simplify IHHcp2 *)
             specialize (IHHcp2 y t Hneq ltac:(tauto)).
             cbn in IHHcp2.
             replace (eqb x y) with false in IHHcp2; [|symmetry; rewrite eqb_neq; auto].
             fold (senv_rename delta y t) in IHHcp2.
             destruct IHHcp2 as [(_ & IHHcp2) | (IHHcp2 & _)].
             2: tauto.

             constructor; auto.

             (* disjointness *)
             unfold senv_disjoint.
             intros m Hm.
             unfold senv_rename; rewrite map_map.
             rewrite in_map_iff.
             intros Hin.
             destruct Hin as (z & Hz1 & Hz2).
             destruct z.
             destruct (eqb_spec t0 y); cbn in Hz1; subst m.
             ++ subst t0.
                tauto.
             ++ unfold senv_disjoint in H0.
                specialize (H0 _ Hm).
                apply H0; rewrite in_map_iff.
                eexists; split; try apply Hz2; auto.

          -- (* Case 2.2: y not in delta *)
             rewrite filter_In in n0.
             rewrite <- (cp_channels _ _ _ Hcp2) in n0.
             cbn in n0.
             rewrite negb_eqb_true_iff in n0.
             assert (n0' : ~ In y (map fst delta)) by tauto.

             (* Simplify IHHcp2 *)
             specialize (IHHcp2 y t Hneq).
             erewrite proc_forbidden_empty in IHHcp2.
             2: apply Hcp2.
             2: cbn; tauto.
             specialize (IHHcp2 ltac:(auto)).
             destruct IHHcp2 as [(IHHcp2 & _) | (_ & IHHcp2')].
             1: cbn in IHHcp2; tauto.

             right; split.
             1: rewrite map_app; rewrite in_app_iff; tauto.
             rewrite IHHcp2'; auto.

        * (* Case 3: s in gamma *)
          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          -- rewrite filter_In in i.
             rewrite negb_eqb_true_iff in i.
             rewrite <- (cp_channels _ _ _ Hcp1) in i.
             cbn in i.
             assert (i' : In s (map fst gamma)) by tauto.

             (* s not in delta *)
             unfold senv_disjoint in H0.
             specialize (H0 _ i') as i''.

             left; split.
             1: right; rewrite map_app; rewrite in_app_iff; auto.

             (* Simplify goal *)
             rewrite map_app.
             fold (senv_rename gamma s t).
             fold (senv_rename delta s t).
             rewrite (senv_rename_nin delta s t); auto.

             (* Simplify IHHcp2 *)
             specialize (IHHcp2 s t Hneq).
             erewrite proc_forbidden_empty in IHHcp2.
             2: apply Hcp2.
             2: cbn; tauto.
             specialize (IHHcp2 ltac:(auto)).
             destruct IHHcp2 as [(IHHcp2 & _) | (_ & IHHcp2')].
             1: cbn in IHHcp2; tauto.
             rewrite IHHcp2'.

             (* Simplify Hallow *)
             cbn in Hallow.
             rewrite in_app_iff in Hallow.
             rewrite filter_In in Hallow.
             rewrite <- (cp_channels _ _ _ Hcp2) in Hallow.
             rewrite negb_eqb_true_iff in Hallow.
             cbn in Hallow.

             (* Simplify IHHcp1 *)
             specialize (IHHcp1 s t Hneq ltac:(tauto)).
             destruct IHHcp1 as [(_ & IHHcp1) | (IHHcp1 & _)].
             2: cbn in IHHcp1; tauto.
             cbn in IHHcp1.
             replace (eqb y s) with false in IHHcp1 by (symmetry; rewrite eqb_neq; auto).
             fold (senv_rename gamma s t) in IHHcp1.

             constructor; auto.
             ++ (* x not in new gamma *)
                unfold senv_rename; rewrite map_map.
                rewrite in_map_iff.
                intros Hin.
                destruct Hin as (z & Hz1 & Hz2).
                destruct z.
                destruct (eqb_spec t0 s); cbn in Hz1.
                ** subst t0 t.
                   apply Hallow; auto.
                ** subst t0.
                   apply H; apply in_map_iff; eexists; split; try apply Hz2; auto.

             ++ (* disjointness *)
                unfold senv_disjoint.
                intros m Hm.
                unfold senv_rename in Hm; rewrite map_map in Hm.
                rewrite in_map_iff in Hm.
                destruct Hm as (z & Hz1 & Hz2).
                destruct z.
                destruct (eqb_spec t0 s); cbn in Hz1.
                ** subst t0 m.
                   intros Hin; apply Hallow; right; right.
                   tauto.
                ** subst t0.
                   apply H0; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

          -- (* Case 4: s in delta, symmetric to case 3 *)
             match type of Hallow with context[if ?p then _ else _] => destruct p end.
             ++ rewrite filter_In in i.
                rewrite negb_eqb_true_iff in i.
                rewrite <- (cp_channels _ _ _ Hcp2) in i.
                cbn in i.
                assert (i' : In s (map fst delta)) by tauto.

                (* s not in gamma *)
                unfold senv_disjoint in H0.
                assert (H0' : ~ In s (map fst gamma)).
                { intros Hin; apply (H0 _ Hin i'). }

                left; split.
                1: right; rewrite map_app; rewrite in_app_iff; auto.

                (* Simplify goal *)
                rewrite map_app.
                fold (senv_rename gamma s t).
                fold (senv_rename delta s t).
                rewrite (senv_rename_nin gamma s t); auto.

                (* Simplify IHHcp1 *)
                specialize (IHHcp1 s t Hneq).
                erewrite proc_forbidden_empty in IHHcp1.
                2: apply Hcp1.
                2: cbn; tauto.
                specialize (IHHcp1 ltac:(auto)).
                destruct IHHcp1 as [(IHHcp1 & _) | (_ & IHHcp1')].
                1: cbn in IHHcp1; tauto.
                rewrite IHHcp1'.

                (* Simplify Hallow *)
                cbn in Hallow.
                rewrite in_app_iff in Hallow.
                rewrite filter_In in Hallow.
                rewrite <- (cp_channels _ _ _ Hcp1) in Hallow.
                rewrite negb_eqb_true_iff in Hallow.
                cbn in Hallow.

                (* Simplify IHHcp2 *)
                specialize (IHHcp2 s t Hneq ltac:(tauto)).
                destruct IHHcp2 as [(_ & IHHcp2) | (IHHcp2 & _)].
                2: cbn in IHHcp2; tauto.
                cbn in IHHcp2.
                replace (eqb x s) with false in IHHcp2 by (symmetry; rewrite eqb_neq; auto).
                fold (senv_rename delta s t) in IHHcp2.

                constructor; auto.

                (* disjointness *)
                unfold senv_disjoint.
                intros m Hm.
                unfold senv_rename; rewrite map_map.
                rewrite in_map_iff.
                intros Hin.
                destruct Hin as (z & Hz1 & Hz2).
                destruct z.
                destruct (eqb_spec t0 s); cbn in Hz1.
                ** subst t0 m.
                   apply Hallow; right; split; auto.
                   intros Heq; subst t.
                   tauto.
                ** subst m.
                   apply (H0 t0); auto; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

             ++ (* Case 5: s not a channel *)
                rewrite filter_In in n1, n2.
                rewrite negb_eqb_true_iff in n1, n2.
                rewrite <- (cp_channels _ _ _ Hcp1) in n1.
                rewrite <- (cp_channels _ _ _ Hcp2) in n2.
                cbn in n1, n2.
                assert (n1' : ~ In s (map fst gamma)) by tauto.
                assert (n2' : ~ In s (map fst delta)) by tauto.

                right; split.
                1: rewrite map_app, in_app_iff; tauto.

                (* Simplify IHHcp1, IHHcp2 *)
                specialize (IHHcp1 s t Hneq).
                specialize (IHHcp2 s t Hneq).
                erewrite proc_forbidden_empty in IHHcp1, IHHcp2.
                2: apply Hcp2.
                3: apply Hcp1.
                2,3: cbn; tauto.
                specialize (IHHcp1 ltac:(auto)).
                specialize (IHHcp2 ltac:(auto)).
                destruct IHHcp1 as [(IHHcp1 & _) | (_ & IHHcp1)].
                1: tauto.
                destruct IHHcp2 as [(IHHcp2 & _) | (_ & IHHcp2)].
                1: tauto.

                rewrite IHHcp1, IHHcp2; auto.

    - (* Proc_OutChAndSplit *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp1 as Hcp1'.
      apply cp_senv_valid in Hcp2 as Hcp2'.
      rewrite senv_valid_cons in Hcp1', Hcp2'.
      rewrite map_app, in_app_iff in Hcp1', Hcp2'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.

        do 2 rewrite map_app.
        fold (senv_rename gamma x t).
        rewrite senv_rename_nin; [|tauto].
        fold (senv_rename delta1 x t).
        rewrite senv_rename_nin; [|auto].
        fold (senv_rename delta2 x t).
        rewrite senv_rename_nin; [|tauto].

        (* Simplify Hallow *)
        do 2 rewrite in_app_iff in Hallow.
        rewrite filter_In in Hallow.
        rewrite <- (proc_channels_perm _ _ Hcp1) in Hallow.
        cbn in Hallow.
        assert (Hallow' : ~ In t (map fst delta1)).
        { intros Hin; apply Hallow.
          right; left; split.
          1: rewrite map_app, in_app_iff; auto.
          destruct (in_dec eq_dec t (map fst gamma)).
          1: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' t); tauto.
          rewrite negb_eqb_true_iff; intros Heq; subst t; tauto.
        }

        specialize (IHHcp2 x t Hneq ltac:(tauto)).
        cbn in IHHcp2.
        destruct IHHcp2 as [(_ & IHHcp2) | (IHHcp2 & _)]; [|tauto].
        rewrite eqb_refl in IHHcp2.
        rewrite map_app in IHHcp2.
        fold (senv_rename gamma x t) in IHHcp2.
        fold (senv_rename delta2 x t) in IHHcp2.
        do 2 (rewrite senv_rename_nin in IHHcp2; [|tauto]).

        constructor; auto.

      + (* Case 2: s = y *)
        destruct (eqb_spec y s).
        * subst s.
          (* y cannot appear in gamma or delta1 *)
          rewrite str_list_repl_nin; [|tauto].
          destruct (in_dec eq_dec y (map fst gamma)); [tauto|].
          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          1: { rewrite <- (proc_channels_perm _ _ Hcp1) in i.
               cbn in i.
               rewrite eqb_refl in i; cbn in i.
               destruct (in_dec eq_dec y (map fst gamma)); [tauto|].
               rewrite map_app, filter_app in i.
               rewrite forallb_filter_nil in i.
               1: rewrite forallb_filter_id in i.
               2,3: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
               2: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' z); tauto.
               2: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
               cbn in i; tauto.
          }

          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          -- (* Case 2.1: y in delta2 *)
             rewrite <- (proc_channels_perm _ _ Hcp2) in i.
             cbn in i.
             rewrite eqb_refl in i; cbn in i.
             destruct (in_dec eq_dec x (map fst gamma)); [tauto|].
             rewrite map_app, filter_app in i.
             rewrite forallb_filter_nil in i.
             1: rewrite forallb_filter_id in i.
             2,3: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
             2: destruct Hcp2' as (_ & Hcp2'); apply senv_app in Hcp2'; destruct Hcp2' as (_ & _ & Hcp2'); specialize (Hcp2' z); tauto.
             2: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
             cbn in i.

             left; split.
             1: right; do 2 rewrite map_app, in_app_iff; auto.
             rewrite app_assoc.
             rewrite map_app.
             fold (senv_rename (gamma ++ delta1) y t).
             rewrite senv_rename_nin.
             2: rewrite map_app, in_app_iff; tauto.
             fold (senv_rename delta2 y t).

             do 2 rewrite in_app_iff in Hallow.
             specialize (IHHcp2 y t Hneq ltac:(tauto)).
             cbn in IHHcp2.
             destruct (eqb_spec x y); [tauto|].
             rewrite map_app, in_app_iff in IHHcp2.
             destruct IHHcp2 as [(_ & IHHcp2) | (IHHcp2 & _)]; [|tauto].
             rewrite map_app in IHHcp2.
             fold (senv_rename gamma y t) in IHHcp2.
             rewrite senv_rename_nin in IHHcp2; [|tauto].
             fold (senv_rename delta2 y t) in IHHcp2.

             rewrite <- app_assoc.
             constructor; auto.

             (* disjointness *)
             assert (Hallow' : ~ In t (map fst delta1)).
             { intros Hin; apply Hallow.
               right; left.
               rewrite <- (proc_channels_perm _ _ Hcp1); cbn.
               destruct (in_dec eq_dec y (map fst gamma)); [tauto|].
               rewrite eqb_refl; cbn.
               rewrite map_app, filter_app.
               rewrite forallb_filter_nil.
               1: rewrite forallb_filter_id.
               2,3: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
               2: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' z); tauto.
               2: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
               cbn; auto.
             }

             unfold senv_disjoint.
             intros z Hz1 Hz2.
             unfold senv_rename in Hz2.
             rewrite map_map in Hz2.
             rewrite in_map_iff in Hz2.
             destruct Hz2 as (w & Hw1 & Hw2); subst z.
             destruct w.
             destruct (eqb_spec t0 y); try subst y; cbn in Hz1.
             ++ contradiction.
             ++ unfold senv_disjoint in H1; specialize (H1 t0).
                apply (in_map fst) in Hw2; cbn in Hw2; tauto.

          -- (* Case 2.2: y not in delta2 *)
             rewrite <- (proc_channels_perm _ _ Hcp1) in n1.
             rewrite <- (proc_channels_perm _ _ Hcp2) in n2.
             cbn in n1, n2.
             rewrite eqb_refl in n1, n2; cbn in n1, n2.
             destruct (in_dec eq_dec x (map fst gamma)); [tauto|].
             destruct (in_dec eq_dec y (map fst gamma)); [tauto|].
             rewrite map_app, filter_app in n1, n2.
             rewrite forallb_filter_nil in n1, n2.
             1: rewrite forallb_filter_id in n1, n2.
             2,3,4,5: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
             2: destruct Hcp2' as (_ & Hcp2'); apply senv_app in Hcp2'; destruct Hcp2' as (_ & _ & Hcp2'); specialize (Hcp2' z); tauto.
             3: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' z); tauto.
             2,3: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
             cbn in n1, n2.

             right; split.
             1: do 2 rewrite map_app, in_app_iff; tauto.
             specialize (IHHcp2 y t Hneq).
             erewrite proc_forbidden_empty in IHHcp2.
             2: apply Hcp2.
             2: cbn; rewrite map_app, in_app_iff; tauto.
             specialize (IHHcp2 ltac:(auto)).
             cbn in IHHcp2.
             rewrite map_app, in_app_iff in IHHcp2.
             destruct IHHcp2 as [(IHHcp2 & _) | (_ & IHHcp2)]; [tauto|].
             rewrite IHHcp2; auto.

        * (* Case 3: s in gamma *)
          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          -- left; split.
             1: rewrite map_app, in_app_iff; auto.
             rewrite in_app_iff in Hallow.

             specialize (IHHcp1 s t Hneq ltac:(tauto)).
             specialize (IHHcp2 s t Hneq ltac:(tauto)).
             cbn in IHHcp1, IHHcp2.
             rewrite map_app, in_app_iff in IHHcp1, IHHcp2.
             destruct IHHcp1 as [(_ & IHHcp1) | (IHHcp1 & _)]; [|tauto].
             destruct IHHcp2 as [(_ & IHHcp2) | (IHHcp2 & _)]; [|tauto].
             rewrite map_app in IHHcp1, IHHcp2.
             fold (senv_rename gamma s t) in IHHcp1, IHHcp2.
             fold (senv_rename delta1 s t) in IHHcp1.
             fold (senv_rename delta2 s t) in IHHcp2.
             destruct (eqb_spec y s); [tauto|].
             destruct (eqb_spec x s); [tauto|].

             do 2 rewrite map_app.
             fold (senv_rename gamma s t).
             fold (senv_rename delta1 s t).
             fold (senv_rename delta2 s t).
             rewrite <- senv_rename_repl.
             constructor; auto.

             ++ (* ques *)
                unfold senv_rename; rewrite map_map.
                rewrite Forall_forall; rewrite Forall_forall in H.
                intros z Hz.
                rewrite in_map_iff in Hz.
                destruct Hz as (w & Hw1 & Hw2); subst z.
                destruct w.
                destruct (eqb t0 s); cbn;
                apply (H s0 ltac:(rewrite in_map_iff; eexists; split; try apply Hw2; auto)).

             ++ (* nodup *)
                assert (Hallow' : x <> t).
                { intros Heq; subst t.
                  apply Hallow; right.
                  eapply proc_forbidden_channel.
                  1: apply Hcp2.
                  3: auto.
                  2: left; auto.
                  cbn; right; rewrite map_app, in_app_iff; left; auto.
                }

                unfold senv_rename.
                rewrite map_map.
                rewrite in_map_iff; intros Hin.
                destruct Hin as (z & Hz1 & Hz2); subst x.
                destruct z.
                destruct (eqb_spec t0 s); try subst s.
                ** cbn in Hallow'; contradiction.
                ** cbn in H0; apply H0; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

             ++ (* disjointness *)
                destruct Hcp1' as (_ & Hcp1').
                destruct Hcp2' as (_ & Hcp2').
                apply senv_app in Hcp1', Hcp2'.
                destruct Hcp1' as (_ & _ & Hcp1').
                destruct Hcp2' as (_ & _ & Hcp2').
                specialize (Hcp1' s i).
                specialize (Hcp2' s i).
                do 2 (rewrite senv_rename_nin; auto).

          -- (* Case 4: s in delta1 *)
             match type of Hallow with context[if ?p then _ else _] => destruct p end.
             ++ rewrite <- (proc_channels_perm _ _ Hcp1) in i.
                cbn in i.
                rewrite eqb_refl in i; cbn in i.
                destruct (in_dec eq_dec y (map fst gamma)); [tauto|].
                rewrite map_app, filter_app in i.
                rewrite forallb_filter_nil in i.
                1: rewrite forallb_filter_id in i.
                2,3: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
                2: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' z); tauto.
                2: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
                cbn in i.

                assert (i' : ~ In s (map fst gamma)).
                { intros Hin.
                  destruct Hcp1' as (_ & Hcp1').
                  apply senv_app in Hcp1'.
                  destruct Hcp1' as (_ & _ & Hcp1').
                  specialize (Hcp1' x); tauto.
                }

                assert (i'' : ~ In s (map fst delta2)).
                { specialize (H1 s); tauto. }

                left; split.
                1: right; do 2 rewrite map_app, in_app_iff; auto.

                assert (Hallow' : ~ In t (map fst delta2)).
                { intros Hin; apply Hallow.
                  right; do 2 rewrite in_app_iff; right; left.
                  rewrite <- (proc_channels_perm _ _ Hcp2); cbn.
                  rewrite eqb_refl; cbn.
                  destruct (in_dec eq_dec x (map fst gamma)); [tauto|].
                  rewrite map_app, filter_app, in_app_iff; right.
                  rewrite filter_In; split; auto.
                  destruct (in_dec eq_dec t (map fst gamma)); auto.
                  1: destruct Hcp2' as (_ & Hcp2'); apply senv_app in Hcp2'; destruct Hcp2' as (_ & _ & Hcp2'); specialize (Hcp2' t); tauto.
                  rewrite negb_eqb_true_iff; intros Heq; subst t; tauto.
                }

                cbn in Hallow; do 2 rewrite in_app_iff in Hallow.
                specialize (IHHcp1 s t Hneq ltac:(tauto)).
                cbn in IHHcp1; rewrite map_app, in_app_iff in IHHcp1.
                destruct IHHcp1 as [(_ & IHHcp1) | (IHHcp1 & _)]; [|tauto].
                destruct (eqb_spec y s); [tauto|].
                rewrite map_app in IHHcp1.
                fold (senv_rename gamma s t) in IHHcp1.
                fold (senv_rename delta1 s t) in IHHcp1.
                rewrite senv_rename_nin in IHHcp1; auto.

                specialize (IHHcp2 s t Hneq).
                erewrite proc_forbidden_empty in IHHcp2.
                2: apply Hcp2.
                2: cbn; rewrite map_app, in_app_iff; tauto.
                specialize (IHHcp2 ltac:(auto)).
                cbn in IHHcp2; rewrite map_app, in_app_iff in IHHcp2.
                destruct IHHcp2 as [(IHHcp2 & _) | (_ & IHHcp2)]; [tauto|].

                rewrite IHHcp2.
                do 2 rewrite map_app.
                fold (senv_rename gamma s t); rewrite senv_rename_nin; auto.
                fold (senv_rename delta2 s t); rewrite senv_rename_nin; auto.
                fold (senv_rename delta1 s t).
                rewrite str_list_repl_nin; auto.
                constructor; auto.

                ** unfold senv_rename.
                   rewrite map_map.
                   rewrite in_map_iff; intros Hin.
                   destruct Hin as (z & Hz1 & Hz2); subst x.
                   destruct z.
                   destruct (eqb_spec t0 s); try subst s.
                   --- cbn in Hallow; tauto.
                   --- cbn in H0; apply H0; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

                ** unfold senv_disjoint.
                   intros z Hz1 Hz2.
                   unfold senv_rename in Hz1.
                   rewrite map_map in Hz1.
                   rewrite in_map_iff in Hz1.
                   destruct Hz1 as (w & Hw1 & Hw2); subst z.
                   destruct w.
                   destruct (eqb_spec t0 s); try subst s.
                   --- cbn in Hz2; contradiction.
                   --- cbn in Hz2.
                       specialize (H1 t0).
                       apply (in_map fst) in Hw2; tauto.

             ++ (* Case 5: s in delta2 *)
                match type of Hallow with context[if ?p then _ else _] => destruct p end.

                ** rewrite <- (proc_channels_perm _ _ Hcp2) in i.
                   cbn in i.
                   rewrite eqb_refl in i; cbn in i.
                   destruct (in_dec eq_dec x (map fst gamma)); [tauto|].
                   rewrite map_app, filter_app in i.
                   rewrite forallb_filter_nil in i.
                   1: rewrite forallb_filter_id in i.
                   2,3: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
                   2: destruct Hcp2' as (_ & Hcp2'); apply senv_app in Hcp2'; destruct Hcp2' as (_ & _ & Hcp2'); specialize (Hcp2' z); tauto.
                   2: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
                   cbn in i.

                   assert (i' : ~ In s (map fst gamma)).
                   { intros Hin.
                     destruct Hcp1' as (_ & Hcp1').
                     apply senv_app in Hcp1'.
                     destruct Hcp1' as (_ & _ & Hcp1').
                     specialize (Hcp1' x); tauto.
                   }

                   assert (i'' : ~ In s (map fst delta1)).
                   { specialize (H1 s); tauto. }

                   left; split.
                   1: right; do 2 rewrite map_app, in_app_iff; auto.

                   assert (Hallow' : ~ In t (map fst delta1)).
                   { intros Hin; apply Hallow.
                     do 2 rewrite in_app_iff; right; left.
                     rewrite <- (proc_channels_perm _ _ Hcp1); cbn.
                     rewrite eqb_refl; cbn.
                     destruct (in_dec eq_dec y (map fst gamma)); [tauto|].
                     rewrite map_app, filter_app, in_app_iff; right.
                     rewrite filter_In; split; auto.
                     destruct (in_dec eq_dec t (map fst gamma)); auto.
                     1: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' t); tauto.
                     rewrite negb_eqb_true_iff; intros Heq; subst t; tauto.
                   }

                   do 2 rewrite in_app_iff in Hallow.
                   specialize (IHHcp2 s t Hneq ltac:(tauto)).
                   cbn in IHHcp2; rewrite map_app, in_app_iff in IHHcp2.
                   destruct IHHcp2 as [(_ & IHHcp2) | (IHHcp2 & _)]; [|tauto].
                   destruct (eqb_spec x s); [tauto|].
                   rewrite map_app in IHHcp2.
                   fold (senv_rename gamma s t) in IHHcp2.
                   fold (senv_rename delta2 s t) in IHHcp2.
                   rewrite senv_rename_nin in IHHcp2; auto.

                   specialize (IHHcp1 s t Hneq).
                   erewrite proc_forbidden_empty in IHHcp1.
                   2: apply Hcp1.
                   2: cbn; rewrite map_app, in_app_iff; tauto.
                   specialize (IHHcp1 ltac:(auto)).
                   cbn in IHHcp1; rewrite map_app, in_app_iff in IHHcp1.
                   destruct IHHcp1 as [(IHHcp1 & _) | (_ & IHHcp1)]; [tauto|].

                   rewrite IHHcp1.
                   do 2 rewrite map_app.
                   fold (senv_rename gamma s t); rewrite senv_rename_nin; auto.
                   fold (senv_rename delta1 s t); rewrite senv_rename_nin; auto.
                   fold (senv_rename delta2 s t).
                   rewrite str_list_repl_nin; auto.
                   constructor; auto.

                   unfold senv_disjoint.
                   intros z Hz1 Hz2.
                   unfold senv_rename in Hz2.
                   rewrite map_map in Hz2.
                   rewrite in_map_iff in Hz2.
                   destruct Hz2 as (w & Hw1 & Hw2); subst z.
                   destruct w.
                   destruct (eqb_spec t0 s); try subst s.
                   --- cbn in Hz1; contradiction.
                   --- cbn in Hz1.
                       specialize (H1 t0).
                       apply (in_map fst) in Hw2; tauto.

                ** (* Case 6: s not a channel *)
                   rewrite <- (proc_channels_perm _ _ Hcp1) in n2.
                   rewrite <- (proc_channels_perm _ _ Hcp2) in n3.
                   cbn in n2, n3.
                   rewrite eqb_refl in n2, n3; cbn in n2, n3.
                   destruct (in_dec eq_dec x (map fst gamma)); [tauto|].
                   destruct (in_dec eq_dec y (map fst gamma)); [tauto|].
                   rewrite map_app, filter_app in n2, n3.
                   rewrite forallb_filter_nil in n2, n3.
                   1: rewrite forallb_filter_id in n2, n3.
                   2,3,4,5: rewrite forallb_forall; intros z Hz; destruct (in_dec eq_dec z (map fst gamma)); auto.
                   2: destruct Hcp2' as (_ & Hcp2'); apply senv_app in Hcp2'; destruct Hcp2' as (_ & _ & Hcp2'); specialize (Hcp2' z); tauto.
                   3: destruct Hcp1' as (_ & Hcp1'); apply senv_app in Hcp1'; destruct Hcp1' as (_ & _ & Hcp1'); specialize (Hcp1' z); tauto.
                   2,3: rewrite negb_eqb_true_iff; intros Heq; subst z; tauto.
                   cbn in n2, n3.

                   right; split.
                   1: do 2 rewrite map_app, in_app_iff; tauto.
                   rewrite str_list_repl_nin; auto.

                   specialize (IHHcp1 s t Hneq).
                   specialize (IHHcp2 s t Hneq).
                   erewrite proc_forbidden_empty in IHHcp1, IHHcp2.
                   2: apply Hcp2.
                   3: apply Hcp1.
                   2,3: cbn; rewrite map_app, in_app_iff; tauto.
                   specialize (IHHcp1 ltac:(auto)).
                   specialize (IHHcp2 ltac:(auto)).
                   cbn in IHHcp1, IHHcp2.
                   rewrite map_app, in_app_iff in IHHcp1, IHHcp2.
                   destruct IHHcp1 as [(IHHcp1 & _) | (_ & IHHcp1)]; [tauto|].
                   destruct IHHcp2 as [(IHHcp2 & _) | (_ & IHHcp2)]; [tauto|].
                   rewrite IHHcp1, IHHcp2; auto.

    - (* Proc_InCh *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      repeat rewrite senv_valid_cons in Hcp'.
      cbn in Hcp'.

      (* Case 1: s = y *)
      destruct (eqb_spec y s).
      + subst s.
        clear Hallow.

        right; split; auto.
        clear IHHcp; firstorder.

      + (* Case 2: s = x *)
        destruct (eqb_spec x s).
        * subst s.
          left; split; auto.
          fold (senv_rename gamma x t).

          (* Simplify IHHcp *)
          specialize (IHHcp x t Hneq Hallow).
          cbn [map fst] in IHHcp.
          destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)].
          2: cbn in IHHcp; tauto.
          cbn in IHHcp.
          rewrite eqb_refl in IHHcp.
          replace (eqb y x) with false in IHHcp by (symmetry; rewrite eqb_neq; tauto).
          fold (senv_rename gamma x t) in IHHcp.

          constructor; auto.

        * (* Case 3: s in gamma or s not a channel *)
          fold (senv_rename gamma s t).

          (* Simplify IHHcp *)
          specialize (IHHcp s t Hneq Hallow).
          cbn in IHHcp.
          replace (eqb x s) with false in IHHcp by (symmetry; rewrite eqb_neq; tauto).
          replace (eqb y s) with false in IHHcp by (symmetry; rewrite eqb_neq; tauto).
          fold (senv_rename gamma s t) in IHHcp.

          destruct IHHcp as [(IHHcp1 & IHHcp2) | (IHHcp1 & IHHcp2)].
          -- (* Case 3.1: s in gamma *)
            left; split; [tauto|].
            constructor; auto.
          -- (* Case 3.2: s not a channel *)
            right; split; [tauto|].
            rewrite IHHcp2; auto.

    - (* Proc_OutLeft *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      rewrite senv_valid_cons in Hcp'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.
        fold (senv_rename gamma x t).

        (* Simplify IHHcp *)
        specialize (IHHcp x t Hneq Hallow).
        destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)].
        2: cbn in IHHcp; tauto.
        cbn in IHHcp.
        rewrite eqb_refl in IHHcp.
        fold (senv_rename gamma x t) in IHHcp.

        constructor; auto.

      + (* Case 2: s in gamma or s not a channel *)
        specialize (IHHcp s t Hneq Hallow).
        destruct IHHcp as [(IHHcp1 & IHHcp2) | (IHHcp1 & IHHcp2)].
        * (* Case 2.1: s in gamma *)
          cbn in IHHcp1.
          destruct IHHcp1 as [? | IHHcp1]; [tauto|].

          cbn in IHHcp2.
          destruct (eqb_spec x s); try contradiction.
          fold (senv_rename gamma s t) in IHHcp2.

          left; split; auto.
          fold (senv_rename gamma s t).
          constructor; auto.

        * (* Case 2.2: s not a channel *)
          cbn in IHHcp1.
          right; split; auto.
          rewrite IHHcp2; auto.

    - (* Proc_OutRight *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      rewrite senv_valid_cons in Hcp'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.
        fold (senv_rename gamma x t).

        (* Simplify IHHcp *)
        specialize (IHHcp x t Hneq Hallow).
        destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)].
        2: cbn in IHHcp; tauto.
        cbn in IHHcp.
        rewrite eqb_refl in IHHcp.
        fold (senv_rename gamma x t) in IHHcp.

        constructor; auto.

      + (* Case 2: s in gamma or s not a channel *)
        specialize (IHHcp s t Hneq Hallow).
        destruct IHHcp as [(IHHcp1 & IHHcp2) | (IHHcp1 & IHHcp2)].
        * (* Case 2.1: s in gamma *)
          cbn in IHHcp1.
          destruct IHHcp1 as [? | IHHcp1]; [tauto|].

          cbn in IHHcp2.
          destruct (eqb_spec x s); try contradiction.
          fold (senv_rename gamma s t) in IHHcp2.

          left; split; auto.
          fold (senv_rename gamma s t).
          constructor; auto.

        * (* Case 2.2: s not a channel *)
          cbn in IHHcp1.
          right; split; auto.
          rewrite IHHcp2; auto.

    - (* Proc_InCase *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp1 as Hcp1'.
      apply cp_senv_valid in Hcp2 as Hcp2'.
      rewrite senv_valid_cons in Hcp1', Hcp2'.

      (* Simplify Hallow *)
      rewrite in_app_iff in Hallow.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.
        fold (senv_rename gamma x t).

        (* Simplify IHHcp1 *)
        specialize (IHHcp1 x t Hneq ltac:(tauto)).
        cbn in IHHcp1.
        destruct IHHcp1 as [(_ & IHHcp1) | (IHHcp1 & _)].
        2: tauto.
        rewrite eqb_refl in IHHcp1.
        fold (senv_rename gamma x t) in IHHcp1.

        (* Simplify IHHcp2 *)
        specialize (IHHcp2 x t Hneq ltac:(tauto)).
        cbn in IHHcp2.
        destruct IHHcp2 as [(_ & IHHcp2) | (IHHcp2 & _)].
        2: tauto.
        rewrite eqb_refl in IHHcp2.
        fold (senv_rename gamma x t) in IHHcp2.

        constructor; auto.

      + (* Case 2: s in gamma or not a channel *)
        (* Simplify IHHcp1 *)
        specialize (IHHcp1 s t Hneq ltac:(tauto)).
        cbn in IHHcp1.
        assert (n' : eqb x s = false) by (rewrite eqb_neq; auto).
        rewrite n' in IHHcp1.
        fold (senv_rename gamma s t) in IHHcp1.

        (* Simplify IHHcp2 *)
        specialize (IHHcp2 s t Hneq ltac:(tauto)).
        cbn in IHHcp2.
        rewrite n' in IHHcp2.
        fold (senv_rename gamma s t) in IHHcp2.

        destruct IHHcp1 as [(IHHcp1 & IHHcp1') | (IHHcp1 & IHHcp1')].
        * (* Case 2.1: s in gamma *)
          destruct IHHcp1 as [? | IHHcp1]; [contradiction|].

          (* Simplify IHHcp2 *)          
          destruct IHHcp2 as [(_ & IHHcp2) | (IHHcp2 & _)].
          2: tauto.

          left; split; auto.
          fold (senv_rename gamma s t).
          constructor; auto.

        * (* Case 2.2: s not a channel *)
          (* Simplify IHHcp2 *)
          destruct IHHcp2 as [(IHHcp2 & _) | (_ & IHHcp2)].
          1: contradiction.

          right; split; auto.
          rewrite IHHcp1', IHHcp2; auto.

    - (* Proc_Server *)
      cbn; intros s t Hneq Hallow.
      rewrite Forall_forall in H.

      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      rewrite senv_valid_cons in Hcp'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.
        fold (senv_rename gamma x t).

        (* Simplify Hallow *)
        rewrite filter_In in Hallow.
        rewrite negb_eqb_true_iff in Hallow.
        rewrite <- (cp_channels _ _ _ Hcp) in Hallow.
        cbn in Hallow.
        assert (Hallow' : ~ In t (map fst gamma)) by (revert Hallow; apply list_nin_helper; tauto).

        constructor.
        * (* ques *)
          rewrite Forall_forall.
          intros z Hz.
          unfold senv_rename in Hz.
          rewrite map_map in Hz.
          rewrite in_map_iff in Hz.
          destruct Hz as (w & Hw1 & Hw2).
          destruct w; cbn in Hw1; subst z.
          specialize (H s ltac:(rewrite in_map_iff; eexists; split; try apply Hw2; auto)).
          destruct (eqb t0 x); cbn; auto.

        * (* nodup *)
          unfold senv_rename.
          rewrite map_map.
          rewrite in_map_iff.
          intros Hin.
          destruct Hin as (z & Hz1 & Hz2).
          destruct z.
          destruct (eqb_spec t0 x); cbn in Hz1; subst t0; try subst t.
          1: apply H0. 2: apply Hallow'. all: rewrite in_map_iff; eexists; split; try apply Hz2; auto.

        * rewrite senv_rename_nin; auto.

      + (* Case 2: s = y *)
        destruct (eqb_spec y s).
        * subst s.
          right; split; [tauto|]; auto.

        * (* Case 3: s in gamma *)
          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          -- (* Simplify i *)
             rewrite filter_In in i.
             rewrite negb_eqb_true_iff in i.
             rewrite <- (cp_channels _ _ _ Hcp) in i.
             cbn in i.
             destruct i as ([? | i] & _); [contradiction|].

             cbn in Hallow.

             (* Simplify IHHcp *)
             specialize (IHHcp s t Hneq ltac:(tauto)).
             cbn in IHHcp.
             replace (eqb y s) with false in IHHcp by (symmetry; rewrite eqb_neq; auto).
             destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)]; [|tauto].
             fold (senv_rename gamma s t) in IHHcp.

             left; split; auto.
             fold (senv_rename gamma s t).
             constructor; auto.
             ++ (* ques *)
                rewrite Forall_forall.
                intros z Hz.
                unfold senv_rename in Hz.
                rewrite map_map in Hz.
                rewrite in_map_iff in Hz.
                destruct Hz as (w & Hw1 & Hw2).
                destruct w.
                specialize (H s0 ltac:(rewrite in_map_iff; eexists; split; try apply Hw2; auto)).
                destruct (eqb t0 s); cbn in Hw1; subst z; auto.

             ++ (* nodup *)
                unfold senv_rename.
                rewrite map_map.
                rewrite in_map_iff.
                intros Hin.
                destruct Hin as (z & Hz1 & Hz2).
                destruct z.
                destruct (eqb_spec t0 s); cbn in Hz1; subst x; try subst t0.
                1: tauto.
                apply H0; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

          -- (* Case 4: s not a channel *)
             (* Simplify n1 *)
             rewrite filter_In in n1.
             rewrite negb_eqb_true_iff in n1.
             rewrite <- (cp_channels _ _ _ Hcp) in n1.
             cbn in n1.
             assert (n1' : ~ In s (map fst gamma)) by tauto.

             right; split; [tauto|].

             (* Simplify IHHcp *)
             specialize (IHHcp s t Hneq).
             erewrite proc_forbidden_empty in IHHcp.
             2: apply Hcp.
             2: cbn; tauto.
             specialize (IHHcp ltac:(auto)).
             destruct IHHcp as [(IHHcp & _) | (_ & IHHcp)].
             1: cbn in IHHcp; tauto.

             rewrite IHHcp; auto.

    - (* Proc_Client *)
      cbn; intros s t Hneq Hallow.

      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      rewrite senv_valid_cons in Hcp'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.
        fold (senv_rename gamma x t).

        (* Simplify Hallow *)
        rewrite filter_In in Hallow.
        rewrite negb_eqb_true_iff in Hallow.
        rewrite <- (cp_channels _ _ _ Hcp) in Hallow.
        cbn in Hallow.
        assert (Hallow' : ~ In t (map fst gamma)) by (revert Hallow; apply list_nin_helper; tauto).

        constructor.
        * (* nodup *)
          unfold senv_rename.
          rewrite map_map.
          rewrite in_map_iff.
          intros Hin.
          destruct Hin as (z & Hz1 & Hz2).
          destruct z.
          destruct (eqb_spec t0 x); cbn in Hz1; subst t0; try subst t.
          1: apply H. 2: apply Hallow'. all: rewrite in_map_iff; eexists; split; try apply Hz2; auto.

        * rewrite senv_rename_nin; auto.

      + (* Case 2: s = y *)
        destruct (eqb_spec y s).
        * subst s.
          right; split; [tauto|]; auto.

        * (* Case 3: s in gamma *)
          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          -- (* Simplify i *)
             rewrite filter_In in i.
             rewrite negb_eqb_true_iff in i.
             rewrite <- (cp_channels _ _ _ Hcp) in i.
             cbn in i.
             destruct i as ([? | i] & _); [contradiction|].

             cbn in Hallow.

             (* Simplify IHHcp *)
             specialize (IHHcp s t Hneq ltac:(tauto)).
             cbn in IHHcp.
             replace (eqb y s) with false in IHHcp by (symmetry; rewrite eqb_neq; auto).
             destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)]; [|tauto].
             fold (senv_rename gamma s t) in IHHcp.

             left; split; auto.
             fold (senv_rename gamma s t).
             constructor; auto.
             ++ (* nodup *)
                unfold senv_rename.
                rewrite map_map.
                rewrite in_map_iff.
                intros Hin.
                destruct Hin as (z & Hz1 & Hz2).
                destruct z.
                destruct (eqb_spec t0 s); cbn in Hz1; subst x; try subst t0.
                1: tauto.
                apply H; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

          -- (* Case 4: s not a channel *)
             (* Simplify n1 *)
             rewrite filter_In in n1.
             rewrite negb_eqb_true_iff in n1.
             rewrite <- (cp_channels _ _ _ Hcp) in n1.
             cbn in n1.
             assert (n1' : ~ In s (map fst gamma)) by tauto.

             right; split; [tauto|].

             (* Simplify IHHcp *)
             specialize (IHHcp s t Hneq).
             erewrite proc_forbidden_empty in IHHcp.
             2: apply Hcp.
             2: cbn; tauto.
             specialize (IHHcp ltac:(auto)).
             destruct IHHcp as [(IHHcp & _) | (_ & IHHcp)].
             1: cbn in IHHcp; tauto.

             rewrite IHHcp; auto.

    - (* Proc_ClientNull *)
      cbn; intros s t Hneq Hallow.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.

        (* Simplify IHHcp *)
        specialize (IHHcp x t Hneq).
        erewrite proc_forbidden_empty in IHHcp.
        2: apply Hcp.
        2: auto.
        rewrite <- (cp_channels _ _ _ Hcp) in Hallow.
        specialize (IHHcp ltac:(auto)).
        destruct IHHcp as [(IHHcp & _) | (_ & IHHcp)]; [tauto|].

        fold (senv_rename gamma x t).
        rewrite senv_rename_nin; auto.
        constructor; auto.

      + (* Case 2: s in gamma *)
        match type of Hallow with context[if ?p then _ else _] => destruct p end.
        * rewrite <- (cp_channels _ _ _ Hcp) in i.
          left; split; auto.

          (* Simplify IHHcp *)
          specialize (IHHcp s t Hneq ltac:(cbn in Hallow; auto)).
          destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)]; [|tauto].

          fold (senv_rename gamma s t).
          constructor; auto.
          -- (* nodup *)
             unfold senv_rename.
             rewrite map_map.
             rewrite in_map_iff.
             intros Hin.
             destruct Hin as (z & Hz1 & Hz2).
             destruct z.
             destruct (eqb_spec t0 s); cbn in Hz1; subst x.
             ++ subst t0.
                cbn in Hallow; tauto.
             ++ apply H; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

        * (* Case 3: s not a channel *)
          rewrite <- (cp_channels _ _ _ Hcp) in n0.
          right; split; [tauto|].

          (* Simplify IHHcp *)
          specialize (IHHcp s t Hneq).
          erewrite proc_forbidden_empty in IHHcp.
          2: apply Hcp.
          2: auto.
          specialize (IHHcp ltac:(auto)).
          destruct IHHcp as [(IHHcp & _) | (_ & IHHcp)]; [contradiction|].

          rewrite IHHcp; auto.

    - (* Proc_ClientSplit *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      repeat rewrite senv_valid_cons in Hcp'.
      cbn in Hcp'.

      (* Case 1: s = y *)
      destruct (eqb_spec y s).
      + subst s.
        right; split; [firstorder | auto].

      + (* Case 2: s = x *)
        destruct (eqb_spec x s).
        * subst s.
          left; split; auto.

          (* Simplify IHHcp *)
          specialize (IHHcp x t Hneq Hallow).
          cbn in IHHcp.
          rewrite eqb_refl in IHHcp.
          replace (eqb y x) with false in IHHcp by (symmetry; rewrite eqb_neq; tauto).
          destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)].
          2: tauto.
          fold (senv_rename gamma x t).
          fold (senv_rename gamma x t) in IHHcp.
          rewrite senv_rename_nin in *; try tauto.

          constructor; auto.

        * (* Case 3: s in gamma or not a channel *)
          specialize (IHHcp s t Hneq Hallow).
          cbn in IHHcp.
          replace (eqb x s) with false in IHHcp by (symmetry; rewrite eqb_neq; tauto).
          replace (eqb y s) with false in IHHcp by (symmetry; rewrite eqb_neq; tauto).
          fold (senv_rename gamma s t) in IHHcp.
          fold (senv_rename gamma s t).

          destruct IHHcp as [(IHHcp1 & IHHcp2) | (IHHcp1 & IHHcp2)].
          -- (* Case 3.1: s in gamma *)
             left; split; [tauto|].
             constructor; auto.
          -- (* Case 3.2: not a channel *)
             right; split; [tauto|].
             rewrite IHHcp2; auto.

    - (* Proc_CompAndSplit *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp1 as Hcp1'.
      apply cp_senv_valid in Hcp2 as Hcp2'.
      rewrite senv_valid_cons in Hcp1', Hcp2'.
      rewrite map_app, in_app_iff in Hcp1', Hcp2'.
      destruct Hcp1' as (Hcp1' & Hcp3).
      destruct Hcp2' as (Hcp2' & Hcp4).
      apply senv_app in Hcp3, Hcp4.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s; right; split; auto.
        do 2 rewrite map_app, in_app_iff.
        tauto.

      + (* Case 2: s in gamma *)
        destruct (in_dec eq_dec s (map fst gamma)).
        * rewrite in_app_iff in Hallow.
          specialize (IHHcp1 s t Hneq ltac:(tauto)).
          specialize (IHHcp2 s t Hneq ltac:(tauto)).
          cbn in IHHcp1, IHHcp2.
          destruct (eqb_spec x s); try contradiction.
          rewrite map_app, in_app_iff in IHHcp1, IHHcp2.
          destruct IHHcp1 as [(_ & IHHcp1) | ?]; [|tauto].
          destruct IHHcp2 as [(_ & IHHcp2) | ?]; [|tauto].
          fold (senv_rename (gamma ++ delta1) s t) in IHHcp1.
          fold (senv_rename (gamma ++ delta2) s t) in IHHcp2.

          left; split.
          1: rewrite map_app, in_app_iff; auto.
          do 2 rewrite senv_rename_app.
          rewrite senv_rename_app in IHHcp1, IHHcp2.
          rewrite <- senv_rename_repl.
          constructor; auto.
          -- unfold senv_rename; rewrite map_map; cbn.
             rewrite Forall_forall.
             rewrite Forall_forall in H.
             intros z Hz.
             rewrite in_map_iff in Hz.
             destruct Hz as (m & Hm1 & Hm2); subst z.
             specialize (H _ ltac:(rewrite in_map_iff; eexists; split; try apply Hm2; auto)).
             destruct m; destruct (eqb t0 s); cbn; auto.

          -- assert (Hcp5 : senv_disjoint gamma delta1) by tauto.
             assert (Hcp6 : senv_disjoint gamma delta2) by tauto.
             unfold senv_disjoint in Hcp5, Hcp6.
             specialize (Hcp5 _ i); specialize (Hcp6 _ i).
             do 2 (rewrite senv_rename_nin; auto).

        * (* Case 3: s in delta1 *)
          match type of Hallow with context[if ?p then _ else _] => destruct p end.
          -- rewrite in_app_iff in Hallow.
             rewrite filter_In in Hallow.
             rewrite negb_in_dec_true_iff in Hallow.
             rewrite <- (cp_channels _ _ _ Hcp2) in Hallow.
             cbn in Hallow.
             rewrite map_app, in_app_iff in Hallow.

             rewrite filter_In in i.
             rewrite negb_in_dec_true_iff in i.
             rewrite <- (cp_channels _ _ _ Hcp1) in i.
             cbn in i.
             rewrite map_app, in_app_iff in i.
             assert (i' : In s (map fst delta1)) by tauto.

             specialize (IHHcp1 s t Hneq ltac:(tauto)).
             cbn in IHHcp1.
             destruct (eqb_spec x s); try contradiction.
             rewrite map_app, in_app_iff in IHHcp1.
             destruct IHHcp1 as [(_ & IHHcp1) | ?]; [|tauto].
             fold (senv_rename (gamma ++ delta1) s t) in IHHcp1.

             unfold senv_disjoint in H0.
             assert (~ In s (map fst delta2)) by (clear IHHcp2; firstorder).
             specialize (IHHcp2 s t Hneq).
             erewrite proc_forbidden_empty in IHHcp2.
             2: apply Hcp2.
             2: cbn; rewrite map_app, in_app_iff; tauto.
             specialize (IHHcp2 ltac:(auto)).
             cbn in IHHcp2.
             destruct (eqb_spec x s); try contradiction.
             rewrite map_app, in_app_iff in IHHcp2.
             destruct IHHcp2 as [? | (_ & IHHcp2)]; [tauto|].

             left; split.
             1: do 2 rewrite map_app, in_app_iff; auto.
             do 2 rewrite senv_rename_app.
             rewrite senv_rename_app in IHHcp1.
             rewrite (senv_rename_nin gamma s t) in IHHcp1; auto.
             rewrite <- senv_rename_repl.
             rewrite senv_rename_nin; auto.
             rewrite (senv_rename_nin delta2 s t).
             2: auto.
             rewrite IHHcp2.

             constructor; auto.
             unfold senv_disjoint.
             intros m Hm.
             rewrite in_map_iff in Hm.
             destruct Hm as (z & Hz1 & Hz2); subst m.
             unfold senv_rename in Hz2.
             rewrite in_map_iff in Hz2.
             destruct Hz2 as (m & Hm1 & Hm2); subst z.
             destruct m; destruct (eqb_spec t0 s); cbn; try subst.
             2: apply H0; rewrite in_map_iff; eexists; split; try apply Hm2; auto.
             intros Hin; apply Hallow; right.
             split; auto.
             unfold senv_disjoint in Hcp4; clear H0; firstorder.

          -- (* Case 4: s in delta 2 *)
             match type of Hallow with context[if ?p then _ else _] => destruct p end.
             ++ rewrite in_app_iff in Hallow.
                rewrite filter_In in Hallow.
                rewrite negb_in_dec_true_iff in Hallow.
                rewrite <- (cp_channels _ _ _ Hcp1) in Hallow.
                cbn in Hallow.
                rewrite map_app, in_app_iff in Hallow.

                rewrite filter_In in i.
                rewrite negb_in_dec_true_iff in i.
                rewrite <- (cp_channels _ _ _ Hcp2) in i.
                cbn in i.
                rewrite map_app, in_app_iff in i.
                assert (i' : In s (map fst delta2)) by tauto.

                specialize (IHHcp2 s t Hneq ltac:(tauto)).
                cbn in IHHcp2.
                destruct (eqb_spec x s); try contradiction.
                rewrite map_app, in_app_iff in IHHcp2.
                destruct IHHcp2 as [(_ & IHHcp2) | ?]; [|tauto].
                fold (senv_rename (gamma ++ delta2) s t) in IHHcp2.

                unfold senv_disjoint in H0.
                assert (~ In s (map fst delta1)) by (clear IHHcp1; firstorder).
                specialize (IHHcp1 s t Hneq).
                erewrite proc_forbidden_empty in IHHcp1.
                2: apply Hcp1.
                2: cbn; rewrite map_app, in_app_iff; tauto.
                specialize (IHHcp1 ltac:(auto)).
                cbn in IHHcp1.
                destruct (eqb_spec x s); try contradiction.
                rewrite map_app, in_app_iff in IHHcp1.
                destruct IHHcp1 as [? | (_ & IHHcp1)]; [tauto|].

                left; split.
                1: do 2 rewrite map_app, in_app_iff; auto.
                do 2 rewrite senv_rename_app.
                rewrite senv_rename_app in IHHcp2.
                rewrite (senv_rename_nin gamma s t) in IHHcp2; auto.
                rewrite <- senv_rename_repl.
                rewrite senv_rename_nin; auto.
                rewrite (senv_rename_nin delta1 s t).
                2: auto.
                rewrite IHHcp1.

                constructor; auto.
                unfold senv_disjoint.
                intros m Hm.
                rewrite in_map_iff.
                intros Hin.
                destruct Hin as (z & Hz1 & Hz2); subst m.
                unfold senv_rename in Hz2.
                rewrite in_map_iff in Hz2.
                destruct Hz2 as (m & Hm1 & Hm2); subst z.
                destruct m; destruct (eqb_spec t0 s); cbn; try subst.
                2: cbn in Hm; apply (H0 _ Hm ltac:(rewrite in_map_iff; eexists; split; try apply Hm2; auto)).
                apply Hallow; left; split; auto.
                cbn in Hm.
                unfold senv_disjoint in Hcp3; clear H0; firstorder.

             ++ (* Case 5: s not a channel *)
                rewrite filter_In in n1, n2.
                rewrite negb_in_dec_true_iff in n1, n2.
                rewrite <- (cp_channels _ _ _ Hcp1) in n1.
                rewrite <- (cp_channels _ _ _ Hcp2) in n2.
                cbn in n1, n2.
                rewrite map_app, in_app_iff in n1, n2.

                specialize (IHHcp1 s t Hneq).
                specialize (IHHcp2 s t Hneq).
                erewrite proc_forbidden_empty in IHHcp1, IHHcp2.
                2: apply Hcp2.
                3: apply Hcp1.
                2,3: cbn; rewrite map_app, in_app_iff; tauto.
                specialize (IHHcp1 ltac:(auto)).
                specialize (IHHcp2 ltac:(auto)).
                cbn in IHHcp1, IHHcp2.
                rewrite map_app, in_app_iff in IHHcp1, IHHcp2.
                destruct IHHcp1 as [? | (_ & IHHcp1)]; [tauto|].
                destruct IHHcp2 as [? | (_ & IHHcp2)]; [tauto|].

                do 2 rewrite map_app, in_app_iff.
                rewrite IHHcp1, IHHcp2.
                rewrite str_list_repl_nin; [|tauto].
                right; split; tauto.

    - (* Proc_OutTyp *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      rewrite senv_valid_cons in Hcp'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.

        (* Specialize (IHHcp *)
        specialize (IHHcp x t Hneq Hallow).
        cbn in IHHcp.
        destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)].
        2: tauto.
        rewrite eqb_refl in IHHcp.
        constructor; auto.

      + (* Case 2: s in gamma or s not a channel *)
        specialize (IHHcp s t Hneq Hallow).
        cbn in IHHcp.
        replace (eqb x s) with false in IHHcp by (symmetry; rewrite eqb_neq; auto).
        destruct IHHcp as [(IHHcp1 & IHHcp2) | (IHHcp1 & IHHcp2)].
        -- left; split; auto.
           constructor; auto.
        -- right; split; auto.
           rewrite IHHcp2; auto.

    - (* Proc_InTyp *)
      cbn; intros s t Hneq Hallow.
      (* senv_valid *)
      apply cp_senv_valid in Hcp as Hcp'.
      rewrite senv_valid_cons in Hcp'.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.

        (* Specialize (IHHcp *)
        specialize (IHHcp x t Hneq Hallow).
        cbn in IHHcp.
        destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)].
        2: tauto.
        rewrite eqb_refl in IHHcp.
        constructor; auto.
        * fold (senv_rename gamma x t).
          rewrite senv_rename_snd.
          auto.

      + (* Case 2: s in gamma or s not a channel *)
        specialize (IHHcp s t Hneq Hallow).
        cbn in IHHcp.
        replace (eqb x s) with false in IHHcp by (symmetry; rewrite eqb_neq; auto).
        destruct IHHcp as [(IHHcp1 & IHHcp2) | (IHHcp1 & IHHcp2)].
        -- left; split; auto.
           constructor; auto.
           fold (senv_rename gamma s t).
           rewrite senv_rename_snd.
           auto.
        -- right; split; auto.
           rewrite IHHcp2; auto.

    - (* Proc_OutUnit *)
      cbn; intros s t Hneq _.
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto; constructor.
      + right; split; auto; tauto.

    - (* Proc_InUnit *)
      cbn; intros s t Hneq Hallow.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.
        fold (senv_rename gamma x t).
        rewrite senv_rename_nin; auto.
        constructor; auto.
        rewrite <- (cp_channels _ _ _ Hcp) in Hallow; auto.

      + (* Case 2: s in gamma *)
        match type of Hallow with context[if ?p then _ else _] => destruct p end.
        * rewrite <- (cp_channels _ _ _ Hcp) in i.
          left; split; auto.
          cbn in Hallow.

          (* Simplify IHHcp *)
          specialize (IHHcp s t Hneq ltac:(auto)).
          destruct IHHcp as [(_ & IHHcp) | (IHHcp & _)]; [|tauto].

          constructor; auto.
          rewrite map_map.
          rewrite in_map_iff.
          intros Hin.
          destruct Hin as (z & Hz1 & Hz2).
          destruct z.
          destruct (eqb_spec t0 s); cbn in Hz1; subst x; try subst t0.
          1: tauto.
          apply H; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

        * (* Case 3: s not a channel *)
          rewrite <- (cp_channels _ _ _ Hcp) in n0.
          right; split; [tauto|].

          (* Simplify IHHcp *)
          specialize (IHHcp s t Hneq).
          erewrite proc_forbidden_empty in IHHcp.
          2: apply Hcp.
          2: auto.
          specialize (IHHcp ltac:(auto)).
          destruct IHHcp as [(IHHcp & _) | (_ & IHHcp)].
          1: contradiction.
          rewrite IHHcp; auto.

    - (* Proc_EmptyCase *)
      cbn [map fst In proc_forbidden proc_rename]; intros s t Hneq Hallow.

      (* Case 1: s = x *)
      destruct (eqb_spec x s).
      + subst s.
        left; split; auto.
        cbn.
        rewrite eqb_refl.
        fold (senv_rename gamma x t).
        rewrite senv_rename_nin; auto.

        (* Simplify Hallow *)
        match type of Hallow with context[if ?p then _ else _] => destruct p end.
        2: cbn in n; tauto.
        clear i.
        cbn in Hallow.
        constructor; auto.

      + (* Case 2 : s in gamma *)
        assert (n' : eqb x s = false) by (rewrite eqb_neq; auto).

        match type of Hallow with context[if ?p then _ else _] => destruct p end.
        * cbn in i; destruct i as [? | i]; [contradiction|].
          cbn in Hallow.
          assert (Hallow' : x <> t /\ ~ In t (map fst gamma)) by tauto.

          left; split; auto.
          cbn.
          rewrite n'.
          fold (senv_rename gamma s t).
          rewrite <- senv_rename_repl.

          constructor.
          -- (* nodup *)
             unfold senv_rename.
             rewrite map_map.
             rewrite in_map_iff.
             intros Hin.
             destruct Hin as (z & Hz1 & Hz2).
             destruct z.
             destruct (eqb_spec t0 s); cbn in Hz1; subst x; try subst t0.
             1: tauto.
             apply H; rewrite in_map_iff; eexists; split; try apply Hz2; auto.

          -- (* senv_valid *)
             apply senv_rename_nin_valid; auto.

        * (* Case 3: s not a channel *)
          cbn in n0.
          right; split; auto.
          rewrite <- senv_rename_repl.
          rewrite senv_rename_nin; auto.

    - (* Permutation *)
      intros s t Hneq Hallow.
      specialize (IHHcp s t Hneq Hallow).
      destruct IHHcp as [(IHHcp1 & IHHcp2) | (IHHcp1 & IHHcp2)].
      + left; split.
        * rewrite <- H; auto.
        * eapply cp_perm.
          1: apply IHHcp2.
          unfold senv_rename.
          apply Permutation_map; auto.
      + right; split; auto.
        intros Hin; apply IHHcp1.
        rewrite H; auto.
  Qed.

  (* Precondition for replacing a propositional variable P with Q *)
  Fixpoint proc_var_subst_pre (p : Process) (v : pvn) (v' : pvn) : Prop :=
  match p with
  | Proc_Const _ _ => True
  | Proc_Link x y => True
  | Proc_Comp x a p q => ~ In v' (styp_forbidden a v) /\ proc_var_subst_pre p v v' /\ proc_var_subst_pre q v v'
  | Proc_OutCh x y p q => proc_var_subst_pre p v v' /\ proc_var_subst_pre q v v'
  | Proc_OutChAndSplit x y l p q => proc_var_subst_pre p v v' /\ proc_var_subst_pre q v v'
  | Proc_InCh x y p => proc_var_subst_pre p v v'
  | Proc_OutLeft x p => proc_var_subst_pre p v v'
  | Proc_OutRight x p => proc_var_subst_pre p v v'
  | Proc_InCase x p q => proc_var_subst_pre p v v' /\ proc_var_subst_pre q v v'
  | Proc_Server x y p => proc_var_subst_pre p v v'
  | Proc_Client x y p => proc_var_subst_pre p v v'
  | Proc_ClientNull x p => proc_var_subst_pre p v v'
  | Proc_ClientSplit x y p => proc_var_subst_pre p v v'
  | Proc_CompAndSplit x a l p q => ~ In v' (styp_forbidden a v) /\ proc_var_subst_pre p v v' /\ proc_var_subst_pre q v v'
  | Proc_OutTyp x a w b p => ~ In v' (styp_forbidden b w) /\ ~ In v' (styp_forbidden a v) /\ proc_var_subst_pre p v v'
  | Proc_InTyp x w _ p => if pvn_eqb w v then True else w <> v' /\ proc_var_subst_pre p v v'
  | Proc_OutUnit x => True
  | Proc_InUnit x p => proc_var_subst_pre p v v'
  | Proc_EmptyCase x l => True
  end.

  (* Replace a free type variable in a process with an expression *)
  (* If v is a free variable in p, replace v with a. *)
  (* if v is not a free variable in p, leave p unchanged *)
  Fixpoint proc_var_subst (p : Process) (v : pvn) (e : STyp) : Process :=
  match p with
  | Proc_Const c l => Proc_Const c l
  | Proc_Link x y => Proc_Link x y
  | Proc_Comp x a p q => Proc_Comp x (styp_subst v a e) (proc_var_subst p v e) (proc_var_subst q v e)
  | Proc_OutCh x y p q => Proc_OutCh x y (proc_var_subst p v e) (proc_var_subst q v e)
  | Proc_OutChAndSplit x y l p q => Proc_OutChAndSplit x y l (proc_var_subst p v e) (proc_var_subst q v e)
  | Proc_InCh x y p => Proc_InCh x y (proc_var_subst p v e)
  | Proc_OutLeft x p => Proc_OutLeft x (proc_var_subst p v e)
  | Proc_OutRight x p => Proc_OutRight x (proc_var_subst p v e)
  | Proc_InCase x p q => Proc_InCase x (proc_var_subst p v e) (proc_var_subst q v e)
  | Proc_Server x y p => Proc_Server x y (proc_var_subst p v e)
  | Proc_Client x y p => Proc_Client x y (proc_var_subst p v e)
  | Proc_ClientNull x p => Proc_ClientNull x (proc_var_subst p v e)
  | Proc_ClientSplit x y p => Proc_ClientSplit x y (proc_var_subst p v e)
  | Proc_CompAndSplit x a l p q => Proc_CompAndSplit x (styp_subst v a e) l (proc_var_subst p v e) (proc_var_subst q v e)
  | Proc_OutTyp x a w b p => Proc_OutTyp x (styp_subst v a e) w (if pvn_eqb w v then b else styp_subst v b e) (proc_var_subst p v e)
  | Proc_InTyp x w b p => Proc_InTyp x w (if pvn_eqb w v then b else styp_subst v b e) (if pvn_eqb w v then p else proc_var_subst p v e)
  | Proc_OutUnit x => Proc_OutUnit x
  | Proc_InUnit x p => Proc_InUnit x (proc_var_subst p v e)
  | Proc_EmptyCase x l => Proc_EmptyCase x l
  end.

  Lemma cp_var_subst :
  forall p v e gamma,
  cp p gamma ->
  Forall (fun r => Forall (fun v' => ~ In v' (styp_forbidden r v)) (fvar e)) (map snd gamma) ->
  Forall (fun v' => proc_var_subst_pre p v v') (fvar e) ->
  cp (proc_var_subst p v e) (map (fun r => (fst r, styp_subst v (snd r) e)) gamma).
  Proof.
    intros p v e gamma Hcp.
    induction Hcp.
    - (* Proc_Const *)
      intros Hpre1 _; cbn.
      rewrite combine_map_snd in Hpre1; auto.
      eapply pcn_sig_subst in Hpre1.
      2: apply H0.
      erewrite combine_map.
      Unshelve.
      4: exact id.
      4: exact (fun r => styp_subst v r e).
      2: intros z; destruct z; cbn; auto.
      2: intros z; destruct z; cbn; auto.
      rewrite map_id.
      constructor; auto.
      rewrite length_map; auto.

    - (* Proc_Link *)
      intros _ _; cbn.
      rewrite <- styp_subst_dual.
      constructor; auto.

    - (* Proc_Comp *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite map_app, Forall_app in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).

      (* Simplify Hpre2 *)
      apply Forall_and_inv in Hpre2.
      destruct Hpre2 as (Hpre2_1 & Hpre2_2).
      apply Forall_and_inv in Hpre2_2.
      destruct Hpre2_2 as (Hpre2_2 & Hpre2_3).

      (* Simplify IHHcp1 *)
      cbn in IHHcp1.
      rewrite Forall_cons_iff in IHHcp1.
      specialize (IHHcp1 ltac:(split; auto) ltac:(auto)).

      (* Simplify IHHcp2 *)
      cbn in IHHcp2.
      rewrite Forall_cons_iff in IHHcp2.
      unfold styp_forbidden in IHHcp2.
      rewrite <- styp_forbidden_dual in IHHcp2.
      specialize (IHHcp2 ltac:(split; auto) ltac:(auto)).

      rewrite map_app.
      constructor; auto.
      2: rewrite styp_subst_dual; auto.

      (* disjointness *)
      unfold senv_disjoint.
      do 2 rewrite map_map; cbn.
      auto.

    - (* Proc_OutCh *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      rewrite map_app, Forall_app in Hpre1_2.
      destruct Hpre1_2 as (Hpre1_2 & Hpre1_3).
      cbn in Hpre1_1.
      assert (Hpre1_1a : Forall (fun v' => ~ In v' (styp_forbidden a v)) (fvar e)) by (rewrite Forall_forall; rewrite Forall_forall in Hpre1_1; intros z; specialize (Hpre1_1 z); rewrite in_app_iff in Hpre1_1; tauto).
      assert (Hpre1_1b : Forall (fun v' => ~ In v' (styp_forbidden b v)) (fvar e)) by (rewrite Forall_forall; rewrite Forall_forall in Hpre1_1; intros z; specialize (Hpre1_1 z); rewrite in_app_iff in Hpre1_1; tauto).

      (* Simplify Hpre2 *)
      apply Forall_and_inv in Hpre2.
      destruct Hpre2 as (Hpre2_1 & Hpre2_2).

      (* Simplify IHHcp1 *)
      cbn in IHHcp1.
      rewrite Forall_cons_iff in IHHcp1.
      specialize (IHHcp1 ltac:(split; auto) ltac:(auto)).

      (* Simplify IHHcp2 *)
      cbn in IHHcp2.
      rewrite Forall_cons_iff in IHHcp2.
      specialize (IHHcp2 ltac:(split; auto) ltac:(auto)).

      rewrite map_app.
      constructor; auto.

      (* nodup *)
      + rewrite map_map; cbn; auto.

      (* disjointness *)
      + unfold senv_disjoint.
        do 2 rewrite map_map; cbn; auto.

    - (* Proc_OutChAndSplit *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      assert (Hpre1_1' : Forall (fun v' => ~ In v' (styp_forbidden a v) /\ ~ In v' (styp_forbidden b v)) (fvar e)).
      { rewrite Forall_forall; rewrite Forall_forall in Hpre1_1; intros z Hz; specialize (Hpre1_1 z Hz); cbn in Hpre1_1; rewrite in_app_iff in Hpre1_1; unfold styp_forbidden; tauto. }
      apply Forall_and_inv in Hpre1_1'.
      do 2 rewrite map_app, Forall_app in Hpre1_2.
      destruct Hpre1_2 as (Hpre1_2 & Hpre1_3 & Hpre1_4).

      (* Simplify Hpre2 *)
      apply Forall_and_inv in Hpre2.
      destruct Hpre2 as (Hpre2_1 & Hpre2_2).

      (* Simplify IHHcp1 *)
      cbn in IHHcp1.
      rewrite Forall_cons_iff in IHHcp1.
      rewrite map_app, Forall_app in IHHcp1.
      specialize (IHHcp1 ltac:(tauto) ltac:(auto)).

      (* Simplify IHHcp2 *)
      cbn in IHHcp2.
      rewrite Forall_cons_iff in IHHcp2.
      rewrite map_app, Forall_app in IHHcp2.
      specialize (IHHcp2 ltac:(tauto) ltac:(auto)).

      rewrite map_app in IHHcp1, IHHcp2.

      do 2 rewrite map_app.
      replace (map fst gamma) with (map fst (map (fun r => (fst r, styp_subst v (snd r) e)) gamma)).
      2: { rewrite map_map; cbn; auto. }
      constructor; auto.

      + rewrite map_map; cbn.
        rewrite Forall_forall; rewrite Forall_forall in H.
        intros z Hz.
        rewrite in_map_iff in Hz.
        destruct Hz as (w & Hw1 & Hw2); subst z.
        specialize (H (snd w) ltac:(apply in_map; auto)).
        destruct (snd w); try contradiction; cbn; auto.

      + rewrite map_map; cbn; auto.
      + unfold senv_disjoint; do 2 rewrite map_map; cbn; auto.

    - (* Proc_InCh *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify IHHcp *)
      cbn in IHHcp.
      repeat rewrite Forall_cons_iff in IHHcp.
      do 2 rewrite Forall_forall in IHHcp.
      rewrite Forall_forall in Hpre1_1.
      specialize (IHHcp ltac:(repeat split; auto; intros z Hz; specialize (Hpre1_1 _ Hz); rewrite in_app_iff in Hpre1_1; tauto) Hpre2).

      constructor; auto.

    - (* Proc_OutLeft *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify IHHcp *)
      cbn in IHHcp.
      rewrite Forall_cons_iff in IHHcp.
      rewrite Forall_forall in IHHcp.
      rewrite Forall_forall in Hpre1_1.
      specialize (IHHcp ltac:(split; auto; intros z Hz; specialize (Hpre1_1 _ Hz); rewrite in_app_iff in Hpre1_1; tauto) Hpre2).

      constructor; auto.

    - (* Proc_OutRight *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify IHHcp *)
      cbn in IHHcp.
      rewrite Forall_cons_iff in IHHcp.
      rewrite Forall_forall in IHHcp.
      rewrite Forall_forall in Hpre1_1.
      specialize (IHHcp ltac:(split; auto; intros z Hz; specialize (Hpre1_1 _ Hz); rewrite in_app_iff in Hpre1_1; tauto) Hpre2).

      constructor; auto.

    - (* Proc_InCase *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify Hpre2 *)
      apply Forall_and_inv in Hpre2.
      destruct Hpre2 as (Hpre2_1 & Hpre2_2).

      (* Simplify IHHcp1, IHHcp2 *)
      cbn in IHHcp1, IHHcp2.
      rewrite Forall_cons_iff in IHHcp1, IHHcp2.
      rewrite Forall_forall in IHHcp1, IHHcp2.
      rewrite Forall_forall in Hpre1_1.
      specialize (IHHcp1 ltac:(split; auto; intros z Hz; specialize (Hpre1_1 _ Hz); rewrite in_app_iff in Hpre1_1; tauto) Hpre2_1).
      specialize (IHHcp2 ltac:(split; auto; intros z Hz; specialize (Hpre1_1 _ Hz); rewrite in_app_iff in Hpre1_1; tauto) Hpre2_2).

      constructor; auto.

    - (* Proc_Server *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify IHHcp *)
      cbn in IHHcp.
      rewrite Forall_cons_iff in IHHcp.
      rewrite Forall_forall in IHHcp.
      rewrite Forall_forall in Hpre1_1.
      specialize (IHHcp ltac:(split; auto; intros z Hz; specialize (Hpre1_1 _ Hz); rewrite in_app_iff in Hpre1_1; tauto) Hpre2).

      constructor; auto.
      2: rewrite map_map; auto.

      rewrite Forall_forall; rewrite Forall_forall in H.
      rewrite map_map; cbn.
      intros z Hz.
      rewrite in_map_iff in Hz.
      destruct Hz as (m & Hm1 & Hm2); subst z.
      specialize (H _ ltac:(rewrite in_map_iff; eexists; split; try apply Hm2; auto)).
      destruct (snd m); try contradiction; cbn; auto.

    - (* Proc_Client *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify IHHcp *)
      cbn in IHHcp.
      rewrite Forall_cons_iff in IHHcp.
      rewrite Forall_forall in IHHcp.
      rewrite Forall_forall in Hpre1_1.
      specialize (IHHcp ltac:(split; auto; intros z Hz; specialize (Hpre1_1 _ Hz); rewrite in_app_iff in Hpre1_1; tauto) Hpre2).

      constructor; auto.
      rewrite map_map; cbn; auto.

    - (* Proc_ClientNull *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify IHHcp *)
      cbn in IHHcp.
      specialize (IHHcp Hpre1_2 Hpre2).

      constructor; auto.
      rewrite map_map; cbn; auto.

    - (* Proc_ClientSplit *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify IHHcp *)
      cbn in IHHcp.
      repeat rewrite Forall_cons_iff in IHHcp.
      rewrite Forall_forall in IHHcp.
      rewrite Forall_forall in Hpre1_1.
      specialize (IHHcp ltac:(repeat split; auto; intros z Hz; specialize (Hpre1_1 _ Hz); rewrite in_app_iff in Hpre1_1; tauto) Hpre2).

      constructor; auto.

    - (* Proc_CompAndSplit *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      do 2 rewrite map_app in Hpre1.
      do 2 rewrite Forall_app in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2 & Hpre1_3).

      (* Simplify Hpre2 *)
      apply Forall_and_inv in Hpre2.
      destruct Hpre2 as (Hpre2_1 & Hpre2_2).
      apply Forall_and_inv in Hpre2_2.
      destruct Hpre2_2 as (Hpre2_2 & Hpre2_3).

      (* Simplify IHHcp1, IHHcp2 *)
      cbn in IHHcp1, IHHcp2.
      rewrite Forall_cons_iff in IHHcp1, IHHcp2.
      rewrite map_app, Forall_app in IHHcp1, IHHcp2.
      specialize (IHHcp1 ltac:(repeat split; auto) ltac:(auto)).
      unfold styp_forbidden in IHHcp2; rewrite <- styp_forbidden_dual in IHHcp2.
      specialize (IHHcp2 ltac:(repeat split; auto) ltac:(auto)).
      rewrite map_app in IHHcp1, IHHcp2.

      do 2 rewrite map_app.
      eassert (H1 : map fst gamma = _).
      2: rewrite H1; constructor; auto.
      4: rewrite styp_subst_dual; auto.

      + rewrite map_map; cbn; auto.
      + rewrite map_map; cbn.
        rewrite Forall_forall; intros r Hr.
        rewrite in_map_iff in Hr.
        destruct Hr as (z & Hz1 & Hz2); subst r.
        rewrite Forall_forall in H.
        specialize (H _ ltac:(rewrite in_map_iff; eexists; split; try apply Hz2; auto)).
        destruct (snd z); try contradiction; cbn; auto.
      + unfold senv_disjoint; intros m; do 2 rewrite map_map; cbn; auto.

    - (* Proc_OutTyp *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify Hpre2 *)
      apply Forall_and_inv in Hpre2.
      destruct Hpre2 as (Hpre2_1 & Hpre2_2).
      apply Forall_and_inv in Hpre2_2.
      destruct Hpre2_2 as (Hpre2_2 & Hpre2_3).

      (* Simplify IHHcp *)
      cbn in IHHcp.
      rewrite Forall_cons_iff in IHHcp.

      destruct (pvn_eqb_spec v0 v).
      + (* Case 1: v is the quantified variable *)
        subst v.
        match type of IHHcp with (?P /\ _) -> _ => assert (H0 : P) end.
        { rewrite Forall_forall; intros z Hz.
          rewrite Forall_forall in Hpre2_1, Hpre2_2.
          apply styp_subst_forbidden; auto.
        }
        specialize (IHHcp ltac:(split; auto) ltac:(auto)).
        constructor; auto.

        (* If z is a free variable in (styp_subst v0 a e),
           it must either be a free variable in a (excluding v0), or it is a free variable in e.
           The first case is covered by H.
           The second case is covered by Hpre2_1.
         *)
        * rewrite Forall_forall; rewrite Forall_forall in H, Hpre2_1.
          intros z Hz.
          apply var_free_subst in Hz.
          destruct Hz as [(Hz & _) | Hz].
          -- specialize (H _ Hz); auto.
          -- specialize (Hpre2_1 _ Hz); auto.

        (* styp_subst v0 b (styp_subst v0 a e) = styp_subst v0 (styp_subst v0 b a) e *)
        * rewrite styp_subst_distr2; auto.

      + (* Case 2: v is not the quantified variable *)
        match type of IHHcp with (?P /\ _) -> _ => assert (H0 : P) end.
        { rewrite Forall_forall; intros z Hz.
          rewrite Forall_forall in Hpre1_1, Hpre2_1, Hpre2_2.
          specialize (Hpre1_1 _ Hz); specialize (Hpre2_1 _ Hz); specialize (Hpre2_2 _ Hz).
          pose proof (styp_forbidden_incl b v [] [v0] ltac:(apply incl_nil_l)).
          apply styp_subst_forbidden; auto.
        }
        specialize (IHHcp ltac:(split; auto) ltac:(auto)).

        constructor.

        (* If v does not appear free in b, then (styp_subst v b e) = b.
           In this case we simply show that all free variables that appear in (styp_subst v a e) can replace v0 in b.
           This is same as above and covered by H and Hpre2_1.

           If v appears free in b, then e cannot contain variable v0 by Hpre1_1.
           In this case we can show that (styp_forbidden (styp_subst v b e) v0) = (styp_forbidden b v0).
         *)
        * destruct (in_dec pvn_eq_dec v (fvar b)).
          -- assert (Hnin : ~ In v0 (fvar e)).
             { intros Hin; rewrite Forall_forall in Hpre1_1.
               apply Hpre1_1 in Hin.
               pose proof (styp_forbidden_bound b v v0 [v0] ltac:(auto) ltac:(left; auto)).
               auto.
             }
             unfold styp_forbidden; rewrite styp_forbidden_subst_no_free; auto.
             rewrite Forall_forall; intros z Hz.
             apply var_free_subst in Hz.
             rewrite Forall_forall in H, Hpre2_1.
             destruct Hz as [(Hz & _) | Hz]; auto.

          -- rewrite styp_subst_no_free_ident; auto.
             rewrite Forall_forall; intros z Hz.
             apply var_free_subst in Hz.
             rewrite Forall_forall in H, Hpre2_1.
             destruct Hz as [(Hz & _) | Hz]; auto.

        (* styp_subst v0 (styp_subst v b e) (styp_subst v a e) = styp_subst v (styp_subst v0 b a) e) *)
        * rewrite styp_subst_distr1; auto.

    - (* STyp_Forall *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (Hpre1_1 & Hpre1_2).
      cbn in Hpre1_1.

      (* Simplify IHHcp *)
      cbn in IHHcp.
      rewrite Forall_cons_iff in IHHcp.

      destruct (pvn_eqb_spec v0 v).
      + (* Case 1: v is the quantified variable *)
        subst v; clear Hpre2.
        (* v0 cannot appear free in any term in gamma *)
        erewrite map_ext_in.
        Unshelve.
        3: exact id.
        2: { intros t Hin.
             rewrite Forall_forall in H.
             destruct t; cbn.
             specialize (H s ltac:(rewrite in_map_iff; eexists; split; try apply Hin; auto)).
             rewrite styp_subst_no_free_ident; auto.
        }
        rewrite map_id; constructor; auto.

      + (* Case 2: v is not the quantified variable *)
        apply Forall_and_inv in Hpre2.
        destruct Hpre2 as (Hpre2_1 & Hpre2_2).
        match type of IHHcp with (?P /\ _) -> _ => assert (H0 : P) end.
        { rewrite Forall_forall; rewrite Forall_forall in Hpre1_1.
          intros z Hz; specialize (Hpre1_1 _ Hz).
          pose proof (styp_forbidden_incl a v [] [v0] ltac:(apply incl_nil_l)) as Hincl.
          intros Hin; apply Hincl in Hin; contradiction.
        }
        specialize (IHHcp ltac:(split; auto) ltac:(auto)).

        constructor; auto.
        rewrite map_map; cbn.
        rewrite Forall_forall; intros r Hr.
        rewrite in_map_iff in Hr.
        destruct Hr as (z & Hz1 & Hz2); subst r.
        rewrite Forall_forall in H.
        specialize (H (snd z) ltac:(rewrite in_map_iff; eexists; split; try apply Hz2; auto)).
        intros Hin.
        apply var_free_subst in Hin.
        destruct Hin as [(Hin & _) | Hin]; [contradiction|].
        rewrite Forall_forall in Hpre2_1.
        specialize (Hpre2_1 _ Hin); contradiction.

    - (* STyp_One *)
      cbn; intros _ _; constructor.

    - (* STyp_Bot *)
      cbn; intros Hpre1 Hpre2.

      (* Simplify Hpre1 *)
      rewrite Forall_cons_iff in Hpre1.
      destruct Hpre1 as (_ & Hpre1_2).

      (* Simplify IHHcp *)
      cbn in IHHcp.
      specialize (IHHcp Hpre1_2 Hpre2).

      constructor; auto.
      rewrite map_map; auto.

    - (* STyp_Top *)
      cbn; intros _ _.
      eassert (Heq : map fst gamma = _).
      2: rewrite Heq; constructor.
      1: rewrite map_map; cbn; auto.
      1: rewrite map_map; cbn; auto.
      unfold senv_valid; rewrite map_map; auto.

    - (* Permutation *)
      intros Hpre1 Hpre2.
      rewrite <- H in Hpre1.
      specialize (IHHcp Hpre1 Hpre2).
      eapply cp_perm.
      1: apply IHHcp.
      apply Permutation_map; auto.
  Qed.

End Wadler_Proc.
