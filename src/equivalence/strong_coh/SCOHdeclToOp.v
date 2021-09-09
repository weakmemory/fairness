Require Import Lia IndefiniteDescription Arith.
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import AuxProp.
Require Import Labels.
Require Import Events.
Require Import Execution.
Require Import View.
Require Import SCOHop.
Require Import CompactedTrace.
Require Import PropExtensionality.
Require Import TraceWf.

Set Implicit Arguments.

#[local]
Hint Resolve is_init_InitEvent : core.

Section DECL_to_OP.
  Variable G : execution.
  Hypothesis WF: Wf G.
  Variable nu : nat -> Event.
  Hypothesis ENUM : enumerates nu (acts G \₁ is_init).
  Hypothesis IMPL :
    forall i (LTi: lt_size i (acts G \₁ is_init))
           j (LTj: lt_size j (acts G \₁ is_init))
           (REL: hb G (nu i) (nu j)), i < j.
  Hypothesis COMPL : rf_complete G.
  Hypothesis CONS : scoh_consistent G.
  Hypothesis FAIR : mem_fair G.
  
  Hypothesis THRB :
    set_finite (fun t => exists x, acts G x /\ t = tid x).

  Lemma BOUND : bounded_threads G.
  Proof.
    set (AA:=THRB). apply  set_finite_nat_bounded in AA. desf.
    exists bound. ins. apply AA; eauto.
  Qed.

  (* In the paper, it is the function mapping eᵢ to i. *)
  Definition nu_inv (x : Event) : nat :=
    match excluded_middle_informative ((acts G \₁ is_init) x) with
    | left PF =>
      proj1_sig (constructive_indefinite_description
                   _ (proj2 (proj2 (proj1 (enumeratesE _ _) ENUM)) x PF))
    | right _ => 0
    end.

  Lemma nu_nu_inv x (ACTS: acts G x) (NI: ~ is_init x) : nu (nu_inv x) = x.
  Proof.
    unfold nu_inv, proj1_sig; unfolder; desf; try clear Heq;
      clarify_not; desf.
  Qed.

  Lemma nu_inv_nu n (LT: lt_size n (acts G \₁ is_init)) : nu_inv (nu n) = n.
  Proof.
    assert (X := ENUM); apply enumeratesE in X; desc.
    unfold nu_inv, proj1_sig; desf; try clear Heq;
      clarify_not; desf; eauto.
    all: apply RNG in LT; red in LT; desf.
  Qed.

  Lemma nu_inv_lt_size x (EE : (acts G \₁ is_init) x) :
    lt_size (nu_inv x) (acts G \₁ is_init).
  Proof.
    unfold nu_inv. desf.
    unfold proj1_sig. do 2 desf.
  Qed.

  Definition ev_ts_w n :=
    length (filterP (fun x => (co G) x n)
                    (undup (proj1_sig (constructive_indefinite_description
                                         _ (proj1 FAIR n))))).

  (* In the paper, it is called _tmap_. *)
  Definition ev_ts n :=
    ifP is_w n then ev_ts_w n
    else match excluded_middle_informative
                 ((acts G ∩₁ (fun a => is_r a)) n) with
         | left PF =>
           ev_ts_w (proj1_sig (constructive_indefinite_description
                                 _ (COMPL PF)))
         | right _ => 0
         end.

  Lemma ev_ts_w_init x : ev_ts_w (InitEvent x) = 0.
  Proof.
    unfold ev_ts_w, proj1_sig; desf; clear Heq.
    apply length_zero_iff_nil, filterP_eq_nil; ins.
    unfolder in COND; desf; eauto using co_init_r, rf_init_r.
  Qed.

  Lemma ev_ts_init x : ev_ts (InitEvent x) = 0.
  Proof.
    unfold ev_ts, ev_ts_w, proj1_sig; desf; clear Heq.
    apply length_zero_iff_nil, filterP_eq_nil; ins.
    unfolder in COND; desf; eauto using co_init_r, rf_init_r.
  Qed.

  Lemma rf_tsE x y :
    rf G x y -> ~ is_w y -> ev_ts x = ev_ts y.
  Proof.
    intros RF NWy.
    apply wf_rfD in RF; unfolder in RF; desf.
    apply wf_rfE in RF0; unfolder in RF0; desf.
    unfold ev_ts; desf; unfold proj1_sig; desf;
      unfolder in *; clarify_not; desf.
    f_equal; eapply (wf_rff WF); red; eauto.
  Qed.

  Lemma co_tsE x y :
    co G x y ->
    ev_ts x < ev_ts y.
  Proof.
    intro CO; apply wf_coD in CO; unfolder in CO; desf.
    unfold ev_ts; desf; unfold ev_ts_w.
    do 2 destruct (constructive_indefinite_description); ins.
    assert (H := CO0).
    eapply i1, in_undup_iff, In_NoDup_Permutation in H; desf.
    rewrite H; ins; desf; ins.
    rewrite Nat.lt_succ_r; ins.
    eapply NoDup_incl_length; auto with hahn.
    red; ins; in_simp.
    assert (CO': co G a y) by eauto using (co_trans WF).
    specialize (i1 _ CO'); rewrite <- in_undup_iff, H in i1; ins; desf.
    edestruct (co_irr WF); eauto.
  Qed.

  Lemma rf_tsE_gen x y :
    rf G x y -> ev_ts x <= ev_ts y.
  Proof.
    ins. destruct (classic (is_w y)) as [WY|NWY].
    2: { eapply rf_tsE in NWY; eauto. lia. }
    enough (ev_ts x < ev_ts y); [lia|].
    eapply co_tsE. apply rf_w_in_co; auto.
    basic_solver.
  Qed.

  Lemma co_tsE_alt :
    co G ≡
       fun x y => 
         ⟪ EX : acts G x ⟫ /\
         ⟪ WX : is_w x ⟫ /\
         ⟪ EY : acts G y ⟫ /\
         ⟪ WY : is_w y ⟫ /\
         ⟪ SL : loc x = loc y ⟫ /\
         ⟪ LTTS : ev_ts x < ev_ts y ⟫.
  Proof.
    unfolder.
    split; intros x y HH; desf.
    { apply (wf_coE WF) in HH. unfolder in HH. desf.
      apply (wf_coD WF) in HH0. unfolder in HH0. desf.
      set (AA:=HH2). apply (wf_col WF) in AA.
      splits; auto. by apply co_tsE. }
    assert (x <> y) as NEQ.
    { intros UU. desf. lia. }
    eapply wf_co_total in NEQ; eauto.
    2,3: eby unfolder; splits.
    desf. exfalso. apply co_tsE in NEQ. lia.
  Qed.

  Lemma fr_tsE x y :
    fr G x y -> ev_ts x < ev_ts y.
  Proof.
    destruct (classic (is_w x)) as [WX|NWX]; intros FR.
    { apply co_tsE.
      apply w_fr_in_co; auto.
      { apply scoh_rmw_atomicity; auto. }
      basic_solver. }
    apply wf_frD in FR; unfolder in FR; desf.
    red in FR0. unfolder in FR0. desf.
    rewrite <- (rf_tsE _ _ FR0); auto. by apply co_tsE.
  Qed.

  Lemma fr_tsE_alt :
    fr G ≡
       fun x y => 
         ⟪ EX : acts G x ⟫ /\
         ⟪ RX : is_r x ⟫ /\
         ⟪ EY : acts G y ⟫ /\
         ⟪ WY : is_w y ⟫ /\
         ⟪ SL : loc x = loc y ⟫ /\
         ⟪ LTTS : ev_ts x < ev_ts y ⟫.
  Proof.
    unfolder.
    split; intros x y HH; desf.
    { apply (wf_frE WF) in HH. unfolder in HH. desf.
      apply (wf_frD WF) in HH0. unfolder in HH0. desf.
      set (AA:=HH2). apply (wf_frl WF) in AA.
      splits; auto. by apply fr_tsE. }
    set (AA:=RX). edestruct COMPL with (x:=x) as [w RF].
    { basic_solver. }
    red. split.
    2: { unfolder. intros HH. desf. lia. }
    exists w. split; auto.
    apply (wf_rfD WF) in RF. unfolder in RF. desf.
    apply (wf_rfE WF) in RF0. unfolder in RF0. desf.
    set (BB:=RF2). apply (wf_rfl WF) in BB.
    apply co_tsE_alt. splits; auto.
    { by rewrite BB. }
    apply rf_tsE_gen in RF2. lia.
  Qed.

  (* Lemma hb_ww_tsE x y *)
  (*       (HB : hb G x y) *)
  (*       (WX : is_w x) (WY : is_w y) *)
  (*       (LL : loc x = loc y) : *)
  (*   ev_ts x < ev_ts y. *)
  (* Proof. *)
  (*   apply (wf_hbE WF) in HB. unfolder in HB. desf. *)
  (*   assert (x <> y) as NEQ. *)
  (*   { intros HH; subst. eapply hb_irr; eauto. } *)
  (*   edestruct wf_co_total as [|AA]; eauto. *)
  (*   1,2: eby unfolder; splits. *)
  (*   { by apply co_tsE. } *)
  (*   exfalso. *)
  (*   cdes CONS. eapply CONS0. generalize HB0 AA. basic_solver 10. *)
  (* Qed. *)

  (* Lemma hb_tsE x y *)
  (*       (HB : hb G x y) *)
  (*       (WX : is_w x) *)
  (*       (LL : loc x = loc y) : *)
  (*   ev_ts x <= ev_ts y. *)
  (* Proof. *)
  (*   apply (wf_hbE WF) in HB. unfolder in HB. desf. *)
  (*   assert (exists w, ((hb G) ⨾ ((rf G)⁻¹)^?) x w /\ is_w w /\ acts G w /\ *)
  (*                     ev_ts y = ev_ts w /\ loc w = loc y) *)
  (*     as [w [AA [BB [CC [DD FF]]]]]. *)
  (*   { destruct (classic (is_w y)) as [WY|NWY]. *)
  (*     { exists y. split; auto. generalize HB0. basic_solver. } *)
  (*     destruct (r_or_w y) as [RY|WY]. *)
  (*     2: by intuition. *)
  (*     assert (exists w, rf G w y) as [w RF]. *)
  (*     { apply COMPL. by split. } *)
  (*     exists w. *)
  (*     apply (wf_rfE WF) in RF. unfolder in RF. desf. *)
  (*     apply (wf_rfD WF) in RF0. unfolder in RF0. desf. *)
  (*     splits; auto. *)
  (*     { generalize RF2 HB0. basic_solver. } *)
  (*     { symmetry. by apply rf_tsE. } *)
  (*       by apply (wf_rfl WF). } *)
  (*   rewrite DD. *)
  (*   destruct (classic (x = w)) as [|NEQ]; subst; auto. *)
  (*   apply Nat.lt_le_incl. *)
  (*   edestruct wf_co_total as [|EE]; eauto. *)
  (*   1,2: eby unfolder; splits. *)
  (*   { by apply co_tsE. } *)
  (*   exfalso. *)
  (*   cdes CONS. eapply CONS0 with (x:=x). *)
  (*   unfolder in AA. desf. *)
  (*   { generalize AA EE. basic_solver 10. } *)
  (*   enough (fr G z x) as GG. *)
  (*   { generalize AA GG. basic_solver 10. } *)
  (*   red. split. *)
  (*   { generalize AA0 EE. basic_solver. } *)
  (*   unfolder. intros HH; desf. *)
  (*   eapply hb_irr; eauto. *)
  (* Qed. *)

  Lemma co_imm_tsE x y :
    immediate (co G) x y -> S (ev_ts x) = ev_ts y.
  Proof.
    intros [CO IMM]; apply wf_coD in CO; unfolder in CO; desf.
    unfold ev_ts; desf; unfold ev_ts_w.
    do 2 destruct (constructive_indefinite_description); ins.
    assert (H := CO0).
    eapply i1, in_undup_iff, In_NoDup_Permutation in H; desf.
    rewrite H; ins; desf; ins.
    f_equal.
    apply Permutation_length, NoDup_Permutation; eauto with hahn.
    eapply nodup_filterP, nodup_consD, Permutation_NoDup; eauto.
    intro z; in_simp; split; ins; desc.
    - assert (X: co G z y) by eauto using (co_trans WF).
      split; ins; desf; eapply i1, in_undup_iff in X.
      rewrite H in X; ins; desf; eauto.
      exfalso; eauto using (co_irr WF).
    - destruct (classic (z = x)) as [|NEQ]; desf.
      hahn_rewrite (wf_coE WF) in CO0; unfolder in CO0; desf.
      hahn_rewrite (wf_coD WF) in CO2; unfolder in CO2; desc.
      hahn_rewrite (wf_coE WF) in H2; unfolder in H2; desf.
      hahn_rewrite (wf_coD WF) in H3; unfolder in H3; desc.
      eapply (wf_co_total WF) in NEQ; unfolder; ins.
      desf; solve [eauto | exfalso; eauto].
      eapply (wf_col WF) in CO4.
      eapply (wf_col WF) in H5; unfold same_loc in *; splits; ins;
        congruence.
  Qed.

  Lemma rf_rmw_tsE x y (RF : rf G x y) (Wy : is_w y) :
    S (ev_ts x) = ev_ts y.
  Proof.
    ins; apply co_imm_tsE.
    assert (L := wf_rfl WF _ _ RF); unfold same_loc, loc in *; ins; clarify.
    assert (V := wf_rfv WF _ _ RF); unfold valw, valr in *; ins; clarify.
    apply (wf_rfE WF) in RF; unfolder in RF; desf.
    apply (wf_rfD WF) in RF0; unfolder in RF0; desf.
    cdes CONS.
    destruct (classic (x = y)) as [|NEQ]; desf.
    { exfalso. eapply CONS0 with (x:=y).
      apply ct_step.  generalize RF2. basic_solver. }
    eapply (wf_co_total WF) in NEQ; unfolder; ins; desf.
    { split; auto. ins. eapply CONS1. basic_solver 10. }
    exfalso. eapply CONS0.
    apply ct_ct; eexists; split; apply ct_step; generalize RF2 NEQ; basic_solver.
  Qed.
  
  Lemma co_ts x y :
    co G x y <-> acts G x /\ acts G y /\ is_w x /\ is_w y /\
                 loc x = loc y /\ ev_ts x < ev_ts y.
  Proof.
    split; ins; desc.
      hahn_rewrite (wf_coE WF) in H;
        hahn_rewrite (wf_coD WF) in H; unfolder in H; desf; splits; ins;
          eauto using co_tsE.
      eapply wf_col; eauto.
    destruct (classic (x = y)) as [|NEQ]; desf; try lia.
    eapply (wf_co_total WF) in NEQ; desf; ins.
    eapply co_tsE in NEQ; lia.
  Qed.


  Lemma ts_uniq x y :
    acts G x -> acts G y -> is_w x -> is_w y ->
    loc x = loc y ->
    ev_ts x = ev_ts y ->
    x = y.
  Proof.
    ins; apply NNPP; intro NEQ.
    eapply wf_co_total in NEQ; unfolder; eauto.
    desf; apply co_tsE in NEQ; lia.
  Qed.
  
  (** Safe points **)
  Definition safepoints w :=
    let f := fun e => 
               ⟪ TL   : ev_ts e < ev_ts w
                        (* Required for updates. *)
                        \/ e = w ⟫ /\
               ⟪ LOC  : loc e = loc w ⟫
    in
    set_compl (dom_rel ((hb G)^? ⨾ ⦗f⦘)).
  
  Lemma safepoints_irr e : ~ safepoints e e.
  Proof. intros AA. apply AA. exists e. basic_solver. Qed.

  Lemma safepoint_hb_mon w :
    codom_rel (⦗safepoints w⦘ ⨾ hb G) ⊆₁ safepoints w.
  Proof.
    unfold safepoints.
    intros x [y HH] AA. apply seq_eqv_l in HH. destruct HH as [BB HB].
    apply BB. generalize AA HB (@hb_trans G). basic_solver 10.
  Qed.

  (** tslot: Time slot for message's propagation **)
  Definition tslot t w :=
    match excluded_middle_informative
            (acts G w /\ is_w w /\ ~ is_init w /\
             t <> 0 /\
             (exists et, acts G et /\ tid et = t)) with
    | left B =>
      let P := fun n =>
                 ⟪ LT  : nu_inv w <= n ⟫ /\
                 ⟪ SP  : forall m (GT : n < m) (EM : lt_size m (acts G \₁ is_init))
                                (TIDT : tid (nu m) = t),
                     safepoints w (nu m) ⟫ in
      let minP := fun n => forall m (PM : P m), n <= m in
      match excluded_middle_informative (exists n, P n /\ minP n) with
      | left A  => Some (proj1_sig (constructive_indefinite_description _ A))
      | right _ => None
      end
    | _ => None
    end.

  Lemma tslot_defined_only_for_w t w m
        (TS : Some m = tslot t w) :
    is_w w.
  Proof. unfold tslot in *. desf; desf. Qed.

  Lemma tslot_defined_only_for_non_init t e m
        (TS : Some m = tslot t e) :
    t <> 0.
  Proof. unfold tslot in *. desf; desf. Qed.

  Lemma tslot_defined_only_for_non_init_e t e m
        (TS : Some m = tslot t e) :
    ~ is_init e.
  Proof. unfold tslot in *. desf; desf. Qed.

  Lemma tslot_defined_only_for_E t w m
        (TS : Some m = tslot t w) :
    acts G w.
  Proof. unfold tslot in *. desf; desf. Qed.

  Lemma tslot_defined_only_for_non_empty_threads t w m
        (TS : Some m = tslot t w) :
    exists e, acts G e /\ tid e = t.
  Proof. unfold tslot in *. desf; desf; eauto. Qed.
  
(*   Lemma tslot_is_safepoint t w m *)
(*         (TS : Some m = tslot t w) : *)
(*     safepoints w (nu m). *)
(*   Proof. *)
(*     unfold tslot in *. do 2 desf. *)
(*     unfold proj1_sig. do 2 desf. clear Heq. *)
(* desf. *)
(*     { rewrite nu_nu_inv; auto. *)
(*       red. intros HH. desc. *)
(*       assert (hb G w e) as HBWE. *)
(*       { generalize INHB (@hb_trans G) (@sb_in_hb G). *)
(*         basic_solver. } *)
(*       apply hb_tsE in HBWE; auto. desf. *)
(*       { lia. } *)
(*       destruct INHB as [x HH]. apply seq_eqv_l in HH. desf. *)
(*       eapply hb_irr with (x:=x); eauto. generalize HH0 (@sb_in_hb G) (@hb_trans G). *)
(*       basic_solver. } *)
(*     red. intros HH. desc. *)
(*     destruct INHB as [x AA]. *)
(*     apply seq_eqv_l in AA. destruct AA as [XX AA]. *)
(*     enough (safepoints w x) as BB. *)
(*     { clear XX. apply BB. eexists. splits; eauto. *)
(*       exists x. basic_solver. } *)
(*     clear dependent e0. subst. *)
(*     unfold proj1_sig. do 2 desf. *)
(*   Qed. *)

  Lemma tslot_lt_index t w n 
        (TS : Some n = tslot t w) :
    nu_inv w <= n.
  Proof.
    unfold tslot in *. do 2 desf.
    unfold proj1_sig. do 2 desf.
  Qed.
  
  (* Lemma no_sb_is_safepoint w e *)
  (*       (NSB : codom_rel (⦗eq e⦘ ⨾ sb G) ⊆₁ ∅) : *)
  (*   safepoints w e. *)
  (* Proof. *)
  (*   red. intros HH. desc. *)
  (*   generalize NSB INHB. basic_solver. *)
  (* Qed. *)

  Lemma sb_nu n (Ln : lt_size n (acts G \₁ is_init))
        m (Lm : lt_size m (acts G \₁ is_init)) :
    sb G (nu n) (nu m) <->
    tid (nu n) = tid (nu m) /\ index (nu n) < index (nu m).
  Proof.
    assert (X := ENUM); apply enumeratesE in X; desc.
    unfold sb; split; ins; unfolder in *; desc.
    all: unfold ext_sb in *; desf; ins; desf; try lia.
    { eapply RNG in Ln; desf; destruct (nu n); ins; ins. }
    all: splits; ins; rewrite <- ?Heq, <- ? Heq0; apply RNG; ins.
  Qed.

  Lemma sb_nu_alt n (Ln : lt_size n (acts G \₁ is_init))
        m (Lm : lt_size m (acts G \₁ is_init))
        (TID : tid (nu m) = tid (nu n)) :
    index (nu m) < index (nu n) <-> m < n.
  Proof.
    assert (X := ENUM); apply enumeratesE in X; desc.
    split; intro X.
    apply IMPL; eauto using lt_lt_size.
    apply t_step, or_introl, sb_nu; ins.
    destruct (lt_eq_lt_dec (index (nu m)) (index (nu n))) as [[|EQ]|LT]; ins; try lia.
      assert (m = n); desf; try lia.
      apply INJ; ins; apply (wf_index WF); splits; ins; try apply RNG; ins.
    assert (n < m); try lia.
    eapply IMPL; ins; apply t_step, or_introl, sb_nu; ins.
  Qed.

  Lemma sb_nu_lt n (Ln : lt_size n (acts G \₁ is_init))
        m (Lm : lt_size m (acts G \₁ is_init)) :
    sb G (nu n) (nu m) <->
    tid (nu n) = tid (nu m) /\ n < m.
  Proof.
    etransitivity.
    { apply sb_nu; auto. }
    split; intros [BB CC]; split; auto.
    all: apply sb_nu_alt; auto.
  Qed.

  Lemma tslot_defined t w
        (TNINIT : t <> 0)
        (ACT : acts G w)
        (NINIT : ~ is_init w)
        (WW : is_w w)
        (TNEMPTY : exists e, acts G e /\ tid e = t) :
    exists m, tslot t w = Some m.
  Proof.
    assert (forall e, acts G e /\ tid e = t -> ~ is_init e) as GNINIT.
    { intros e [GE TE]. rewrite <- TE in TNINIT.
      intros HH. rewrite <- wf_tid_init in HH; eauto. }
    desf. unfold tslot. desf; eauto.
    2: { exfalso. apply n. splits; eauto. }
    exfalso. rename n into AA. apply AA.
    enough (exists n : nat,
               (nu_inv w <= n /\
                forall m : nat,
                  n < m -> tid (nu m) = tid e -> lt_size m (acts G \₁ is_init) ->
                  safepoints w (nu m)))
      as HH'.
    { desf. eapply set_nat_exists_min with (n:=n); splits; eauto. }
    clear a. clear AA.
    destruct (classic (exists j,
                          ⟪ JGE  : nu_inv w < j ⟫ /\
                          ⟪ GEJ  : lt_size j (acts G \₁ is_init) ⟫ /\
                          ⟪ TMJ  : tid (nu j) = tid e ⟫ /\
                          ⟪ NSFJ : ~ safepoints w (nu j) ⟫)) as [|NEX].
    2: { exists (nu_inv w). splits; auto. ins. apply NNPP. intros HH.
         apply NEX; eauto. }
    desf.
    set (TT:=ENUM). rewrite enumeratesE in TT. desf.
    assert (acts G (nu j)) as NUJE.
    { by apply RNG. }
    destruct (classic (set_finite (acts G \₁ is_init))) as [FIN|INF].
    { edestruct @set_finite_r_min_precise_bounded
        with (A:=Event)
             (s:=(acts G ∩₁ (fun x => tid x = tid e) ∩₁ (fun x => nu_inv w < nu_inv x)))
             (r:=(sb G)⁻¹)
             (n:=nu j) as [bound].
      { eapply set_finite_mori; [|by apply FIN].
        red. basic_solver. }
      { apply transitive_transp. by apply sb_trans. }
      { by apply sb_irr. }
      { unfolder. splits; auto. by rewrite nu_inv_nu. }
      desf.
      unfolder in INS. desf.
      exists (nu_inv bound).
      splits; auto.
      { lia. }
      intros m LTT TIDM LTM. exfalso.
      assert (acts G (nu m)) as ME by (by apply RNG).
      assert (~ is_init (nu m)) as NINIM; auto.
      edestruct same_thread with (x:=bound) (y:=nu m) as [[EQ|SB]|SB]; eauto; subst.
      { by rewrite INS1. }
      { rewrite nu_inv_nu in LTT; auto. lia. }
      { eapply BND; eauto. unfolder. splits; auto.
        rewrite nu_inv_nu; auto. lia. }
      apply sb_in_hb in SB. rewrite <- nu_nu_inv with (x:=bound) in SB; auto.
      eapply IMPL in SB; auto.
      { lia. }
      apply nu_inv_lt_size. split; auto. }
    destruct (classic
                (set_finite
                   (fun n => (acts G ∩₁ (fun x => tid x = tid e)) (nu n))))
      as [SF|NSF].
    { assert (set_finite (acts G ∩₁ (fun x => tid x = tid e))) as AA.
      { red in SF. desf.
        exists (map nu findom). ins.
        assert (acts G x) by apply IN.
        assert (~ is_init x).
        { apply GNINIT. apply IN. }
        rewrite <- nu_nu_inv with (x:=x); auto.
        apply in_map. apply SF.
        rewrite nu_nu_inv with (x:=x); auto. }
      eapply set_finite_r_min_precise_bounded with (r:=(sb G)⁻¹) (n:=nu j) in AA.
      4: by split.
      3: by apply sb_irr.
      2: { apply transitive_transp. by apply sb_trans. }
      desf.
      unfolder in INS. desf.
      destruct (SUR bound) as [nbound].
      { split; auto. }
      desf. exists nbound.
      assert (~ dom_rel (sb G) (nu nbound)) as NSB.
      { intros [y SB].
        assert (tid y = tid e).
        { apply sb_tid_init in SB. desf; intuition.
          red in SB. desf. ins. intuition. }
        eapply BND; eauto. split; auto.
        apply (@wf_sbE G) in SB. unfolder in SB. desf. }
      splits; auto.
      2: { red. ins. intros HH. desc.
           assert (acts G (nu m)) as EGM.
           { by apply RNG. }
           assert (sb G (nu nbound) (nu m)) as SB.
           { apply sb_nu_lt; auto. rewrite INS0. split; auto. }
           generalize SB NSB. basic_solver. }
      apply Nat.le_ngt; intros AA.
      assert (sb G (nu nbound) (nu j)) as SB.
      { apply sb_nu_lt; auto. rewrite INS0. split; auto. lia. }
      generalize SB NSB. basic_solver. }
    apply not_all_not_ex.
    intros HH.
    remember (fun e =>
                (acts G \₁ is_init) e /\
                ev_ts e < ev_ts w /\
                loc e = loc w) as ff.
    enough (~ set_finite ff) as PR.
    { apply PR. eapply set_finite_more with (y:=(is_r ∪₁ is_w) ∩₁ ff).
      { generalize r_or_w. basic_solver. }
      rewrite set_inter_union_l. eapply set_finite_union.
      cdes FAIR. apply and_comm.
      rewrite co_tsE_alt in FAIR0.
      rewrite fr_tsE_alt in FAIR1.
      split.
      { eapply set_finite_mori; [|by apply FAIR0 with (y:=w)].
        subst ff. red. basic_solver. }
      eapply set_finite_mori; [|by apply FAIR1 with (y:=w)].
      subst ff. red. basic_solver. }
    intros SF.
    assert (set_finite (fun n => ff (nu n))) as SFNU.
    { red in SF. desf. exists (map nu_inv findom).
      ins. desf.
      arewrite (x = nu_inv (nu x)).
      { rewrite nu_inv_nu; auto. apply lt_size_infinite; auto. }
      apply in_map. apply SF. by splits. }
    apply set_finite_nat_bounded in SFNU. destruct SFNU as [bound SFNU].
    eapply set_infinite_nat_exists_bigger
      with (n:=1+bound+j) in NSF.
    destruct NSF as [m [LT [GM TT]]]. unnw.
    specialize (HH m). apply HH. splits; auto.
    { lia. }
    ins. red. intros [e0 AA]. apply seq_eqv_r in AA. desc.
    assert (~ is_init (nu m0)) as NINITM0.
    { by apply RNG. }
    assert (~ is_init e0) as NINIT'.
    { destruct AA as [|HB]; desf. apply no_hb_to_init in HB; auto. unfolder in HB. desf. }
    assert ((acts G \₁ is_init) (nu m0)) as ACTNINTIM0 by (by apply RNG).
    assert ((acts G \₁ is_init) e0) as ACTNINITE0.
    { destruct AA as [|HB]; desf.
      split.
      2: by apply no_hb_to_init in HB; auto.
      apply (wf_hbE WF) in HB. unfolder in HB. desf. }
    assert (acts G e0) by apply ACTNINITE0.
    assert (m0 <= nu_inv e0) as LTT.
    { destruct AA as [|HB]; desc; subst.
      { rewrite nu_inv_nu; auto. }
      apply Nat.lt_le_incl.
      rewrite <- nu_inv_nu with (n:=m0); auto.
      apply IMPL; auto.
      all: try rewrite nu_inv_nu; auto.
      all: try rewrite nu_nu_inv; auto.
      apply nu_inv_lt_size; auto. }
    desf.
    2: lia.
    enough (nu_inv e0 <= bound).
    { lia. }
    apply Nat.lt_le_incl. apply SFNU.
    rewrite nu_nu_inv; auto.
  Qed.

  Hint Resolve hb_irr : hahn.

  Lemma hb_preds y :
    set_finite (fun x => (hb G)^? x y /\ ~ is_init x).
  Proof.
    forward eapply fsupp_hb as X; eauto with hahn.
    { eapply has_finite_antichains_sb; ins.
      apply BOUND. }
    specialize (X y); desf.
    exists (y :: findom); unfolder in *; ins; desf; eauto 6.
  Qed.

  Lemma sbrf_preds y :
    set_finite (fun x => ((rf G)^? ;; (sb G)^?) x y /\ ~ is_init x).
  Proof.
    eapply set_finite_mori.
    2: by apply (hb_preds y).
    assert (((rf G)^? ⨾ (sb G)^?) ⊆ (hb G)^?) as AA.
    { unfold hb. rewrite cr_of_ct.
      rewrite <- rt_cr. rewrite <- inclusion_r_rt with (r:=sb G ∪ rf G).
      all: basic_solver 10. }
    red. intros x HH. desf. apply AA in HH. basic_solver.
  Qed.
  
  (* In the paper, it is called _vmap_. *)
  Definition ev_view e l :=
    max_of_list
      (map
         ev_ts
         (filterP
            (fun a => is_w a /\ loc a = l)
            (proj1_sig
               (constructive_indefinite_description
                  _ ((proj1 (set_finiteE _) (sbrf_preds e))))))).

  Lemma ev_view_includes x y :
    ((rf G)^? ;; (sb G)^?) x y -> is_w x -> ev_ts x <= ev_view y (loc x).
  Proof.
    unfold ev_view.
    destruct (constructive_indefinite_description); ins.
    destruct (classic (is_init x)) as [INITx|NIx].
    destruct x; ins; rewrite ev_ts_init; lia.
    desf. destruct a0 as [a0 i].
    specialize_full i; eauto. red in i.
    apply in_max_of_list. in_simp.
    exists x. splits; auto.
    in_simp. auto.
  Qed.
  
  (* TODO: move to a more appropriate place *)
  Lemma rfsb_sb : (rf G)^? ⨾ (sb G)^? ;; (sb G) ⊆ (rf G)^? ⨾ (sb G)^?.
  Proof using.
    arewrite ((sb G)^? ⨾ sb G ⊆ sb G).
    { generalize (@sb_trans G). basic_solver. }
    basic_solver 10.
  Qed.

  (* TODO: move to a more appropriate place *)
  Lemma rfsb_in_hb : (rf G)^? ⨾ (sb G)^? ⊆ (hb G)^?.
  Proof using.
    unfold hb. rewrite cr_of_ct. rewrite <- rt_rt.
    rewrite <- inclusion_r_rt with (r:=sb G ∪ rf G); [|done].
    basic_solver 10.
  Qed.

  Lemma sb_viewE x y :
    sb G x y -> view_le (ev_view x) (ev_view y).
  Proof.
    unfold ev_view.
    ins. do 2 destruct (constructive_indefinite_description); intros. ins.
    desf.
    intro l; apply incl_max_of_list; red; ins; in_simp.
    exists x2. splits; auto.
    in_simp. splits; auto. apply a1. apply a2 in H1.
    desf. splits; auto.
    apply rfsb_sb. apply seqA. eexists; eauto.
  Qed.

  Lemma sb_hb_preds y :
    set_finite (fun x => (sb G ⨾ (hb G)^?) x y /\ ~ is_init x).
  Proof.
    eapply set_finite_mori.
    2: by apply hb_preds with (y:=y).
    assert (sb G ⨾ (hb G)^? ⊆ (hb G)^?) as AA.
    { rewrite sb_in_hb. generalize hb_trans. basic_solver. }
    red. generalize AA. basic_solver 10.
  Qed.
  
  Lemma tslot_dom_finite_lt n :
    set_finite (fun tw =>
                  exists m,
                    Some m = tslot (fst tw) (snd tw) /\
                    m < n).
  Proof.
    set (AA:=BOUND). destruct AA as [nt AA].
    exists (list_prod (List.seq 0 nt)
                      (map nu (List.seq 0 (S n)))).
    ins. desf. destruct x as [t w]. ins.
    apply in_prod_iff. split.
    { apply in_seq0_iff.
      edestruct tslot_defined_only_for_non_empty_threads; eauto.
      desf. by apply AA. }
    assert (~ is_init w) as NINIT.
    { eapply tslot_defined_only_for_non_init_e; eauto. }
    assert (acts G w) as EW.
    { eapply tslot_defined_only_for_E; eauto. }
    rewrite <- nu_nu_inv with (x:=w); auto.
    in_simp. eexists. splits; eauto.
    apply in_seq0_iff.
    apply tslot_lt_index in IN. lia.
  Qed.

  Lemma tslot_dom_finite n :
    set_finite (fun tw => Some n = tslot (fst tw) (snd tw)).
  Proof.
    eapply set_finite_mori.
    2: by apply tslot_dom_finite_lt.
    red. basic_solver.
  Qed.

  Lemma tslot_w_dom_finite_lt t n :
    set_finite (fun w =>
                  exists m,
                    Some m = tslot t w /\
                    m < n).
  Proof.
    exists (map nu (List.seq 0 (S n))).
    ins. desf. ins.
    assert (~ is_init x) as NINIT.
    { eapply tslot_defined_only_for_non_init_e; eauto. }
    assert (acts G x) as EW.
    { eapply tslot_defined_only_for_E; eauto. }
    rewrite <- nu_nu_inv with (x:=x); auto.
    in_simp. eexists. splits; eauto.
    apply in_seq0_iff.
    apply tslot_lt_index in IN. lia.
  Qed.

  Definition props_before t n :=
    proj1_sig
      (constructive_indefinite_description
         _ ((proj1 (set_finiteE _) (tslot_w_dom_finite_lt t n)))).

  (* In the paper, it is called _vmap-propagate_. *)
  Definition ev_view_prop e l : nat :=
    let n := nu_inv e in
    max_of_list
      (map ev_ts (filterP (fun w => loc w = l)
                          (props_before (tid e) n))).

  Lemma props_before_sb_mon x y z (SB : sb G x y)
        (IN : In z (props_before (tid x) (nu_inv x))) :
    In z (props_before (tid y) (nu_inv y)).
  Proof.
    assert (acts G x /\ acts G y) as [EX EY].
    { apply wf_sbE in SB; auto. unfolder in SB. desf. }
    unfold props_before, proj1_sig in *. do 2 desf. clear Heq Heq0.
    apply a2 in IN. desf. apply a1. splits; auto.
    clear dependent x0. clear dependent x1.
    assert (tid x <> 0) as TIDXNINIT.
    { eapply tslot_defined_only_for_non_init; eauto. }
    assert (~ is_init x) as NINITX.
    { unfold is_init. desf. }
    assert (tid y = tid x) as TEQ.
    { apply sb_tid_init in SB. desf. }
    assert (~ is_init y) as NINITY.
    { unfold is_init. desf. ins. auto. }
    rewrite TEQ.
    exists m. splits; auto.
    enough (nu_inv x < nu_inv y); [lia|].
    apply IMPL.
    1,2: by apply nu_inv_lt_size; split; auto.
    apply sb_in_hb. do 2 (rewrite nu_nu_inv; auto).
  Qed.

  Lemma props_before_index_mon t x y z (LE : x <= y)
        (IN : In z (props_before t x)) :
    In z (props_before t y).
  Proof.
    unfold props_before, proj1_sig in *. do 2 desf. clear Heq Heq0.
    apply a2 in IN. desf. apply a1. splits; auto.
    clear dependent x0. clear dependent x1.
    eexists. splits; eauto. lia.
  Qed.

  Lemma tslot_gt_is_safepoint t w m n
        (TS : Some m = tslot t w)
        (ACT : lt_size n (acts G \₁ is_init))
        (TT : tid (nu n) = t)
        (LT : m < n) :
    safepoints w (nu n).
  Proof.
    unfold tslot in TS. do 2 desf. unfold proj1_sig in LT. do 2 desf. clear Heq.
    apply SP0; auto.
  Qed.

  Lemma props_before_hb_mon x y z (HB : hb G x y)
        (IN : In z (props_before (tid x) (nu_inv x))) :
    In z (props_before (tid y) (nu_inv y)).
  Proof.
    assert (acts G x /\ acts G y) as [EX EY].
    { apply wf_hbE in HB; auto. unfolder in HB. desf. }
    unfold props_before, proj1_sig in *. do 2 desf. clear Heq Heq0.
    apply a2 in IN. desf. apply a1. splits; auto.
    clear dependent x0. clear dependent x1.
    assert (tid x <> 0) as TIDXNINIT.
    { eapply tslot_defined_only_for_non_init; eauto. }
    assert (~ is_init x) as NINITX.
    { unfold is_init. desf. }
    assert (~ is_init y) as NINITY.
    { intros HH. eapply hb_init_r; eauto. }
    assert (tid y <> 0) as TIDYNINIT.
    { intros HH. apply (wf_tid_init WF) in HH; auto. }
    assert (lt_size (nu_inv x) (acts G \₁ is_init)) as LTNUINVX.
    { apply nu_inv_lt_size. split; auto. }
    assert (lt_size (nu_inv y) (acts G \₁ is_init)) as LTNUINVY.
    { apply nu_inv_lt_size. split; auto. }
    assert (acts G z) as EZ.
    { eapply tslot_defined_only_for_E; eauto. }
    assert (is_w z) as WZ.
    { eapply tslot_defined_only_for_w; eauto. }
    assert (~ is_init z) as NINITZ.
    { eapply tslot_defined_only_for_non_init_e; eauto. }
    assert (lt_size (nu_inv z) (acts G \₁ is_init)) as LTNUINVZ.
    { apply nu_inv_lt_size. split; auto. }
    assert (nu_inv x < nu_inv y) as NUINVLT.
    { apply IMPL.
      1,2: by apply nu_inv_lt_size; split; auto.
      do 2 (rewrite nu_nu_inv; auto). }
    assert (safepoints z x) as SFZX.
    { rewrite <- nu_nu_inv with (x:=x); auto.
      eapply tslot_gt_is_safepoint with (m:=m); eauto.
      rewrite nu_nu_inv; auto. }
    assert (safepoints z y) as SFZY.
    { eapply safepoint_hb_mon. exists x. basic_solver. }

    unfold tslot in IN. do 2 desf.
    unfold proj1_sig in IN0. do 2 desf. clear Heq.
    clear dependent n.
    unfold tslot. desf.
    3: { exfalso. apply n. splits; eauto. }
    2: { exfalso. desf. apply n. eapply set_nat_exists_min with (n:=nu_inv y).
         splits; eauto.
         { lia. }
         ins.
         assert (sb G y (nu m)) as SB.
         { rewrite <- nu_nu_inv with (x:=y); auto.
           apply sb_nu_lt; auto.
           rewrite nu_nu_inv; auto. }
         intros AA. apply SP0 with (m:=nu_inv x); auto.
         all: rewrite nu_nu_inv; auto.
         apply sb_in_hb in SB.
         generalize HB SB (@hb_trans G) AA. basic_solver 10. }
    eexists. splits; eauto. unfold proj1_sig. do 2 desf. clear Heq.
    enough (x1 <= Nat.pred (nu_inv y)); [lia|].
    apply a13. splits; [lia|].
    ins.
    destruct (classic (m = nu_inv y)) as [|NEQ]; subst.
    { rewrite nu_nu_inv; auto. }
    assert (sb G y (nu m)) as SB.
    { rewrite <- nu_nu_inv with (x:=y); auto.
      apply sb_nu_lt; auto.
      rewrite nu_nu_inv; auto. split; auto. lia. }
    apply sb_in_hb in SB.
    eapply safepoint_hb_mon. exists y. basic_solver.
  Qed.

  Lemma hb_view_propE x y (HB : hb G x y) :
    view_le (ev_view_prop x) (ev_view_prop y).
  Proof.
    unfold ev_view_prop.
    intros l. apply incl_max_of_list. red. ins. in_simp.
    eexists. splits; eauto. in_simp. splits; eauto.
    eapply props_before_hb_mon; eauto.
  Qed.

  (* In the paper, it is called _vmap-full_. *)
  Definition ev_view_full (e : Event) := view_join (ev_view e) (ev_view_prop e).

  Lemma ev_view_full_includes x y :
    ((rf G)^? ;; (sb G)^?) x y -> is_w x -> ev_ts x <= ev_view_full y (loc x).
  Proof.
    ins. etransitivity.
    { eapply ev_view_includes; eauto. }
    unfold ev_view_full, view_join. apply Nat.le_max_l.
  Qed.

  Lemma sb_view_fullE x y :
    sb G x y -> view_le (ev_view_full x) (ev_view_full y).
  Proof.
    ins. unfold ev_view_full.
    eapply view_le_join.
    { by apply sb_viewE. }
    apply hb_view_propE. by apply sb_in_hb.
  Qed.

  Definition msg_of (n : nat) :=
    {| mloc := loc (nu n) ;
       mval := valw (nu n) ;
       mts := ev_ts (nu n) ;
       mview := ev_view_full (nu n) |}.

  (* In the paper, it is called M_i. *)
  Definition scoh_mem (n : nat) :=
    Minit ∪₁ ⋃₁ m < n, ifP is_w (nu m) then eq (msg_of m) else ∅.

  (* In the paper, it is called T'_i. *)
  Definition scoh_view' (n : nat) t :=
    view_join (view_joinl (map ev_view_full
                               (filterP (fun x => tid x = t)
                                        (map nu (List.seq 0 n)))))
              (fun l : Loc =>
                 max_of_list
                   (map ev_ts (filterP (fun w => loc w = l)
                                       (props_before t (Nat.pred n))))).

  (* In the paper, it is called T_i. *)
  Definition scoh_view (n : nat) t :=
    view_join (scoh_view' n t)
              (fun l : Loc =>
                 max_of_list
                   (map ev_ts (filterP (fun w => loc w = l)
                                       (props_before t n)))).

  Definition scoh_state (n : nat) : State :=
    (scoh_mem n, scoh_view n).
  
  Lemma props_before_zero t : props_before t 0 = nil.
  Proof.
    unfold props_before, proj1_sig. desf. clear Heq. desf.
    destruct x; auto. exfalso. destruct a0 as [_ HH].
    specialize (HH e). destruct HH; desf; lia.
  Qed.

  Lemma scoh_state_init :
    scoh_state 0 = Sinit.
  Proof.
    unfold scoh_state, Sinit; f_equal.
    { unfold scoh_mem; extensionality msg.
      apply propositional_extensionality; unfolder.
      split; ins; desf; eauto; lia. }
    unfold scoh_view, scoh_view'. ins.
    extensionality t.
    arewrite (List.seq 0 0 = nil); ins.
    rewrite props_before_zero; auto.
  Qed.
  
  (* TODO: move to a more appropriate place. *)
  Lemma rfsb_init_r :
    (rf G)^? ;; (sb G)^? ⊆ <|fun _ => True|> ∪ (rf G)^? ;; (sb G)^? ;; <|set_compl is_init|>.
  Proof using WF.
    rewrite no_sb_to_init at 1.
    rewrite no_rf_to_init at 1; auto.
    basic_solver 20.
  Qed.

  (* TODO: move to a more appropriate place. *)
  Lemma wf_rfsbE :
    (rf G)^? ;; (sb G)^? ⊆ <|fun _ => True|> ∪
                           <|acts G|> ;; (rf G)^? ;; (sb G)^? ;; <|acts G|>.
  Proof using WF.
    rewrite wf_sbE at 1.
    rewrite (wf_rfE WF) at 1.
    basic_solver 20.
  Qed.

  Lemma ev_view_init x :
    ev_view (InitEvent x) = (fun _ => 0).
  Proof.
    extensionality l. unfold ev_view, proj1_sig; desf; desf. clear Heq.
    induction x0; ins; desc; ins; desc.
    inv a. desf; ins; rewrite IHx0; auto.
    { rewrite Nat.max_0_r.
      destruct a0 as [_ [HH BB]]; eauto.
      apply rfsb_init_r  in HH. unfolder in HH. desf. }
    all: split; intros y HH; [|by desf; apply a0; auto].
    all: desf; apply rfsb_init_r in HH; unfolder in HH; desf.
  Qed.

  Lemma props_before_tnit_is_empty e :
    props_before 0 e = nil.
  Proof.
    unfold props_before, proj1_sig. do 2 desf. clear Heq.
    destruct x; auto.
    assert (In e0 (e0::x)) as AA by (by constructor).
    apply a0 in AA. desf.
    apply tslot_defined_only_for_non_init in AA. lia.
  Qed.

  Lemma ev_view_prop_init x :
    ev_view_prop (InitEvent x) = (fun _ => 0).
  Proof.
    unfold ev_view_prop. extensionality l.
    apply Nat.le_antisymm.
    2: lia.
    apply le_max_of_list_l. ins. in_simp.
    rewrite props_before_tnit_is_empty in H0. inv H0.
  Qed.

  Lemma ev_view_full_init x :
    ev_view_full (InitEvent x) = (fun _ => 0).
  Proof.
    unfold ev_view_full. rewrite ev_view_init, ev_view_prop_init.
      by rewrite view_join_0_l.
  Qed.

  Lemma ev_ts_nzero n (Ln : lt_size n (acts G \₁ is_init)) :
    is_w (nu n) -> ev_ts (nu n) <> 0.
  Proof.
    assert (X := ENUM); apply enumeratesE in X; desc.
    unfold ev_ts; desf.
    unfold ev_ts_w, proj1_sig; desf; clear Heq.
    intros _.
    specialize (i0 (InitEvent (loc (nu n)))); specialize_full i0.
      apply co_init_l; ins; eauto.
    apply in_undup_iff, in_split in i0; desc.
    rewrite i0, filterP_app, length_app; ins; desf; ins; try lia.
    destruct n0; apply co_init_l; ins; eauto.
  Qed.

  Lemma ev_viewI x (ELEM: (acts G \₁ is_init) x) l :
    exists y, acts G y /\ is_w y /\ loc y = l
              /\ ((rf G)^? ;; (sb G)^?) y x
              /\ ev_ts y = ev_view x l.
  Proof.
    unfold ev_view, proj1_sig; desf; clear Heq; desf.
    destruct a0 as [_ a0].
    rename x0 into l'.
    induction l'; ins; desf; eauto 10.
    { exists (InitEvent l); rewrite ev_ts_init; splits; ins.
      apply (wf_initE WF); ins.
      red in ELEM; desc.
      eexists; splits.
      { by left. }
      right. apply init_ninit_sb; auto.
      apply (wf_initE WF); ins. }
    2: { inv a. apply IHl'; auto.
         etransitivity; [|by apply a0].
         basic_solver. }
    ins; desf; ins; desf; eauto 10.
    inv a. rewrite maxE; desf; eauto 10.
    { apply IHl'; auto.
      etransitivity; [|by apply a0].
      basic_solver. }
    specialize (a0 a1). destruct a0 as [HH]; eauto.
    exists a1. splits; eauto.
    apply wf_rfsbE in HH. unfolder in HH. desf.
    apply ELEM.
  Qed.

  Lemma hb_from_sb_nu n m
    (LTm : lt_size m (acts G \₁ is_init))
    (LTn : n < m)
    (TID : tid (nu n) <> 0 -> tid (nu m) <> 0 -> tid (nu n) = tid (nu m)) :
    hb G (nu n) (nu m).
  Proof.
    assert (X := ENUM); apply enumeratesE in X; desc.
    assert (tid (nu m) <> 0) as NM.
    { intros HH. apply (wf_tid_init WF) in HH.
      { apply RNG in HH; auto. }
      apply RNG; auto. }
    assert (LTnn : lt_size n (acts G \₁ is_init)).
    { eapply lt_lt_size; eauto. }
    assert (tid (nu n) <> 0) as NN.
    { intros HH. apply (wf_tid_init WF) in HH.
      { apply RNG in HH; auto. }
      apply RNG; auto. }
    apply t_step, or_introl, sb_nu; eauto using lt_lt_size.
    rewrite sb_nu_alt; ins; eauto using lt_lt_size.
  Qed.

  (* TODO: move to a more appropriate place *)
  Lemma fr_rfsb (SPL : SCpL G) : irreflexive (fr G ;; (rf G)^? ;; (sb G)^?).
  Proof using WF.
    red. intros x HH. unfolder in HH. desf.
    { eapply SPL with (x:=x). apply ct_step.
      generalize HH. basic_solver. }
    { eapply SPL with (x:=x).
      apply ct_ct; exists z; split; apply ct_step; generalize HH HH0; basic_solver. }
    { set (AA:=HH). apply (wf_frl WF) in AA.
      eapply SPL with (x:=x).
      apply ct_ct; exists z0; split; apply ct_step;
        generalize HH HH1 AA; basic_solver 10. }
    set (AA:=HH0). apply (wf_rfl WF) in AA.
    set (BB:=HH ). apply (wf_frl WF) in BB.
    unfold same_loc in *. rewrite AA in BB. symmetry in BB.
    eapply SPL with (x:=x).
    apply ct_ct; exists z0; split.
    2: { repeat left. basic_solver. }
    apply ct_ct; exists z; split; apply ct_step;
      generalize HH0 HH1 AA; basic_solver 20.
  Qed.

  (* TODO: move to a more appropriate place *)
  Lemma co_rfsb (SPL : SCpL G) : irreflexive (co G ;; (rf G)^? ;; (sb G)^?).
  Proof using WF.
    red. intros x HH. unfolder in HH. desf.
    { eapply SPL with (x:=x). apply ct_step.
      generalize HH. basic_solver. }
    { eapply SPL with (x:=x).
      apply ct_ct; exists z; split; apply ct_step; generalize HH HH0; basic_solver. }
    { set (AA:=HH). apply (wf_col WF) in AA.
      eapply SPL with (x:=x).
      apply ct_ct; exists z0; split; apply ct_step;
        generalize HH HH1 AA; basic_solver 10. }
    set (AA:=HH0). apply (wf_rfl WF) in AA.
    set (BB:=HH ). apply (wf_col WF) in BB.
    unfold same_loc in *. rewrite AA in BB. symmetry in BB.
    eapply SPL with (x:=x).
    apply ct_ct; exists z0; split.
    2: { repeat left. basic_solver. }
    apply ct_ct; exists z; split; apply ct_step;
      generalize HH0 HH1 AA; basic_solver 20.
  Qed.

  Lemma ev_view_loc_w x (W: is_w x) :
    ev_view x (loc x) = ev_ts x.
  Proof.
    unfold ev_view, proj1_sig, scoh_view; desf; clear Heq.
    desf.
    destruct (classic (is_init x)).
    { destruct x; ins; rewrite ev_ts_init.
      apply max_of_list_eq_zero; ins; in_simp.
      apply a0 in H1. desf.
      apply rfsb_init_r in H1. unfolder in H1. desf. }
    assert (IN: In x x0).
    { apply a0. basic_solver 10. }
    apply in_split in IN; desf.
    rewrite filterP_app, map_app, max_of_list_app; ins; desf; ins;
      clarify_not; desf; try solve [destruct x; ins; destruct l; ins].
    rewrite Nat.max_comm, <- Nat.max_assoc, Nat.max_l; ins.
    rewrite <- max_of_list_app, <- map_app, <- filterP_app.
    rewrite le_max_of_list_l; ins; in_simp.
    destruct (classic (x0 = x)) as [|NEQ]; desf.
    destruct a0 as [_ HH]. destruct (HH x0) as [HB NINIT].
    { apply in_app_or in H1. desf.
      { apply in_app_r. red; auto. }
        by apply in_app_l. }
    set (CC:=HB). apply wf_rfsbE in CC.
    destruct CC as [CC|CC].
    { unfolder in CC. desf. }
    apply seq_eqv_l in CC. desf.
    assert (acts G x) as EX.
    { unfolder in CC0. desf. }
    eapply (wf_co_total WF) in NEQ; unfolder; splits; ins; desf; eauto.
    { apply co_tsE in NEQ; lia. }
    exfalso. eapply co_rfsb.
    { apply CONS. }
    exists x0; split; eauto.
  Qed.

  Lemma ev_view_prop_loc x (ACTX : (acts G \₁ is_init) x) :
    ev_view_prop x (loc x) <= ev_ts x.
  Proof.
    assert (acts G x /\ ~ is_init x) as [AX NIX] by apply ACTX.
    unfold ev_view_prop, props_before, proj1_sig. do 2 desf. clear Heq.
    apply le_max_of_list_l. ins. in_simp.
    apply a0 in H0. desf.
    apply Nat.nlt_ge. intros LTT.
    eapply tslot_gt_is_safepoint; eauto.
    { by apply nu_inv_lt_size. }
    all: rewrite nu_nu_inv; auto.
    exists x. apply seq_eqv_r. splits; auto.
  Qed.

  Lemma ev_view_full_loc_w x (W: is_w x) (ACTX : (acts G \₁ is_init) x) :
    ev_view_full x (loc x) = ev_ts x.
  Proof.
    unfold ev_view_full, view_join.
    rewrite ev_view_loc_w; auto.
    apply Max.max_l. by apply ev_view_prop_loc.
  Qed.
  
  Lemma ev_view_loc x (Ax : acts G x) :
    ev_view x (loc x) = ev_ts x.
  Proof.
    destruct (classic (is_w x)) as [|NW]; eauto using ev_view_loc_w.
    unfold ev_ts, proj1_sig; desf; clarify_not.
    2: by destruct x; ins; destruct l; ins.
    clear Heq s; rename x0 into w.
    assert (W: is_w w) by (apply wf_rfD in r; unfolder in *; desf).
    assert (L: loc w = loc x) by (apply wf_rfl in r; unfolder in *; desf).
    apply Nat.le_antisymm.
    2: { rewrite <- L; eapply Nat.le_trans, ev_view_includes; ins.
         { unfold ev_ts; desf; right; vauto. }
         generalize r. basic_solver 10. }
    replace (ev_ts_w w) with (ev_ts w) by (unfold ev_ts; desf).
    assert (X := ENUM); apply enumeratesE in X; desc.
    forward apply (SUR x) as (i & I); try split; ins; desf.
    { apply (wf_rfD WF) in r; unfolder in r. desf. destruct x; ins. }
    unfold ev_view, proj1_sig; desf; clear Heq.
    apply le_max_of_list_l; ins; in_simp.
    destruct (classic (x0 = w)) as [|NEQ]; desf.
    set (AA:=H0). apply a0 in AA. desf.
    apply wf_rfsbE in AA. destruct AA as [AA|AA].
    { unfolder in AA. desf. }
    apply seq_eqv_l in AA. destruct AA as [EX0 AA].
    (* unfolder in AA. desf. *)
    (* apply (wf_hbE WF) in AA; unfolder in AA; desc. *)
    apply (wf_rfE WF) in r; unfolder in r; desc.
    eapply (wf_co_total WF) in NEQ; unfolder; splits; ins; try congruence.
    desf; try solve [apply co_tsE in NEQ; lia].
    exfalso. eapply fr_rfsb; [by apply CONS|].
    eexists; split. 
    { split.
      { exists w; split; eauto. }
      intros HH. unfolder in HH. desf. }
    apply a0 in H0. desf.
  Qed.

  Lemma ev_view_full_loc x (ACTX : (acts G \₁ is_init) x) :
    ev_view_full x (loc x) = ev_ts x.
  Proof.
    assert (acts G x) by apply ACTX.
    unfold ev_view_full, view_join.
    rewrite ev_view_loc; auto.
    apply Max.max_l. by apply ev_view_prop_loc.
  Qed.

  Lemma scoh_view'_r n
        (LT : lt_size n (acts G \₁ is_init))
        w (RF : rf G w (nu n)) :
    scoh_view' n (tid (nu n)) (loc (nu n)) <= ev_ts w.
  Proof.
    set (TT:=ENUM). apply enumeratesE in TT. desf.
    assert (~ is_init (nu n)) as NINITN.
    { intros HH. apply rf_init_r in RF; auto. }
    assert (R := RF).
    apply (wf_rfE WF) in RF; unfolder in RF; desc.
    apply (wf_rfD WF) in RF0; unfolder in RF0; desc.
    apply (wf_rfl WF) in R; red in R; unfold loc in *; ins.
    assert (is_init w \/ exists m, m < n /\ w = nu m).
    { apply (wf_rfE WF) in RF2; unfolder in RF2; desf.
      assert (X := proj1 (enumeratesE _ _) ENUM); desc.
      classical_right.
      specialize (SUR w); specialize_full SUR; ins; desf.
      eexists; split; ins; eapply IMPL; ins; apply t_step; vauto. }
    destruct (le_lt_dec (scoh_view' n (tid (nu n)) (loc (nu n)))
                        (ev_ts w)) as [|LT']; ins.
    exfalso; unfold scoh_view in LT'.
    clear H.
    unfold scoh_view', view_join in LT'.
    apply NPeano.Nat.max_lt_iff in LT'.
    desf.
    { rewrite view_joinlE, lt_max_of_list_r in LT'; desf. in_simp.
      assert (HB: sb G (nu x) (nu n)).
      { assert (X := ENUM); apply enumeratesE in X; desc.
        specialize (RNG x); specialize_full RNG; eauto using lt_lt_size.
        apply proj2 in RNG.
        apply sb_nu; eauto using lt_lt_size.
        rewrite sb_nu_alt; ins; eauto using lt_lt_size. }
      assert (acts G (nu x)) as ENUX.
      { apply wf_sbE in HB. unfolder in HB. desf. }
      assert (lt_size x (acts G \₁ is_init)) as LTACTX.
      { eapply lt_lt_size; eauto. }
      unfold ev_view_full, view_join in LT'0.
      apply NPeano.Nat.max_lt_iff in LT'0. desf.
      { unfold ev_view, proj1_sig in LT'0; desf; clear Heq.
        rewrite lt_max_of_list_r in LT'0; desf; in_simp.
        set (AA:=LT'4). apply a0 in AA. desf.
        assert (acts G x1) as EX1.
        { apply wf_rfsbE in AA. unfolder in AA. desf. }
        assert (co G w x1).
        { rewrite co_ts; unfold loc; splits; ins; try congruence.
          red in LT'0; desf. by rewrite R. }
        eapply fr_rfsb; [by apply CONS|].
        exists x1. split.
        2: { eapply rfsb_sb. apply seqA. exists (nu x). split; eauto. }
        split.
        { eexists; eauto. }
        intros HH. unfolder in HH. desf.
        cdes CONS. eapply PORF.
        eapply ct_end. eexists. split.
        2: by left; apply HB.
        apply rfsb_in_hb in AA.
          by apply cr_of_ct in AA. }
      unfold loc in LT'0. rewrite <- R in LT'0.
      unfold ev_view_prop in LT'0. apply lt_max_of_list_r in LT'0. desf.
      in_simp. unfold props_before in *.
      unfold proj1_sig in *; desf. clear Heq. desf.
      apply a0 in LT'4. desf. clear dependent x1.
      rewrite nu_inv_nu in LT'5; auto.
      assert (safepoints x0 (nu x)) as SFWX.
      { eapply tslot_gt_is_safepoint; eauto. }
      assert (safepoints x0 (nu n)) as SFWN.
      { eapply safepoint_hb_mon. apply sb_in_hb in HB. basic_solver 10. }
      assert (acts G x0) as ACTSX0.
      { eapply tslot_defined_only_for_E; eauto. }
      apply SFWN. exists (nu n). apply seq_eqv_r. splits; eauto.
      2: by rewrite LT'0.
      assert (is_w x0) as WY.
      { by apply tslot_defined_only_for_w in LT'4. }
      destruct (classic (nu n = x0)) as [|NEQ]; auto. left.
      destruct (classic (is_w (nu n))).
      2: by rewrite <- rf_tsE with (x:=w) (y:=nu n).
      assert (ev_ts (nu n) <> ev_ts x0) as TNEQ.
      { intros HH. apply NEQ. apply ts_uniq; auto. by rewrite LT'0. }
      rewrite <- rf_rmw_tsE with (x:=w) (y:=nu n); auto.
      rewrite <- rf_rmw_tsE with (x:=w) (y:=nu n) in TNEQ; auto.
      clear -LT'2 TNEQ. lia. }
    apply lt_max_of_list_r in LT'. desf. in_simp.
    unfold props_before, proj1_sig in LT'1. do 2 desf. clear Heq.
    apply a0 in LT'1. desf. clear dependent x0.
    assert (acts G x) as EX.
    { eapply tslot_defined_only_for_E; eauto. }
    assert (is_w x) as WX.
    { eapply tslot_defined_only_for_w; eauto. }
    assert (co G w x) as CO.
    { rewrite co_ts; unfold loc; splits; ins; try congruence.
      rewrite R. simpls. }
    assert (safepoints x (nu n)) as SFXN.
    { eapply tslot_gt_is_safepoint; eauto. lia. }
    assert (is_w x) as WY.
    { eapply tslot_defined_only_for_w; eauto. }
    apply SFXN. exists (nu n). apply seq_eqv_r. splits; eauto.
    destruct (classic (nu n = x)) as [|NEQ]; auto. left.
    destruct (classic (is_w (nu n))).
    2: by rewrite <- rf_tsE with (x:=w) (y:=nu n).
    assert (ev_ts (nu n) <> ev_ts x) as TNEQ.
    { intros HH. apply NEQ. apply ts_uniq; auto. }
    rewrite <- rf_rmw_tsE with (x:=w) (y:=nu n); auto.
    rewrite <- rf_rmw_tsE with (x:=w) (y:=nu n) in TNEQ; auto.
    lia.
  Qed.

  Lemma scoh_view'_load n
        (LT : lt_size n (acts G \₁ is_init)) thread index x v
        (N : nu n = ThreadEvent thread index (Aload x v))
        w (RF : rf G w (nu n)) :
    scoh_view' n thread x <= ev_ts w.
  Proof.
    rewrite <- scoh_view'_r; eauto.
    rewrite N; ins.
  Qed.

  Lemma scoh_view_r n
        (LT : lt_size n (acts G \₁ is_init))
        w (RF : rf G w (nu n)) :
    scoh_view n (tid (nu n)) (loc (nu n)) <= ev_ts w.
  Proof.
    unfold scoh_view, view_join.
    apply Max.max_lub.
    { apply scoh_view'_r; auto. }
    set (TT:=ENUM). apply enumeratesE in TT. desf.
    assert (~ is_init (nu n)) as NINITN.
    { intros HH. apply rf_init_r in RF; auto. }
    assert (R := RF).
    apply (wf_rfE WF) in RF; unfolder in RF; desc.
    apply (wf_rfD WF) in RF0; unfolder in RF0; desc.
    apply (wf_rfl WF) in R; red in R; unfold loc in *; ins.
    apply Nat.nlt_ge. intros LT'.
    apply lt_max_of_list_r in LT'. desf. in_simp.
    unfold props_before, proj1_sig in LT'1. do 2 desf. clear Heq.
    apply a0 in LT'1. desf. clear dependent x0.
    assert (acts G x) as EX.
    { eapply tslot_defined_only_for_E; eauto. }
    assert (is_w x) as WX.
    { eapply tslot_defined_only_for_w; eauto. }
    assert (co G w x) as CO.
    { rewrite co_ts; unfold loc; splits; ins; try congruence. }
    assert (safepoints x (nu n)) as SFXN.
    { eapply tslot_gt_is_safepoint; eauto. }
    assert (is_w x) as WY.
    { eapply tslot_defined_only_for_w; eauto. }
    apply SFXN. exists (nu n). apply seq_eqv_r. splits; eauto.
    destruct (classic (nu n = x)) as [|NEQ]; auto. left.
    destruct (classic (is_w (nu n))).
    2: by rewrite <- rf_tsE with (x:=w) (y:=nu n).
    assert (ev_ts (nu n) <> ev_ts x) as TNEQ.
    { intros HH. apply NEQ. apply ts_uniq; auto. }
    rewrite <- rf_rmw_tsE with (x:=w) (y:=nu n); auto.
    rewrite <- rf_rmw_tsE with (x:=w) (y:=nu n) in TNEQ; auto.
    lia.
  Qed.

  Lemma scoh_view_load n
        (LT : lt_size n (acts G \₁ is_init)) thread index x v
        (N : nu n = ThreadEvent thread index (Aload x v))
        w (RF : rf G w (nu n)) :
    scoh_view n thread x <= ev_ts w.
  Proof.
    rewrite <- scoh_view_r; eauto.
    rewrite N; ins.
  Qed.

  Lemma view_le_scoh_ev' n (LT :  lt_size n (acts G \₁ is_init)) :
    view_le (scoh_view' n (tid (nu n))) (ev_view_full (nu n)).
  Proof.
    assert (X := ENUM); apply enumeratesE in X; desc.
    assert (NIn: ~ is_init (nu n)) by (apply RNG; ins).
    intro x.
    unfold scoh_view', view_join.
    apply Nat.max_lub.
    2: { apply le_max_of_list_l. ins. in_simp.
         unfold props_before, proj1_sig in *. do 2 desf. clear Heq.
         unfold ev_view_full. unfold view_join.
         etransitivity; [|by apply Nat.le_max_r].
         unfold ev_view_prop. apply in_max_of_list. in_simp. exists x0.
         splits; auto.
         apply a0 in H0. clear dependent x. desf.
         in_simp. splits; auto. unfold props_before, proj1_sig. do 2 desf. clear Heq.
         apply a0. clear dependent x. splits; auto.
         exists m. splits; auto. rewrite nu_inv_nu; auto. lia. }
    destruct (exists_max (fun x => tid (nu x) = tid (nu n)) n) as [MAX|]; desc.
    { unfold scoh_view'.
      replace (filterP _ _) with (@nil Event); ins.
      { forward apply ev_viewI with (x := nu n) (l := x) as X; desc; eauto.
        lia. }
      symmetry; rewrite filterP_eq_nil; ins; in_simp.
      eapply MAX; eauto. }
    unfold scoh_view.
    rewrite view_joinlE, (seq_split0 H), map_app, filterP_app.
    rewrite map_app, map_app, max_of_list_app;
      ins; desf; ins; try congruence.
    rewrite Nat.max_comm, <- Nat.max_assoc, <- max_of_list_app.
    rewrite Nat.max_l; ins.
    { eapply sb_view_fullE. apply sb_nu; eauto using lt_lt_size.
      splits; auto. apply sb_nu_alt; auto. eapply lt_lt_size; eauto. }
    rewrite le_max_of_list_l; ins; in_simp.
    rewrite in_app_iff in *; desf; in_simp.
    { edestruct H1 with (j := x0); try lia. }
    apply sb_view_fullE; eauto using lt_lt_size.
    apply sb_nu; eauto using lt_lt_size.
    split.
    { etransitivity; eauto. }
    apply sb_nu_alt; eauto using lt_lt_size.
    etransitivity; eauto.
  Qed.

  Lemma view_le_scoh_ev n (LT :  lt_size n (acts G \₁ is_init)) :
    view_le (scoh_view n (tid (nu n))) (ev_view_full (nu n)).
  Proof.
    unfold scoh_view. apply view_join_lub.
    { by apply view_le_scoh_ev'. }
    assert (X := ENUM); apply enumeratesE in X; desc.
    assert (NIn: ~ is_init (nu n)) by (apply RNG; ins).
    intro x.
    apply le_max_of_list_l. ins. in_simp.
    unfold props_before, proj1_sig in *. do 2 desf. clear Heq.
    unfold ev_view_full. unfold view_join.
    etransitivity; [|by apply Nat.le_max_r].
    unfold ev_view_prop. apply in_max_of_list. in_simp. exists x0.
    splits; auto.
    apply a0 in H0. clear dependent x. desf.
    in_simp. splits; auto. unfold props_before, proj1_sig. do 2 desf. clear Heq.
    apply a0. clear dependent x. splits; auto.
    exists m. splits; auto. rewrite nu_inv_nu; auto.
  Qed.

  Lemma scoh_view_sb l n pn (SB : sb G pn (nu n))
        (LTN : lt_size n (acts G \₁ is_init)) :
    ev_view_full pn l <= scoh_view n (tid (nu n)) l.
  Proof using IMPL.
    assert (X := ENUM); apply enumeratesE in X; desc.
    ins.
    set (AA:=SB). apply sb_tid_init in AA. desf.
    2: { destruct pn; ins. rewrite ev_view_full_init. lia. }
    eapply Nat.le_trans, Nat.le_max_l.
    unfold scoh_view'. eapply Nat.le_trans, Nat.le_max_l.
    rewrite view_joinlE. apply in_max_of_list.
    do 2 (in_simp; eexists; splits; eauto).
    in_simp. splits; auto.
    assert (acts G (nu n) /\ ~ is_init (nu n)) as [EN NN] by (by apply RNG).
    assert (tid (nu n) <> 0) as NNN.
    { intros HH. apply NN. eapply wf_tid_init; eauto. }
    assert (~ is_init pn) as NINITPN.
    { intros BB. destruct pn; ins. eauto. }
    apply wf_sbE in SB. unfolder in SB. desf.
    edestruct (SUR pn).
    { by split. }
    desf. eexists; split; eauto. apply in_seq0_iff.
    apply IMPL; auto. by apply sb_in_hb.
  Qed.

  Lemma ev_view_w n (LT :  lt_size n (acts G \₁ is_init))
        (NR: ~ is_r (nu n)) :
    ev_view_full (nu n) =
    upd (scoh_view n (tid (nu n)))
        (loc (nu n)) (ev_ts (nu n)).
  Proof.
    assert (X := ENUM); apply enumeratesE in X; desc.
    assert (NIn: ~ is_init (nu n)) by (apply RNG; ins).
    assert (Wn: is_w (nu n))
      by (destruct (nu n); ins; destruct l; ins).
    extensionality x.
    unfold upd; desf.
    { apply ev_view_full_loc_w; auto. }
    apply Nat.le_antisymm.
    2: by apply view_le_scoh_ev.
    unfold scoh_view, view_join.
    unfold ev_view_full at 1, view_join at 1.
    apply Max.max_lub.
    2: { unfold ev_view_prop.
         unfold scoh_view, view_join.
         etransitivity; [|by apply Nat.le_max_r].
         rewrite nu_inv_nu; auto. }
    destruct ev_viewI with (x := nu n) (l := x) as [i I]; desf; auto.
    rewrite <- I3.
    destruct I2 as [pn [[RF|RF] [SB|SB]]]; subst.
    { desf. }
    2: { exfalso. apply (wf_rfD WF) in RF. unfolder in RF. desf. }
    2: { transitivity (ev_view_full pn (loc i)).
         2: by apply scoh_view_sb.
         apply ev_view_full_includes; auto.
         generalize RF. basic_solver 10. }
    transitivity (ev_view_full pn (loc pn)).
    2: by apply scoh_view_sb.
    unfold ev_view_full, view_join.
    eapply Nat.le_trans, Nat.le_max_l.
    rewrite ev_view_loc; auto.
  Qed.

  Lemma ev_view_r n (LT :  lt_size n (acts G \₁ is_init))
        w (RF: rf G w (nu n)) :
    ev_view_full (nu n) =
    upd (scoh_view n (tid (nu n)))
        (loc (nu n)) (ev_ts (nu n)).
  Proof.
    assert (X := ENUM); apply enumeratesE in X; desc.
    assert (NIn: ~ is_init (nu n)) by (apply RNG; ins).
    extensionality x.
    apply (wf_rfE WF) in RF; unfolder in RF; desf.
    apply (wf_rfD WF) in RF0; unfolder in RF0; desf.
    assert (hb G w (nu n)) as HB.
    { by apply rf_in_hb. }
    apply Nat.le_antisymm.
    2: { unfold view_join, upd; desf.
         { rewrite ev_view_full_loc; auto. }
           by eapply view_le_scoh_ev. }
    unfold view_join, upd; desf.
    { rewrite ev_view_full_loc; auto with arith; apply RNG. }
    unfold ev_view_full at 1, view_join at 1.
    apply Max.max_lub.
    2: { unfold ev_view_prop.
         unfold scoh_view, view_join.
         etransitivity; [|by apply Nat.le_max_r].
         rewrite nu_inv_nu; auto. }
    destruct ev_viewI with (x := nu n) (l := x) as [i I]; desf; auto.
    rewrite <- I3.
    rename RF into RFG.
    destruct I2 as [pn [[RF|RF] [SB|SB]]]; subst.
    { desf. }
    2: { assert (i = w); subst.
         { eapply wf_rff; eauto. }
         exfalso. apply (wf_rfl WF) in RF. apply n0 in RF. desf. }
    2: { transitivity (ev_view_full pn (loc i)).
         2: by apply scoh_view_sb.
         apply ev_view_full_includes; auto.
         generalize RF. basic_solver 10. }
    transitivity (ev_view_full pn (loc pn)).
    2: by apply scoh_view_sb.
    unfold ev_view_full, view_join.
    eapply Nat.le_trans, Nat.le_max_l.
    rewrite ev_view_loc; auto.
  Qed.

  Lemma scoh_view_S n (LT : lt_size n (acts G \₁ is_init)):
    scoh_view' (S n) = upd (scoh_view n) (tid (nu n)) (ev_view_full (nu n)).
  Proof.
    extensionality t; extensionality l; unfold scoh_view, upd; desf.
    2: { unfold scoh_view' at 1. unfold view_join; ins.
         assert (view_joinl
                    (map ev_view_full
                         (filterP (fun x : Event => tid x = t) (map nu (List.seq 0 (S n)))))
                    l =
                 view_joinl
                    (map ev_view_full
                         (filterP (fun x : Event => tid x = t) (map nu (List.seq 0 n))))
                    l) as AA.
         { rewrite !view_joinlE.
           apply Nat.le_antisymm.
           all: apply incl_max_of_list; red; ins; in_simp.
           all: do 2 (eexists; splits; eauto; in_simp).
           all: splits; eauto.
           all: eexists; splits; eauto.
           all: apply in_seq0_iff; try lia.
           destruct (classic (x = n)); [exfalso; desf|lia]. }
         rewrite AA.
         apply Nat.le_antisymm.
         all: apply Nat.max_lub.
         all: try by apply Nat.le_max_r.
         { etransitivity; [|by apply Nat.le_max_l].
           unfold scoh_view'. by apply Nat.le_max_l. }
         unfold scoh_view'. apply Nat.max_lub.
         { by apply Nat.le_max_l. }
         etransitivity; [|by apply Nat.le_max_r].
         apply incl_max_of_list; red; ins; in_simp.
         do 2 (eexists; splits; eauto; in_simp).
         eapply props_before_index_mon; [|by eauto]. lia. }
    apply Nat.le_antisymm.
    { unfold scoh_view', view_join; ins.
      apply Nat.max_lub.
      2: { unfold ev_view_full, view_join.
           etransitivity; [|by apply Nat.le_max_r].
           unfold ev_view_prop. rewrite nu_inv_nu; auto. }
      eapply view_le_joinl_l; ins; in_simp.
      destruct (classic (x = n)); subst.
      { by apply view_le_refl. }
      apply sb_view_fullE.
      assert (x < n) by lia.
      apply sb_nu_lt; splits; auto.
      eapply lt_lt_size; eauto. }
    unfold scoh_view', view_join.
    etransitivity; [|by apply Nat.le_max_l].
    rewrite view_joinlE. apply in_max_of_list.
    do 2 (in_simp; eexists; splits; eauto).
    in_simp; splits; eauto. eexists; splits; eauto.
    apply in_seq0_iff. lia.
  Qed.

  Definition scoh_state' (n : nat) : State :=
    (scoh_mem n, scoh_view' n).

  Definition lab_of_ev e :=
    match e with
    | ThreadEvent t i (Aload x v) =>
      SCOH_event (ThreadEvent t i (Aload x v)) (ev_ts e) (ev_view_full e)
    | ThreadEvent t i lab =>
      SCOH_event (ThreadEvent t i lab) (Nat.pred (ev_ts e)) (ev_view_full e)
    | InitEvent _ => deflabel
    end.

  Lemma scoh_step_all' n (LT: lt_size n (acts G \₁ is_init)) :
    SCOH_step (scoh_state n) (lab_of_ev (nu n)) (scoh_state' (S n)).
  Proof.
    assert (X := ENUM); apply enumeratesE in X; desc.
    assert (acts G (nu n)) as ACTSN.
    { apply RNG; auto. }
    destruct (nu n) eqn: N; ins.
    { specialize (RNG _ LT); rewrite N in *; red in RNG; ins; desf. }
    destruct l; ins.
    { destruct (COMPL (x := nu n)) as [w RF].
      split; [apply (proj1 (enumeratesE _ _) ENUM); ins| rewrite N; ins].
      rewrite <- rf_tsE with (x := w); eauto.
      2: by rewrite <- N; ins.
      eapply SCOHstep_read with (view := ev_view_full w);
        try rewrite scoh_view_S, N; ins.
      { assert (is_init w \/ exists m, m < n /\ w = nu m).
        { apply (wf_rfE WF) in RF; unfolder in RF; desf.
          assert (X := proj1 (enumeratesE _ _) ENUM); desc.
          classical_right.
          specialize (SUR w); specialize_full SUR; ins; desf.
          eexists; split; ins; eapply IMPL; ins; apply t_step; vauto. }
        rewrite N in *.
        assert (L := wf_rfl WF _ _ RF); unfold same_loc, loc in *; ins; clarify.
        assert (V := wf_rfv WF _ _ RF); unfold valw, valr in *; ins; clarify.
        apply (wf_rfD WF) in RF; unfolder in RF; desc.
        desf; [left; red; ins | right; exists m; ins; splits; desf ].
        destruct w; ins; rewrite ev_ts_init, ev_view_full_init; ins. }
      { eapply scoh_view_load; eauto; congruence. }
      { unfold scoh_mem; apply set_extensionality.
        apply (wf_rfD WF) in RF; unfolder in RF; desc.
        rewrite set_bunion_lt_S, N; ins; desf; rels. }
      2: { rewrite scoh_view_S; auto. rewrite N. ins. }
      rewrite <- N in *.
      erewrite ev_view_r; eauto.
      f_equal; try solve [rewrite N; unfold loc; ins].
      symmetry. apply rf_tsE; auto.
      unfold is_w, is_w_l. rewrite N. desf. }
    { assert (Wn : is_w (nu n)) by (rewrite N; ins).
      assert (ev_ts (nu n) <> 0) as NUNTNZ.
      { apply ev_ts_nzero; auto. }
      eapply SCOHstep_write; ins;
        try rewrite scoh_view_S, N; ins.
      all: try rewrite Nat.succ_pred;
        try rewrite <- N; eauto using ev_ts_nzero.
      { rewrite ev_view_w, N; ins; rewrite N; ins. }
      { unfold scoh_view, view_join.
        apply Nat.max_lub_lt.
        (* TODO: a lot of repetion below. *)
        2: { apply lt_max_of_list_l. split.
             { apply ev_ts_nzero; auto. }
             ins. in_simp. unfold props_before, proj1_sig in *. do 2 desf. clear Heq.
             apply a0 in H0. desf. clear dependent x.
             assert (is_w x0) as WX0 by (eapply tslot_defined_only_for_w; eauto).
             assert (acts G x0) as ACTSX0.
             { eapply tslot_defined_only_for_E; eauto. }
             eapply tslot_gt_is_safepoint in H1; eauto.
             2: by rewrite N; ins.
             apply Nat.nle_gt. intros LE.
             apply le_lt_or_eq in LE. destruct LE as [LTT|EQ].
             2: { apply ts_uniq in EQ; auto; try by rewrite N; ins. desf.
                  eapply safepoints_irr; eauto. }
             apply H1. exists (nu n). unfolder. ins. splits; eauto.
             rewrite N. ins. }
        unfold scoh_view'. apply Nat.max_lub_lt.
        2: { apply lt_max_of_list_l. split; auto.
             ins. in_simp. unfold props_before, proj1_sig in *. do 2 desf. clear Heq.
             apply a0 in H0. desf. clear dependent x.
             assert (is_w x0) as WX0 by (eapply tslot_defined_only_for_w; eauto).
             assert (acts G x0) as ACTSX0.
             { eapply tslot_defined_only_for_E; eauto. }
             eapply tslot_gt_is_safepoint in H0; eauto.
             3: lia.
             2: by rewrite N; ins.
             apply Nat.nle_gt. intros LE.
             apply le_lt_or_eq in LE. destruct LE as [LTT|EQ].
             2: { apply ts_uniq in EQ; auto; try by rewrite N; ins. desf.
                  eapply safepoints_irr; eauto. }
             apply H0. exists (nu n). unfolder. ins. splits; eauto.
             rewrite N. ins. }
        rewrite view_joinlE.
        rewrite lt_max_of_list_l; split;
          eauto using ev_ts_nzero; ins; in_simp.
        (* forward eapply hb_from_sb_nu as HB'; eauto. *)
        (* { rewrite N; unfold tid; desf. } *)
        unfold ev_view_full, view_join. apply Nat.max_lub_lt.
        2: { unfold ev_view_prop. apply lt_max_of_list_l; splits; auto.
             ins. in_simp. rewrite nu_inv_nu in *; auto.
             2: eby eapply lt_lt_size.
             unfold props_before, proj1_sig in *. do 2 desf. clear Heq.
             apply a0 in H1. desf. clear dependent x.
             assert (acts G x1) as EX1 by (eapply tslot_defined_only_for_E; eauto).
             assert (is_w x1) as WX1 by (eapply tslot_defined_only_for_w; eauto).
             eapply tslot_gt_is_safepoint in H1; eauto.
             3: lia.
             2: by rewrite N; ins.
             apply Nat.nle_gt. intros LE.
             apply le_lt_or_eq in LE. destruct LE as [LTT|EQ].
             2: { apply ts_uniq in EQ; auto; try by rewrite N; ins. desf.
                  eapply safepoints_irr; eauto. }
             apply H1. exists (nu n). unfolder. splits; eauto.
             rewrite N. ins. }
        assert (LTS0 : lt_size x0 (acts G \₁ is_init)) by eauto using lt_lt_size.
        assert (TX0  : tid (nu x0) = tid (nu n)) by (by rewrite N; unfold tid; desf).
        assert (SB' : sb G (nu x0) (nu n)).
        { apply sb_nu; eauto. split; auto.
          apply sb_nu_alt; auto. }
        unfold ev_view, proj1_sig; desf. clear Heq.
        rewrite lt_max_of_list_l; split; auto.
        ins; in_simp.
        apply a0 in H1. desf. clear dependent x1.
        destruct (classic (x2 = nu n)) as [|NEQ]; desf.
        { exfalso.
          apply rfsb_in_hb in H1. destruct H1 as [AA|AA].
          { rewrite AA in SB'. eapply sb_irr; eauto. }
          eapply hb_irr; eauto. apply ct_ct; eexists. split; eauto.
          apply sb_in_hb; eauto. }
        assert (HB : hb G x2 (nu n)).
        { apply rfsb_in_hb in H1. destruct H1 as [AA|AA]; subst; auto.
          { by apply sb_in_hb. }
          apply ct_ct. eexists; split; eauto.
            by apply sb_in_hb. }
        apply wf_hbE in HB; auto. unfolder in HB. desf.
        eapply wf_co_total in NEQ; eauto.
        all: unfolder; splits; ins; eauto;
          try solve [rewrite N; ins].
        desf; eauto using co_tsE.
        exfalso. eapply co_rfsb; [by apply CONS|].
        eexists; split; eauto.
        apply rfsb_sb. apply seqA. eexists; eauto. }
      { unfold scoh_mem; apply set_extensionality.
        rewrite set_bunion_lt_S, N; ins; desf; rels.
        rewrite <- set_unionA; apply set_equiv_union; ins.
        unfold msg_of; rewrite N; unfold loc, valw; ins. }
      assert (X := ENUM); apply enumeratesE in X; desc.
      unfold fresh_tstamp, scoh_mem, Minit, msg_of; unfolder; red; ins; desf.
      eapply ev_ts_nzero; eauto.
      apply ts_uniq in H2; ins; try apply RNG; eauto using lt_lt_size.
      unfold ev_ts in *; desf.
      apply INJ in H2; ins; desf; eauto using lt_lt_size; lia.
      rewrite N; ins. }
    unfold scoh_mem.
    assert (Wn : is_w (nu n)) by (rewrite N; ins).
    destruct (COMPL (x := nu n)) as [w RF].
    split; [apply (proj1 (enumeratesE _ _) ENUM); ins| rewrite N; ins].
    forward apply rf_rmw_tsE as TS; eauto.
    eapply SCOHstep_rmw with (view := ev_view_full w); ins;
      try rewrite scoh_view_S, N; ins.
    all: try rewrite Nat.succ_pred;
      try rewrite <- N; eauto using ev_ts_nzero.
    { assert (L := wf_rfl WF _ _ RF); unfold same_loc, loc in *; ins; clarify.
      assert (V := wf_rfv WF _ _ RF); unfold valw, valr in *; ins; clarify.
      apply (wf_rfE WF) in RF; unfolder in RF; desf.
      apply (wf_rfD WF) in RF0; unfolder in RF0; desf.
      assert (is_init w \/ exists m, m < n /\ w = nu m).
      { assert (X := proj1 (enumeratesE _ _) ENUM); desc.
        classical_right.
        specialize (SUR w); specialize_full SUR; ins; desf.
        eexists; split; ins; eapply IMPL; ins; apply t_step; vauto. }
      rewrite N in *.
      desf; [left; red; ins | right; exists m; splits; ins; desf ].
      destruct w; ins; rewrite ev_ts_init, ev_view_full_init in *.
      all: rewrite <- TS; ins. }
    { rewrite <- TS; ins.
      forward eapply scoh_view_r; eauto.
      rewrite N; ins. }
    { erewrite ev_view_r with (w := w); eauto.
      f_equal; f_equal; rewrite N; ins. }
    { unfold scoh_mem; apply set_extensionality.
      rewrite set_bunion_lt_S, N; ins; desf; rels.
      rewrite <- set_unionA; apply set_equiv_union; ins.
      unfold msg_of; rewrite N; unfold loc, valw; ins. }
    clear TS.
    assert (X := ENUM); apply enumeratesE in X; desc.
    unfold fresh_tstamp, scoh_mem, Minit, msg_of; unfolder; red; ins; desf.
    eapply ev_ts_nzero; eauto.
    apply ts_uniq in H2; ins; try apply RNG; eauto using lt_lt_size.
    unfold ev_ts in *; desf.
    apply INJ in H2; ins; desf; eauto using lt_lt_size; lia.
    rewrite N; ins.
  Qed.

  Definition SCOH_step_no_lbl_gen (l : SCOH_label) (a b : State) :=
    exists w t x v tstamp view view',
      << TBT   : t <> 0 /\ exists e, acts G e /\ t = tid e >> /\
      << LBL   : l = SCOH_internal t x tstamp >> /\
      << EW    : acts G w >> /\
      << NINIT : ~ is_init w >> /\
      << WW    : is_w w >> /\
      << ST    : tstamp = ev_ts w >> /\
      << SV    : v = valw w >> /\
      << INMEM : fst a (Msg x v tstamp view) >> /\
      << LTX   : snd a t x < tstamp >> /\
      << SMMEM : fst b = fst a >> /\
      << NVIEW : view' = upd (snd a t) x tstamp >> /\
      << NST   : snd b = upd (snd a) t view' >>.
  
  Definition SCOH_step_no_lbl (a b : State) :=
    exists l, SCOH_step_no_lbl_gen l a b.
  
  Lemma SCOH_step_no_lbl_same_mem : SCOH_step_no_lbl ⊆ fst ↓ eq.
  Proof. unfold SCOH_step_no_lbl, SCOH_step_no_lbl_gen. unfolder. ins. desf. Qed.

  Lemma SCOH_steps_no_lbl_same_mem : SCOH_step_no_lbl^* ⊆ fst ↓ eq.
  Proof.
    apply inclusion_rt_ind.
    { basic_solver. }
    { by apply SCOH_step_no_lbl_same_mem. }
    unfolder. intros x y z HH AA. by rewrite HH.
  Qed.
  
  Lemma SCOH_steps_view_mono t :
    (fun a b => exists l, SCOH_step a l b)^* ⊆ (fun x => snd x t) ↓ view_le.
  Proof.
    apply inclusion_rt_ind.
    { basic_solver. }
    { unfolder. ins. desf. eapply SCOH_step_view_mono; eauto. }
    unfolder. intros x y z HH AA.
    eapply view_le_trans; eauto.
  Qed.

  Lemma scoh_props_steps_gen n (LT: lt_size n (acts G \₁ is_init))
        ram rav tslotlist
        (TSD : forall t w (IN : In (t, w) tslotlist),
            acts G w /\ ~ is_init w /\ is_w w /\
            t <> 0 /\ (exists e, acts G e /\ t = tid e) /\ 
            exists view,
              ram (Msg (loc w) (valw w) (ev_ts w) view)) :
    SCOH_step_no_lbl＊
      (ram, rav)
      (ram, fun t => view_join
                       (rav t)
                       (fun l =>
                          max_of_list
                            (map (fun x => ev_ts (snd x))
                                 (filterP (fun tw => loc (snd tw) = l /\ fst tw = t)
                                          tslotlist)))).
  Proof.
    induction tslotlist; ins.
    { arewrite (rav = fun t : Tid => view_join (rav t) (fun _ : Loc => 0)) at 1.
      2: by apply rt_refl.
      extensionality l. by rewrite view_join_0_r. }
    destruct a as [t w]. ins.
    match goal with
    | |- SCOH_step_no_lbl＊ (ram, rav) (ram, ?X) => set (Y:=X)
    end.
    match goal with
    | H: _ -> SCOH_step_no_lbl＊ (ram, rav) (ram, ?X) |- _ => set (Z:=X)
    end.
    assert (SCOH_step_no_lbl＊ (ram, rav) (ram, Z)) as HH.
    { apply IHtslotlist. ins. eapply TSD; eauto. }
    clear IHtslotlist.
    destruct (le_lt_dec (ev_ts w) (Z t (loc w))) as [LE|LTT].
    { arewrite (Y = Z); auto. extensionality t'. extensionality l'.
      unfold Z, Y, view_join. do 2 desf. ins.
      rewrite Nat.max_comm with (n := ev_ts w).
      rewrite Nat.max_assoc.
      rewrite Nat.max_l; auto. }
    apply rt_end. right. exists (ram, Z). splits; auto.
    edestruct (TSD t w); eauto. desf.
    red. eexists. exists w, (tid e), (loc w), (valw w), (ev_ts w). do 2 eexists.
    splits; eauto.
    extensionality t'. extensionality l'; ins.
    unfold upd. do 2 desf.
    all: try by unfold Y, view_join; do 2 desf.
    unfold Y, view_join. do 2 desf.
    2: { exfalso. apply n0. desf. }
    ins.
    rewrite Nat.max_comm with (n := ev_ts w).
    rewrite Nat.max_assoc.
    rewrite Nat.max_r; auto. unfold Z, view_join in LTT. lia.
  Qed.

  Lemma scoh_props_steps n (LT: lt_size n (acts G \₁ is_init)) :
    SCOH_step_no_lbl＊ (scoh_state' (S n)) (scoh_state (S n)).
  Proof.
    set (s:=fun tw => Some n = tslot (fst tw) (snd tw)).
    assert (set_finite s) as SF by apply tslot_dom_finite.
    apply set_finiteE in SF. desf.
    unfold scoh_state, scoh_state', scoh_view.
    pose (scoh_props_steps_gen LT (scoh_mem (S n)) (scoh_view' (S n)) findom) as HH.
    match goal with
    | |- SCOH_step_no_lbl＊ (_, _) (_, ?X) => set (Y:=X)
    end.
    match goal with
    | H: _ -> SCOH_step_no_lbl＊ (_, _) (_, ?X) |- _ => set (Z:=X)
    end.
    arewrite (Y = Z).
    2: { apply HH. ins. apply SF0 in IN. unfold s in *. ins.
         unfold scoh_mem.
         assert (acts G w) as EW.
         { eapply tslot_defined_only_for_E; eauto. }
         assert (is_w w) as WW.
         { eapply tslot_defined_only_for_w; eauto. }
         assert (~ is_init w) as NINITW.
         { eapply tslot_defined_only_for_non_init_e; eauto. }
         splits; auto.
         { eapply tslot_defined_only_for_non_init; eauto. }
         { apply tslot_defined_only_for_non_empty_threads in IN. desf. eauto. }
         set (AA:=IN). apply tslot_lt_index in AA.
         eexists. right. exists (nu_inv w). splits.
         { lia. }
         unfold msg_of.
         rewrite nu_nu_inv; auto. desf. }
    extensionality t. extensionality l.
    unfold Y, Z, view_join.
    apply Nat.le_antisymm; apply Nat.max_lub.
    all: try by apply Nat.le_max_l.
    2: { etransitivity; [|by apply Nat.le_max_r].
         apply incl_max_of_list. red. ins. in_simp.
         eexists. splits; eauto. in_simp. splits; auto.
         unfold props_before, proj1_sig. do 2 desf. clear Heq.
         apply a0. clear dependent x0. apply SF0 in H0. red in H0.
         eexists. splits; eauto. }
    (* TODO: generalize to a lemma? *)
    unfold scoh_view', view_join. rewrite <- Nat.max_assoc.
    etransitivity; [|by apply Nat.le_max_r].
    apply le_max_of_list_l. ins. in_simp.
    unfold props_before, proj1_sig in *. do 2 desf. clear Heq Heq0.
    apply a2 in H0. desf.
    destruct (classic (m = n)); subst.
    { etransitivity; [|by apply Nat.le_max_r].
      apply in_max_of_list. in_simp. exists (t, x). splits; eauto.
      in_simp. splits; auto. apply SF0. red. ins. }
    etransitivity; [|by apply Nat.le_max_l].
    apply in_max_of_list. in_simp. exists x. splits; eauto.
    in_simp. splits; auto. apply a1. exists m. splits; auto. lia.
  Qed.

  Lemma scoh_step_all n (LT: lt_size n (acts G \₁ is_init)) :
    ((fun x => SCOH_step x (lab_of_ev (nu n))) ⨾ SCOH_step_no_lbl＊) 
                                             (scoh_state n)  (scoh_state (S n)).
  Proof.
    eexists. split.
    { by apply scoh_step_all'. }
      by apply scoh_props_steps.
  Qed.

End DECL_to_OP.


Lemma proj_ev_lab_of_ev (G : execution) (WF : Wf G) (FAIR : mem_fair G) RFC CONS
      nu (ENUM : enumerates nu (acts G \₁ is_init))
      n (LT : lt_size n (acts G \₁ is_init))
      (THRB : set_finite (fun t => exists x, acts G x /\ t = tid x)) :
  proj_ev (lab_of_ev WF ENUM RFC CONS FAIR THRB (nu n)) = (nu n).
Proof.
  unfold lab_of_ev; desf; ins.
  apply enumeratesE in ENUM; desc.
  specialize (RNG _ LT); red in RNG; desc; rewrite Heq in *; ins.
Qed.


Lemma SCOH_decl_implies_op G
      (WF : Wf G) (FAIR: mem_fair G)
      (RFC : rf_complete G)
      (CONS: scoh_consistent G)
      (THRB : set_finite (fun t => exists x, acts G x /\ t = tid x)) :
  exists s t,
    LTS_trace_param scoh_lts s t  /\
    run_fair s t /\
    trace_elems (trproj t) ≡₁ acts G \₁ is_init /\
    trace_wf (trproj t).
Proof.
  assert (IRRhb: irreflexive (hb G)) by (by apply CONS).
  assert (B: bounded_threads G).
  { by apply BOUND. }

  assert (dom_rel (lt ⨾ ⦗fun n => lt_size n (acts G \₁ is_init)⦘) ⊆₁
                  (fun n => lt_size n (acts G \₁ is_init))) as LTCLOS.
  { generalize (@lt_lt_size _ (acts G \₁ is_init)). basic_solver. }

  assert (forall l : SCOH_label, ~ SCOH_step_no_lbl_gen RFC FAIR l ≡ ∅₂ -> ~ is_external l)
    as NLBLNEXT.
  { ins. intros HH. red in HH. apply H. split.
    2: basic_solver.
    intros x y AA. cdes AA. desf. }
  assert (forall l, SCOH_step_no_lbl_gen RFC FAIR l ⊆ (fun rl x y => SCOH_step x rl y) l)
    as STEPINSTEP.
  { unfolder. intros l x y S. cdes S. eapply SCOHstep_internal; eauto. }

  forward eapply exec_exists_enum with (r := hb G) as (nu & ENUM & ORD);
    eauto using fsupp_hb, has_finite_antichains_sb with hahn.

  set (DD:=ENUM). apply enumeratesE in DD. desf. 

  assert ((fun n => lab_of_ev WF ENUM RFC CONS FAIR THRB (nu n))
            ↑₁ (fun n => lt_size n (acts G \₁ is_init)) ⊆₁ is_external) as LOELTS.
  { intros x [y HH]. desf. red. unfold lab_of_ev. desf.
    eapply RNG; eauto. red. desf. }

  edestruct compacted_trace_exists with 
      (lab     := fun n => lab_of_ev WF ENUM RFC CONS FAIR THRB (nu n))
      (labdom  := fun n => lt_size n (acts G \₁ is_init))
      (STEP    := fun rl : SCOH_label =>
                    fun (x y : State) => SCOH_step x rl y)
      (INTSTEP := SCOH_step_no_lbl_gen RFC FAIR)
      (cstate  := scoh_state WF ENUM RFC CONS FAIR THRB) as [ct CT]; auto.
  { ins. apply scoh_step_all; auto. }
  edestruct ct2t_exists as [t CT2T]; eauto.
  { apply deflabel. }
  set (TT:=CT2T). unfold ct2t in TT.

  assert (Sinit = ct2r ct 0) as SINIT.
  { arewrite (0 = cti2ri ct 0). rewrite wf_cti2ri.
    destruct (CT 0) as [AA]. desc. rewrite AA. ins.
      by rewrite scoh_state_init. }

  exists (ct2r ct).
  assert (X := scoh_step_all WF ENUM ORD RFC).
  tertium_non_datur (set_finite (acts G \₁ is_init)) as [FIN|INF].
  2: { exists (trace_inf t).
       assert (trace_elems (trproj (trace_inf t)) ≡₁ acts G \₁ is_init) as TETRP.
       { unfold trproj. rewrite trace_elems_map, trace_elems_filter.
         unfolder. split; intros x HH.
         2: { apply SUR in HH. desf.
              eexists. splits.
              3: by eapply proj_ev_lab_of_ev; eauto.
              2: { unfold lab_of_ev. desf.
                   exfalso. apply RNG in HH. apply HH. by rewrite Heq. }
              exists (cti2ri ct i).
              edestruct (TT (cti2ri ct i)) as [XX YY].
              { red. exists i. splits; auto.
                enough (cti2ri ct i < cti2ri ct (1 + i)); [lia|].
                apply cti2ri_S_mon. }
              desf.
              2: { exfalso. apply n. eauto. }
              desf. rewrite YY. unfold proj1_sig. do 2 desf. clear Heq.
              clear YY. apply cti2ri_inj in REP0; subst; eauto. }
         desf. red in HH. desf.
         edestruct (TT n) as [XX YY].
         { red. exists n. splits; auto.
           { by apply lt_size_infinite. }
           apply cti2ri_lt_n. }
         do 2 desf.
         2: { cdes YY. rewrite LBL in HH1. inv HH1. }
         rewrite YY. unfold proj1_sig. do 2 desf. clear Heq.
         assert (lt_size x (acts G \₁ is_init)) as QQ.
         { by apply lt_size_infinite. }
         rewrite proj_ev_lab_of_ev; auto. by apply RNG. }
       assert (trace_length (trproj (trace_inf t)) = NOinfinity) as TLINF.
       { unfold trace_length. desf. exfalso. apply INF. rewrite <- TETRP. exists l. ins. }
       assert (forall i d, trace_nth i (trproj (trace_inf t)) d = nu i) as TNNU.
       { intros i d. unfold trproj. 
         erewrite ct2t_infinite_filtered; eauto.
         2: { split; [basic_solver|]. red. ins. by apply lt_size_infinite. }
         ins. unfold proj_ev, lab_of_ev. desf.
         exfalso. eapply RNG with (i:=i); eauto.
         { by apply lt_size_infinite. }
         red. desf. }
       assert (trace_nodup (trproj (trace_inf t))) as TNDP.
       { red. ins. rewrite !TNNU. intros HH. assert (i <> j) as AA by lia.
         apply AA. apply INJ; auto. all: by apply lt_size_infinite. }
       ins. splits; ins.
       { ins. apply TT. red.
         exists i. splits; auto.
         { by apply lt_size_infinite. }
         apply cti2ri_lt_n. }
       2: { eapply trace_wf_helper; eauto.
            ins. apply ORD; auto. by apply sb_in_hb. }
       exists (fun t => exists x, acts G x /\ ~ is_init x /\ t = tid x). splits.
       { eapply set_finite_mori.
         2: by apply THRB.
         red. basic_solver. }
       { unfolder. ins. desf.
         edestruct (TT n) as [XX YY].
         { red. exists n. splits; auto.
           { by apply lt_size_infinite. }
           apply cti2ri_lt_n. }
         unfold proj1_sig in *. do 2 desf.
         { clear Heq. apply cti2ri_inj in REP; subst.
           arewrite (tid_of (t (cti2ri ct x)) = tid (nu x)).
           { rewrite YY. unfold lab_of_ev. desf. }
           assert ((acts G \₁ is_init) (nu x)) as [HH AA] by (by apply RNG).
           eauto. }
         cdes YY. rewrite LBL; ins; subst.
         exists e. splits; auto. intros HH. apply TBT.
         eapply wf_tid_init; eauto. }
       intros i tid [e FF] l tstamp. desf.
       destruct (classic
                   (exists st', SCOH_step (ct2r ct i) (SCOH_internal (tid e) l tstamp) st'))
         as [[st' ST]|NST].
       2: { exists i. splits; auto. right. ins. apply NST. eauto. }
       assert (compacted_trace_dom
                 (fun n => lt_size n (acts G \₁ is_init))
                 ct i) as CTD.
       { red. exists i. splits.
         { apply lt_size_infinite; auto. }
         enough (1 + i <= cti2ri ct (1 + i)); [lia|].
         apply cti2ri_lt_n. }
       edestruct wf_compacted_trace_dom with (i:=i) (ct:=ct) as [n HH]; eauto.
       assert (exists n',
                  i <= cti2ri ct n' /\
                  (internal_step (SCOH_step_no_lbl_gen RFC FAIR))^*
                                                               (ct2r ct i) (ct2r ct (cti2ri ct n')))
         as [n' [LL SS]].
       { desf.
         2: { eexists. splits; eauto. apply rt_refl. }
         edestruct c2tr_trace_istep_helper with (i:=i) (n:=n) as [n']; eauto. }
       clear dependent n. rename n' into n.
       assert (fst (ct2r ct i) = fst (ct2r ct (cti2ri ct n))) as SMEM.
       { eapply SCOH_steps_no_lbl_same_mem.
         eapply clos_refl_trans_mori; [|by apply SS].
           by unfold internal_step, SCOH_step_no_lbl. }
       inv ST.
       rewrite SMEM in *. rewrite wf_cti2ri in *.
       assert (bs (ct n) = scoh_state WF ENUM RFC CONS FAIR THRB n) as AA by apply CT.
       rewrite AA in *.
       unfold scoh_state, scoh_mem in MSG. ins.
       destruct MSG as [MSG|MSG].
       { red in MSG. desf. ins. lia. }
       red in MSG. desf. unfold msg_of in MSG0. inv MSG0. clear MSG0.
       assert (lt_size y (acts G \₁ is_init)) as LTY.
       { by apply lt_size_infinite. }
       edestruct tslot_defined with (t:=tid e) (w:=nu y) as [m HH]; eauto.
       { intros HH. apply FF0. eapply wf_tid_init; eauto. }
       1,2: by apply RNG.
       assert
         (ev_ts RFC FAIR (nu y) <= snd (ct2r ct (cti2ri ct (1 + m))) (tid e) (loc (nu y)))
         as CC.
       { rewrite wf_cti2ri. ins.
         assert (bs (ct (S m)) =
                 scoh_state WF ENUM RFC CONS FAIR THRB (S m)) as BB by apply CT.
         rewrite BB. unfold scoh_state.
         unfold scoh_view, view_join. ins.
         etransitivity; [|by apply Max.le_max_r].
         apply in_max_of_list. in_simp. exists (nu y). splits; auto.
         in_simp. splits; auto. unfold props_before, proj1_sig. do 2 desf. clear Heq.
         apply a0. eexists. splits; auto. eauto. }
       exists (cti2ri ct (1 + m)). split.
       2: { right. ins. inv STEP. lia. }
       apply Nat.le_ngt. intros RR.
       apply Nat.lt_le_incl in RR.
       eapply ct2t_steps with (ct:=ct) in RR; eauto.
       eapply SCOH_steps_view_mono with (t:=tid e) in RR.
       enough (ev_ts RFC FAIR (nu y) <= snd (ct2r ct i) (tid e) (loc (nu y))); [lia|].
       etransitivity; [by apply CC|]. by apply RR. }
  apply set_finiteE in FIN. desc.
  assert (forall i,
             i < length findom <->
             lt_size i (acts G \₁ is_init)) as LTSG.
  { ins. split; intros HH.
    { exists findom. splits; auto.
      ins. by apply FIN0. }
    red in HH. desc.
    enough (length dom <= length findom); [lia|].
    apply NoDup_incl_length; auto.
    red. ins. apply FIN0. by apply HH0. }
  assert ((fun y => y < length findom) ⊆₁ (fun n => lt_size n (acts G \₁ is_init))) as LTSGg.
  { unfolder. ins. by apply LTSG. }
  exists (trace_fin (map t (List.seq 0 (cti2ri ct (length findom))))).
  ins. splits; ins.
  { ins. rewrite nth_indep with (d':=t 0); auto.
    rewrite map_nth, seq_nth; ins.
    2: by rewrite map_length, seq_length in LLEN.
    apply TT. red.
    rewrite map_length, seq_length in LLEN.
    edestruct wf_compacted_trace_dom with (i:=i) (ct:=ct) as [n]; eauto.
    { red.
      assert (0 < length findom) as NNIL.
      { unfold cti2ri, cti2ri_helper in LLEN.
        destruct findom; ins; lia. }
      exists (Nat.pred (length findom)). splits.
      { apply LTSG. lia. }
      arewrite (1 + Nat.pred (length findom) = length findom) by lia.
      lia. }
    desf.
    { exists n. splits; auto. }
    exists (1 + n). splits; auto.
    2: { apply lt_le_S. apply cti2ri_S_mon. }
    apply LTSG. apply cti2ri_mon in LLEN. lia. }
  { rewrite filterP_map, map_map.
    unfolder. split; intros x HH.
    2: { apply SUR in HH. desf.
         edestruct (TT (cti2ri ct i)) as [XX YY].
         { red. exists i. splits; auto.
           enough (cti2ri ct i < cti2ri ct (1 + i)); [lia|].
           apply cti2ri_S_mon. }
         desf.
         2: { exfalso. apply n. eauto. }
         unfold proj1_sig in YY. do 2 desf. clear Heq.
         apply cti2ri_inj in REP; subst.
         apply cti2ri_inj in REP0; subst.
         in_simp. exists (cti2ri ct x).
         split.
         { rewrite YY. eapply proj_ev_lab_of_ev; eauto. }
         in_simp. split.
         2: { rewrite YY. unfold lab_of_ev. desf.
              exfalso. apply RNG in HH. apply HH. by rewrite Heq. }
         apply RNG in LBDOM. apply FIN0 in LBDOM.
         apply cti2ri_mon. by apply LTSG. }
    in_simp. rename x0 into n.
    edestruct (TT n) as [XX YY].
    { red.
      assert (0 < length findom) as NNIL.
      { unfold cti2ri, cti2ri_helper in HH0.
        destruct findom; ins; lia. }
      exists (Nat.pred (length findom)). splits.
      { apply LTSG. lia. }
      arewrite (1 + Nat.pred (length findom) = length findom) by lia. }
    do 2 desf.
    2: { cdes YY. rewrite LBL in HH1. inv HH1. }
    rewrite YY. unfold proj1_sig. do 2 desf. clear Heq.
    rewrite proj_ev_lab_of_ev; auto. apply RNG.
    clear YY. by apply cti2ri_inj in REP. }
  assert
  (forall i d
          (HH : NOmega.lt_nat_l
                  i (trace_length
                       (trproj (trace_fin
                                  (map t (List.seq 0 (cti2ri ct (length findom)))))))),
                trace_nth
                  i (trproj (trace_fin (map t (List.seq 0 (cti2ri ct (length findom)))))) d
                = nu i /\
                i < length findom) as AA.
  { intros i d. unfold trproj. erewrite ct2t_finite_filtered; eauto.
    ins. rewrite map_map. rewrite !map_length in HH.
    rewrite nth_indep with
        (d:=d)
        (d':=proj_ev (lab_of_ev WF ENUM RFC CONS FAIR THRB (nu 0))); auto.
    2: by rewrite map_length.
    rewrite seq_length in HH.
    rewrite map_nth with
        (f:=fun x : nat => proj_ev (lab_of_ev WF ENUM RFC CONS FAIR THRB (nu x))).
    rewrite seq_nth; auto; ins.
    rewrite proj_ev_lab_of_ev; auto. }
  eapply trace_wf_helper; eauto.
  4: by intros; destruct (AA i d) as [AI II]; auto.
  { ins. apply ORD; auto. by apply sb_in_hb. }
  { unfold trproj. erewrite ct2t_finite_filtered; eauto.
    ins. rewrite map_map. split; red; intros x HH.
    { apply in_map_iff in HH. desf.
      apply in_seq_iff in HH0. ins.
      assert (lt_size x0 (acts G \₁ is_init)) by (apply LTSGg; lia).
      rewrite proj_ev_lab_of_ev; auto. }
    apply SUR in HH. desf. erewrite <- proj_ev_lab_of_ev; eauto.
    apply in_map_iff. eexists; splits; eauto.
    apply in_seq_iff. ins. split; [lia|]. by apply LTSG. }
  unfold trproj. red. ins.
  destruct (AA i d) as [AI II]; [lia|].
  destruct (AA j d) as [AJ JJ]; auto.
  rewrite AI, AJ.
  intros HH. apply INJ in HH; auto.
  lia. 
Qed.
