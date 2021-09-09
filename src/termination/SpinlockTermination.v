From hahn Require Import Hahn.
From hahn Require Import HahnOmega.
Require Import PropExtensionality.
Require Import AuxRel.
Require Import Lia.
Require Import Labels.
Require Import Events.
Require Import Execution.
Require Import AuxProp.
Require Import TraceWf.
Require Import SetSize.
Require Import IndefiniteDescription.
Require Import Backport.
Require Import List.
Import ListNotations.
Require Import TerminationDecl.

Notation "'E' G" := (acts G) (at level 1). 
Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).
Notation "'Locs_' locs" := (fun x => In (loc x) locs) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

(* Spinlock busy-wait description sufficient for the proof:
   only states that two subsequent reads of 0 terminate loop. *)
Definition spinlock_wait_trace tr l :=
    ⟪BW_ITER: forall i d (DOM: NOmega.lt_nat_l i (trace_length tr)),
        exists thread index valr, trace_nth i tr d = ThreadEvent thread index (Aload l valr) ⟫ /\
    ⟪NEMPTY: trace_length tr <> NOnum 0⟫ /\
    ⟪TERM: forall i d (DOM': NOmega.lt_nat_l (i + 1) (trace_length tr)),
        (valr (trace_nth i tr d) = 0) /\ (valr (trace_nth (i + 1) tr d) = 0)
        -> trace_length tr = NOnum (i + 2) ⟫.

Definition cas_trace (tr: trace Event) l :=
  exists thread index,
    tr = trace_fin [ThreadEvent thread index (Armw l 0 1)]. 

Definition lock_trace tr l := exists tr_bw tr_cas,
    ⟪APP_L: tr = trace_app tr_bw tr_cas ⟫ /\
    ⟪BW_TR: spinlock_wait_trace tr_bw l⟫ /\
    ⟪CAS_TR: cas_trace tr_cas l⟫.

Definition unlock_trace tr l := 
  exists thread index,
    tr = trace_fin [ThreadEvent thread index (Astore l 0)]. 

(* Spinlock's lock and unlock calls with 'lock' at l. *)
Definition lock_unlock_execution (G: execution) (l: Loc) :=
  exists (tr: trace Event),
    ⟪L_U: exists tr_l tr_u, ⟪APP: tr = trace_app tr_l tr_u ⟫ /\
                       ⟪LOCK: lock_trace tr_l l ⟫ /\
                       ⟪UNLOCK: unlock_trace tr_u l ⟫ ⟫/\
    ⟪TR_E: trace_elems tr ≡₁ (E G) \₁ is_init ⟫ /\
    ⟪TR_WF: trace_wf tr ⟫. 

Definition spinlock_client_execution G l :=
  forall t Gt (TRE: thread_restricted_execution G t Gt),
    lock_unlock_execution Gt l.

Section SpinloopTermination. 
Variable G: execution.

Hypothesis (FAIR: mem_fair G).
Hypothesis (SCpL: SCpL G).
Hypothesis (WF: Wf G). 
Hypothesis (RFC: rf_complete G).
Hypothesis (BOUNDED_THREADS: exists n, forall e, E G e -> tid e < n).

Lemma last_write_zero w (SL_EXEC: spinlock_client_execution G (loc w))
      (MAXw: mo_max G w):
  valw w = 0. 
Proof.
  destruct w; [done| ]. 
  remember (ThreadEvent thread index l) as w. 
  set (Gt := (restrict G thread)). destruct Gt as [Gt TRE].
  red in SL_EXEC. desc. 
  specialize (SL_EXEC _ _ TRE). red in SL_EXEC. desc.
  do 2 (red in MAXw; desc). 
  assert (trace_elems tr w) as TRw.  
  { apply TR_E. split; [| by vauto]. 
    apply TRE. subst. split; auto. }
  red in LOCK. desc. subst tr_l tr. simpl in *.
  assert (~ trace_elems tr_bw w) as NRw.
  { red in BW_TR. desc.
    red. intros INw. apply trace_in_nth with (d := InitEvent 0) in INw. desc. 
    specialize BW_ITER with (d := InitEvent 0). specialize_full BW_ITER; eauto.
    desc. by rewrite <- INw0, BW_ITER in MAXw1. }
  destruct tr_bw; [| done].
  
  red in CAS_TR. red in UNLOCK. desc. subst tr_cas tr_u. simpl in *.
  remember (ThreadEvent thread1 index1 (Armw (loc w) 0 1)) as w_l.
  remember (ThreadEvent thread0 index0 (Astore (loc w) 0)) as w_u.  
  rewrite <- app_assoc in TRw. apply in_app_or in TRw. des; [done| ].
  simpl in TRw. des; [| | done].
  2: { by rewrite <- TRw, Heqw_u. }  
  
  subst w. rewrite <- TRw in *.
  exfalso. red in MAXw0. apply (MAXw0 w_u). red. splits.
  2: { done. }
  2: { split; [| by vauto].
       cut ((E Gt \₁ is_init) w_u).
       { destruct TRE. ins. red in H. desc. apply tr_acts_set in H. unfolder in H. by desc. }
       apply TR_E. rewrite <- app_assoc. do 2 apply in_app_r. done. } 
  apply sb_w_loc; try by vauto.
  destruct TRE. rewrite tr_acts_set in TR_E. destruct TR_E.
  forward eapply (H w_l) as Wl; [| forward eapply (H w_u) as Wu].
  1, 2: repeat rewrite in_app_iff; simpl; tauto. 
  unfolder in Wl. unfolder in Wu. desc.
  red. apply seq_eqv_lr. splits; auto. 
  subst w_l w_u. simpl in *. split; [congruence| ].
  
  (* red in TR_WF. simpl in TR_WF. *)

  rewrite <- app_assoc in TR_WF. apply trace_wf_fin_app with (l1 := l0) (tr2 := trace_fin _) in TR_WF. 
  simpl in TR_WF. red in TR_WF.  
  specialize (TR_WF 0 1) with (d := InitEvent 0). simpl in TR_WF.
  apply TR_WF; [lia | lia | congruence].  
Qed. 

Lemma sl_fin_w l (SL_EXEC: spinlock_client_execution G l):
  set_finite (E G ∩₁ (fun a : Event => is_w a) ∩₁ Loc_ l).
Proof. 
  rewrite events_separation, <- !set_bunion_inter_compat_r. 
  cdes BOUNDED_THREADS.  
  arewrite ((fun _ : nat => True) ≡₁ (fun i => i < n) ∪₁ (fun i => i >= n)).
  { unfolder. split; lia. }
  rewrite set_bunion_union_l. apply set_finite_union. split.
  2: { eapply set_finite_more; [|eapply set_finite_empty].
       split; [| basic_solver].
       apply set_subset_bunion_l. intros thread GE. 
       destruct (restrict G thread) as [Gt TRE]. simpl in *. destruct TRE. 
       red. ins. unfolder in H. desc. specialize (BOUNDED_THREADS0 x). specialize_full BOUNDED_THREADS0.
       { apply tr_acts_set in H. red in H. by desc.  }
       apply tr_acts_set in H. red in H. desc. lia. }
  apply set_finite_bunion; [apply set_finite_lt| ]. 
  intros thread LT.
  destruct (restrict G thread) as [Gt TRE]. simpl in *. 
  red in SL_EXEC. specialize_full SL_EXEC; eauto. red in SL_EXEC. desc.
  
  rewrite set_union_minus_alt with (s' := is_init). apply set_finite_union. split.
  { exists [InitEvent l]. unfolder. ins. desc. destruct x; vauto. }     
  rewrite set_interA, <- set_inter_minus_l. rewrite <- TR_E.
  red in LOCK. desc. 
  assert (trace_elems tr_bw ∩₁ is_w ≡₁ ∅) as BW_NO_W.
  { split; [| basic_solver]. red. ins. red in H. desc.
    red in BW_TR. desc.
    apply trace_in_nth with (d := InitEvent 0) in H. desc.
    specialize BW_ITER with (d:= InitEvent 0). specialize_full BW_ITER; eauto.
    desc. subst x. rewrite BW_ITER in H0. by unfold is_w in H0. }
  subst tr tr_l. rewrite <- trace_app_assoc. rewrite trace_elems_app.
  rewrite set_inter_union_l. rewrite <- set_interA, BW_NO_W, set_inter_empty_l, set_union_empty_l.
  destruct (excluded_middle_informative (trace_finite tr_bw)).
  2: { rewrite set_inter_empty_l. apply set_finite_empty. }
  red in CAS_TR. red in UNLOCK. desc. subst tr_cas tr_u. simpl.
  red. exists [ThreadEvent thread1 index0 (Armw l 0 1); ThreadEvent thread0 index (Astore l 0)].
  ins. unfolder in IN. desc. des; auto. 
Qed. 


Theorem spinlock_client_terminates_impl l
        (SL_EXEC: spinlock_client_execution G l):
  set_finite (E G \₁ is_init).
Proof.  
  contra INF. apply (not_iff_compat (fin_iff_tre_fin G BOUNDED_THREADS)) in INF.
  apply (@not_all_ex_not Tid _) in INF as [thread INF].   
  apply (@not_all_ex_not _ _) in INF as [Gt INF].
  apply imply_to_and in INF as [TRE INFt].
  red in SL_EXEC. desc. pose proof SL_EXEC as SL_EXEC0. specialize_full SL_EXEC; eauto.
  red in SL_EXEC. desc. red in LOCK. desc.
  
  assert (~ trace_finite tr_bw) as INF_BW.
  { destruct tr_bw.
    2: { red. ins. red in H. by desc. }
    red in CAS_TR. red in UNLOCK. desc. subst tr_cas tr_u tr_l tr.
    simpl in TR_E. destruct INFt.
    rewrite <- TR_E. by vauto. } 
  assert (trace_nodup tr_bw) as NODUP_BW.
  { apply trace_wf_nodup.
    subst tr tr_l. rewrite <- trace_app_assoc in TR_WF.
    eapply trace_wf_app; eauto. }

  forward eapply (inf_reads_latest_full tr_bw G [l]) as [i LIMIT]; eauto.
  { red. ins. apply set_finite_mori with (y := trace_elems tr_bw) in H.
    { by apply nodup_trace_elems in H. } 
    red. apply set_subset_inter_r. split; [done| ].
    red. ins. apply trace_in_nth with (d := InitEvent 0) in H0. desc.
    red in BW_TR. desc. specialize (BW_ITER n (InitEvent 0) H0).
    desc. subst. by rewrite BW_ITER. }
  { subst tr tr_l. repeat rewrite trace_elems_app in TR_E.
    destruct TRE. rewrite tr_acts_set in TR_E.
    eapply set_subset_trans.
    { eapply set_equiv_subset; [reflexivity| symmetry; apply TR_E | basic_solver]. }
    basic_solver. }
  { red. intros e [INe Re]. simpl. 
    red in BW_TR. desc. eapply trace_in_nth with (d := InitEvent 0) in INe.
    desc. specialize_full BW_ITER; eauto. desc.
    rewrite <- INe0, BW_ITER. vauto. }
  { arewrite (Locs_ [l] ⊆₁ Loc_ l) by basic_solver. by apply sl_fin_w. } 

  red in BW_TR. desc.
  destruct tr_bw as [| ev_enum]. 
  { apply INF_BW. vauto. }
  simpl in *.

  assert (forall j, exists w, rf G w (ev_enum j) /\
                    (E G ∩₁ is_w ∩₁ Loc_ l) w) as RF.
  { ins.
    specialize (BW_ITER j (InitEvent 0) I). desc.
    forward eapply (RFC (ev_enum j)) as [w RF].
    { split; [| by rewrite BW_ITER].
      cut ((E Gt \₁ is_init) (ev_enum j)).
      { intros [ET NI]. destruct TRE. by apply tr_acts_set in ET as [EG _]. }
      apply TR_E. subst tr tr_l. apply trace_elems_app. left. vauto. }
    exists w. split; auto.
    unfolder. splits; [apply wf_rfE in RF | apply wf_rfD in RF | apply wf_rfl in RF]; try (by (apply seq_eqv_lr in RF; desc)); auto. 
    by rewrite BW_ITER in RF. }
  
  pose proof (RF i) as [wi [RFi Wi]]. forward eapply (LIMIT i) as MAXi; [lia| by vauto| ]. 
  pose proof (RF (i + 1)) as [wi' [RFi' Wi']]. forward eapply (LIMIT (i + 1)) as MAXi'; [lia| by vauto| ].

  assert (wi' = wi); [| subst wi']. 
  { red in MAXi. red in MAXi'. desc. eapply max_elt_unique; [apply co_sto| | | |]; eauto. 
    1, 2: eapply set_subset_max_elt; eauto; basic_solver. }

  apply wf_rfv in RFi; [apply wf_rfv in RFi'| ]; auto.
  forward eapply last_write_zero as ZERO; eauto.
  { replace (loc wi) with l; vauto. unfolder in Wi. by desc. }
  
  forward eapply TERM with (i := i); vauto. split; congruence. 
Qed.

End SpinloopTermination. 

Theorem spinlock_client_terminates
        (G : execution)
        (FAIR : mem_fair G)
        (SCpL : Execution.SCpL G)
        (WF : Wf G)
        (RFC : rf_complete G)
        (BOUNDED_THREADS : exists n, forall e : Event, E G e -> tid e < n)
        (l : Loc)
        (SL_EXEC : spinlock_client_execution G l)
  :
  set_finite (E G \₁ is_init). 
Proof. eapply spinlock_client_terminates_impl; eauto. Qed. 

Redirect "axioms_spinlock" Print Assumptions spinlock_client_terminates.
  
