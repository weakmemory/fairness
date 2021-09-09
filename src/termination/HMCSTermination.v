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
Require Import RAop. 

Require Import TSO.
Require Import SC.
Require Import RAop.
Require Import ModelsRelationships.

Notation "'E' G" := (acts G) (at level 1). 
Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).
Notation "'Locs_' locs" := (fun x => In (loc x) locs) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'Valr_' v" := (fun x => valr x = v) (at level 1).
Notation "'Valw_' v" := (fun x => valw x = v) (at level 1).

Set Implicit Arguments. 

Ltac unfolder' := unfold trace_finite, set_compl, cross_rel, set_minus, set_inter, set_union, is_r, is_r_l, is_w, is_w_l, is_rmw, is_rmw_l, is_init, same_loc, loc, loc_l, valr, valr_l, valw, valw_l, lab, tid in *.

Definition d_ := InitEvent 0.

Section FenceTrace.
  (** Currently fence traces are defined as empty which is enough to prove properties not related to RC11 ***)
  
  Definition release_fence (tr: trace Event) :=
    tr = trace_fin [].
  
  Lemma release_fence_no_write (tr: trace Event) (REL: release_fence tr):
    trace_elems tr ∩₁ is_w ⊆₁ ∅.
  Proof. red in REL. subst tr. basic_solver. Qed. 
  
  Lemma rel_fin tr  (REL: release_fence tr):
    trace_finite tr.
  Proof. red in REL. subst tr. by exists []. Qed.

  Opaque release_fence. 

  
  Definition acquire_fence (tr: trace Event) :=
    tr = trace_fin [].
  
  Lemma acquire_fence_no_write (tr: trace Event) (ACQ: acquire_fence tr):
    trace_elems tr ∩₁ is_w ⊆₁ ∅.
  Proof. red in ACQ. subst tr. basic_solver. Qed. 
  
  Lemma acq_fin tr (ACQ: acquire_fence tr):
    trace_finite tr.
  Proof. red in ACQ. subst tr. by exists []. Qed.

  Opaque acquire_fence. 


  Lemma rel_not_inf_length tr (REL: release_fence tr):
    trace_length tr <> NOinfinity.
  Proof. edestruct rel_fin, tr; vauto. Qed.
  
  Lemma acq_not_inf_length tr (ACQ: acquire_fence tr):
    trace_length tr <> NOinfinity.
  Proof. edestruct acq_fin, tr; vauto. Qed.

End FenceTrace. 

Section HMCS.

  Definition hmcs_acquire_end lock (statuses nexts: list Loc) (thread: Tid) tr :=
    (* exists pred index0 index1 , *)
    exists index pred tr_acq_end,
      let swap := trace_fin [ThreadEvent thread index (Armw lock pred thread)] in
      tr = trace_app swap tr_acq_end /\
      (if (NPeano.Nat.eq_dec pred 0)
       then
         (exists index0,
             let w := ThreadEvent thread index0 (Astore (nth thread statuses 0) 0) in
             tr_acq_end = trace_fin [w])
       else
         (exists index0 tr_acq_wait,
             let w_pred := ThreadEvent thread index0 (Astore (nth pred nexts 0) thread) in
             tr_acq_end = trace_app (trace_fin [w_pred]) tr_acq_wait /\
             busywait (nth thread statuses 0) tr_acq_wait (eq 0))
      ).

  

  Definition hmcs_acquire_real lock (statuses nexts: list Loc) thread tr :=
    exists index tr_acq_end tr_relf,
      let writes := trace_fin
          [ThreadEvent thread index (Astore (nth thread statuses 0) 1);
           ThreadEvent thread (index + 1) (Astore (nth thread nexts 0) 0)] in
      tr = trace_app (trace_app writes tr_relf) tr_acq_end /\
      release_fence tr_relf /\
      hmcs_acquire_end lock statuses nexts thread tr_acq_end. 
             
  
  Definition hmcs_acquire lock statuses nexts thread tr :=
    exists tr_acqr tr_acqf,
      tr = trace_app tr_acqr tr_acqf /\
      hmcs_acquire_real lock statuses nexts thread tr_acqr /\
      acquire_fence tr_acqf.

  Definition trace_last {A: Type} (tr: trace A) (d: A) :=
    match tr with
    | trace_fin l => last l d
    | trace_inf _ => d
    end. 

  Definition hmcs_lock_pass (statuses: list Loc) tr succ :=
    exists thread index,
      let w := Astore (nth succ statuses 0) 0 in
      tr = trace_fin [ThreadEvent thread index w].

  Definition no_succ_release lock thread tr :=
    exists index, let rmw := ThreadEvent thread index (Armw lock thread 0) in
             tr = trace_fin [rmw]. 
  
  Definition succ_wait_release lock (nexts: list Loc) thread tr :=
    exists index other tr_succ_wait,
      let r_late := ThreadEvent thread index (Aload lock other) in
      tr = trace_app (trace_fin [r_late]) tr_succ_wait /\
      other <> thread /\
      busywait (nth thread nexts 0) tr_succ_wait (set_compl (eq 0)).
  
  Definition hmcs_release_real lock (statuses nexts: list Loc) thread tr :=
    exists index succ tr_acqf tr_rel_end,
      let r_succ := ThreadEvent thread index (Aload (nth thread nexts 0) succ) in
      tr = trace_app (trace_app (trace_fin [r_succ]) tr_acqf) tr_rel_end /\
      acquire_fence tr_acqf /\
      if (NPeano.Nat.eq_dec succ 0)
      then (no_succ_release lock thread tr_rel_end \/
            (exists tr_wait tr_pass,
                tr_rel_end = trace_app tr_wait tr_pass /\
                succ_wait_release lock nexts thread tr_wait /\
                hmcs_lock_pass statuses tr_pass (valr (trace_last tr_wait d_))))
      else hmcs_lock_pass statuses tr_rel_end succ.
           
  Definition hmcs_release lock statuses nexts thread tr :=
    exists tr_relf tr_relr,
      tr = trace_app tr_relf tr_relr /\
      release_fence tr_relf /\
      hmcs_release_real lock statuses nexts thread tr_relr. 

  (* HMCS lock's lock and unlock calls with 'Lock' at lock.
     QNode.locked and QNode.next are represented by 
     'statuses' and 'nexts' arrays. *)
  Definition hmcs_acqiure_release (lock: Loc) (statuses nexts: list Loc)
             (thread: Tid) (tr: trace Event) :=
    exists tr_acq tr_rel,
      ⟪APP: tr = trace_app tr_acq tr_rel ⟫ /\
      ⟪ACQ: hmcs_acquire lock statuses nexts thread tr_acq ⟫ /\
      ⟪REL: hmcs_release lock statuses nexts thread tr_rel ⟫.

End HMCS.

Section HMCSClient.
  Variable n_threads: nat.
    
  Definition hmcs_thread lock statuses nexts G tr thread :=
    let (Gt, _) := restrict G thread in
    ⟪HMCS: hmcs_acqiure_release lock statuses nexts thread tr ⟫ /\
    ⟪TR_E: trace_elems tr ≡₁ E Gt ⟫ /\
    ⟪TR_WF: trace_wf tr ⟫.
  
  Definition hmcs_client lock statuses nexts G :=
    forall thread (NINIT: thread <> 0) (CNT: thread < n_threads),
    exists tr, hmcs_thread lock statuses nexts G tr thread.

End HMCSClient.


Section HMCSClientTermination.
  Variable n_threads: nat. 
  Variables (lock: Loc) (statuses nexts: list Loc). 
  Hypothesis DISJ_LOC: NoDup (lock :: statuses ++ nexts).
  Hypothesis (STATUSES_LEN: ⟪STATUSES_LEN: length statuses = n_threads⟫)
             (NEXTS_LEN: ⟪NEXTS_LEN: length nexts = n_threads⟫).
  Hypothesis LOCS_NO0: ~ In 0 (lock :: statuses ++ nexts). 

  Variable G: execution. 
  Hypothesis HMCS_CLIENT: hmcs_client n_threads lock statuses nexts G. 
  Hypothesis FAIR: mem_fair G.
  Hypothesis SCpL: SCpL G.
  Hypothesis WF: Wf G.
  Hypothesis RFC: rf_complete G.
  Hypothesis BOUNDED_THREADS: (fun thread => exists e, (E G ∩₁ Tid_ thread) e)
                                ≡₁ (fun thread => thread < n_threads).

  Hypothesis MODEL: ⟪MODEL: sc_consistent G \/ TSO_consistent G \/ ra_consistent G⟫.

  Lemma ra_no_cycle (RA: ra_consistent G):
    ~ exists e, (sb G ⨾ co G ⨾ sb G ⨾ ((restr_rel is_rmw (rf G))^* ⨾ rf G)) e e.
  Proof.
    intros CYCLE. desc. destruct CYCLE as [w1 [SB1 [w2 [CO HB]]]]. 
    red in RA. desc. destruct (RA w2).
    exists w1. split; [| basic_solver].
    red. apply ct_unit. exists e. split; [| basic_solver].
    eapply hahn_inclusion_exp in HB.
    2: { rewrite inclusion_restr, <- ct_end. apply inclusion_refl. }
    apply ct_begin. destruct HB. desc. exists x. split; [basic_solver 10| ].
    eapply clos_refl_trans_mori; [apply inclusion_union_r2| by apply inclusion_t_rt].
  Qed.

  Lemma no_cycle: ~ exists e, (sb G ⨾ co G ⨾ sb G ⨾ ((restr_rel is_rmw (rf G))^* ⨾ rf G)) e e.
  Proof.
    enough (ra_consistent G) as RA; [by apply ra_no_cycle| ].
    cdes MODEL.
    des; [eapply sc_implies_tso, tso_implies_ra in MODEL0 | apply tso_implies_ra in MODEL0|]; auto. 
  Qed. 
    
  Lemma tid0_init: E G ∩₁ Tid_ 0 ≡₁ E G ∩₁ is_init.
  Proof.
    enough (forall e (Ee: E G e), Tid_ 0 e <-> is_init e) as EQUIV.
    { unfolder. split; ins; desc; split; try apply EQUIV; auto. } 
    ins. eapply wf_tid_init; eauto.
  Qed.

  Ltac by_subst := by (subst; unfolder'; simpl in *; (lia || des; (vauto || lia))).
  Ltac by_destruct x := by (destruct x as [| t_ ind_ l_]; [| destruct l_]; by_subst). 
  
  Definition lock_order: relation Tid :=
    fun t1 t2 => exists w1 w2,
        (E G ∩₁ Tid_ t1 ∩₁ is_rmw ∩₁ Loc_ lock ∩₁ Valw_ t1) w1 /\
        (E G ∩₁ Tid_ t2 ∩₁ is_rmw ∩₁ Loc_ lock ∩₁ Valw_ t2) w2 /\
        co G w1 w2.

  Lemma NoDup_disj_elems {A: Type} (l1 l2: list A) (NODUP: NoDup (l1 ++ l2)):
    (fun a => In a l1) ∩₁ (fun a => In a l2) ⊆₁ ∅.
  Proof.
    remember (l1 ++ l2) as l. generalize dependent l1. generalize dependent l2.
    induction l.
    { ins. destruct l1, l2; basic_solver. }
    ins. destruct l1; [basic_solver| ].
    simpl in *. inversion Heql. subst. clear Heql.
    inversion NODUP. subst.
    specialize (IHl H2 _ _ eq_refl).
    arewrite ((fun a => a0 = a \/ In a l1) ≡₁ eq a0 ∪₁ (fun a => In a l1)) by basic_solver.
    rewrite set_inter_union_l. apply set_subset_union_l. split; auto.
    red. ins. apply H1. apply in_app_r. by_subst.
  Qed.            
    
  Ltac trace_app_elems_exh :=
    match goal with
    | H: trace_elems (trace_app ?t1 ?t2) ?e |- _ =>
      apply trace_in_app in H; destruct H as [H | H]; desc; trace_app_elems_exh
    | H: trace_elems (trace_fin ?l) ?e |- _ =>
      simpl in H; des; try done
    | _ => auto
    end. 

  Ltac unfold_acquire := unfold hmcs_acquire, hmcs_acquire_real, hmcs_acquire_end in *.
  Ltac unfold_release := unfold hmcs_release, hmcs_release_real, no_succ_release, succ_wait_release, hmcs_lock_pass in *.

  Lemma disj_locs thread (BOUND: thread < n_threads):
    nth thread statuses 0 <> lock /\ nth thread nexts 0 <> lock /\
    nth thread statuses 0 <> nth thread nexts 0. 
  Proof.
    remember (lock :: statuses ++ nexts) as locs.
    replace lock with (nth 0 locs 0) by by_subst.
    replace (nth thread statuses 0) with (nth (thread + 1) locs 0).
    2: { subst locs. rewrite PeanoNat.Nat.add_1_r. simpl.
         apply app_nth1. congruence. }
    replace (nth thread nexts 0) with (nth (thread + 1 + n_threads) locs 0).
    2: { subst locs. rewrite PeanoNat.Nat.add_1_r. simpl.
         rewrite <- STATUSES_LEN, NPeano.Nat.add_comm. apply app_nth2_plus. }
    splits; red; intros EQ; apply NoDup_nth in EQ; try by_subst; subst locs; simpl; rewrite app_length, STATUSES_LEN, NEXTS_LEN; lia. 
  Qed.     

  Lemma nexts0_iff_overflow thread:
    nth thread nexts 0 = 0 <-> n_threads <= thread. 
  Proof.
    split.
    2: { ins. rewrite nth_overflow; congruence. }
    intros EQ0.
    destruct (PeanoNat.Nat.lt_ge_cases thread n_threads); auto.
    forward eapply (@nth_In _ thread nexts 0) as IN; [congruence| ].
    rewrite EQ0 in IN. destruct LOCS_NO0.
    simpl. right. apply in_app_iff. tauto.  
  Qed. 

  Lemma statuses0_iff_overflow thread:
    nth thread statuses 0 = 0 <-> n_threads <= thread. 
  Proof.
    split.
    2: { ins. rewrite nth_overflow; congruence. }
    intros EQ0.
    destruct (PeanoNat.Nat.lt_ge_cases thread n_threads); auto.
    forward eapply (@nth_In _ thread statuses 0) as IN; [congruence| ].
    rewrite EQ0 in IN. destruct LOCS_NO0.
    simpl. right. apply in_app_iff. tauto.  
  Qed. 

  Lemma lock_writes:
    E G ∩₁ is_w ∩₁ Loc_ lock \₁ is_init ⊆₁ is_rmw ∩₁ (fun e => valw e = tid e \/ valw e = 0 /\ valr e = tid e).
  Proof.
    red. intros rmw RMW.
    remember (tid rmw) as thread. assert (⟪TID: Tid_ thread rmw⟫) by by_subst. clear Heqthread. 
    cdes HMCS_CLIENT. specialize (HMCS_CLIENT0 thread). specialize_full HMCS_CLIENT0.
    { red. ins. subst thread. eapply wf_tid_init in H; by_subst. }
    { apply BOUNDED_THREADS. by_subst. }
    desc. red in HMCS_CLIENT0. destruct (restrict G thread) as [Gt [TRE]]. desc.
    assert (trace_elems tr rmw) as TRrmw.
    { apply TR_E, TRE. by_subst. }
    forward eapply (@disj_locs thread) as LOC; [apply BOUNDED_THREADS; by_subst|].
    red in HMCS. desc. unfold_acquire. unfold_release. desc. subst.
    trace_app_elems_exh; try by_subst. 
    { edestruct (@release_fence_no_write tr_relf0); by_subst. }
    { destruct (NPeano.Nat.eq_dec pred 0); desc; subst.
      { simpl in TRrmw0; des; by_subst. }
      { trace_app_elems_exh.
        { destruct (PeanoNat.Nat.lt_ge_cases pred n_threads).
          { forward eapply (@disj_locs pred) as LOC'; auto. 
            desc. destruct LOC'0. by_subst. }
          { apply nexts0_iff_overflow in H0.
            by_subst. }
        }
        eapply wait_trace_reads in TRrmw2; eauto. by_subst. }
    }
    { edestruct (@acquire_fence_no_write tr_acqf); by_subst. }
    { edestruct (@release_fence_no_write tr_relf); by_subst. }
    { edestruct (@acquire_fence_no_write tr_acqf0); by_subst. }
    { destruct (NPeano.Nat.eq_dec succ 0).
      { des.
        { subst. trace_app_elems_exh. by_subst. } 
        { subst tr_rel_end tr_wait. trace_app_elems_exh; try by_subst. 
          { eapply wait_trace_reads in TRrmw3; try by_subst. }
          subst tr_pass.
          remember (valr (trace_last (trace_app (trace_fin [ThreadEvent thread index3 (Aload lock other)]) tr_succ_wait) d_)) as addr.
          simpl in TRrmw3. des; [| done].
          destruct (PeanoNat.Nat.lt_ge_cases addr n_threads).
          { forward eapply (@disj_locs addr); auto. ins. desc. by_subst. }
          { apply statuses0_iff_overflow in H0.
            rewrite H0 in TRrmw3. by_subst. }
        }
      }            
      desc. subst. trace_app_elems_exh; try by_subst. 
      forward eapply (@disj_locs succ) as LOC'.
      { destruct (PeanoNat.Nat.lt_ge_cases succ n_threads); auto.
        apply statuses0_iff_overflow in H0. by_subst. }
      by_subst. }
  Qed.

  Lemma trace_app_not_inf {A: Type} (tr1 tr2: trace A):
    trace_length (trace_app tr1 tr2) <> NOinfinity <->
    (trace_length tr1 <> NOinfinity /\ trace_length tr2 <> NOinfinity).
  Proof using.
    clear dependent n_threads. clear dependent lock.
    destruct tr1, tr2; try by_subst; tauto. 
  Qed.

  Ltac trace_length_not_inf :=
    match goal with
    | |- trace_length (trace_app ?t1 ?t2) <> NOinfinity =>
      apply trace_app_not_inf; split; trace_length_not_inf
    | H: trace_finite ?t |- trace_length ?t <> NOinfinity =>
      destruct t; by_subst
    | |- trace_length ?t <> NOinfinity =>
        by ((by apply rel_not_inf_length) || (by apply acq_not_inf_length) || by_subst)
    | |- _ => auto
    end. 
  
  Ltac fin_trace_solver :=
    match goal with
    | |- trace_finite (trace_app ?t1 ?t2) => apply trace_app_finite; split; fin_trace_solver
    | |- trace_length ?t <> NOinfinity => trace_length_not_inf
    | |- _ => by_subst || by auto using rel_fin, acq_fin
    end. 
  
  Ltac trace_elems_solver :=
    match goal with
    | |- trace_elems (trace_app ?t1 ?t2) ?e => apply trace_in_app; ((left; trace_elems_solver) || (right; split; [trace_length_not_inf| ]; trace_elems_solver))
    | |- _ => by_subst
    end.

  Lemma lock_write_unique thread (NINIT: thread <> 0) (CNT: thread < n_threads):
    exists! rmw, (E G ∩₁ is_rmw ∩₁ Loc_ lock ∩₁ Valw_ thread) rmw.
  Proof.
    cdes HMCS_CLIENT. specialize_full HMCS_CLIENT0; eauto. desc.
    red in HMCS_CLIENT0. destruct (restrict G thread) as [Gt [TRE]]. desc.
    red in HMCS. desc. red in ACQ. desc. red in ACQ0. desc. red in ACQ3. desc.
    remember (ThreadEvent thread index0 (Armw lock pred thread)) as rmw. exists rmw.

    red. split.
    { assert (trace_elems tr rmw) as TRrmw.
      { subst tr tr_acq tr_acqr tr_acq_end.
        do 2 (apply trace_in_app; left). apply trace_in_app.
        right. split; [fin_trace_solver| ]. 
        apply trace_in_app. left. by_subst. } 
      apply TR_E, TRE in TRrmw. by_subst. }
    { intros rmw' RMW'.
      forward eapply (@lock_writes rmw') as RMW'_; [by_destruct rmw'| ].
      assert (trace_elems tr rmw') as TRrmw'.
      { apply TR_E, TRE. by_subst. }
      subst tr. apply trace_in_app in TRrmw'. des.
      { subst tr_acq. apply trace_in_app in TRrmw'. des.
        2: { edestruct acquire_fence_no_write; eauto. by_destruct rmw'. }
        subst tr_acqr. apply trace_in_app in TRrmw'. des.
        { apply trace_in_app in TRrmw'. des.
          { simpl in TRrmw'. des; by_subst. }
          { edestruct (@release_fence_no_write tr_relf); auto. by_destruct rmw'. }
        }
        subst tr_acq_end. apply trace_in_app in TRrmw'0. des; [by_subst| ].
        destruct (NPeano.Nat.eq_dec pred 0); desc; subst tr_acq_end0. 
        { simpl in TRrmw'1. des; by_subst. }
        { apply trace_in_app in TRrmw'1. des; [simpl in TRrmw'1; des; by_subst| ].
          eapply wait_trace_reads in TRrmw'2; eauto.
          forward eapply (NoDup_disj_elems [lock] statuses) as DISJ.
          { simpl. eapply nodup_append_left.
            erewrite <- app_comm_cons; eauto. }
          destruct (DISJ lock). split; [by_subst| ].
          replace lock with (nth thread statuses 0); [| by_subst]. 
          apply nth_In. rewrite STATUSES_LEN. by_subst. }
      }
      red in REL. desc. subst tr_rel. apply trace_in_app in TRrmw'0. des.      
      { edestruct (@release_fence_no_write tr_relf0); eauto. by_destruct rmw'. }
      red in REL1. desc. subst tr_relr. apply trace_in_app in TRrmw'1. des.
      { apply trace_in_app in TRrmw'1. des; [simpl in *; des; by_subst| ].
        edestruct acquire_fence_no_write; eauto. by_destruct rmw'. }
      destruct (NPeano.Nat.eq_dec succ 0).
      { des. 
        { red in REL3. desc. subst tr_rel_end.        
          red in TRrmw'2. simpl in TRrmw'2. des; by_subst. }
        subst tr_rel_end.
        apply trace_in_app in TRrmw'2.
        des; [| red in REL4; desc; by_subst].
        red in REL1. desc. subst tr_wait.
        apply trace_in_app in TRrmw'2. des; [simpl in *; des; by_subst| ].
        eapply wait_trace_reads in REL5; eauto.
        forward eapply NoDup_disj_elems as DISJ. 
        { erewrite <- app_comm_cons; eauto. }
        destruct (DISJ lock). split; [by_subst| ].
        replace lock with (nth thread nexts 0).
        2: { specialize (REL5 _ TRrmw'3). by_subst. } 
        apply nth_In. rewrite NEXTS_LEN. by_subst. 
      }
      red in REL3. desc. subst tr_rel_end. simpl in *. des; by_subst. }
  Qed.


  Lemma unique_eq {A: Type} (S: A -> Prop) x y
        (UNIQUIE: exists! z, S z)
        (Sx: S x) (Sy: S y):
    x = y.
  Proof. destruct UNIQUIE. transitivity x0; [symmetry| ]; apply H; auto. Qed.

  Lemma unique_rmw_helper thread (NINIT: thread <> 0):
    (E G ∩₁ Tid_ thread ∩₁ is_rmw ∩₁ Loc_ lock ∩₁ Valw_ thread) ≡₁
    (E G ∩₁ is_rmw ∩₁ Loc_ lock ∩₁ Valw_ thread).
  Proof.
    split; [basic_solver| ].
    red. ins.
    forward eapply (@lock_writes x) as L; [by_destruct x| ]. 
    destruct L. des; by_subst.
  Qed.

  Lemma rmws_atomicity_violation_helper w rmw1 rmw2
        (RF1: rf G w rmw1) (RF2: rf G w rmw2)
        (RMW1: is_rmw rmw1) (RMW2: is_rmw rmw2)
        (CO: co G rmw1 rmw2):
    False.
  Proof.
    forward eapply rmw_atom as ATOM_G; eauto. 
    forward eapply (@ATOM_G w rmw2) as ATOM.
    { destruct rmw2; [| destruct l]; by_subst. }
    red in ATOM. desc. apply ATOM0.
    exists rmw1. split; eauto.
    apply rf_co_helper; eauto. destruct rmw1; [| destruct l]; by_subst. 
  Qed.

  Lemma rmws_atomicity_violation w rmw1 rmw2
        (RF1: rf G w rmw1) (RF2: rf G w rmw2)
        (RMW1: is_rmw rmw1) (RMW2: is_rmw rmw2):
    rmw1 = rmw2.
  Proof.
    contra NEQ. 
    forward eapply (@wf_co_total _ WF (loc w)) with (a := rmw1) (b := rmw2)
      as CO; auto.
    { apply exploit_rf in RF1; auto. destruct rmw1; [| destruct l]; by_subst. }
    { apply exploit_rf in RF2; auto. destruct rmw2; [| destruct l]; by_subst. }
    des.
      all: eapply rmws_atomicity_violation_helper; [.. | apply CO]; eauto.
  Qed.
  
  Lemma lock_write_unique_reads rmw1 rmw2
        (RMW1: (E G ∩₁ is_rmw ∩₁ Loc_ lock) rmw1)
        (RMW2: (E G ∩₁ is_rmw ∩₁ Loc_ lock) rmw2)
        (VALR_EQ: valr rmw1 = valr rmw2)
        (VALR_N0: valr rmw1 <> 0):
    rmw1 = rmw2.
  Proof.
    forward eapply (@RFC rmw1) as [rmw' RF1]; [by_destruct rmw1 |].
    forward eapply (@RFC rmw2) as [rmw'' RF2]; [by_destruct rmw2 |].
    apply exploit_rf in RF1; auto. apply exploit_rf in RF2; auto.
    destruct (classic (is_init rmw')); [by_destruct rmw'| ].
    destruct (classic (is_init rmw'')); [by_destruct rmw''| ].
    forward eapply (@lock_writes rmw') as RMW'; [by_subst| ].
    forward eapply (@lock_writes rmw'') as RMW''; [by_destruct rmw''| ].
    
    assert (rmw'' = rmw'); [| subst rmw''].
    { eapply unique_eq.
      { apply (@lock_write_unique (valr rmw1)); auto.
        destruct RMW'. des; [| lia].
        rewrite <- RF13, H2. apply BOUNDED_THREADS. exists rmw'. by_subst. }
      { by_destruct rmw''. }
      { by_subst. }
    }
    eapply rmws_atomicity_violation; by_subst.  
  Qed.
  
  Lemma lock_order_dom:
    lock_order ⊆ ⦗gt n_threads \₁ eq 0⦘ ⨾ lock_order ⨾ ⦗gt n_threads \₁ eq 0⦘. 
  Proof.
    red. ins.
    assert (forall rmw, (E G ∩₁ is_rmw) rmw -> (gt n_threads \₁ eq 0) (tid rmw))
           as TID_HELPER.
    { ins. split.
      { eapply BOUNDED_THREADS. by_subst. }
      intros T0. symmetry in T0. 
      eapply wf_tid_init in T0; eauto; [| by_subst].
      eapply init_w in T0; by_subst. }
    cdes H.     
    forward eapply (TID_HELPER w1); [by_subst| ].
    forward eapply (TID_HELPER w2); [by_subst| ].
    replace (tid w1) with x by by_subst. replace (tid w2) with y by by_subst.
    basic_solver 10.
  Qed.

  Lemma unique_equiv {A: Type} (S1 S2: A -> Prop) (EQUIV: S1 ≡₁ S2)
        (UNIQUE: exists! x, S1 x):
    exists! x, S2 x.
  Proof.
    destruct UNIQUE. exists x. destruct H. split; [by apply EQUIV| ].
    ins. apply H0. by apply EQUIV.
  Qed.
    
  Lemma lock_order_spo: strict_partial_order lock_order.
  Proof.    
    red. split.
    { red. intros thread ORD.      
      cdes ORD. cut (w1 = w2).
      { intros. subst. eapply co_irr; eauto. }
      eapply unique_eq; eauto.
      apply lock_order_dom, seq_eqv_lr in ORD. desc. 
      eapply unique_equiv; [symmetry; apply unique_rmw_helper| ].
      { by_subst. }
      apply lock_write_unique; by_subst. }
    { red. ins. cdes H. cdes H0. 
      cut (w2 = w0).
      { ins. subst. exists w1. exists w3. splits; auto.
        eapply co_trans; eauto. }
      eapply unique_eq. 
      { apply lock_order_dom, seq_eqv_lr in H. desc. 
        apply (@lock_write_unique (tid w2)); by_subst. }
      all: by_subst. }
  Qed. 
          
  Lemma lock_order_wf: well_founded lock_order.
  Proof.
    apply wf_finite with (l := seq 0 n_threads). 
    { destruct lock_order_spo. apply trans_irr_acyclic; auto. }
    red. ins.
    apply in_seq0_iff. eapply BOUNDED_THREADS.          
    red in REL. desc. exists w1. by_subst. 
  Qed.

  Lemma no_excessive_events thread
        (OVER: thread >= n_threads):
    E G ∩₁ Tid_ thread ≡₁ ∅.
  Proof.
    split; [| basic_solver].
    red. ins. 
    destruct BOUNDED_THREADS. specialize (H0 thread).
    specialize_full H0; by_subst.
  Qed.

  Lemma events_separation_inter (M: Event -> Prop)
        (THREAD_FIN: forall thread (BOUND: thread < n_threads),
            set_finite (E G ∩₁ Tid_ thread ∩₁ M)):
    set_finite (E G ∩₁ M).
  Proof.
    rewrite events_separation, <- set_bunion_inter_compat_r.
    arewrite ((fun _ : nat => True) ≡₁ (fun i => i < n_threads) ∪₁ (fun i => i >= n_threads)).
    { unfolder. split; lia. }
    rewrite set_bunion_union_l. apply set_finite_union. split.
    2: { rewrite set_subset_bunion_l with (sb := ∅); [exists []; auto| ].
         intros thread BOUND. 
         destruct (restrict G thread) as [Gt [TRE]]. simpl. 
         rewrite TRE, no_excessive_events; basic_solver. }
    apply set_finite_bunion; [by apply set_finite_lt| ].
    intros thread BOUND.
    destruct (restrict G thread) as [Gt [TRE]]. simpl.
    rewrite TRE. by apply THREAD_FIN.
  Qed.
  

  Ltac fin_subtrace_filtered :=
    match goal with
    | |- set_finite (trace_elems (trace_app ?t1 ?t2) ∩₁ ?M) =>
      rewrite trace_elems_app, set_inter_union_l; apply set_finite_unionI;
      [| destruct (excluded_middle_informative _)]; fin_subtrace_filtered
    | |- set_finite (trace_elems (trace_fin ?l) ∩₁ ?M) =>
      exists l; ins; by_subst
    | |- set_finite (trace_elems ?t ∩₁ ?M) =>
      try ((by exists []; ins; by_subst) ||
           (edestruct (@rel_fin t) as [?l L]; eauto; rewrite L; eexists; ins; by_subst) ||
           (edestruct (@acq_fin t) as [?l L]; eauto; rewrite L; eexists; ins; by_subst)
          )
    | _ => try (by exists []; ins; by_subst)
    end.

  Lemma fin_ninit_writes:
    set_finite (E G ∩₁ is_w \₁ is_init).
  Proof.
    rewrite set_minusE, set_interA. apply events_separation_inter.    
    ins.
    destruct (PeanoNat.Nat.eq_0_gt_0_cases thread).
    { subst thread. rewrite tid0_init. exists []. basic_solver. }
    cdes HMCS_CLIENT. specialize (HMCS_CLIENT0 thread).
    specialize_full HMCS_CLIENT0; try by_subst. desc.
    red in HMCS_CLIENT0. destruct (restrict G thread) as [Gt [TRE]]. desc.
    rewrite <- TRE, <- TR_E.
    eapply set_finite_mori.
    { red. rewrite <- set_interA. red. ins. eapply proj1. eauto. }
    red in HMCS. desc.
    rewrite APP, trace_elems_app, set_inter_union_l. apply set_finite_unionI.
    { unfold_acquire. desc. subst.
      fin_subtrace_filtered.
      destruct (NPeano.Nat.eq_dec pred 0); desc; subst; fin_subtrace_filtered.
      erewrite wait_trace_reads; eauto. fin_subtrace_filtered. }
    { destruct (excluded_middle_informative _); [| exists []; ins; by_subst].
      unfold_release.
      desc. destruct (NPeano.Nat.eq_dec succ 0); des; desc; subst; fin_subtrace_filtered.
      erewrite wait_trace_reads; eauto. fin_subtrace_filtered. }
  Qed.

  Lemma fin_l_writes l:
    set_finite (E G ∩₁ is_w ∩₁ Loc_ l). 
  Proof.
    rewrite set_union_minus_alt with (s' := is_init).
    apply set_finite_union. split.
    { pose proof (wf_initE WF). exists [InitEvent l]. ins. destruct x; by_subst. }
    eapply set_finite_mori; [| apply fin_ninit_writes]. red. basic_solver.
  Qed.
  
  Lemma wait_latest_read_helper l tr cond
        (WAIT: busywait l tr cond)
        (INF: ~ trace_finite tr)
        (IN_G: trace_elems tr ⊆₁ E G)
        (TWF: trace_wf tr):
    exists i, forall j w,
        i <= j -> rf G w (trace_nth j tr w) -> mo_max G w. 
  Proof.
    eapply inf_reads_latest_full with (locs := [l]); eauto.
    { intros FIN. apply INF.
      apply nodup_trace_elems; [by apply trace_wf_nodup| ].
      eapply set_finite_more; [| apply FIN].
      symmetry. rewrite set_interC. eapply set_inter_absorb_l.
      rewrite wait_trace_reads; eauto. basic_solver. }
    { exists n_threads. ins. apply BOUNDED_THREADS. by_subst. }
    { rewrite wait_trace_reads; basic_solver. }
    { by apply trace_wf_nodup. }
    { eapply set_finite_mori; [| apply (fin_l_writes l)]. red. basic_solver. }
  Qed.

  Lemma mo_max_co w w' (MAXw: mo_max G w) (W': (E G ∩₁ is_w ∩₁ Loc_ (loc w)) w'):
    (co G)^? w' w.
  Proof.
    destruct (classic (w' = w)) as [| NEQ]; [basic_solver| right]. 
    forward eapply wf_co_total with (a := w) (b := w') as CO; eauto.
    { red in MAXw. by_subst. }
    des; [| done].
    red in MAXw. desc. destruct (MAXw0 w'). by_subst. 
  Qed.

  Lemma disj_statuses_nexts thread1 thread2:
    nth thread1 statuses 0 = nth thread2 nexts 0 ->
    n_threads <= thread1 /\ n_threads <= thread2.
  Proof.
    intros EQ. 
    destruct (PeanoNat.Nat.lt_ge_cases thread1 n_threads),
    (PeanoNat.Nat.lt_ge_cases thread2 n_threads); auto. 
    { rewrite app_comm_cons in DISJ_LOC. apply nodup_app in DISJ_LOC. cdes DISJ_LOC.
      destruct (DISJ_LOC2 (nth thread1 statuses 0)).
      { right. apply nth_In. congruence. }
      { rewrite EQ. apply nth_In. congruence. }
    }
    { apply nexts0_iff_overflow in H0. rewrite H0 in EQ.
      apply statuses0_iff_overflow in EQ. lia. }
    { apply statuses0_iff_overflow in H. rewrite H in EQ.
      symmetry in EQ. apply nexts0_iff_overflow in EQ. lia. }
  Qed. 
  
  Lemma unique_nexts thread1 thread2        
        (EQ: nth thread1 nexts 0 = nth thread2 nexts 0):
    thread1 = thread2 \/ n_threads <= thread1 /\ n_threads <= thread2. 
  Proof.
    rewrite app_comm_cons in DISJ_LOC. apply nodup_app in DISJ_LOC.
    cdes DISJ_LOC.
    destruct (PeanoNat.Nat.lt_ge_cases thread1 n_threads),
    (PeanoNat.Nat.lt_ge_cases thread2 n_threads); auto.
    { left. eapply NoDup_nth; eauto; congruence. }
    { apply nexts0_iff_overflow in H0. rewrite H0 in EQ.
      apply nexts0_iff_overflow in EQ. lia. }
    { apply nexts0_iff_overflow in H. rewrite H in EQ.
      symmetry in EQ. apply nexts0_iff_overflow in EQ. lia. }
  Qed. 

  Lemma unique_statuses thread1 thread2
        (EQ: nth thread1 statuses 0 = nth thread2 statuses 0):
    thread1 = thread2 \/ n_threads <= thread1 /\ n_threads <= thread2. 
  Proof.
    rewrite app_comm_cons in DISJ_LOC. apply nodup_app in DISJ_LOC.
    cdes DISJ_LOC.
    destruct (PeanoNat.Nat.lt_ge_cases thread1 n_threads),
    (PeanoNat.Nat.lt_ge_cases thread2 n_threads); auto.
    { inversion DISJ_LOC0. subst. 
      left. eapply NoDup_nth; eauto; congruence. }
    { apply statuses0_iff_overflow in H0. rewrite H0 in EQ.
      apply statuses0_iff_overflow in EQ. lia. }
    { apply statuses0_iff_overflow in H. rewrite H in EQ.
      symmetry in EQ. apply statuses0_iff_overflow in EQ. lia. }
  Qed. 

  Lemma release_no_next_writes tr pred thread
        (RELEASE: hmcs_release lock statuses nexts thread tr)
        (NINIT: pred <> 0) (BOUND: pred < n_threads):
    trace_elems tr ∩₁ is_w ∩₁ Loc_ (nth pred nexts 0) ⊆₁ ∅.
  Proof.
    desc. red. intros w W.
    unfolder in W. desc. 
    unfold_release. desc. subst. trace_app_elems_exh.
    { edestruct (@release_fence_no_write tr_relf); by_subst. }
    { by_subst. }
    { edestruct (@acquire_fence_no_write tr_acqf); by_subst. }
    forward eapply (@disj_locs pred) as DISJ_LOCS.
    { auto. }
    destruct (NPeano.Nat.eq_dec succ 0).
    { des.
      { by_subst. }
      subst. trace_app_elems_exh; try by_subst.
      { eapply wait_trace_reads in W4; by_subst. }
      forward eapply disj_statuses_nexts with (thread2 := pred); by_subst. }
    desc. subst tr_rel_end.
    forward eapply disj_statuses_nexts with (thread2 := pred); by_subst. 
  Qed. 

  Lemma thread_next_write_unique thread tr w1 w2 pred
        (NINIT: 0 < pred) (BOUND: pred < n_threads)
        (HMCS: hmcs_acqiure_release lock statuses nexts thread tr)
        (W1: (trace_elems tr ∩₁ is_w ∩₁ Loc_ (nth pred nexts 0) \₁ Valw_ 0) w1)
        (W2: (trace_elems tr ∩₁ is_w ∩₁ Loc_ (nth pred nexts 0) \₁ Valw_ 0) w2):
    w1 = w2.
  Proof.
    eapply set_equiv_exp in W1; [eapply set_equiv_exp in W2| ]. 
    2, 3: rewrite <- set_inter_minus_r, set_interA; apply set_equiv_refl.
    destruct W1 as [TR1 W1], W2 as [TR2 W2].
    pose proof (@disj_statuses_nexts thread pred) as DISJ1.
    forward eapply (@disj_locs pred) as DISJ1'; auto. 
    red in HMCS. desc.
    rewrite APP in TR1. apply trace_in_app in TR1. des.
    2: { edestruct release_no_next_writes with (pred := pred); by_subst. }    
    unfold_acquire. desc. subst tr_acq tr_acqr tr_acq_end.
    trace_app_elems_exh; try by_subst. 
    { edestruct (@release_fence_no_write tr_relf); by_subst. }
    2: { edestruct (@acquire_fence_no_write tr_acqf); by_subst. }
    destruct (NPeano.Nat.eq_dec pred0 0); desc; subst tr_acq_end0. 
    { trace_app_elems_exh. by_subst. }
    trace_app_elems_exh.
    2: { eapply wait_trace_reads in TR4; by_subst. }

    subst. move TR2 at bottom. trace_app_elems_exh; try by_subst. 
    { edestruct (@release_fence_no_write tr_relf); by_subst. }
    { eapply wait_trace_reads in TR5; by_subst. } 
    { edestruct (@acquire_fence_no_write tr_acqf); by_subst. }
    { edestruct release_no_next_writes with (pred := pred); by_subst. }     
  Qed. 
  
  Lemma rmw_of_next_write_exists w pred
        (NINIT: pred <> 0) (BOUND: pred < n_threads)
        (W: (E G ∩₁ is_w ∩₁ Loc_ (nth pred nexts 0) \₁ Valw_ 0) w):
    exists rmw, (E G ∩₁ Loc_ lock ∩₁ is_rmw ∩₁ Valr_ pred) rmw /\ same_tid w rmw.  
  Proof.
    remember (tid w) as thread.
    cdes HMCS_CLIENT. specialize (HMCS_CLIENT0 thread). specialize_full HMCS_CLIENT0.
    { red. ins. subst thread. eapply wf_tid_init in H; [destruct w; by_subst| ..]; by_subst. }
    { apply BOUNDED_THREADS. exists w. by_subst. }
      desc. red in HMCS_CLIENT0. destruct (restrict G thread) as [Gt [TRE]]. desc.
    red in HMCS. desc. unfold_acquire. desc. 
    remember (ThreadEvent thread index0 (Armw lock pred0 thread)) as rmw.
    exists rmw.
    enough ((trace_elems tr ∩₁ Loc_ lock ∩₁ is_w ∩₁ Valr_ pred) rmw).
    { eapply set_equiv_exp in H.
      2: { rewrite TR_E, TRE. apply set_equiv_refl. }
      by_subst. }
    split.
    { unfolder. splits; try by_subst.
      subst. trace_elems_solver. } 
    
    assert (trace_elems tr w) as TRw.
    { apply TR_E, TRE. by_subst. }
    rewrite APP in TRw. apply trace_in_app in TRw. des.
    2: { forward eapply release_no_next_writes with (x := w); eauto; by_subst. }
    forward eapply (@disj_locs thread) as DISJ_LOCS.
    { apply BOUNDED_THREADS. exists w. by_subst. }
    pose proof (@disj_statuses_nexts thread pred) as DISJ_LOCS'.
    forward eapply (@disj_locs pred) as DISJ_LOCS''.
    { auto. }
    subst tr_acq tr_acqr tr_acq_end. move TRw at bottom.
    trace_app_elems_exh.
    { specialize_full DISJ_LOCS'; by_destruct w. }
    { by_destruct w. }
    { edestruct (@release_fence_no_write tr_relf); by_subst. }
    { by_destruct w. }
    2: { edestruct (@acquire_fence_no_write tr_acqf); by_subst. }
    destruct (NPeano.Nat.eq_dec pred0 0); desc; subst tr_acq_end0. 
    { trace_app_elems_exh. by_destruct w. }
    trace_app_elems_exh.
    2: { eapply wait_trace_reads in TRw2; by_subst. }
    rewrite TRw1 in *.
    forward eapply (@unique_nexts pred pred0).
    { by_destruct w. }
    by_subst. 
  Qed. 
      
  Lemma next_write_unique pred (NINIT: 0 < pred) (BOUND: pred < n_threads):
    let next_writes := E G ∩₁ is_w ∩₁ Loc_ (nth pred nexts 0) \₁ Valw_ 0 in
    forall w1 w2 (W1: next_writes w1) (W2: next_writes w2),
      w1 = w2.
  Proof.
    remember (E G ∩₁ is_w ∩₁ Loc_ (nth pred nexts 0) \₁ Valw_ 0) as NW.
    ins. 
    forward eapply (@rmw_of_next_write_exists w1 pred) as [rmw RMW]; try by_subst.
    forward eapply (@rmw_of_next_write_exists w2 pred) as [rmw' RMW']; try by_subst.
    assert (rmw' = rmw); [| subst rmw']. 
    { apply lock_write_unique_reads; by_subst. }

    remember (tid rmw) as thread.
    pose proof (@HMCS_CLIENT thread) as HMCS. specialize_full HMCS.
    { red. intros. subst thread. eapply wf_tid_init in H; by_destruct rmw. }
    { apply BOUNDED_THREADS. by_subst. }
    desc. red in HMCS. destruct (restrict G thread) as [Gt [TRE]]. desc.     

    eapply (@thread_next_write_unique thread tr w1 w2 pred); auto.
    1, 2: eapply set_equiv_exp; [rewrite TR_E, TRE; apply set_equiv_refl| by_subst].
  Qed.
  
  Lemma mo_max_unique_helper w1 w2 (MAX1: mo_max G w1) (MAX2: mo_max G w2)
        (LOC: same_loc w1 w2):
    w1 = w2.
  Proof.
    unfold mo_max in *.
    eapply max_elt_unique.
    { apply co_sto with (l := (loc w1)). eauto. }
    1, 2: by_subst.
    1, 2:  desc; eapply set_subset_max_elt; eauto; basic_solver.
  Qed. 
                                                    
  Lemma fin_traces_app {A: Type} (l1 l2: list A):
    trace_app (trace_fin l1) (trace_fin l2) = trace_fin (l1 ++ l2).
  Proof. done. Qed.

  Lemma trace_wf_app_both tr1 tr2 (FIN1: trace_finite tr1)
        (WF_APP: trace_wf (trace_app tr1 tr2)):
    trace_wf tr1 /\ trace_wf tr2.
  Proof.
    split; [eapply trace_wf_app; eauto| ].
    destruct tr1; [| by_subst].
    eapply trace_wf_fin_app; eauto.
  Qed. 
    
    Lemma trace_last_app {A: Type} (tr1 tr2: trace A)
          (FIN1: trace_finite tr1) (NEMPTY2: ~ tr2 = trace_fin []):
      forall d, trace_last (trace_app tr1 tr2) d = trace_last tr2 d.
    Proof.
      destruct tr1, tr2; try by_subst. simpl.
      ins. destruct l0; [by_subst| ]. 
      apply last_app.
    Qed. 
      
      
    Lemma wait_last_read l tr cond (WAIT: busywait l tr cond)
          (FIN: trace_finite tr):
      forall d, cond (valr (trace_last tr d)) /\ (trace_elems tr (trace_last tr d)).
    Proof.
      ins. red in WAIT. desc. subst tr. apply trace_app_finite in FIN. desc.
      destruct tr_fail, tr_ok; try by_subst. simpl.
      inversion BW_trace. subst l1. rewrite last_last.
      unfolder. splits; try by_subst. by apply in_app_r.
    Qed.
          

  Section InsideThread.
    Variable thread: Tid. 
    Variables tr_acqr tr_acqf tr_relf tr_relr: trace Event.
    
    Hypothesis (NINIT : 0 < thread).
    Hypothesis (LT : thread < n_threads).
    Hypothesis (ACQ0 : hmcs_acquire_real lock statuses nexts thread tr_acqr).
    Hypothesis (ACQ1 : acquire_fence tr_acqf).
    Hypothesis (REL0 : release_fence tr_relf).
    Hypothesis (REL1 : hmcs_release_real lock statuses nexts thread tr_relr).

    Let tr := trace_app (trace_app tr_acqr tr_acqf) (trace_app tr_relf tr_relr). 

    Hypothesis (TR_E : trace_elems tr ≡₁ E G ∩₁ Tid_ thread).
    Hypothesis (TR_WF : trace_wf tr).

    Hypothesis (IND: forall thread' (ORD: lock_order thread' thread),
                   set_finite (E G ∩₁ Tid_ thread')).

    Lemma hmcs_tr: hmcs_acqiure_release lock statuses nexts thread tr.
    Proof.
      subst tr. red. do 2 eexists. 
      splits; eauto; red; eauto.
    Qed. 
        
    Ltac exploit_trace_app_finite :=
      match goal with
      | H: trace_finite (trace_app ?t1 ?t2) |- _ =>
        apply trace_app_finite in H; desc
      end.

    Lemma tr_acqr_elemsET: trace_elems tr_acqr ⊆₁ E G ∩₁ Tid_ thread.
    Proof.
      rewrite <- TR_E. subst tr. do 2 rewrite trace_elems_app. basic_solver.
    Qed.

    Lemma lock_co_rf_imm:
      immediate (restr_rel (Loc_ lock \₁ is_init) (co G))
                ⊆ restr_rel is_rmw (rf G).
    Proof.
      red. intros rmw1 rmw2 CO. red in CO. desc.      
      red in CO. desc. apply exploit_co in CO; auto. 
      forward eapply (@lock_writes rmw1) as RMW1; [by_subst| ].
      forward eapply (@lock_writes rmw2) as RMW2; [by_subst| ]. 
      red. splits; try by_subst.
      forward eapply (@RFC rmw2) as [w' RF]; [by_destruct rmw2| ].
      destruct (classic (w' = rmw1)) as [| NEQ]; [congruence| ].
      forward eapply (@wf_co_total _ WF lock)with (a := rmw1) (b := w') as CO'; auto.
      { by_subst. }
      { apply exploit_rf in RF; auto. by_destruct w'. }
      des.
      { eapply co_ninit, seq_eqv_r in CO'; eauto.
        apply exploit_rf in RF; auto. 
        destruct (CO0 w').
        { red. splits; by_destruct w'. }
        { red. splits; try by_destruct w'. desc. apply rf_co_helper; auto. }
      }
      destruct (cycle_helper2 _ rmw2 rmw1 SCpL).
      2: { basic_solver. }
      right. red. split.
      { eexists. split; eauto. }
      red. ins. red in H. desc. eapply co_irr; vauto. 
    Qed. 

    Lemma lock_co_rf: restr_rel (Loc_ lock \₁ is_init) (co G) ⊆ (restr_rel is_rmw (rf G))^+.
    Proof.
      rewrite (@fsupp_imm_t _ (restr_rel (Loc_ lock \₁ is_init) (co G))).
      { apply clos_trans_mori, lock_co_rf_imm. }
      { forward eapply (fin_l_writes lock) as [dom DOM].
        exists dom. ins. apply DOM.
        red in REL. desc. apply exploit_co in REL; by_subst. }
      { apply irreflexive_restr, co_irr; auto. }
      { apply transitive_restr, co_trans; auto. }      
    Qed.

    Lemma rmw_rf_chain rmw rmw' r
          (LOCK: (E G ∩₁ Loc_ lock ∩₁ is_rmw) rmw)
          (RF: rf G rmw' rmw)
          (R: (E G ∩₁ Loc_ lock ∩₁ is_r) r)
          (SB: sb G rmw' r)
        (NEQ_VAL: valr r <> valw rmw'):
      ((restr_rel is_rmw (rf G))＊ ⨾ rf G) rmw r.
    Proof.
      forward eapply (@RFC r) as [w RFr]; [by_subst| ].
      destruct (classic (w = rmw)) as [| NEQ'].
      { subst w. exists rmw. split; auto. apply rt_refl. }
      forward eapply (@wf_co_total _ WF lock) with (a := rmw) (b := w) as CO'; eauto.
      { by_destruct rmw. }
      { apply exploit_rf in RFr; auto. by_destruct w. }
      des.
      2: { destruct (classic (w = rmw')) as [| NEQ]. 
           { apply exploit_rf in RFr; by_subst. } 
           forward eapply (@wf_co_total _ WF lock) with (a := w) (b := rmw') as CO; eauto.
           { apply exploit_rf in RFr; auto. by_destruct w. }
           { apply exploit_rf in RF; auto. by_destruct rmw'. }
           des.
           { destruct (cycle_helper2 _ rmw' r SCpL).
             { repeat left. apply exploit_rf in RF; auto. red. splits; by_subst. }
             { right. red. split.
               2: { red. ins. red in H. desc. subst rmw'. eapply sb_irr; eauto. }
               eexists. split; eauto. }
           }
           destruct (cycle_helper2 _ rmw w SCpL).
           2: { basic_solver. }
           right. red. split.
           { eexists. eauto. }
           red. intros. red in H. desc. subst rmw. eapply co_irr; eauto. }
      exists w. split; auto.

      apply inclusion_t_rt. apply lock_co_rf.
      apply exploit_co in CO'; auto. desc.
      red. splits; auto.
      { by_destruct rmw. }
      { apply co_ninit, seq_eqv_r in CO'; auto. by_destruct w. }       
    Qed. 
      
    Lemma prev_release_events_succ0 rmw pred
          w_next rmw'
          index index0 index1 index2 index4
          pred0
          tr_acq_end tr_relf0 tr_acq_end0 tr_acq_wait
          tr0 tr_acq tr_rel tr_acqr0 tr_acqf0 tr_acq_end1 tr_relf1 tr_acq_end2 tr_relf2 tr_relr0 tr_acqf1 tr_rel_end
          Gt'
          (APP : tr0 = trace_app tr_acq tr_rel)
          (LOCK: (trace_elems tr_acqr ∩₁ Loc_ lock ∩₁ is_rmw ∩₁
                              Valr_ pred ∩₁ Valw_ thread) rmw)
          (PRED: pred <> 0)
          (ACQ2 : tr_acqr =
                  trace_app
                    (trace_app
                       (trace_fin
                          [ThreadEvent thread index (Astore (nth thread statuses 0) 1);
                          ThreadEvent thread (index + 1) (Astore (nth thread nexts 0) 0)])
                       tr_relf0) tr_acq_end)
          (ACQ3 : release_fence tr_relf0)
          (Heqw_next : w_next =
              ThreadEvent thread index1 (Astore (nth pred nexts 0) thread))
          (ACQ5 : tr_acq_end0 = trace_app (trace_fin [w_next]) tr_acq_wait)
          (ACQ6 : busywait (nth thread statuses 0) tr_acq_wait (eq 0))
          (ACQ4 : tr_acq_end = trace_app (trace_fin [rmw]) tr_acq_end0)
          (ETrmw : (E G ∩₁ Tid_ thread) rmw)
          (RMW : rmw = ThreadEvent thread index0 (Armw lock pred thread))
          (RFlock : rf G rmw' rmw)
          (RMW' : ((fun a : Event => is_rmw a)
                     ∩₁ (fun e : Event => valw e = tid e \/ valw e = 0)) rmw')
          (ETw_next : (E G ∩₁ Tid_ thread) w_next)
          (PRED_TID : tid rmw' = pred)
          (ETrmw' : (E G ∩₁ Tid_ pred) rmw')
          (BOUNDS'0 : pred < n_threads)
          (TRE' : E Gt' ≡₁ E G ∩₁ Tid_ pred)
          (ACQ : tr_acq = trace_app tr_acqr0 tr_acqf0)
  (ACQ7 : tr_acqr0 =
         trace_app
           (trace_app
              (trace_fin
                 [ThreadEvent pred index2 (Astore (nth pred statuses 0) 1);
                 ThreadEvent pred (index2 + 1) (Astore (nth pred nexts 0) 0)])
              tr_relf1) tr_acq_end1)
  (ACQ9 : release_fence tr_relf1)
  (ACQ10 : tr_acq_end1 = trace_app (trace_fin [rmw']) tr_acq_end2)
  (ACQ11 : if NPeano.Nat.eq_dec pred0 0
          then
           exists index0 : nat,
             tr_acq_end2 =
             trace_fin
               [ThreadEvent pred index0 (Astore (nth pred statuses 0) 0)]
          else
           exists (index0 : nat) (tr_acq_wait : trace Event),
             tr_acq_end2 =
             trace_app
               (trace_fin
                  [ThreadEvent pred index0 (Astore (nth pred0 nexts 0) pred)])
               tr_acq_wait /\ busywait (nth pred statuses 0) tr_acq_wait (eq 0))
  (ACQ8 : acquire_fence tr_acqf0)
  (REL : tr_rel = trace_app tr_relf2 tr_relr0)
  (REL2 : release_fence tr_relf2)
  (REL3 : tr_relr0 =
         trace_app
           (trace_app
              (trace_fin
                 [ThreadEvent pred index4 (Aload (nth pred nexts 0) 0)])
              tr_acqf1) tr_rel_end)
  (REL4 : acquire_fence tr_acqf1)
  (REL5 : (exists index : nat,
            tr_rel_end = trace_fin [ThreadEvent pred index (Armw lock pred 0)]) \/
         (exists tr_wait tr_pass : trace Event,
            tr_rel_end = trace_app tr_wait tr_pass /\
            (exists (index : nat) (other : Val) (tr_succ_wait : trace Event),
               tr_wait =
               trace_app
                 (trace_fin [ThreadEvent pred index (Aload lock other)])
                 tr_succ_wait /\
               other <> pred /\
               busywait (nth pred nexts 0) tr_succ_wait (set_compl (eq 0))) /\
            (exists (thread : Tid) (index : nat),
               tr_pass =
               trace_fin
                 [ThreadEvent thread index
                    (Astore (nth (valr (trace_last tr_wait d_)) statuses 0) 0)])))
  (TR_E0 : trace_elems tr0 ≡₁ E Gt')
  (TR_WF0 : trace_wf tr0)
  (FIN' : trace_finite tr0):
      
  exists r'_lock w'_st : Event,
    (is_r ∩₁ Loc_ lock) r'_lock /\
    (is_w ∩₁ Loc_ (nth thread statuses 0) ∩₁ Valw_ 0)
      w'_st /\
    sb G r'_lock w'_st /\
    ((restr_rel is_rmw (rf G))＊ ⨾ rf G) rmw r'_lock.
    Proof.
      des.
      { remember (ThreadEvent pred index3 (Armw lock pred 0)) as rmw''.
        enough (rf G rmw' rmw'') as RF'.
        { forward eapply (rmws_atomicity_violation rmw' rmw rmw''); try by_subst.            
          ins.
          (* by_subst.  - stopped working as is*)
          enough (valw rmw = 0); by_subst. }
        assert ((E G ∩₁ Tid_ pred) rmw'') as ETrmw''.
        { apply TRE', TR_E0.
          subst tr0. apply trace_elems_app. rewrite emiT.
          2: { apply trace_app_finite in FIN'. by desc. }
          right. subst. trace_elems_solver. }
        forward eapply (@RFC rmw'') as [rmw'_ RF']; [by_subst| ].
        replace rmw' with rmw'_; auto.
        eapply unique_eq; [by apply (@lock_write_unique pred) | ..].
        { apply exploit_rf in RF'; auto. unfolder. splits; try by_subst. 
          forward eapply (@lock_writes rmw'_); [by_destruct rmw'_| ].
          ins. by_subst. }
        { apply exploit_rf in RFlock; auto. by_destruct rmw'. }          
      }
      remember (ThreadEvent pred index5 (Aload lock other)) as r'_lock.
      assert (trace_elems tr0 r'_lock) as TR0r'_lock.
      { (* It works as is, but too slowly. You may want to skip it during WiP *)
        subst. repeat exploit_trace_app_finite. trace_elems_solver. } 
      remember (ThreadEvent thread0 index3 (Astore (nth (valr (trace_last tr_wait d_)) statuses 0) 0)) as w'_st.
      assert (trace_elems tr0 w'_st) as TR0w'_st.
      { (* It works as is, but too slowly. You may want to skip it during WiP *)
        subst. repeat exploit_trace_app_finite. trace_elems_solver. }
      exists r'_lock, w'_st.
      assert ((E G ∩₁ Tid_ pred) r'_lock) as EPr'_lock.
      { apply TRE', TR_E0. subst.
        (* It works as is, but too slowly. You may want to skip it during WiP *)
        trace_elems_solver. }
      assert ((E G ∩₁ Tid_ pred) w'_st) as EPw'_st.
      { apply TRE', TR_E0. subst.
        (* It works as is, but too slowly. You may want to skip it during WiP *)
        trace_elems_solver. }
      
      splits; [by_subst| ..]. 
      { enough (valr (trace_last tr_wait d_) = thread) as LOC_THREAD.
        { by_subst. }
        remember (trace_last tr_wait d_) as r_last.
        forward eapply wait_last_read with (d := d_) as [N0 TRwait]; eauto. 
        { subst. repeat exploit_trace_app_finite. auto. }
        subst tr_wait. rewrite trace_last_app in Heqr_last; [| by_subst |].
        2: { eapply wait_nonempty; eauto. } 
        forward eapply wait_trace_reads with (x := r_last) as R_LAST; try by vauto.
        rewrite PRED_TID in *. 
        forward eapply (@RFC r_last) as [w RFlast].
        { enough (trace_elems tr0 r_last) as TR0. 
          { apply TR_E0, TRE' in TR0. by_subst. }
          forward eapply wait_last_read with (d := d_) as [_ TRswait]; eauto.
          { subst. repeat exploit_trace_app_finite. auto. }
          (* It works as is, but too slowly. You may want to skip it during WiP *)
          subst. repeat exploit_trace_app_finite. trace_elems_solver. }
        replace thread with (valw w).
        { apply exploit_rf in RFlast; by_subst. }
        rewrite <- Heqr_last in *.
        
        replace w with w_next; [by_subst| ].
        eapply (@next_write_unique pred); eauto.
        { lia. }
        { unfolder. splits; by_subst. }
        { apply exploit_rf in RFlast; auto.          
          unfolder. splits; by_subst. }
      }
      { apply seq_eqv_lr. splits.
        1, 3: by_subst. 
        apply (trace_wf_app_sb tr_wait tr_pass).
        { subst. repeat exploit_trace_app_finite.
          repeat (match goal with
                  | H: trace_wf (trace_app ?t1 ?t2) |- _ =>
                    apply trace_wf_app_both in H; [| fin_trace_solver]; desc; try by auto
                  end). }
        { subst. repeat (exploit_trace_app_finite; auto). }
        1, 2: subst; trace_elems_solver. 
        by_subst. }
      
      eapply rmw_rf_chain; eauto.
      1, 2:  by_subst.
      { apply seq_eqv_lr. splits; try by_subst.
        eapply trace_wf_app_sb.
        { subst tr0. eauto. }
        { subst tr0. apply trace_app_finite in FIN'. by desc. }
        { subst. trace_elems_solver. }
        { subst. trace_elems_solver. }
        by_subst. }
      apply exploit_rf in RFlock; auto. by_subst.
    Qed. 

    Lemma prev_release_events rmw pred
          (LOCK: (trace_elems tr_acqr ∩₁ Loc_ lock ∩₁ is_rmw ∩₁ Valr_ pred ∩₁ Valw_ thread) rmw)
          (PRED: pred <> 0):
      exists w'_st r,
        (is_w ∩₁ Loc_ (nth thread statuses 0) ∩₁ Valw_ 0) w'_st /\
        sb G r w'_st /\
        ((is_r ∩₁ Loc_ lock) r /\
         (((restr_rel is_rmw (rf G))^* ⨾ rf G) rmw r)
         \/
         (is_r ∩₁ Loc_ (nth pred nexts 0) \₁ Valr_ 0) r
        ).
    Proof.
      unfold_acquire. cdes ACQ0.
      forward eapply (@tr_acqr_elemsET rmw) as ETrmw; [by_subst| ]. 
      
      assert (rmw = ThreadEvent thread index0 (Armw lock pred0 thread)) as RMW.
      { eapply unique_eq.
        { eapply unique_equiv. 
          2: { apply (@lock_write_unique thread); lia. }
          symmetry. apply unique_rmw_helper. lia. }
        { by_subst. } 
        eapply set_equiv_exp.
        { do 2 rewrite set_interA. apply set_equiv_refl2. }
        split; [| by_subst]. apply tr_acqr_elemsET. subst. trace_elems_solver. }
      assert (pred0 = pred); [by_subst | subst pred0]. rewrite <- RMW in *. 
            
      assert (exists rmw', rf G rmw' rmw) as [rmw' RFlock].
      { apply RFC. by_destruct rmw. }
      forward eapply (@lock_writes rmw') as RMW'.
      { apply exploit_rf in RFlock; auto. unfolder. splits; try by_subst.
        by_destruct rmw'. }
      destruct (NPeano.Nat.eq_dec pred O); [lia| ]. desc.
      remember (ThreadEvent thread index1 (Astore (nth pred nexts 0) thread)) as w_next.
      forward eapply (@tr_acqr_elemsET w_next) as ETw_next; [subst; trace_elems_solver| ].

      assert (tid rmw' = pred) as PRED_TID.
      { forward eapply (@unique_rmw_helper pred) as [_ RMW'_].
        { lia. }
        specialize (RMW'_ rmw'). specialize_full RMW'_; [| by_subst].
        apply exploit_rf in RFlock; auto. by_destruct rmw'. }

      assert ((E G ∩₁ Tid_ pred) rmw') as ETrmw'.
      { apply exploit_rf in RFlock; by_subst. }
      
      assert (pred <> 0 /\ pred < n_threads) as BOUNDS'. 
      { split.
        2: { apply BOUNDED_THREADS. by_subst. }
        subst pred. red. intros. eapply wf_tid_init in H; eauto; [| by_subst]. 
        destruct rmw'; by_subst. }
      cdes HMCS_CLIENT. specialize (HMCS_CLIENT0 pred).
      specialize_full HMCS_CLIENT0; auto. desc.
      red in HMCS_CLIENT0. destruct (restrict G pred) as [Gt' [TRE']]. desc.
      red in HMCS. desc. unfold_acquire. desc.
      assert (rmw' = ThreadEvent pred index3 (Armw lock pred0 pred)).
      { eapply unique_eq.
        { eapply unique_equiv. 
          2: by apply (@lock_write_unique pred).
          symmetry. by apply unique_rmw_helper. }
        { apply exploit_rf in RFlock; auto. unfolder. splits; by_subst. }
        eapply set_equiv_exp.
        { rewrite <- TRE', <- TR_E0, !set_interA; apply set_equiv_refl2. }
        split; [| by_subst]. subst. trace_elems_solver. }
      rewrite <- H in *. clear H.

      assert (trace_finite tr0) as FIN'.
      { apply nodup_trace_elems; [by apply trace_wf_nodup| ].
        rewrite TR_E0, TRE'. apply IND. exists rmw'. exists rmw.
        splits; [| by_subst| ]. 
        { apply exploit_rf in RFlock; auto. unfolder. splits; try by_subst. }
        apply rf_co_helper; auto. by_destruct rmw. }

      unfold_release. desc.
      destruct (NPeano.Nat.eq_dec succ 0).
      { subst succ. 
        forward eapply prev_release_events_succ0 with (tr0 := tr0); eauto.
        { by_subst. }
        ins. desc. exists w'_st, r'_lock. auto. }

      desc. 
      remember (ThreadEvent pred index4 (Aload (nth pred nexts 0) succ)) as r'.
      assert ((E G ∩₁ Tid_ pred) r') as EPr'.
      { apply TRE', TR_E0. subst tr0. apply trace_in_app. right. split.
        { exploit_trace_app_finite. fin_trace_solver. }
        subst. trace_elems_solver. }
      remember (ThreadEvent thread0 index5 (Astore (nth succ statuses 0) 0)) as w'_st.
      assert ((E G ∩₁ Tid_ pred) w'_st) as EPw'_st.
      { apply TRE', TR_E0. subst tr0. apply trace_in_app. right. split.
        { exploit_trace_app_finite. fin_trace_solver. }
        subst. trace_elems_solver. }
      assert (succ = thread); [| subst succ].
      { replace succ with (valr r') by by_subst.
        forward eapply (@RFC r') as [w' RF']; [by_subst| ].
        assert (w' = w_next); [| subst w'].
        { apply (@next_write_unique pred); try lia.
          { apply exploit_rf in RF'; auto. by_subst. }
          { unfolder. splits; by_subst. }
        }
        apply exploit_rf in RF'; auto. by_subst. } 
        
      exists w'_st, r'. splits.
      { unfolder. splits; by_subst. }
      { apply seq_eqv_lr. splits.
        1, 3: by_subst.
        subst tr0.
        apply trace_wf_app_sb with (tr1 := trace_fin [r'])
                                   (tr2 := trace_app tr_acqf1 tr_rel_end).
        { rewrite trace_app_assoc.
          subst. 
          exploit_trace_app_finite.
          repeat (match goal with
                  | H: trace_wf (trace_app ?t1 ?t2) |- _ =>
                    apply trace_wf_app_both in H; [| fin_trace_solver]; desc; auto
                  end). }
        { by_subst. }
        { by_subst. }
        { subst. trace_elems_solver. }
        { by_subst. }
      }
      right. by_subst. 
    Qed.

    Lemma status_write_thread:
      (E G ∩₁ is_w ∩₁ Loc_ (nth thread statuses 0) \₁ Valw_ 0) ⊆₁ Tid_ thread.
    Proof.
      red. intros w W.
      assert (0 < tid w < n_threads) as TID.
      { split.
        { cut (tid w <> 0); [lia| ].
          red. intros EQ0. eapply wf_tid_init in EQ0; by_destruct w. }
        { apply BOUNDED_THREADS. by_subst. }
      }          
      forward eapply (@HMCS_CLIENT (tid w)); try lia. ins. desc. red in H.
      destruct (restrict G (tid w)) as [Gt' [TRE']]. desc.
      assert (trace_elems tr0 w) as TRw.
      { apply TR_E0, TRE'. by_subst. }
      red in HMCS. desc. red in ACQ, REL. desc.
      subst tr0 tr_acq tr_rel. trace_app_elems_exh.
      2: { edestruct (@acquire_fence_no_write tr_acqf0); by_subst. }
      2: { edestruct (@release_fence_no_write tr_relf0); by_subst. }
      2: { unfold_release. cdes REL1. subst.
           move TRw1 at bottom. trace_app_elems_exh.
           { forward eapply (@disj_statuses_nexts (tid w) (tid w)); [by_destruct w| ].
             lia. }
           { edestruct (@acquire_fence_no_write tr_acqf2); by_subst. }
           destruct (NPeano.Nat.eq_dec succ0 0); desc; des; subst. 
           { trace_app_elems_exh. by_destruct w. }
           { trace_app_elems_exh; try by_destruct w.
             eapply wait_trace_reads in TRw3; eauto. by_subst. }
           { trace_app_elems_exh. by_subst. }
      }
      unfold_acquire. desc. subst.
      move TRw at bottom. trace_app_elems_exh.
      { forward eapply (@unique_statuses (tid w) thread); [by_destruct w| ]. 
        ins. des; by_subst. }
      { forward eapply (@disj_locs (tid w)); [lia| ].
        ins. desc. destruct H. by_destruct w. }
      { edestruct (@release_fence_no_write tr_relf1); by_subst. }
      { forward eapply (@disj_locs thread); [lia| ].
        ins. desc. destruct H. by_destruct w. } 
      { destruct (NPeano.Nat.eq_dec pred 0); desc; subst.
        { trace_app_elems_exh. by_destruct w. }
        { trace_app_elems_exh.
          { forward eapply (@disj_statuses_nexts thread pred); by_destruct w. }
          { eapply wait_trace_reads in TRw2; by_subst. }
        }
      }
    Qed.
      

    Lemma status_writes:
      exists! w, (E G ∩₁ is_w ∩₁ Loc_ (nth thread statuses 0) \₁ Valw_ 0) w.
    Proof.
      cdes ACQ0. 
      remember (ThreadEvent thread index (Astore (nth thread statuses 0) 1)) as w.
      exists w. split.
      { unfolder. splits; try by_subst. apply tr_acqr_elemsET.
        subst. trace_elems_solver. }
      intros w' W'. 
      assert (tid w' = thread) as TID. 
      { rewrite (@status_write_thread w'); by_subst. }
      assert (trace_elems tr w') as TRw'.
      { apply TR_E. by_subst. }
      subst tr. trace_app_elems_exh.
      2: { edestruct (@acquire_fence_no_write tr_acqf); by_subst. }
      2: { edestruct (@release_fence_no_write tr_relf); by_subst. }
      2: { unfold_release. cdes REL1. subst.
           move TRw'1 at bottom. trace_app_elems_exh.
           { forward eapply (@disj_statuses_nexts (tid w') (tid w')); [by_destruct w'| ].
             lia. }
           { edestruct (@acquire_fence_no_write tr_acqf0); by_subst. }
           destruct (NPeano.Nat.eq_dec succ 0); desc; des; subst. 
           { trace_app_elems_exh. by_destruct w'. }
           { trace_app_elems_exh; try by_destruct w'.
             eapply wait_trace_reads in TRw'3; eauto. by_subst. }
           { trace_app_elems_exh. by_subst. }
      }
      unfold_acquire. desc. subst.
      move TRw' at bottom. trace_app_elems_exh.
      { forward eapply (@disj_statuses_nexts (tid w') (tid w')); [by_destruct w'| ].
        lia. }
      { edestruct (@release_fence_no_write tr_relf0); by_subst. }
      { forward eapply (@disj_locs (tid w')); [lia| ].
        ins. desc. destruct H. by_destruct w'. }
      { destruct (NPeano.Nat.eq_dec pred 0); desc; subst.
        { trace_app_elems_exh. by_destruct w'. }
        { trace_app_elems_exh.
          { forward eapply (@disj_statuses_nexts (tid w') pred); by_destruct w'. }
          { eapply wait_trace_reads in TRw'2; by_subst. }
        }
      }
    Qed.

    Lemma rmw_valw_bounded w (W: (E G ∩₁ is_w ∩₁ Loc_ lock) w):
      valw w < n_threads.
    Proof.
      destruct (classic (is_init w)); [by_destruct w| ].
      (* apply exploit_rf in RF; auto.  *)
      forward eapply (@lock_writes w) as W_; [by_destruct w| ]. 
      red in W_. desc. des; [| by_subst].
      rewrite W_0. apply BOUNDED_THREADS. exists w. by_subst. 
    Qed.

    Lemma rmw_valr_bounded rmw (RMW: (E G ∩₁ is_w ∩₁ Loc_ lock \₁ is_init) rmw):
      valr rmw < n_threads. 
    Proof.
      forward eapply (@lock_writes rmw) as RMW_; [by_subst| ]. 
      forward eapply (@RFC rmw) as [w RF]; [by_destruct rmw| ].
      erewrite <- wf_rfv; eauto.
      apply exploit_rf in RF; auto. 
      apply rmw_valw_bounded. unfolder. splits; by_subst.
    Qed. 
    
    Lemma acquire_real_fin:
      trace_finite tr_acqr.
    Proof.
      cdes ACQ0.
      enough (trace_finite tr_acq_end); [subst; fin_trace_solver| ].
      cdes ACQ4. destruct (NPeano.Nat.eq_dec pred 0); [by_subst| ]. desc.
      enough (trace_finite tr_acq_wait); [subst; fin_trace_solver| ].
      contra INF.

      remember (nth thread statuses 0) as st.
      remember (ThreadEvent thread index0 (Armw lock pred thread)) as rmw.
      remember (ThreadEvent thread index (Astore st 1)) as w1.

      assert (trace_elems tr_acq_wait ⊆₁ E G) as ACQ_E.
      { transitivity (trace_elems tr_acqr).
        { subst. repeat (rewrite trace_elems_app, emiT; [| fin_trace_solver]).
          basic_solver. }
        etransitivity; [apply tr_acqr_elemsET| ]. basic_solver. }
      
      forward eapply (fin_w_max G st) as [wmax [MAX LOC]];
        [done| by apply fin_l_writes| ].

      (* forward eapply (@status_writes wmax) as MAX'; [red in MAX; by_subst| ]. *)
      pose proof (classic (Valw_ 0 wmax)) as MAX'. 

      (* red in MAX'. *)
      des.
      
      { apply INF. eapply wait_fin_iff_cond; eauto.
        forward eapply (wait_latest_read_helper ACQ7) as [i LATEST]; try by_subst.
        { subst tr. edestruct rel_fin; eauto. edestruct acq_fin; eauto.
          subst. move TR_WF at bottom. 
          rewrite <- !trace_app_assoc in TR_WF.
          repeat (apply trace_wf_app_both in TR_WF as [_ TR_WF]; [| fin_trace_solver]).
          eapply trace_wf_app; eauto. }
        remember (trace_nth i tr_acq_wait d_) as r. exists r.
        assert (NOmega.lt_nat_l i (trace_length tr_acq_wait)) as DOMi.
        { destruct tr_acq_wait; [edestruct INF; vauto | by_subst]. }
        split.
        { subst r. by apply trace_nth_in. }
        forward eapply (@RFC r) as [w RFwr].
        { apply hahn_subset_exp with (s := trace_elems tr_acq_wait).
          2: { subst r. by apply trace_nth_in. }
          apply set_subset_inter_r. split; auto. 
          erewrite wait_trace_reads; eauto. basic_solver. }
        specialize (LATEST i w). specialize_full LATEST; [lia| ..].
        { erewrite trace_nth_indep; [by_subst| ].
          destruct tr_acq_wait; by_subst. }
        rewrite <- MAX'.
        rewrite (@mo_max_unique_helper wmax w); try by_subst.  
        { apply exploit_rf in RFwr; by_subst. }
        { apply wait_trace_reads in ACQ7.
          specialize (ACQ7 r). specialize_full ACQ7.
          { subst r. by apply trace_nth_in. }
          apply exploit_rf in RFwr; auto. by_subst. }
      }
      
      assert (wmax = w1); [| subst wmax].
      { eapply unique_eq; [apply status_writes| ..].
        { red in MAX. by_subst. }
        { unfolder. splits; try by_subst.
          apply tr_acqr_elemsET. subst. trace_elems_solver. }
      }

      forward eapply (@prev_release_events rmw pred) as [w'_st [r' PROPS']]; eauto.
      { unfolder. splits; try by_subst. subst. trace_elems_solver. }
      
      desc.  
      forward eapply (@mo_max_co w1 w'_st) as CO; try by_subst.
      { desc. apply seq_eqv_lr in PROPS'0. by_subst. }
      destruct CO as [| CO]; [by_subst| ].
      assert (E G w1) as Ew1.
      { red in MAX. by_subst. }

      assert (E G rmw) as Ermw.
      { apply hahn_subset_exp with (s := trace_elems tr); [rewrite TR_E; basic_solver| ].
        subst tr. subst. trace_elems_solver. }
      
      des.
      { assert (sb G w1 rmw) as SBw1rmw. 
        { apply seq_eqv_lr. splits; auto.
          move TR_WF at bottom. subst tr. do 2 apply trace_wf_app in TR_WF.
          rewrite ACQ2 in TR_WF.
          edestruct rel_fin; eauto. rewrite H, fin_traces_app in TR_WF.
          eapply trace_wf_app_sb; eauto; try by_subst. 
          subst. trace_elems_solver. }
        apply no_cycle. exists r'. repeat (eexists; split; eauto). }
      { remember (ThreadEvent thread index1 (Astore (nth pred nexts 0) thread)) as w_next. 
        assert (rf G w_next r') as RF'.
        { forward eapply (@RFC r') as [w' RF']; [apply seq_eqv_lr in PROPS'0; by_subst| ].
          replace w_next with w'; [done| ].
          apply (@next_write_unique pred); try lia.
          { replace pred with (valr rmw) by by_subst.
            apply rmw_valr_bounded. by_subst. }
          { apply exploit_rf in RF'; auto. unfolder. splits; by_subst. }
          { eapply set_equiv_exp; [rewrite !set_interA, <- set_inter_minus_r; apply set_equiv_refl| ].
            split; [| unfolder; splits; by_subst].
            forward eapply (@tr_acqr_elemsET w_next); [| ins; by_subst].
            subst. trace_elems_solver. }
        }
        assert (sb G w1 w_next) as SB.
        { apply seq_eqv_lr. splits; try by_subst.
          2: { apply exploit_rf in RF'; by_subst. }
          do 2 apply trace_wf_app in TR_WF. subst tr_acqr. 
          eapply trace_wf_app_sb; eauto; subst;
            [fin_trace_solver | trace_elems_solver | trace_elems_solver | by_subst]. }
        apply no_cycle. exists r'. repeat (eexists; split; eauto).
        apply rt_refl. 
      }
    Qed.

    Lemma acquire_real_events:
      exists w_next rmw,
        (trace_elems tr_acqr ∩₁ is_w ∩₁ Loc_ (nth thread nexts 0) ∩₁ Valw_ 0) w_next /\
        (trace_elems tr_acqr ∩₁ is_w ∩₁ Loc_ lock ∩₁ Valw_ thread) rmw /\
        sb G w_next rmw.
    Proof.
      unfold_acquire. cdes ACQ0.
      remember (ThreadEvent thread (index + 1) (Astore (nth thread nexts 0) 0)) as w_next.
      remember (ThreadEvent thread index0 (Armw lock pred thread)) as rmw.
      exists w_next, rmw.
      splits.
      1, 2:  eapply set_equiv_exp;
        [rewrite !set_interA; apply set_equiv_refl|
         split; [subst; trace_elems_solver| by_subst]].
      apply seq_eqv_lr. splits.
      1, 3: apply tr_acqr_elemsET; subst; trace_elems_solver.
      subst tr. do 2 apply trace_wf_app in TR_WF. subst tr_acqr. 
      eapply trace_wf_app_sb; eauto.
      { fin_trace_solver. }
      { trace_elems_solver. }
      { subst. trace_elems_solver. }
      { by_subst. }
    Qed. 

    Lemma tr_relr_elemsET: trace_elems tr_relr ⊆₁ E G ∩₁ Tid_ thread.
    Proof.
      rewrite <- TR_E. unfold tr. rewrite trace_elems_app, emiT.
      2: { apply trace_app_finite. split; [apply acquire_real_fin| fin_trace_solver]. }
      apply set_subset_union_r. right.
      rewrite trace_elems_app, emiT; [basic_solver | fin_trace_solver]. 
    Qed.

    (* Lemma co_wf: well_founded (co G). *)
    (* Proof. *)

    Lemma next_rmw_exists rmw r_lock
          (RMW : (trace_elems tr_acqr ∩₁ is_w ∩₁ Loc_ lock
                              ∩₁ Valw_ thread) rmw)
          (Ermw : (E G ∩₁ Tid_ thread) rmw)
          (RLOCK: (trace_elems tr_relr ∩₁ is_r ∩₁ Loc_ lock \₁ Valr_ thread) r_lock):
      exists rmw', rf G rmw rmw' /\ co G rmw rmw'
              (* /\ *)
              (* (Valw_ 0 rmw' /\ trace_elems *)
                                .
    Proof. 
      forward eapply (@tr_relr_elemsET r_lock) as ETr_lock; [by_subst| ]. 
      assert (sb G rmw r_lock) as SB.
      { apply seq_eqv_lr. splits; try by_subst.
        eapply trace_wf_app_sb; eauto.
        { apply trace_app_finite. split; [apply acquire_real_fin | fin_trace_solver]. }
        { trace_elems_solver. }
        { subst. trace_elems_solver. }
        forward eapply (@tr_relr_elemsET r_lock); [by_subst| ]. 
        by_destruct r_lock. }
      
      forward eapply (@RFC r_lock) as [w_lock RFlock]; [by_subst| ].
      destruct (classic (w_lock = rmw)) as [| NEQ].
      { subst w_lock.
        red in RLOCK. desc. destruct RLOCK0. 
        erewrite <- wf_rfv; by_subst. }
      forward eapply (@wf_co_total _ WF lock) with (a := w_lock) (b := rmw) as CO; eauto.
      { apply exploit_rf in RFlock; auto. unfolder. splits; by_subst. }
      { by_subst. }
      des.
      { destruct (cycle_helper2 _ rmw r_lock SCpL).
        { repeat left. red. split; by_subst. }
        right. split.
        2: { unfolder. red. ins. desc. subst r_lock.
             eapply sb_irr; eauto. }
        eexists. split; eauto. }
      
      apply fsupp_imm_t in CO;
        [| cdes FAIR | eapply co_irr | eapply co_trans]; eauto.      
      apply ct_begin in CO as [rmw' [IMM_CO CO']].
      
      exists rmw'. split; [| red in IMM_CO; by desc].
      apply lock_co_rf_imm.
      red in IMM_CO. desc. red. split.
      { red. splits; auto.
        { by_destruct rmw. }
        { apply exploit_co in IMM_CO; auto. red. split; by_subst. }
      }
      { ins. red in R1, R2. apply (IMM_CO0 c); by_subst. }
    Qed.

    Lemma next_write_of_rmw rmw
        (RMW : (E G ∩₁ is_w ∩₁ Loc_ lock ∩₁ Valr_ thread \₁ Valw_ 0) rmw):
      exists w_next,
        (is_w ∩₁ Loc_ (nth thread nexts 0) \₁ Valw_ 0) w_next /\
        sb G rmw w_next.
    Proof.
      forward eapply (@lock_writes rmw) as RMW_; [by_destruct rmw| ].
      destruct RMW_ as [RMW_ VAL]. des; [| by_subst]. 
      
      forward eapply (@HMCS_CLIENT (tid rmw)).
      { red. intros. eapply wf_tid_init in H; eauto; by_destruct rmw. }
      { apply BOUNDED_THREADS. by_subst. }
      ins. desc. red in H. destruct (restrict G (tid rmw)) as [Gt' [TRE']]. desc.
      
      red in HMCS. unfold_acquire. desc.
      rewrite <- VAL in *.
      remember (ThreadEvent (tid rmw) index0 (Armw lock pred (tid rmw))) as rmw'.
      
      assert ((E G ∩₁ Tid_ (tid rmw)) rmw') as ETrmw'.
      { rewrite <- VAL. apply TRE', TR_E0. subst.
        rewrite VAL. trace_elems_solver. }
      assert (rmw' = rmw); [| subst rmw'].
      { eapply unique_eq.
        { apply (@lock_write_unique (valw rmw)); [by_subst| ].
          apply rmw_valw_bounded. by_subst. }
        1, 2:  by_subst. }
      rewrite VAL, H in *.
      assert (pred = thread); [| subst pred]. 
      { replace thread with (valr rmw) by by_subst. by rewrite <- H. }

      destruct (NPeano.Nat.eq_dec thread 0); [lia| ]. desc.
      remember (ThreadEvent (tid rmw) index1 (Astore (nth thread nexts 0) (tid rmw))) as w_next.
      exists w_next. split.
      { split; [by_subst| ]. replace (valw w_next) with (tid rmw); by_subst. }
      apply seq_eqv_lr. splits; [by_subst| ..].
      2: { eapply hahn_subset_exp with (s := trace_elems tr0). 
           { rewrite TR_E0, TRE'. basic_solver. }
           subst. trace_elems_solver. }
      subst. do 2 apply trace_wf_app in TR_WF0. 
      apply trace_wf_app_both in TR_WF0 as [_ TR_WF0]; [| fin_trace_solver].
      eapply trace_wf_app_sb; eauto;
        [fin_trace_solver| by_subst| trace_elems_solver].
    Qed. 

    Lemma lock_not_status i:
      lock <> nth i statuses 0.
    Proof.
      red. intros EQ. 
      destruct (PeanoNat.Nat.lt_ge_cases i n_threads).
      { rewrite app_comm_cons in DISJ_LOC. apply nodup_app in DISJ_LOC.
        cdes DISJ_LOC.
        cut (0 = S i); [lia| ].
        eapply NoDup_nth with (d := 0); [apply DISJ_LOC0| ..]; auto; simpl;
          [lia | ].
        apply Lt.lt_n_S. rewrite <- STATUSES_LEN in H. auto. }
      { rewrite nth_overflow in EQ; [| by rewrite STATUSES_LEN].
        by_subst. }
    Qed. 

    Lemma lock_not_next i:
      lock <> nth i nexts 0.
    Proof.
      red. intros EQ. 
      destruct (PeanoNat.Nat.lt_ge_cases i n_threads).
      { cdes DISJ_LOC.
        cut (0 = n_threads + S i); [lia| ].
        eapply NoDup_nth with (d := 0); [apply DISJ_LOC| ..]; auto;
          [simpl; lia | .. ].
        { cdes NEXTS_LEN. cdes STATUSES_LEN. simpl. rewrite app_length. lia. }
        replace (n_threads + S i) with (S (length statuses + i)).
        2: { rewrite STATUSES_LEN. lia. }
        simpl. by rewrite app_nth2_plus. } 
      { rewrite nth_overflow in EQ; [| by rewrite NEXTS_LEN].
        by_subst. }
    Qed.       

    Lemma release_no_wait rmw
          (RMW: (trace_elems tr ∩₁ is_w ∩₁ Loc_ lock ∩₁ Valw_ 0 \₁ is_init) rmw):
      trace_finite tr.
    Proof.      
      eapply set_equiv_exp in RMW.
      2: { rewrite <- set_inter_minus_r. repeat rewrite set_interA. apply set_equiv_refl. }
      destruct RMW as [TRw RMW]. unfold tr.
      apply trace_app_finite. split.
      { apply trace_app_finite. split; [apply acquire_real_fin| fin_trace_solver]. }
      apply trace_app_finite. split; [fin_trace_solver| ].
      subst tr. 
      unfold_acquire. cdes ACQ0. move TRw at bottom. subst.
      trace_app_elems_exh; try by_subst.
      { destruct (lock_not_next thread). by_subst. }
      { edestruct (@release_fence_no_write tr_relf0); by_subst. }
      destruct (NPeano.Nat.eq_dec pred 0); desc; subst.
      { trace_app_elems_exh. destruct (lock_not_status thread). by_subst. }
      { trace_app_elems_exh.
        { destruct (lock_not_next thread). by_subst. }
        eapply wait_trace_reads in TRw2; eauto. by_subst. }
      { edestruct (@acquire_fence_no_write tr_acqf); by_subst. }
      { edestruct (@release_fence_no_write tr_relf); by_subst. }

      unfold_release. cdes REL1. move TRw1 at bottom. subst.
      apply trace_app_finite. split; [fin_trace_solver| ]. 
      trace_app_elems_exh.      
      { destruct (lock_not_next thread). by_subst. }
      { edestruct (@acquire_fence_no_write tr_acqf0); by_subst. }
      { destruct (NPeano.Nat.eq_dec succ 0); des; desc; subst.
        { fin_trace_solver. }
        { trace_app_elems_exh; [by_subst| | ].
          { eapply wait_trace_reads in TRw3; by_subst. }
          destruct (lock_not_status ((valr
                    (trace_last
                       match tr_succ_wait with
                       | trace_fin l' =>
                           trace_fin
                             (ThreadEvent thread index3 (Aload lock other)
                              :: l')
                       | trace_inf f =>
                           trace_inf
                             (trace_prepend
                                [ThreadEvent thread index3 (Aload lock other)]
                                f)
                       end d_)))). by_subst. }
        { fin_trace_solver. }
      }
    Qed. 

    Lemma next_write0_thread:
      (E G ∩₁ is_w ∩₁ Loc_ (nth thread nexts 0) ∩₁ Valw_ 0 \₁ is_init) ⊆₁ Tid_ thread.
    Proof.
      red. intros w W.
      assert (0 < tid w < n_threads) as TID.
      { split.
        { cut (tid w <> 0); [lia| ].
          red. intros EQ0. eapply wf_tid_init in EQ0; by_subst. }
        { apply BOUNDED_THREADS. by_subst. }
      }
      forward eapply (@HMCS_CLIENT (tid w)); try lia. ins. desc. red in H.
      destruct (restrict G (tid w)) as [Gt' [TRE']]. desc.
      assert (trace_elems tr0 w) as TRw.
      { apply TR_E0, TRE'. by_subst. }
      red in HMCS. desc. red in ACQ, REL. desc.
      subst tr0 tr_acq tr_rel. trace_app_elems_exh.
      2: { edestruct (@acquire_fence_no_write tr_acqf0); by_subst. }
      2: { edestruct (@release_fence_no_write tr_relf0); by_subst. }
      2: { unfold_release. cdes REL1. subst.
           move TRw1 at bottom. trace_app_elems_exh.
           { forward eapply (@disj_statuses_nexts (tid w) (tid w)); [by_destruct w| ].
             lia. }
           { edestruct (@acquire_fence_no_write tr_acqf2); by_subst. }
           destruct (NPeano.Nat.eq_dec succ0 0); desc; des; subst.
           { trace_app_elems_exh.
             forward eapply (@disj_locs thread); [lia| ].
             ins. desc. destruct H0. by_destruct w. }
           { trace_app_elems_exh; try by_destruct w.
             { eapply wait_trace_reads in TRw3; eauto. by_subst. }
             forward eapply (@disj_statuses_nexts (valr
                    (trace_last
                       match tr_succ_wait with
                       | trace_fin l' =>
                           trace_fin
                             (ThreadEvent (tid w) index2 (Aload lock other)
                              :: l')
                       | trace_inf f =>
                           trace_inf
                             (trace_prepend
                                [ThreadEvent (tid w) index2 (Aload lock other)]
                                f)
                       end d_)) thread); by_destruct w. }
           { trace_app_elems_exh.
             forward eapply (@disj_statuses_nexts succ0 thread); by_subst. }
      }
      unfold_acquire. desc. subst.
      move TRw at bottom. trace_app_elems_exh.
      { forward eapply (@unique_statuses (tid w) thread); [by_destruct w| ].
        ins. des; by_subst. }
      { forward eapply (unique_nexts (tid w) thread); by_destruct w. }
      { edestruct (@release_fence_no_write tr_relf1); by_subst. }
      { forward eapply (@disj_locs thread); [lia| ].
        ins. desc. destruct H0. by_destruct w. }
      { destruct (NPeano.Nat.eq_dec pred 0); desc; subst.
        { trace_app_elems_exh.
          forward eapply (@disj_statuses_nexts (tid w) thread); by_destruct w. }
        { trace_app_elems_exh.
          { enough (tid w = 0); by_destruct w. }
          { eapply wait_trace_reads in TRw2; by_subst. }
        }
      }
    Qed.

    Lemma next_writes0:
      exists! w, (E G ∩₁ is_w ∩₁ Loc_ (nth thread nexts 0) ∩₁ Valw_ 0 \₁ is_init) w.
    Proof.
      cdes ACQ0.
      remember (ThreadEvent thread (index + 1) (Astore (nth thread nexts 0) 0)) as w.
      exists w. split.
      { unfolder. splits; try by_subst. apply tr_acqr_elemsET.
        subst. trace_elems_solver. }
      intros w' W'.
      assert (tid w' = thread) as TID.
      { rewrite (@next_write0_thread w'); by_subst. }
      assert (trace_elems tr w') as TRw'.
      { apply TR_E. by_subst. }
      subst tr. trace_app_elems_exh.
      2: { edestruct (@acquire_fence_no_write tr_acqf); by_subst. }
      2: { edestruct (@release_fence_no_write tr_relf); by_subst. }
      2: { unfold_release. cdes REL1. subst.
           move TRw'1 at bottom. trace_app_elems_exh.
           { forward eapply (@disj_statuses_nexts (tid w') (tid w')); [by_destruct w'| ].
             lia. }
           { edestruct (@acquire_fence_no_write tr_acqf0); by_subst. }
           destruct (NPeano.Nat.eq_dec succ 0); desc; des; subst.
           { trace_app_elems_exh.
             forward eapply (@disj_locs (tid w')); [by_subst| ].
             ins. desc. destruct H0. by_destruct w'. }
           { trace_app_elems_exh; try by_destruct w'.
             { eapply wait_trace_reads in TRw'3; eauto. by_subst. }
             forward eapply (@disj_statuses_nexts (valr
                     (trace_last
                        match tr_succ_wait with
                        | trace_fin l' =>
                            trace_fin
                              (ThreadEvent (tid w') index2 (Aload lock other)
                               :: l')
                        | trace_inf f =>
                            trace_inf
                              (trace_prepend
                                 [ThreadEvent (tid w') index2
                                    (Aload lock other)] f)
                        end d_)) (tid w')); by_destruct w'. }
           { trace_app_elems_exh.
             forward eapply (@disj_statuses_nexts succ (tid w')); by_destruct w'. }
      }
      unfold_acquire. desc. subst.
      move TRw' at bottom. trace_app_elems_exh.
      { forward eapply (@disj_statuses_nexts (tid w') (tid w')); [by_destruct w'| ].
        lia. }
      { edestruct (@release_fence_no_write tr_relf0); by_subst. }
      { forward eapply (@disj_locs (tid w')); [lia| ].
        ins. desc. destruct H0. by_destruct w'. }
      { destruct (NPeano.Nat.eq_dec pred 0); desc; subst.
        { trace_app_elems_exh. forward eapply (@disj_locs (tid w')); [by_destruct w'| ].
          ins. desc. destruct H1. by_destruct w'. }
        { trace_app_elems_exh.
          { forward eapply (@unique_nexts (tid w') pred); [by_destruct w'| ].
            ins. des; by_destruct w'. }
          { eapply wait_trace_reads in TRw'2; by_subst. }
        }
      }
    Qed. 

    Lemma release_real_fin:
      trace_finite tr_relr.
    Proof.
      cdes REL1. rewrite REL2. apply trace_app_finite. split.
      { fin_trace_solver. }
      destruct (NPeano.Nat.eq_dec succ 0); [| red in REL4; by_subst].
      des; [red in REL4; by_subst| ].
      rewrite REL4. apply trace_app_finite. split; [| red in REL6; by_subst].
      red in REL5. desc. rewrite REL5. apply trace_app_finite. split; [by_subst|].

      destruct acquire_real_events as [w_next0 [rmw [Wnext RMW]]].
      assert ((E G ∩₁ Tid_ thread) rmw) as Ermw.
      { apply TR_E. subst tr. trace_elems_solver. }
      remember (ThreadEvent thread index0 (Aload lock other)) as r_lock.
      forward eapply (@tr_relr_elemsET r_lock) as ETr_lock.
      { subst. trace_elems_solver. }
      assert (exists rmw', rf G rmw rmw' /\ co G rmw rmw') as [rmw' [RFlock COlock]].
      { apply next_rmw_exists with (r_lock := r_lock); eauto. 
        { by_subst. }
        eapply set_equiv_exp.
        { rewrite <- set_inter_minus_r, !set_interA; apply set_equiv_refl. }
        split; [| by_subst]. subst. trace_elems_solver. }

      assert ((E G ∩₁ Loc_ lock \₁ is_init) rmw') as ENIrmw'.
      { apply exploit_rf in RFlock; auto.
        apply exploit_co in COlock; by_destruct rmw'. }
      destruct (classic (Valw_ 0 rmw')) as [VAL0 | VAL'].
      { forward eapply (@lock_writes rmw') as LW'.
        { apply exploit_rf in RFlock; auto. apply exploit_co in COlock; auto.
          by_destruct rmw'. }
        forward eapply (@release_no_wait rmw') as TR_FIN. 
        { apply set_inter_minus_r. do 4 apply set_interA. split; [| by_destruct rmw'].
          red in LW'. desc. des.
          { rewrite VAL0 in LW'0. symmetry in LW'0.
            eapply wf_tid_init in LW'0; by_subst. }
          apply TR_E. split; [by_subst| ].
          rewrite <- LW'1. erewrite <- wf_rfv; eauto. by_subst. }
        (* TODO: here we already have the finiteness of the whole trace *)
        subst tr. subst.
        repeat (exploit_trace_app_finite; auto). }
      
      assert (exists w_next', (is_w ∩₁ Loc_ (nth thread nexts 0) \₁ Valw_ 0) w_next' /\
                         sb G rmw' w_next') as [w_next' [Wnext' SB]].
      { apply next_write_of_rmw.
        unfolder. splits; try by_destruct rmw'.
        erewrite <- wf_rfv; eauto. by_subst. }
      
      assert (mo_max G w_next' \/ mo_max G w_next0) as MAX.
      { forward eapply (@fin_w_max G (nth thread nexts 0)) as [wmax [MAX LOC]]; auto.
        { apply fin_l_writes. }
        assert ((E G \₁ is_init) w_next0) as ENIw_next0.
        { split. 
          2: { unfolder in Wnext. desc. apply tr_acqr_elemsET in Wnext. 
               red. intros. eapply wf_tid_init in H; by_subst. }
          unfolder in Wnext. desc. apply tr_acqr_elemsET in Wnext. by_subst. }
        assert ((E G ∩₁ is_w ∩₁ Loc_ (nth thread nexts 0) \₁ is_init) wmax) as WMAX_.
        { enough (~ is_init wmax).
          { red in MAX. by_subst. }
          red. intros. red in MAX. desc. red in MAX0.
          apply (MAX0 w_next0). red. splits; try by_subst.
          apply co_init_l; eauto; by_subst. }
        
        destruct (classic (Valw_ 0 wmax)).
        { right. replace w_next0 with wmax; auto.
          eapply unique_eq; [apply next_writes0| ..].
          { by_subst. }
          { desc.
            pose proof RMW0 as RMW0_. apply seq_eqv_lr in RMW0_. 
            assert (~ is_init w_next0) as NINITw_next0.
            { unfolder in Wnext. desc. apply tr_acqr_elemsET in Wnext. 
              red. intros. eapply wf_tid_init in H0; eauto; by_subst. }
            by_subst. }
        }
        { left. replace w_next' with wmax; auto.
          eapply (@next_write_unique thread); auto. 
          { red in MAX. by_subst. }
          { apply seq_eqv_lr in SB. by_subst. }        
        }
      }
      des.
      { contra INF.
        assert (trace_elems tr_succ_wait ⊆₁ E G) as WAIT_E.
        { transitivity (trace_elems tr_relr).
          2: { rewrite tr_relr_elemsET. basic_solver. } 
          subst. do 2 (rewrite trace_elems_app, emiT; [| fin_trace_solver]).
          rewrite <- trace_app_assoc, trace_elems_app, emiT; [| fin_trace_solver].
          rewrite trace_elems_app. basic_solver. }
        forward eapply (wait_latest_read_helper REL8) as [i LATEST]; try by_subst.
        { unfold tr in TR_WF. apply trace_wf_app_both in TR_WF.
          2: { apply trace_app_finite. split; [apply acquire_real_fin | fin_trace_solver]. }
          subst. cdes TR_WF. repeat exploit_trace_app_finite.
          rewrite <- !trace_app_assoc in TR_WF1. 
          repeat (match goal with
                  | H: trace_wf (trace_app ?t1 ?t2) |- _ =>
                    apply trace_wf_app_both in H; [| fin_trace_solver]; desc; try by auto
                  end).
          by apply trace_wf_app in TR_WF5. }
        
        apply INF. eapply wait_fin_iff_cond; eauto.
        assert (NOmega.lt_nat_l i (trace_length tr_succ_wait)) as DOMi.
        { destruct tr_succ_wait; [edestruct INF; vauto | by_subst]. }
        remember (trace_nth i tr_succ_wait d_) as r. exists r.
        assert (trace_elems tr_succ_wait r) as WAIT_R. 
        { subst r. by apply trace_nth_in. }
        split; auto. 
        forward eapply (@RFC r) as [w RF]. 
        { split; [basic_solver| ]. 
          eapply wait_trace_reads in WAIT_R; eauto. by_subst. }
        specialize (LATEST i w). specialize_full LATEST; [lia| ..].
        { erewrite trace_nth_indep; by_subst. }
        replace (valr r) with (valw w) by (apply exploit_rf in RF; by_subst).
        rewrite (@mo_max_unique_helper w w_next'); try by_subst.
        apply wait_trace_reads in REL8. specialize (REL8 r). specialize_full REL8.
        { subst r. by apply trace_nth_in. }
        apply exploit_rf in RF; by_subst. }
      
      forward eapply (@mo_max_co w_next0 w_next') as CO; try by_subst.
      { apply seq_eqv_lr in SB. unfolder. splits; by_subst. }
      red in CO. des; [by_subst| ].
      destruct no_cycle. exists rmw'. do 3 (eexists; split; eauto).
      exists rmw. split; [apply rt_refl| auto]. 
    Qed.
    
    Lemma thread_trace_finite:
      trace_finite tr. 
    Proof.
      destruct acquire_real_fin, release_real_fin.
      subst tr. fin_trace_solver. 
    Qed.
      
  End InsideThread. 

  

  Lemma hmcs_acqiure_release_terminates_induction thread
        (IND: forall thread' (ORD: lock_order thread' thread),
            set_finite (E G ∩₁ Tid_ thread' \₁ is_init)):
    set_finite (E G ∩₁ Tid_ thread \₁ is_init).
  Proof.
    destruct (PeanoNat.Nat.eq_0_gt_0_cases thread) as [| NINIT].
    { subst. rewrite tid0_init. exists []. basic_solver. }
    destruct (PeanoNat.Nat.le_gt_cases n_threads thread) as [| LT].
    { rewrite no_excessive_events; auto. exists []. basic_solver. }
    cdes HMCS_CLIENT. specialize (HMCS_CLIENT0 thread). 
    specialize_full HMCS_CLIENT0; eauto; [lia| ]. desc.
    
    red in HMCS_CLIENT0. destruct (restrict G thread) as [Gt [TRE]]. desc.
    unfold hmcs_acqiure_release, hmcs_acquire, hmcs_release in HMCS. desc. 
    arewrite (E G ∩₁ Tid_ thread \₁ is_init ⊆₁ E G ∩₁ Tid_ thread) by basic_solver.
    rewrite <- TRE, <- TR_E.

    apply nodup_trace_elems; [by apply trace_wf_nodup| ].
    subst. eapply thread_trace_finite; eauto.
    { etransitivity; eauto. }
    
    ins. specialize (IND _ ORD).
    rewrite set_union_minus_alt with (s' := is_init).
    rewrite set_interA. arewrite (Tid_ thread' ∩₁ is_init ⊆₁ ∅).
    2: { by rewrite set_inter_empty_r, set_union_empty_l. }
    red. ins.
    apply lock_order_dom, seq_eqv_lr in ORD. desc. red in ORD. desc. 
    apply ORD2. replace thread' with (tid x) by by_subst.
    symmetry. eapply wf_tid_init; eauto; [| by_subst].
    apply wf_initE; by_subst.
  Qed.
  
  Lemma hmcs_acqiure_release_terminates thread:
    set_finite (E G ∩₁ Tid_ thread \₁ is_init). 
  Proof.    
    pattern thread.
    eapply well_founded_ind;
      [apply lock_order_wf | apply hmcs_acqiure_release_terminates_induction].
  Qed.
    
  Theorem hmcs_client_terminates_impl:
    set_finite (E G \₁ is_init).
  Proof.
    rewrite set_minusE. apply events_separation_inter.
    ins. rewrite <- set_minusE. apply hmcs_acqiure_release_terminates. 
  Qed.
  
End HMCSClientTermination.


Theorem hmcs_client_terminates
        (n_threads : nat)
        (lock : Loc)
        (statuses nexts : list Loc)
        (DISJ_LOC : NoDup (lock :: statuses ++ nexts))
        (STATUSES_LEN : length statuses = n_threads)
        (NEXTS_LEN : length nexts = n_threads)
        (LOCS_NO0 : ~ In 0 (lock :: statuses ++ nexts))
        (G : execution)
        (HMCS_CLIENT : hmcs_client n_threads lock statuses nexts G)
        (FAIR : mem_fair G)
        (SCpL : Execution.SCpL G)
        (WF : Wf G)
        (RFC : rf_complete G)
        (BOUNDED_THREADS : (fun thread : nat =>
                     exists e : Event, (E G ∩₁ Tid_ thread) e)
                    ≡₁ (fun thread : nat => thread < n_threads))
        (MODEL : sc_consistent G \/ TSO_consistent G \/ ra_consistent G)
  :
  set_finite (E G \₁ is_init). 
Proof. eapply hmcs_client_terminates_impl; eauto. Qed.

Redirect "axioms_hmcs" Print Assumptions hmcs_client_terminates.
