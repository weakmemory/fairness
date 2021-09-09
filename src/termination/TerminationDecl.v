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

Notation "'E' G" := (acts G) (at level 1). 
Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).
Notation "'Locs_' locs" := (fun x => In (loc x) locs) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

Ltac contra name :=
  match goal with
  | |- ?gl => destruct (classic gl) as [|name]; [auto|exfalso]
  end.


Definition mo_max G (w: Event) := (E G ∩₁ is_w) w /\ max_elt (restr_rel (E G ∩₁ is_w) (co G)) w. 

Record thread_restricted_execution Gfull thread Gthread :=
  { tr_acts_set: E Gthread ≡₁ E Gfull ∩₁ Tid_ thread;
  }.

Definition restrict G thread: {Gt | thread_restricted_execution G thread Gt}.
  set (Gt := {| acts := E G ∩₁ Tid_ thread; rf := ∅₂; co := ∅₂; |}).
  exists Gt. by subst. 
Qed. (* don't care about definition *)


Lemma events_separation G:
  (E G ≡₁ ⋃₁ t, E (proj1_sig (restrict G t))).
Proof.
  split.
  2: { apply set_subset_bunion_l. ins.
       destruct (restrict G x) as [Gt TRE]. simpl.
       destruct TRE. rewrite tr_acts_set0. basic_solver. }
  red. intros e Ee.
  exists (tid e). split; auto.
  destruct (restrict G (tid e)) as [Gt TRE]. simpl.
  destruct TRE. apply tr_acts_set0.
  split; vauto.
Qed. 

Lemma fin_w_max G l (WF: Wf G)
      (BOUNDED_WRITES: set_finite (E G ∩₁ is_w ∩₁ Loc_ l)):
  exists w, mo_max G w /\ Loc_ l w. 
Proof.
  forward eapply (@latest_fin _ (E G ∩₁ is_w ∩₁ Loc_ l) (co G))
    as [w [W LATEST]]; auto. 
  { apply set_nonemptyE. exists (InitEvent l). unfolder. splits; vauto.
    by apply wf_initE. }
  { red. split.
    { red. split; [apply co_irr | apply co_trans]; auto. }
    { eapply is_total_mori; [| reflexivity |by apply wf_co_total with (x := l)]. 
      red. basic_solver 10. }
  }
  exists w. unfold mo_max, max_elt. unfolder in *. desc. splits; auto.
  ins. desc. specialize (LATEST b). specialize_full LATEST.
  { splits; vauto.
    symmetry. eapply wf_col; eauto. }
  des.
  { subst. eapply co_irr; eauto. }
  { eapply co_acyclic; eauto. apply ct_unit. eexists. split; eauto. by apply ct_step. }
Qed.  

(* The formalization of the Theorem 5.3. 
   Note that here we actually prove a stronger statement 
   because there are no explicit spinlock and iterations definitions. *)
Lemma inf_reads_latest (tr: trace Event) (G: execution) (locs: list Loc)
      (INF_READS: ~ set_finite (trace_elems tr ∩₁ is_r ∩₁ Locs_ locs))
      (BOUNDED_THREADS: exists n, forall e, E G e -> tid e < n)
      (IN_G: trace_elems tr ⊆₁ E G)
      (NODUP: trace_nodup tr)
      (BOUNDED_WRITES: set_finite (E G ∩₁ is_w ∩₁ Locs_ locs))
      (WF: Wf G)
      (FAIR: mem_fair G)
      (RFC: rf_complete G):
  exists (i: nat), forall (j: nat) (w: Event) (LE: i <= j) (RF: rf G w (trace_nth j tr w))
         (Li: Locs_ locs (trace_nth j tr w)),
      mo_max G w. 
Proof.
  destruct tr eqn:TR; [| rewrite <- TR in *]. 
  { destruct INF_READS. simpl.
    apply set_finite_mori with (x := (fun a => In a l)); [red; basic_solver| by vauto]. }
  desc.
  
  contra H. pose proof (@not_ex_all_not nat _ H) as OLD_READS. clear H. simpl in OLD_READS.

  red in FAIR. desc. red in FAIR0.
  forward eapply (@functional_choice Loc Event (fun l w => In l locs -> mo_max G w /\ Loc_ l w)) as [mo_max_of MO_MAX_OF]. 
  { ins. destruct (classic (In x locs)).
    2: { exists (InitEvent 0). tauto. }
    forward eapply fin_w_max with (l := x); vauto.
    { arewrite (Loc_ x ⊆₁ Locs_ locs) by basic_solver. }
    ins. desc. vauto. }
  forward eapply (@functional_choice Loc (list Event) (fun l pref => forall r, fr G r (mo_max_of l) -> In r pref)) as [pref_of PREF_OF]; [by ins| ]. 
  set (w_pref := flat_map pref_of locs). 

  (* a subtle technicality: *)
  (* add writes to that list to handle case when the last write is a RMW *)
  assert (set_finite (E G ∩₁ (fun a : Event => is_w a) ∩₁ Locs_ locs)) as [writes WRITES].
  { arewrite (Locs_ locs ⊆₁ (⋃₁ l ∈ (fun x => In x locs), Loc_ l)) by basic_solver. 
    repeat rewrite <- set_bunion_inter_compat_l. apply set_finite_bunion; [by vauto| ].
    ins. arewrite (Loc_ a ⊆₁ Locs_ locs) by basic_solver. }

  set (pref_E := filterP (trace_elems tr) (w_pref ++ writes)).
  forward eapply (@functional_choice Event nat (fun e n => In e pref_E -> fl n = e)) as [e2i E2I]. 
  { ins. destruct (classic (In x pref_E)).
    2: { exists 0. by ins. }
    subst pref_E. apply in_filterP_iff in H. desc.
    apply trace_in_nth with (d := InitEvent 0) in H0. desc.
    exists n0. ins. by subst tr. }
  set (n' := max_of_list (map e2i pref_E) + 1).

  assert (forall i d (EPREF: In (trace_nth i tr d) pref_E), i < n') as INDEX_BOUND.
  { ins. remember (trace_nth i tr d) as e.     
    assert (In (e2i e) (map e2i pref_E)) as I_BOUND; [by apply in_map| ]. 
    pose proof (in_max_of_list _ _ I_BOUND).
    cut (e2i e = i); [by lia| ].
    eapply (trace_nodup_inj NODUP) with (d := d) (d' := d); vauto.
    simpl in *. by rewrite E2I. }
  
  specialize (OLD_READS n').
  apply (@not_all_ex_not _ _) in OLD_READS as [j OLD_READ].  
  apply (@not_all_ex_not _ _) in OLD_READ as [w' OLD_READ]. 
  apply imply_to_and in OLD_READ as [LE OLD_READ].
  apply imply_to_and in OLD_READ as [RFj OLD_READ].
  apply imply_to_and in OLD_READ as [Lj OLD].
  
  remember (trace_nth j tr w') as ej.
  remember (mo_max_of (loc ej)) as w.
  assert (is_r ej) as Rj.
  { apply wf_rfD, seq_eqv_lr in RFj; auto. by desc. }
  (* assert (In (loc ej) locs) as LOCj. *)
  (* { apply FIN_LOCS. vauto. } *)
  assert ((E G ∩₁ (fun a : Event => is_w a) ∩₁ Loc_ (loc w)) w') as W'.
  { apply (wf_rfD WF), seq_eqv_lr in RFj. desc. apply (wf_rfE WF), seq_eqv_lr in RFj0. desc. 
    unfolder. splits; auto.
    transitivity (loc ej); [by apply (wf_rfl WF)| ].
    subst w. specialize (MO_MAX_OF (loc ej) Lj). desc. congruence. }
  assert ((E G ∩₁ (fun a : Event => is_w a) ∩₁ Loc_ (loc w)) w) as W.
  { specialize (MO_MAX_OF (loc ej) Lj). desc. red in MO_MAX_OF. desc.
    splits; vauto. }
  assert (co G w' w) as COw'w.
  { pose proof (@wf_co_total _ WF (loc w)) as TOT. red in TOT.
    specialize TOT with (a := w) (b := w'). specialize_full TOT; auto.
    { red. ins. subst w'. specialize (MO_MAX_OF (loc ej) Lj). desc. congruence. }
    des; [| done]. exfalso.
    specialize (MO_MAX_OF (loc ej) Lj). desc. red in MO_MAX_OF. desc. eapply MO_MAX_OF1.
    red. splits; [by vauto| generalize W| generalize W']; basic_solver. }
  specialize (PREF_OF (loc ej) ej). specialize_full PREF_OF. 
  { red. split.
    { red. exists w'. split; vauto. }
    unfolder. red. ins. desc. rewrite <- Heqw in H. 
    specialize (INDEX_BOUND j w'). specialize_full INDEX_BOUND; [| lia]. 
    subst pref_E. apply in_filterP_iff. split; [| vauto].
    apply in_app_iff. right. apply WRITES.
    rewrite <- Heqej, H. unfolder. unfolder in W. desc. splits; auto.
    replace (loc w) with (loc ej); auto. 
    subst w. specialize (MO_MAX_OF (loc ej)). desc. congruence. }

  specialize (INDEX_BOUND j w'). specialize_full INDEX_BOUND; [| lia].  
  subst pref_E. rewrite filterP_app. apply in_app_l, in_filterP_iff. split; [| by vauto].
  subst w_pref. apply in_flat_map. exists (loc ej). split; vauto. 
Qed. 
  
Lemma exploit_rf G w r (WF: Wf G) (RF: rf G w r):
  rf G w r /\ E G w /\ E G r /\ is_w w /\ is_r r /\ same_loc w r /\ valw w = valr r.
Proof.
  generalize (proj1 (wf_rfE WF) _ _ RF), (proj1 (wf_rfD WF) _ _ RF),
  (wf_rfl WF), (wf_rfv WF).
  basic_solver. 
Qed.

Lemma exploit_co G w1 w2 (WF: Wf G) (CO: co G w1 w2):
  co G w1 w2 /\
  E G w1 /\ E G w2 /\
  is_w w1 /\ is_w w2 /\
  same_loc w1 w2 /\
  ~ is_init w2. 
Proof.
  generalize (proj1 (wf_coE WF) _ _ CO), (proj1 (wf_coD WF) _ _ CO),
  (wf_col WF), (proj2 (co_ninit WF) _ _ CO). 
  basic_solver. 
Qed.

Lemma inf_reads_latest_full tr G locs 
      (INF_READS: ~ set_finite (trace_elems tr ∩₁ is_r))
      (BOUNDED_THREADS: exists n, forall e, E G e -> tid e < n)
      (IN_G: trace_elems tr ⊆₁ E G)
      (FIN_LOCS: trace_elems tr ∩₁ is_r ⊆₁ Locs_ locs)
      (NODUP: trace_nodup tr)
      (BOUNDED_WRITES: set_finite (E G ∩₁ is_w ∩₁ Locs_ locs))
      (WF: Wf G)
      (FAIR: mem_fair G)
      (RFC: rf_complete G):
  exists i, forall j w (LE: i <= j) (RF: rf G w (trace_nth j tr w)), mo_max G w. 
Proof.
  forward eapply inf_reads_latest; eauto.
  { red. ins. apply INF_READS. rewrite <- (set_interK (_ ∩₁ _)).
    by rewrite FIN_LOCS at 2. }
  ins. desc. exists i. ins. eapply H; eauto.
  apply FIN_LOCS. apply exploit_rf in RF; auto. desc. split; auto.
  apply trace_nth_in. destruct tr; [| done].
  destruct INF_READS. simpl. 
  apply set_finite_mori with (x := (fun a => In a l)); [red; basic_solver| by vauto].
Qed. 


Lemma fin_iff_tre_fin G (BOUNDED_THREADS: exists n, forall e, E G e -> tid e < n):
  set_finite (E G \₁ is_init) <-> forall t Gt (TRE: thread_restricted_execution G t Gt), set_finite (E Gt \₁ is_init).
Proof.
  split; intros FIN. 
  { ins.
    eapply set_finite_mori; eauto. red.  
    destruct TRE. rewrite tr_acts_set0. basic_solver. }
  { desc. apply set_finite_mori with (x := ⋃₁ t < n, E (proj1_sig (restrict G t)) \₁ is_init).
    { red. red. intros x [Ex NIx].
      exists (tid x). split; auto.
      destruct (restrict G (tid x)) as [Gt TRE]. simpl.
      destruct TRE. split; auto. apply tr_acts_set0. split; auto. }
    apply set_finite_bunion.
    { exists (List.seq 0 n). ins. by apply in_seq0_iff. }
    intros t LT. apply (FIN t).  
    by destruct (restrict G t) as [Gt TRE]. }
Qed.

Section Utils.
  Context {A: Type}. 

  Lemma cycle_helper2 (r: relation A) x y (AC: acyclic r) 
        (R1: r x y) (R2: r y x):
    False.
  Proof. apply (AC x). vauto. Qed. 
  
  Lemma cycle_helper3 (r: relation A) x y z (AC: acyclic r) 
        (R1: r x y) (R2: r y z) (R3: r z x):
    False.
  Proof. apply (AC x). apply ct_unit. exists z. split; vauto. Qed. 
  
  Lemma inter_subset_helper (S S1 S2: A -> Prop):
    (forall x (Sx: S x), S1 x <-> S2 x) -> S ∩₁ S1 ≡₁ S ∩₁ S2.
  Proof.
    ins. apply set_equiv_exp_iff. ins. specialize (H x).
    unfold set_inter. 
    split; ins; desc; split; intuition.
  Qed.

  Lemma max_elt_unique (r: relation A) (S: A -> Prop) x y
        (STO: strict_total_order S r) (Sx: S x) (Sy: S y)
        (MAXx: max_elt (restr_rel S r) x) (MAXy: max_elt (restr_rel S r) y):
    x = y.
  Proof.
    contra NEQ.
    red in STO. desc. red in STO0. specialize (STO0 _ Sx _ Sy NEQ).
    des; [eapply MAXx | eapply MAXy]; vauto. 
  Qed.
  
End Utils.


Section ScplHelpers.
Variable G: execution.
Hypothesis WF: Wf G.
Hypothesis SCL: SCpL G. 
  
Lemma sb_w_loc w1 w2 (W1: is_w w1) (W2: is_w w2) (SB: sb G w1 w2) (SL: same_loc w1 w2):
  co G w1 w2.
Proof.
  pose proof (@wf_co_total _ WF (loc w1)) as TOT. red in TOT.
  apply wf_sbE, seq_eqv_lr in SB. desc. 
  specialize TOT with (a := w1) (b := w2). specialize_full TOT.
  1, 2: unfolder; splits; vauto.
  { red. ins. generalize (@sb_irr G w1). vauto. }
  des; [done| ].
  exfalso. do 2 red in SCL. apply (SCL w1).
  apply ct_unit. red. exists w2. split; [| basic_solver].
  apply ct_step. repeat left. split; auto.
Qed.

Lemma sb_rf_co r1 r2 w1 w2
      (SB: (sb G)^? r1 r2) (RF1: rf G w1 r1) (RF2: rf G w2 r2)
      (SL: same_loc r1 r2):
  (co G)^? w1 w2.
Proof.
  destruct (classic (w1 = w2)) as [| NEQ]; [basic_solver| ].
  red in SB. des.
  { subst. left. eapply wf_rff; eauto. } 
  pose proof (@wf_co_total _ WF (loc w1)) as TOT. red in TOT.
  assert (same_loc w1 w2) as SLw.
  { apply wf_rfl in RF1; [apply wf_rfl in RF2| ]; auto. congruence. }
  Ltac ext_rf hyp := apply (wf_rfE WF), seq_eqv_lr in hyp as [Ew [RF_ Er]]; apply (wf_rfD WF), seq_eqv_lr in RF_ as [Ww [tgt Rr]].
  specialize TOT with (a := w1) (b := w2).
  specialize_full TOT; [ext_rf RF1| ext_rf RF2| done|].
  1, 2: unfolder; splits; done.
  des; [basic_solver| ].
  exfalso. do 2 red in SCL.
  assert (fr G r2 w1) as FR.
  { red. split; [exists w2; split; done| ].
    unfolder. red. ins. desc. subst r2.
    apply (SCL r1), ctEE. exists 1. split; auto. red.
    exists w1. split; [| basic_solver].
    apply seq_eqv_l. split; auto. repeat left. red. split; auto. }
    
  apply (SCL r1), ctEE. exists 2. split; auto. red.
  exists w1. split; [| basic_solver 10].
  exists r2. split; [| basic_solver 10].
  apply seq_eqv_l. split; auto. repeat left. red. split; auto.
Qed.

Lemma rf_co_helper w w' (RF: rf G w w') (W': is_w w'):
  co G w w'.
Proof.
  apply (wf_rfE WF), seq_eqv_lr in RF. desc.
  apply (wf_rfD WF), seq_eqv_lr in RF0. desc.
  apply (wf_rfl WF) in RF2 as LOC. 
  forward eapply (@wf_co_total _ WF (loc w)) with (a := w) (b := w') as TOT; vauto.
  { red. ins. edestruct rf_irr; vauto. }
  des; [done| ].
  destruct (cycle_helper2 _ w w' SCL); basic_solver.  
Qed.

Lemma nodup_trace_elems {A: Type} (tr: trace A) (NODUP: trace_nodup tr):
  trace_finite tr <-> set_finite (trace_elems tr).
Proof.
  split; intros FIN. 
  { unfold trace_finite in FIN. destruct tr; desc; vauto. }
  forward eapply (@trace_nodup_size _ tr); auto.
  unfold set_size. destruct (excluded_middle_informative _); [| done].
  destruct tr; [| done]. destruct FIN. vauto.
Qed.

Lemma co_sto l:
  strict_total_order (E G ∩₁ is_w ∩₁ Loc_ l) (co G).
Proof.
  red. split; [| by apply wf_co_total]. 
  red. split; [apply co_irr | apply co_trans]; auto. 
Qed.

End ScplHelpers. 
    

Lemma emiT {A: Type} {P: Prop} (b1 b2: A) (p: P):
  (ifP P then b1 else b2) = b1.
Proof. by destruct (excluded_middle_informative P). Qed. 

Lemma emiF {A: Type} {P: Prop} (b1 b2: A) (np: ~ P):
  (ifP P then b1 else b2) = b2.
Proof. by destruct (excluded_middle_informative P). Qed.

Lemma trace_wf_app tr1 tr2 (TWF: trace_wf (trace_app tr1 tr2)):
  trace_wf tr1. 
Proof.
  destruct tr1; [| done]. 
  red in TWF. 
  red. intros. specialize (TWF i j) with (d := d).
  simpl in LTj.
  do 2 rewrite trace_nth_app, emiT in TWF. 2-4: by (simpl; lia). 
  specialize_full TWF; auto.
  destruct tr2; [| done]. simpl. rewrite length_app. lia. 
Qed.

Lemma trace_wf_fin_app l1 tr2 (TWF: trace_wf (trace_app (trace_fin l1) tr2)):
  trace_wf tr2.
Proof.
  red in TWF. 
  red. ins. specialize (TWF (i + length l1) (j + length l1)) with (d := d).
  destruct tr2; simpl in *.
  { rewrite app_length in TWF. do 2 rewrite app_nth2 in TWF; try lia.
    repeat rewrite NPeano.Nat.add_sub in TWF.
    specialize_full TWF; auto; lia. }
  unfold trace_prepend in TWF. repeat rewrite NPeano.Nat.add_sub in TWF.
  replace (PeanoNat.Nat.ltb (i + length l1) (length l1)) with false in TWF;
    [replace (PeanoNat.Nat.ltb (j + length l1) (length l1)) with false in TWF| ].
  2, 3: symmetry; apply NPeano.Nat.ltb_ge; lia.
  apply TWF; lia.  
Qed. 

Lemma trace_app_nil_r {A: Type} (tr: trace A):
  trace_app tr (trace_fin []) = tr.
Proof.
  destruct tr; simpl; f_equal; auto using app_nil_r.
Qed. 

Lemma trace_app_finite {A: Type} (tr1 tr2: trace A):
  trace_finite (trace_app tr1 tr2) <-> trace_finite tr1 /\ trace_finite tr2.
Proof.
  unfold trace_finite. destruct tr1, tr2; split; ins; desc; vauto. 
Qed. 

Lemma trace_wf_app_sb tr1 tr2 e1 e2 (TWF: trace_wf (trace_app tr1 tr2))
      (FIN1: trace_finite tr1)
      (TR1: trace_elems tr1 e1) (TR2: trace_elems tr2 e2)
      (TID: tid e1 = tid e2):
  ext_sb e1 e2.
Proof.
  destruct tr1 as [l1| ]; [| by destruct FIN1]. 
  red in TWF. apply In_nth_error in TR1 as [i IN1].
  set (d_ := InitEvent 0). 
  pose proof (trace_in_nth _ _ TR2 d_) as [j [DOMj J]].
  assert (trace_nth i (trace_app (trace_fin l1) tr2) d_ = e1) as I'.
  { rewrite trace_nth_app, emiT.
    { simpl. erewrite nth_error_nth; eauto. }
    apply nth_error_Some. by rewrite IN1. }
  assert (trace_nth (length l1 + j) (trace_app (trace_fin l1) tr2) d_ = e2) as J'.
  { rewrite trace_nth_app, emiF.
    { simpl. by rewrite Minus.minus_plus. }
    simpl. lia. }
  specialize (TWF i (length l1 + j)) with (d := d_). specialize_full TWF.
  { apply PeanoNat.Nat.lt_lt_add_r, nth_error_Some. by rewrite IN1. }
  { rewrite trace_length_app. destruct (trace_length tr2); [done | simpl in *; lia]. }
  { congruence. }
  rewrite I', J' in TWF. red. destruct e1, e2; simpl in *; auto; lia.
Qed.

Definition busywait l tr cond :=
  exists tr_fail tr_ok,
  ⟪BW_APP: tr = trace_app tr_fail tr_ok ⟫ /\
  ⟪BW_FAIL: forall e (TRe: trace_elems tr_fail e),
      exists thread index val, e = ThreadEvent thread index (Aload l val) /\
                          ~ cond val⟫ /\
  ⟪BW_trace: exists thread index val,
      tr_ok = trace_fin [ThreadEvent thread index (Aload l val)] /\
      cond val⟫.

Lemma wait_trace_reads l tr cond
      (WAIT: busywait l tr cond):
  trace_elems tr ⊆₁ is_r ∩₁ Loc_ l \₁ is_w. 
Proof.
  red in WAIT. desc. subst.
  rewrite trace_elems_app. apply set_subset_union_l. split. 
  { red. ins. apply BW_FAIL in H. desc. by subst. }
  destruct (excluded_middle_informative _); [basic_solver | done].
Qed.

Lemma wait_fin_iff_cond l tr cond
      (WAIT: busywait l tr cond):
  trace_finite tr <-> exists e, trace_elems tr e /\ cond (valr e). 
Proof.
  split. 
  { intros FIN.
    red in WAIT. desc. subst.
    exists (ThreadEvent thread index (Aload l val)). split; [| done].
    apply trace_in_app. right. split; [| by vauto]. 
    apply trace_app_finite in FIN. desc. red in FIN. desc. by subst. }
  intros [e [TRe CONDe]]. red in WAIT. desc.
  subst tr. apply trace_app_finite. split; [| by vauto].
  contra INF. apply trace_elems_app in TRe. rewrite emiF in TRe; [| done].
  red in TRe. des; [| done]. specialize (BW_FAIL e TRe). desc. by subst. 
Qed.

Lemma wait_nonempty l tr cond (WAIT: busywait l tr cond):
  tr <> trace_fin [].
Proof.
  red in WAIT. desc. subst. destruct tr_fail; vauto.
  simpl. red. intros EQ. inversion EQ. apply app_eq_nil in H0. by desc. 
Qed. 
