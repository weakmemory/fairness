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
Require Import Subtrace.

Notation "'E' G" := (acts G) (at level 1). 
Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).
Notation "'Locs_' locs" := (fun x => In (loc x) locs) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'Valr_' v" := (fun x => valr x = v) (at level 1).
Notation "'Valw_' v" := (fun x => valw x = v) (at level 1).

Set Implicit Arguments. 

Ltac unfolder' := unfold trace_finite, set_compl, cross_rel, set_minus, set_inter, set_union, is_r, is_r_l, is_w, is_w_l, is_rmw, is_rmw_l, is_init, same_loc, loc, loc_l, valr, valr_l, valw, valw_l, lab, tid in *.
Ltac omegaW no := (destruct no; [done|simpl in *; lia]).

Section Utils.

Lemma set_nequiv_diff {A: Type} (S1 S2: A -> Prop) (NEQUIV: ~ (S1 ≡₁ S2)):
  exists x, ~ S1 x /\ S2 x \/ S1 x /\ ~ S2 x.
Proof. 
  contra ALL. apply NEQUIV.
  pose proof (@not_ex_all_not _ _ ALL). clear ALL. simpl in H.
  apply set_equiv_exp_iff. ins.  
  specialize (H x). tauto. 
Qed. 
  

Lemma same_relation_exp_iff {A: Type} (r1 r2: relation A):
  r1 ≡ r2 <-> forall x y, r1 x y <-> r2 x y.
Proof.
  split; [apply same_relation_exp| ].
  ins. split; red; ins; by apply H. 
Qed. 

Lemma restr_rel_exp_iff {A: Type} (r1 r2: relation A) (S: A -> Prop):
  restr_rel S r1 ≡ restr_rel S r2 <-> forall x y (X: S x) (Y: S y), r1 x y <-> r2 x y.
Proof.
  etransitivity; [apply same_relation_exp_iff| ]. split; ins; specialize (H x y).
  { unfold restr_rel in H. destruct H.
    split; ins; [forward eapply H | forward eapply H0]; vauto; ins; by desc. }
  { split; ins; red; unfold restr_rel in H0; desc;
      specialize_full H; auto; split; intuition. }
Qed.


End Utils.   



Ltac by_subst := by (subst; unfolder'; simpl in *; (lia || des; (vauto || lia))).

Section Iterations. 
(* Tools to reason about a trace that is a concatenation of (possibly infinite) 
   amount of iterations each of which satisfies the given predicate. *)

Variables (A: Type).
(* Single iteration predicate. *)
Variable (M: trace A -> Prop).
(* Iterations bounds and total amount. *)
Variables (bounds: nat -> nat_omega) (n_iters: nat_omega).

Definition no2n no := match no with | NOnum n => n | NOinfinity => 0 end.

Definition iterates tr :=
  ⟪BOUND0: bounds 0 = NOnum 0 ⟫ /\
  ⟪MON: forall i (ITER: NOmega.lt_nat_l i n_iters),
      NOmega.lt (bounds i) (bounds (i + 1))  ⟫ /\
  ⟪ITER: forall i (ITER: NOmega.lt_nat_l i n_iters),
      let len := NOmega.sub (bounds (i + 1)) (bounds i) in
      let iter := subtrace tr (no2n (bounds i)) len in 
      M iter ⟫ /\
  ⟪BOUND_MATCH: match n_iters with
                | NOnum n => bounds n = trace_length tr
                | NOinfinity => ~ trace_finite tr
                end⟫.

Lemma iters_elem_bounds tr i (ITER_TL: iterates tr)
      (DOMi: NOmega.lt_nat_l i (trace_length tr)):
  exists j,
    NOmega.lt (NOnum j) n_iters /\
    NOmega.le (bounds j) (NOnum i) /\
    NOmega.lt (NOnum i) (bounds (j + 1)).
Proof.
  induction i.
  { exists 0. red in ITER_TL. desc. destruct n_iters.
    2: { destruct n.
         { simpl. destruct tr.
           2: { simpl in BOUND_MATCH. congruence. }
           simpl in BOUND_MATCH. rewrite BOUND0 in BOUND_MATCH.
           inversion BOUND_MATCH. destruct l; vauto. simpl in DOMi. lia. }
         splits; [by_subst | by rewrite BOUND0| ].
         specialize (MON 0). specialize_full MON; [by_subst| ]. congruence. }
    splits; try by_subst.
    { by rewrite BOUND0. }
    rewrite <- BOUND0. by apply MON. }
  specialize_full IHi; [omegaW (trace_length tr)| ]. desc.
  destruct (bounds (j + 1)) as [| b] eqn:J'. 
  { exists j. rewrite J'. splits; auto. omegaW (bounds j). }
  simpl in IHi1.
  destruct (classic (S i < b)).
  { exists j. rewrite J'. splits; auto. omegaW (bounds j). }
  assert (S i = b) by lia. subst b.
  exists (j + 1).
  assert (NOmega.lt (NOnum (j + 1)) n_iters) as LT. 
  { red in ITER_TL. desc. destruct n_iters as [| n_iters']; [done| ].
    simpl in *. destruct (classic (j + 1 < n_iters')); [done| ].
    assert (j + 1 = n_iters') by lia. subst n_iters'.
    destruct tr.
    2: { simpl in BOUND_MATCH. congruence. }
    simpl in *. rewrite BOUND_MATCH in J'. inversion J'. lia. }
  splits; auto.     
  { by rewrite J'. }
  rewrite <- J'. 
  red in ITER_TL. desc. by apply MON.
Qed.

Lemma iterates_mon tr (ITER_TL: iterates tr):
  forall i j (LT: i < j)
    (DOMj: NOmega.le (NOnum j) n_iters),
    NOmega.lt (bounds i) (bounds j).
Proof.
  ins.
  red in ITER_TL. desc. 
  apply lt_diff in LT as [d LT]. subst j. induction d.
  { apply MON. omegaW n_iters. }
  specialize_full IHd; [destruct n_iters; by_subst| ].
  eapply NOmega.lt_trans; eauto. 
  replace (i + S (S d)) with (i + S d + 1) by lia. apply MON.
  omegaW n_iters.
Qed. 
    
Lemma bounds_bound tr (ITER_TL: iterates tr):
  forall i (DOMi: NOmega.le (NOnum i) n_iters),
    ~ NOmega.lt (trace_length tr) (bounds i). 
Proof.
  intros. intros LT. 
  destruct tr eqn:TR; [| by_subst].
  red in ITER_TL. desc.
  destruct n_iters eqn:NI; [edestruct BOUND_MATCH; by_subst| ].
  simpl in *.
  simpl in DOMi. apply Lt.le_lt_or_eq in DOMi. des. 
  2: { subst i. rewrite BOUND_MATCH in LT. lia. }
  forward eapply (@iterates_mon tr) with (i := i) (j := n) as LTB; try by_subst.
  { red. splits; by_subst. }  
  destruct (bounds i), (bounds n); try by_subst.
  inversion BOUND_MATCH. simpl in LTB. lia.
Qed. 
      
Lemma iters_elems tr (ITER: iterates tr):
  trace_elems tr ≡₁
  (⋃₁i ∈ fun i => NOmega.lt_nat_l i n_iters,
               trace_elems (subtrace tr (no2n (bounds i)) (NOmega.sub (bounds (i + 1)) (bounds i)))).
Proof.
  split.
  2: { apply set_subset_bunion_l. ins. apply subtrace_incl. }
  red. ins. apply trace_in_nth with (d := x) in H as [n [DOMn NTH]].
  forward eapply (@iters_elem_bounds tr); eauto. intros. desc.
  exists j. split; [done| ].
  rewrite <- NTH. destruct (bounds j) as [| bj]; [done| simpl in H0].
  apply le_diff in H0 as [i LE]. rewrite LE. simpl.
  assert (~
  NOmega.lt (trace_length tr)
    (NOmega.add (NOnum bj) (NOmega.sub (bounds (j + 1)) (NOnum bj)))). 
  { forward eapply bounds_bound with (i := j + 1); try by_subst.
    { omegaW n_iters. }
    intros. destruct (trace_length tr), (bounds (j + 1)); by_subst. }
  rewrite <- subtrace_trace_corr with (len := NOmega.sub (bounds (j + 1)) (NOnum bj)); auto.
  2: { omegaW (bounds (j + 1)). }
  apply trace_nth_in. rewrite subtrace_length; auto. 
  omegaW (bounds (j + 1)).
Qed. 

Lemma iters_disj_helper tr i j x
      (ITER: iterates tr) (LTij: i < j)
      (DOMj: NOmega.lt_nat_l j n_iters) (NODUP: trace_nodup tr):
  let iter := fun n => subtrace tr (no2n (bounds n)) (NOmega.sub (bounds (n + 1)) (bounds n)) in
  ~ (trace_elems (iter i) x /\ trace_elems (iter j) x).
Proof.
  simpl. intros [Ix Jx].
  apply trace_in_nth with (d := x) in Ix as [m [DOMm MTH]].
  apply trace_in_nth with (d := x) in Jx as [n [DOMn NTH]].
  red in ITER. desc.
  
  forward eapply bounds_bound with (i := j + 1) as DOMj'; [by_subst| omegaW n_iters| ].
  forward eapply (MON j DOMj) as BOUNDj.
  destruct (bounds j) as [| bj] eqn:BJ; try by_subst. simpl in *.
  remember (NOmega.sub (bounds (j + 1)) (NOnum bj)) as lenj.
  assert (~ NOmega.lt (trace_length tr) (NOmega.add (NOnum bj) lenj)) as BOUNDj'.
  { destruct (trace_length tr), (bounds (j + 1)); by_subst. }
  forward eapply (subtrace_length tr bj lenj) as LENj; [by_subst| ]. 
  rewrite subtrace_trace_corr in NTH; [| by_subst | rewrite <- LENj; by_subst].
  
  forward eapply bounds_bound with (i := i + 1) as DOMi'; [by_subst| omegaW n_iters| ]. 
  forward eapply (MON i) as BOUNDi; [omegaW n_iters| ]. 
  destruct (bounds i) as [| bi] eqn:BI; try by_subst. simpl in *. 
  remember (NOmega.sub (bounds (i + 1)) (NOnum bi)) as leni.
  assert (~ NOmega.lt (trace_length tr) (NOmega.add (NOnum bi) leni)) as BOUNDi'.
  { destruct (trace_length tr), (bounds (i + 1)); by_subst. }
  forward eapply (subtrace_length tr bi leni) as LENi; [by_subst| ].
  rewrite subtrace_trace_corr in MTH; [| by_subst | rewrite <- LENi; by_subst].

  destruct (NODUP (bi + m) (bj + n)) with (d := x); try congruence.
  2: { rewrite LENj in DOMn.
       destruct (trace_length tr), (bounds (j + 1)); by_subst. }
  assert (~ NOmega.lt (bounds j) (bounds (i + 1))) as FOO.
  { assert (i + 1 = j \/ i + 1 < j) by lia. des.
    { subst j. apply NOmega.lt_irrefl. }
    forward eapply iterates_mon with (i := i + 1) (j := j); try by_subst.
    { omegaW n_iters. }
    ins. destruct (bounds (i + 1)), (bounds j); by_subst. }
  rewrite BJ in FOO. destruct (bounds (i + 1)) as [| bi'] eqn:BI'; [by_subst| ].
  simpl in FOO. cut (bi + m < bi'); [lia| ].
  rewrite LENi, Heqleni in DOMm. by_subst.
Qed. 
  
Lemma iters_disj tr i j x
      (ITER_TL: iterates tr) (DOMi: NOmega.lt_nat_l i n_iters)
      (DOMj: NOmega.lt_nat_l j n_iters) (NODUP: trace_nodup tr):
  let iter := fun n => subtrace tr (no2n (bounds n)) (NOmega.sub (bounds (n + 1)) (bounds n)) in
  trace_elems (iter i) x /\ trace_elems (iter j) x -> i = j.
Proof.
  simpl. 
  pose proof (PeanoNat.Nat.lt_trichotomy i j) as LT.
  des; [| done| ]; ins; [| apply and_comm in H];
    eapply iters_disj_helper in H; by_subst.
Qed.

End Iterations. 

Section Ticketlock. 

Definition acquire_trace t tr ticket := 
  exists thread index,
    tr = trace_fin [ThreadEvent thread index (Armw t ticket (ticket + 1))].

Definition lock_trace s t tr := exists tr_acq tr_bw ticket,
    ⟪APP: tr = trace_app tr_acq tr_bw ⟫ /\
    ⟪ACQ: acquire_trace t tr_acq ticket ⟫ /\
    ⟪BW: busywait s tr_bw (eq ticket) ⟫.

Definition unlock_trace s tr := 
  exists thread index serving,
    tr = trace_fin [ThreadEvent thread index (Aload s serving); 
                   ThreadEvent thread (index + 1) (Astore s (serving + 1))].

Definition count_trace c tr :=
  exists thread index counter,
    tr = trace_fin [ThreadEvent thread index (Aload c counter); 
                   ThreadEvent thread (index + 1) (Astore c (counter + 1))].

(* Ticketlock's lock and unlock calls with thread's counter increase in between
   with 'serving', 'ticket' and counter at s, t and c correspondingly. *)
Definition ticketlock_execution (s t c: Loc) (tr: trace Event) :=
  exists tr_l tr_c tr_u,
    ⟪APP: tr = trace_app tr_l (trace_app tr_c tr_u) ⟫ /\
    ⟪L: lock_trace s t tr_l ⟫ /\
    ⟪CNT: count_trace c tr_c⟫ /\
    ⟪U: unlock_trace s tr_u ⟫ /\
    ⟪TID: exists thread_, trace_elems tr ⊆₁ Tid_ thread_ ⟫. 


End Ticketlock.


Section TicketlockProgress.

Variable G: execution.

(* 'serving' and 'ticket' locations. *)
Variable s t: Loc. 
Hypothesis (NEQst: s <> t).

(* In the paper we prove the growth of each thread's register values. 
   Since we can't express local registers values in a graph, 
   we introduce additional memory locations instead. *)
Variable counters: list Loc.
Variable n_threads: nat. 
Hypothesis CNT_CORR: ⟪CNTCORR: length counters = n_threads⟫. 
Hypothesis (CNT_NODUP: NoDup counters).
Hypothesis (CNT_DISJ: disjoint counters [s; t]).

Hypothesis (FAIR: mem_fair G).
Hypothesis (SCpL: SCpL G).
Hypothesis (WF: Wf G). 
Hypothesis (RFC: rf_complete G).
Hypothesis (BOUNDED_THREADS: (fun thread => exists e, (E G ∩₁ Tid_ thread) e)
                               ≡₁ (fun thread => thread < n_threads)).

(* To reason about infinite amount of iterations we explicitly store their
   bounds (in a thread's trace) and amounts. *)
Variable (thread_traces: list (trace Event))
         (thread_bounds: list (nat -> nat_omega))
         (thread_niters: list nat_omega).
Definition tr_ : trace Event := trace_fin [].
Definition bounds_ : nat -> nat_omega := fun _ => NOinfinity.
Definition niters_ := NOinfinity. 

Definition d_ := InitEvent 0.

Definition repeated_lock_unlock thread :=
  let tr := nth thread thread_traces tr_ in
  let (Gt, _) := restrict G thread in
  ⟪ITER: iterates (ticketlock_execution s t (nth thread counters 0))
                  (nth thread thread_bounds bounds_)
                  (nth thread thread_niters niters_)
                  tr ⟫ /\
  ⟪TR_E: trace_elems tr ≡₁ E Gt ⟫ /\
  ⟪TR_WF: trace_wf tr ⟫.

Definition repeated_ticketlock_client_execution :=
  forall thread (NINIT: thread <> 0) (CNT: thread < n_threads),
    ⟪REP_L_U: repeated_lock_unlock thread ⟫ /\
    ⟪INF: ~ set_finite (E G ∩₁ Tid_ thread)⟫ .

Hypothesis (TL_EXEC: repeated_ticketlock_client_execution).


Lemma tid_bounded: forall e, E G e -> tid e < n_threads.
Proof. ins. apply BOUNDED_THREADS. vauto. Qed. 

Definition valw_lt := fun x y => valw x < valw y.

Lemma iter_of_helper e (ENIe: (E G \₁ is_init) e):
  ⟪ITER: iterates (ticketlock_execution s t (nth (tid e) counters 0))
                  (nth (tid e) thread_bounds bounds_)
                  (nth (tid e) thread_niters niters_)
                  (nth (tid e) thread_traces tr_) ⟫ /\
  ⟪TR_E: trace_elems (nth (tid e) thread_traces tr_) ≡₁
         E (proj1_sig (restrict G (tid e))) ⟫ /\
  ⟪TR_WF : trace_wf (nth (tid e) thread_traces tr_) ⟫ /\
  ⟪INF: ~ set_finite (E G ∩₁ Tid_ (tid e)) ⟫. 
Proof.
  pose proof (@TL_EXEC (tid e)) as TL. specialize_full TL.
  { intros Z. apply (wf_tid_init WF) in Z; by_subst. }
  { apply BOUNDED_THREADS. by_subst. }
  desc. red in REP_L_U. destruct (restrict G (tid e)) as [Gt [TRE]]. desc. 
  eauto.
Qed. 


Lemma iter_of_exists e (ENIe: (E G \₁ is_init) e):
  exists i,
    let tr := nth (tid e) thread_traces tr_ in 
    let bounds := nth (tid e) thread_bounds bounds_ in 
    let n_iters := nth (tid e) thread_niters niters_ in 
    NOmega.lt_nat_l i n_iters /\
    trace_elems (subtrace tr (no2n (bounds i)) (NOmega.sub (bounds (i + 1)) (bounds i))) e.
Proof.
  destruct e eqn:E_; [by_subst| rewrite <- E_ in *].

  remember (nth (tid e) thread_traces tr_) as tr.
  forward eapply iter_of_helper; eauto. ins. desc.
  destruct (restrict G (tid e)) as [Gt [TRE]]. 

  assert (trace_elems tr e) as TRe.
  { rewrite Heqtr. apply TR_E, TRE. by_subst. }
  eapply iters_elems in TRe; [| by_subst]. by_subst.
Qed. 

Definition iter_of (e: Event): trace Event.
  destruct (excluded_middle_informative ((E G \₁ is_init) e)) as [ENIe| ]. 
  2: { exact tr_. }
  pose proof (iter_of_exists ENIe) as I.
  apply constructive_indefinite_description in I as [i I].
  exact (subtrace (nth (tid e) thread_traces tr_)
           (no2n (nth (tid e) thread_bounds bounds_ i))
           (NOmega.sub (nth (tid e) thread_bounds bounds_ (i + 1))
                       (nth (tid e) thread_bounds bounds_ i))).
Defined. 

Lemma iter_lu e (Ee: (E G \₁ is_init) e):
  ticketlock_execution s t (nth (tid e) counters 0) (iter_of e).
Proof.
  unfold iter_of. destruct (excluded_middle_informative _); [| done].
  destruct (constructive_indefinite_description _ _) as [i [DOMi ITERi]].
  forward eapply iter_of_helper; eauto. ins. desc.
  red in ITER. desc. apply ITER; auto.
Qed. 

Lemma iter_thread e (Ee: (E G \₁ is_init) e):
  trace_elems (iter_of e) ⊆₁ Tid_ (tid e).
Proof.
  unfold iter_of. destruct (excluded_middle_informative _); [| done].
  destruct (constructive_indefinite_description _ _) as [i [DOMi ITERi]].
  forward eapply iter_of_helper; eauto. ins. desc.
  transitivity (trace_elems (nth (tid e) thread_traces tr_)).
  { apply subtrace_incl. }
  destruct (restrict G (tid e)) as [Gt [TRE]]. rewrite TR_E, TRE. basic_solver. 
Qed.

Lemma iter_disj e1 e2 (Ee: (E G \₁ is_init) e1) (Ee': (E G \₁ is_init) e2)
      (ITER_NEQ: iter_of e1 <> iter_of e2):
  trace_elems (iter_of e1) ∩₁ trace_elems (iter_of e2) ≡₁ ∅.
Proof.
  split; [| done]. intros e [ITER1 ITER2].

  assert (tid e1 = tid e2) as SAME_TID. 
  { apply iter_thread in ITER1; [apply iter_thread in ITER2| ]; by_subst. }  
  
  unfold iter_of in *.
  do 2 (destruct (excluded_middle_informative _); [| done]). 
  destruct (constructive_indefinite_description _ _) as [i [DOMi ITERi]].
  destruct (constructive_indefinite_description _ _) as [j [DOMj ITERj]].

  forward eapply iter_of_helper; eauto. ins. desc. 
  remember (tid e1) as thread. rewrite <- SAME_TID in *.
  remember (nth thread thread_traces tr_) as tr.
  remember (nth thread thread_bounds bounds_) as bounds.

  apply ITER_NEQ. cut (i = j); [congruence| ].
  eapply iters_disj; eauto.
  apply trace_wf_nodup. auto. 
Qed.

Lemma iter_corr e e' (Ee: (E G \₁ is_init) e) (Ee': (E G \₁ is_init) e'):
  trace_elems (iter_of e') e <-> iter_of e' = iter_of e. 
Proof.
  pose proof (iter_thread Ee') as TID'.
  unfold iter_of in *. 
  do 2 (destruct (excluded_middle_informative _); [| done]). 
  destruct (constructive_indefinite_description _ _) as [i [DOMi ITERi]].
  destruct (constructive_indefinite_description _ _) as [j [DOMj ITERj]].  

  forward eapply iter_of_helper; eauto. ins. desc. 
  
  split.
  { intros TRe.
    remember (tid e) as thread.
    assert (tid e' = thread) by (apply TID' in TRe; by_subst).
    rewrite H in *. clear H.
    cut (i = j); [congruence| ].
    eapply iters_disj; eauto.
    apply trace_wf_nodup. auto. }
  { intros SAME.
    cut (i = j); [congruence| ]. 
    remember (tid e) as thread.
    assert (tid e' = thread).
    { rewrite <- SAME in ITERj. apply TID' in ITERj. congruence. }  
    rewrite H in *. clear H.
    eapply iters_disj with (x := e); eauto.
    { apply trace_wf_nodup. auto. }
    { split; congruence. }
  }
Qed.

Lemma iter_self e (Ee: (E G \₁ is_init) e):
  trace_elems (iter_of e) e. 
Proof. by apply iter_corr. Qed. 

Lemma iter_init l:
  iter_of (InitEvent l) = trace_fin [].
Proof. unfold iter_of. destruct (excluded_middle_informative _); by_subst. Qed.

Lemma iter_exec e (Ee: (E G \₁ is_init) e):
  trace_elems (iter_of e) ⊆₁ E G. 
Proof.
  unfold iter_of. 
  destruct (excluded_middle_informative _); [| done]. 
  destruct (constructive_indefinite_description _ _) as [i [DOMi ITERi]].
  forward eapply iter_of_helper; eauto. ins. desc.

  transitivity (trace_elems (nth (tid e) thread_traces tr_)).
  { apply subtrace_incl. }
  rewrite TR_E. destruct (restrict G (tid e)) as [Gt [TRE]].
  rewrite TRE. basic_solver. 
Qed.

Lemma iter_wf  e (Ee: (E G \₁ is_init) e):
  trace_wf (iter_of e).
Proof.
  unfold iter_of. 
  destruct (excluded_middle_informative _); [| done]. 
  destruct (constructive_indefinite_description _ _) as [i [DOMi ITERi]].

  unfold subtrace. destruct (excluded_middle_informative _) as [| LT].
  { red. by_subst. }
  do 2 (destruct (constructive_indefinite_description _ _)). desc.

  forward eapply iter_of_helper; eauto. ins. desc.
  remember (nth (tid e) thread_traces tr_) as tr.
  remember (nth (tid e) thread_bounds bounds_) as bounds.
  
  rewrite e1 in TR_WF. destruct x; [| by_subst]. 
  eapply trace_wf_app, trace_wf_fin_app. eauto. 
Qed.

Ltac unfold_subtraces H := unfold ticketlock_execution, lock_trace, count_trace, unlock_trace, acquire_trace, busywait in H. 

Lemma trace_finite_features tr c (TL: ticketlock_execution s t c tr)
      (CONTENTS: exists e, (trace_elems tr ∩₁ (Locs_ counters ∪₁ Loc_ s ∩₁ is_w)) e):
  trace_finite tr.
Proof.
  destruct CONTENTS as [e [TRe Ce]]. 
  unfold_subtraces TL. desc.  subst tr tr_acq tr_l tr_bw tr_ok tr_c tr_u.
  cut (trace_finite tr_fail).
  { ins. red in H. desc. rewrite H. vauto. }
  contra INF. do 2 rewrite <- trace_app_assoc in TRe.
  apply trace_in_app in TRe. des.
  { simpl in TRe. des; [| done]. subst e. unfolder in Ce. des; try basic_solver.
    unfolder'. apply (@CNT_DISJ t); vauto. }
  apply trace_elems_app in TRe0. rewrite emiF in TRe0; [| by vauto].
  red in TRe0. des; [| done]. specialize (BW_FAIL _ TRe0). desc.
  subst e. red in Ce. des; try by_subst.
  unfolder'. apply (@CNT_DISJ s); vauto.
Qed. 

Ltac exh := match goal with
            | |- (_ \/ _) => (left; exh) || (right; exh)
            | |- (_ /\ _) => splits; exh
            | |- _ => by vauto
            end. 

Ltac thread_helper thr e := specialize (thr e); specialize_full thr;
                            [subst; rewrite !trace_in_app; exh| by unfolder'].

Lemma fin_iter_struct' tr c (TL: ticketlock_execution s t c tr)
      (FIN: trace_finite tr):
  exists thread fail_reads index0 index1 index2 index3 ticket counter serving,
    let events :=
        ThreadEvent thread index0 (Armw t ticket (ticket + 1)) ::
        fail_reads ++
        [ThreadEvent thread index1 (Aload s ticket);
        ThreadEvent thread index2 (Aload c counter);
        ThreadEvent thread (index2 + 1) (Astore c (counter + 1));
        ThreadEvent thread index3 (Aload s serving);
        ThreadEvent thread (index3 + 1) (Astore s (serving + 1))]
    in
    ⟪STRUCT: tr = trace_fin events ⟫ /\
    ⟪FAIL_READS: forall e (IN_FAIL: In e fail_reads), exists thread index v,
          e = ThreadEvent thread index (Aload s v) /\ ticket <> v ⟫.
Proof.
  unfold_subtraces TL. desc.  

  assert (trace_finite tr_fail) as [fail_reads FIN_FAIL]. 
  { contra INF. 
    subst. do 2 (apply trace_app_finite in FIN; desc).
    by apply trace_app_finite in FIN1; desc. }
  
  assert (thread = thread_ /\ thread1 = thread_ /\
          thread0 = thread_ /\ thread2 = thread_);
    [|desc; subst thread thread0 thread1 thread2].
  { splits.
    - thread_helper TID (ThreadEvent thread index (Aload c counter)).
    - thread_helper TID (ThreadEvent thread1 index1 (Armw t ticket (ticket + 1))).
    - thread_helper TID (ThreadEvent thread0 index0 (Aload s serving)).
    - thread_helper TID (ThreadEvent thread2 index2 (Aload s ticket)). }
  
  subst. simpl in *. rewrite <- !app_assoc. simpl.
  do 8 (eexists; eauto).
Qed.

Lemma iter_w_unique tr w1 w2 c (TL: ticketlock_execution s t c tr)
      (W1: is_w w1) (W2: is_w w2)
      (SL: same_loc w1 w2)
      (TR1: trace_elems tr w1) (TR2: trace_elems tr w2)
      (CNT: In c counters):
  w1 = w2. 
Proof.
  assert (c <> s /\ c <> t) as DISJ; [| clear CNT].
  { apply not_or_and. red. ins. destruct (@CNT_DISJ c); by_subst. }
  
  unfold_subtraces TL. desc.  
  assert (forall w (W: is_w w) (TR: trace_elems tr w),
             In w [ThreadEvent thread1 index1 (Armw t ticket (ticket + 1));
                   ThreadEvent thread (index + 1) (Astore c (counter + 1));
                   ThreadEvent thread0 (index0 + 1) (Astore s (serving + 1))])
    as EXH.
  { ins. subst.
    repeat (apply trace_in_app in TR; des; try by_subst).
    { apply trace_in_app in TR0; des; try by_subst.
      specialize (BW_FAIL _ TR0). by_subst. }
    repeat (apply trace_in_app in TR0; des; try by_subst).
    simpl in TR3. des; try by_subst. intuition. }
  
  pose proof (EXH w1 W1 TR1) as EXH1. pose proof (EXH w2 W2 TR2) as EXH2.
  simpl in *. des; by_subst. 
Qed. 

Lemma fin_iter_struct thread index serving
      (Ew: E G (ThreadEvent thread index (Astore s (serving + 1)))):
  exists ticket counter fail_reads index0 index1 index2 index3,
    let c := (nth thread counters 0) in
    let events :=
        ThreadEvent thread index0 (Armw t ticket (ticket + 1)) ::
        fail_reads ++
        [ThreadEvent thread index1 (Aload s ticket);
        ThreadEvent thread index2 (Aload c counter);
        ThreadEvent thread (index2 + 1) (Astore c (counter + 1));
        ThreadEvent thread index3 (Aload s serving);
        ThreadEvent thread index (Astore s (serving + 1))]
    in
    ⟪STRUCT: iter_of (ThreadEvent thread index (Astore s (serving + 1))) = trace_fin events ⟫ /\
    ⟪FAIL_READS: forall e (IN_FAIL: In e fail_reads), exists thread index v,
        e = ThreadEvent thread index (Aload s v) /\ ticket <> v ⟫. 
Proof.
  remember (ThreadEvent thread index (Astore s (serving + 1))) as w.
  remember (nth thread counters 0) as c.
  assert (ticketlock_execution s t c (iter_of w)) as TL. 
  { subst c. replace thread with (tid w) by by_subst. 
    apply iter_lu. by_subst. }
  forward eapply (@fin_iter_struct' (iter_of w)); eauto. 
  { apply (@trace_finite_features (iter_of w) c); auto. 
    exists w. split; [| basic_solver]. 
    apply iter_self; by_subst. }
  ins. desc.

  forward eapply (@iter_w_unique (iter_of w) w (ThreadEvent thread0 (index3 + 1) (Astore s (serving0 + 1))) c) as W; try by_subst.
  { apply iter_self. by_subst. }
  { rewrite STRUCT. simpl. right. apply in_app_r. simpl. intuition. }
  { subst c. apply nth_In. replace thread with (tid w) by by_subst.
    rewrite CNT_CORR. by apply tid_bounded. }
    
  assert (thread0 = thread /\ serving0 = serving); [| desc; subst thread0 serving0].
  { split; [by_subst| ]. unfolder'. subst w. inversion W. lia. } 

  do 7 eexists. splits; vauto.
Qed.

Lemma write_s_exact w (W: (E G ∩₁ is_w ∩₁ Loc_ s ) w):
  is_init w \/
  exists thread index serving, 
    w = ThreadEvent thread index (Astore s (serving + 1)).
Proof.
  destruct w eqn:W_; [by_subst| rewrite <- W_ in *]. right.
  forward eapply (@iter_of_helper w); try by_subst. ins. desc.
  forward eapply (@iter_lu w) as TL; [by_subst| ]. 
  
  forward eapply (@trace_finite_features (iter_of w)) as ITER_FIN; eauto.
  { exists w. unfolder. splits; try by_subst.
    apply iter_self. by_subst. }
  eapply fin_iter_struct' in ITER_FIN; eauto. desc. simpl in ITER_FIN. desc.
  exists thread0. exists (index3 + 1). exists serving.
  eapply iter_w_unique; try by_subst.
  { apply iter_self. by_subst. }
  { rewrite STRUCT. simpl. right. apply in_app_r. intuition. }
  apply nth_In. rewrite CNT_CORR. apply BOUNDED_THREADS. by_subst. 
Qed. 


Lemma tid_disj e (Ee: E G e):
  nth (tid e) counters 0 <> s /\ nth (tid e) counters 0 <> t.
Proof.
  apply not_or_and. red. ins. 
  pose proof (tid_bounded _ Ee) as LT.
  red in CNT_DISJ. specialize (@CNT_DISJ (nth (tid e) counters 0)).
  specialize_full CNT_DISJ; [apply nth_In; congruence| | done].
  red. des; vauto.
Qed. 

Lemma write_t_exact w (W: (E G ∩₁ Loc_ t) w):
  is_init w \/
  exists thread index ticket, 
    w = ThreadEvent thread index (Armw t ticket (ticket + 1)).
Proof.
  destruct w eqn:W_; [by vauto| rewrite <- W_ in *]. right. 
  forward eapply (@iter_self w) as ITER; [by_subst| ].
  forward eapply (@iter_lu w) as TL; [by_subst| ].

  unfold_subtraces TL. desc. 
  rewrite APP in ITER. subst tr_acq tr_l tr_bw tr_ok tr_c tr_u.
  do 4 rewrite trace_in_app in ITER. des.
  { simpl in ITER. subst w. des; [| done]. eauto. }  
  { specialize (BW_FAIL _ ITER0). desc. subst w. inversion BW_FAIL. by_subst. }
  { simpl in ITER1. des; [| done]. subst w. inversion ITER1. by_subst. }
  { forward eapply (tid_disj w) as DISJ; [by_subst| ].
    simpl in ITER0. des; [| | done]; subst w; inversion ITER0; by_subst. }
  { simpl in ITER1. des; [| | done]; subst w; inversion ITER1; by_subst. }
Qed. 


Lemma writes_t_unique x y
      (X: (E G ∩₁ Loc_ t) x) (Y: (E G ∩₁ Loc_ t) y)
      (VALEQ: valw x = valw y):
  x = y.
Proof.
  generalize dependent x. generalize dependent y.  
  cut (forall v x y (X: (E G ∩₁ Loc_ t) x) (Y: (E G ∩₁ Loc_ t) y)
         (VALEQ: valw x = valw y) (Vx: valw x = v),
          x = y).
  { ins. eapply H; eauto. }

  contra NEQ_. apply not_all_ex_not in NEQ_.
  forward eapply (exists_min _ NEQ_) as [vx [NEQ MIN]]. clear NEQ_.
  apply not_all_ex_not in NEQ as [x NEQ]. apply not_all_ex_not in NEQ as [y NEQ].
  apply imply_to_and in NEQ as [X NEQ]. apply imply_to_and in NEQ as [Y NEQ].
  apply imply_to_and in NEQ as [VALEQ NEQ]. apply imply_to_and in NEQ as [Vx NEQ].

  unfolder in X. desc. forward eapply (@write_t_exact x) as X'; try by vauto. 
  unfolder in Y. desc. forward eapply (@write_t_exact y) as Y'; try by vauto.
  des.
  { destruct x, y; by_subst. }
  { destruct x, y; vauto. by_subst. }
  { destruct x; by_subst. }

  assert (ticket0 = ticket); [| subst ticket0].
  { subst x y. by_subst. }
  assert (vx = (ticket + 1)); try by_subst. subst vx. 

  specialize (MIN ticket). specialize_full MIN; [lia| ]. apply NNPP in MIN. 
  assert (exists wx, rf G wx x) as [wx RFx]; [eapply RFC; subst x; split; done| ]. 
  assert (exists wy, rf G wy y) as [wy RFy]; [eapply RFC; subst y; split; done| ]. 

  specialize (MIN wx wy). specialize_full MIN.
  1-3: eapply exploit_rf in RFx; eapply exploit_rf in RFy; try by_subst. 
  { transitivity (valr x); [by apply (wf_rfv WF)| by subst x]. }
  
  forward eapply (@wf_co_total _ WF t) with (a := x) (b := y) as TOT; try by vauto.

  (* pose proof rmw_atom as RMW_ATOM. red in RMW_ATOM. *)
  forward eapply rmw_atom as RMW_ATOM; eauto. 
  
  des.
  { specialize (RMW_ATOM wx y). specialize_full RMW_ATOM; [basic_solver| ].
    destruct RMW_ATOM. apply H1. exists x. split; auto.
    subst wy x. apply rf_co_helper; auto. }
  { specialize (RMW_ATOM wx x). specialize_full RMW_ATOM; [subst x; basic_solver| ]. 
    destruct RMW_ATOM. apply H1. exists y. split; auto. 
    apply rf_co_helper; vauto. }
Qed.


Lemma co_t_val_helper x y
      (X: (E G ∩₁ Loc_ t) x) (Y: (E G ∩₁ Loc_ t) y)
      (COxy: co G x y) (LEyx: valw y <= valw x):
  False.
Proof.
  apply Lt.le_lt_or_eq in LEyx as [LTyx | EQ].
  2: { forward eapply (@writes_t_unique x y) as EQ_; eauto. subst y.
       edestruct co_irr; eauto. }
       
  generalize dependent x. generalize dependent y. 
  cut (forall vx x y (X: (E G ∩₁ Loc_ t) x) (Y: (E G ∩₁ Loc_ t) y)
         (Vx: valw x = vx),
          ~ (co G x y /\ valw y < vx)).
  { ins. by apply (H (valw x) x y). }
  contra CONTRA_. apply not_all_ex_not in CONTRA_.
  forward eapply (exists_min _ CONTRA_) as [vx [CONTRA MIN]]. clear CONTRA_.
  apply not_all_ex_not in CONTRA as [x CONTRA]. apply not_all_ex_not in CONTRA as [y CONTRA]. 
  apply imply_to_and in CONTRA as [X CONTRA]. apply imply_to_and in CONTRA as [Y CONTRA].
  apply imply_to_and in CONTRA as [VALEQ CONTRA]. apply NNPP in CONTRA as [CO LE].
  
  unfolder in X. unfolder in Y. desc.   
  forward eapply (@write_t_exact y) as Y'; try by vauto. des. 
  { eapply wf_co_init; eauto. red. vauto. }
  forward eapply (@write_t_exact x) as X'; try by vauto. des.
  { destruct x; by_subst. }

  rewrite X' in VALEQ. unfold valw, valw_l in VALEQ. simpl in VALEQ. subst vx. 
  rewrite Y' in LE. unfold valw, valw_l in LE. simpl in LE.
  apply PeanoNat.Nat.add_lt_mono_r in LE. 
  specialize (MIN ticket0). specialize_full MIN; [lia| ]. apply NNPP in MIN.

  assert (exists wx, rf G wx x) as [wx RFx]; [eapply RFC; desc; subst x; split; done|].
  assert (exists wy, rf G wy y) as [wy RFy]; [eapply RFC; desc; subst y; split; done|].
  eapply exploit_rf in RFx; eauto. eapply exploit_rf in RFy; eauto. desc.
  rewrite X' in RFx5. rewrite Y' in RFy5.
  unfold valr, valr_l in RFx5. unfold valr, valr_l in RFy5.
  simpl in *. 
  specialize (MIN wx wy). specialize_full MIN; try by vauto.  
  
  apply not_and_or in MIN. des; [| by_subst]. 
  forward eapply (@wf_co_total _ WF t) with (a := wx) (b := wy) as TOT; try by vauto.
  { red. ins. by_subst. }
  des; [done| ].
  apply (@cycle_helper3 _ _ y wx x SCpL); try by basic_solver. 
  repeat right. red. split; auto.
  { exists wy. split; red; auto. }
  red. ins. red in H. desc.
  apply (@cycle_helper2 _ _ x y SCpL); basic_solver. 
Qed.

Lemma co_t_val:
  restr_rel (E G ∩₁ is_w ∩₁ Loc_ t) (co G) ≡
  restr_rel (E G ∩₁ is_w ∩₁ Loc_ t) valw_lt.
Proof.  
  apply restr_rel_exp_iff. ins.
  destruct (classic (x = y)).
  { subst. unfold valw_lt. split; [| lia].
    ins. edestruct co_irr; eauto. }
  assert (valw x < valw y \/ valw y < valw x) as VAL.
  { pose proof (NPeano.Nat.lt_trichotomy (valw x) (valw y)). des; try tauto.
    forward eapply (@writes_t_unique x y); by_subst. }
  forward eapply (wf_co_total WF) with (a := x) (b := y) as CO; eauto.
  des; [tauto| | | ]. 
  { edestruct (@co_t_val_helper x y); by_subst. }
  { edestruct (@co_t_val_helper y x); by_subst. }
  transitivity False; split; try tauto; ins.
  { eapply (co_acyclic WF). vauto. }
  { red in H0. lia. }
Qed.


Lemma writes_s_chain w v (W: (E G ∩₁ (fun a => is_w a) ∩₁ Loc_ s ∩₁ Valw_ v) w):
  forall v' (LT: v' < v),
  exists w',
    (E G ∩₁ (fun a => is_w a) ∩₁ Loc_ s ∩₁ Valw_ v') w' /\
    co G w' w. 
Proof.
  generalize dependent w. induction v using Wf_nat.lt_wf_ind. ins.
  destruct v; [lia| ]. 
  forward eapply write_s_exact as [| W_]; auto.
  { type_solver. }
  { destruct w; vauto. unfolder'. lia. }
  desc.
  assert (v = serving); [| subst v].
  {  subst w. unfolder'. lia. }
  forward eapply (@iter_lu w) as ITER; [by_subst| ].
  forward eapply (@iter_wf w) as TWF; [by_subst| ].
  forward eapply (@fin_iter_struct thread index serving); [by_subst| ]. ins. desc.
  remember (ThreadEvent thread index3 (Aload s serving)) as r_u.
  assert (exists w', rf G w' r_u) as [w' RF'].
  { apply RFC. split; [| by subst].
    eapply (@iter_exec w); [by_subst| ].
    rewrite W_, STRUCT. simpl. intuition. }
  assert (sb G r_u w) as SBrw. 
  { eapply exploit_rf in RF'; eauto. desc. red. apply seq_eqv_lr. splits; try by_subst. 
    red in TWF.
    assert (trace_nth (S (length fail_reads + 3)) (iter_of w) d_ = r_u) as I.
    { subst w. rewrite STRUCT. simpl.
      rewrite app_nth2, Minus.minus_plus; by_subst. }
    assert (trace_nth (S (length fail_reads + 4)) (iter_of w) d_ = w) as J.
    { subst w. rewrite STRUCT. simpl.
      rewrite app_nth2, Minus.minus_plus; by_subst. }
    specialize (TWF (S (length fail_reads + 3)) (S (length fail_reads + 4))) with (d := d_).  
    rewrite I, J in TWF. specialize_full TWF; [lia | |by_subst |].
    { rewrite W_, STRUCT. simpl. rewrite !app_length. simpl. lia. }
    destruct r_u, w; vauto. }
  assert (co G w' w) as COw'w.
  { forward eapply (@wf_co_total _ WF (loc w)) with (a := w) (b := w') as TOT; try by vauto.
    { type_solver. }
    { eapply exploit_rf in RF'; eauto. desc. vauto. }
    { red. ins. subst w'. red in SCpL. eapply cycle_helper2; eauto.
      { generalize RF'. basic_solver. }
      repeat left. split; vauto. }
    des; [| done]. exfalso. 
    red in SCpL.  eapply (@cycle_helper3 _ _ _ _ _ SCpL); try basic_solver. 
    repeat left. split; vauto. }

  assert ((E G ∩₁ is_w ∩₁ Loc_ s ∩₁ Valw_ serving) w') as W'_. 
  { eapply exploit_rf in RF'; eauto. desc. by_subst. }
  
  apply Lt.lt_le_S, Lt.le_lt_or_eq in LT. des.
  { apply Lt.lt_S_n in LT. specialize (H serving) with (w := w') (v' := v').
    specialize_full H; [lia | done | lia | ].
    desc. exists w'0. split; auto. eapply co_trans; eauto. }
  apply eq_add_S in LT. subst v'. eexists. split; eauto. 
Qed.

Lemma tl_nonempty tr c (TL: ticketlock_execution s t c tr):
  NOmega.lt_nat_l 0 (trace_length tr).
Proof. 
  unfold_subtraces TL. desc. 
  subst. rewrite <- trace_app_assoc, trace_length_app. simpl.
  destruct (trace_length _); simpl; lia. 
Qed.
  
Lemma rmw_of_tl_exact tr c (TL: ticketlock_execution s t c tr)
      (IN_E: trace_elems tr ⊆₁ E G):
  exists rmw, (E G ∩₁ is_rmw ∩₁ Loc_ t) rmw /\ trace_nth 0 tr d_ = rmw.
Proof.
  forward eapply (@tl_nonempty tr) as NE; eauto. 
  unfold_subtraces TL. desc.  
  remember (ThreadEvent thread1 index1 (Armw t ticket (ticket + 1))) as rmw.
  exists rmw.
  assert (trace_nth 0 tr d_ = rmw) as TR0.
  { subst tr tr_l tr_acq. rewrite trace_nth_app, emiT.
    2: { rewrite trace_length_app. simpl. omegaW (trace_length tr_bw). }
    rewrite trace_nth_app, emiT; by_subst. }
    
  split; auto.
  unfolder. splits; try by_subst. apply IN_E.
  rewrite <- TR0. by apply trace_nth_in. 
Qed. 

Lemma rmw_of_tl tr c (TL: ticketlock_execution s t c tr)
      (IN_E: trace_elems tr ⊆₁ E G):
  exists rmw, (E G ∩₁ is_rmw ∩₁ Loc_ t) rmw /\ trace_elems tr rmw.
Proof.
  forward eapply rmw_of_tl_exact; vauto. ins. desc. exists rmw. split; auto.
  rewrite <- H0. apply trace_nth_in.
  eapply tl_nonempty; eauto.
Qed.
  
Lemma rmw_of_event e (Ee: (E G \₁ is_init) e):
  exists rmw, (E G ∩₁ is_rmw ∩₁ Loc_ t) rmw /\ trace_elems (iter_of e) rmw.
Proof.
  apply (@rmw_of_tl (@iter_of e) (nth (tid e) counters 0));
    [by apply iter_lu | by apply iter_exec]. 
Qed. 

Lemma co_s_rmw_helper serving thread index
      (IH: forall m,
          m < S serving ->
          forall w_,
            (E G ∩₁ is_w ∩₁ Loc_ s ∩₁ Valw_ m) w_ ->
            (E G ∩₁ is_w ∩₁ Loc_ s) ∩₁ (fun w' => co G w' w_) ≡₁
            (E G ∩₁ is_w ∩₁ Loc_ s) ∩₁ (fun w' => valw w' < m) /\
            (forall rmw, is_rmw rmw -> trace_elems (iter_of w_) rmw -> valw rmw = m)):
  let w := ThreadEvent thread index (Astore s (serving + 1)) in
  E G w -> 
  forall rmw (RMW: is_rmw rmw) (TRrmw: trace_elems (iter_of w) rmw),
    valw rmw = S serving. 
Proof.
  remember (ThreadEvent thread index (Astore s (serving + 1))) as w. simpl.
  intros Ew. ins.
  remember (iter_of w) as iter_w. 
  forward eapply (@iter_lu w) as TL; [by vauto| ].
  forward eapply (@iter_self w) as ITER; [by vauto| ].
  forward eapply (@iter_wf w) as ITER_WF; [by vauto| ].
  rewrite <- Heqiter_w in *.  
  forward eapply fin_iter_struct; try by vauto. ins. desc. 
  
  rewrite Heqiter_w, Heqw, STRUCT in TRrmw. simpl in TRrmw.
  rewrite in_app_iff in TRrmw. simpl in TRrmw. des; try type_solver.
  2: { specialize (FAIL_READS _ TRrmw). desc. type_solver. }

  rewrite <- TRrmw. unfold valw, valw_l. simpl. cut (serving = ticket); [lia| ]. 
  
  pose proof (NPeano.Nat.lt_trichotomy serving ticket). des; [ | done | ].
  { remember (ThreadEvent thread index1 (Aload s ticket)) as r_ok. 
    assert (exists w', rf G w' r_ok) as [w' RF'].
    { apply RFC. split; [| by subst].
      eapply (@iter_exec w); [by vauto| ]. 
      rewrite Heqw, STRUCT. simpl. intuition. }
    remember (ThreadEvent thread index3 (Aload s serving)) as r_u.
    assert (exists w'', rf G w'' r_u) as [w'' RF''].
    { apply RFC. split; [| by subst]. 
      eapply (@iter_exec w); [by vauto| ]. 
      rewrite Heqw, STRUCT. simpl. intuition. }
    remember (ThreadEvent thread index2 (Aload (nth thread counters 0) counter)) as r_c.
    remember (ThreadEvent thread (index2 + 1) (Astore (nth thread counters 0) (counter + 1))) as w_c. 
    assert (sb G r_ok r_u) as SB.
    { red. eapply exploit_rf in RF'; eauto. eapply exploit_rf in RF''; eauto.
      desc. apply seq_eqv_lr. splits; auto.
      eapply (trace_wf_app_sb (trace_fin [r_ok]) (trace_fin [r_c; w_c; r_u; w])); try by vauto.
      2: { simpl. tauto. }
      move ITER_WF at bottom. rewrite Heqiter_w, Heqw, STRUCT in ITER_WF.
      simpl in ITER_WF. rewrite <- Heqw in ITER_WF. 
      apply trace_wf_fin_app with (l1 := rmw :: fail_reads). vauto. }
    forward eapply sb_rf_co as CO; eauto; [by subst| ].
    red in CO. des.
    { apply (wf_rfv WF) in RF'. apply (wf_rfv WF) in RF''. by_subst. }
    specialize (IH serving) with (w_ := w''). specialize_full IH; [lia| | ].
    { eapply exploit_rf in RF''; eauto. by_subst. }
    destruct IH as [[CO_ _] _].

    specialize (CO_ w'). specialize_full CO_.
    { eapply exploit_rf in RF'; eauto. desc. splits; vauto. }
    destruct CO_ as [_ CO_]. 
    
    eapply exploit_rf in RF'; eauto. desc. subst. unfolder'. lia. }
  { assert (exists w', (E G ∩₁ is_w ∩₁ Loc_ s ∩₁ Valw_ (ticket + 1)) w') as [w' W']. 
    { forward eapply (@writes_s_chain w (serving + 1)) with (v' := ticket + 1)
        as [w' W'_]; eauto; [by_subst| lia | by_subst]. }
    assert ((E G \₁ is_init) w') as ENIw'.
    { unfolder'. desc. split; auto. destruct w'; lia. }

    specialize (IH (ticket + 1)) with (w_ := w'). specialize_full IH; [lia| done | ].
    desc.

    forward eapply (@rmw_of_event w') as [rmw' [RMW' WITH_W']]; [by_subst| ]. 
    
    specialize (IH0 rmw'). specialize_full IH0; try by_subst.
    assert (rmw' = rmw); [| subst rmw'].
    { apply writes_t_unique; try by_subst.
      unfolder. splits; try by by_subst. eapply (@iter_exec w); vauto. 
      rewrite STRUCT. vauto. }
    
    forward eapply (@iter_disj w w') as [DISJ _]; try by vauto.
    { intros SAME_ITER.
      cut (w = w'); [ins; by_subst| ].
      eapply (@iter_w_unique (@iter_of w)); try by_subst.
      { rewrite SAME_ITER. by apply iter_self. }
      apply nth_In. rewrite CNT_CORR. apply BOUNDED_THREADS. by_subst. } 
    edestruct (DISJ rmw); vauto. rewrite STRUCT. vauto. }
Qed.


Lemma writes_unique_bounded v v' x y (S: Event -> Prop)
      (IH: forall w (LT: valw w < v)
             (Sw: S w), 
          S ∩₁ (fun w' => co G w' w) ≡₁ S ∩₁ (fun w' => valw w' < valw w))
      (S_WRITES: exists l, S ⊆₁ E G ∩₁ is_w ∩₁ Loc_ l)
      (Sx: S x) (Sy: S y)
      (VALx: valw x = v') (VALy: valw y = v') (BOUND: v' < v):
  x = y.
Proof.
  contra NEQ. desc. 
  forward eapply (wf_co_total WF) with (a := x) (b := y) as CO; eauto.
  subst. des.
  { specialize (IH y). specialize_full IH; [lia | auto| ].
    destruct IH as [IH _ ]. 
    specialize (IH x). specialize_full IH; [vauto| ].
    unfolder in IH. lia. }
  { specialize (IH x BOUND Sx) as [IH _].
    specialize (IH y). specialize_full IH; [vauto| ].
    unfolder in IH. lia. }
Qed.

Lemma co_s_helper v w (W: (E G ∩₁ is_w ∩₁ Loc_ s ∩₁ Valw_ v) w):
  (E G ∩₁ is_w ∩₁ Loc_ s) ∩₁ (fun w' => co G w' w) ≡₁
  (E G ∩₁ is_w ∩₁ Loc_ s) ∩₁ (fun w' => valw w' < v) /\
  forall rmw (RMW: is_rmw rmw) (CORR: trace_elems (iter_of w) rmw), valw rmw = v. 
Proof.

  generalize dependent w. induction v as [ v IHv] using Wf_nat.lt_wf_ind. ins.
  forward eapply (@write_s_exact w) as W_; [generalize W; basic_solver| ]. 
  
  destruct v.  
  { des; [| subst w; unfolder'; desc; lia]. 
    destruct w; vauto. rewrite iter_init. simpl. split; [| done].
    split; [| unfolder; lia].
    unfolder. ins. desc. 
    apply co_ninit, seq_eqv_r in H0; eauto. desc. red in H3. by desc. }
  des.
  { destruct w; vauto. unfolder'. desc. lia. }
  assert (v = serving); [| subst v].
  { subst w. unfolder'. desc. lia. }
  
  assert (forall rmw (RMW: is_rmw rmw) (TR: trace_elems (iter_of w) rmw),
             valw rmw = S serving) as RMW_CORR.
  { ins. subst w. eapply co_s_rmw_helper; by_subst. }
  split; auto.
  
  contra NEQ. apply set_nequiv_diff in NEQ. destruct NEQ as [w_ NEQ]. des.
  { red in NEQ0. desc.
    unfold set_inter in NEQ at 1. apply not_and_or in NEQ. des; [done| ].
    forward eapply (wf_co_total WF) with (a := w) (b := w_) as CO; try by_subst. 
    { red. ins. subst w w_. unfold valw, valw_l in NEQ1. simpl in NEQ1. lia. }
    des; [| done].
    forward eapply (@writes_s_chain w) with (v' := serving) as [w' [W' CO']]; try by vauto. 
    apply Lt.lt_n_Sm_le, Lt.le_lt_or_eq in NEQ1. des.
    2: { forward eapply (writes_unique_bounded) with (v := S serving) (v' := serving) (x := w') (y := w_) (S := E G ∩₁ is_w ∩₁ Loc_ s);
         try by_subst. 
         { ins. specialize (IHv (valw w0) LT w0). specialize_full IHv; by_subst. }
         ins. destruct (co_irr WF w); eauto. congruence. }
    specialize (IHv serving) with (w := w'). specialize_full IHv; try by_subst.
    destruct IHv as [[_ IHv] _]. 
    specialize (IHv w_). specialize_full IHv; [by_subst| ].
    red in IHv. desc.
    eapply cycle_helper3; eauto; basic_solver. }
  { red in NEQ. desc. 
    unfold set_inter in NEQ0 at 1. apply not_and_or in NEQ0. des; [done| ]. 
    apply PeanoNat.Nat.nlt_ge in NEQ0.
    assert (exists w', valw w' = S serving /\ co G w' w) as [w' [VAL' CO']].
    { apply Lt.le_lt_or_eq in NEQ0. des; [| by vauto].
      forward apply (@writes_s_chain w_ (valw w_)); try by_subst.
      ins. desc. exists w'. split; [by_subst| ].
      eapply co_trans; eauto. }
    assert (forall rmw (RMW: is_rmw rmw) (TR: trace_elems (iter_of w') rmw),
               valw rmw = S serving) as RMW_CORR'.
    { ins. eapply exploit_co in CO'; eauto. desc. 
      forward eapply (@write_s_exact w'); try by_subst. ins. des; [by destruct w' | ].
      assert (serving0 = serving); [subst w'; unfolder'; lia | subst serving0].
      rewrite H in CO'0. eapply co_s_rmw_helper; eauto. congruence. }

    forward eapply (@rmw_of_event w) as [rmw [RMW WITH_W]]; [by_subst| ]. 
    forward eapply (@rmw_of_event w') as [rmw' [RMW' WITH_W']].
    { eapply exploit_co in CO'; eauto. desc. split; auto. destruct w'; vauto. }
    forward eapply (@writes_t_unique rmw rmw'); try by_subst.
    { rewrite RMW_CORR, RMW_CORR'; by_subst. }
    ins. subst rmw'.
    
    apply exploit_co in CO'; auto. 
    forward eapply (@iter_disj w w') as [DISJ _]; try by_subst.
    { destruct w'; by_subst. }
    { intros SAME_ITER.
      cut (w = w').
      { intros. subst w'. desc. eapply co_irr; eauto. }
      eapply (@iter_w_unique (@iter_of w)); try by_subst.
      { apply iter_lu. by_subst. }
      { apply iter_self. by_subst. }
      { rewrite SAME_ITER. apply iter_self. destruct w'; by_subst. }
      apply nth_In. rewrite CNT_CORR. apply BOUNDED_THREADS. exists w. by_subst. } 
    edestruct (DISJ rmw); vauto. }    
Qed.

Lemma writes_s_unique x y 
      (X: (E G ∩₁ is_w ∩₁ Loc_ s) x) (Y: (E G ∩₁ is_w ∩₁ Loc_ s) y)
      (VALEQ: valw x = valw y):
  x = y.
Proof.
  contra NEQ. 
  forward eapply (wf_co_total WF) with (a := x) (b := y) as CO; eauto.
  des. 
  { forward eapply (@co_s_helper (valw y) y) as [[IMPL _] _]; [done| ].
    specialize (IMPL x). specialize_full IMPL; [by_subst| ].
    unfolder in IMPL. lia. }
  { forward eapply (@co_s_helper (valw x) x) as [[IMPL _] _]; [done| ].
    specialize (IMPL y). specialize_full IMPL; [by_subst| ].
    unfolder in IMPL. lia. }
Qed.

Lemma co_s_val:
  restr_rel (E G ∩₁ is_w ∩₁ Loc_ s) (co G) ≡
  restr_rel (E G ∩₁ is_w ∩₁ Loc_ s) valw_lt.
Proof.
  apply restr_rel_exp_iff. ins.
  destruct (classic (x = y)).
  { subst. unfold valw_lt. split; [| lia].
    ins. edestruct co_irr; eauto. }
  assert (valw x < valw y \/ valw y < valw x) as VAL.
  { pose proof (NPeano.Nat.lt_trichotomy (valw x) (valw y)). des; try tauto.
    forward eapply (@writes_s_unique x y); vauto. }
  des. 
  { split; auto. ins.
    forward eapply (@co_s_helper (valw y) y) as [[_ IMPL] _]; [done| ].
    specialize (IMPL x). specialize_full IMPL; by_subst. }
  { transitivity False; split; try tauto; [| unfold valw_lt; lia].
    ins. forward eapply (@co_s_helper (valw x) x) as [[_ IMPL] _]; [done| ].
    specialize (IMPL y). specialize_full IMPL; [by_subst| ].
    unfolder in IMPL. desc. eapply (co_acyclic WF). vauto. }
Qed. 


Lemma w_rmw_corr w rmw
      (W: (E G ∩₁ is_w ∩₁ Loc_ s) w)
      (RMW: (E G ∩₁ Loc_ t) rmw) (NINIT: ~ is_init rmw)
      (VALEQ: valw w = valw rmw):
  iter_of w = iter_of rmw.
Proof.
  apply iter_corr; try by_subst.
  { split; [by_subst| ]. destruct w; [| done].
    forward eapply (@write_t_exact rmw); [by_subst| ]. ins. des; [done| ].
    subst rmw. unfolder'. lia. }
  
  forward eapply write_t_exact as [| RMW_]; eauto; [done| ]. desc.  
  forward eapply (@write_s_exact w) as [| W_]; try by_subst. 
  { destruct w; [| done]. subst rmw. unfolder'. lia. }
  desc. forward eapply (fin_iter_struct thread0 index0 serving); [by_subst| ].
  rewrite <- W_ in *. ins. desc.
  assert (serving = ticket); [| subst serving].
  { subst w rmw. unfolder'. lia. }

  remember (ThreadEvent thread0 index1 (Armw t ticket0 (ticket0 + 1))) as rmw'.
  cut (rmw' = rmw); [rewrite STRUCT; by vauto| ]. 
  assert (trace_elems (iter_of w) rmw') as TR' by (rewrite STRUCT; vauto). 
  apply writes_t_unique; [| by_subst | ].
  { split; [| by vauto]. apply (@iter_exec w); by_subst. }
  forward eapply (@co_s_helper (ticket + 1) w) as [_ RMW_CORR]; [by_subst| ].
  rewrite RMW_CORR; by_subst. 
Qed.

  

Lemma UNIQUE_HELPER i (S: Event -> Prop)
      (UNIQUE: forall x y (Sx: S x) (Sy: S y) (VALEQ: valw x = valw y), x = y):
  set_finite (S ∩₁ Valw_ i).
Proof. 
  ins. destruct (classic (S ∩₁ Valw_ i ≡₁ ∅)) as [| NEMPTY].
  { rewrite H. apply set_finite_empty. }
  apply set_nonemptyE in NEMPTY. desc. exists [x].
  ins. left. apply UNIQUE; by_subst. 
Qed. 

Lemma valw_bounded_fin v (S: Event -> Prop)
      (UNIQUE: forall x y (Sx: S x) (Sy: S y) (VALEQ: valw x = valw y), x = y):
  set_finite (S ∩₁ (fun e => valw e < v)).
Proof.
  arewrite ((fun e => valw e < v) ⊆₁ (⋃₁ i < v, Valw_ i)).
  { red. ins. red. eauto. }
  rewrite <- !set_bunion_inter_compat_l. apply set_finite_bunion; [apply set_finite_lt| ].  
  ins. by apply UNIQUE_HELPER.
Qed. 

Lemma writes_bounded_fin v:
  set_finite (E G ∩₁ is_w ∩₁ Locs_ [s; t] ∩₁ (fun e => valw e < v)).
Proof.
  arewrite (Locs_ [s; t] ⊆₁ Loc_ s ∪₁ Loc_ t) by basic_solver.
  rewrite !set_inter_union_r, set_inter_union_l.
  apply set_finite_unionI; apply valw_bounded_fin; ins;
    [apply writes_s_unique | apply writes_t_unique]; by_subst.
Qed.
  
Lemma inf_iter_struct tr c (TL: ticketlock_execution s t c tr)
      (INF: ~ trace_finite tr):
  exists thread index ticket f_fail,
    ⟪STRUCT: tr = trace_app (trace_fin [ThreadEvent thread index (Armw t ticket (ticket + 1))]) (trace_inf f_fail) ⟫ /\
    ⟪FAIL_READS: forall i, exists thread index v,
        f_fail i = ThreadEvent thread index (Aload s v) /\ v <> ticket ⟫. 
Proof.
  unfold_subtraces TL. desc.

  Ltac inf_app_helper app inf :=
    rewrite app in inf; apply (not_iff_compat (trace_app_finite _  _ )) in inf;
    apply not_and_or in inf; des; try by (edestruct inf; vauto).
  inf_app_helper APP INF. inf_app_helper APP0 INF. inf_app_helper BW_APP INF.

  destruct tr_fail; [by edestruct INF; vauto| ].
  exists thread1. exists index1. exists ticket. exists fl. splits; [by subst| ]. 
  ins. specialize (BW_FAIL (fl i)). specialize_full BW_FAIL; [by vauto| ].
  desc. eauto.
Qed.

Lemma iter_rmw_unique tr rmw1 rmw2 c (TL: ticketlock_execution s t c tr)
      (RMW1: (Loc_ t ∩₁ is_w) rmw1) (RMW2: (Loc_ t ∩₁ is_w) rmw2)
      (TR1: trace_elems tr rmw1) (TR2: trace_elems tr rmw2)
      (CNT: In c counters):
  rmw1 = rmw2.
Proof. eapply iter_w_unique; by_subst. Qed. 

Lemma bounded_values' rmw ticket
      (RMW: (E G ∩₁ Loc_ t ∩₁ Valw_ (ticket + 1)) rmw)
      (INF : ~ trace_finite (iter_of rmw)):
  E G ∩₁ is_w ∩₁ Loc_ s ⊆₁ (fun e => valw e < ticket + 1).
Proof.
  forward eapply (@write_t_exact rmw); [by_subst| ]. ins. des.
  { unfolder'. destruct rmw; [lia | vauto]. }  
  remember (iter_of rmw) as tr.

  forward eapply (@inf_iter_struct tr); try by vauto. 
  { rewrite Heqtr. apply iter_lu. by_subst. }
  intros. desc.
  forward eapply (@iter_rmw_unique tr rmw (ThreadEvent thread0 index0 (Armw t ticket1 (ticket1 + 1)))); try by_subst.
  { rewrite Heqtr. apply iter_lu. by_subst. }
  { rewrite Heqtr. apply iter_self. by_subst. }
  { rewrite STRUCT. simpl. exists 0. vauto. }
  {apply nth_In. rewrite CNT_CORR. apply tid_bounded. by_subst. }
  intros. rewrite H in H0. inversion H0. subst thread0 index0 ticket1. clear H5.
  assert (ticket0 = ticket); [by_subst| subst ticket0].
    
  red. intros w' W'.
  contra LE. apply Compare_dec.not_lt in LE. red in LE.
  assert (exists w, (E G ∩₁ is_w ∩₁ Loc_ s ∩₁ Valw_ (ticket + 1)) w) as [w W].
  { apply Lt.le_lt_or_eq in LE. des; [| exists w'; by_subst]. 
    forward eapply (@writes_s_chain w' (valw w')) with (v' := ticket + 1)
      as [w [W _]]; by_subst. }
  forward eapply (@w_rmw_corr w rmw) as SAME_ITER; try by_subst.
  
  assert (trace_elems (iter_of w) w) as TRw. 
  { apply iter_self. destruct w; by_subst. }
  forward eapply (@write_s_exact w) as W_; [by_subst| ]. intros. des.
  { unfolder'. destruct w; lia. }
  rewrite SAME_ITER, <- Heqtr, STRUCT in TRw.
  apply trace_in_app in TRw. des; try by_subst.
  simpl in TRw0. desc. specialize (FAIL_READS n). desc.
  congruence. 
Qed.

Lemma tl_ninit tr c (TL: ticketlock_execution s t c tr):
  trace_elems tr ⊆₁ set_compl is_init.
Proof.
  destruct (classic (trace_finite tr)).
  { forward eapply fin_iter_struct'; eauto. ins. desc.
    subst. simpl. red. ins.
    des; [by_subst| ]. apply in_app_iff in H0. des; [| by_subst].
    apply FAIL_READS in H0. by_subst. }
  forward eapply inf_iter_struct; eauto. intros. desc.
  subst. rewrite trace_elems_app, emiT; [| by_subst].
  apply set_subset_union_l. split; [basic_solver| ].
  red. ins. desc. specialize (FAIL_READS n). desc. by rewrite H0, FAIL_READS.
Qed. 

Lemma iter_eni e (ENIe: (E G \₁ is_init) e):
  trace_elems (iter_of e) ⊆₁ E G \₁ is_init.
Proof.
  rewrite set_minusE. apply set_subset_inter_r.
  split; [by apply iter_exec | by eapply tl_ninit, iter_lu].
Qed. 

Lemma inf_tr_read_latest e
      (ENI: (E G \₁ is_init) e)
      (INF : ~ trace_finite (iter_of e)):
  exists i,    
  forall j w (LE: i <= j),
    let r := (trace_nth j (iter_of e) w) in
    Loc_ s r /\ rf G w r
    -> mo_max G w.
Proof.
  remember (iter_of e) as tr. 
  forward eapply (@iter_lu e) as LU; [done| ].
  unfold_subtraces LU. desc.
  assert (trace_finite tr_acq) as FIN_ACQ by by_subst.
  assert (trace_nodup tr) as NODUP; [by subst; apply trace_wf_nodup, iter_wf| ].
  
  forward eapply (inf_reads_latest tr G [s]); try by done.
  { red. intros FIN. 
    cut (trace_finite tr_fail).
    { intros FINtr. red in FINtr. desc.
      rewrite Heqtr, APP in INF. subst. simpl in INF.
      apply INF. red. eauto. }

    apply nodup_trace_elems. 
    { apply trace_wf_nodup. forward eapply (@iter_wf e) as WFtr; [done| ]. 
      rewrite APP in WFtr. subst.
      by apply trace_wf_app, trace_wf_fin_app, trace_wf_app in WFtr. }
    rewrite Heqtr, APP, APP0, BW_APP, <- trace_app_assoc in FIN. 
    rewrite trace_elems_app, !set_inter_union_l in FIN.
    apply set_finite_union in FIN as [_ FIN]. rewrite emiT in FIN; [| by_subst].
    do 2 (rewrite trace_elems_app, !set_inter_union_l in FIN). 
    do 2 (apply set_finite_union in FIN as [FIN _]). 
    rewrite set_interA, set_inter_absorb_r in FIN; [done| ]. 
    red. ins. specialize (BW_FAIL _ H). by_subst. }
  { exists (length counters). ins. rewrite CNT_CORR. by apply tid_bounded. }
  { transitivity (trace_elems tr); [basic_solver| ].
    subst. apply (iter_exec); eauto. }
  { eapply set_finite_mori; [| apply (writes_bounded_fin (ticket + 1))].
    red. transitivity (E G ∩₁ is_w ∩₁ Locs_ [s] ∩₁ (fun e => valw e < ticket + 1)); [| basic_solver].
    apply set_subset_inter_r. split; auto.
    arewrite (Locs_ [s] ⊆₁ Loc_ s) by basic_solver.
    remember (ThreadEvent thread1 index1 (Armw t ticket (ticket + 1))) as rmw.
    assert (trace_elems (iter_of e) rmw) as ITERrmw.
    { subst. rewrite APP, <- !trace_app_assoc. apply trace_in_app. vauto. }
    assert ((E G \₁ is_init) rmw) as ENIrmw.
    { split; [| by_subst]. eapply (@iter_exec e); vauto. }
    apply (@bounded_values' rmw); [by_subst| ]. 
    forward eapply (@iter_corr rmw e) as [ITER_EQ _]; try by_subst.
    rewrite <- ITER_EQ; vauto. }
  ins. desc. exists i. ins. desc. eapply H; eauto. 
Qed. 
  
Lemma no_inf_iter e (ENIe: (E G \₁ is_init) e):
  trace_finite (iter_of e).
Proof.
  remember (valw (trace_nth 0 (iter_of e) d_)) as v.
  generalize dependent e. generalize dependent v.
  contra INF_. apply not_all_ex_not in INF_.
  forward eapply (exists_min _ INF_) as [ticket [INF MIN]]. clear INF_.
  apply not_all_ex_not in INF as [e INF]. apply imply_to_and in INF as [ENI INF]. 
  apply imply_to_and in INF as [VAL INF].

  remember (trace_nth 0 (iter_of e) d_) as rmw.
  assert (trace_elems (iter_of e) rmw) as ITERrmw.
  { subst rmw. apply trace_nth_in.
    destruct (iter_of e); [| done]. destruct l; [| by_subst].
    destruct INF. vauto. }
  forward eapply (@iter_eni e) with (x := rmw) as ENIrmw; try by_subst.  
  assert (iter_of e = iter_of rmw) as SAME_ITER by (apply iter_corr; by_subst). 
  forward eapply (@iter_lu rmw) as TL; try by_subst. 
  remember (iter_of rmw) as tr.
  forward eapply (@inf_iter_struct tr); try by vauto.
  { congruence. }
  intros. desc.
  assert (rmw = ThreadEvent thread index (Armw t ticket0 (ticket0 + 1))) as RMW_.
  { rewrite SAME_ITER, STRUCT, trace_nth_app, emiT in Heqrmw; by_subst. }
  move RMW_ at top. 
  assert (ticket = ticket0 + 1) by by_subst. 
  subst ticket. rename ticket0 into ticket. clear H. 
    
  forward eapply (@inf_tr_read_latest rmw) as [i READ_LATEST]; try by_subst.
  { congruence. }
  set (r := f_fail i).
  assert ((E G ∩₁ is_r ∩₁ Loc_ s) r) as R.
  { subst r. specialize (FAIL_READS i). desc.
    unfolder. splits; try by (rewrite FAIL_READS; vauto).
    eapply (@iter_exec rmw); try by_subst. rewrite <- Heqtr, STRUCT.
    apply trace_in_app. right. split; vauto. }
  
  assert (exists w, rf G w r) as [w RF] by (apply RFC; by_subst).
  specialize (READ_LATEST (i + 1) w). specialize_full READ_LATEST; [lia| | ].
  { rewrite <- Heqtr, STRUCT, <- RMW_. simpl.
    replace (i + 1) with (length [rmw] + i); [| simpl; lia].
    rewrite trace_prepend_snd. by_subst. }

  cut (valw w = ticket).
  { ins.
    specialize (FAIL_READS i). desc.
    apply (wf_rfv WF) in RF. subst r. rewrite FAIL_READS in RF. unfolder'. lia. }

  pose proof (PeanoNat.Nat.lt_trichotomy (valw w) ticket) as LT.
  des; [| done| ]; exfalso.
  2: { forward eapply (@bounded_values' rmw ticket) as BOUND; try by_subst.
       { congruence. }
       specialize (BOUND w). specialize_full BOUND; [| lia]. 
       apply exploit_rf in RF; auto. desc. 
       unfolder. splits; by_subst. }
  
  assert (exists rmw', rf G rmw' rmw) as [rmw' RF']; [apply RFC; by_subst| ].    
  forward eapply (@write_t_exact rmw') as RMW'_.
  { apply exploit_rf in RF'; auto. by_subst. }      
  destruct ticket as [| ticket]; [lia| ]. 
  des.
  { destruct rmw'; [| done]. subst rmw. apply exploit_rf in RF'; auto.
    unfolder'. lia. }
  assert ((E G \₁ is_init) rmw') as ENI'.
  { apply exploit_rf in RF'; by_subst. }
  
  assert (ticket0 = ticket); [| subst ticket0].
  { apply exploit_rf in RF'; auto. subst. unfolder'. lia. }
  
  specialize (MIN (ticket + 1)). specialize_full MIN; [by_subst| ].
  apply NNPP in MIN. specialize (MIN rmw'). specialize_full MIN; try by_subst.
  { forward eapply (@iter_lu rmw') as TL'; [by_subst| ]. 
    forward eapply (@rmw_of_tl_exact (iter_of rmw') (nth thread0 counters 0));
      [by_subst| by apply iter_exec| ]. 
    ins. desc.
    cut (rmw' = rmw0); [ins; subst rmw0; rewrite <- H1; by_subst| ].
    eapply (@iter_rmw_unique (iter_of rmw')); try by_subst.
    { type_solver. }
    { by apply iter_self. }
    { rewrite <- H0. apply trace_nth_in.
      destruct (iter_of rmw'); [| done]. destruct l; by_subst. }
    { apply nth_In. rewrite CNT_CORR. apply BOUNDED_THREADS. exists rmw'. by_subst. }
  }
  
  assert (ticketlock_execution s t (nth (tid rmw') counters 0)
                               (iter_of rmw')) as TL'. 
  { apply exploit_rf in RF'; auto. apply iter_lu; try by_subst. }
  forward eapply (@fin_iter_struct' (iter_of rmw')); eauto. ins. desc.
  assert (ticket0 = ticket); [| subst ticket0].
  { cut (rmw' = ThreadEvent thread1 index1 (Armw t ticket0 (ticket0 + 1))).
    { ins. subst. inversion H. lia. }
    eapply (@iter_rmw_unique (iter_of rmw') rmw'); try by_subst.
    { by apply iter_self. }
    rewrite STRUCT0. simpl. vauto.
    apply nth_In. replace thread0 with (tid rmw') by by_subst.
    rewrite CNT_CORR. apply BOUNDED_THREADS. by_subst. }
  
  remember (ThreadEvent thread1 (index4 + 1) (Astore s (serving + 1))) as w'.
  assert (E G w'). 
  { apply (@iter_exec rmw'); try by_subst.
    rewrite STRUCT0. simpl.
    right. apply in_app_r. simpl. tauto. }
  cut (serving = ticket).
  { ins. subst serving.
    red in READ_LATEST. desc. red in READ_LATEST0.
    apply (READ_LATEST0 w'). red. splits; try by_subst.
    { cut (restr_rel (E G ∩₁ is_w ∩₁ Loc_ s) (co G) w w'); [basic_solver| ].
      apply co_s_val. red. splits; try by_subst. 
      { red. subst w'. unfold valw at 2, valw_l at 1. simpl. lia. }
      { apply exploit_rf in RF; auto. unfolder'. basic_solver. }
    }
  }
  
  forward eapply (@co_s_helper (serving + 1) w') as [_ CORR]; [by_subst| ].
  specialize (CORR rmw'). specialize_full CORR; try by_subst.
  replace (iter_of w') with (iter_of rmw'); [by apply iter_self| ].
  apply iter_corr; try by_subst.
  rewrite STRUCT0. simpl.
  right. apply in_app_r. simpl. tauto. 
Qed. 

Lemma events_loc e (ENI: (E G \₁ is_init) e):
  Locs_ ([s; t; nth (tid e) counters 0]) e.
Proof. 
  destruct e eqn:E_; [by_subst| ]. rewrite <- E_.
  remember (iter_of e) as tr.
  forward eapply (@iter_lu e) as LU; try by_subst.
  forward eapply (@iter_self e) as ITER; try by_subst.
  assert (In (nth thread counters 0) counters) as CNT.
  { apply nth_In.
    replace thread with (tid e) by by_subst.
    rewrite CNT_CORR. apply tid_bounded. by_subst. }

  destruct (classic (trace_finite tr)).
  { forward eapply (@fin_iter_struct' tr); try by_subst. ins. desc.
    assert (tid e = thread0); [| subst thread0].
    { forward eapply (@iter_thread e) as INCL; try by_subst.
      specialize (INCL (ThreadEvent thread0 index0 (Armw t ticket (ticket + 1)))).
      specialize_full INCL; try by_subst.
      rewrite <- Heqtr, STRUCT. simpl. intuition. }

    rewrite <- Heqtr, STRUCT in ITER. move ITER at bottom.
    simpl in ITER. rewrite in_app_iff in ITER. simpl in ITER.
    des; try by_subst.
    { specialize (FAIL_READS _ ITER). desc. by_subst. }
    1,2: subst e; rewrite <- ITER; unfolder'; by_subst. }
  { forward eapply (@inf_iter_struct tr); try by_subst. intros. desc.
    rewrite <- Heqtr, STRUCT in ITER. move ITER at bottom.
    apply trace_in_app in ITER. des; try by_subst.
    simpl in ITER0. desc.
    specialize (FAIL_READS n). specialize_full FAIL_READS; try by_subst.
    cut (loc e = s); [by_subst| ].
    desc. rewrite ITER0, FAIL_READS. by_subst. }
Qed.
 
Lemma counters_separated thread (CNT: thread < length counters)
      (NINIT: thread <> 0):
  E G ∩₁ Loc_ (nth thread counters 0) \₁ is_init  ⊆₁ Tid_ thread.
Proof.
  red. intros e [LOCe NINITe].
  destruct e eqn:E_; [by_subst| ]. simpl.

  forward eapply (@events_loc e) as LOCS; [by_subst| ]. 
  assert (loc e = nth thread counters 0) as LOC by by_subst. 
  simpl in LOCS. des; try done.
  1, 2: destruct (@CNT_DISJ (loc e)); [rewrite LOC; by apply nth_In| by_subst]. 

  rewrite LOC in LOCS. apply NoDup_nth in LOCS; try by_subst. 
  rewrite CNT_CORR. apply tid_bounded. by_subst.
Qed. 
  

Lemma c_writes_order thread (CNT: thread < length counters) (NINIT: thread <> 0):
  strict_total_order (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0)) (sb G).
Proof.
  red. split; [by red; auto using sb_irr, sb_trans| ].
  red. ins.
  destruct a eqn:A, b eqn:B; [by_subst|left |right | ];
    try (red; apply seq_eqv_lr; by_subst).
  rewrite <- A, <- B in *. 
  forward eapply (@counters_separated thread) with (x := a) as TIDa; try by_subst. 
  forward eapply (@counters_separated thread) with (x := b) as TIDb; try by_subst. 
  edestruct same_thread with (x := a) (y := b); try by_subst.
  red in H. des; by_subst. 
Qed. 

Lemma write_c_exact thread w
      (CNT: thread < length counters) (NINIT: thread <> 0)
      (W: (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0)) w):
  is_init w \/
  exists index counter, 
    w = ThreadEvent thread index (Astore (nth thread counters 0) (counter + 1)).
Proof.
  destruct w eqn:W_; [by vauto| rewrite <- W_ in *]. right. 
  forward eapply (@iter_self w) as ITER; [by_subst| ].
  forward eapply (@iter_lu w) as TL; [by_subst| ].

  unfold_subtraces TL. desc. 
  assert (thread_ = thread); [| subst thread_].
  { specialize (TID w). specialize_full TID; [apply iter_self; by_subst| ].
    forward eapply counters_separated with (x := w); by_subst. }
  assert (loc w <> s /\ loc w <> t) as LOCw.
  { apply not_or_and. intros IN. 
    specialize (@CNT_DISJ (loc w)). specialize_full CNT_DISJ; try by_subst.
    replace (loc w) with (nth thread counters 0) by by_subst. by apply nth_In. }
  
  rewrite APP in ITER. subst tr_acq tr_l tr_bw tr_ok tr_c tr_u. 
  do 4 rewrite trace_in_app in ITER. des; try by_subst.
  { specialize (BW_FAIL _ ITER0). desc. subst w. inversion BW_FAIL. by_subst. }
  { simpl in ITER0. des; try by_subst.
    cut (thread1 = thread); [ins; by_subst| ]. 
    specialize (TID w). specialize_full TID; [apply iter_self | ]; by_subst. }
Qed.

Lemma write_c_read w thread (CNT: thread < length counters) (NINIT: thread <> 0)
      (W: (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0) \₁ is_init) w):
  exists r, (E G ∩₁ is_r ∩₁ Loc_ (nth thread counters 0) ∩₁ Tid_ thread) r /\
       index w = index r + 1 /\
       valw w = valr r + 1. 
Proof.
  forward eapply (@write_c_exact thread w) as W_; try by_subst. des; [by_subst| ].

  remember (nth thread counters 0) as c.
  assert (In c counters) as C by (subst c; by apply nth_In). 
  
  assert (ticketlock_execution s t c (iter_of w)) as TLx.
  { subst c. replace thread with (tid w) by by_subst. eapply iter_lu. by_subst. }
  forward eapply (@fin_iter_struct' (iter_of w)) as FIN; try by_subst.
  { eapply trace_finite_features; eauto.
    exists w. split; [apply iter_self| ]; by_subst. }
  desc. simpl in FIN. rewrite <- Heqc in FIN. desc.

  assert (w = ThreadEvent thread0 (index2 + 1) (Astore c (counter0 + 1))) as X'.
  { eapply iter_w_unique; try by_subst.
    { apply iter_self. by_subst. }
    rewrite STRUCT. simpl. intuition. }
  rewrite W_ in X'. inversion X'. apply PeanoNat.Nat.add_cancel_r in H2. 
  subst thread0 index counter0. clear X'.

  exists (ThreadEvent thread index2 (Aload c counter)).
  unfolder. splits; try by_subst.
  apply (@iter_exec w); [by_subst| ].
  rewrite STRUCT. simpl. intuition.
Qed.

Lemma read_c_source r thread (CNT: thread < length counters) (NINIT: thread <> 0)
      (R: (E G ∩₁ is_r ∩₁ Loc_ (nth thread counters 0)) r):
  exists w, rf G w r /\
       sb G w r.
Proof. 
  assert (exists w, rf G w r) as [w RF] by (apply RFC; by_subst).
  exists w. split; auto.
  apply exploit_rf in RF; auto. 
  assert (~ is_init r) as NIr.
  { intros INIT. edestruct read_or_rmw_not_init; by_subst. }
  destruct w eqn:W; [apply seq_eqv_lr; destruct r; by_subst| rewrite <- W in *].
  assert (thread0 = thread); [| subst thread0].
  { replace thread0 with (tid w) by by_subst.
    apply counters_separated; unfolder; splits; by_subst. }
  forward eapply (same_thread WF r w) as SB; try by_subst. 
  { erewrite counters_separated with (x := r); unfolder; splits; by_subst. }
  des; [| done]. red in SB. des; [edestruct rf_irr; by vauto| ].
  exfalso. eapply cycle_helper2; eauto; [generalize RF; basic_solver| ].
  repeat left. by_subst.
Qed. 

Lemma writes_c_unique x y thread (CNT: thread < length counters) (NINIT: thread <> 0)
      (X: (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0)) x)
      (Y: (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0)) y) 
      (VALEQ: valw x = valw y):
  x = y.
Proof.
  remember (valw x) as v. generalize dependent x. generalize dependent y.
  generalize dependent v. contra DIFF.
  apply not_all_ex_not in DIFF.
  apply exists_min in DIFF as [v [DIFF MIN]].
  apply not_all_ex_not in DIFF as [x DIFF].
  apply imply_to_and in DIFF as [X DIFF]. apply imply_to_and in DIFF as [Vx DIFF].
  apply not_all_ex_not in DIFF as [y DIFF].
  apply imply_to_and in DIFF as [Y DIFF]. apply imply_to_and in DIFF as [Vy DIFF].

  remember (nth thread counters 0) as c.
  assert (In c counters) as C by (subst c; by apply nth_In). 

  forward eapply (@write_c_exact thread x) as X_; try by_subst.
  forward eapply (@write_c_exact thread y) as Y_; try by_subst.
  des; destruct x, y; try by_subst; [rewrite X_ in Vx | rewrite Y_ in Vy | ]; try by_subst.
  inversion X_. inversion Y_. subst thread0 index1 l thread1 index2 l0.
  clear X_ Y_. rewrite <- Heqc in *. 
  remember (ThreadEvent thread index (Astore c (counter + 1))) as x.
  remember (ThreadEvent thread index0 (Astore c (counter0 + 1))) as y.

  forward eapply (@write_c_read x thread) as [rx RX]; try by_subst.
  forward eapply (@write_c_read y thread) as [ry RY]; try by_subst.
  forward eapply (@read_c_source rx thread) as [w' [RFx SBx]]; try by_subst. 
  forward eapply (@read_c_source ry thread) as [w'' [RFy SBy]]; try by_subst. 
  assert (w' = w''); [| subst w''].
  { specialize (MIN counter). specialize_full MIN; [by_subst|]. apply NNPP in MIN.
    apply exploit_rf in RFx; auto. apply exploit_rf in RFy; auto.
    desc. apply MIN; unfolder; splits; by_subst. }

  assert (sb G x ry \/ sb G y rx) as SB.
  { enough (Events.index x < Events.index ry \/ Events.index y < Events.index rx) as IND.
    { des; [left; destruct ry | right; destruct rx]; apply seq_eqv_lr; by_subst. }
    desc. rewrite RX0, RY0. rename index into index_. 
    assert (index rx + 1 < index ry \/ index ry + 1 < index rx \/
            index rx + 1 = index ry \/ index ry + 1 = index rx \/
            index rx = index ry) as IND by lia.
    des; try lia.
    { enough (x = ry); [by_subst| eapply (wf_index WF); splits; by_subst ]. }
    { enough (y = rx); [by_subst| eapply (wf_index WF); splits; by_subst ]. }
    { enough (x = y); [done|eapply (wf_index WF); splits; unfold same_index; by_subst]. }
  }
    
  des.
  { eapply (@cycle_helper2 _ _ x ry); eauto; [repeat left; by_subst| ].
    right. red. split.
    2: { intros [EQ]. subst ry. eapply sb_irr; eauto. }
    eexists. split; eauto.
    apply exploit_rf in RFx; auto. apply sb_w_loc; try by_subst.
    eapply sb_trans; [apply SBx| ].
    apply seq_eqv_lr. splits; try by_subst.
    red. subst x. destruct rx; splits; by_subst. }
  { eapply (@cycle_helper2 _ _ y rx); eauto; [repeat left; by_subst| ].
    right. red. split.
    2: { intros [EQ]. subst rx. eapply sb_irr; eauto. }
    eexists. split; eauto.
    apply exploit_rf in RFy; auto. apply sb_w_loc; try by_subst.
    eapply sb_trans; [apply SBy| ].
    apply seq_eqv_lr. splits; try by_subst.
    red. subst y. destruct ry; splits; by_subst. }
Qed. 


Lemma iter_of_from_bounds (thread: Tid) i
      (CNT: thread < length counters) (NINIT: thread <> 0)
      (DOMi: NOmega.lt_nat_l i (nth thread thread_niters niters_)):
  exists e, (E G \₁ is_init) e /\
       let bounds := nth thread thread_bounds bounds_ in
       let tr := nth thread thread_traces tr_ in 
       subtrace tr (no2n (bounds i)) (NOmega.sub (bounds (i + 1)) (bounds i))
       = iter_of e.
Proof.
  remember (nth thread thread_traces tr_) as tr. 
  remember (nth thread thread_bounds bounds_) as bounds.
  remember (nth thread thread_niters niters_) as n_iters.
  remember (nth thread counters 0) as c.
  simpl. remember (subtrace tr (no2n (bounds i)) (NOmega.sub (bounds (i + 1)) (bounds i))) as iter.
  pose proof (@TL_EXEC thread) as R. specialize_full R; try congruence. desc.
  red in REP_L_U. destruct (restrict G thread) as [Gt [TRE]]. desc.
  rewrite <- Heqbounds, <- Heqtr, <- Heqc, <- Heqn_iters in *. 

  remember (trace_nth 0 iter d_) as e. exists e.
  assert (trace_elems iter e) as TRe.
  { forward eapply bounds_bound with (i := i + 1) as BOUND'; try by_subst.
    { replace (i + 1) with (S i) by lia. by_subst. }
    rewrite <- Heqtr, <- Heqbounds in BOUND'. 
    red in ITER. desc. specialize (MON i DOMi). 
    subst e. apply trace_nth_in. rewrite Heqiter, subtrace_length. 
    { destruct (bounds i), (bounds (i + 1)); by_subst. }
    destruct (trace_length tr), (bounds i), (bounds (i + 1)); by_subst. }

  assert ((E G \₁ is_init) e) as ENIe.
  { rewrite Heqiter in TRe. apply subtrace_incl, TR_E, TRE in TRe.
    destruct TRe. destruct e; by_subst. }  
  split; [done| ].   
  unfold iter_of. destruct (excluded_middle_informative _); [| done].
  destruct (constructive_indefinite_description _) as [i' [DOMi' I'e]].
  assert (tid e = thread) as TID. 
  { rewrite Heqiter in TRe. apply subtrace_incl, TR_E, TRE in TRe. by_subst. }
  rewrite TID, Heqiter. cut (i = i'); [congruence| ].

  eapply iters_disj with (x := e); eauto.
  { congruence. }
  { by apply trace_wf_nodup. }
  rewrite TID in I'e. split; by_subst.   
Qed. 

Lemma inf_iters_amount thread (CNT: thread < length counters) (NINIT: thread <> 0):
  nth thread thread_niters niters_ = NOinfinity. 
Proof.
  remember (nth thread thread_traces tr_) as tr.
  remember (nth thread thread_bounds bounds_) as bounds. 
  remember (nth thread thread_niters niters_) as n_iters. 
  destruct n_iters; [done| ].
  pose proof (@TL_EXEC thread) as R. specialize_full R; [by_subst| congruence | ].
  desc. destruct INF.
  red in REP_L_U. destruct (restrict G thread) as [Gt [TRE]]. desc.
  rewrite <- TRE, <- TR_E, <- Heqtr. rewrite iters_elems; try by_subst.  
  apply set_finite_bunion; [by rewrite <- Heqn_iters; apply set_finite_lt| ].
  intros i DOMi. 
  forward eapply iter_of_from_bounds as [ei [ENIei ITERei]]; try by_subst.
  simpl in ITERei. 
  forward eapply no_inf_iter as FIN_TR; try by_subst.
  rewrite Heqtr, ITERei.
  red in FIN_TR. desc. rewrite FIN_TR. vauto. 
Qed.


Lemma NOmega_le_plus_minus x y (LE: ~ NOmega.lt y x):
  NOmega.add x (NOmega.sub y x) = y.
Proof.
  destruct x, y; try by_subst.
  simpl in *. f_equal. lia. 
Qed.

Lemma iters_sb (tr: trace Event) M bounds n_iters
      (ITERS: iterates M bounds n_iters tr)
      (TR_WF: trace_wf tr):
  let iter_i := fun i => subtrace tr (no2n (bounds i)) (NOmega.sub (bounds (i + 1)) (bounds i)) in
  forall i e e'
    (DOMi: NOmega.lt_nat_l (i + 1) n_iters)
    (ITERi: trace_elems (iter_i i) e)
    (ITERi': trace_elems (iter_i (i + 1)) e')
    (TID: tid e = tid e'),
    ext_sb e e'.
Proof.
  ins. 
  remember (subtrace tr (no2n (bounds i)) (NOmega.sub (bounds (i + 1)) (bounds i))) as iter.
  remember (subtrace tr (no2n (bounds (i + 1)))
                     (NOmega.sub (bounds (i + 1 + 1)) (bounds (i + 1)))) as iter'.

  forward eapply bounds_bound with (i := i + 1) as BOUND; eauto.
  { omegaW n_iters. }
  destruct (bounds (i + 1)) as [| bi'] eqn:Bi'.
  { red in ITERS. desc. destruct tr; try by_subst.
    specialize (MON (i + 1)). specialize_full MON; [by destruct n_iters; by_subst| ].
    destruct (bounds (i + 1)); by_subst. }
  destruct (bounds i) as [| bi] eqn:Bi.
  { red in ITERS. desc.
    specialize (MON i). specialize_full MON; [by destruct n_iters; by_subst| ]. 
    destruct (bounds i); by_subst. }
  simpl in *.
  assert (bi < bi') as LT. 
  { red in ITERS. desc.
    specialize (MON i). specialize_full MON; [by destruct n_iters; by_subst| ].
    by rewrite Bi', Bi in MON. }
  assert (NOmega.lt_nat_l bi' (bounds (i + 1 +1))) as LT'. 
  { red in ITERS. desc.
    specialize (MON (i + 1)). specialize_full MON; [by destruct n_iters; by_subst| ].
    rewrite Bi' in MON. vauto. }

  apply trace_in_nth with (d := d_) in ITERi as [n [DOMn NTH]].
  apply trace_in_nth with (d := d_) in ITERi' as [n' [DOMn' N'TH]].
  red in TR_WF.

  assert (trace_length iter = NOnum (bi' - bi)) as LEN1.
  { rewrite Heqiter, subtrace_length; auto. 
    red in ITERS. desc.
    specialize (MON i). specialize_full MON; [by destruct n_iters; by_subst| ].
    rewrite Bi', Bi in MON. simpl in MON.
    simpl. rewrite Minus.le_plus_minus_r; by_subst. }
  assert (trace_length iter' = NOmega.sub (bounds (i + 1 + 1)) (NOnum bi')) as LEN2.
  { rewrite Heqiter', subtrace_length; auto. 
    red in ITERS. desc.
    pose proof (MON (i + 1)) as MON'. specialize_full MON'; [done| ].
    forward eapply bounds_bound with (i := i + 1 + 1); try by_subst.
    { omegaW n_iters. }
    destruct (bounds (i + 1 + 1)), tr; by_subst. }

  assert (trace_nth (bi + n) tr d_ = e) as E1. 
  { rewrite <- subtrace_trace_corr with (len := trace_length iter); try by_subst.
    { congruence. }
    rewrite LEN1. simpl. rewrite Minus.le_plus_minus_r; auto. lia. }
  assert (trace_nth (bi' + n') tr d_ = e') as E2.
  { rewrite <- subtrace_trace_corr with (len := NOmega.sub (bounds (i + 1 + 1)) (NOnum bi')); try by_subst.
    { rewrite NOmega_le_plus_minus; [| omegaW (bounds (i + 1 + 1))].
      eapply bounds_bound; eauto. omegaW n_iters. }
    rewrite LEN2 in DOMn'. omegaW (bounds (i + 1 + 1)). }
  
  specialize (TR_WF (bi + n) (bi' + n')) with (d := d_). specialize_full TR_WF.
  { red in ITERS. desc.
    specialize (MON i). specialize_full MON; [by destruct n_iters; by_subst| ].
    rewrite Bi', Bi in MON. simpl in MON.
    cut (n < bi' - bi); [lia| ].
    rewrite LEN1 in DOMn. by simpl in DOMn. }
  { cut (~ NOmega.lt (trace_length tr) (bounds (i + 1 + 1))); auto.
    2: { eapply bounds_bound; eauto. omegaW n_iters. }
    intros DOM''.
    cut (NOmega.lt_nat_l (bi' + n') (bounds (i + 1 + 1))).
    { ins. destruct (bounds (i + 1 + 1)), tr; by_subst. }    
    red in ITERS. desc. specialize (MON (i + 1)). specialize_full MON; [done| ].
    rewrite LEN2 in DOMn'. omegaW (bounds (i + 1 + 1)). }
  { by rewrite E1, E2. }

  rewrite E1, E2 in TR_WF. 
  destruct e, e'; by_subst.
Qed. 


Lemma next_c_write e (thread: Tid) (CNT: thread < length counters)
      (NINIT: thread <> 0) (Ee: E G e) (Te: is_init e \/ Tid_ thread e):
  exists w, (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0)) w /\ sb G e w.
Proof.
  remember (nth thread counters 0) as c.
  pose proof (@TL_EXEC thread) as TL_EXEC'.
  specialize_full TL_EXEC'; [by_subst| congruence | ]. desc. 
  red in REP_L_U. desc.
  destruct (restrict G thread) as [Gt [TRE]]. desc.  
  forward eapply inf_iters_amount as INF_ITERS; try by_subst.
  rewrite <- Heqc, INF_ITERS in ITER.
  remember (nth thread thread_traces tr_) as tr.
  remember (nth thread thread_bounds bounds_) as bounds. 
  
  cut (exists i, forall e'
              (ITERi: trace_elems (subtrace tr (no2n (bounds i)) (NOmega.sub (bounds (i + 1)) (bounds i))) e'), ext_sb e e').
  { intros [i NEXT_ITER]. 
    remember (subtrace tr (no2n (bounds i))
              (NOmega.sub (bounds (i + 1)) (bounds i))) as tr_cur. 
    assert (trace_elems tr_cur ⊆₁ E Gt) as IN_ET.
    { etransitivity; [subst; apply subtrace_incl| by rewrite <- Heqtr, TR_E]. }
    assert (ticketlock_execution s t c tr_cur) as TLcur.
    { subst tr_cur c. by apply ITER. }
    forward eapply (@iter_of_from_bounds thread i) as [ei [ENIei ITERei]]; auto.
    { by rewrite INF_ITERS. }
    simpl in ITERei. rewrite <- Heqtr, <- Heqbounds in ITERei. 
    forward eapply (@no_inf_iter ei) as FINcur; try by_subst.
    rewrite <- ITERei, <- Heqtr_cur in FINcur. 
    (* { etransitivity; [eauto | rewrite TRE; basic_solver]. } *)
    eapply fin_iter_struct' in FINcur; try by_subst. simpl in FINcur. desc.
    (* rewrite <- Heqc in *.  *)
    remember (ThreadEvent thread0 (index2 + 1) (Astore c (counter + 1))) as w.
    assert (trace_elems tr_cur w) as TRCw.
    { rewrite STRUCT. simpl. right. apply in_app_r. subst. intuition. }
    assert (thread0 = thread); [| subst thread0].
    { replace thread0 with (tid w) by by_subst. rewrite TRE in IN_ET.
      specialize (IN_ET w). specialize_full IN_ET; by_subst. }
    exists w.
    assert (E G w) as Ew.
    { cut (E Gt w). 
      { ins. apply TRE in H. by_subst. }
      apply IN_ET. by_subst. }
    split; unfolder; splits; try by_subst.    
    red. apply seq_eqv_lr. splits; try by_subst.
    apply NEXT_ITER. by_subst. }
    
  des. 
  { destruct e; [| done]. exists 0. intros.
    red in ITER. desc. specialize (ITER 0 I).
    eapply tl_ninit in ITERi; eauto.
    basic_solver. }

  destruct e eqn:E_; [by_subst| ]. 
  simpl in Te. subst thread0. rewrite <- E_ in *.
  assert (trace_elems tr e) as TRe by (apply TR_E, TRE; by_subst).
  eapply iters_elems in TRe as [i [DOMi ITERi]]; eauto. 
  exists (i + 1). ins. eapply iters_sb; eauto.
  apply subtrace_incl, TR_E, TRE in ITERi0. by_subst.  
Qed. 

Lemma ticketlock_client_progress_weak (INF: ~ set_finite (E G)):
  forall thread val (CNT: thread < length counters) (NINIT: thread <> 0),
  exists val' w, (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0) ∩₁ Valw_ val') w /\
            val <= val'.
Proof.
  ins. contra BOUNDED_.
  remember (nth thread counters 0) as c. 
  assert (E G ∩₁ is_w ∩₁ Loc_ c ⊆₁ (fun e => valw e < val)) as BOUNDED.
  { red. ins.
    destruct (PeanoNat.Nat.lt_ge_cases (valw x) val) as [| LE]; [done| ].
    destruct BOUNDED_. by_subst. }
  clear BOUNDED_.

  assert (set_finite (E G ∩₁ is_w ∩₁ Loc_ c)) as W_BOUND.
  { eapply set_finite_mori. 
    2: { eapply valw_bounded_fin. ins. eapply writes_c_unique; eauto. }
    red. apply set_subset_inter_r. split; vauto. }

  forward eapply latest_fin with (S := E G ∩₁ is_w ∩₁ Loc_ c) (r := sb G); auto.
  { apply set_nonemptyE. exists (InitEvent c). unfolder. splits; try by_subst.
    apply wf_initE; vauto. }
  { subst c. by apply c_writes_order. }
  intros [w [W MAX]].

  forward eapply (@next_c_write w) as [w' [W' SB]]; try by_subst.
  { destruct (classic (is_init w)); [by_subst| ].
    forward eapply counters_separated with (x := w); by_subst. }
    
  rewrite <- Heqc in W'. specialize (MAX w' W').
  red in MAX. des; [eapply sb_irr; by vauto| ].
  eapply cycle_helper2 with (x := w) (y := w'); eauto;
    repeat left; red; split; by_subst. 
Qed.

Lemma writes_c_chain w v thread (CNT: thread < length counters) (NINIT: thread <> 0)
      (W: (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0) ∩₁ Valw_ v) w):
  forall v' (LT: v' < v),
  exists w',
    (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0) ∩₁ Valw_ v') w'. 
Proof.
  generalize dependent w. induction v; ins; [lia| ].
  
  destruct w eqn:W_; [by_subst| rewrite <- W_ in *]. 
  forward eapply (@write_c_read w) as [r R]; try by_subst. 
  forward eapply (@read_c_source r) as [w' W']; try by_subst.

  apply Lt.lt_n_Sm_le, PeanoNat.Nat.le_lteq in LT. des.
  2: { exists w'. apply exploit_rf in W'; auto. unfolder'. splits; by_subst. }
  
  specialize (IHv w') with (v' := v'). specialize_full IHv; try by_subst. 
  desc. apply exploit_rf in W'; auto.
  unfolder'. splits; by_subst.
Qed.

Theorem ticketlock_client_progress_impl (INF: ~ set_finite (E G)):
  forall thread val (CNT: thread < length counters) (NINIT: thread <> 0),
  exists w, (E G ∩₁ is_w ∩₁ Loc_ (nth thread counters 0) ∩₁ Valw_ val) w.
Proof.
  ins.
  forward eapply ticketlock_client_progress_weak with (val := val); try by_subst.
  ins. desc.
  apply Lt.le_lt_or_eq in H0. des; [| by vauto].
  forward eapply (@writes_c_chain w val') with (v' := val); eauto.
Qed.
  

End TicketlockProgress.

Theorem ticketlock_client_progress
  (G : execution)
  (s t : Loc)
  (NEQst : s <> t)
  (counters : list Loc)
  (n_threads : nat)
  (CNT_CORR : length counters = n_threads)
  (CNT_NODUP : NoDup counters)
  (CNT_DISJ : disjoint counters [s; t])
  (FAIR : mem_fair G)
  (SCpL : Execution.SCpL G)
  (WF : Wf G)
  (RFC : rf_complete G)
  (BOUNDED_THREADS : (fun thread : nat =>
                     exists e : Event, (E G ∩₁ Tid_ thread) e)
                    ≡₁ (fun thread : nat => thread < n_threads))
  (thread_traces : list (trace Event))
  (thread_bounds : list (nat -> nat_omega))
  (thread_niters : list nat_omega)
  (TL_EXEC : repeated_ticketlock_client_execution
               G s t counters n_threads
               thread_traces thread_bounds thread_niters )
  (INF : ~ set_finite E G)
  :
  forall thread val : nat,
  thread < length counters ->
  thread <> 0 ->
  exists w : Event,
    (E G ∩₁ (fun a : Event => is_w a) ∩₁ Loc_ (nth thread counters 0)
     ∩₁ Valw_ val) w. 
Proof. eapply ticketlock_client_progress_impl; eauto. Qed.

Redirect "axioms_ticketlock" Print Assumptions ticketlock_client_progress.
    
