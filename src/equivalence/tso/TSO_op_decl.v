Require Import AuxRel.
Require Import Labels.
Require Import Events.
Require Import Lia.
Require Import Arith.
Require Import Execution.
Require Import IndefiniteDescription.
Require Import PropExtensionality.
Require Import List.
Require Import TraceWf.
From hahn Require Import Hahn. 
Require Import SC.
Require Import TSO.
Require Import AuxProp.

Set Implicit Arguments.


Lemma minus_inter_union {A: Type} (r r': relation A) : r ≡ r ∩ r' ∪ r \ r'.
Proof. unfolder; split; ins; desf; tauto. Qed.

Lemma sb_ppo_ext G: sb G ≡ ppo G ∪ ⦗is_w⦘ ⨾ sb G ⨾ ⦗is_r⦘.
Proof.
  rewrite (minus_inter_union (sb G) ((is_w) × (is_r))) at 1.
  unfold ppo. rewrite unionC. apply union_more; [auto| basic_solver].
Qed.

Section Op2Decl.

Variable tr: trace TSO_label.
Variable states: nat -> TSOMemory. 
Hypothesis (TR: LTS_trace_param TSO_lts states tr). 
Hypothesis (WF: TSO_trace_wf tr). 
Hypothesis (FAIR: TSO_fair tr states).

Definition Eninit := fun e => trace_elems tr (inl e).
Hypothesis BOUNDED_THREADS: exists n, forall e, Eninit e -> tid e < n.
Hypothesis NO_TID0: forall e, Eninit e -> tid e <> 0. 

Definition EG := is_init ∪₁ Eninit.


Definition trace_labels := fun n => trace_nth n tr def_lbl. 

Definition trace_index : Event -> nat.
  intros e.
  destruct (excluded_middle_informative (Eninit e)).
  2: { exact 0. }
  red in e0. pose proof (@trace_in_nth _ tr (inl e) e0 def_lbl).
  apply constructive_indefinite_description in H. destruct H. exact x. 
Defined. 

Lemma ti_inj e1 e2 (E'1: Eninit e1) (E'2: Eninit e2) (EQ: trace_index e1 = trace_index e2):
  e1 = e2.
Proof.
  unfold trace_index in EQ.
  do 2 (destruct (excluded_middle_informative _); [| done]).
  do 2 (destruct (constructive_indefinite_description _ _); desc).
  subst x0. congruence. 
Qed. 

Lemma trace_index_simpl e (ENINIT: Eninit e):
  forall d, trace_nth (trace_index e) tr d = inl e.
Proof.
  ins. unfold trace_index. destruct (excluded_middle_informative _); [| done].
  destruct (constructive_indefinite_description _ _). desc.
  rewrite <- a0. by apply trace_nth_indep. 
Qed. 

Lemma trace_index_simpl' e (ENINIT: Eninit e):
  trace_labels (trace_index e) = inl e.
Proof.
  unfold trace_labels. apply trace_index_simpl; auto. 
Qed. 

Lemma TS0: LTS_init TSO_lts (states 0).
Proof. by apply LTS_trace_param' in TR as [H _]. Qed.

Lemma TSi i (DOM: NOmega.lt_nat_l i (trace_length tr)) d:
  LTS_step TSO_lts (states i) (trace_nth i tr d) (states (S i)).
Proof. apply LTS_trace_param' in TR as [_ H]. by apply H. Qed.

Lemma Eninit_non_init: is_init ∩₁ Eninit ≡₁ ∅.
Proof.
  split; [| basic_solver].
  red. intros e [INIT NINIT].
  destruct e; vauto. red in NINIT.
  apply trace_in_nth with (d := def_lbl) in NINIT. desc.
  pose proof (TSi n NINIT def_lbl). rewrite NINIT0 in H. inversion H.
Qed. 

Definition trace_before := fun x y => trace_index x < trace_index y.
Lemma tb_respects_sb: ⦗Eninit⦘ ⨾ ext_sb ⨾ ⦗Eninit⦘ ≡ ⦗Eninit⦘ ⨾ (trace_before ∩ same_tid) ⨾ ⦗Eninit⦘. 
Proof.
  split.
  { rewrite seq_eqv_lr. red. ins. desc.
    apply seq_eqv_lr. splits; auto. 
    destruct x, y; vauto.
    { by destruct (proj1 Eninit_non_init (InitEvent x)). }
    simpl in H0. desc. split; auto. subst thread0.
    red. unfold trace_index.
    do 2 (destruct (excluded_middle_informative _); [| done]).
    do 2 (destruct (constructive_indefinite_description _ _); desc).
    red in WF.
    pose proof (NPeano.Nat.lt_trichotomy x x0). des; auto.
    { subst. rewrite a2 in a0. inversion a0. lia. }
    forward eapply (@WF x0 x def_lbl thread index0 index l0 l); auto.
    lia. }
  { red. ins. apply seq_eqv_lr in H. desc.
    apply seq_eqv_lr. splits; auto.
    destruct x. 
    { by destruct (proj1 Eninit_non_init (InitEvent x)). }
    destruct y. 
    { by destruct (proj1 Eninit_non_init (InitEvent x)). }
    simpl. red in H0. desc. red in H2. simpl in H2.
    splits; vauto.
    red in H0. unfold trace_index in H0. 
    do 2 (destruct (excluded_middle_informative _); [| done]).
    do 2 (destruct (constructive_indefinite_description _ _); desc).
    eapply WF; eauto. }
Qed. 

Lemma tb_SPO: strict_total_order Eninit trace_before.
Proof.
  red. split.
  { unfold trace_before. split.
    all: red; ins; lia. }
  red. ins. unfold trace_before.
  pose proof (Nat.lt_trichotomy (trace_index a) (trace_index b)). des; auto.
  by apply ti_inj in H.
Qed.

Definition is_init' e :=
  match e with
  | InitEvent _ => true
  | ThreadEvent _ _ _ => false
  end. 

(* Definition is_regular_write e := is_w e && negb (is_rmw e || is_init' e).  *)
(* (* Definition regular_write lbl := (is_w \₁ (is_rmw ∪₁ is_init)) (proj_ev lbl). *) *)
(* Definition regular_write (lbl: TSO_label) := *)
(*   match lbl with *)
(*   | inl e => is_regular_write e *)
(*   | _ => false *)
(*   end. *)
Definition count_upto S bound :=
  length (filterP S (map (fun i : nat => trace_nth i tr def_lbl) (List.seq 0 bound))).


Definition state_before_event e := states (trace_index e). 


Definition check {A: Type } S (elt: A) := length (ifP S elt then elt :: nil else nil).

Lemma check0 {A: Type } S (elt: A) (NS: ~ S elt): check S elt = 0.
Proof. unfold check. destruct (excluded_middle_informative (S elt)); vauto. Qed.  

Lemma check1 {A: Type } (S: A -> Prop) (elt: A) (SSS: S elt): check S elt = 1.
Proof. unfold check. destruct (excluded_middle_informative (S elt)); vauto. Qed.  

Lemma buffer_same_transition st1 st2 lbl thread (STEP: TSO_step st1 lbl st2)
      (OTHER: lbl_thread_opt lbl <> Some thread):
  snd (st1) thread = snd (st2) thread. 
Proof.
  destruct st1 as [mem1 buf1]. destruct st2 as [mem2 buf2]. simpl.
  inversion STEP; vauto; simpl in OTHER. 
  all: rewrite updo; auto. 
Qed. 

(* Ltac unfolder' := unfold set_compl, regular_write', is_regular_write', set_minus, set_inter, set_union, is_r, is_r_l, is_w, is_w_l, is_rmw, is_rmw_l, is_init, lab, is_prop, trace_labels, def_lbl, in_thread, lbl_thread_opt.  *)


Lemma buffer_size_inv st1 st2 lbl thread (STEP: TSO_step st1 lbl st2):
  length (snd st1 thread) +
  check (regular_write' ∩₁ in_thread thread) lbl =
  check (is_prop ∩₁ in_thread thread) lbl +
  length (snd st2 thread).
Proof.
  destruct st1 as [mem1 buf1]. destruct st2 as [mem2 buf2]. simpl.
  destruct (classic (lbl_thread_opt lbl = Some thread)) as [EQ | NEQ] .
  2: { forward eapply buffer_same_transition as SAME_BUF; eauto. simpl in SAME_BUF.
       rewrite SAME_BUF. 
       repeat rewrite check0; [lia| |].
       all: apply set_compl_inter; right; vauto. }
  inversion STEP; subst; simpl in EQ; inv EQ. 
  { repeat rewrite check0; [lia| |].
    { apply set_compl_inter; left; vauto. }
    apply set_compl_inter; left.
    unfolder'. intuition. }
  { repeat rewrite check0; [lia| |].
    { apply set_compl_inter; left; vauto. }
    apply set_compl_inter; left.
    unfolder'. intuition. }
  { rewrite check1.
    2: { unfolder'. simpl. intuition. }
    rewrite check0.
    2: { unfolder'. simpl. intuition. }
    rewrite upds. rewrite length_app. simpl. lia. }
  { repeat rewrite check0; [lia| |].
    { apply set_compl_inter; left; vauto. }
    apply set_compl_inter; left.
    unfolder'. intuition. }
  { rewrite upds. rewrite BUF. simpl.
    rewrite check0.
    2: { unfolder'. simpl. intuition. }
    rewrite check1; [| unfolder'; simpl; intuition].
    lia. }
Qed. 


Lemma buffer_size thread i (DOM: NOmega.le (NOnum i) (trace_length tr)):
  count_upto (regular_write' ∩₁ in_thread thread) i = count_upto (is_prop ∩₁ in_thread thread) i + length (snd (states i) thread).
Proof.
  induction i.
  { simpl. unfold count_upto. rewrite seq0. simpl.
    pose proof TS0 as TS0. simpl in TS0. by rewrite <- TS0. }
  remember (states (S i)) as s. simpl.
  unfold count_upto. rewrite !seqS, !Nat.add_0_l, !map_app, !filterP_app, !length_app. simpl.
  fold (count_upto (regular_write' ∩₁ in_thread thread) i).
  fold (count_upto (is_prop ∩₁ in_thread thread) i).
  specialize_full IHi.
  { apply NOmega.le_trans with (m := NOnum (S i)); vauto. } 
  fold (check (regular_write' ∩₁ in_thread thread) (trace_nth i tr def_lbl)). 
  fold (check (is_prop ∩₁ in_thread thread) (trace_nth i tr def_lbl)). 
  remember (states i) as st_prev.
  rewrite IHi.
  rewrite <- !Nat.add_assoc.
  f_equal. 

  simpl in IHi. 
  apply buffer_size_inv.
  forward eapply (TSi i) with (d := def_lbl) as TSi; vauto.
Qed. 

Lemma sim_subtraces_conv (C1 C2: TSO_label -> Prop)
           (LEN: trace_length (trace_filter C1 tr) = trace_length (trace_filter C2 tr)):
  forall i (C1i: C1 (trace_labels i))
    (DOMi: NOmega.lt_nat_l i (trace_length tr)),
  exists j, C2 (trace_labels j) /\
       NOmega.lt_nat_l j (trace_length tr) /\
       count_upto C1 i = count_upto C2 j.
Proof.
  ins.
  remember (trace_filter C1 tr) as tr1. remember (trace_filter C2 tr) as tr2.
  pose proof (trace_lt_length_filter i tr DOMi C1 def_lbl C1i).
  fold (count_upto C1 i) in H. remember (count_upto C1 i) as k.
  rewrite <- Heqtr1, LEN in H. pose proof H as DOM_TR2k. 
  rewrite Heqtr2 in H. apply trace_nth_filter with (d := def_lbl) in H.
  destruct H as [j [DOMj [FILTER_MATCH COUNT]]].
  exists j. splits; auto.
  unfold trace_labels. rewrite <- FILTER_MATCH.
  apply trace_nth_in with (d := def_lbl) in DOM_TR2k.
  rewrite Heqtr2 in DOM_TR2k. apply trace_in_filter in DOM_TR2k.
  by desc. 
Qed.


Lemma NOmega_lt_trichotomy (x y: nat_omega): (NOmega.lt x y) \/ (NOmega.lt y x) \/ (x = y).
Proof.
  destruct x, y; vauto. simpl.
  pose proof (Nat.lt_trichotomy n n0). des; vauto.
Qed.

Ltac contra name :=
  match goal with
  | |- ?gl => destruct (classic gl) as [|name]; [auto|exfalso]
  end.


Lemma filter_ends {A: Type} (t: trace A) (S: A -> Prop) d
      (FIN: trace_length (trace_filter S t) <> NOinfinity):
  exists i, (NOmega.le (NOnum i) (trace_length t)) /\
       forall j (GE: j >= i) (DOM: NOmega.lt_nat_l j (trace_length t)),
         ~ S (trace_nth j t d).
Proof.
  unfold trace_filter in FIN. 
  destruct t.
  { simpl. exists (length l). split; [lia| ]. ins. lia. }
  destruct (excluded_middle_informative (set_finite (fl ↓₁ S))).
  2: { vauto. }
  pose proof s as s'. apply set_finite_nat_bounded in s'. desc.
  exists bound. split.
  { vauto. }
  ins. red. ins.
  specialize (s' j). specialize_full s'; [vauto| ]. 
  lia.
Qed. 

Lemma trace_split {A: Type} (t: trace A) k d
      (LE_LENGTH: NOmega.le (NOnum k) (trace_length t)):
  exists l t'', l = map (fun i => trace_nth i t d) (List.seq 0 k) /\
           t = trace_app (trace_fin l) t''. 
Proof.
  destruct t.
  { simpl in *. exists (firstn k l). exists (trace_fin (skipn k l)).
    splits.
    2: { by rewrite firstn_skipn. }
    replace k with (length (firstn k l)) at 2.
    2: { apply firstn_length_le. lia. }
    rewrite map_nth_seq with (d := d); auto.
    intros. rewrite Nat.add_0_l.
    rewrite <- (firstn_skipn k) at 1. rewrite app_nth1; auto. }
  simpl trace_nth. exists (map (fun i => fl i) (List.seq 0 k)).
  exists (trace_inf (fun n => fl (k + n))). splits; auto. simpl.
  unfold trace_prepend. rewrite map_length, seq_length.
  f_equal.

  exten.

  ins. destruct (Nat.ltb x k) eqn:LTB.
  { rewrite map_nth. rewrite seq_nth; vauto. by apply Nat.ltb_lt. }
  f_equal. rewrite <- le_plus_minus; auto. by apply Nat.ltb_ge in LTB.   
Qed. 

Lemma NOmega_add_le x y: NOmega.le (NOnum x) (NOmega.add (NOnum x) y).
Proof. destruct y; vauto. simpl. lia. Qed.
  
Lemma count_le_filter {A: Type} (t: trace A) (S: A -> Prop) bound d
  (LE_LENGTH: NOmega.le (NOnum bound) (trace_length t)):
  NOmega.le
    (NOnum (length (filterP S (map (fun i => trace_nth i t d) (List.seq 0 bound)))))
    (trace_length (trace_filter S t)).
Proof.
  pose proof (trace_split t bound d LE_LENGTH) as [l [t'' [MAP APP]]].
  rewrite <- MAP, APP.  
  rewrite trace_filter_app; [| vauto]. 
  rewrite trace_length_app. simpl trace_length. 
  apply NOmega_add_le.
Qed. 

Lemma count_upto_next i F:
  count_upto F (S i) = count_upto F i + check F (trace_labels i).
Proof.
  unfold count_upto. rewrite seqS, plus_O_n.
  by rewrite !map_app, !filterP_app, !length_app. 
Qed. 


Lemma count_upto_more i j F (LE: i <= j):
  count_upto F i <= count_upto F j. 
Proof.
  apply le_lt_eq_dec in LE. destruct LE as [LT | EQ]; [| subst; lia]. 
  apply lt_diff in LT. desc. subst. 
  unfold count_upto. rewrite seq_add.
  rewrite !map_app, !filterP_app, !length_app.
  lia. 
Qed. 

(* TODO: generalize, move to hahn? *)
Lemma ge_default i:
  trace_labels i = def_lbl <-> ~ (NOmega.lt_nat_l i (trace_length tr)).
Proof. 
  split.
  { red. intros DEF LT.
    pose proof TR as TR'. apply LTS_trace_param' in TR'. desc.
    specialize (TR'0 i LT def_lbl).
    unfold trace_labels in DEF.
    rewrite DEF in TR'0.
    inversion TR'0. }
  intros.
  unfold trace_labels, trace_nth.
  remember (trace_length tr) as tr_len.
  destruct tr.
  2: { simpl in Heqtr_len.
       exfalso. apply H. vauto. }
  unfold NOmega.lt_nat_l in H. rewrite Heqtr_len in H. simpl in H.
  rewrite nth_overflow; auto. lia.
Qed.

Lemma lt_nondefault i:
  trace_labels i <> def_lbl <-> NOmega.lt_nat_l i (trace_length tr).
Proof. 
  pose proof (ge_default i). apply not_iff_compat in H.
  eapply iff_trans; eauto. split; auto. apply NNPP.
Qed. 

Ltac liaW no := (destruct no; [done|simpl in *; lia]).

Lemma EXACT_PROPS thread:
  trace_length (trace_filter (regular_write' ∩₁ in_thread thread) tr) =
  trace_length (trace_filter (is_prop ∩₁ in_thread thread) tr).
Proof.
  remember (trace_length (trace_filter (regular_write' ∩₁ in_thread thread) tr)) as len_writes.
  remember (trace_length (trace_filter (is_prop ∩₁ in_thread thread) tr)) as len_props. 
  pose proof (NOmega_lt_trichotomy len_writes len_props). des; auto.
  { exfalso. destruct len_writes as [|n_writes]; auto.
    forward eapply (trace_nth_filter (is_prop ∩₁ in_thread thread) tr n_writes def_lbl) as [extra_prop_pos [DOM_EP [MATCH_PROP COUNT_PROPS]]].
    { vauto. }
    fold (count_upto (is_prop ∩₁ in_thread thread) extra_prop_pos) in COUNT_PROPS.
    forward eapply (filter_ends tr (regular_write' ∩₁ in_thread thread) def_lbl) as [w_bound [DOM_WB WRITES_BOUND]]. 
    { by rewrite <- Heqlen_writes. }
    set (bound := max (extra_prop_pos + 1) w_bound).     
    forward eapply (buffer_size thread bound) as BUF_SIZE.
    { destruct tr; auto. simpl in *. subst bound.
      apply NPeano.Nat.max_lub_iff. split; lia. }
    simpl in BUF_SIZE. remember (states bound) as st.
    cut (count_upto (regular_write' ∩₁ in_thread thread) bound <= n_writes /\
         count_upto (is_prop ∩₁ in_thread thread) bound > n_writes).
    { ins. desc. lia. }
    split.
    { cut (NOmega.le (NOnum (count_upto (regular_write' ∩₁ in_thread thread) bound)) (NOnum n_writes)).
      { ins. }
      rewrite Heqlen_writes. unfold count_upto. apply count_le_filter.
      simpl. destruct (trace_length tr); vauto.
      subst bound. apply Nat.max_lub_iff. simpl in *. split; lia. }
    unfold gt. apply Nat.lt_le_trans with (m := count_upto (is_prop ∩₁ in_thread thread) (extra_prop_pos + 1)).
    { rewrite COUNT_PROPS.
      rewrite Nat.add_1_r, count_upto_next.
      rewrite check1; [lia| ].
      unfold trace_labels. rewrite <- MATCH_PROP.
      forward eapply (trace_nth_in (trace_filter (is_prop ∩₁ in_thread thread) tr) n_writes) with (d := def_lbl) as IN_FILTER. 
      { rewrite <- Heqlen_props. vauto. }
      vauto. 
      apply trace_in_filter in IN_FILTER. by desc. }
    apply count_upto_more. subst bound. apply Nat.le_max_l. }
  exfalso. 
  destruct len_props as [|n_props]; auto.

  forward eapply (trace_nth_filter (regular_write' ∩₁ in_thread thread) tr n_props def_lbl) as [extra_write_pos [DOM_EW [MATCH_WRITE COUNT_WRITES]]].
  { vauto. }
  fold (count_upto (regular_write' ∩₁ in_thread thread) extra_write_pos) in COUNT_WRITES.
  set (enabled st := exists st', TSO_step st (inr thread) st').
  assert (forall i (GE: i >= (extra_write_pos + 1))
            (LE: NOmega.le (NOnum i) (trace_length tr)),
             enabled (states i)) as ENABLED_AFTER_WRITES.
  { intros. pose proof (buffer_size thread i) as BUF_SIZE. specialize_full BUF_SIZE.
    { destruct tr; vauto. }
    cut (length (snd (states i) thread) > 0).
    { ins. destruct (states i) as [mem bufs]. simpl in *. red.
      destruct (bufs thread) as [| (loc, val) buf'] eqn:BUFS; [simpl in H0; lia| ].
      exists (upd mem loc val, upd bufs thread buf'). by eapply tso_prop. }
    simpl in BUF_SIZE. cut (count_upto (regular_write' ∩₁ in_thread thread) i > count_upto (is_prop ∩₁ in_thread thread) i); [ins; lia| ].
    unfold gt.
    apply Nat.le_lt_trans with (m := n_props).
    { forward eapply (count_le_filter tr (is_prop ∩₁ in_thread thread) i def_lbl) as COUNT_LE_FILTER; auto.
      rewrite <- Heqlen_props in COUNT_LE_FILTER. simpl in COUNT_LE_FILTER.
      by unfold count_upto. }
    apply Nat.lt_le_trans with (m := count_upto (regular_write' ∩₁ in_thread thread) (extra_write_pos + 1)).
    2: { apply count_upto_more. lia. }
    rewrite Nat.add_1_r, count_upto_next. rewrite <- COUNT_WRITES.
    rewrite check1; [lia| ].
    unfold trace_labels. rewrite <- MATCH_WRITE.
    remember (regular_write' ∩₁ in_thread thread) as F.
    remember (trace_nth n_props (trace_filter F tr) def_lbl) as elem. 
    forward eapply (proj1 (trace_in_filter elem F tr)); [| intuition]. 
    subst elem. apply trace_nth_in. vauto. }  
  
  forward eapply (filter_ends tr (is_prop ∩₁ in_thread thread) def_lbl) as [props_end [DOM NOMORE_PROPS]]. 
  { by rewrite <- Heqlen_props. }
  set (after_last_prop := max (extra_write_pos + 1) props_end).


  assert (NOmega.le (NOnum after_last_prop) (trace_length tr)) as ALP_LE. 
  { destruct tr; vauto. simpl in *. unfold after_last_prop. apply NPeano.Nat.max_lub_iff. split; lia. }

  pose proof FAIR as FAIR_. 
  specialize (@FAIR_ after_last_prop thread). specialize_full FAIR_; auto. 
  { apply ENABLED_AFTER_WRITES; auto. 
    pose proof (Nat.le_max_l (extra_write_pos + 1) props_end). lia. }
  
  destruct FAIR_ as (j & ALPj & DOMj & TRj). 
  specialize (NOMORE_PROPS j). specialize_full NOMORE_PROPS.
  { pose proof (Nat.le_max_r (extra_write_pos + 1) props_end). lia. }
  { apply lt_nondefault. unfold trace_labels. by rewrite TRj. }
  rewrite TRj in NOMORE_PROPS. unfolder'. intuition. 
Qed.

Definition same_thread x y :=
  let thread := lbl_thread_opt x in
  thread = lbl_thread_opt y /\ thread <> None. 

Lemma set_extensionality A (r r' : A -> Prop) :
  r ≡₁ r' -> r = r'.
Proof.
  ins. extensionality x. 
  apply propositional_extensionality; split; apply H.
Qed.  

(* Lemma init_non_rw: forall l, ~ regular_write' (inl (InitEvent l)). *)
(* Proof. *)
(*   apply init_non_rw'.  *)
(* Qed. *)



Lemma write2prop_lem w
      (* (DOM: NOmega.lt_nat_l w (trace_length tr)) *)
      (W: regular_write' (trace_labels w)):
  exists p,
    ⟪THREAD_PROP: (is_prop ∩₁ same_thread (trace_labels w)) (trace_labels p)⟫ /\
    (* ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\ *)
    ⟪W_P_CORR: count_upto (regular_write' ∩₁ same_thread (trace_labels w)) w =
               count_upto (is_prop ∩₁ same_thread (trace_labels w)) p⟫.
Proof.
  simpl.
  assert (DOM: NOmega.lt_nat_l w (trace_length tr)).
  { destruct (classic (NOmega.lt_nat_l w (trace_length tr))); auto.
    exfalso. apply ge_default in H. rewrite H in W.
    unfolder'. intuition. }
  pose proof (reg_write_structure _ W). 
  desc.
  assert (same_thread (trace_labels w) ≡₁ in_thread thread).
  { rewrite H. simpl. unfold same_thread. simpl.
    unfold in_thread.
    red. split; red; ins; desc; vauto. }
  apply set_extensionality in H0. rewrite H0 in *. 
  pose proof sim_subtraces_conv as TMP. specialize_full TMP.
  { eapply (EXACT_PROPS thread). }
  { red. splits; eauto.
    rewrite H. vauto. }
  { auto. }
  desc. exists j. splits; vauto.
Qed.

                      
Definition write2prop (w: nat) :=
  match (excluded_middle_informative (regular_write' (trace_labels w))) with
  | left W => (proj1_sig ((constructive_indefinite_description _ (write2prop_lem w W))))
  | right _ => 0
  end.


Lemma w2p_later w (W: regular_write' (trace_labels w)):
  w < write2prop w.
Proof.
  remember (trace_labels w) as tlab.
  unfold write2prop.
  destruct (excluded_middle_informative (regular_write' (trace_labels w))); [clear W| by vauto].  
  destruct (constructive_indefinite_description _ _) as [p [PROP CORR]]. simpl.
  pose proof (Nat.lt_trichotomy w p). des; auto.
  { subst. red in PROP. exfalso. 
    apply reg_write_structure in r. destruct r as [thread [index [loc [val H]]]].
    rewrite H in PROP. red in PROP. by desc. }
  exfalso. rename H into LT. 
  apply reg_write_structure in r. destruct r as [thread [index [loc [val TLAB]]]].
  forward eapply (buffer_size thread (p + 1)) as BUF_SIZE.
  { contra GE. forward eapply (proj2 (ge_default p)) as P_DEF. 
    { red. intros. apply GE. simpl. red in H. destruct tr; vauto.
      simpl in *. lia. }
    red in PROP. rewrite P_DEF in PROP.
    generalize PROP. unfolder'. intuition. }
  red in CORR.
  assert (same_thread (trace_labels w) = in_thread thread) as RESTR_EQUIV. 
  { apply set_extensionality. rewrite TLAB. simpl.
    unfold same_thread, in_thread. simpl. red. splits; red; ins; desc; vauto. }
  rewrite RESTR_EQUIV in CORR.
  replace (count_upto (is_prop ∩₁ in_thread thread) (p + 1)) with ((count_upto (is_prop ∩₁ in_thread thread) p) + 1) in BUF_SIZE.
  2: { unfold count_upto.
       rewrite Nat.add_1_r with (n := p), seqS, Nat.add_0_l.
       rewrite map_app, filterP_app, length_app. simpl.
       rewrite RESTR_EQUIV in PROP.
       destruct (excluded_middle_informative ((is_prop ∩₁ in_thread thread) (trace_nth p tr def_lbl))); vauto. }
  rewrite <- CORR in BUF_SIZE.
  cut (count_upto (regular_write' ∩₁ in_thread thread) (p + 1) <= count_upto (regular_write' ∩₁ in_thread thread) w).
  { ins. lia. }
  apply count_upto_more. lia. 
Qed. 
  

Definition vis (e: Event) :=
  match (excluded_middle_informative (is_regular_write' e)) with
  | left W => write2prop (trace_index e)
  | right _ => (trace_index e)
  end. 

Definition vis_lt := is_init × Eninit ∪ ⦗Eninit⦘ ⨾ (fun x y => vis x < vis y) ⨾ ⦗Eninit⦘. 

Lemma vis_SPO:
  strict_partial_order vis_lt. 
Proof.
  unfold vis_lt, map_rel. 
  red. split. 
  { apply irreflexive_union. split.
    { red. ins. red in H. desc. by apply (proj1 Eninit_non_init x). }
    red. ins. apply seq_eqv_lr in H. desc. lia. }
  apply transitiveI.
  rewrite seq_union_l. apply inclusion_union_l.
  { apply inclusion_union_r1_search. red. ins.
    red in H. desc. red in H. desc.
    red. red in H0. des.
    { red in H0. by desc. }
    apply seq_eqv_lr in H0. by desc. }
  apply inclusion_union_r2_search.
  rewrite seq_union_r.
  rewrite !seqA. arewrite (⦗Eninit⦘ ⨾ is_init × Eninit ⊆ ∅₂).
  { generalize Eninit_non_init. basic_solver. }
  rewrite !seq_false_r, union_false_l.
  hahn_frame_l. hahn_frame_r. rewrite !inclusion_seq_eqv_l.
  red. ins. red in H. desc. lia. 
Qed. 

Lemma TI_LE_VIS e (ENINIT: Eninit e): trace_index e <= vis e.
Proof.
  unfold vis. simpl.
  destruct (excluded_middle_informative (is_regular_write' e)); [| lia]. 
  apply Nat.lt_le_incl. apply w2p_later.
  unfold trace_labels. rewrite trace_index_simpl; auto.  
Qed.

(* Lemma mem_read_source: *)
(*   let st := trace_states tr TR in *)
(*   forall i loc val (MEM: fst (st i) loc = val), *)
(*   exists thread iw ip t_iw, *)
(*     ⟪PROP_BEFORE: ip <= i⟫ /\ *)
(*     ⟪NTH_THREAD_WRITE:  ⟫ *)

Lemma r_vis e (Rr: is_r e): vis e = trace_index e.
Proof.
  unfold vis.
  generalize Rr. unfolder'. destruct e; vauto. destruct l; ins.
  all: destruct (excluded_middle_informative _ ); intuition. 
Qed. 

Definition exact_tid e := match e with
                          | InitEvent _ => 0
                          | ThreadEvent thread _ _ => thread
                          end.


Definition rf' w r :=
  let (_, bufs) := (state_before_event r) in
  match filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) (loc r))
               (bufs (exact_tid r)) with
  | nil => latest_of_by (fun e => loc e = loc r /\ vis_lt e r /\ EG e /\ is_w e) vis_lt w
  | _ => latest_of_by (fun e => loc e = loc r /\ trace_before e r /\ exact_tid e = exact_tid r /\ Eninit e /\ is_w e) trace_before w
  end. 

Definition nth_such n S i := count_upto S i = n /\ S (trace_labels i).

Lemma rmw_vis e (RMW: is_rmw e): vis e = trace_index e.
Proof.
  unfold vis.
  destruct (excluded_middle_informative (is_regular_write' e)); auto.
  exfalso. do 2 red in i. desc. apply i0. red. vauto. 
Qed.

Lemma regw_vis e (RMW: is_regular_write' e): vis e = write2prop (trace_index e). 
Proof.
  unfold vis.
  destruct (excluded_middle_informative (is_regular_write' e)); vauto.
Qed.

Lemma RESTR_EQUIV thread index lbl:
  same_thread (inl (ThreadEvent thread index lbl)) = in_thread thread.
Proof.
  ins. apply set_extensionality. 
  unfold same_thread, in_thread. simpl. red. splits; red; ins; desc; vauto.
Qed. 


Lemma w2p_regw w thread (REG: regular_write' (inl w))
      (TID: tid w = thread) (E'w: Eninit w):
  (is_prop ∩₁ in_thread thread) (trace_nth (write2prop (trace_index w)) tr def_lbl).
Proof.
  unfold write2prop. destruct (excluded_middle_informative _).
  2: { generalize REG, n. rewrite trace_index_simpl'; auto. intuition. }
  destruct (constructive_indefinite_description _ _). desc. simpl in *.
  rewrite trace_index_simpl' in *; auto.
  apply reg_write_structure in r. desc. inversion r. subst. 
  erewrite <- RESTR_EQUIV; eauto.
Qed. 

Lemma ti_uniq i j thread ind lbl (EQ: trace_nth i tr def_lbl = trace_nth j tr def_lbl)
      (EVENT: trace_nth i tr def_lbl = inl (ThreadEvent thread ind lbl)):
  i = j.
Proof.
  fold (trace_labels i) in EQ, EVENT. fold (trace_labels j) in EQ. 
  pose proof WF as WF'. 
  red in WF'. specialize WF' with (d := def_lbl) (thread := thread) (lbl1 := lbl) (lbl2 := lbl). 
  pose proof (Nat.lt_trichotomy i j). des; auto; exfalso. 
  { specialize (@WF' i j ind ind H). forward eapply WF'; eauto; [| unfold trace_labels in *; congruence| lia].
    apply lt_nondefault. by rewrite <- EQ, EVENT. }
  { specialize (@WF' j i ind ind H). forward eapply WF'; eauto; [| unfold trace_labels in *; congruence| lia].
    apply lt_nondefault. by rewrite EVENT. }
Qed.

Lemma ti_infer ind thread index lbl
      (TRACE: trace_nth ind tr def_lbl = inl (ThreadEvent thread index lbl)):
  trace_index (ThreadEvent thread index lbl) = ind.
Proof.
  forward eapply ti_uniq with (i := ind) (j := trace_index (ThreadEvent thread index lbl)); eauto.
  rewrite trace_index_simpl; auto.
  red. rewrite <- TRACE. apply trace_nth_in.
  apply lt_nondefault. unfold trace_labels. rewrite TRACE. vauto.
Qed.

Lemma nth_such_self (F: TSO_label -> Prop) i (Fi: F (trace_labels i)):
  nth_such (count_upto F i) F i.
Proof.
  red. split; auto.
Qed. 


Lemma buffer_sources i thread (DOM: NOmega.lt_nat_l i (trace_length tr)):
  let buf := snd (states i) thread in
  let ip := count_upto (is_prop ∩₁ in_thread thread) i in
  forall k l v (AT_K: Some (l, v) = nth_error buf k),
  exists ind,
    let lab_w := ThreadEvent thread ind (Astore l v) in
    let w := trace_index lab_w in 
    ⟪ WRITE_POS: nth_such (ip + k) (regular_write' ∩₁ in_thread thread) w ⟫ /\
    (* ⟪ WRITE_VALUE: trace_labels w =  ⟫ /\ *)
    ⟪ WRITE_BEFORE: w < i ⟫ /\
    ⟪ PROP_AFTER: i <= write2prop w ⟫ /\
    ⟪ ENINIT: Eninit lab_w ⟫. 
Proof.
  induction i.
  { ins. rewrite <- TS0 in AT_K. simpl in AT_K. unfold empty_buffer in AT_K. by destruct k. }
  simpl in *. ins.
  assert (NOmega.lt_nat_l i (trace_length tr)) as DOM'.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  specialize (IHi DOM').

  assert (Some (l, v) = nth_error (snd (states i) thread) k ->
          ~ (is_prop ∩₁ in_thread thread) (trace_nth i tr def_lbl) ->
          exists ind : nat,
            nth_such (count_upto (is_prop ∩₁ in_thread thread) (S i) + k)
                     (regular_write' ∩₁ in_thread thread)
                     (trace_index (ThreadEvent thread ind (Astore l v))) /\
            trace_index (ThreadEvent thread ind (Astore l v)) < S i /\
            S i <= write2prop (trace_index (ThreadEvent thread ind (Astore l v))) /\
            Eninit (ThreadEvent thread ind (Astore l v))) as SAME.
  { ins. specialize (IHi k l v). specialize_full IHi; [congruence| ].
    desc. exists ind. splits; vauto.
    { cut (count_upto (is_prop ∩₁ in_thread thread) (S i) = count_upto (is_prop ∩₁ in_thread thread) i); [congruence| ].
      rewrite count_upto_next, check0; [lia| ]. auto. }
    apply le_lt_or_eq in PROP_AFTER. des; [lia| ].
    forward eapply (@w2p_regw (ThreadEvent thread ind (Astore l v)) thread) as W2P_PROP; try (by vauto).
    unfolder'. intuition. }
    
  forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
  inversion TSi.
  { apply SAME; [congruence| ]. rewrite <- H. unfolder'. intuition. }
  { apply SAME; [congruence| ]. rewrite <- H. unfolder'. intuition. }
  { rewrite <- H2 in AT_K. simpl in AT_K.
    destruct (classic (thread0 = thread)).
    2: { rewrite updo in AT_K; auto.
         apply SAME; [by rewrite <- H0| ].
         rewrite <- H. unfolder'. intuition. }
    subst thread0. 
    rewrite upds in AT_K.
    assert (k <= length (bufs thread)) as W_POS.
    { forward eapply (proj1 (nth_error_Some (bufs thread ++ (loc, val) :: nil) k)).
      { apply opt_val. eauto. }
      rewrite length_app. simpl. lia. }
    apply le_lt_or_eq in W_POS. des.
    { apply SAME.
      { rewrite nth_error_app1 in AT_K; auto. by rewrite <- H0. }
      rewrite <- H. unfolder'. intuition. }
    exists index.
    assert (l = loc /\ v = val).  
    { rewrite W_POS in AT_K. rewrite nth_error_app2 in AT_K; [| lia].
      rewrite Nat.sub_diag in AT_K. simpl in AT_K. by inversion AT_K. }
    desc. subst loc val.
    forward eapply (ti_infer i) as IND; eauto. 
    splits.
    { forward eapply (buffer_size thread (i)) as BUF_SIZE.
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      simpl in BUF_SIZE. rewrite W_POS.
      rewrite count_upto_next, check0.
      2: { unfold trace_labels. rewrite <- H. unfolder'. intuition. }
      rewrite Nat.add_0_r.
      rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE. rewrite <- BUF_SIZE.
      rewrite IND. apply nth_such_self.
      unfold trace_labels. rewrite <- H. unfolder'. intuition. }
    { lia. }
    { rewrite IND. forward eapply (w2p_later i) as LATER.
      { unfold trace_labels. rewrite <- H. unfolder'. intuition. }
      lia. }
    red. rewrite H. apply trace_nth_in. auto. }
  { destruct (classic (thread0 = thread)).
    2: { apply SAME.
         { rewrite <- H0. by rewrite <- H2 in AT_K. }
         rewrite <- H. unfolder'. intuition. }
    subst thread0. rewrite <- H2 in AT_K. simpl in AT_K.
    rewrite NO_BUF in AT_K. by destruct k. }
  { destruct (classic (thread0 = thread)).
    2: { apply SAME.
         { rewrite <- H0. simpl.
           rewrite <- H2 in AT_K. simpl in AT_K. rewrite updo in AT_K; auto. }
         rewrite <- H. unfolder'. intuition. vauto. }
    subst thread0.
    rewrite <- H2 in AT_K. simpl in AT_K. rewrite upds in AT_K.
    specialize (IHi (S k) l v). specialize_full IHi. 
    { rewrite <- H0. simpl. by rewrite BUF. }
    desc. exists ind.
    splits; vauto.
    { replace (count_upto (is_prop ∩₁ in_thread thread) (S i)) with (count_upto (is_prop ∩₁ in_thread thread) i + 1).
      { by rewrite <- NPeano.Nat.add_assoc, Nat.add_1_l. }
      rewrite count_upto_next, check1; auto.
      unfold trace_labels. by rewrite <- H. }
    apply le_lt_or_eq in PROP_AFTER. des; [done| ].

    exfalso.
    unfold write2prop in PROP_AFTER. destruct (excluded_middle_informative _).
    2: { generalize n. rewrite trace_index_simpl'; auto. unfolder'. intuition. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    rewrite trace_index_simpl' in *; auto.
    rewrite RESTR_EQUIV in *. subst x.
    red in WRITE_POS. desc. lia. }
Qed. 
    
Lemma W_SPLIT w (Ww: is_w w) (E'w: Eninit w):
  is_regular_write' w /\ vis w = write2prop (trace_index w) \/
  is_rmw w /\ vis w = trace_index w. 
Proof.
  ins. destruct (classic (is_regular_write' w)).
  { left. split; auto. unfold vis, write2prop.
    destruct (excluded_middle_informative _ ); vauto. }
  assert (is_rmw w).
  { generalize Ww, H. unfolder'. destruct w.
    { by destruct (proj1 Eninit_non_init (InitEvent x)). }
    destruct l; intuition. }  
  right. split; auto. 
  rewrite rmw_vis; auto.
Qed.   
    
Definition G :=
  {| acts := EG;
     co := ⦗EG ∩₁ is_w⦘ ⨾ restr_eq_rel Events.loc vis_lt ⨾ ⦗EG ∩₁ is_w⦘;     
     rf := ⦗EG ∩₁ is_w⦘ ⨾ rf' ⨾ ⦗EG ∩₁ is_r⦘ |}.

Lemma nonreg_rmw w (Ww: is_w w) (E'w: Eninit w) (NONREG: ~ is_regular_write' w):
  is_rmw w.
Proof.
  generalize Ww NONREG. unfolder'. destruct w.
  { by destruct (proj1 Eninit_non_init (InitEvent x)). }
  destruct l; vauto. intuition.
Qed. 

Lemma vis_lt_init_helper x y (SB: sb G x y): vis_lt x y \/ (Eninit x /\ Eninit y).
Proof.
  unfold sb in SB. apply seq_eqv_lr in SB. destruct SB as [Ex [SBxy Ey]]. ins.  
  do 2 red in Ex. des.
  { do 2 red in Ey. des; vauto.
    red in SBxy. destruct x, y; vauto. }
  do 2 red in Ey. des.
  { red in SBxy. destruct x, y; vauto. }
  vauto.
Qed.

Lemma vis_respects_sb_w: restr_rel is_w (sb G) ⊆ vis_lt.
Proof.
  unfold restr_rel. red. ins. destruct H as [SBxy [Wx Wy]].
  destruct (vis_lt_init_helper SBxy) as [|[E'x E'y]]; auto. 
  red. red. right. apply seq_eqv_lr. splits; auto.
  red in SBxy. apply seq_eqv_lr in SBxy. destruct SBxy as [_ [SBxy _]].
  forward eapply (proj1 tb_respects_sb x y) as H; [basic_solver| ].
  apply seq_eqv_lr in H. destruct H as [_ [[TBxy TIDxy] _]]. 
  (* apply tb_respects_sb in SBxy. destruct SBxy as [TBxy TIDxy].  *)
  red in TBxy.
  unfold vis. destruct (excluded_middle_informative _) as [X | X]; destruct (excluded_middle_informative _) as [Y | Y]; auto. 
  3: { apply lt_trans with (m := trace_index y); auto. apply w2p_later.
       unfold trace_labels. rewrite trace_index_simpl; auto. }
  { unfold write2prop. destruct (excluded_middle_informative _); vauto.
    2: { unfold trace_labels in n. rewrite trace_index_simpl in n; vauto. }
    destruct (excluded_middle_informative _); vauto.
    2: { unfold trace_labels in n. rewrite trace_index_simpl in n; vauto. }
    destruct (constructive_indefinite_description _ _) as [px Px].
    destruct (constructive_indefinite_description _ _) as [py Py].
    simpl in *. desc.
    unfold trace_labels in *. rewrite !trace_index_simpl in *; auto.
    assert (exists thread, same_thread (inl x) = in_thread thread /\ same_thread (inl y) = in_thread thread).
    { pose proof (reg_write_structure _ r). desc. inv H. 
      pose proof (reg_write_structure _ r0). desc. inv H0. 
      red in TIDxy. simpl in TIDxy. inv TIDxy.
      exists thread0. 
      split; apply RESTR_EQUIV. }
    desc. rewrite H, H0 in *. 
    assert (count_upto (regular_write' ∩₁ in_thread thread) (trace_index x) < count_upto (regular_write' ∩₁ in_thread thread) (trace_index y)).
    { subst. apply Nat.lt_le_trans with (m := count_upto (regular_write' ∩₁ in_thread thread) (trace_index x + 1)).
      2: { eapply count_upto_more. lia. }
      rewrite Nat.add_1_r, count_upto_next.
      rewrite check1; [lia|].
      unfold trace_labels. rewrite trace_index_simpl; auto. red. split; auto.
      rewrite <- H. unfold same_thread. generalize r. destruct x. unfolder'. intuition. vauto. } 
    apply lt_diff in H1. desc. rewrite W_P_CORR0, W_P_CORR in H1. 
    destruct (NPeano.Nat.lt_ge_cases px py); auto. 
    pose proof (count_upto_more (is_prop ∩₁ in_thread thread) H2). lia. }
  destruct (NPeano.Nat.lt_ge_cases (write2prop (trace_index x)) (trace_index y)) as [| LE]; auto.
  exfalso.
  forward eapply (@reg_write_structure (inl x)) as H. 
  { vauto. }
  desc. inversion H. clear H.  
  destruct y.
  { exfalso. by apply (proj1 Eninit_non_init (InitEvent x0)). }
  destruct l; vauto.
  assert (thread0 = thread); [|subst thread0]. 
  { red in TIDxy. vauto. }
  remember (ThreadEvent thread index0 (Armw x0 vr vw)) as tlab. 
  assert (NOmega.lt_nat_l (trace_index tlab) (trace_length tr)) as DOM. 
  { contra GE. apply ge_default in GE.
    unfold trace_labels in GE. rewrite trace_index_simpl in GE; auto. 
    rewrite Heqtlab in GE. discriminate GE. }
  set (st := states (trace_index tlab)).
  forward eapply (TSi (trace_index tlab)) with (d := def_lbl) as TSi; eauto. 
  rewrite trace_index_simpl in TSi; auto.
  rewrite Heqtlab in TSi at 2. inversion TSi. subst. 
  remember (ThreadEvent thread index0 (Armw x0 (sh_mem x0) vw)) as e_rmw. 
  remember (ThreadEvent thread index (Astore loc val)) as e_w.
  forward eapply (@buffer_size thread (trace_index e_rmw)) as BUF_SIZE. 
  { destruct (trace_length tr); auto. simpl in *. lia. }
  simpl in BUF_SIZE. rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE.
  rewrite NO_BUF in BUF_SIZE. simpl in BUF_SIZE. rewrite Nat.add_0_r in BUF_SIZE.
  remember (write2prop (trace_index e_w)) as vis_w. 
  assert (count_upto (regular_write' ∩₁ same_thread (trace_labels (trace_index e_w))) (trace_index e_w) =
          count_upto (is_prop ∩₁ same_thread (trace_labels (trace_index e_w))) vis_w) as VIS_W.
  { subst vis_w. unfold write2prop in *. destruct (excluded_middle_informative _).
    2: { generalize n, X. rewrite trace_index_simpl'; auto. by unfolder'. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    lia. }
  replace (same_thread (trace_labels (trace_index e_w))) with (in_thread thread) in VIS_W.
  2: { rewrite trace_index_simpl'; auto. subst e_w. by rewrite RESTR_EQUIV. }
  assert (count_upto (regular_write' ∩₁ in_thread thread) (trace_index e_w) < count_upto (regular_write' ∩₁ in_thread thread) (trace_index e_rmw)) as MORE_WRITES.
  { unfold lt. rewrite <- Nat.add_1_r.
    rewrite <- (@check1 _ (regular_write' ∩₁ in_thread thread) (trace_labels ((trace_index e_w)))).
    2: { red. rewrite trace_index_simpl'; auto. by subst e_w. }
    rewrite <- count_upto_next. apply count_upto_more. lia. }
  assert (count_upto (is_prop ∩₁ in_thread thread) (trace_index e_rmw) <= count_upto (is_prop ∩₁ in_thread thread) vis_w) as MORE_PROPS.
  { apply count_upto_more. lia. }
  lia. 
Qed.
  
  
Lemma rf_before_prop w r (RF: rf G w r)
      (BUF:   let (_, bufs) := (state_before_event r) in
              filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) (loc r))
                     (bufs (exact_tid r)) <> nil):
  trace_index r < vis w.
Proof.
  simpl in RF. apply seq_eqv_lr in RF. destruct RF as [[E'w Ww] [RF [E'r Rr]]].
  do 2 red in E'r. des.
  { edestruct init_non_r; eauto. }
  remember (state_before_event r) as st. destruct st as [mem bufs].
  red in RF. rewrite <- Heqst in RF.
  remember (filter (fun loc_val : Loc * Val => fst loc_val =? loc r)
                   (bufs (exact_tid r))) as buf_flt.
  destruct buf_flt; [done| ].
  rename buf_flt into h. remember (p :: h) as buf_flt. clear Heqbuf_flt0.  
  clear E'w. red in RF. destruct RF as [[LOC [TBwr [TID [E'w _]]]] LATEST].
  contra BEFORE. apply not_lt in BEFORE. red in BEFORE.
  apply le_lt_or_eq in BEFORE. des.
  2: { assert (trace_labels (vis w) = trace_labels (trace_index r)) by auto.
       rewrite trace_index_simpl' in H; auto.
       unfold vis in H. destruct (excluded_middle_informative _).
       2: { rewrite rmw_vis in BEFORE; [| apply nonreg_rmw; auto]. red in TBwr. lia. }
       unfold write2prop in H. destruct (excluded_middle_informative _).
       2: { generalize i, n. rewrite trace_index_simpl'; auto. }
       destruct (constructive_indefinite_description _ _). desc. simpl in *.
       generalize THREAD_PROP, Rr. rewrite H. unfolder'. intuition. }
  assert (exists flt_ind val, Some (loc r, val) = nth_error buf_flt flt_ind) as FLT_POS. 
  { destruct buf_flt; [vauto| ]. exists 0. destruct p0. exists v. simpl.
    do 2 f_equal.
    assert (In (l, v) (filter (fun loc_val : Loc * Val => fst loc_val =? loc r)
                              (bufs (exact_tid r)))).
    { by rewrite <- Heqbuf_flt. }
    apply in_filter_iff in H. desc. simpl in H0. by apply beq_nat_true in H0. }
  desc.
  remember (bufs (exact_tid r)) as buf. 
  assert (exists buf_ind, Some (loc r, val) = nth_error buf buf_ind) as BUF_POS.
  { symmetry in FLT_POS. apply nth_error_In in FLT_POS.
    rewrite Heqbuf_flt in FLT_POS. apply in_filter_iff in FLT_POS. desc.
    apply In_nth_error in FLT_POS. desc. eauto. }
  desc. 
  forward eapply (@buffer_sources (trace_index r) (exact_tid r)) with (k := buf_ind) (l := (loc r)) (v := val) as [w_ind SOURCE].
  { apply lt_nondefault. rewrite trace_index_simpl'; auto.
    generalize Rr. unfolder'. destruct r; vauto. } 
  { unfold state_before_event in Heqst. rewrite <- Heqst. simpl. vauto. } 
  simpl in SOURCE. desc. remember (ThreadEvent (exact_tid r) w_ind (Astore (loc r) val)) as w'.

  specialize (LATEST w'). specialize_full LATEST.
  { splits; vauto. }

  red in LATEST. des.
  { subst w'. red in TBwr. rewrite LATEST in *.
    rewrite regw_vis in BEFORE.
    2: { subst. unfolder'. intuition. }
    lia. }

  forward eapply (@vis_respects_sb_w w' w) as VISw'w.
  { red. splits; try (by vauto). red. apply seq_eqv_lr. splits; auto.
    1,3: by (simpl; unfold EG; vauto).
    forward eapply (proj2 tb_respects_sb w' w) as TB.
    2: { apply seq_eqv_lr in TB. by desc. }
    apply seq_eqv_lr. splits; auto. 
    split; auto. 
    red. unfold exact_tid in TID. 
    subst w'. destruct w, r; vauto.
    (* simpl in *. destruct (proj1 Eninit_non_init (InitEvent x)); vauto. *) }
  do 2 red in VISw'w. des.
  { red in VISw'w. desc. destruct (proj1 Eninit_non_init w'); vauto. }
  apply seq_eqv_lr in VISw'w. desc.
  rewrite regw_vis in VISw'w0; [| subst w'; unfolder'; intuition].  
  lia. 
Qed. 


Definition proj_ev (x: TSO_label) := match x with | inl e => e | inr _ => InitEvent 0 end.


Lemma fsupp_vis_loc: fsupp (restr_eq_rel loc vis_lt).
Proof.
  red. ins. 
  set (extract_event := fun i => proj_ev (trace_labels i)). 
  exists (InitEvent (loc y) :: map extract_event (List.seq 0 (vis y))).
  ins. desc.
  red in REL. desc. do 2 red in REL. des.
  { left. red in REL. desc. 
    destruct x; vauto. rewrite <- REL0. by unfold loc, loc_l. }
  right. 
  apply seq_eqv_lr in REL. desc. 
  replace x with (extract_event (trace_index x)).
  2: { unfold extract_event. unfold trace_labels. by rewrite trace_index_simpl. }
  apply in_map. apply in_seq0_iff.
  apply le_lt_trans with (m := vis x); auto. by apply TI_LE_VIS. 
Qed. 

Lemma vis_inj x y (E'x: Eninit x) (E'y: Eninit y) (VIS_EQ: vis x = vis y): x = y.
Proof.
  unfold vis in VIS_EQ.
  destruct (excluded_middle_informative (is_regular_write' x)) as [X | X]; destruct (excluded_middle_informative (is_regular_write' y)) as [Y | Y].
  2: { unfold write2prop in VIS_EQ. 
       destruct (excluded_middle_informative _).
       2: { rewrite trace_index_simpl' in n; vauto. }
       destruct (constructive_indefinite_description _ _). desc. simpl in *.
       rewrite VIS_EQ, !trace_index_simpl' in THREAD_PROP; auto.
       generalize THREAD_PROP. unfolder'. intuition. }
  2: { unfold write2prop in VIS_EQ. 
       destruct (excluded_middle_informative _).
       2: { rewrite trace_index_simpl' in n; vauto. }
       destruct (constructive_indefinite_description _ _). desc. simpl in *.
       rewrite <- VIS_EQ, !trace_index_simpl' in THREAD_PROP; auto.
       generalize THREAD_PROP. unfolder'. intuition. }
  2: { apply ti_inj; vauto. }
  unfold write2prop in VIS_EQ. 
  do 2 destruct (excluded_middle_informative _).
  all: try (rewrite trace_index_simpl' in *; vauto).
  do 2 destruct (constructive_indefinite_description _ _). desc. simpl in *.
  subst. rewrite trace_index_simpl' in *; auto.
  pose proof (reg_write_structure _ r). pose proof (reg_write_structure _ r0).
  desc. inversion H. inversion H0. subst.
  rewrite RESTR_EQUIV in *. 
  remember (ThreadEvent thread0 index0 (Astore loc0 val0)) as w1.
  remember (ThreadEvent thread index (Astore loc val)) as w2.
  assert (thread0 = thread); [| subst thread0]. 
  { generalize THREAD_PROP0, THREAD_PROP. unfolder'.
    destruct (trace_labels x1); vauto; intuition. congruence. }
  rewrite <- W_P_CORR0 in W_P_CORR.
  pose proof (Nat.lt_trichotomy (trace_index w1) (trace_index w2)). des.
  2: { apply ti_inj; vauto. }
  { apply lt_diff in H1. desc. rewrite H1 in W_P_CORR.
    assert (count_upto (regular_write' ∩₁ in_thread thread) (S (trace_index w1)) = count_upto (regular_write' ∩₁ in_thread thread) (trace_index w1) + 1).
    { rewrite count_upto_next. rewrite check1; [lia| ].
      rewrite trace_index_simpl'; auto. red. splits; vauto. }
    forward eapply (@count_upto_more (S (trace_index w1)) (trace_index w1 + S d)(regular_write' ∩₁ in_thread thread)) as LE; lia. }
  { apply lt_diff in H1. desc. rewrite H1 in W_P_CORR.
    assert (count_upto (regular_write' ∩₁ in_thread thread) (S (trace_index w2)) = count_upto (regular_write' ∩₁ in_thread thread) (trace_index w2) + 1).
    { rewrite count_upto_next. rewrite check1; [lia| ].
      rewrite trace_index_simpl'; auto. red. splits; vauto. }
    forward eapply (@count_upto_more (S (trace_index w2)) (trace_index w2 + S d)(regular_write' ∩₁ in_thread thread)) as LE; lia. }
Qed. 

Lemma co_loc_total l:
  strict_total_order (EG ∩₁ is_w ∩₁ (fun a => loc a = l)) (co G). 
Proof.
  red. split.
  { red. split.
    { red. ins. apply seq_eqv_lr in H. desc.
      red in H0. desc. do 2 red in H0. des.
      { by apply (proj1 Eninit_non_init x). }
      apply seq_eqv_lr in H0. desc. lia. }
    { simpl. red. ins. apply seq_eqv_lr in H. apply seq_eqv_lr in H0. desc.
      apply seq_eqv_lr. splits; auto.
      red in H3, H1. desc. red. split; [| congruence].
      red in H3, H1. red in H3, H1. des.
      { red in H3, H1. desc. vauto. }
      { apply seq_eqv_lr in H3. red in H1. desc. destruct (proj1 Eninit_non_init y); vauto. }
      { red in H3. apply seq_eqv_lr in H1. desc. red. left. red. vauto. }
      apply seq_eqv_lr in H3. apply seq_eqv_lr in H1. desc. red. right.
      apply seq_eqv_lr. splits; auto. lia. } }
  red. intros x [[Ex Wx] Lx] y [[Ey Wy] Ly] NEQ.
  simpl in Ex, Ey. do 2 red in Ex, Ey. des.
  { destruct x, y; vauto. unfold loc, loc_l in Ly. simpl in Ly. by subst. }
  { right. simpl. apply seq_eqv_lr. splits; vauto. }
  { left. simpl. apply seq_eqv_lr. splits; vauto. }
  pose proof (Nat.lt_trichotomy (vis x) (vis y)). des.
  2: { forward eapply (vis_inj x y); vauto. }
  { left. simpl. apply seq_eqv_lr. splits; vauto. red. split; auto.
    red. right. apply seq_eqv_lr. splits; auto. }  
  { right. simpl. apply seq_eqv_lr. splits; vauto. red. split; auto.
    red. right. apply seq_eqv_lr. splits; auto. }
Qed.


Lemma no_writes_no_buffer thread l i (DOM: NOmega.lt_nat_l i (trace_length tr))
      (NO_LOC_WRITES: forall e, ~ (loc e = l /\ trace_index e < i /\
                              i <= write2prop (trace_index e) /\
                              exact_tid e = thread /\ Eninit e /\ is_w e)):
  let buf := snd (states i) thread in
  filter (fun loc_val: Loc * Val => fst loc_val =? l) buf = nil.
Proof.
  simpl. 
  remember (filter (fun loc_val : Loc * Val => fst loc_val =? l)
                   (snd (states i) thread)) as buf_flt.
  apply length_zero_iff_nil. destruct (Nat.eq_0_gt_0_cases (length buf_flt)) as [| NEMPTY]; [vauto|]. exfalso.
  apply lt_diff in NEMPTY. desc.
  assert (exists elt, Some elt = nth_error buf_flt d) as [elt NTH_FLT]. 
  { forward eapply (proj2 (nth_error_Some buf_flt d)); [lia| ].
    destruct (nth_error buf_flt d); vauto. }
  forward eapply nth_error_In as IN_FLT; eauto.
  rewrite Heqbuf_flt in IN_FLT. apply in_filter_iff in IN_FLT. desc.
  apply In_nth_error in IN_FLT. desc.
  destruct elt as (l0, v).
  remember (states i) as st. destruct st as [mem bufs]. simpl in *. 
  simpl in *. apply beq_nat_true in IN_FLT0. subst.

  forward eapply (@buffer_sources i thread DOM n l v) as [ind H].
  { by rewrite <- IN_FLT, <- Heqst. }
  simpl in H. desc.
  apply (NO_LOC_WRITES (ThreadEvent thread ind (Astore l v))).
  splits; auto.
Qed. 
  
Lemma read_source r (Er: EG r) (Rr: is_r r):
  exists! w, rf G w r.
Proof.
  cut ((exists! w, (EG ∩₁ is_w) w /\ rf' w r) /\ (EG ∩₁ is_r) r).
  { ins. unfold unique in H. desc.
    exists x. red. splits.
    { apply seq_eqv_lr. splits; auto. }
    ins. desc. apply seq_eqv_lr in H3. desc. apply H1. splits; auto. }
  split; [| vauto].
  unfold rf'.
  do 2 red in Er. des.
  { exfalso. eapply init_non_r; eauto. }
  (* red in Er. pose proof Er as Er_.  *)
  (* apply trace_in_nth with (d := def_lbl) in Er. desc. *)
  unfold state_before_event.
  forward eapply (TSi (trace_index r)) with (d := def_lbl) as TSi; eauto.
  { contra GE.
    pose proof (proj2 (ge_default (trace_index r)) GE).
    unfold def_lbl in H. by rewrite trace_index_simpl' in H; vauto. }
  
  rewrite trace_index_simpl in TSi; auto.
  destruct r; vauto. simpl.
  remember (ThreadEvent thread index l) as r.
  (* destruct (bufs thread) eqn:BUF. *)
  remember (states (trace_index r)) as st. destruct st as [mem bufs].
  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (bufs thread)) eqn:BUF.
  { remember (fun e : Event => loc e = loc r /\ vis_lt e r /\ EG e /\ is_w e) as writes.
    cut (exists! w, latest_of_by writes (co G) w).
    { subst writes. intros [w [LATEST UNIQ]]. red in LATEST. desc.
      exists w. red. split.
      { split; vauto.
        red. splits; vauto. intros. specialize (LATEST0 y S').
        red in LATEST0. des; [vauto| ]. simpl in LATEST0. apply seq_eqv_lr in LATEST0. desc. red in LATEST4. desc. vauto. }
      ins. desc. red in H0. desc. apply UNIQ. red. splits; vauto.
      ins. specialize (H1 y S').
      red in H1. des; [vauto| ].
      red. right. apply seq_eqv_lr. splits; vauto.
      red. split; auto. congruence. }
    apply latest_unique.
    { apply antisymmetric_inclusion with (r := co G); [| basic_solver].
      apply strict_partial_order_antisymmetric.
      by destruct (co_loc_total (loc r)). }
    assert (set_finite writes) as WRITES_FIN.
    { arewrite (writes ⊆₁ fun e => loc e = loc r /\ vis_lt e r) by basic_solver.
      pose proof (fsupp_vis_loc r) as [findom FINDOM].
      red. exists findom. ins. desc. apply FINDOM. red. split; auto. }
    assert (~ writes ≡₁ ∅) as HAS_WRITES.
    { apply set_nonemptyE. exists (InitEvent (loc r)).
      subst. splits; vauto. }
    assert (strict_total_order writes (co G)) as TOTAL.
    { red. split.
      { by destruct (co_loc_total (loc r)). }
      forward eapply (@is_total_mori _ (EG ∩₁ is_w ∩₁ (fun a => loc a = loc r)) writes) as H.
      { subst. unfold Basics.flip. basic_solver. }
      { eapply (inclusion_refl2 (co G)). }
      apply H, co_loc_total. }
    apply latest_fin; eauto. }
  remember (fun e : Event => loc e = loc r /\ trace_before e r /\ exact_tid e = thread /\  Eninit e /\ is_w e) as writes.
  cut (exists w, unique (latest_of_by writes trace_before) w).
  { ins. unfold unique in H. desc. red in H. desc.
    rewrite Heqwrites in H. desc.
    exists w. red. splits; vauto.
    ins. desc. red in H6. desc. apply H0. red. splits; vauto. }

  assert (set_finite writes) as WRITES_FIN.
  { apply set_finite_mori with (x := fun e => trace_before e r /\ Eninit e).
    { red. rewrite Heqwrites. basic_solver. }
    red.
    set (extract_event := fun i => match (trace_labels i) with
                                | inr _ => InitEvent 0
                                | inl e => e
                                end).
    exists (map extract_event (List.seq 0 (trace_index r))).
    ins. desc.
    replace x with (extract_event (trace_index x)).
    2: { unfold extract_event.
         unfold trace_labels. by rewrite trace_index_simpl. }
    apply in_map. by apply in_seq0_iff. }
  assert (~ writes ≡₁ ∅) as HAS_WRITES.
  { red. ins.
    forward eapply (@no_writes_no_buffer thread (loc r) (trace_index r)) as BUF_EMPTY; eauto.
    { contra GE. forward eapply (proj2 (ge_default (trace_index r))); auto.
      unfold trace_labels. rewrite trace_index_simpl, Heqr; auto. by unfolder'. }
    { ins. red. ins. desc.
      apply le_lt_or_eq in H2. des.
      2: { unfold write2prop in H2. destruct (excluded_middle_informative _).
           2: { lia. }
           destruct (constructive_indefinite_description _ _). simpl in *. desc.
           subst. rewrite trace_index_simpl' with (e := ThreadEvent _ _ _) in THREAD_PROP; auto.
           generalize THREAD_PROP. unfolder'. intuition. }
      apply (proj1 H e). rewrite Heqwrites. splits; auto. }
    simpl in BUF_EMPTY. rewrite <- Heqst in BUF_EMPTY. simpl in BUF_EMPTY.
    by rewrite BUF in BUF_EMPTY. }
  assert (strict_total_order writes trace_before) as TOTAL.
  { cdes tb_SPO.
    red. split; auto.
    forward eapply (@is_total_mori _ Eninit writes) as H.
    { red. basic_solver. }
    { eapply (inclusion_refl2 trace_before). }
      by apply H. }
  forward eapply (@latest_fin _ _ trace_before WRITES_FIN HAS_WRITES) as LATEST'; [vauto| ].
  apply latest_unique in LATEST'.
  2: { apply antisymmetric_inclusion with (r := trace_before); [| basic_solver].
       apply strict_partial_order_antisymmetric. by cdes tb_SPO. }
  unfold unique in LATEST'. desc. exists x. split; [vauto| ].
  red in LATEST'. desc. by rewrite Heqwrites in LATEST'. 
Qed. 
  

Lemma nth_such_unique k F i j (NTH_I: nth_such k F i) (NTH_J: nth_such k F j):
  i = j.
Proof.
  red in NTH_I, NTH_J. desc. 
  pose proof (Nat.lt_trichotomy i j) as LT. des; auto.
  { exfalso. apply lt_diff in LT. desc. subst.
    forward eapply (@count_upto_more (S i) (i + S d) F) as MORE; [lia| ].
    rewrite count_upto_next, check1 in MORE; auto. lia. }
  { exfalso. apply lt_diff in LT. desc. subst.
    forward eapply (@count_upto_more (S j) (j + S d) F) as MORE; [lia| ].
    rewrite count_upto_next, check1 in MORE; auto. lia. }  
Qed. 

Lemma no_vis_lt_init e l (VIS: vis_lt e (InitEvent l)): False.
Proof.
  do 2 red in VIS. des.
  { red in VIS. desc. by destruct (proj1 Eninit_non_init (InitEvent l)). }
  apply seq_eqv_lr in VIS. desc. by destruct (proj1 Eninit_non_init (InitEvent l)).
Qed.

Lemma winit_helper ind w l (DOM: NOmega.lt_nat_l ind (trace_length tr))
      (LATEST : latest_of_by
             (fun e' : Event =>
              loc e' = l /\ (is_init e' \/ vis e' < ind) /\ EG e' /\ is_w e')
             vis_lt w)
      (W_: is_init w): 
  fst (states ind) l = valw w.
Proof.
  red in LATEST. desc.
  destruct w; vauto. unfold loc, loc_l, valw. simpl in *. clear LATEST1. 
  generalize dependent DOM. generalize dependent LATEST0. induction ind.
  { ins.  by rewrite <- TS0. }
  ins.
  rewrite <- IHind.
  3: { destruct (trace_length tr); vauto. simpl in *. lia. }
  2: { ins. desc. apply LATEST0. splits; vauto. des; auto. }
  symmetry.
  forward eapply (TSi ind) with (d := def_lbl) as TSi. 
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  inversion TSi; try done.
  { simpl. destruct (classic (loc = x)).
    2: { rewrite updo; auto. }
    subst x. exfalso.
    remember (ThreadEvent thread index (Armw loc val_r val_w)) as rmw. 
    forward eapply (@ti_infer ind thread index (Armw loc (sh_mem loc) val_w))  as TI; [vauto| ].
    specialize (LATEST0 rmw).
    specialize_full LATEST0.
    { splits; try (by vauto). 
      { right. rewrite rmw_vis; vauto. }
      red. right. red. subst rmw. rewrite H. apply trace_nth_in.
      destruct (trace_length tr); vauto. simpl in *. lia. } 
    red in LATEST0. des; [vauto| ].
    eapply no_vis_lt_init; eauto. }
  simpl. destruct (classic (loc = x)).
  2: { rewrite updo; auto. }
  subst x. rewrite upds. 
  forward eapply (@buffer_sources ind thread) with (k :=0) (l := loc) (v := val) as [ind_w SRC].
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  { rewrite <- H0. simpl. by rewrite BUF. }
  simpl in SRC. desc.
  remember (ThreadEvent thread ind_w (Astore loc val)) as w. 
  specialize (LATEST0 w). specialize_full LATEST0.
  { splits; try (by vauto). right. cut (vis (ThreadEvent thread ind_w (Astore loc val)) = ind); [ins; subst w; lia| ].
    unfold vis. destruct (excluded_middle_informative _ ).
    2: { generalize n. unfolder'. intuition. }
    unfold write2prop. destruct (excluded_middle_informative _).
    2: { generalize n. rewrite trace_index_simpl'; vauto. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    rewrite trace_index_simpl', <- Heqw in *; try (by vauto).
    red in WRITE_POS. desc.
    replace (same_thread (inl w)) with (in_thread thread) in *.
    2: { symmetry. subst w. apply RESTR_EQUIV. }
    rewrite WRITE_POS, Nat.add_0_r in W_P_CORR.
    apply nth_such_unique with (k := count_upto (is_prop ∩₁ in_thread thread) ind) (F := is_prop ∩₁ in_thread thread); vauto.
    red. split; auto. unfold trace_labels. by rewrite <- H. }
  red in LATEST0. des; [vauto| ]. exfalso. eapply no_vis_lt_init; eauto. 
Qed. 


Lemma latest_mem_value_kept' ind w l
      (DOM: NOmega.lt_nat_l ind (trace_length tr))
      (LATEST: latest_of_by (fun e' => loc e' = l /\ (vis e' < ind) /\ EG e' /\ is_w e') vis_lt w):
  fst (states ind) l = valw w.
Proof.
  red in LATEST. desc. apply lt_diff in LATEST1. desc. rewrite LATEST1 in *.
  clear dependent ind.
  induction d.
  { assert (NOmega.lt_nat_l (vis w) (trace_length tr)) as DOM'.
    { destruct (trace_length tr); vauto. simpl in *. lia. }
    do 2 red in LATEST2. des.      
    { destruct w; vauto. 
      apply winit_helper; vauto. red. splits; vauto. ins. desc.
      des.
      { destruct y; vauto. unfold loc, loc_l in S'. simpl in S'. subst x0; auto. }
      apply LATEST0. splits; vauto. }
    destruct w.
    { by destruct (proj1 Eninit_non_init (InitEvent x)). }
    destruct l0; [done| | ].
    { remember (ThreadEvent thread index (Astore x v)) as w.      
      assert (vis w = write2prop (trace_index w)) as VISw.
      { apply regw_vis. subst w. unfolder'. intuition. }
      rewrite VISw in *. 
      forward eapply (TSi (vis w)) with (d := def_lbl) as TSi.
      { congruence. }
      assert ((is_prop ∩₁ same_thread (trace_labels (trace_index w))) (trace_nth (vis w) tr def_lbl)) as PROP.
      { unfold write2prop in VISw. destruct (excluded_middle_informative _).
        2: { generalize n. rewrite trace_index_simpl'; auto. subst w.
             unfolder'. intuition. }
        destruct (constructive_indefinite_description _ _). desc. simpl in *.
        subst x0. auto. }
      inversion TSi.
      all: try (by generalize PROP; rewrite <- H; unfolder'; intuition).
      assert (thread0 = thread); [| subst thread0].
      { red in PROP. desc.
        rewrite trace_index_simpl' in PROP0; auto. rewrite <- H in PROP0.
        subst w. red in PROP0. unfold lbl_thread_opt in PROP0.
        desc. by inversion PROP0. }      
      rewrite Nat.add_1_r, <- VISw, <- H2. simpl.
      forward eapply (@buffer_sources (vis w) thread) with (k := 0) (l := loc) (v :=val) as [ind_w INDw].
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      { rewrite <- H0. simpl. by rewrite BUF. }
      simpl in INDw. desc.
      remember (ThreadEvent thread ind_w (Astore loc val)) as w'.
      rewrite Nat.add_0_r in WRITE_POS.
      cut (w' = w).
      { ins. subst w' w. inversion H1. subst.
        unfold loc, loc_l, valw. simpl. by apply upds. }
      apply ti_inj; try (by vauto).
      apply (@nth_such_unique (count_upto (is_prop ∩₁ in_thread thread) (vis w))
                              (regular_write' ∩₁ in_thread thread)); auto.
      unfold write2prop in VISw. destruct (excluded_middle_informative _).
      2: { generalize n. rewrite trace_index_simpl'; auto. subst w.
           unfolder'. intuition. }
      destruct (constructive_indefinite_description _ _). desc. simpl in *. subst x0.
      rewrite trace_index_simpl' in *; auto.
      replace (same_thread (inl w)) with (in_thread thread) in *.
      2: { symmetry. subst w. apply RESTR_EQUIV. }
      split; auto.
      rewrite trace_index_simpl'; auto. subst w. vauto. }
    remember (ThreadEvent thread index (Armw x vr vw)) as rmw. 
    rewrite rmw_vis in *; try (by subst rmw; intuition). 
    forward eapply (TSi (trace_index rmw)) with (d := def_lbl) as TSi.
    { congruence. }
    rewrite trace_index_simpl in TSi; auto. inversion TSi.
    all: try (subst rmw; discriminate).
    subst rmw. inversion H. subst thread0 index0 x val_r val_w vr. 
    remember (ThreadEvent thread index (Armw loc (sh_mem loc) vw)) as rmw.
    rewrite Nat.add_1_r, <- H2. simpl.
    assert (loc = l); [| subst loc]. 
    { subst rmw. unfold Events.loc, loc_l in LATEST. by simpl in LATEST. }
    rewrite upds. vauto. }
  specialize_full IHd.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  { ins. desc. apply LATEST0. splits; vauto. lia. }
  rewrite <- IHd. symmetry. replace (vis w + S (S d)) with (S (vis w + (S d))) by lia.
  assert (NOmega.lt_nat_l (vis w + S d) (trace_length tr)) as DOM'. 
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  forward eapply (TSi (vis w + S d)) with (d := def_lbl) as TSi; auto. 
  inversion TSi; auto.
  { simpl. destruct (classic (loc = l)).
    2: { rewrite updo; auto. }
    subst loc. exfalso. 
    specialize (LATEST0 (ThreadEvent thread index (Armw l val_r val_w))).
    forward eapply ti_infer as TI; eauto.
    specialize_full LATEST0.
    { splits; try (by vauto).
      { rewrite rmw_vis; auto. lia. }
      right. red. rewrite H. apply trace_nth_in; auto. }
    red in LATEST0. des.
    { rewrite LATEST0 in TI. unfold vis in TI.
      destruct (excluded_middle_informative _); [| lia].
      subst w. generalize i. unfolder'. intuition. }
    do 2 red in LATEST0. des.
    { red in LATEST0. desc. vauto. }
    apply seq_eqv_lr in LATEST0. desc. 
    rewrite rmw_vis in LATEST1; auto. lia. }
  { simpl. destruct (classic (loc = l)).
    2: { rewrite updo; auto. }
    subst loc. exfalso. 
    forward eapply (@buffer_sources (vis w + S d) thread) with (k := 0) (l := l) (v := val) as [ind_w INDw].
    { destruct (trace_length tr); vauto. }
    { rewrite <- H0. simpl. by rewrite BUF. }
    simpl in INDw. desc.
    remember (ThreadEvent thread ind_w (Astore l val)) as w'.
    assert (vis w' = vis w + S d) as VISw'.
    { rewrite regw_vis; [| subst w'; unfolder'; intuition].
      (* red in WRITE_POS. desc. rewrite Nat.add_0_r in WRITE_POS. *)
      unfold write2prop in PROP_AFTER. unfold write2prop.
      destruct (excluded_middle_informative _).
      2: { lia. }
      destruct (constructive_indefinite_description _ _). desc. simpl in *.
      replace (same_thread (trace_labels (trace_index w'))) with (in_thread thread) in *.
      2: { symmetry. rewrite trace_index_simpl'; auto. 
           subst w'. apply RESTR_EQUIV. }
      apply (@nth_such_unique (count_upto (regular_write' ∩₁ in_thread thread) (trace_index w')) (is_prop ∩₁ in_thread thread)).
      { vauto. }
      red. splits.
      { red in WRITE_POS. lia. }
      unfold trace_labels. rewrite <- H. vauto. }
    specialize (LATEST0 w'). specialize_full LATEST0.
    { splits; vauto. lia. }
    red in LATEST0. des.
    { subst w. lia. }
    do 2 red in LATEST0. des.
    { red in LATEST0. desc. by destruct (proj1 Eninit_non_init w'). }
    apply seq_eqv_lr in LATEST0. desc. lia. }
Qed. 
       
  
Lemma latest_mem_value_kept ind w l
      (DOM: NOmega.lt_nat_l ind (trace_length tr))
      (LATEST: latest_of_by (fun e' => loc e' = l /\ (is_init e' \/ vis e' < ind) /\ EG e' /\ is_w e') vis_lt w):
  fst (states ind) l = valw w.
Proof.
  destruct (classic (is_init w)) as [W_ | W_]. 
  { by apply winit_helper. }
  apply latest_mem_value_kept'; auto.
  red in LATEST. desc. des; [done| ]. 
  red. splits; vauto. ins. desc. apply LATEST0. splits; vauto. 
Qed. 
  
    
  
Lemma latest_buf_value_read' thread w ind loc val
      (TB_LATEST:
         latest_of_by
           (fun e =>
              match lab e with
              | Aload x _ | Astore x _ | Armw x _ _ => x
              end = loc /\ trace_index e < ind /\
              exact_tid e = thread /\ Eninit e /\ is_w e) trace_before w
         /\ ind < vis w )
      (BUF_LATEST: let bufs := snd (states ind) in 
                   latest_buffered (bufs thread) loc (Some val))
      (DOM: NOmega.lt_nat_l ind (trace_length tr)):
  val = valw w.
Proof.
  set (prev_write := fun i => (fun e : Event =>
                 match lab e with
                 | Aload x _ | Astore x _ | Armw x _ _ => x
                 end = loc /\
                 trace_index e < i 
                 /\ exact_tid e = thread /\ Eninit e /\ is_w e)).
  fold (prev_write ind) in TB_LATEST.
  generalize dependent w. generalize dependent val. generalize dependent DOM.
  set (P := fun ind => NOmega.lt_nat_l ind (trace_length tr) ->
  forall val : Val,
  (let bufs := snd (states ind) in
   latest_buffered (bufs thread) loc (Some val)) ->
  forall w : Event, latest_of_by (prev_write ind) trace_before w /\ ind < vis w
               ->  val = valw w).
  cut (P ind); [done| ].
  apply (@lt_wf_ind ind P). clear ind. intros ind IH.
  red. intros DOM val LATEST_BUFFERED w LATEST_OF.
  destruct ind as [| ind_prev].
  { rewrite <- TS0 in LATEST_BUFFERED. by inversion LATEST_BUFFERED. }
  remember (S ind_prev) as ind_cur.
  specialize (IH ind_prev). specialize_full IH; [lia| ].
  subst P. simpl in IH.
  assert (NOmega.lt_nat_l ind_prev (trace_length tr)) as DOM_prev.
  { destruct (trace_length tr); auto. simpl in *. lia. }
  specialize (IH DOM_prev).

  (* check: if e_prev is not W@loc, is it always latest_of_by for prev index? *)
  remember (trace_nth ind_prev tr def_lbl) as e_prev.
  (* specify just one part of statement for now*)
  desc.
  destruct (classic (trace_index w = ind_prev)) as [W_IND | W_IND]. 
  { pose proof (TSi ind_prev DOM_prev def_lbl) as TSi. simpl in TSi.
    red in LATEST_OF. desc. red in LATEST_OF. desc.
    rewrite <- W_IND, trace_index_simpl in TSi; auto.    
    assert (w = ThreadEvent thread (index w) (Astore loc (Events.valw w))) as W.
    { destruct w.
      { by destruct (proj1 Eninit_non_init (InitEvent x)). }
      simpl.
      simpl in LATEST_OF3. subst thread0. f_equal.
      destruct l; auto.
      { generalize LATEST_OF5. by unfolder'. }
      rewrite rmw_vis in LATEST_OF0; auto. lia. }
    rewrite W in TSi at 2. inversion TSi. subst loc0 val0 thread0.
    rewrite W_IND in H5. rewrite Heqind_cur, <- H5 in LATEST_BUFFERED.
    move LATEST_BUFFERED at bottom.
    simpl in LATEST_BUFFERED. rewrite upds in LATEST_BUFFERED.
    inversion LATEST_BUFFERED; [discriminate| ].
    inversion LATEST_VALUE. subst val0. clear LATEST_VALUE. 
    simpl in LATEST_BUF. rewrite filter_app, length_app in LATEST_BUF.
    simpl in LATEST_BUF. rewrite Nat.eqb_refl in LATEST_BUF.
    rewrite nth_error_app2 in LATEST_BUF.
    2: { simpl. lia. }
    simpl in LATEST_BUF. rewrite Nat.add_sub, Nat.sub_diag in LATEST_BUF.
    simpl in LATEST_BUF. vauto. }
  assert (latest_of_by (prev_write ind_prev) trace_before w) as PREV_LATEST.
  { subst prev_write. red in LATEST_OF. desc. 
    subst ind_cur.
    move LATEST_OF2 at bottom. 
    red in LATEST_OF2. apply Peano.le_S_n, le_lt_or_eq in LATEST_OF2. des; [|done].
    red. splits; vauto.
    ins. desc. apply LATEST_OF1. splits; vauto. }

  specialize IH with (val := val) (w := w). apply IH.
  2: { splits; [done | lia]. }
  pose proof (TSi ind_prev DOM_prev def_lbl) as TSi. simpl in TSi.
  rewrite <- Heqe_prev in TSi.
  inversion TSi.
  1, 2: by congruence.
  2: { destruct (classic (thread0 = thread)).
       2: { subst ind_cur. by rewrite <- H in LATEST_BUFFERED. }
       subst ind_cur thread0. by rewrite <- H in LATEST_BUFFERED. }
  { rewrite Heqind_cur, <- H in LATEST_BUFFERED. simpl in *.
    destruct (classic (thread0 = thread)).
    2: { rewrite updo in LATEST_BUFFERED; auto. }
    subst thread0. rewrite upds in LATEST_BUFFERED.
    inversion LATEST_BUFFERED; [discriminate| ].
    inversion LATEST_VALUE. subst val1. clear LATEST_VALUE.
    simpl in LATEST_BUF. rewrite filter_app, length_app in LATEST_BUF.
    simpl in LATEST_BUF. 
    destruct (Nat.eqb loc0 loc) eqn:L.
    2: { simpl in LATEST_BUF. rewrite app_nil_r, Nat.add_0_r in LATEST_BUF. vauto. }
    apply beq_nat_true in L. subst loc0.
    exfalso. apply W_IND.
    remember (Astore loc val0) as lbl'. 
    remember (ThreadEvent thread index lbl') as w'. 
    assert (Eninit w') as E'w'.
    { red. rewrite H1. subst. by apply trace_nth_in. }
    forward eapply (@ti_uniq (trace_index w') ind_prev thread index lbl') as IND; eauto.
    { rewrite trace_index_simpl; vauto. }
    { rewrite trace_index_simpl; vauto. }
    assert (latest_of_by (prev_write ind_cur) trace_before w').
    { red. split.
      { red. splits; vauto. }
      ins. red in S'. desc. rewrite Heqind_cur in S'0. apply lt_n_Sm_le, le_lt_or_eq in S'0.
      unfold trace_before. red. des; [by vauto| ].
      left. apply ti_inj; vauto. }
    cut (w' = w); [by ins; vauto| ]. 
    forward eapply (@latest_unique _ (prev_write ind_cur) trace_before) as UNIQ; eauto.
    { cdes tb_SPO. cdes tb_SPO0. by apply trans_irr_antisymmetric. }
    unfold unique in UNIQ. desc. rewrite <- UNIQ0; auto.
    rewrite (UNIQ0 w'); auto. }
  rewrite Heqind_cur, <- H in LATEST_BUFFERED. simpl in *.
  destruct (classic (thread0 = thread)).
  2: { rewrite updo in LATEST_BUFFERED; auto. }
  subst thread0. rewrite upds in LATEST_BUFFERED. rewrite BUF.
  inversion LATEST_BUFFERED; [discriminate| ].
  inversion LATEST_VALUE. subst val1. clear LATEST_VALUE. 
  simpl in LATEST_BUF. 
  eapply latest_loc; eauto. simpl in *.
  destruct (Nat.eqb loc0 loc); [| done].
  simpl. rewrite Nat.sub_0_r.
  remember (filter (fun loc_val : Loc * Val => fst loc_val =? loc) buf') as buf_flt.
  destruct buf_flt; [done |]. simpl in *. by rewrite Nat.sub_0_r in LATEST_BUF.
Qed.
  

Lemma latest_buf_value_read thread w r val
      (TB_LATEST:
         latest_of_by
           (fun e => loc e = loc r /\ trace_before e r /\
              exact_tid e = thread /\ Eninit e /\ is_w e) trace_before w)
      (BUF_LATEST: let bufs := snd (states (trace_index r)) in 
                   latest_buffered (bufs thread) (loc r) (Some val))
      (DOM: NOmega.lt_nat_l (trace_index r) (trace_length tr))
      (Rr: is_r r)
      (E'r: Eninit r)
      (TID_R: exact_tid r = thread):
  val = valw w.
Proof.
  eapply latest_buf_value_read' with (ind := trace_index r) (loc := loc r) (thread := thread); auto.
  desc. 
  unfold trace_before at 1 in TB_LATEST.
  red in TB_LATEST. desc.
  pose proof (r_vis r Rr) as VISr. 
  unfold latest_of_by. splits; auto.
  remember (states (trace_index r)) as st. destruct st as [mem bufs]. simpl in *.
  assert (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (bufs (exact_tid r)) <> nil) as BUF_NEMPTY. 
  1: { unfold state_before_event. 
       inversion BUF_LATEST; [discriminate| ].
       simpl in LATEST_BUF. red. ins.
       replace (exact_tid r) with thread in H.
       by rewrite H in LATEST_BUF. }
  
  apply rf_before_prop.
  2: { unfold state_before_event. by rewrite <- Heqst. }
  simpl. apply seq_eqv_lr. unfold set_inter. splits; auto.
  1,3: by (simpl; unfold EG; vauto).
  red. unfold state_before_event. rewrite <- Heqst.
  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r)
                   (bufs (exact_tid r))); vauto.
  (* Set Printing All. *)
  red. splits; vauto. ins. apply TB_LATEST0. desc. splits; vauto. congruence. 
Qed.


Lemma rf_same_value w r (RF: rf G w r): valw w = valr r.
Proof.
  simpl in RF. apply seq_eqv_lr in RF. destruct RF as [W [RF [Er Rr]]].
  do 2 red in Er. des; [by destruct (init_non_r r)| ]. 
  red in RF. unfold state_before_event in RF.
  (* pose proof TR as TR'. apply LTS_traceE in TR'. desc. *)
  remember (states (trace_index r)) as st.
  assert (NOmega.lt_nat_l (trace_index r) (trace_length tr)) as DOMr. 
  { contra GE. forward eapply (proj2 (ge_default (trace_index r))); auto.
    rewrite trace_index_simpl'; auto. unfolder'. ins. vauto. }
  forward eapply (TSi (trace_index r)) with (d := def_lbl) as TSi; eauto. 
  destruct st as [sh_mem bufs].
  rewrite trace_index_simpl in TSi; auto.
  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r)
                   (bufs (exact_tid r))) eqn:BUF_FLT.
  { cut (sh_mem (loc r) = valw w). 
    { ins.            
      inversion TSi; vauto.
      { rewrite <- Heqst in H1. inversion H1. subst.
        unfold Events.loc, loc_l in BUF_FLT. simpl in BUF_FLT.        
        inversion BUF; vauto. simpl in LATEST_BUF.  
        by rewrite BUF_FLT in LATEST_BUF. }
      { rewrite <- Heqst in H1. inversion H1. subst.
        unfold Events.loc, loc_l in H. simpl in H.
        by unfold valr, valr_l. }
      { rewrite <- Heqst in H1. inversion H1. subst.
        unfold Events.loc, loc_l in H. simpl in H.
        by unfold valr, valr_l. } }
    
    forward eapply (@latest_mem_value_kept (trace_index r) w (loc r)); vauto.
    2: by rewrite <- Heqst.
    (* { by rewrite trace_index_simpl'. } *)
    red. red in RF. desc. splits; vauto.
    { do 2 red in RF1. des.
      { red in RF1. desc. by left. }
      right. apply seq_eqv_lr in RF1. desc.
      by rewrite (r_vis r) in RF4. }
    ins. desc.
    (* des. *)
    destruct (classic (is_init y)). 
    { do 2 red in RF2. destruct RF2. 
      { destruct w, y; vauto. left. f_equal. unfold loc, loc_l in *. simpl in *.
        congruence. }
      red. right. red. left. split; vauto. }
    des; [done| ]. do 2 red in S'1. des; [done| ]. 
    
    apply RF0. splits; vauto. do 2 red. des; vauto. 
    right. apply seq_eqv_lr. splits; vauto.
    by rewrite (r_vis r). }
  
  inversion TSi; vauto.
  { rewrite <- Heqst in H0. inversion H0. subst.
    unfold valr, valr_l, Events.loc, loc_l in *. simpl in *. 
    cut (val = valw w).
    { ins. }
    desc. 
    eapply (@latest_buf_value_read thread w (ThreadEvent thread index (Aload loc val)) val); eauto.
    simpl. rewrite <- Heqst. vauto. }
    (* split; vauto. red. splits; vauto.  *)
  { rewrite <- Heqst in H0. inversion H0. subst.
    unfold Events.loc, loc_l in BUF_FLT. simpl in BUF_FLT. 
    inversion BUF; vauto. by rewrite BUF_FLT in EMPTY_BUF. }
  { rewrite <- Heqst in H0. inversion H0. subst.
    unfold Events.loc, loc_l in BUF_FLT. simpl in BUF_FLT. 
    by rewrite NO_BUF in BUF_FLT. }
Qed. 

Lemma WFG: Wf G.
Proof.
  split.
  { ins. desc. do 2 red in H. des; [vauto|].
    assert (~ is_init b).
    { destruct a, b; vauto.
      red in H2. simpl in H2. subst.
      by apply NO_TID0 in H. }
    do 2 red in H0. des; [vauto|].
    destruct a, b; vauto.
    { exfalso. by simpl in H3. }
    { by destruct (proj1 Eninit_non_init (InitEvent x)). } 
    { by destruct (proj1 Eninit_non_init (InitEvent x)). }
    red in H2. simpl in H2. subst index0.
    red in H, H0. apply trace_in_nth with (d := def_lbl) in H. apply trace_in_nth with (d := def_lbl) in H0. desc.
    simpl in *. red in WF.
    specialize WF with (d := def_lbl) (thread := thread0) (index1 := index) (index2 := index). 
    pose proof (Nat.lt_trichotomy n n0). des.
    2: { subst. congruence. }
    all: subst; specialize_full WF; eauto; lia. }
  { simpl. basic_solver. }
  { simpl. basic_solver. }
  { simpl. rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l.
    unfold rf'. red. ins.
    destruct (state_before_event y). destruct (filter _ _); unfold latest_of_by in H; by desc. }
  { apply rf_same_value. }
  { unfold functional. intros r w1 w2 RF1 RF2. unfold transp in *.
    forward eapply (@read_source r) as [w' [RF' UNIQ]]. 
    1, 2: generalize RF1; simpl; basic_solver.
    rewrite <- (UNIQ w1), <- (UNIQ w2); [auto|generalize RF2 |generalize RF1]; simpl; basic_solver. }
  { simpl. basic_solver. }
  { simpl. basic_solver. }
  { simpl. basic_solver. }
  { destruct (co_loc_total 0). by cdes H. }
  { ins. by destruct (co_loc_total x). }
  { red. ins. apply seq_eqv_lr in H. desc.
    red in H0. desc. do 2 red in H0. des.
    { by apply (proj1 Eninit_non_init x). }
    apply seq_eqv_lr in H0. desc. lia. }
  { simpl. unfold EG. basic_solver. }
  { split; [| basic_solver]. rewrite seq_eqv_r.
    red. ins. desc. apply seq_eqv_lr in H. desc. red in H1. desc.
    do 2 red in H1. des.
    { apply (proj1 Eninit_non_init y). red in H1. by desc. }
    apply seq_eqv_lr in H1. desc. by apply (proj1 Eninit_non_init y). }
  { ins. do 2 red in ACT. des.
    { by destruct e. }
    specialize (NO_TID0 e ACT). destruct e; vauto. }
Qed.

Lemma co_implies_vis_lt: co G ⊆ vis_lt.
Proof. simpl. basic_solver. Qed.

Lemma sb_rf_irr: irreflexive (sb G ⨾ rf G).
Proof.
  red. intros r [w [SB RF]].
  simpl in RF. apply seq_eqv_lr in RF. destruct RF as [Ww [RF Rr]].  
  red in RF.
  destruct (state_before_event r) as [mem bufs].
  (* destruct (bufs (exact_tid r)). *)
  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (bufs (exact_tid r))). 
  { desc.
    destruct (vis_lt_init_helper SB). des.
    { red in RF. desc. 
      cdes vis_SPO.
      forward eapply (@trans_irr_antisymmetric _ vis_lt); eauto. }
    unfold sb in SB. apply seq_eqv_lr in SB. destruct SB as [Ew [SB Er]].
    forward eapply (proj1 tb_respects_sb r w) as H_.
    { basic_solver. }
    apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]]. 
    
    red in TB, RF. desc. do 2 red in RF1. des.
    { generalize (proj1 Eninit_non_init w), RF1. basic_solver. }
    apply seq_eqv_lr in RF1. destruct RF1 as [_ [VIS _]].
    red in Rr. desc.  
    rewrite (r_vis r) in VIS; eauto.
    pose proof (TI_LE_VIS w H0). lia. }
  desc.
  unfold sb in SB. apply seq_eqv_lr in SB. destruct SB as [Er [SB Ew]].

  forward eapply (proj1 tb_respects_sb r w) as H_.
  { simpl in Er, Ew. do 2 red in Er. des.
    { red in Rr. desc. by destruct (init_non_r r). }
    do 2 red in Ew. des.
    { red in SB. destruct r.
      { by destruct (proj1 Eninit_non_init (InitEvent x)). }
      destruct w; [done| ]. basic_solver. }
    apply seq_eqv_lr. splits; auto. }
  apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]]. 
  
  red in TB, RF. desc.
  red in RF1. lia. 
Qed.

Lemma rfe_implies_vis_lt: rfe G ⊆ vis_lt.
Proof.
  unfold rfe.
  red. intros w r [RFwr NSBwr].
  simpl in RFwr. apply seq_eqv_lr in RFwr. destruct RFwr as [Ww [RFwr Rr]]. 
  red in Ww, Rr. desc. 
  red in RFwr.
  remember (state_before_event r) as st. destruct st as [mem bufs].   
  destruct (classic (exact_tid w = exact_tid r)).
  2: {
    (* destruct (exact_tid r). *)
    destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (bufs (exact_tid r))). 
    2: { desc. red in RFwr. by desc. } 
    red in RFwr. by desc. }
  (* destruct (bufs (exact_tid r)); *)
  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (bufs (exact_tid r))) eqn:BUF_FLT;
    [red in RFwr; by desc| ].
  desc. red in RFwr. desc. 
  exfalso. apply NSBwr. red in RFwr0. 
  apply seq_eqv_lr. splits; eauto.
  forward eapply (proj2 tb_respects_sb w r).
  2: { basic_solver. }
  apply seq_eqv_lr. splits; vauto. 
  do 2 red in Rr. des; auto. by destruct (init_non_r r). 
Qed.

Lemma fr_implies_vis_lt: fr G ⊆ vis_lt.
Proof.
  red. intros r w FR. red. right.
  apply (wf_frD WFG), seq_eqv_lr in FR. destruct FR as [Rr [FR Ww]].
  apply (fr_ninit WFG), seq_eqv_r in FR. destruct FR as [FR [Ew NINITw]].
  apply (wf_frE WFG), seq_eqv_lr in FR. destruct FR as [Er [FR _]].
  simpl in *. unfold EG, set_union in *. des; vauto.
  { edestruct (init_non_r); eauto. } 
  apply seq_eqv_lr. splits; auto.
  erewrite r_vis; eauto.
  pose proof (Nat.lt_trichotomy (trace_index r) (vis w)). des; auto.
  { exfalso. unfold vis in H.
    destruct (excluded_middle_informative _) as [W|W].
    2: { apply ti_inj in H; vauto. apply (fr_irr WFG FR). }
    unfold write2prop in H. destruct (excluded_middle_informative _) as [W_|W_].
    2: { unfold trace_labels in W_. rewrite trace_index_simpl in W_; auto. }
    destruct (constructive_indefinite_description _ _) as [p Pp]. simpl in *. desc.
    rewrite <- H in THREAD_PROP.
    unfold trace_labels at 2 in THREAD_PROP. rewrite trace_index_simpl in THREAD_PROP; auto.
    red in THREAD_PROP. desc. vauto. }
  exfalso. red in FR. destruct FR as [[w' [RF CO]] NEQ]. unfold transp in RF.
  pose proof (rf_before_prop RF) as RF_PROP. 
  simpl in RF. apply seq_eqv_lr in RF. desc. red in RF0.  
  destruct (state_before_event r) as [mem bufs].
  (* pose proof (proj1 (wf_rfE WFG) _ _ RF). apply seq_eqv_lr in H0. destruct H0 as [Ew' [_ _]].  *)
  
  (* destruct (bufs (exact_tid r)). *)
  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (bufs (exact_tid r))) eqn:BUF_FLT. 
  { desc. red in RF0. desc.
    specialize (RF2 w). specialize_full RF2.
    { splits; vauto.
      { apply (wf_col WFG) in CO. red in CO. congruence.  }
      red. right. apply seq_eqv_lr. splits; auto. by rewrite (r_vis r Rr). }
    (* vauto.  *)
    (* apply (RF2 w). exists w. *)
    red in RF2. des.
    { subst w'. by apply (co_irr WFG w). }
    simpl in CO. apply seq_eqv_lr in CO. destruct CO as [Ww' [[VISw'w LOCw'w] _]].
    forward eapply (strict_partial_order_antisymmetric vis_SPO w w') as EQ; auto.
    subst w'. cdes vis_SPO. eapply vis_SPO0; eauto. }
  desc.
  simpl in CO. apply seq_eqv_lr in CO. destruct CO as [Ww' [[VISw'w LOCw'w] _]].
  do 2 red in VISw'w. des.
  { red in VISw'w. desc. red in RF0. desc.
    destruct (proj1 Eninit_non_init w'). vauto. }
  apply inclusion_seq_eqv_l, inclusion_seq_eqv_r in VISw'w.
  red in RF0. desc.
  specialize_full RF_PROP; [done| ]. 
  lia. 
Qed.


Lemma rel_helper: rf G ∪ co G ∪ fr G ⊆ restr_eq_rel loc (sb G) ∪ (rfe G ∪ coe G ∪ fre G).
Proof.
  rewrite fri_union_fre, (fri_in_sbloc' WFG).
  rewrite coi_union_coe, (coi_in_sbloc' WFG).
  rewrite rfi_union_rfe, (rfi_in_sbloc' WFG).
  repeat (apply inclusion_union_l; [| basic_solver]). basic_solver.  
Qed.

Lemma buffer_shift thread i j (LE: i <= j) (DOM: NOmega.lt_nat_l j (trace_length tr)):
  let pi := count_upto (is_prop ∩₁ in_thread thread) i in
  let pj := count_upto (is_prop ∩₁ in_thread thread) j in
  let buf_i := snd (states i) thread in
  let buf_j := snd (states j) thread in
  forall item k (ITEM: Some item = nth_error buf_i (k + (pj - pi))),
    Some item = nth_error buf_j k.
Proof.
  simpl. apply le_diff in LE. desc. subst j. induction d.
  { rewrite Nat.add_0_r, Nat.sub_diag. ins. by rewrite Nat.add_0_r in ITEM. }
  ins. replace (i + S d) with (S (i + d)) in * by lia. 
  assert (NOmega.lt_nat_l (i + d) (trace_length tr)) as DOM'.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  specialize (IHd DOM'). 
  remember (count_upto (is_prop ∩₁ in_thread thread) i) as Pi.
  remember (count_upto (is_prop ∩₁ in_thread thread) (S (i + d))) as Pcur. 
  remember (count_upto (is_prop ∩₁ in_thread thread) (i + d)) as Pprev.
  assert (Pcur = Pprev + check (is_prop ∩₁ in_thread thread) (trace_nth (i + d) tr def_lbl)) as CUR.
  { subst. by rewrite count_upto_next. }
  forward eapply (TSi (i + d)) with (d := def_lbl) as TSi; auto.  
  inversion TSi.
  { rewrite check0 in CUR.
    2: { rewrite <- H. unfolder'. intuition. }
    rewrite Nat.add_0_r in CUR. rewrite CUR in ITEM.
    erewrite IHd; eauto. congruence. }
  { rewrite check0 in CUR.
    2: { rewrite <- H. unfolder'. intuition. }
    rewrite Nat.add_0_r in CUR. rewrite CUR in ITEM.
    erewrite IHd; eauto. congruence. }
  { rewrite check0 in CUR.
    2: { rewrite <- H. unfolder'. intuition. }
    rewrite Nat.add_0_r in CUR. rewrite CUR in ITEM.
    specialize (IHd item k ITEM). 
    rewrite IHd. 
    rewrite <- H0. simpl.
    destruct (classic (thread0 = thread)).
    2: { rewrite updo; auto. }
    subst thread0. rewrite upds. rewrite nth_error_app1; auto.
    apply nth_error_Some. apply opt_val. exists item. by rewrite <- H0 in IHd. }
  { rewrite check0 in CUR.
    2: { rewrite <- H. unfolder'. intuition. }
    rewrite Nat.add_0_r in CUR. rewrite CUR in ITEM.
    erewrite IHd; eauto. by rewrite <- H0. }
  { simpl. destruct (classic (thread0 = thread)).
    2: { rewrite updo; auto. 
         rewrite check0 in CUR.
         2: { rewrite <- H. unfolder'.
              unfold in_thread, lbl_thread_opt. intuition. vauto. }
         rewrite Nat.add_0_r in CUR. rewrite CUR in ITEM.
         erewrite IHd; eauto. by rewrite <- H0. }
    subst thread0. rewrite upds.
    rewrite check1 in CUR.
    2: { rewrite <- H. unfolder'. vauto. }
    rewrite CUR in ITEM.
    specialize (IHd item (k + 1)). specialize_full IHd.
    { rewrite ITEM. f_equal.
      assert (Pi <= Pprev) as MORE. 
      { subst. apply count_upto_more. lia. }
      do 2 (rewrite Nat.add_sub_assoc; [| lia]). lia. }
    rewrite IHd, <- H0. simpl. rewrite BUF. by rewrite Nat.add_1_r. }
Qed. 

Lemma buf_between w p thread ind loc val (W2P: p = write2prop w)
      (EVENT: trace_nth w tr (inl (InitEvent 0)) = inl (ThreadEvent thread ind (Astore loc val))):
  forall i (BETWEEN: w < i /\ i <= p),
    let bufs := snd (states i) in
    (filter (fun loc_val : nat * Val => fst loc_val =? loc) (bufs thread)) <> nil.
Proof.
  ins.
  remember (states w) as st0. destruct st0 as [sh_mem0 bufs0].
  remember (states i) as st. destruct st as [sh_mem bufs].
  cut (exists n, nth_error (bufs thread) n = Some (loc, val)).
  { ins. desc. cut (In (loc, val) (filter (fun loc_val : nat * Val => fst loc_val =? loc) (bufs thread))).
    { ins. by destruct (filter _ _). }
    apply in_filter_iff. split.
    { eapply nth_error_In. eauto. }
    apply Nat.eqb_refl. }
  remember (states (w + 1)) as st1. destruct st1 as [sh_mem1 bufs1].
  remember (length (bufs0 thread)) as l0.
  assert (Some (loc, val) = nth_error (bufs1 thread) l0) as W_LAST.
  { forward eapply (TSi w) with (d := def_lbl) as TSi.
    { apply lt_nondefault. unfold trace_labels. unfolder'. by rewrite EVENT. }
    unfold def_lbl in TSi. rewrite EVENT in TSi. inversion TSi.
    rewrite <- Heqst0 in H0. inversion H0.
    subst thread0 index loc0 val0 sh_mem2 bufs2.
    rewrite NPeano.Nat.add_1_r in Heqst1. rewrite <- Heqst1 in H5. inversion H5.
    rewrite upds. rewrite nth_error_app2; [| lia].
    by rewrite Heql0, Nat.sub_diag. }

  remember (count_upto (is_prop ∩₁ in_thread thread) (w + 1)) as p1.
  remember (count_upto (is_prop ∩₁ in_thread thread) i) as pi.
  remember (count_upto (is_prop ∩₁ in_thread thread) w) as p0.
  forward eapply (@count_upto_more (w + 1) i (is_prop ∩₁ in_thread thread)) as MORE_PROPS; [lia|].
  rewrite <- Heqp1, <- Heqpi in MORE_PROPS. apply le_diff in MORE_PROPS. desc.
  apply plus_minus in MORE_PROPS. 
  assert (exists k, l0 = k + d) as [k BUF_SHIFT]. 
  { destruct (le_lt_dec d l0).
    { apply le_diff in l. desc. exists d0. lia. }
    exfalso.
    rewrite Nat.add_1_r, count_upto_next, check0, Nat.add_0_r in Heqp1.
    2: { unfold trace_labels, def_lbl. rewrite EVENT. unfolder'. intuition. }
    assert (p1 = p0) by congruence. subst p1. clear H. try rewrite <- Heqp0 in *.
    assert (pi > p0 + l0) as OVER_PROPS by lia.

    forward eapply (@buffer_size thread w) as WRITE_NTH.
    { apply NOmega.lt_le_incl. apply lt_nondefault.
      unfold trace_labels, def_lbl. by rewrite EVENT. }
    
    simpl in WRITE_NTH. rewrite <- Heqp0, <- Heqst0 in WRITE_NTH.
    simpl in WRITE_NTH. rewrite <- Heql0 in WRITE_NTH.  
    
    unfold write2prop in W2P. destruct (excluded_middle_informative _).
    2: { unfolder'. intuition. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    replace (same_thread (trace_labels w)) with (in_thread thread) in *. 
    2: { unfold trace_labels, def_lbl. rewrite EVENT. symmetry. apply RESTR_EQUIV. }
    rewrite W_P_CORR in WRITE_NTH. subst x.
    forward eapply (@count_upto_more i p (is_prop ∩₁ in_thread thread)) as MORE; [lia| ].
    lia. }
  rewrite BUF_SHIFT, MORE_PROPS in W_LAST.

  exists k. 
  forward eapply (@buffer_shift thread (w + 1) i) with (k := k) (item := (loc, val)); eauto. 
  { lia. }
  { eapply NOmega.le_lt_nat; eauto. 
    apply lt_nondefault.
    replace (trace_labels p) with ((inr thread):TSO_label); [done| ]. 
    subst p.
    forward eapply (@w2p_regw (ThreadEvent thread ind (Astore loc val)) thread) as W2P_PROP; try (by vauto).
    { unfolder'. intuition. }
    { red. rewrite <- EVENT. apply trace_nth_in. apply lt_nondefault.
      unfold trace_labels, def_lbl. rewrite EVENT. intuition. vauto. }
    rewrite (ti_infer w) in W2P_PROP; [| done].
    unfold trace_labels.
    generalize W2P_PROP. remember (trace_nth (write2prop w) tr def_lbl) as lbl. 
    unfolder'. destruct lbl; intuition; vauto. }
  { by rewrite <- Heqst1, <- Heqp1, <- Heqpi. }
  by rewrite <- Heqst. 
Qed.


Lemma nonw_vis e (NW: ~ is_w e): vis e = trace_index e.
Proof.
  unfold vis.
  destruct (excluded_middle_informative (is_regular_write' e)); auto.
  exfalso. apply NW. do 2 red in i. by desc.
Qed.

  
Lemma sb_fr_irr: irreflexive (sb G ⨾ fr G).
Proof.
  red. intros w [r [SBwr FRrw]].
  pose proof (fr_implies_vis_lt FRrw) as VISrw. do 2 red in VISrw.
  des.
  { red in VISrw. desc. apply (wf_frD WFG), seq_eqv_lr in FRrw. desc. 
    destruct r; vauto. }
  apply seq_eqv_lr in VISrw. desc. 
  (* destruct VISrw as [VISrw _]. red in VISrw. *)
  apply (wf_frD WFG), seq_eqv_lr in FRrw. destruct FRrw as [Rr [FRrw Ww]].
  rewrite r_vis in VISrw0; auto. 
  unfold vis in VISrw0.
  destruct (excluded_middle_informative (is_regular_write' w)) as [WREGw| ]. 
  2: { unfold sb in SBwr. apply seq_eqv_lr in SBwr. desc.
       forward eapply (proj1 tb_respects_sb w r) as H_; [basic_solver| ].
       apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]]. 
       red in TB. lia. }
  assert (trace_index w < trace_index r) as TBwr.
  { forward eapply (proj1 tb_respects_sb w r) as H_. 
    { apply seq_eqv_lr. splits; auto. red in SBwr. apply seq_eqv_lr in SBwr. basic_solver. }
    apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]]. by red in TB. }
  forward eapply (reg_write_structure (inl w)); vauto. ins. desc. inversion H.
  assert (exact_tid w = exact_tid r).
  { apply sb_tid_init in SBwr. des; vauto. }
  assert (thread = exact_tid r).
  { ins. subst.  simpl in *. congruence. }
  
  forward eapply (@buf_between (trace_index w) (write2prop (trace_index w)) thread index loc val) as IN_BUF; auto.
  { by rewrite trace_index_simpl, H1. }
  { split; eauto. lia. }  
  remember (states (trace_index r)) as st_r. destruct st_r as [mem bufs].
  simpl in IN_BUF.


  pose proof FRrw as FRrw_. 
  red in FRrw. destruct FRrw as [[w' [RFw'r COw'w]] NEQrw]. unfold transp in RFw'r.
  pose proof RFw'r as RFw'r_.
  simpl in RFw'r. apply seq_eqv_lr in RFw'r. desc.
  red in RFw'r0. 
  unfold state_before_event in RFw'r0.
  rewrite <- Heqst_r in RFw'r0.
  desc. rewrite <- H2 in RFw'r0.
  assert (Events.loc r = loc) as LOC.
  { replace loc with (Events.loc w); [| vauto].
    apply (wf_frl WFG) in FRrw_. vauto. }
  rewrite LOC in RFw'r0. 

  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc) (bufs thread)) eqn:BUF_FLT; [done| ].  
  desc. red in RFw'r0. desc.
  specialize (RFw'r2 w). specialize_full RFw'r2.
  { splits; vauto. }
  red in RFw'r2. des.
  { subst w'. by apply (co_irr WFG w). }
  forward eapply (Execution.same_thread WFG w' w) as SBW; try (by vauto).
  { red. ins. by apply (proj1 Eninit_non_init w'). }
  des.
  { red in SBW. des.
    { subst w'. by apply (co_irr WFG w). }
    red in SBW. apply seq_eqv_lr in SBW. desc.
    forward eapply (proj1 tb_respects_sb w' w) as H_; [basic_solver| ].
    apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]]. 
    unfold trace_before in *. lia. }
  forward eapply (@vis_respects_sb_w w w') as VIS. 
  { red. splits; vauto. }
  do 2 red in VIS. des.
  { red in VIS. desc. vauto. }
  simpl in COw'w. apply seq_eqv_lr in COw'w.
  apply seq_eqv_lr in VIS. desc.
  red in COw'w0. desc. do 2 red in COw'w0. des.
  { red in COw'w0. desc. apply (proj1 Eninit_non_init w'). vauto. }
  apply seq_eqv_lr in COw'w0. desc. lia. 
Qed.

Lemma w_sbloc_fr_implies_co: ⦗is_w⦘ ⨾ restr_eq_rel loc (sb G) ⨾ fre G ⊆ co G.
Proof.
  rewrite seq_eqv_l. unfold seq. red. intros w1 w2 [Wx [r [[SBw1r LOCw1r] FRErw2]]]. 
  apply seq_eqv_lr. apply (wf_freD WFG) in FRErw2. apply seq_eqv_lr in FRErw2.
  destruct FRErw2 as [Rr [FRErw2 Ww2]].
  apply (wf_freE WFG) in FRErw2. apply seq_eqv_lr in FRErw2. desc.
  assert (EG w1) as Ew1. 
  { red in SBw1r. apply seq_eqv_lr in SBw1r. by desc. }
  splits; vauto.
  assert (loc r = loc w2) as LOCrw2. 
  1: { apply eq_Transitive with (y := loc r); auto.
       pose proof (proj2 (fri_union_fre G)). rewrite (wf_frl WFG) in H.
       apply H. vauto. }
  red. split; [| congruence]. 
  (* assert (EG w2) as Ew2. *)
  (* { apply  (wf_freE WFG) in FRErw2. apply seq_eqv_lr in FRErw2. by desc. } *)
  destruct (classic (w1 = w2)) as [EQ|NEQ].
  { subst w2. exfalso. apply (@sb_fr_irr w1). red. exists r. split; auto.
    apply fri_union_fre. vauto. }
  forward eapply (@wf_co_total G WFG (loc r) w1) as TOTAL; eauto. 
  1,2: done.
  des.
  { simpl in TOTAL. apply seq_eqv_lr in TOTAL. desc. red in TOTAL0. by desc. }
  exfalso. 
  cut (fr G r w1).
  { ins. exfalso. apply (@sb_fr_irr w1). basic_solver. }
  red. red. split.
  2: { red. ins. red in H. desc. subst. eapply sb_irr. eauto. }
  red. do 2 (do 2 red in FRErw0; desc).
  red in FRErw0. destruct FRErw0 as [w' [RFw'r COw'w2]].
  exists w'. split; auto. apply (co_trans WFG) with (y := w2); auto.
Qed. 

Lemma rmw_is_w: is_rmw ⊆₁ is_w. 
Proof. red. ins. destruct x; vauto. destruct l; vauto. Qed. 
  
Lemma rmw_is_r: is_rmw ⊆₁ is_r. 
Proof. red. ins. destruct x; vauto. destruct l; vauto. Qed. 
  
Lemma ninit_vis_helper x y (E'x : Eninit x) (E'y : Eninit y) (VIS: vis_lt x y):
  vis x < vis y.
Proof. 
  do 2 red in VIS. des; vauto.
  { exfalso. red in VIS. desc. by apply (proj1 Eninit_non_init x). }
  apply seq_eqv_lr in VIS. by desc.
Qed. 
  
Lemma vis_respects_ppo: ppo G ⊆ vis_lt. 
Proof.
  unfold ppo.
  red. ins. red in H. desc.
  destruct (vis_lt_init_helper H) as [| [E'x E'y]]; auto. 
  red. right. apply seq_eqv_lr. splits; auto.
  unfold cross_rel in H0. apply not_and_or in H0.
  red in H. apply seq_eqv_lr in H. destruct H as [_ [SBxy _]]. 
  des.
  { rewrite nonw_vis; auto. 
    pose proof (TI_LE_VIS y E'y).
    forward eapply (proj1 tb_respects_sb x y) as H_; [basic_solver| ].
    apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]].
    red in TB. lia. }
  assert (is_w y) as Wy.
  { destruct y; vauto. destruct l; vauto. }
  destruct (is_w x) eqn:X.
  2: { replace (vis x) with (trace_index x).
       { pose proof (TI_LE_VIS y E'y).
         forward eapply (proj1 tb_respects_sb x y) as H_; [basic_solver| ].
         apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]].
         red in TB. lia. }
       rewrite nonw_vis; vauto. }
  forward eapply (@vis_respects_sb_w x y) as VIS. 
  { red. splits; vauto. red. apply seq_eqv_lr. splits; vauto. }
  by apply ninit_vis_helper. 
Qed.


Lemma vis_respects_impliedfence: implied_fence G ⊆ vis_lt.
Proof.
  unfold implied_fence.
  apply inclusion_union_l.
  { rewrite seq_eqv_r. red. intros x y [SBxy RMWy].
    destruct (vis_lt_init_helper SBxy) as [| [E'x E'y]]; auto.
    red. right.
    apply seq_eqv_lr in SBxy. desc.
    apply seq_eqv_lr. splits; auto.
    apply rmw_is_w in RMWy.
    destruct (is_w x) eqn:X.
    { forward eapply (@vis_respects_sb_w x y) as VIS.
      { red. splits; vauto. red. apply seq_eqv_lr. vauto. }
      by apply ninit_vis_helper. }
    rewrite nonw_vis; vauto.  
    apply NPeano.Nat.lt_le_trans with (m := trace_index y).
    2: { by apply (TI_LE_VIS y). }
    forward eapply (proj1 tb_respects_sb x y) as H_; [basic_solver| ]. 
    apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]].
    red in TB. lia. }
  rewrite seq_eqv_l. red. intros x y [RMWx SBxy].
  destruct (vis_lt_init_helper SBxy) as [| [E'x E'y]]; auto.
  red. right.
  apply seq_eqv_lr in SBxy. desc.
  apply seq_eqv_lr. splits; auto. 
  apply NPeano.Nat.lt_le_trans with (m := trace_index y).
  2: { by apply (TI_LE_VIS y). }
  rewrite rmw_vis; auto.
  forward eapply (proj1 tb_respects_sb x y) as H_; [basic_solver| ].
  apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]].
  red in TB. lia. 
Qed. 


Lemma empty_inter_minus_same {A: Type} (X Y: A -> Prop):
  X ∩₁ Y ≡₁ ∅ <-> X \₁ Y ≡₁ X.
Proof.
  split.
  { ins. red. split; [basic_solver| ].
    red. ins.
    red in H. desc.
    red. split; auto.
    red in H. specialize (H x).
    red. ins. apply H. basic_solver. }
  { intros. rewrite <- H. basic_solver. }
Qed.

Lemma TSO_op_implies_decl:
  (fun e => trace_elems tr (inl e)) ≡₁ acts G \₁ is_init /\
  
  Wf G /\ mem_fair G /\
  rf_complete G /\
  TSO_consistent G.
Proof.
  splits.
  { simpl. unfold EG.
    rewrite set_minus_union_l, set_minusK, set_union_empty_l.
    unfold Eninit. eapply set_equiv_rel_Transitive; [apply set_equiv_refl| ].
    symmetry. apply empty_inter_minus_same. rewrite set_interC. apply Eninit_non_init. }
  { apply WFG. }
  { red. apply fsupp_union_iff.
    apply fsupp_mon with (r' := restr_eq_rel loc vis_lt); [| apply fsupp_vis_loc].
    rewrite restr_eq_rel_same_loc. apply inclusion_union_l.
    { apply inclusion_inter_r; [apply co_implies_vis_lt | apply (wf_col WFG)]. }
    { apply inclusion_inter_r; [apply fr_implies_vis_lt | apply (wf_frl WFG)]. }
  }
  { red. simpl. unfold set_inter at 1. red. ins. desc.  
    forward eapply read_source as [w W]; eauto.
    red in W. desc. simpl in W. apply seq_eqv_lr in W. desc. 
    red. exists w. apply seq_eqv_lr. splits; vauto. }
  {
    assert (rfe G ∪ coe G ∪ fre G ⊆ vis_lt) as EXT_ORDER.
    { arewrite (coe G ⊆ co G). arewrite (fre G ⊆ fr G). 
      rewrite rfe_implies_vis_lt, co_implies_vis_lt, fr_implies_vis_lt.
      by rewrite !unionK. }
    assert (acyclic (TSO_hb G)) as TSO_HB_ACYC.  
    { red. unfold TSO_hb. rewrite ct_of_ct. 
      rewrite vis_respects_ppo, vis_respects_impliedfence, rfe_implies_vis_lt, co_implies_vis_lt, fr_implies_vis_lt. rewrite !unionK.
      cdes vis_SPO. apply trans_irr_acyclic; auto. }
    red. split; auto. red.
    do 2 rewrite unionA with (r1 := restr_eq_rel _ _ ).
    rewrite rel_helper. rewrite <- unionA, unionK.
    apply acyclic_union1.
    { rewrite inclusion_restr_eq. apply sb_acyclic. }
    { apply inclusion_acyclic with (r' := TSO_hb G); auto.
      unfold TSO_hb. rewrite <- ct_step. 
      rewrite coi_union_coe, fri_union_fre. basic_solver. }
    rewrite ct_of_trans.
    2: { apply restr_eq_trans, sb_trans. }
    arewrite (restr_eq_rel loc (sb G) ⊆ ppo G ∪ (⦗is_w⦘ ⨾ restr_eq_rel loc (sb G) ⨾ ⦗is_r⦘)).
    { rewrite sb_ppo_ext at 1. rewrite restr_eq_union.
      apply union_mori; basic_solver. }
    rewrite seq_union_l. 
    rewrite vis_respects_ppo. rewrite EXT_ORDER at 1. 
    rewrite ct_begin with (r := (rfe G ∪ coe G ∪ fre G)). rewrite EXT_ORDER at 2.
    arewrite (is_r ≡₁ (is_r ∩₁ is_rmw) ∪₁ (is_r \₁ is_rmw)).
    { rewrite set_minusE. rewrite <- set_inter_union_r.
      rewrite <- set_compl_minus, set_minusK. basic_solver. }
    arewrite (is_r ∩₁ is_rmw ⊆₁ is_rmw) by basic_solver. 
    rewrite id_union. case_union _ _. do 2 rewrite seq_union_r. 
    arewrite (restr_eq_rel loc (sb G) ⨾ ⦗fun a : Event => is_rmw a⦘ ⊆ vis_lt).
    { rewrite inclusion_restr_eq. eapply inclusion_trans. 
      2: { eapply vis_respects_impliedfence. }
      vauto. }
    rewrite EXT_ORDER at 1. rewrite <- ct_begin. rewrite inclusion_seq_eqv_l at 1.
    rewrite <- unionA, unionK.  
    
    arewrite (⦗is_r \₁ is_rmw⦘ ⨾ (rfe G ∪ coe G ∪ fre G) ⊆ fre G).
    { rewrite (wf_rfeD WFG), (wf_coeD WFG).
      rewrite <- seq_union_r. case_union _ _ .
      seq_rewrite <- id_inter.
      arewrite ((is_r \₁ is_rmw) ∩₁ is_w ≡₁ ∅); [| basic_solver]. 
      red. split; [| basic_solver]. red. ins. do 2 (red in H; desc).
      destruct x; vauto; destruct l; vauto. }
    sin_rewrite w_sbloc_fr_implies_co. rewrite co_implies_vis_lt.
    rewrite <- seq_union_r. rewrite inclusion_t_rt, unionK. rewrite <- ct_begin.
    unfold acyclic. rewrite ct_of_ct. fold (acyclic vis_lt).
    cdes vis_SPO. apply trans_irr_acyclic; auto. }
Qed.

End Op2Decl.

