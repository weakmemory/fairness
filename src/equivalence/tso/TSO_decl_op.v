Require Import AuxRel.
Require Import Labels.
Require Import Events.
Require Import Lia.
Require Import Arith.
Require Import Execution.
Require Import IndefiniteDescription.
Require Import PropExtensionality.
Require Import List.
Import ListNotations. 
Require Import TraceWf.
From hahn Require Import Hahn.
Require Import TSO.
Require Import ChoiceFacts.
Require Import FinFun.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Backport.
Require Import SetSize.
Require Import ListSum.
Require Import AuxProp.

Set Implicit Arguments.

Ltac liaW no := (destruct no; [done|simpl in *; lia]).

Section BlockExpand.

Variable (A: Type) (bf: nat -> list A). 
Hypothesis NEMPTY: forall i, bf i <> [].

Definition block_pos_fun {A: Type} (f: nat -> list A) i d a :=
  Some a = nth_error (f i) d.

Definition block_trace_elems_fun (f: nat -> list TSO_label) :=
  fun e => exists i d, block_pos_fun f i d (inl e). 

Definition block_trace_prefix i := map bf (List.seq 0 i). 

Definition a_ : A.
  set (bf0 := bf 0).
  destruct (bf 0) eqn:BF0.
  { by destruct (@NEMPTY 0). }
  exact a. 
Qed. (* don't care about definition, just use some a:A as default for 'nth' *)

Definition expanded :=
  fun i => let lbls := flatten (block_trace_prefix (S i)) in
        nth i lbls a_.

Lemma btpS i: block_trace_prefix (S i) = block_trace_prefix i ++ [bf i]. 
Proof.
  unfold block_trace_prefix. by rewrite seqS, map_app.
Qed.

Lemma btp0: block_trace_prefix 0 = []. 
Proof.
  unfold block_trace_prefix. by rewrite seq0.
Qed. 

Lemma block_len j:
  length (bf j) > 0. 
Proof.
  destruct (bf j) eqn:BFj; simpl; [by destruct (NEMPTY BFj) | lia].
Qed.

Lemma index_lt_flatten i: i < length (flatten (block_trace_prefix (S i))).
Proof.
  induction i.
  { unfold block_trace_prefix. rewrite <- mk_listE. simpl.
    rewrite app_length. simpl. pose proof (block_len 0). lia. }
  rewrite btpS, flatten_app, length_app. simpl. rewrite length_app. simpl.
  pose proof (block_len (S i)). lia.
Qed.

Lemma index_lt_flatten' i: i < length (flatten (block_trace_prefix i)) + 1. 
Proof.
  induction i; [lia| ].
  rewrite btpS, flatten_app, length_app. simpl. rewrite length_app. simpl.
  pose proof (block_len i). lia. 
Qed.

Lemma btp_eq n i (LT: i < n): nth_error (block_trace_prefix n) i = Some (bf i).
Proof.
  unfold block_trace_prefix. erewrite map_nth_error with (d := i); auto.
  apply lt_diff in LT. desc. subst n. rewrite seq_app.
  rewrite nth_error_app2.
  2: { by rewrite seq_length. }
  by rewrite Nat.add_0_l, seq_length, Nat.sub_diag. 
Qed.

Lemma btp_mon m n (LE: m <= n):
  length (flatten (block_trace_prefix m)) <= length (flatten (block_trace_prefix n)).
Proof.
  apply le_diff in LE. desc. subst n.
  unfold block_trace_prefix. rewrite seq_add, map_app, flatten_app, length_app.
  lia.
Qed. 


Lemma expanded_corr
      n (a: A) (AT_EXP: expanded n = a)
      i d (N: n = length (flatten (block_trace_prefix i)) + d)
      (LT: d < length (bf i))
      (* H : d <> length (bf i) - 1 *):
  nth_error (bf i) d = Some a.
Proof.
  unfold expanded in AT_EXP.
  rewrite N in AT_EXP.
  assert (exists l, flatten
                 (block_trace_prefix
                    (S (length (flatten (block_trace_prefix i)) + d))) =
               flatten (block_trace_prefix i) ++ (bf i) ++ l).
  { cut (i < (S (length (flatten (block_trace_prefix i)) + d))).
    { ins. apply lt_diff in H. desc. rewrite H.
      unfold block_trace_prefix.
      rewrite seq_add. rewrite Nat.add_0_l, seqS_hd.
      rewrite map_app, flatten_app. simpl. eauto. }
    pose proof (index_lt_flatten' i). lia. }
  desc. rewrite H in AT_EXP.
  rewrite app_nth2 in AT_EXP; [| lia]. rewrite minus_plus in AT_EXP.
  rewrite app_nth1 in AT_EXP; [| lia]. 
  rewrite <- AT_EXP. apply nth_error_nth'. lia.
Qed. 

Lemma expanded_src n a (AT_EXP: expanded n = a):
  exists i d,
    n = length (flatten (block_trace_prefix i)) + d /\
    nth_error (bf i) d = Some a.
Proof.
  generalize dependent a. induction n.
  { ins. exists 0. exists 0. unfold expanded in AT_EXP. unfold block_trace_prefix in *.
    replace (List.seq 0 1) with [0] in AT_EXP by vauto.
    simpl in AT_EXP. rewrite app_nth1 in AT_EXP.
    2: { apply block_len. }
    pose proof (@NEMPTY 0). destruct (bf 0); [done| ]. vauto. }
  ins.
  remember (expanded n) as p. specialize (IHn p eq_refl) as [i [d [N POSp]]].
  assert (d < length (bf i)) as LT.
  { apply nth_error_Some. apply opt_val; eauto. }
  destruct (classic (d = length (bf i) - 1)).
  { exists (S i). exists 0.
    assert (S n = length (flatten (block_trace_prefix (S i)))) as SN. 
    { rewrite btpS, flatten_app, length_app.
      simpl. rewrite length_app. simpl. lia. }
    split; [lia| ].
    eapply expanded_corr; eauto; [lia| ].
    pose proof (block_len (S i)). lia. }
  exists i. exists (S d). split; [lia| ].
  eapply expanded_corr; eauto; lia. 
Qed.

Lemma expanded_dst n a i d
      (N: n = length (flatten (block_trace_prefix i)) + d)
      (BLOCK_POS: nth_error (bf i) d = Some a):
  expanded n = a.
Proof. 
  unfold expanded, block_trace_prefix.
  assert (i <= n).
  { subst n. forward eapply index_lt_flatten' with (i := i) as LT; eauto. lia. }
  apply le_diff in H as [k DIFF].
  rewrite DIFF at 2. 
  replace (S (i + k)) with (i + S k) by lia. 
  rewrite seq_add, map_app, flatten_app, Nat.add_0_l.
  rewrite app_nth2.
  2: { red. subst n. unfold block_trace_prefix. lia. }
  subst n. rewrite minus_plus.
  rewrite seqS_hd. simpl. 
  rewrite app_nth1.
  2: { apply nth_error_Some, opt_val. eauto. }
  apply nth_error_nth. auto.
Qed.


End BlockExpand. 


Section FunDefinitions.

Definition LTS_fun_limP {State Label : Type} (lts : LTS State Label) (f: nat -> Label) lim fl' :=
    LTS_init lts (fl' 0) /\
    (forall i, NOmega.lt_nat_l i lim -> LTS_step lts (fl' i) (f i) (fl' (S i))). 
  
Definition LTS_fun_lim {State Label : Type} (lts : LTS State Label) (f: nat -> Label) lim :=
  exists fl': nat -> State, LTS_fun_limP lts f lim fl'. 
  
Definition fun_states {st lb: Type} {lts: LTS st lb}
           f lim (TRACE: LTS_fun_lim lts f lim) :=
  proj1_sig (constructive_indefinite_description _ TRACE).

Definition fun_wf_lim (f: nat -> TSO_label) (lim: nat_omega) :=
forall (i j : nat) (thread : Tid) (index1 index2 : nat)
  (lbl1 lbl2 : Lab),
i < j ->
NOmega.lt_nat_l j lim ->
f i = inl (ThreadEvent thread index1 lbl1) ->
f j = inl (ThreadEvent thread index2 lbl2) -> index1 < index2.

Definition TSO_fair_fun_lim f lim st (TSO_TRACE: LTS_fun_limP TSO_lts f lim st) :=
  forall i tid
    (DOM_EXT: NOmega.le (NOnum i) lim)
    (ENABLED: enabled (st i) tid),
  exists j, i <= j /\ (NOmega.lt_nat_l j lim) /\
       f j = inr tid. 

End FunDefinitions.

Section BlockFunDefinitions.

Inductive TSO_block_step: TSOMemory -> list (TSO_label) -> TSOMemory -> Prop :=
| TSO_block_step_none st:
    TSO_block_step st [] st
| TSO_block_step_next st1 st2 st' lbl lbls' (STEP: TSO_step st1 lbl st')
                      (STEPS': TSO_block_step st' lbls' st2):
    TSO_block_step st1 (lbl :: lbls') st2. 

Definition TSO_block_lts : LTS TSOMemory (list TSO_label) := 
{| LTS_init := eq TSO.Minit;
   LTS_final := ∅;
   LTS_step := fun st1 lbls st2 => TSO_block_step st1 lbls st2 /\ lbls <> [] |}.
 
Definition block_trace_wf_prefix_fun (f: nat -> list TSO_label) lim :=
  forall (i j di dj : nat) (thread : Tid) (index1 index2 : nat)
  (lbl1 lbl2 : Lab),
    (i < j \/ i = j /\ di < dj) ->
    (NOmega.lt_nat_l j lim) ->
    block_pos_fun f i di (inl (ThreadEvent thread index1 lbl1)) ->
    block_pos_fun f j dj (inl (ThreadEvent thread index2 lbl2)) ->
    index1 < index2.

Definition block_TSO_fair_fun_lim (bf: nat -> list TSO_label) lim st :=
  forall i tid
    (DOM_EXT: NOmega.le (NOnum i) lim)
    (ENABLED: enabled (st i) tid),
  exists j, i <= j /\ (NOmega.lt_nat_l j lim) /\
       In (inr tid) (bf j). 

End BlockFunDefinitions.

Section FunTrace.
Variable (A: Type) (size: nat_omega). 
  
Definition fun_trace_equiv (f: nat -> A) (tr: trace A) :=
  trace_length tr = size /\
  (forall d i (DOM: NOmega.lt_nat_l i size), trace_nth i tr d = f i).
  

Lemma trace_of_fun (f: nat -> A):
  exists tr, fun_trace_equiv f tr. 
Proof.
  unfold fun_trace_equiv. 
  destruct size.
  { by exists (trace_inf f). }
  exists (trace_fin (map f (List.seq 0 n))). split.
  { simpl. f_equal. rewrite map_length. apply seq_length. }
  ins. rewrite <- mk_listE. rewrite nth_mk_list.
  destruct (le_lt_dec n i); auto. lia.
Qed.

End FunTrace.   
  
Section Utils.

Lemma TSO_step_deterministic st st1 st2 lbl
      (STEP1: TSO_step st lbl st1) (STEP2: TSO_step st lbl st2):
  st1 = st2. 
Proof.
  inversion STEP1; inversion STEP2; congruence.
Qed.

Lemma TSO_block_step_deterministic st st1 st2 lbls
      (STEP1: TSO_block_step st lbls st1) (STEP2: TSO_block_step st lbls st2):
  st1 = st2.
Proof.
  generalize dependent st.  generalize dependent st1. generalize dependent st2. induction lbls.
  { ins. inversion STEP1. inversion STEP2. congruence. }
  ins. inversion STEP1. inversion STEP2. subst st0 st3 st4 st5 lbl lbl0 lbls'0 lbls'.  
  forward eapply (@TSO_step_deterministic st st' st'0) as EQ; eauto.
  subst. eapply IHlbls; eauto.
Qed. 
  
Lemma firstn_map {A B: Type} (f: A -> B) l n:
  map f (firstn n l) = firstn n (map f l).
Proof.
  generalize dependent n. induction l. 
  { ins. by destruct n. }
  ins. destruct n; [done| ].
  simpl. by rewrite IHl. 
Qed.

Lemma NOmega_le_lt_or_eq (x y: nat_omega) (LE: NOmega.le x y):
  x = y \/ NOmega.lt x y.
Proof.
  destruct x, y; vauto. simpl in *.
  forward eapply le_lt_or_eq as OR; eauto. des; vauto.
Qed.

Lemma last_pos {A: Type} (l: list A) a d (NONDEF: a <> d):
  last l d = a <-> Some a = nth_error l (length l - 1).
Proof.
  split.
  { ins. generalize dependent a. induction l.
    { ins. vauto. }
    ins. rewrite Nat.sub_0_r. destruct l.
    { subst a0. by simpl. }
    simpl. specialize_full IHl; eauto.
    simpl in IHl. by rewrite Nat.sub_0_r in IHl. }
  { ins. generalize dependent a. induction l.
    { ins. }
    ins. rewrite Nat.sub_0_r in H.
    destruct l.
    { simpl in *. by inversion H. }
    apply IHl; auto. simpl in H. simpl. by rewrite Nat.sub_0_r. }
Qed.

Lemma dom_bunion (A B: Type) (s : B -> Prop) (r : B -> relation A):
  dom_rel (⋃x ∈ s, r x) ≡₁ (⋃₁x ∈ s, dom_rel (r x)).
Proof. basic_solver. Qed.

Lemma emiT {A: Type} {P: Prop} (b1 b2: A) (p: P):
  (ifP P then b1 else b2) = b1.
Proof. by destruct (excluded_middle_informative P). Qed. 

Lemma emiF {A: Type} {P: Prop} (b1 b2: A) (np: ~ P):
  (ifP P then b1 else b2) = b2.
Proof. by destruct (excluded_middle_informative P). Qed.

Lemma inj_map {A B: Type} (f: A -> B) l1 l2 (INJ: Injective f)
      (MAP_EQ: map f l1 = map f l2):
  l1 = l2.
Proof.
  generalize dependent l2. induction l1.
  { ins. symmetry in MAP_EQ. by apply List.map_eq_nil in MAP_EQ. }
  destruct l2; [done| ].
  ins. inversion MAP_EQ.
  apply INJ in H0. subst a0. f_equal. by apply IHl1.
Qed.

Lemma inj_nth_error {A B: Type} (f: A -> B) l x (INJ: Injective f) k
      (MAP_NTH: nth_error (map f l) k = Some (f x)):
  nth_error l k = Some x.
Proof.
  generalize dependent x. generalize dependent k. induction l.
  { ins. by destruct k. }
  ins. destruct k.
  { simpl in *. inversion MAP_NTH. apply INJ in H0. by subst. }
  simpl in *. by apply IHl.
Qed. 
  
Lemma inj_in {A B: Type} (f: A -> B) l x (INJ: Injective f)
      (MAP_IN: In (f x) (map f l)):
  In x l.
Proof.
  induction l; [done| ].
  simpl in MAP_IN. des.
  { apply INJ in MAP_IN. by subst. }
  apply in_cons, IHl, MAP_IN.
Qed. 

Lemma finite_minus {A: Type} (S1 S2: A -> Prop) (FIN: set_finite S1):
  set_finite (S1 \₁ S2).
Proof.
  arewrite (S1 \₁ S2 ⊆₁ S1); basic_solver.
Qed.

Lemma finite_inter {A: Type} (S1 S2: A -> Prop) (FIN: set_finite S1):
  set_finite (S1 ∩₁ S2).
Proof.
  arewrite (S1 ∩₁ S2 ⊆₁ S1); basic_solver.
Qed.


Lemma firstn_end {A: Type} (l: list A) n x (NTH: Some x = List.nth_error l n):
  firstn (n + 1) l = firstn n l ++ cons x nil.
Proof.
  ins. 
  symmetry in NTH. apply nth_error_split in NTH as [l1 [l2 [CAT H]]].
  rewrite <- H. pose proof (@firstn_app_2 A 1 l1 (x :: l2)).
  rewrite CAT. simpl in H0. rewrite H0.
  pose proof (@firstn_app_2 A 0 l1). simpl in H1. rewrite app_nil_r, NPeano.Nat.add_0_r in H1.
  rewrite H1. auto. 
Qed.

Lemma Forall_index {A: Type} (l: list A) P:
    Forall P l <-> forall x i (XI: Some x = nth_error l i), P x.
Proof.
  split.
  { induction l; [by destruct i| ].
    ins. 
    inv H. destruct i; simpl in XI; [by inversion XI| ].
    eapply IHl; eauto. }
  induction l; [done| ].
  ins. constructor.
  { by apply H with (i := 0). }
  apply IHl. ins. by apply H with (i := S i). 
Qed.

End Utils.

Require Import Orders Sorting ZArith.
Module SBOrder <: TotalLeBool.
  Definition t := Event.

  Definition leb e1 e2 :=
    match e1, e2 with
    | InitEvent l1, InitEvent l2 => true
    | InitEvent _, ThreadEvent _ _ _ => true
    | ThreadEvent _ _ _, InitEvent _ => false
    | ThreadEvent thread1 index1 _, ThreadEvent thread2 index2 _ =>    
      (thread1 <? thread2) || ((thread1 =? thread2) && (index1 <=? index2))
    end. 

  Lemma leb_total : forall x y : t, leb x y = true \/ leb y x = true.
  Proof.
    ins. destruct x, y; simpl; try by intuition.
    pose proof (NPeano.Nat.lt_trichotomy thread thread0). des.
    { apply Nat.ltb_lt in H. rewrite H. intuition. }
    { subst thread0.
      destruct (Nat.le_ge_cases index index0); apply Nat.leb_le in H; rewrite H, Nat.eqb_refl; intuition. }
    { apply Nat.ltb_lt in H. rewrite H. intuition. }
  Qed.
  
  Lemma leb_trans: Transitive leb.
  Proof.
    red. ins. 
    destruct x, y, z; simpl in *; try (by intuition).
    apply Bool.orb_true_intro.
    des.
    1, 2, 3: left; apply Nat.ltb_lt. 
    { apply Nat.ltb_lt in H0. apply Nat.ltb_lt in H. lia. }
    { apply Nat.ltb_lt in H0. apply Nat.eqb_eq in H. lia. }
    { apply Nat.ltb_lt in H. apply Nat.eqb_eq in H0. lia. }
    { right. apply andb_true_intro.
      apply Nat.eqb_eq in H0. apply Nat.eqb_eq in H.
      apply Nat.leb_le in H1. apply Nat.leb_le in H2.
      split; [apply Nat.eqb_eq| apply Nat.leb_le]; lia. }
  Qed. 

End SBOrder.

Module SBSort := Sort SBOrder.


Section Decl2Op.

Variable G : execution.
Notation "'E'" := (acts G).

Hypothesis WF: Wf G.
Hypothesis FAIR: mem_fair G.
Hypothesis RF_COMPL: rf_complete G.
Hypothesis TSO_CONS: TSO_consistent G.
(* Hypothesis FIN_THREADS: bounded_threads G.  *)
Hypothesis BOUNDED_THREADS: exists n, forall e, (E \₁ is_init) e -> tid e < n.
Hypothesis NO_TID0: forall e, (E \₁ is_init) e -> tid e <> 0. 

Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

Lemma TSO_hb_spo: strict_partial_order (TSO_hb G).
Proof.
  red. split.
  { cdes TSO_CONS. generalize TSO_CONS0.
    unfold TSO_hb, acyclic. by rewrite ct_of_ct. }
  { unfold TSO_hb. apply transitive_ct. }
Qed. 

(* Lemma TSO_hb_G: TSO_hb G ⊆ E × (E \₁ is_init). *)
Lemma TSO_hb_G: (ppo G ∪ implied_fence G ∪ rfe G ∪ co G ∪ fr G) ⊆ E × (E \₁ is_init).
Proof.
  arewrite (ppo G ∪ implied_fence G ⊆ sb G). arewrite (rfe G ⊆ rf G). 
  rewrite wf_rfE, wf_coE, wf_frE; auto.
  unfold fr. rewrite no_rf_to_init, <- co_ninit, no_sb_to_init; auto.  
  unfold sb. basic_solver.
Qed.

Ltac contra name :=
  match goal with
  | |- ?gl => destruct (classic gl) as [|name]; [done|exfalso]
  end.

Lemma sb_order3 x y z thread (NEQxy: x <> y) (NEQyz: y <> z) (NEQxz: x <> z)
      (X: (E ∩₁ Tid_ thread \₁ is_init) x) (Y: (E ∩₁ Tid_ thread \₁ is_init) y) (Z: (E ∩₁ Tid_ thread \₁ is_init) z):
  exists a b c, (sb G a b /\ sb G b c) /\
           (In a [x; y; z]) /\ 
           (In b [x; y; z]) /\ 
           (In c [x; y; z]). 
           (* (E ∩₁ Tid_ thread \₁ is_init) a /\ (E ∩₁ Tid_ thread \₁ is_init) b /\ (E ∩₁ Tid_ thread \₁ is_init) c. *)
Proof.
  forward eapply (Execution.same_thread WF x y) as SB_xy. 
  1-4: by unfolder'; basic_solver.
  forward eapply (Execution.same_thread WF y z) as SB_yz. 
  1-4: by unfolder'; basic_solver.
  forward eapply (Execution.same_thread WF x z) as SB_xz. 
  1-4: by unfolder'; basic_solver.
  des.
  all: unfold HahnRelationsBasic.clos_refl in *; des; try done.
  all: do 3 eexists; split; [eauto| intuition]. 
Qed.


Lemma seq_nth_error n k (DOM: k < n):
  nth_error (List.seq 0 n) k = Some k.
Proof.
  apply lt_diff in DOM. desc. rewrite DOM, seq_add, nth_error_app2.
  2: { rewrite seq_length. lia. }
  by rewrite Nat.add_0_l, seqS_hd, seq_length, Nat.sub_diag.
Qed. 

Lemma TSO_sb_n_total: exists n,
    n_total (E \₁ is_init)
    (⦗E \₁ is_init⦘ ⨾ (ppo G ∪ implied_fence G) ⨾ ⦗E \₁ is_init⦘)
    n.
Proof.
  cdes BOUNDED_THREADS. exists (2 * n).
  red. ins. 
  
  assert (length l = list_sum
                       (map (fun t => length (filterP (fun e => tid e = t) l))
                            (List.seq 0 n))).
  { forward eapply list_sum_separation with (tid_ := tid) (domB := List.seq 0 n) as EQ; eauto.
    { apply seq_NoDup. }
    { ins. apply in_seq0_iff. auto. }
    rewrite EQ. f_equal. rewrite seq_length.
    apply map_ext_in_iff. ins. f_equal. apply filterP_ext. ins.
    rewrite seq_nth_error; [intuition; clarify| ].
    by apply in_seq0_iff in H. } 
    
  assert (exists t, length (filterP Tid_ t l) >= 3) as [thread GE3].
  { contra LT3. forward eapply (@list_sum_bound (map (fun t : nat => length (filterP Tid_ t l)) (List.seq 0 n)) 2) as BOUND. 
    { ins. apply in_map_iff in INx. desc.
      contra GE. apply LT3. exists x0. lia. }
    rewrite map_length, seq_length in BOUND. lia. }
  
  assert (exists x y z, x <> y /\ y <> z /\ x <> z /\ ((E ∩₁ Tid_ thread \₁ is_init) ∩₁ (fun e => In e l)) x /\ ((E ∩₁ Tid_ thread \₁ is_init) ∩₁ (fun e => In e l)) y /\ ((E ∩₁ Tid_ thread \₁ is_init) ∩₁ (fun e => In e l)) z) as (x & y & z & NEQxy & NEQyz & NEQxz & X & Y & Z).
  { remember (filterP Tid_ thread l) as tl.
    destruct tl as [| x l_]; [simpl in GE3; lia| ].
    destruct l_ as [| y l_]; [simpl in GE3; lia| ].
    destruct l_ as [| z l_]; [simpl in GE3; lia| ].
    exists x. exists y. exists z.
    assert (forall e (INe: In e (x :: y :: z :: l_)), ((E ∩₁ Tid_ thread \₁ is_init)) e) as DOMe.
    { rewrite Heqtl. ins. apply in_filterP_iff in INe. desc.
      apply set_inter_minus_l. splits; intuition. }
    assert (forall e, In e [x; y; z] -> In e l) as DOMl.
    { ins. cut (In e (filterP (Tid_ thread) l)); [by apply in_filterP_iff| ].
      rewrite <- Heqtl. simpl. intuition. }
    assert (NoDup (x :: y :: z :: l_)) by (rewrite Heqtl; eapply nodup_filterP; eauto).
    splits.
    4-6: by (split; [| apply DOMl; intuition]; apply DOMe; simpl; intuition).
    { red. ins. subst. inversion H0. intuition. }
    { red. ins. subst. inversion H0. inversion H4. intuition. }
    { red. ins. subst. inversion H0. intuition. }
  }
  
  forward eapply (@sb_order3 x y z) as (a & b & c & [SBab SBbc] & A & B & C); auto.
  1-3: by unfolder'; desc; eauto.
  
  cut (exists u v, In u [x; y; z] /\ In v [x; y; z] /\ (ppo G ∪ implied_fence G) u v).
  { intros (u & v & INu & INv & REL). exists u. exists v. splits.
    { clear A B C.
      apply inclusion_union_l  with (r'' := sb G) in REL; [| unfold ppo; basic_solver | unfold implied_fence; basic_solver].
      red. ins. subst. eapply sb_irr; eauto. }
    { unfolder'. desc. simpl in INu.
      des; try congruence; done. }
    { unfolder'. desc. simpl in INv. des; try congruence; done. }
    apply seq_eqv_lr. splits; [| auto| ].
    { unfolder'. desc. simpl in INu. des; split; vauto. }
    { unfolder'. desc. simpl in INv. des; split; vauto. }
  }
  
  assert (forall e, In e [x; y; z] -> ((E ∩₁ Tid_ thread \₁ is_init) e /\ In e l)) as DOMe'.
  { ins. des; vauto. }
  pose proof (DOMe' _ A) as A_. pose proof (DOMe' _ B) as B_. pose proof (DOMe' _ C) as C_. desc.
  assert (forall x y, sb G x y -> x <> y) as NEQ.
  { ins. red. ins. apply (@sb_irr G x0). congruence. }
  pose proof (NEQ _ _ SBab) as NEQab. pose proof (NEQ _ _ SBbc) as NEQbc. clear NEQ.
  
  destruct a eqn:A'; [by unfolder'; intuition| ].
  destruct l0.
  { exists a. exists b.  splits; auto; [congruence| ].
    left. red. split; [congruence| ]. unfolder'. subst. intuition. }
  2: { exists a. exists b. splits; auto; [congruence| ].
       right. red. right. apply seq_eqv_l. splits; vauto. }
  
  destruct b eqn:B'; [by unfolder'; intuition| ].
  destruct l0.
  3: { exists a. exists b. splits; auto; [congruence| congruence| ].
       right. red. left. apply seq_eqv_r. splits; vauto. }
  2: { exists a. exists b. splits; auto; [congruence| congruence| ].
       left. red. split; vauto. unfolder'. intuition. }
  
  destruct c eqn:C'; [by unfolder'; intuition| ].
  destruct l0.
  3: { exists b. exists c. splits; auto; [congruence| congruence| ].
       right. red. left. apply seq_eqv_r. splits; vauto. }
  2: { exists a. exists c. splits; auto; [congruence| congruence| ].
       left. red. split.
       { eapply sb_trans; vauto. }
       unfolder'. subst. intuition. }
  exists b. exists c. splits; auto; [congruence| congruence| ].
  left. red. split; vauto.
  unfolder'. subst. intuition.
Qed. 

Lemma TSO_hb_fsupp: fsupp (⦗set_compl is_init⦘ ⨾ TSO_hb G).
Proof.
  unfold TSO_hb.
  cut (fsupp (⦗E \₁ is_init⦘ ⨾ (ppo G ∪ implied_fence G ∪ rfe G ∪ co G ∪ fr G) ⨾  ⦗E \₁ is_init⦘)⁺).
  { apply fsupp_mon.
    forward eapply dom_helper_3 with (r := union _ _ ) as [H _].
    rewrite H at 1; [clear H| by apply TSO_hb_G]. 
    rewrite clos_trans_rotl.
    rewrite <- !seqA.
    arewrite (⦗set_compl is_init⦘ ⨾ ⦗E⦘ ≡ ⦗E \₁ is_init⦘) by basic_solver.
    arewrite (⦗E \₁ is_init⦘ ⨾ ⦗E⦘ ≡ ⦗E \₁ is_init⦘) by basic_solver.
    rewrite clos_trans_rotl. rewrite !seqA, seq_eqvK.
    apply inclusion_refl2. }
  
  apply fsupp_ct with (s := E \₁ is_init).
  { eapply inclusion_acyclic; [apply inclusion_seq_eqv_l| ].
    eapply inclusion_acyclic; [apply inclusion_seq_eqv_r| ].
    cdes TSO_CONS. generalize TSO_CONS0. unfold TSO_hb, acyclic. by rewrite ct_of_ct. }
  { basic_solver. }
  { pose proof TSO_sb_n_total as [n NTOTAL].
    eapply has_finite_antichainsI; eauto. 
    eapply n_total_mori; eauto.
    { apply set_subset_refl2. }
    basic_solver 10.
  }
      
  cdes FAIR. 
  repeat case_union _ _. repeat apply fsupp_union.
  { eapply fsupp_mon; [| apply (fsupp_sb WF)]. unfold ppo. basic_solver. }
  { eapply fsupp_mon; [| apply (fsupp_sb WF)]. unfold implied_fence. basic_solver 10. }
  { eapply fsupp_mon; [| apply (fsupp_rf WF)]. unfold rfe. basic_solver. }
  { eapply fsupp_mon; [| apply FAIR0]. basic_solver. }
  { eapply fsupp_mon; [| apply FAIR1]. basic_solver. }
Qed.

Lemma enum_exists:
  exists enum, enumerates enum (acts G \₁ is_init) /\
          forall ix iy
            (DOMx: NOmega.lt_nat_l ix (set_size (E \₁ is_init)))
            (DOMy: NOmega.lt_nat_l iy (set_size (E \₁ is_init)))
            (ORD: TSO_hb G (enum ix) (enum iy)),
            ix < iy.
Proof.
  pose proof (countable_ninit WF) as CNT.
  forward eapply countable_ext with (r := ⦗set_compl is_init⦘ ⨾ TSO_hb G) as ENUM. 
  { apply (countable_ninit WF). }
  { cut (strict_partial_order (TSO_hb G)); [basic_solver 10| ].
    apply TSO_hb_spo. }
  { apply TSO_hb_fsupp. }
  des.
  { exfalso. apply ENUM. constructor. vauto. }
  eexists. split; eauto.
  ins.
  apply ENUM0. 
  1, 2: by apply set_lt_size.
  apply seq_eqv_l. split; auto. 
  apply enumeratesE' in ENUM. desc. specialize (INSET _ DOMx).
  red in INSET. by desc.
Qed. 
  
Definition enum: nat -> Event := proj1_sig (constructive_indefinite_description _ enum_exists). 

Lemma ENUM: enumerates enum (acts G \₁ is_init).
Proof.
  unfold enum. destruct (constructive_indefinite_description _ _). by desc. 
Qed. 

Lemma ENUM_ORDER ix iy
      (DOMx: NOmega.lt_nat_l ix (set_size (E \₁ is_init)))
      (DOMy: NOmega.lt_nat_l iy (set_size (E \₁ is_init)))
      (ORD: TSO_hb G (enum ix) (enum iy)):
  ix < iy.
Proof.
  unfold enum in ORD. destruct (constructive_indefinite_description _ _).
  simpl in *. intuition. 
Qed. 


Lemma G_INSET i (DOM: NOmega.lt_nat_l i (set_size (E \₁ is_init))):
  (E \₁ is_init) (enum i).
Proof.
  pose proof (proj1 (@enumeratesE' _ enum (E \₁ is_init)) ENUM).
  simpl in H. desc. by apply INSET.
Qed.

Lemma G_INJ i j
      (DOMi: NOmega.lt_nat_l i (set_size (E \₁ is_init)))
      (DOMj: NOmega.lt_nat_l j (set_size (E \₁ is_init)))
      (ENUM_EQ: enum i = enum j):
  i = j. 
Proof.
  pose proof (proj1 (@enumeratesE' _ enum (E \₁ is_init)) ENUM).
  simpl in H. desc. by apply INJ. 
Qed.

Lemma G_IND e (ENIe: (E \₁ is_init) e):
  exists i, NOmega.lt_nat_l i (set_size (E \₁ is_init)) /\ enum i = e.
Proof. 
  pose proof (proj1 (@enumeratesE' _ enum (E \₁ is_init)) ENUM).
  simpl in H. desc. by apply IND.
Qed. 


Definition covered_events i := map enum (List.seq 0 i). 

Definition cur_events i :=
  dom_rel (⦗E \₁ is_init⦘ ⨾ (sb G)^? ⨾ ⦗fun e => In e (covered_events i)⦘).

Definition sb_sort : list Event -> list Event := SBSort.sort. 

Lemma sb_sort1_tmp (a: Event): sb_sort [a] = [a].
Proof. by unfold sb_sort, SBSort.sort. Qed.

Lemma sb_sort_perm_tmp l: Permutation l (sb_sort l).
Proof.  unfold sb_sort. apply SBSort.Permuted_sort. Qed. 
    
Definition as_list {A: Type} (S: A -> Prop) (FIN: set_finite S):
  {l: list A | NoDup l /\ S ≡₁ (fun x : A => In x l)}.
    by apply constructive_indefinite_description, set_finiteE.
Qed.

Lemma ce_finite i: set_finite (cur_events i).
Proof.
  unfold cur_events.
  arewrite (⦗fun e => In e (covered_events i)⦘ ≡ bunion (fun e => In e (covered_events i)) (fun e => ⦗eq e⦘)) by basic_solver.
  rewrite !seq_bunion_r.
  rewrite dom_bunion. apply set_finite_bunion.
  { red. by exists (covered_events i). }
  ins.
  pose proof (fsupp_sb WF) as FSUPP. red in FSUPP. specialize (FSUPP a). desc.
  red. exists (a :: findom). ins.
  red in IN. desc. apply seq_eqv_lr in IN. desc. subst y.
  red in IN0. des; [by vauto| ]. right.
  apply FSUPP. apply seq_eqv_l. split; auto. red in IN. by desc.
Qed.

Definition Bf_events i: list Event :=
  let fin_diff := (@finite_minus _ (cur_events (S i)) (cur_events i) (ce_finite (S i))) in
  sb_sort (proj1_sig (as_list fin_diff)).

Definition Bf i : list TSO_label :=
  map inl (Bf_events i) ++ (ifP (is_regular_write' (enum i))
                            then [inr (tid (enum i))] else []).

Lemma Bf_events_labels i:
  (fun e : Event => In (inl e) (Bf i)) ≡₁ (fun x0 : Event => In x0 (Bf_events i)).
Proof.
  unfold Bf.
  split.
  2: { red. ins. by apply in_app_l, in_map. }
  red. ins. apply in_app_iff in H. des.
  { apply inj_in in H; auto. red. ins. by inversion H0. }
  exfalso. destruct (excluded_middle_informative _); [| done]. 
  simpl in H. des; done.
Qed. 

Lemma Bf_events_nth e i k:
  nth_error (Bf_events i) k = Some e <-> nth_error (Bf i) k = Some (inl e).
Proof.
  unfold Bf. split.
  { ins. rewrite nth_error_app1.
    { by apply map_nth_error. }
    rewrite length_map. apply nth_error_Some, opt_val. eauto. }
  { ins. destruct (Nat.lt_ge_cases k (length (map inl (Bf_events i): list TSO_label))).
    { rewrite nth_error_app1 in H; auto. eapply inj_nth_error; eauto.
      red. ins. by inversion H1. }
    rewrite nth_error_app2 in H; [| auto].
    replace (ifP is_regular_write' (enum i) then [inr (tid (enum i))] else []) with (map inr (ifP is_regular_write' (enum i) then [(tid (enum i))] else []): list TSO_label) in H; [| by destruct (excluded_middle_informative _)].
    apply nth_error_In, in_map_iff in H. desc. discriminate. }
Qed. 

Definition lbl_sb (lbl1 lbl2: TSO_label) :=
  match lbl1, lbl2 with
  | inl e1, inl e2 => sb G e1 e2
  | _, _ => True
  end. 

Lemma Bf_nodup i: NoDup (Bf i).
Proof.
  unfold Bf, Bf_events. apply nodup_append.
  { apply Injective_map_NoDup.
    { red. ins. by inversion H. }
    destruct (as_list _) as [l L]. desc. simpl in *.  
    by apply Permutation_NoDup with (l := l); [apply sb_sort_perm_tmp| ]. }
  { by destruct (excluded_middle_informative _). }
  { red. ins. destruct (excluded_middle_informative _); [| done].
    simpl in IN2. des; auto. subst a.
    apply in_map_iff in IN1. by desc. }
Qed.

Lemma covered_ext i: covered_events (S i) = covered_events i ++ [enum i].
Proof.
  unfold covered_events. by rewrite seqS, Nat.add_0_l, map_app.
Qed.


Lemma set_union_app {A: Type} (l1 l2: list A):
  (fun a => In a (l1 ++ l2)) ≡₁ (fun a => In a l1) ∪₁ (fun a => In a l2).
Proof.
  apply set_equiv_exp_iff. ins. unfold set_union. apply in_app_iff.
Qed.

Lemma ce_ext i: cur_events (S i) ≡₁ cur_events i ∪₁ (fun e => In (inl e) (Bf i)).
Proof.
  rewrite <- set_union_absorb_l with (s := cur_events i) (s' := cur_events (S i)).
  2: { unfold cur_events. red. ins. red in H. desc. apply seq_eqv_lr in H. desc.
       exists y. apply seq_eqv_lr. splits; auto.
       rewrite covered_ext. by apply in_app_l. }
  rewrite (AuxProp.set_union_minus_alt (cur_events (S i)) (cur_events i)), <- set_unionA.
  rewrite set_union_absorb_r with (s' := cur_events i); [| basic_solver].  
  apply set_equiv_union; [basic_solver| ]. 
  unfold Bf.
  unfold cur_events. 
  apply set_equiv_rel_Transitive  with (y := (fun e : Event =>
      In ((inl e): TSO_label)
        (map inl (sb_sort (proj1_sig
                             (as_list (finite_minus (cur_events i) (ce_finite (S i))))))))).
  2: { apply set_equiv_exp_iff. split; intuition.
       apply in_app_iff in H. des; auto.
       destruct (excluded_middle_informative _); simpl in H; des; done. }
  remember (as_list (finite_minus (cur_events i) (ce_finite (S i)))) as lst.
  destruct lst. simpl in *. desc. 
  rewrite a0. split.
  { red. ins. apply in_map. apply (@Permutation_in _ x (sb_sort x) x0 (sb_sort_perm_tmp x)); eauto. }
  red. ins. apply in_map_iff in H. desc. inversion H. subst x1.
  apply (@Permutation_in _ (sb_sort x) x x0); eauto.
  apply Permutation_sym, sb_sort_perm_tmp.
Qed.

Definition thread_prefix i thread : list Event :=
  sb_sort (proj1_sig (as_list (@finite_inter _ (cur_events i) (Tid_ thread) (ce_finite i)))).

Lemma thread_prefix_properties i thread e:
  In e (thread_prefix i thread) <-> ((cur_events i) ∩₁ Tid_ thread) e.
Proof.
  split.
  { intros IN. unfold thread_prefix in IN.
    destruct (as_list _) as [l L]. desc. simpl in *.
    apply L0. apply Permutation_in with (l := sb_sort l); auto.
    apply Permutation_sym, sb_sort_perm_tmp. }
  { intros [CEe TIDe]. unfold thread_prefix. 
    destruct (as_list _) as [l L]. desc. simpl in *.
    apply Permutation_in with (l := l); [by apply sb_sort_perm_tmp| ].
    by apply L0. }
Qed. 


Lemma Bf_ce_disjoint i: cur_events i ∩₁ (fun e => In (inl e) (Bf i)) ≡₁ ∅.
Proof.
  split; [| basic_solver].
  unfold Bf, Bf_events. destruct (as_list _). desc. simpl in *.
  destruct a0 as [_ NCUR].
  red. ins. red in H. desc.
  apply in_app_iff in H0. des.
  2: { destruct (excluded_middle_informative _); intuition.
       simpl in H0. des; by inversion H. }
  specialize (NCUR x0). specialize_full NCUR.
  { apply in_map_iff in H0. desc. inversion H0. subst x1.
    apply (@Permutation_in _ (sb_sort x) x x0); eauto.
    apply Permutation_sym, sb_sort_perm_tmp. }
  red in NCUR. by desc.
Qed.   

Lemma Bf_ce_diff i: (fun e => In (inl e) (Bf i)) ≡₁ cur_events (S i) \₁ cur_events i.
Proof.
  rewrite (ce_ext i). generalize (Bf_ce_disjoint i). basic_solver 10.
  Unshelve. eauto. eauto.
Qed.

Lemma CE_E i: cur_events i ⊆₁ E \₁ is_init. 
Proof. ins. unfold cur_events. basic_solver. Qed.

Lemma Bf_contents i
      (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init))):
  (fun e => In (inl e) (Bf i)) ≡₁ ((fun e => (sb G)^? e (enum i)) \₁ cur_events i) ∩₁ set_compl is_init.
Proof.
  rewrite Bf_ce_diff.
  split.
  { red. ins. red in H. desc. split. 
    2: { apply CE_E in H. generalize H. basic_solver. }
    split; auto. 
    pose proof (proj1 (ce_ext i) _ H). red in H1. des; [done| ].
    do 2 red in H. desc. apply seq_eqv_lr in H. desc.
    rewrite covered_ext in H3. apply in_app_iff in H3. des.
    { exfalso. apply H0. exists y. apply seq_eqv_lr. splits; vauto. }
    simpl in H3. des; [| done]. congruence. }
  { red. ins. red in H. desc. red in H. desc. split; auto.
    exists (enum i). apply seq_eqv_lr. splits; try vauto.
    2: { rewrite covered_ext. intuition. }
    red in H. des.
    { subst. by apply G_INSET. }
    red in H. apply seq_eqv_lr in H. desc. split; auto. }
Qed.

Lemma sort_clarification {A: Type} (r r': relation A) l
      (SORT: StronglySorted (r ∪ r') l)
      (NO': forall x y (INx: In x l) (INy: In y l), ~ r' x y):
  StronglySorted r l.
Proof.
  induction l; [done| ].
  apply StronglySorted_inv in SORT. desc.
  apply SSorted_cons.
  { apply IHl; auto.
    ins. apply NO'; by vauto. }
  apply Forall_forall. intros x INx.
  pose proof (Forall_forall ((r ∪ r') a) l) as [SORT' _].
  specialize (SORT' SORT0 x INx). red in SORT'. des; auto.
  specialize (NO' a x). specialize_full NO'; by vauto.
Qed.


Lemma sb_sort_sim l: (fun e => In e l) ≡₁ (fun e => In e (sb_sort l)).
Proof.
  apply set_equiv_exp_iff. split. 
  { ins. eapply Permutation_in; [apply sb_sort_perm_tmp| ]; auto. }
  { ins. eapply Permutation_in; [apply Permutation_sym, sb_sort_perm_tmp| ]; auto. }
Qed.

Lemma sorted_ordered {A: Type} (l: list A) (r: relation A):
  StronglySorted r l <->
  forall x y ix iy
    (X: nth_error l ix = Some x) (Y: nth_error l iy = Some y) (LT: ix < iy),
    r x y.
Proof.
  split.
  { intros SORTED. ins. 
    assert (length (firstn iy l) = iy) as LENy.
    { apply firstn_length_le. apply Nat.lt_le_incl.
      apply nth_error_Some, opt_val. eauto. }
    rewrite <- (firstn_skipn iy l) in *. rewrite firstn_skipn in LENy. 
    apply StronglySorted_app_iff in SORTED. desc.
    apply SORTED1.
    { apply nth_error_In with (n := ix).
      rewrite nth_error_app1 in X; auto. lia. }
    { apply nth_error_In with (n := 0).
      rewrite nth_error_app2 in Y; [| lia].
      rewrite LENy, Nat.sub_diag in Y. auto. }
  }
  { induction l; [done| ].
    intros REL. constructor.
    { apply IHl. ins. apply REL with (ix := S ix) (iy := S iy); auto. lia. }
    eapply Forall_index. ins. specialize (REL a x 0 (S i)). specialize_full REL; auto.
    lia. }
Qed.

Lemma sort_ninit l thread
      (ENI: (fun e => In e l) ⊆₁ E \₁ is_init)
      (THREAD: (fun e => In e l) ⊆₁ Tid_ thread)
      (NODUP: NoDup l):
  StronglySorted ext_sb (SBSort.sort l).
Proof.
  apply sorted_ordered. ins.
  assert (StronglySorted SBOrder.leb (SBSort.sort l)) as SORT'. 
  { apply SBSort.StronglySorted_sort. apply SBOrder.leb_trans. }
  destruct (classic (x = y)) as [| NEQ].
  { subst.
    forward eapply (proj1 (@NoDup_nth_error _ (SBSort.sort l))).
    { eapply Permutation_NoDup; [| eauto]. apply SBSort.Permuted_sort. }
    2: { by rewrite X, Y. }
    { apply nth_error_Some, opt_val. eauto. }
    lia. }
  forward eapply (proj1 (@sorted_ordered _ (SBSort.sort l) SBOrder.leb) SORT' x y ix iy) as REL'; eauto.
  eapply nth_error_In, Permutation_in in X; [|by apply Permutation_sym, SBSort.Permuted_sort]. 
  eapply nth_error_In, Permutation_in in Y; [|by apply Permutation_sym, SBSort.Permuted_sort]. 
  unfold SBOrder.leb in REL'. 
  destruct x, y; try done.
  { specialize (ENI (InitEvent x)). specialize_full ENI; auto. unfolder'. by desc. }
  simpl in *. apply hahn__orb_split in REL'. des.
  { pose proof (THREAD _ X). pose proof (THREAD _ Y).
    simpl in *. apply Nat.ltb_lt in REL'. lia. }
  apply NPeano.Nat.eqb_eq in REL'. split; auto.
  apply Nat.leb_le, le_lt_or_eq in REL'0. des; [done| ].
  exfalso. 
  forward eapply wf_index; eauto.
  unfolder'. splits; vauto.
  { apply ENI in X. by desc. }
  { apply ENI in Y. by desc. }
Qed.   

Lemma sorted_restr {A: Type} (l: list A) (r: relation A) S
      (SORTED: StronglySorted r l)
      (IN_S: (fun a => In a l) ⊆₁ S):
  StronglySorted (restr_rel S r) l. 
Proof.
  assert (r ≡ restr_rel S r ∪ (r \ restr_rel S r)).
  { split; try basic_solver. red. ins.
    destruct (classic (restr_rel S r x y)); basic_solver. }
  rewrite H in SORTED.
  apply sort_clarification in SORTED; auto.
  ins. red. ins. red in H0. desc.
  apply H1. red. split; auto.
Qed. 
  
  
Lemma event_block_prefix e i (CE: (cur_events (S i) \₁ cur_events i) e):
  forall e' (PREV: cur_events i e') (TID: tid e = tid e'), sb G e' e.
Proof.
  ins. destruct CE as [CUR NPREV].
  forward eapply (CE_E PREV) as ENIe'. forward eapply (CE_E CUR) as ENIe.
  destruct (Execution.same_thread WF e e'); try (by (red in ENIe; red in ENIe'; desc)).
  exfalso. red in H. des; [subst; done| ].
  apply NPREV. do 2 red. 
  do 2 red in PREV. desc. apply seq_eqv_lr in PREV. desc. 
  exists y. apply seq_eqv_lr. splits; eauto. right. 
  red in PREV0. des; [subst e'; done| by eapply sb_trans; eauto]. 
Qed.

Lemma sb_sorted_perm_eq l l' (PERM: Permutation l l')
      (SORTED: StronglySorted ext_sb l)
      (SORTED': StronglySorted ext_sb l'):
  l = l'.
Proof.
  eapply sorted_perm_eq; eauto. 
  { apply ext_sb_trans. }
  { apply strict_partial_order_antisymmetric. red.
    split; [apply ext_sb_irr | apply ext_sb_trans]. }
Qed. 

Lemma Bf_thread i
      (DOM: NOmega.lt_nat_l i (set_size (E \₁ is_init))):
  (fun e => In (inl e) (Bf i)) ⊆₁ Tid_ (tid (enum i)).
Proof. 
  rewrite Bf_ce_diff. red. ins. red in H. desc.
  do 2 red in H. desc. apply seq_eqv_lr in H. desc.
  rewrite covered_ext in H2. apply in_app_iff in H2. des.
  { exfalso. apply H0. exists y. apply seq_eqv_lr. splits; auto. }
  simpl in H2. des; [| done].
  red in H1. des; [congruence| ].
  red in H1. apply seq_eqv_lr in H1. desc.
  destruct x; [by unfolder'; desc| ]. destruct y; [done| ].
  simpl in H3. desc. by rewrite H2.
Qed. 

Lemma tp_ext i thread (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init))):
  thread_prefix (S i) thread =
  thread_prefix i thread ++ (ifP (tid (enum i) = thread)
                             then Bf_events i
                             else []).
Proof.
  pose proof (Bf_ce_disjoint i) as DISJ. 
  unfold thread_prefix.
  destruct (as_list _) as [l' L']. destruct (as_list _) as [l L].
  simpl in *. desc.
  rewrite ce_ext, set_inter_union_l in L'0. rewrite L0 in L'0.
  assert ((fun e : Event => In (inl e) (Bf i)) ⊆₁ Tid_ (tid (enum i))) as BF_THREAD.
  { rewrite Bf_contents; auto.
    rewrite set_inter_minus_l. rewrite set_minus_subset.
    red. ins. red in H. desc.
    red in H. des; [subst; done| ].
    red in H. apply seq_eqv_lr in H. desc.
    red in H1. destruct x; [by unfolder'| ].
    destruct (enum i); by desc. }
  
  assert (Permutation l (SBSort.sort l)) as PERM by apply SBSort.Permuted_sort.
  assert (Permutation l' (SBSort.sort l')) as PERM' by apply SBSort.Permuted_sort.

  assert (StronglySorted ext_sb (SBSort.sort l)) as SORT.
  { apply sort_ninit with (thread := thread); auto. 
    { rewrite <- L0, CE_E. basic_solver. }
    { rewrite <- L0. basic_solver. } }
  
  destruct (excluded_middle_informative _).
  2: { rewrite app_nil_r.
       generalize dependent L'0. 
       arewrite ((fun e : Event => In (inl e) (Bf i)) ∩₁ Tid_ thread ≡₁ ∅).
       { split; [| basic_solver]. rewrite BF_THREAD. basic_solver. }
       rewrite set_union_empty_r.
       unfold sb_sort. ins.
       apply sb_sorted_perm_eq. 
       { apply NoDup_Permutation.
         1, 2: by (eapply Permutation_NoDup; eauto). 
         ins. eapply iff_trans. 
         { symmetry. generalize x.
           apply set_equiv_exp_iff. apply sb_sort_sim. }
         symmetry. eapply iff_trans.
         { symmetry. generalize x.
           apply set_equiv_exp_iff. apply sb_sort_sim. }
         generalize x. now apply set_equiv_exp_iff. }
       { apply sort_ninit with (thread := thread); auto. 
         { rewrite <- L'0, <- L0, CE_E. basic_solver. }
         rewrite <- L'0, <- L0. basic_solver. }
       auto. }
  
  assert (StronglySorted ext_sb (sb_sort l ++ Bf_events i)) as SORTED_APP. 
  { apply StronglySorted_app.
    { auto. } 
    { unfold Bf_events, sb_sort.
      destruct (as_list _). desc. simpl in *.
      apply sort_ninit with (thread := thread); auto. 
      { rewrite <- a0, CE_E. basic_solver. }
      { rewrite <- Bf_ce_diff in a0. rewrite <- a0, BF_THREAD. basic_solver. } }
    { ins. cut (sb G x1 x2); [unfold sb; basic_solver| ].
      apply event_block_prefix with (i := i).
      { apply Bf_ce_diff. unfold Bf. by apply in_app_l, in_map. }
      { rewrite sb_sort_sim in L0. apply L0 in IN1. red in IN1. by desc. }
      { transitivity thread.
        { rewrite BF_THREAD; auto. 
          unfold Bf. by apply in_app_l, in_map. }
        { eapply Permutation_in in IN1; [| eapply Permutation_sym, SBSort.Permuted_sort; eauto].
          apply L0 in IN1. red in IN1. by desc. }
      }
    }
  }
  subst thread. 
  rewrite set_inter_absorb_r in L'0 by apply BF_THREAD.
  apply sb_sorted_perm_eq; auto.
  2: { apply sort_ninit with (thread := tid (enum i)); auto.
       { rewrite <- L'0. rewrite Bf_ce_diff.
         rewrite <- L0. do 2 rewrite CE_E at 1. basic_solver. }
       { rewrite <- L'0, <- L0, BF_THREAD. basic_solver. } }
  apply NoDup_Permutation.
  { eapply Permutation_NoDup; eauto. }
  { apply nodup_append.
    { eapply Permutation_NoDup; eauto. }
    { unfold Bf_events. destruct (as_list _). desc. simpl in *.
      eapply Permutation_NoDup; [eapply SBSort.Permuted_sort|]; eauto. }
    { red. ins. apply DISJ with (x := a). split.
      { rewrite sb_sort_sim in L0. apply L0 in IN1. red in IN1. by desc. }
      { unfold Bf. by apply in_app_l, in_map. }
    }
  }
  { intros x. rewrite in_app_iff. generalize x. apply set_equiv_exp_iff.
    fold (set_union (fun x0 => In x0 (sb_sort l)) (fun x0 => In x0 (Bf_events i))).
    rewrite <- !sb_sort_sim. 
    rewrite <- L'0. apply set_equiv_union; [basic_solver| ].
    apply Bf_events_labels. }
Qed.

Definition simulates (st: TSOMemory) (i: nat): Prop :=
  let cov := covered_events i in
  ⟪MEM: forall l,
      let l_writes := filterP (is_w ∩₁ Loc_ l) cov in
      fst st l = valw (last l_writes (InitEvent l))⟫ /\
  ⟪BUFS: forall thread,
      let cur_prefix := thread_prefix i thread in
      let contents := filterP (is_regular_write' \₁ (fun e => In e cov)) cur_prefix in
      snd st thread = map (fun e => (loc e, valw e: Val)) contents⟫.


Lemma LTS_traceE':
      forall {State Label : Type} {lts : LTS State Label} (t : trace Label),
(exists fl' : nat -> State,
  LTS_init lts (fl' 0) /\
  (forall i : nat,
   NOmega.lt_nat_l i (trace_length t) ->
   forall d : Label, LTS_step lts (fl' i) (trace_nth i t d) (fl' (S i)))) ->
LTS_trace lts t.
Proof.
  ins. desc. red.
  destruct t; [by vauto| ].
  simpl in *. exists fl'. split; intuition.
Qed.

Lemma DOM_HELPER' {A: Type} (bf: nat -> list A) block_tr_size
      (NEMPTY : forall i : nat, bf i <> []):
  forall i d n (N: n = length (flatten (block_trace_prefix bf i)) + d),
    let tr_size := match block_tr_size with
                   | NOinfinity => NOinfinity
                   | NOnum n => NOnum (length (flatten (block_trace_prefix bf n)))
                   end in
    NOmega.le (NOnum n) tr_size ->
    NOmega.le (NOnum i) block_tr_size.
Proof.
  simpl. intros i d n N DOMn.
  destruct block_tr_size as [| nblocks]; [done| ]. simpl in *.
  
  subst n.
  unfold block_trace_prefix in DOMn.
  destruct (le_lt_dec i nblocks); auto. exfalso.
  apply lt_diff in l. desc. subst i.
  rewrite seq_add, map_app, flatten_app, length_app in DOMn.
  rewrite seqS, map_app, flatten_app, length_app in DOMn.
  rewrite !Nat.add_0_l in DOMn. simpl in DOMn. rewrite app_nil_r in DOMn.
  pose proof (block_len bf NEMPTY (nblocks + d0)). lia.
Qed.

Lemma DOM_HELPER {A: Type} (bf: nat -> list A) block_tr_size:
  forall i d n (N: n = length (flatten (block_trace_prefix bf i)) + d),
    let tr_size := match block_tr_size with
                   | NOinfinity => NOinfinity
                   | NOnum n => NOnum (length (flatten (block_trace_prefix bf n)))
                   end in
    NOmega.lt_nat_l n tr_size -> 
    NOmega.lt_nat_l i block_tr_size.
Proof.
  simpl. intros i d n N DOMn. 
  destruct block_tr_size as [| nblocks]; [done| ]. simpl in *. 
  
  subst n. 
  unfold block_trace_prefix in DOMn.
  destruct (le_lt_dec nblocks i); auto.
  apply le_diff in l. desc. subst i.
  rewrite seq_add, map_app, flatten_app, length_app in DOMn.
  lia.
Qed. 


Lemma block_step_app st1 st2 lbls1 lbls2: 
  TSO_block_step st1 (lbls1 ++ lbls2) st2 <->
  exists st', TSO_block_step st1 lbls1 st' /\ TSO_block_step st' lbls2 st2.
Proof.
  split.
  {
    intros STEPS. 
    generalize dependent st1. generalize dependent st2. induction lbls1.
    { rewrite app_nil_l. ins. exists st1. split; vauto. }
    ins. inversion STEPS. subst. specialize (IHlbls1 st2 st' STEPS') as [st'' [STEP1 STEPS'']].
    exists st''. split; auto. econstructor; eauto.
  }
  generalize dependent st1. induction lbls1.
  { ins. desc. inversion H. by subst. }
  ins. desc. inversion H. subst. specialize_full IHlbls1; eauto.
  econstructor; eauto. 
Qed.

Lemma expanded_block {A: Type} (bf: nat -> list A) (NEMPTY: forall i, bf i <> []) i:
  bf i =
  map (expanded bf NEMPTY)
      (List.seq (length (flatten (block_trace_prefix bf i))) (length (bf i))).
Proof. 
  unfold expanded.
  symmetry. apply map_nth_seq with (d := (a_ bf NEMPTY)).
  ins.
  assert (i < S (length (flatten (block_trace_prefix bf i)) + i0)).
  { pose proof (index_lt_flatten' bf NEMPTY i). lia. }
  apply lt_diff in H. desc. rewrite H.
  assert (exists l', block_trace_prefix bf (i + S d) = (block_trace_prefix bf i) ++ (bf i :: l')).
  { unfold block_trace_prefix. rewrite seq_add, map_app. 
    eexists. f_equal. rewrite Nat.add_0_l, seqS_hd. vauto. }
  desc. rewrite H0, flatten_app.
  rewrite app_nth2; [| lia].
  rewrite minus_plus. simpl. rewrite app_nth1; auto.
Qed. 

Lemma prefix_as_expanded {A: Type} (bf: nat -> list A) (NEMPTY: forall i, bf i <> []) i:
  flatten (map bf (List.seq 0 i)) =
  map (expanded bf NEMPTY)
      (List.seq 0 (length (flatten (block_trace_prefix bf i)))).
Proof. 
  induction i.
  { by rewrite btp0. }
  rewrite seqS, map_app, flatten_app.
  rewrite btpS, flatten_app, length_app, seq_add, map_app.
  rewrite <- IHi. f_equal.
  rewrite !Nat.add_0_l. simpl. rewrite app_nil_r.
  apply expanded_block. 
Qed. 

Definition blocks_reach bf bst block_tr_size :=
  let lbls := fun i => flatten (block_trace_prefix bf i) in
  forall i (DOM: NOmega.le (NOnum i) block_tr_size),
    TSO_block_step TSO.Minit (lbls i) (bst i).

Definition advance_fun bf st' block_tr_size
      (NEMPTY: (forall i : nat, bf i <> []))
      (BLOCK_REACH: blocks_reach bf st' block_tr_size)
  :
  exists (st: nat -> TSOMemory), forall i,
        let tr_size := match block_tr_size with
                  | NOinfinity => NOinfinity
                  | NOnum n => NOnum (length (flatten (block_trace_prefix bf n)))
                  end in
      let lbls := map (expanded bf NEMPTY) (List.seq 0 i) in
      NOmega.le (NOnum i) tr_size -> TSO_block_step TSO.Minit lbls (st i).
Proof.
  
  remember (match block_tr_size with
                  | NOinfinity => NOinfinity
                  | NOnum n => NOnum (length (flatten (block_trace_prefix bf n)))
                  end) as tr_size. 
  simpl.
  set (PP := fun i sti => match
      match block_tr_size with
      | NOinfinity => NOinfinity | NOnum n => NOnum (length (flatten (block_trace_prefix bf n)))
      end
    with
    | NOinfinity => True | NOnum m => i <= m
    end -> TSO_block_step TSO.Minit (map (expanded bf NEMPTY) (List.seq 0 i)) (sti)). 
  forward eapply (functional_choice PP).
  2: { ins. desc. exists f. ins. apply H. subst tr_size. liaW block_tr_size. } 
  intros i.
  destruct (classic (NOmega.le (NOnum i) tr_size)).
  2: { exists TSO.Minit. red. subst tr_size. liaW block_tr_size. }
  rename i into n. 
  remember (expanded bf NEMPTY n) as fn. 
  forward eapply (expanded_src bf NEMPTY n) as [i [d [N POS]]]; eauto.  
  forward eapply DOM_HELPER' with (block_tr_size := block_tr_size) as DOMi; eauto.
  { subst tr_size. liaW block_tr_size. }
  (* forward eapply blocks_reach as BLOCK_STEPS; eauto. simpl in BLOCK_STEPS. *)
  destruct (NOmega_le_lt_or_eq _ _ DOMi). 
  { subst tr_size. destruct block_tr_size as [| nblocks]; [done| ].
    inversion H0. subst i. simpl in *.
    assert (d = 0) by lia. subst d. rewrite Nat.add_0_r in N.
    exists (st' nblocks). red. ins.
    subst n. rewrite <- prefix_as_expanded.
    red in BLOCK_REACH. by apply BLOCK_REACH. }

  red in BLOCK_REACH. 
  assert (exists st, TSO_block_step (st' i) (firstn d (bf i)) st) as [st STEPS']. 
  { forward eapply (BLOCK_REACH (S i)) as REACH'; eauto. 
    rewrite btpS, flatten_app in REACH'. simpl in REACH'. rewrite app_nil_r in REACH'.
    apply block_step_app in REACH'. desc.
    cut (st'0 = st' i); [ins; subst st'0| ]. 
    2: { eapply TSO_block_step_deterministic; eauto. }
    rewrite <- (firstn_skipn d (bf i)) in REACH'0.
    apply block_step_app in REACH'0. desc. eauto. }
    
  exists st. red. ins.

  rewrite N, seq_add, map_app. apply block_step_app. exists (st' i). split.
  { rewrite <- prefix_as_expanded. by apply BLOCK_REACH. }

  rewrite Nat.add_0_l.
  replace (List.seq (length (flatten (block_trace_prefix bf i))) d) with (firstn d (List.seq (length (flatten (block_trace_prefix bf i))) (length (bf i)))).
  { rewrite firstn_map. rewrite <- expanded_block with (NEMPTY := NEMPTY); auto. }
  assert (d < length (bf i)).
  { apply nth_error_Some, opt_val. eauto. }
  apply lt_diff in H2 as [k DIFF]. rewrite DIFF.
  rewrite seq_add. rewrite firstn_app.
  rewrite seq_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2; auto. by rewrite seq_length. 

Qed. 


Lemma fairness_blocks bf st' block_tr_size
      (NEMPTY: (forall i : nat, bf i <> []))
      (BLOCK_REACH: blocks_reach bf st' block_tr_size)
  :
    exists st : nat -> TSOMemory,
    LTS_init TSO_lts (st 0) /\
    (forall n : nat,
        let f := expanded bf NEMPTY in
        let tr_size := match block_tr_size with
                  | NOinfinity => NOinfinity
                  | NOnum n => NOnum (length (flatten (block_trace_prefix bf n)))
                  end in
        NOmega.lt (NOnum n) tr_size -> LTS_step TSO_lts (st n) (f n) (st (S n))) /\
    (forall i : nat,
        NOmega.le (NOnum i) block_tr_size ->
        st' i = st (length (flatten (block_trace_prefix bf i)))).
Proof.
  forward eapply advance_fun with (NEMPTY := NEMPTY) as [st ST_STEPS]; eauto.
  simpl in ST_STEPS. 
  exists st. splits.
  { specialize (ST_STEPS 0). specialize_full ST_STEPS; [liaW block_tr_size|]. 
    replace (List.seq 0 0) with (nil : list nat) in ST_STEPS by done.
    simpl in ST_STEPS. inversion ST_STEPS. by subst. }
  { intros n LT. 
    forward eapply (ST_STEPS n) as STEPSn; [liaW block_tr_size| ].
    forward eapply (ST_STEPS (S n)) as STEPSsn; [liaW block_tr_size| ].
    assert (exists st_n', TSO_block_step TSO.Minit (map (expanded bf NEMPTY) (List.seq 0 n)) st_n' /\ LTS_step TSO_lts (st_n') (expanded bf NEMPTY n) (st (S n))) as [st_n' [STEPS' STEP']].
    { rewrite seqS, map_app in STEPSsn. simpl in STEPSsn.
      apply block_step_app in STEPSsn. desc. exists st'0. split; auto.
      simpl. inversion STEPSsn0. subst. inversion STEPS'. by subst. }
    assert (st_n' = st n).
    { eapply TSO_block_step_deterministic; eauto. }
    subst st_n'. auto. }
  { intros i LE.
    (* forward eapply blocks_reach as STEPS'; eauto. *)
    red in BLOCK_REACH.
    specialize (BLOCK_REACH i LE).
    specialize (ST_STEPS (length (flatten (block_trace_prefix bf i)))).
    specialize_full ST_STEPS. 
    { destruct block_tr_size; [done| ]. simpl in *. by apply btp_mon. }
    rewrite <- prefix_as_expanded in ST_STEPS. 
    eapply TSO_block_step_deterministic; eauto. }
Qed.

Definition TSO_step' st1 st2 := exists lbl, TSO_step st1 lbl st2. 

Lemma enabled_preserved st1 st2 labels thread
      (STEPS: TSO_block_step st1 labels st2)
      (ENABLED1: enabled st1 thread)
      (NO_PROPS: ~ In (inr thread) labels):
  enabled st2 thread.
Proof.
  generalize dependent st1. generalize dependent st2. induction labels.
  { ins. inversion STEPS. by subst. }
  ins.
  apply not_or_and in NO_PROPS as [NOT_PROP NO_PROPS'].
  assert (forall st2 a (NOT_PROP: a <> inr thread) (STEP: TSO_step st1 a st2),
             enabled (st2) thread) as STEP_HELPER.  
  { clear dependent a. clear dependent st2. ins. 
    subst. simpl in *. 
    inversion STEP; try (by vauto).
    { red in ENABLED1. desc. inversion ENABLED1.
      subst. simpl in *. inversion H2. clear H2. subst.
      remember (upd bufs thread0 (bufs thread0 ++ [(loc, val)])) as bufs2. 
      red. 
      destruct (classic (thread0 = thread)). 
      { subst thread0. 
        exists (upd sh_mem loc0 val0, upd bufs2 thread (buf' ++ [(loc, val)])).
        constructor. subst. rewrite upds. rewrite BUF. apply app_comm_cons. }
      exists (upd sh_mem loc0 val0, upd bufs2 thread (buf')).
      constructor. subst. rewrite updo; auto. }
    { red in ENABLED1. desc. inversion ENABLED1.
      subst. simpl in *. inversion H2. clear H2. subst.
      destruct (classic (thread0 = thread)).
      { subst thread0. by rewrite NO_BUF in BUF. }
      vauto. }
    { destruct (classic (thread0 = thread)); [vauto| ].
      red in ENABLED1. desc. inversion ENABLED1.
      subst. simpl in *. inversion H3. clear H3. subst.
      remember (upd sh_mem loc val) as sh_mem2. remember (upd bufs thread0 buf') as bufs2. 
      red. exists (upd sh_mem2 loc0 val0, upd bufs2 thread buf'0).
      constructor. subst. rewrite updo; auto. }
  }

  inversion STEPS.
  subst.
  apply IHlabels with (st1 := st'); auto.
  eapply STEP_HELPER; eauto. 
Qed. 


Lemma fairness_trans bf bst block_tr_size
      (NEMPTY: (forall i : nat, bf i <> []))
      (BLOCK_REACH: blocks_reach bf bst block_tr_size)
      (BLOCK_FAIR: block_TSO_fair_fun_lim bf  block_tr_size bst):
  let lim := match block_tr_size with
             | NOinfinity => NOinfinity
             | NOnum n => NOnum (length (flatten (block_trace_prefix bf n)))
             end in
  exists st (TSO_TRACE : LTS_fun_limP TSO_lts (expanded bf NEMPTY) lim st),
    TSO_fair_fun_lim TSO_TRACE.
Proof.
  set (tr_size := match block_tr_size with
                  | NOinfinity => NOinfinity
                  | NOnum n => NOnum (length (flatten (block_trace_prefix bf n)))
                  end).
  remember (expanded bf NEMPTY) as f.
  (* red in BLOCK_REACH. *)
  cut (exists st : nat -> TSOMemory,
          LTS_init TSO_lts (st 0) /\
          (forall n, NOmega.lt_nat_l n tr_size ->
                LTS_step TSO_lts (st n) (f n) (st (S n))) /\
          (forall i, NOmega.le (NOnum i) block_tr_size ->
                bst i = st (length (flatten (block_trace_prefix bf i))))). 
  { intros [st [INIT [STEP CORR]]].
    exists st. exists (conj INIT STEP). red. ins. rename i into n.
    assert (NOmega.lt_nat_l n tr_size) as DOMn.
    { destruct block_tr_size as [| nblocks]; [done| ]. subst tr_size. simpl in *. 
      apply le_lt_or_eq in DOM_EXT. des; auto.
      exfalso. red in BLOCK_FAIR. specialize (@BLOCK_FAIR nblocks tid).
      specialize_full BLOCK_FAIR; [done| | ].
      { rewrite CORR; auto. by rewrite <- DOM_EXT. }
      desc. simpl in *. lia. }
    contra UNFAIR.

    set (nth_lbl := f n). 
    forward eapply (@expanded_src _ bf NEMPTY n nth_lbl) as [i [d [N_ID BLOCK_POS]]]; [by vauto| ].

    assert (forall i j (LT: i < j) (DOMj: NOmega.le (NOnum j) tr_size),
               TSO_block_step (st i) (map f (List.seq i (j - i))) (st j)) as ST_STEPS. 
    { clear dependent i. clear dependent d.
      intros i j LT DOM. apply lt_diff in LT as [d DIFF]. subst j. rewrite minus_plus. generalize dependent i. 
      induction d.
      { ins. replace (map f (List.seq i 1)) with [f i] by done.
        eapply TSO_block_step_next with (st' := st (i + 1)); [| apply TSO_block_step_none]. 
        replace (i + 1) with (S i) by lia. apply STEP. liaW tr_size. }
      ins. rewrite seqS_hd. simpl.
      apply TSO_block_step_next with (st' := st (S i)).
      { apply STEP. liaW tr_size. }
      replace (i + S (S d)) with (S (i + (S d))) by lia.
      apply IHd. liaW tr_size. }

    set (next_blockpos := length (flatten (block_trace_prefix bf (S i)))).
    assert (NOmega.le (NOnum (S i)) block_tr_size) as DOM'. 
    { by eapply DOM_HELPER; eauto. }
    assert (NOmega.le (NOnum next_blockpos) tr_size) as DOM''. 
    { subst tr_size next_blockpos. 
      destruct block_tr_size as [| nblocks]; [done| ]. simpl in *. by apply btp_mon. }

    assert (n < next_blockpos) as LE.
    { subst n next_blockpos. rewrite btpS, flatten_app, length_app.
      apply Nat.add_lt_mono_l. simpl. rewrite length_app.
      cut (d < length (bf i)); [ins; lia| ].
      apply nth_error_Some, opt_val; eauto. }
    assert (enabled (st next_blockpos) tid) as ENABLED_NEXT.
    { apply enabled_preserved with (st1 := st n) (labels := map f (List.seq n (next_blockpos - n))); auto.
      red. ins. apply In_nth_error in H as [k PROP].
      assert (n + k < next_blockpos) as POS.
      { forward eapply (nth_error_Some (map f (List.seq n (next_blockpos - n))) k) as [IND _]; eauto.
        specialize_full IND; [apply opt_val; eauto| ].
        rewrite length_map, seq_length in IND. lia. }
      apply UNFAIR. exists (n + k). splits; [lia| | ].
      { subst tr_size. liaW block_tr_size. }
      forward eapply (@lt_diff k (next_blockpos - n)) as [t DIFF]; [lia| ].
      rewrite DIFF in PROP. rewrite seq_add, map_app in PROP.
      rewrite nth_error_app2 in PROP; [| by rewrite map_length, seq_length].
      rewrite map_length, seq_length, Nat.sub_diag in PROP.
      rewrite seqS_hd in PROP. simpl in PROP. vauto. }
    
      
    red in BLOCK_FAIR. specialize (BLOCK_FAIR (S i) tid). specialize_full BLOCK_FAIR; auto. 
    { subst next_blockpos. rewrite CORR; auto. }
    destruct BLOCK_FAIR as (ip & AFTER & DOMip & PROP).
    apply In_nth_error in PROP as [dp PROP].

    set (np := length (flatten (block_trace_prefix bf ip)) + dp).     
    apply UNFAIR. exists np. splits.
    { subst n. subst np.
      apply le_diff in AFTER as [k AFTER]. rewrite AFTER.
      unfold block_trace_prefix. rewrite seq_add, map_app, flatten_app, length_app.
      rewrite seqS, map_app, flatten_app, length_app.
      simpl. rewrite length_app. simpl.
      cut (d < length (bf i)); [ins; lia| ].
      apply nth_error_Some. apply opt_val. eauto. }
    { subst tr_size. destruct block_tr_size as [| nblocks]; [done| ]. simpl in *.
      subst np. apply lt_diff in DOMip as [k DOMip]. rewrite DOMip.
      replace (ip + S k) with (S ip + k) by lia. 
      unfold block_trace_prefix. rewrite seq_add, map_app, flatten_app, length_app.
      rewrite seqS, map_app, flatten_app, length_app.
      simpl. rewrite length_app. simpl.
      cut (dp < length (bf ip)); [ins; lia| ].
      apply nth_error_Some. apply opt_val. eauto. }
    subst f. erewrite expanded_dst; vauto. }
  
  forward eapply (@fairness_blocks bf bst block_tr_size NEMPTY); [done| ]. 
  ins. desc.
  exists st. splits; vauto. 
Qed. 


Definition blocks_enumerator (bf: nat -> list TSO_label) :=
  forall i (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init))),
    ⟪BLOCKS: (fun e => In (inl e) (bf i)) ≡₁ cur_events (S i) \₁ cur_events i⟫ /\
    ⟪NODUP: NoDup (bf i) ⟫ /\
    ⟪NEMPTY: bf i <> [] ⟫ /\
    ⟪WFL: forall thread index1 index2 lbl1 lbl2 d1 d2
            (E1: nth_error (bf i) d1 = Some (inl (ThreadEvent thread index1 lbl1)))
            (E2: nth_error (bf i) d2 = Some (inl (ThreadEvent thread index2 lbl2)))
            (LT: d1 < d2), 
        index1 < index2 ⟫.


Lemma enum_CE e ind (DOM: NOmega.lt (NOnum ind) (set_size (E \₁ is_init)))
      (ENUMe : enum ind = e):
  cur_events (S ind) e.
Proof.
  unfold cur_events. red. exists e. apply seq_eqv_lr. splits.
  { rewrite <- ENUMe. by apply G_INSET. }
  { basic_solver. }
  unfold covered_events. rewrite seqS, map_app. simpl.
  apply in_app_r. simpl. by left.
Qed. 

Lemma in_ce e i:
  In e (covered_events i) <-> exists j, enum j = e /\ j < i.
Proof.
  split.
  { intros CE. apply In_nth_error in CE as [j COV]. exists j.
    assert (j < i) as BEFORE. 
    { replace i with (length (covered_events i)).
      2: { unfold covered_events. rewrite map_length. apply seq_length. }
      apply nth_error_Some, opt_val. eauto. }
    split; auto. 
    unfold covered_events in COV. apply lt_diff in BEFORE. desc. subst i.
    rewrite seq_add, map_app, nth_error_app2 in COV.
    2: { by rewrite map_length, seq_length. }
    rewrite map_length, seq_length, Nat.sub_diag, Nat.add_0_l, seqS_hd in COV.
    simpl in COV. by inversion COV. }
  { intros [j [ENUMe LT]].
    apply lt_diff in LT. desc. subst.
    unfold covered_events. rewrite seq_add, Nat.add_0_l, map_app.
    apply in_app_r. rewrite seqS_hd. simpl. by left. }
Qed. 

Lemma r_new r i (Rr: is_r r) (ENUMr: enum i = r) (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init))):
  ~ cur_events i r.
Proof. 
  unfold cur_events. red. ins.
  red in H. desc. apply seq_eqv_lr in H. destruct H as (ENIr & SB'ry & COVy). 
  pose proof (proj1 (in_ce y i) COVy) as [j [ENUMy BEFORE]].
  red in SB'ry. des.
  { subst y. cut (j = i); [ins; lia| ].
    apply G_INJ; [| | congruence]; liaW (set_size (E \₁ is_init)). }  
  forward eapply (@ENUM_ORDER i j); [auto|liaW (set_size (E \₁ is_init)) | | ins; lia]. 
  red. rewrite ENUMr, ENUMy.
  destruct r eqn:R; [by unfolder'| ].
  rewrite <- R. 
  destruct l; [| by unfolder'| ]; apply ct_step. 
  { cut (ppo G r y); [basic_solver 10| ].
    do 2 red. split; [congruence| ].
    subst. unfolder'. intuition. }
  cut (implied_fence G r y); [basic_solver 10| ]. red. right.
  apply seq_eqv_l. split; vauto.
Qed.

Lemma covered_cur e i (COV: In e (covered_events i))
      (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init))):
  cur_events i e.
Proof.
  do 2 red. exists e. apply seq_eqv_lr. split; auto.
  unfold covered_events in COV. apply in_map_iff in COV. desc.
  assert (x < i); [by apply in_seq0_iff in COV0| ].
  rewrite <- COV. apply G_INSET. liaW (set_size (E \₁ is_init)).
Qed.

Lemma event_block_closed e i (CE: cur_events i e):
  forall j (LE: i <= j), cur_events j e. 
Proof.
  ins. do 2 red.
  do 2 red in CE. desc. apply seq_eqv_lr in CE. desc.
  exists y. apply seq_eqv_lr. splits; auto.
  unfold covered_events in *. apply le_diff in LE as [d DIFF]. subst j.
  rewrite seq_add, map_app. by eapply in_or_app; eauto. 
Qed.

Lemma Bf_rmw i thread index l vr vw
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMrmw: enum i = ThreadEvent thread index (Armw l vr vw)):
  Bf i = [inl (ThreadEvent thread index (Armw l vr vw))].
Proof.
  remember (ThreadEvent thread index (Armw l vr vw)) as rmw.
  unfold Bf, Bf_events. rewrite emiF.
  2: { rewrite ENUMrmw. subst rmw. unfolder'. intuition. }
  rewrite app_nil_r. replace ([inl rmw]) with (map inl [rmw]: list TSO_label) by done.
  f_equal.
  destruct as_list as [lst [NODUP EQUIV]]. simpl.
  
  rewrite <- Bf_ce_diff, Bf_contents in EQUIV; [| done].

  assert ((fun x : Event => In x lst) ≡₁ eq rmw).
  { split.
    { red. ins. apply EQUIV in H. do 2 (red in H; desc).
      red in H. des; [subst; done|].
      exfalso.
      assert ((E \₁ is_init) x) as ENIx.
      { red. split; auto. red in H. apply seq_eqv_lr in H. by desc. }
      pose proof (G_IND ENIx) as [ix [DOMx ENUMx]].
      forward eapply (@ENUM_ORDER ix i); auto. 
      { red. rewrite ENUMx, ENUMrmw. apply ct_step. cut (implied_fence G x rmw); [basic_solver 10| ].
        red. left. apply seq_eqv_r. split; [congruence | vauto]. }
      ins. apply H1. exists x. apply seq_eqv_lr. splits; [| basic_solver |]. 
      { rewrite <- ENUMx. by apply G_INSET. }
      apply in_ce. eauto. }
    { red. ins. subst x. apply EQUIV. split; [| by vauto].
      split; [basic_solver| ].
      apply r_new; auto. subst. by unfolder'. }
  }
  assert (eq rmw ≡₁ (fun e => In e [rmw])) by basic_solver. rewrite H0 in H.
  forward eapply (@NoDup_Permutation _ lst [rmw]) as PERM; auto.
  { by apply set_equiv_exp_iff. }
  apply Permutation_sym in PERM. rewrite (Permutation_length_1_inv PERM). 
  apply sb_sort1_tmp. 
Qed.


Lemma covered_nodup i (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init))):
  NoDup (covered_events i).
Proof.
  induction i.
  { unfold covered_events. rewrite seq0. by simpl. }  
  rewrite covered_ext. apply nodup_append; auto.
  { apply IHi. liaW (set_size (E \₁ is_init)). }
  red. ins. des; [| done].
  apply in_ce in IN1. desc.
  cut (j = i); [lia| ].
  apply G_INJ; [| | congruence]; liaW (set_size (E \₁ is_init)).
Qed.



Lemma list_split {A: Type} l (a: A) n (NTH: nth_error l n = Some a):
  l = firstn n l ++ [a] ++ skipn (S n) l.
Proof. 
  rewrite <- (firstn_skipn (S n) l) at 1.
  erewrite <- Nat.add_1_r, firstn_end; eauto. 
  symmetry. apply app_assoc.
Qed. 

Lemma nodup_blocks {A: Type} (l1 l2: list A) x y ix iy
      (X: nth_error (l1 ++ l2) ix = Some x) (Y: nth_error (l1 ++ l2) iy = Some y)
      (IN1: In x l1) (IN2: In y l2)
      (NODUP: NoDup (l1 ++ l2)):
  ix < iy. 
Proof.
  apply nodup_app in NODUP. desc. 
  pose proof (NPeano.Nat.lt_trichotomy ix iy). des; auto.
  { exfalso. 
    subst iy. rewrite Y in X. inversion X. subst y.
    eapply NODUP1; eauto. }
  exfalso. apply lt_diff in H. desc.
  destruct (Nat.le_gt_cases (length l1) ix).
  { rewrite nth_error_app2 in X; auto.
    apply nth_error_In in X. eapply NODUP1; eauto. }
  destruct (Nat.le_gt_cases (length l1) iy).
  2: { rewrite nth_error_app1 in Y; auto.
       apply nth_error_In in Y. apply (NODUP1 y); eauto. }
  lia. 
Qed. 

Lemma covered_index i n e (NTH: nth_error (covered_events i) n = Some e):
  enum n = e.
Proof.
  assert (n < i) as LT.
  { replace i with (length (covered_events i)).
    { apply nth_error_Some, opt_val. eauto. }
    unfold covered_events. by rewrite map_length, seq_length. }
  apply lt_diff in LT. desc. subst i. 
  unfold covered_events in NTH. rewrite seq_add, map_app, nth_error_app2 in NTH.
  2: { by rewrite map_length, seq_length. }
  rewrite map_length, seq_length, Nat.sub_diag, Nat.add_0_l in NTH.
  rewrite seqS_hd in NTH. simpl in NTH. by inversion NTH.
Qed.

Lemma covered_writes_ordered i l w1 w2 p1 p2
  (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init))):
  let ws := filterP ((fun a : Event => is_w a) ∩₁ Loc_ l) (covered_events i) in
  nth_error ws p1 = Some w1 ->
  nth_error ws p2 = Some w2 ->
  p1 < p2 ->
  co G w1 w2.
Proof.
  remember (filterP ((fun a : Event => is_w a) ∩₁ Loc_ l) (covered_events i)) as ws.
  simpl. intros W1 W2 LT.

  assert (forall w i (ITH: Some w = nth_error ws i),
             (E ∩₁ (fun a0 : Event => is_w a0) ∩₁ Loc_ l) w) as W.
  { ins. symmetry in ITH. apply nth_error_In in ITH.
    subst ws. apply in_filterP_iff in ITH. desc.
    apply covered_cur, CE_E in ITH; auto.
    unfolder'. desc. splits; vauto. }
  
  forward eapply (@wf_co_total G WF l) as TOT. red in TOT.
  specialize TOT with (a := w1) (b := w2). specialize_full TOT.
  1, 2: by eapply W; eauto.
  { red. ins. subst w2.
    assert (p1 = p2); [| lia].
    eapply (NoDup_nth_error ws); [| | congruence].
    { subst ws. by apply nodup_filterP, covered_nodup. }
    apply nth_error_Some, opt_val. eauto. }
  des; [done| ]. exfalso.
  
  pose proof (list_split ws p1 W1) as SPLIT. rewrite app_assoc in SPLIT. 
  symmetry in Heqws. rewrite SPLIT in Heqws. apply filterP_eq_app in Heqws. desc.
  
  assert (In w1 l1') as IN1.
  { rewrite SPLIT, nth_error_app1 in W1.
    2: { rewrite length_app, firstn_length_le; [simpl; lia| ].
         apply Nat.lt_le_incl. apply nth_error_Some, opt_val.
         rewrite <- SPLIT in W1. eauto. }
    rewrite <- Heqws0 in W1.
    apply nth_error_In, in_filterP_iff in W1. by desc. }
  assert (In w2 l2') as IN2.
  { rewrite SPLIT, nth_error_app2 in W2.
    2: { rewrite length_app, firstn_length_le; [simpl; lia| ].
         apply Nat.lt_le_incl. apply nth_error_Some, opt_val.
         rewrite <- SPLIT in W2. eauto. }
    rewrite <- Heqws1 in W2.
    apply nth_error_In, in_filterP_iff in W2. by desc. }
  assert (exists j1, nth_error (covered_events i) j1 = Some w1) as [j1 J1].
  { apply In_nth_error. rewrite Heqws. by apply in_app_l. } 
  assert (exists j2, nth_error (covered_events i) j2 = Some w2) as [j2 J2].
  { apply In_nth_error. rewrite Heqws. by apply in_app_r. }

  forward eapply (@nodup_blocks _ l1' l2') as LT12; eauto.
  1, 2: by (rewrite Heqws in *; eauto).
  { rewrite <- Heqws. by apply covered_nodup. }

  assert (j2 < i) as LTi.
  { replace i with (length (covered_events i)).
    { apply nth_error_Some, opt_val. eauto. }
    unfold covered_events. by rewrite length_map, length_seq. } 
  forward eapply (@ENUM_ORDER j2 j1); auto.
  1, 2: liaW (set_size (E \₁ is_init)). 
  2: { lia. }
  erewrite !covered_index; eauto.
  red. apply ct_step.  basic_solver. 
Qed. 

Lemma BEFORE_W i (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMw: is_w (enum i)):
  forall w' (WL: In w' (filterP ((fun a : Event => is_w a) ∩₁ Loc_ (loc (enum i)))
                           (covered_events i))),
    co G w' (enum i).
Proof. 
  ins.
  remember (enum i) as w. 
  pose proof (@wf_co_total G WF (loc w)) as TOT. red in TOT.
  specialize TOT with (a := w') (b := w). specialize_full TOT.
  { apply in_filterP_iff in WL. desc.
    apply covered_cur, CE_E in WL; auto.
    red in WL, WL0. by desc. }
  { pose proof (G_INSET i DOM) as ENIe.
    red in ENIe. desc. unfold set_inter. splits; congruence. }
  { apply in_filterP_iff in WL. desc.
    apply in_ce in WL as [j [ENUMw' LT]].
    red. ins. subst w'. cut (j = i); [ins; lia| ].
    apply G_INJ; [| | congruence]; liaW (set_size (E \₁ is_init)). }
  des; auto. exfalso.
  apply in_filterP_iff in WL. desc. unfold covered_events in WL.
  apply in_map_iff in WL as [pw' POS]. desc.
  forward eapply (@ENUM_ORDER i pw') as LT; auto.
  { apply in_seq0_iff in POS0. liaW (set_size (E \₁ is_init)). } 
  { red. rewrite <- Heqw, POS. apply ct_step. basic_solver. }
  apply in_seq0_iff in POS0. lia.
Qed.

Lemma prev_covered i e (HB: TSO_hb G e (enum i)) (NIe: ~ is_init e)
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init))):
  In e (covered_events i).
Proof.
  apply in_ce.
  forward eapply (@G_IND e) as [ind IND]. 
  { red in HB. eapply inclusion_t_ind in HB; [| apply TSO_hb_G| basic_solver]. 
    red in HB. desc. red in HB0. desc. 
    red. split; auto. }
  desc. exists ind. split; auto.
  apply ENUM_ORDER; auto. congruence.
Qed.

Lemma fr_covered_conflict i w w'
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (RFwr: rf G w (enum i))
      (COww': co G w w')
      (COVw': In w' (covered_events i)):
  False.
Proof.
  apply in_ce in COVw' as [iw' [ENUMw' LT]].
  cut (i < iw'); [lia| ].
  apply ENUM_ORDER; auto.
  { liaW (set_size (E \₁ is_init)). }
  rewrite ENUMw'.
  red. apply ct_step. cut (fr G (enum i) w'); [basic_solver 10| ]. red. split.
  2: { unfold eqv_rel. red. ins. desc. subst w'.
       forward eapply (@G_INJ i iw'); auto. 
       { liaW (set_size (E \₁ is_init)). }
       lia. }
  red. eexists. split; eauto.
Qed. 

  
Lemma empty_buf_init_read i l
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (RFwr: rf G (InitEvent l) (enum i)):
  last (filterP ((fun a : Event => is_w a) ∩₁ Loc_ l) (covered_events i))
       (InitEvent l) = InitEvent l.
Proof.
  remember (enum i) as r.
  destruct (filterP ((fun a : Event => is_w a) ∩₁ Loc_ l) (covered_events i)) as [| w' ws'] eqn:COV_WS.
  { simpl. apply (wf_rfl WF) in RFwr. red in RFwr.
    subst. unfold loc, loc_l in RFwr. simpl in RFwr. auto. }
  exfalso.
  assert (In w' (filterP ((fun a : Event => is_w a) ∩₁ Loc_ l) (covered_events i))); [by rewrite COV_WS| ].
  apply in_filterP_iff in H as [COVw' WLw'].
  eapply fr_covered_conflict; eauto.
  { rewrite <- Heqr. eauto. }
  apply co_init_l; vauto.
  { unfolder'. by desc. }
  { eapply CE_E, covered_cur; eauto. }
  { unfolder'. by desc. }
Qed. 

Lemma empty_buf_read i w
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (RFwr : rf G w (enum i))
      (NO_BUFS: filterP (is_regular_write' ∩₁ Loc_ (loc w) \₁ (fun e => In e (covered_events (S i)))) (thread_prefix (S i) (tid (enum i))) = []):
      
  last (filterP ((fun a : Event => is_w a) ∩₁ Loc_ (loc w)) (covered_events i))
       (InitEvent (loc w)) = w.
Proof.
  remember (loc w) as l. remember (enum i) as r.
  unfold loc, loc_l in Heql. 
  destruct w eqn:W.
  { simpl in Heql. subst x. apply empty_buf_init_read; vauto. }

  simpl in Heql. 
  assert (In w (filterP ((fun a : Event => is_w a) ∩₁ Loc_ l) (covered_events i))) as IN_WS.
  { apply in_filterP_iff. split.
    2: { split.
         { apply (wf_rfD WF), seq_eqv_lr in RFwr. desc. congruence. }
         { apply (wf_rfl WF) in RFwr. red in RFwr. by subst. }
    }
    contra NCOV. 
    forward eapply (@prev_covered i w); auto.
    2: { subst w. by unfolder'. }
    rewrite <- Heqr. red. apply ct_step.  
    apply rfi_union_rfe in RFwr. red in RFwr. des; [| basic_solver].
    assert (sb G w r) as SBwr.
    { red in RFwr. red in RFwr. desc. congruence. }
    destruct l0.
    { subst w x. apply  (wf_rfiD WF) in RFwr. apply seq_eqv_lr in RFwr. by desc. }
    { exfalso. subst x.
      eapply (proj1 (@filterP_eq_nil _ (is_regular_write' ∩₁ Loc_ l \₁
               (fun e : Event => In e (covered_events (S i)))) (thread_prefix (S i) (tid r)))) with (x := w) in NO_BUFS; eauto.
      { apply thread_prefix_properties. split.
        2: { destruct (sb_tid_init SBwr); auto. by subst w. }
        exists (enum i). apply seq_eqv_lr. splits; vauto.
        { red. split; [| done].
          apply (wf_rfiE WF) in RFwr. apply seq_eqv_lr in RFwr. by desc. }
        { rewrite covered_ext. by apply in_app_r. }
      }
      split.
      { subst w. unfolder'. intuition. }
      rewrite covered_ext. rewrite in_app_iff. apply and_not_or. split; auto.
      simpl. apply and_not_or. split; auto.
      red. ins. subst w.
      do 2 red in RFwr. desc. eapply rf_irr with (x := r); eauto.
      2: congruence.
      generalize TSO_CONS. unfold TSO_consistent. tauto. } 
    { cut (implied_fence G w r); [ins; basic_solver 10| ].
      red. right. apply seq_eqv_l. split; subst; done. }
  }
  
  remember (filterP ((fun a : Event => is_w a) ∩₁ Loc_ l) (covered_events i)) as ws.
  assert (exists w', nth_error ws (length ws - 1) = Some w') as [w' LAST].
  { apply opt_val, nth_error_Some. destruct ws; [done| simpl; lia]. }
  apply In_nth_error in IN_WS as [pw POS].
  apply last_pos; [by subst| ].
  pose proof (NPeano.Nat.lt_trichotomy pw (length ws - 1)). des; [| congruence| ].
  2: { rewrite (proj2 (@nth_error_None _ ws pw)) in POS; [done| lia]. }
  exfalso. eapply fr_covered_conflict; eauto.
  { rewrite <- Heqr. eauto. }
  { eapply covered_writes_ordered; eauto; vauto. }
  { apply nth_error_In in LAST. subst ws. apply in_filterP_iff in LAST. by desc. }
Qed.

Lemma FILTER_HELPER i (NONREGW: ~ is_regular_write' (enum i)):
  (is_regular_write' \₁ (fun e : Event => In e (covered_events (S i)))) ≡₁ (is_regular_write' \₁ (fun e : Event => In e (covered_events i))). 
Proof. 
  apply set_equiv_exp_iff. intros x. 
  unfold set_minus. rewrite covered_ext, in_app_iff. simpl. 
  split; [tauto| ]. 
  ins. desc. split; [auto| ].
  apply and_not_or. split; auto. apply and_not_or. split; auto.
  red. ins. vauto.
Qed.

Lemma filterP_split {A: Type} (S T: A -> Prop) l:
  filterP (S ∩₁ T) l = filterP S (filterP T l).
Proof.
  induction l; [done| ].
  simpl. symmetry. destruct (classic (T a)).
  { rewrite emiT; auto. destruct (classic (S a)).
    { rewrite !emiT; [| basic_solver]. simpl.
      rewrite emiT; auto. congruence. }
    { rewrite !emiF.
      2: { unfolder. intuition. }
      simpl. rewrite emiF; auto. }
  }
  { rewrite !emiF; auto. unfolder. intuition. }
Qed.


Lemma filter_map:
  forall (A : Type) (d : A -> bool) (B : Type) (f : B -> A) (l : list B),
    filter d (map f l) = map f (filter (fun b => d (f b)) l).
Proof.
  ins. induction l; [done| ].
  simpl. destruct (d (f a)); simpl; congruence. 
Qed.

Lemma filterP_all (A: Type) (S: A -> Prop) l (ALL: Forall S l):
  filterP S l = l.
Proof.
  induction l; [done| ].
  apply Forall_cons in ALL. desc. 
  simpl. rewrite emiT; [| done].
  f_equal. by apply IHl.
Qed. 

Lemma filterP_nil (A: Type) (S: A -> Prop) l:
  l = [] -> filterP S l = []. 
Proof. ins. by subst. Qed. 

Lemma rmw_step sh_mem bufs i thread index l vr vw
      (SIM : simulates (sh_mem, bufs) i)
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMrmw: enum i = ThreadEvent thread index (Armw l vr vw)):
  TSO_step (sh_mem, bufs)
           (inl (ThreadEvent thread index (Armw l vr vw)))
           (upd sh_mem l vw, bufs).
Proof.
  remember (ThreadEvent thread index (Armw l vr vw)) as rmw.
  pose proof (G_INSET i DOM) as ENIe.
  red in SIM. desc.
  specialize (BUFS thread). simpl in BUFS.
  rewrite Heqrmw.
  assert (bufs thread = []) as NO_BUFS.
  { rewrite BUFS. apply map_eq_nil. apply filterP_eq_nil.
    intros w PREFw [REGWw NCOVw].
    assert ((E \₁ is_init) w) as ENIw.
    { apply thread_prefix_properties in PREFw as [CEw TIDw]. 
      do 2 red in CEw. desc. apply seq_eqv_lr in CEw. by desc. }
    apply NCOVw. clear NCOVw.
    forward eapply (G_IND ENIw) as [iw [DOMw ENUMw]].    
    forward eapply (@ENUM_ORDER iw i) as SBw_rmw; auto. 
    2: { unfold covered_events. apply lt_diff in SBw_rmw. desc. subst.
         rewrite seq_add, map_app. apply in_app_r.
         rewrite Nat.add_0_l, seqS_hd. simpl. auto. }
    red. apply ct_step. cut (implied_fence G (enum iw) (enum i)); [ins; basic_solver 10| ].
    red. left. apply seq_eqv_r. split; [| by rewrite ENUMrmw, Heqrmw].
    rewrite ENUMrmw, ENUMw.
    apply event_block_prefix with (i := i); auto.
    2: { by apply thread_prefix_properties in PREFw as [H _]. }
    2: { apply thread_prefix_properties in PREFw as [CEw TIDw].
         subst rmw. forward eapply (reg_write_structure (inl w)); done. }
    red. split.
    { by apply enum_CE. }
    eapply r_new; eauto. subst. by unfolder'. }
  constructor; auto.
  
  rewrite MEM.
  assert (exists w, rf G w rmw) as [w RFw_rmw].
  { red in RF_COMPL. forward eapply (@RF_COMPL rmw); eauto. 
    split; [red in ENIe; desc; congruence| by subst rmw]. }
  replace vr with (valr rmw) by vauto. rewrite <- (wf_rfv WF _ _ RFw_rmw).
  f_equal.
  
  replace l with (loc w).
  2: { apply (wf_rfl WF) in RFw_rmw. red in RFw_rmw. vauto. }
  apply empty_buf_read; auto.
  { congruence. }
  rewrite NO_BUFS in BUFS. symmetry in BUFS. apply List.map_eq_nil in BUFS.
  rewrite tp_ext; auto. rewrite emiT; [| done]. rewrite filterP_app.
  apply app_eq_nil. split.
  2: { apply filterP_eq_nil. ins.
       apply Bf_events_labels in IN. erewrite Bf_rmw in IN; eauto.
       2: { vauto. }
       simpl in IN. des; [| done]. inversion IN. subst x.
       unfolder'. intuition. }

  erewrite filterP_ext.
  2: { ins. generalize x. apply set_equiv_exp_iff.
       rewrite <- set_inter_minus_l, set_interC. apply set_equiv_refl2. }
  rewrite filterP_split, filterP_nil; [done| ].

  rewrite <- BUFS. replace (tid (enum i)) with thread.
  2: { by rewrite ENUMrmw, Heqrmw. }
  apply filterP_ext. ins. generalize x. apply set_equiv_exp_iff. 
  apply FILTER_HELPER. rewrite ENUMrmw, Heqrmw. unfolder'. intuition. 
Qed.
  
Lemma rmw_simulation_preserved sh_mem bufs i thread index l vr vw
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (SIM : simulates (sh_mem, bufs) i)
      (Heqei : enum i = ThreadEvent thread index (Armw l vr vw)):
  simulates (upd sh_mem l vw, bufs) (S i). 
Proof.  
  remember (ThreadEvent thread index (Armw l vr vw)) as rmw.
  assert (Bf i = [inl rmw]) as BLOCK. 
  { subst rmw. by apply Bf_rmw. }  
  red. splits. 
  { ins. destruct (classic (l = l0)).
    2: { rewrite updo; auto.
         red in SIM. desc. rewrite MEM.
         f_equal. rewrite covered_ext, filterP_app. simpl.
         rewrite emiF; [by rewrite app_nil_r| ].
         rewrite Heqei, Heqrmw. unfolder'. intuition. }
    subst l0. rewrite upds. rewrite covered_ext, filterP_app.
    simpl. erewrite emiT; [| by rewrite Heqei, Heqrmw]. 
    rewrite last_app. simpl. by rewrite Heqei, Heqrmw. }
  { ins. red in SIM. desc.
    rewrite BUFS.
    f_equal.
    rewrite tp_ext, filterP_app; auto.
    rewrite filterP_ext with (f' := (is_regular_write' \₁ (fun e : Event => In e (covered_events (S i))))).
    2: { ins. symmetry. apply set_equiv_exp_iff, FILTER_HELPER.
         rewrite Heqei, Heqrmw. unfolder'. intuition. }
    rewrite <- app_nil_r at 1. f_equal.
    destruct (excluded_middle_informative _); [| done]. 
    unfold Bf in BLOCK. rewrite emiF in BLOCK.
    2: { rewrite Heqei, Heqrmw. unfolder'. intuition. }
    rewrite app_nil_r in BLOCK. 
    replace [inl rmw] with (map inl [rmw]: list TSO_label) in BLOCK by done.
    apply inj_map in BLOCK.
    2: { red. ins. by inversion H. }
    rewrite BLOCK. simpl. rewrite emiF; [done| ].
    subst rmw. unfolder'. intuition. }
Qed.
  

Lemma Bf_w i thread index l v
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMw: enum i = ThreadEvent thread index (Astore l v)):
  Bf i = (ifP (cur_events i (ThreadEvent thread index (Astore l v)))
          then []
          else [inl (ThreadEvent thread index (Astore l v))]
         ) ++ [inr thread]. 
Proof.
  remember (ThreadEvent thread index (Astore l v)) as w. 
  unfold Bf.
  rewrite emiT; [| by rewrite ENUMw, Heqw; unfolder'; intuition].
  f_equal; [| by rewrite ENUMw, Heqw].
  replace (ifP cur_events i w then [] else [inl w])
    with
      (map inl (ifP cur_events i w then [] else [w]): list TSO_label);
    [| by destruct (excluded_middle_informative _)].
  f_equal.
  unfold Bf_events. destruct (as_list _) as [block [NODUP DIFF]]. simpl in *.

  rewrite <- Bf_ce_diff, Bf_contents in DIFF; [| done].

  assert ((fun x => In x block) ≡₁ (fun x => In x (ifP cur_events i w then [] else [w]))).
  { split.
    { red. ins. apply DIFF in H. do 2 (red in H; desc).
      red in H. des.
      { subst x. rewrite emiF; [| congruence]. by vauto. }
      exfalso.
      assert ((E \₁ is_init) x) as ENIx.
      { red. split; auto. red in H. apply seq_eqv_lr in H. by desc. }
      pose proof (G_IND ENIx) as [ix [DOMx ENUMx]].
      forward eapply (@ENUM_ORDER ix i); auto.
      { red. rewrite ENUMx, ENUMw. apply ct_step. 
        cut (ppo G x w); [basic_solver 10| ].
        red.
        red. split; [congruence| ]. 
        subst x w. unfold cross_rel. unfolder'. intuition. }
      ins. apply H1. exists x. apply seq_eqv_lr. splits; [| basic_solver |]. 
      { rewrite <- ENUMx. by apply G_INSET. }
      apply in_ce. eauto. }
    { red. ins.
      destruct (excluded_middle_informative _); [done| ].
      simpl in H. des; [| done]. 
      subst x. apply DIFF. split; [| by vauto].
      split; [basic_solver| done]. }
  }

  destruct (excluded_middle_informative _).
  { replace block with (nil: list Event); [done| ].
    destruct block; [done| ]. exfalso. by apply (proj1 H e). }
  forward eapply (@NoDup_Permutation _ block [w]) as PERM; auto.
  { by apply set_equiv_exp_iff. }
  apply Permutation_sym in PERM. rewrite (Permutation_length_1_inv PERM). 
  apply sb_sort1_tmp. 
Qed.
  
Definition opt_buf_ext i thread index l v :=
  ifP (cur_events i (ThreadEvent thread index (Astore l v)))
then [] else [(l, v)].

Lemma enum_new_w bufs i thread index l v
      (BUFS : bufs thread =
         map (fun e => (loc e, valw e))
           (filterP
              (is_regular_write' \₁ (fun e : Event => In e (covered_events i)))
              (thread_prefix i thread)))
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMw : enum i = ThreadEvent thread index (Astore l v))
      (n : ~ cur_events i (ThreadEvent thread index (Astore l v))):
  bufs thread = [].
Proof.
  remember (ThreadEvent thread index (Astore l v)) as w. 
  destruct (bufs thread) as [| p b]; [done| ]. exfalso.
  assert (In p (p :: b)) as INBUF by done.
  rewrite BUFS in INBUF.
  apply in_map_iff in INBUF as [w' [LVw' INBUF]].
  apply in_filterP_iff in INBUF as [INBUF W'].
  assert (cur_events i w') as CEw'.
  { apply thread_prefix_properties in INBUF. red in INBUF. by desc. }
  assert (tid w' = tid w) as TID.
  { apply thread_prefix_properties in INBUF. red in INBUF. desc. vauto. }
  forward eapply (@event_block_prefix w i) with (e' := w') as SBw'w; auto.
  { red. split; [| congruence]. by apply enum_CE. }    
  forward eapply (@prev_covered i w') as COVw'; auto.
  { red. rewrite ENUMw. apply ct_step. cut (ppo G w' w); [basic_solver 10| ].
    do 2 red. split; auto. generalize W'. unfolder'.
    destruct w'; intuition; vauto. }
  { unfolder'. intuition. }
  red in W'. by desc.
Qed. 

Lemma tp_nodup i thread: NoDup (thread_prefix i thread).
Proof.
  unfold thread_prefix. eapply NoDup_StronglySorted; [apply ext_sb_irr| ].
  unfold sb_sort. destruct (as_list _). desc. simpl. 
  apply sort_ninit with (thread := thread); auto. 
  { rewrite <- a0, CE_E. basic_solver. }
  { rewrite <- a0. basic_solver. } 
Qed. 

Lemma enum_old_w
      i thread index l v
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMw : enum i = ThreadEvent thread index (Astore l v))
      (c : cur_events i (ThreadEvent thread index (Astore l v))):
  filterP (is_regular_write' \₁ (fun e : Event => In e (covered_events i)))
          (thread_prefix i thread) =
  enum i :: filterP (is_regular_write' \₁ (fun e : Event => In e (covered_events (S i))))
       (thread_prefix i thread).
Proof.
  remember (ThreadEvent thread index (Astore l v)) as w.

  remember (filterP (is_regular_write' \₁ (fun e => In e (covered_events i)))
                    (thread_prefix i thread)) as buf.
  assert (In w buf) as INw.
  { subst buf. apply in_filterP_iff. split.
    { apply thread_prefix_properties. split; vauto. }
    split.
    { subst w. unfolder'. intuition. }
    red. ins. apply in_ce in H as [i' [ENUM'w LT]].
    
    forward eapply (@G_INJ i i'); vauto; [liaW (set_size (E \₁ is_init))| congruence | lia]. }
  apply In_nth_error in INw as [k POSw].

  assert (exists buf' buf'', buf = buf' ++ [w] ++ buf'') as BUF_STRUCT.
  { rewrite (@list_split _ buf w k); eauto. }
  desc.
  forward eapply filterP_eq_middle as (Fw & evs1 & evs2 & EVS_STRUCT & BUF' & BUF'').
  { rewrite Heqbuf in BUF_STRUCT. eauto. }
  rewrite EVS_STRUCT, filterP_app.
  rewrite BUF_STRUCT.

  assert (buf' = []) as NO_BUFS'.
  { destruct buf' as [| w' buf_]; [done| ].
    assert (Some w' = nth_error (w' :: buf_) 0) as POSw'.
    { destruct buf_; [done| ]. simpl. eauto. }
    assert (0 < k) as POSk.
    { eapply nodup_blocks with (l1 := w' :: buf_) (l2 := [w] ++ buf''); eauto. 
      { rewrite <- BUF_STRUCT. eauto. }
      1, 2: by vauto.
      rewrite <- BUF_STRUCT, Heqbuf. apply nodup_filterP, tp_nodup. }
    symmetry in POSw'.
    pose proof (nth_error_In _ _ POSw') as INw'. rewrite BUF' in INw'.
    apply in_filterP_iff in INw'. desc.
    forward eapply (@prev_covered i w') as COVw'; auto.
    { rewrite ENUMw. apply ct_step. cut (ppo G w' w); [unfold TSO_hb; basic_solver 10| ].
      unfold ppo. red. split.
      2: { unfolder'. subst w. intuition. }
      eapply sorted_ordered with (l := buf); eauto.
      2: { by rewrite BUF_STRUCT. } 
      rewrite Heqbuf. apply StronglySorted_filterP.
      unfold thread_prefix. unfold sb.
      destruct (as_list _). desc. simpl in *.
      rewrite <- restr_relE. apply sorted_restr. 
      { apply sort_ninit with (thread := thread); auto. 
        { rewrite <- a0, CE_E. basic_solver. }
        { rewrite <- a0. basic_solver. } }
      { arewrite ((fun a1 => In a1 (sb_sort x)) ≡₁ (fun a1 => In a1 x)).
        2: { rewrite <- a0, CE_E. basic_solver. }
        apply set_equiv_exp_iff. unfold sb_sort.
        ins; split; eapply Permutation_in; [eapply Permutation_sym|]; apply SBSort.Permuted_sort. }
    }
    { unfolder'. intuition. }
    red in INw'0. by desc. }

  assert (forall m (NEQ: m <> length evs1) (MTH: Some w = nth_error (thread_prefix i thread) m), False) as NO_W.
  { ins.
    assert (Some w = nth_error (thread_prefix i thread) (length evs1)) as POS2.
    { rewrite EVS_STRUCT. rewrite nth_error_app2; [| lia]. by rewrite Nat.sub_diag. }
    forward eapply NoDup_nth_error as [INJ _].
    specialize (INJ (tp_nodup i thread) m (length evs1)). specialize_full INJ.
    { apply nth_error_Some, opt_val. eauto. }
    { congruence. }
    lia. }
   
  replace (filterP _ evs1) with ([]: list Event).
  2: { rewrite filterP_ext with (f' := is_regular_write' \₁ (fun e => In e (covered_events i))).
       { congruence. }
       ins. unfold set_minus. apply and_iff_compat_l, not_iff_compat.
       rewrite covered_ext. etransitivity; [eapply in_app_iff| ].
       split; [| tauto]. ins. des; [done| | done].
       rewrite ENUMw in H. subst x.
       exfalso.

       apply In_nth_error in IN. desc.
       assert (n < length evs1) as LT.
       { apply nth_error_Some, opt_val. eauto. }
       apply NO_W with (m := n); [lia| ]. 
       rewrite EVS_STRUCT. rewrite nth_error_app1; auto. }
  rewrite !NO_BUFS', !app_nil_l.
  simpl app. f_equal; [congruence| ].
  rewrite BUF''.
  simpl. rewrite emiF.
  2: { red. ins. red in H. desc. apply H0. rewrite covered_ext.
       apply in_app_iff. right. by rewrite ENUMw. }
  apply filterP_ext. ins. unfold set_minus. apply and_iff_compat_l, not_iff_compat.
  symmetry. rewrite covered_ext. etransitivity; [eapply in_app_iff |].
  split; [| tauto]. ins. des; [done| | done].

  apply In_nth_error in IN. desc.
  exfalso. apply NO_W with (m := length evs1 + 1 + n); [lia| ].
  rewrite EVS_STRUCT.
  rewrite <- Nat.add_assoc, nth_error_app2; [| lia]. rewrite minus_plus.
  rewrite Nat.add_1_l. simpl. congruence. 
Qed.


Lemma w_step sh_mem bufs i thread index l v
      (SIM : simulates (sh_mem, bufs) i)
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMw: enum i = ThreadEvent thread index (Astore l v)):
  let bufs_pre := upd bufs thread (bufs thread ++ opt_buf_ext i thread index l v) in
  TSO_block_step (sh_mem, bufs)
    ((ifP cur_events i (ThreadEvent thread index (Astore l v)) then []
      else [inl (ThreadEvent thread index (Astore l v))]) ++ [
     inr thread])
    (upd sh_mem l v, upd bufs_pre thread (tl (bufs_pre thread))). 
Proof.
  remember (upd bufs thread (bufs thread ++ opt_buf_ext i thread index l v)) as bufs_pre.
  unfold opt_buf_ext in Heqbufs_pre. 
  remember (ThreadEvent thread index (Astore l v)) as w. 
  remember (ifP cur_events i w then [] else [inl w]) as block.
  simpl.

  apply block_step_app.
  exists (sh_mem, bufs_pre).
  
  assert (exists buf', bufs_pre thread = (l, v) :: buf') as [buf' BUF'].
  { red in SIM. desc. specialize (BUFS thread). simpl in BUFS.
    destruct (excluded_middle_informative ).
    { subst block. rewrite app_nil_r, updI in Heqbufs_pre. subst bufs_pre.
      erewrite enum_old_w in BUFS; eauto; [| subst w; by eauto|congruence].
      rewrite BUFS. simpl. rewrite ENUMw, Heqw. unfolder'. eauto. }
    exists nil. rewrite Heqbufs_pre.
    forward eapply enum_new_w as NO_BUF; eauto; [subst w; by eauto|congruence| ].
    rewrite NO_BUF, app_nil_l, upds. auto. }
  split.
  2: { rewrite BUF'. simpl.
       eapply TSO_block_step_next; [| econstructor]. by constructor. }
  unfold opt_buf_ext in Heqbufs_pre.
  destruct (excluded_middle_informative ).
  { subst. rewrite app_nil_r. rewrite updI. econstructor. }
  rewrite Heqblock, Heqbufs_pre.
  eapply TSO_block_step_next; [| econstructor].
  subst w. by constructor. 
Qed.

Lemma tl_map {A B: Type} (f: A -> B) l:
  tl (map f l) = map f (tl l).
Proof. destruct l; done. Qed. 
  
Lemma w_simulation_preserved sh_mem bufs i thread index l v
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (SIM : simulates (sh_mem, bufs) i)
      (Heqei : enum i = ThreadEvent thread index (Astore l v)):
  let bufs_pre := upd bufs thread (bufs thread ++ opt_buf_ext i thread index l v) in
  simulates (upd sh_mem l v, upd bufs_pre thread (tl (bufs_pre thread))) (S i). 
Proof.
  remember (upd bufs thread (bufs thread ++ opt_buf_ext i thread index l v)) as bufs_pre.
  unfold opt_buf_ext in Heqbufs_pre. 
  remember (ThreadEvent thread index (Astore l v)) as w. 
  simpl. red in SIM. desc. red. splits.
  { ins. destruct (classic (l0 = l)).
    2: { rewrite updo; auto. rewrite MEM.
         f_equal. rewrite covered_ext, filterP_app. simpl.
         rewrite emiF; [by rewrite app_nil_r| ].
         rewrite Heqei, Heqw. unfolder'. intuition. }
    subst l0. rewrite upds. rewrite covered_ext, filterP_app.
    simpl. erewrite emiT; [| by rewrite Heqei, Heqw]. 
    rewrite last_app. simpl. by rewrite Heqei, Heqw. }
  { ins.
    rewrite tp_ext; auto.
    replace (tid (enum i)) with thread; [|by rewrite Heqei, Heqw].
    replace (Bf_events i) with (ifP cur_events i w then [] else [w]).
    2: { forward eapply Bf_w as BF; eauto.
         { subst w. eauto. }
         rewrite <- Heqw in BF. 
         unfold Bf in BF. rewrite emiT in BF; [| rewrite Heqei, Heqw; unfolder'; intuition].
         replace (tid (enum i)) with thread in BF; [|by rewrite Heqei, Heqw].
         apply app_inv_tail in BF.
         replace (ifP cur_events i w then [] else [inl w]) with
             (map inl (ifP cur_events i w then [] else [w]): list TSO_label) in BF; [| destruct (excluded_middle_informative _); done].
         eapply inj_map; eauto. red. ins. by inversion H. }
    rewrite filterP_app.
    destruct (classic (thread0 = thread)).
    2: { rewrite emiF; auto. simpl. rewrite app_nil_r.
         rewrite updo; auto. subst bufs_pre. rewrite updo; auto.
         rewrite filterP_ext with (f' := (is_regular_write' \₁ (fun e => In e (covered_events i)))); auto. 
         ins. unfold set_minus. apply and_iff_compat_l, not_iff_compat.
         rewrite covered_ext, in_app_iff.
         split; [| tauto]. ins. des; vauto.
         apply thread_prefix_properties in IN.
         rewrite Heqei in IN. red in IN. desc. simpl in IN0. vauto. }
    subst thread0. rewrite emiT; auto.
    rewrite upds. subst bufs_pre. rewrite upds. 
    replace (ifP cur_events i w then [] else [(l, v)]) with
        (map (fun e => (loc e, valw e)) (ifP cur_events i w then [] else [w])).
    2: { destruct (excluded_middle_informative _); [done| ].
         subst w. by unfolder'. }
    destruct (excluded_middle_informative _).
    2: { rewrite filterP_ext with (f' := (is_regular_write' \₁ (fun e => In e (covered_events i)))); auto.
         2: { ins. unfold set_minus. apply and_iff_compat_l, not_iff_compat.
              rewrite covered_ext, in_app_iff.
              split; [| tauto]. ins. des; vauto.
              apply thread_prefix_properties in IN. red in IN. desc. congruence. }
         rewrite map_app, <- BUFS. 
         forward eapply enum_new_w as NO_BUF; eauto; [subst w; by eauto|congruence| ].
         rewrite NO_BUF, !app_nil_l. simpl.
         rewrite emiF; [done| ].
         red. ins. red in H. desc. apply H0.
         rewrite covered_ext, Heqei. by apply in_app_r. } 
    { simpl. rewrite !app_nil_r.
      rewrite BUFS.
      erewrite enum_old_w; eauto;[subst w; by eauto|congruence]. }
  }
Qed.

Definition extra_events i :=
  (fun e => (sb G \ (sb G ⨾ ⦗is_r⦘ ⨾ sb G)) e (enum i))
    \₁ ((fun e => In e (covered_events i)) ∪₁ is_init).

Lemma ew_finite i: set_finite (extra_events i).
Proof.
  unfold extra_events.
  rewrite set_minus_union_r, set_interC. apply finite_inter.
  red. exists (thread_prefix (S i) (tid (enum i))).
  ins. unfold thread_prefix. destruct (as_list _). desc. simpl in *.
  eapply Permutation_in.
  { eapply sb_sort_perm_tmp. }
  red in IN. desc. red in IN. desc. apply seq_eqv_lr in IN. desc.
  apply a0. unfold cur_events. red. split.
  { red. exists (enum i). red in IN. 
    apply seq_eqv_lr. splits; try by vauto.
    { right. apply seq_eqv_lr. splits; auto. }
    rewrite covered_ext. by apply in_app_r. }
  destruct x, (enum i); try done.
  simpl in *. by desc.
Qed.

Definition extra_events_list i := 
  let ew_fin := ew_finite i in
  sb_sort (proj1_sig (as_list ew_fin)).

Lemma eel_ee i e (INL: In e (extra_events_list i)): extra_events i e.
Proof.
  unfold extra_events_list in INL. destruct (as_list _). desc. simpl in *.
  by apply a0, sb_sort_sim.
Qed.

Lemma ee_local_writes i
      (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init))):
  extra_events i ⊆₁ Tid_ (tid (enum i)) ∩₁ is_regular_write'.
Proof.
  unfold extra_events. 
  apply set_subset_inter_r. split.
  { red. ins. red in H. desc. destruct x.
    { unfolder in H0. simpl in H0. intuition. }
    red in H. desc. apply sb_tid_init in H. des; done. }
  unfolder. intros x [[SBxe IMM] H]. apply not_or_and in H as [NCOV NINIT].
  destruct x; [simpl in NINIT; done| ].
  destruct l; [| by unfolder'; intuition| ]; exfalso; apply NCOV, prev_covered; auto. 
  { red. apply ct_step. cut (ppo G (ThreadEvent thread index (Aload x v)) (enum i)); [basic_solver 5 |].
    red. split; auto. unfolder'. intuition. }
  { red. apply ct_step. cut (implied_fence G (ThreadEvent thread index (Armw x vr vw)) (enum i)); [basic_solver 5 |].
    red. right. apply seq_eqv_l. split; vauto. }
Qed. 

Lemma Bf_r i thread index l v
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMr: enum i = ThreadEvent thread index (Aload l v)):
  Bf i = map inl (extra_events_list i ++ [ThreadEvent thread index (Aload l v)]).
Proof.
  remember (ThreadEvent thread index (Aload l v)) as r. 
  unfold Bf.
  rewrite emiF; [| by rewrite ENUMr, Heqr; unfolder'; intuition].
  rewrite app_nil_r. f_equal. 

  unfold Bf_events. destruct (as_list _) as [block [NODUP DIFF]]. simpl in *.

  pose proof DIFF as DIFF_. 
  rewrite <- Bf_ce_diff, Bf_contents in DIFF; [| done].

  assert ((fun x => In x block) ≡₁ (fun x => In x (extra_events_list i ++ [r]))).
  { 
    split.
    { red. ins. apply DIFF in H. do 2 (red in H; desc).
      red in H. des.
      { subst x. apply in_app_r. vauto. }
      (* exfalso. *)
      apply in_app_l. 
      assert ((E \₁ is_init) x) as ENIx.
      { red. split; auto. red in H. apply seq_eqv_lr in H. by desc. }
      pose proof (G_IND ENIx) as [ix [DOMx ENUMx]].
      unfold extra_events_list. destruct (as_list _). desc. simpl in *.
      eapply Permutation_in; [apply sb_sort_perm_tmp| ].
      apply a0. unfold extra_events. red. split.
      2: { red. ins. red in H2. des; [| done].
           apply covered_cur in H2; auto. }
      red. split; [done| ].
      red. ins. red in H2. destruct H2 as [r' [SBxr' H2]]. apply seq_eqv_l in H2 as [Rr' SBr'r].
      apply H1. red. exists r'. apply seq_eqv_lr. splits; [done|by right | ]. 
      apply in_ce.
      forward eapply (@G_IND r') as [ir' [DOMr' ENUMr']].
      { red in SBxr'. apply seq_eqv_lr in SBxr'. desc.
        pose proof (init_non_r r' Rr'). vauto. }
      exists ir'. split; auto.
      apply (@ENUM_ORDER ir' i); auto.
      rewrite ENUMr', ENUMr.
      red.
      destruct r'; [done| ]. remember (ThreadEvent thread0 index0 l0) as r'. 
      destruct l0; [| subst; done| ]; apply ct_step. 
      { cut (ppo G r' r); [basic_solver 10| ]. red. red. split; [congruence| ].
        unfolder'. subst r'. intuition. }
      { cut (implied_fence G r' r); [basic_solver 10| ]. red. right.
        apply seq_eqv_l. split; [| congruence]. unfolder'. by subst r'. }
    }
    { assert (In r block) as BLOCKr. 
      { apply DIFF. split.
        2: { red. red. ins. eapply init_non_r; eauto. subst r. by unfolder'. }
        red. split; [by left; congruence| ].
        apply r_new; [subst r; by unfolder'| congruence |done]. }
      red. ins. apply in_app_iff in H. des.
      2: { simpl in H. des; [| done]. by subst x. }
      apply DIFF. 
      unfold extra_events_list in H. destruct (as_list _). desc. simpl in *.
      eapply Permutation_in in H; [| by apply Permutation_sym, sb_sort_perm_tmp].
      apply a0 in H. do 2 (red in H; desc).
      unfold set_union in H0. apply not_or_and in H0. desc.
      red in H. desc. 
      split; [| done]. red. split; [by right; congruence| ].
      red. ins. do 2 red in H3. destruct H3 as [r' H3].
      apply seq_eqv_lr in H3. desc.
      red in H4. des; [by vauto| ].
      assert (sb G r' r) as SBr'r.
      { eapply event_block_prefix with (i := i). 
        { by apply DIFF_. }
        { by apply covered_cur. }
        { transitivity (tid x).
          { rewrite ENUMr in H. apply sb_tid_init in H. des; done. }
          { apply sb_tid_init in H4. des; done. }
        }
      }
      apply H2. red. exists r'. split; auto. apply seq_eqv_l. split; [| congruence].
      contra NRr'. apply H0, in_ce.
      pose proof (G_IND H3) as [ix [DOMx ENUMx]].
      exists ix. split; auto.
      apply in_ce in H5. desc. cut (ix < j); [lia| ]. 
      apply ENUM_ORDER; auto.
      { liaW (set_size (E \₁ is_init)). }
      red. rewrite ENUMx, H5.
      assert ((E \₁ is_init) r') as [Er' NIr']. 
      { red. split.
        { red in H. apply seq_eqv_lr in SBr'r. by desc. }
        apply no_sb_to_init, seq_eqv_r in H4. by desc. }
      destruct r'; [by unfolder'| ]. remember (ThreadEvent thread0 index0 l0) as r'. 
      destruct l0; [by subst r'; unfolder'| | ]; apply ct_step. 
      { cut (ppo G x r'); [basic_solver 10| ]. do 2 red. split; auto.
        subst x r'. unfolder'. intuition. }
      { cut (implied_fence G x r'); [basic_solver 10| ]. red. left.
        apply seq_eqv_r. split; auto. subst r'. by unfolder'. }
    }
  }

  forward eapply (@NoDup_Permutation _ block (extra_events_list i ++ [r])) as PERM; auto.
  { unfold extra_events_list. destruct (as_list _).
    desc. simpl in *.
    unfold extra_events in a0. 
    apply nodup_app. splits; [| done| ].
    { apply Permutation_NoDup with (l := x); auto. apply sb_sort_perm_tmp. }
    red. ins. des; [| done]. subst a1.
    eapply Permutation_in in IN1; [| apply Permutation_sym, sb_sort_perm_tmp].
    apply a0 in IN1. unfold extra_events in IN1.
    do 2 (red in IN1; desc). apply (@sb_irr G r). congruence. }
  { by apply set_equiv_exp_iff. }

  apply sb_sorted_perm_eq; auto.
  { apply perm_trans with (l' := block); auto.
    apply Permutation_sym, sb_sort_perm_tmp. }
  { unfold sb_sort. apply sort_ninit with (thread := thread); auto.
    { rewrite <- DIFF_, CE_E. basic_solver. }
    { rewrite H, set_union_app.
      unfold extra_events_list. destruct (as_list _). desc. simpl.
      rewrite sb_sort_sim in a0. rewrite <- a0, ee_local_writes; auto.
      apply set_subset_union_l. split. 
      { rewrite ENUMr, Heqr. simpl. basic_solver. }
      { rewrite Heqr. basic_solver. } }
  }
  { apply StronglySorted_app.
    { unfold extra_events_list, sb_sort. destruct (as_list _). desc. simpl in *.
      apply sort_ninit with (thread := thread); auto. 
      { rewrite <- a0. unfold extra_events, sb. basic_solver. }
      { rewrite <- a0, ee_local_writes, ENUMr, Heqr; auto. simpl. basic_solver. } }
    { constructor; done. }
    { ins. des; [| done]. subst x2.
      unfold extra_events_list, sb_sort in IN1.
      eapply Permutation_in in IN1; [| apply Permutation_sym, sb_sort_perm_tmp].
      destruct (as_list _). desc. simpl in *.
      apply a0 in IN1. unfold extra_events in IN1.
      do 2 (red in IN1; desc). apply seq_eqv_lr in IN1. desc. congruence. }
  }  
Qed.

Lemma filter_filterP(A : Type) (S: A -> Prop) (T: A -> bool) l
      (EQ: forall a, S a <-> T a = true):
    filterP S l = filter T l. 
Proof.
  induction l; [done| ].
  specialize (EQ a). simpl. destruct (T a).
  { rewrite emiT; [congruence| ]. intuition. }
  { rewrite emiF; [congruence| ]. intuition. }
Qed.

Lemma ee_structure i thread index l v
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMr: enum i = ThreadEvent thread index (Aload l v)):
    filterP (is_regular_write' \₁ (fun e => In e (covered_events (S i))))
            (Bf_events i) = extra_events_list i.
Proof.
  forward eapply Bf_r as BF; eauto.
  unfold Bf in BF. rewrite emiF, app_nil_r in BF; [| rewrite ENUMr; unfolder'; intuition].
  apply inj_map in BF; [| by red; ins; inversion H].
  rewrite BF, filterP_app. simpl. rewrite emiF, app_nil_r; [| unfolder'; intuition].
  unfold set_minus. forward eapply filterP_split with (l := extra_events_list i) as SPLIT.
  unfold set_inter in SPLIT. rewrite SPLIT.
  rewrite filterP_all.
  2: { apply Forall_filterP, Forall_forall. ins.
       forward eapply (@ee_local_writes i DOM x) as [_ REGWx]; auto.
       unfold extra_events_list in H. destruct (as_list _). desc. simpl in *.
       by apply a0, sb_sort_sim. }
  apply filterP_all, Forall_forall. ins. 
  unfold extra_events_list in H. destruct (as_list _). desc. simpl in *.
  rewrite sb_sort_sim in a0. apply a0 in H.
  do 2 red in H. desc. unfold set_union in H0.
  rewrite covered_ext, in_app_iff. apply and_not_or. split; [by intuition| ].
  simpl. apply and_not_or. split; [| done].
  red. ins. subst x. red in H. desc. eapply (@sb_irr G); eauto.
Qed. 

Lemma cov_ncov_co i w1 w2
      (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (COV1: In w1 (covered_events i))
      (NCOV2: ~ In w2 (covered_events i))
      (W1: is_w w1)
      (W2: is_w w2)
      (E2: (E \₁ is_init) w2)
      (LOC: same_loc w1 w2):
  co G w1 w2.
Proof.
  pose proof (@wf_co_total G WF (loc w1)) as TOT. red in TOT.
  specialize TOT with (a := w1) (b := w2). specialize_full TOT.
  { apply covered_cur, CE_E in COV1; auto. red in COV1. desc. by unfolder. }
  { red in E2. desc. by unfolder. }
  { red. ins. by subst. }
  des; [done| ]. exfalso.
  pose proof (G_IND E2) as [iw2 [DOM2 ENUMw2]]. 
  apply in_ce in COV1. desc.
  apply NCOV2. apply in_ce. exists iw2. split; auto.
  cut (iw2 < j); [lia| ].
  apply ENUM_ORDER; auto.
  { liaW (set_size (E \₁ is_init)). }
  red. apply ct_step. basic_solver.
Qed.

Lemma rf_co_latest i thread index l v w
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMr : enum i = ThreadEvent thread index (Aload l v))
      (RFwr : rf G w (enum i)):
  forall w'
      (INw': In w'
                (filter (fun b : Event => loc b =? l)
                 (filterP
                    (is_regular_write' \₁
                     (fun e : Event => In e (covered_events i)))
                    (thread_prefix i thread) ++ extra_events_list i))),
    (co G)^? w' w.
Proof.
  ins. 
  remember (ThreadEvent thread index (Aload l v)) as r. rewrite ENUMr in RFwr.
  contra NCOw'w. unfold HahnRelationsBasic.clos_refl in NCOw'w. apply not_or_and in NCOw'w. desc. 
  pose proof (@wf_co_total G WF (loc w)) as TOT. red in TOT.
  specialize TOT with (a := w) (b := w'). specialize_full TOT. 
  { apply (wf_rfE WF), seq_eqv_lr in RFwr. desc.
    apply (wf_rfD WF), seq_eqv_lr in RFwr0. desc.
      by unfolder. }
  { apply in_filter_iff in INw'. desc.
    apply beq_nat_true in INw'0. split. 
    2: { rewrite INw'0. erewrite wf_rfl; [| | apply RFwr]; auto.
         subst r. by unfolder'. }
    apply in_app_iff in INw'. des.
    { apply in_filterP_iff in INw'. desc.
      apply thread_prefix_properties in INw'. red in INw'. desc.
      apply CE_E in INw'. red in INw'. red in INw'1. desc.
      unfolder'. intuition. }
    { unfold extra_events_list in INw'. destruct (as_list _). desc. simpl in *.
      rewrite sb_sort_sim in a0. apply a0 in INw'.
      split.
      { unfold extra_events in INw'. red in INw'. desc.
        unfold sb in INw'. red in INw'. desc. apply seq_eqv_lr in INw'. by desc. } 
      { apply ee_local_writes in INw'; auto. red in INw'. desc. unfolder'. intuition. }
    }
  }
  { intuition. }
  des; [| done].
  assert (sb G w' r) as SBw'r.
  { apply in_filter_iff in INw'. desc.
    apply in_app_iff in INw'. des.
    { apply in_filterP_iff in INw'. desc. apply thread_prefix_properties in INw'.
      red in INw'. desc. 
      apply event_block_prefix with (i := i); auto.
      { apply Bf_ce_diff. erewrite Bf_r; eauto.
        2: { rewrite ENUMr. by subst r. }
        rewrite map_app. apply in_app_r. subst r. vauto. }
      { rewrite INw'2. by subst r. }
    }
    unfold extra_events_list in INw'. destruct (as_list _). desc. simpl in *.
    rewrite sb_sort_sim in a0. apply a0 in INw'.
    do 2 red in INw'. desc. red in INw'. desc. congruence. }
  cdes TSO_CONS. red in TSO_CONS1. apply (TSO_CONS1 w').
  apply ct_begin. red. exists r. split.
  { cut (restr_eq_rel loc (sb G) w' r); [basic_solver 10| ]. red. split; auto.
    erewrite <- (wf_rfl WF w r RFwr). erewrite <- wf_col; eauto. }
  { apply rt_step. cut (fr G r w'); [basic_solver 10| ].
    red. split.
    2: { red. ins. red in H. desc. subst w'. by apply (sb_irr SBw'r). }
    red. exists w. split; auto. }
Qed. 
  


Lemma r_step sh_mem bufs i thread index l v
      (SIM : simulates (sh_mem, bufs) i)
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (ENUMr: enum i = ThreadEvent thread index (Aload l v)):
    TSO_block_step (sh_mem, bufs)
             (map inl (extra_events_list i ++ [ThreadEvent thread index (Aload l v)]))
             (sh_mem, upd bufs thread (bufs thread ++
                                            map (fun e : Event => (loc e, valw e: Val)) (extra_events_list i))).
Proof.
  remember (ThreadEvent thread index (Aload l v)) as r.
  pose proof (G_INSET _ DOM) as ENIr. 
rewrite map_app. apply block_step_app.
  exists (sh_mem, upd bufs thread (bufs thread ++ map (fun e => (loc e, valw e: Val))
                                   (extra_events_list i))).
  split.
  { remember (extra_events_list i) as ws.
    unfold extra_events_list in Heqws. destruct (as_list _). desc. simpl in *.
    pose proof (@ee_local_writes i DOM) as LW. rewrite a0, sb_sort_sim, <- Heqws in LW.
    generalize dependent LW. generalize ws.
    set (P := fun ws0 => (fun e : Event => In e ws0) ⊆₁ Tid_ (tid (enum i)) ∩₁ is_regular_write' ->
  TSO_block_step (sh_mem, bufs) (map inl ws0)
    (sh_mem,
     upd bufs thread (bufs thread ++ map (fun e => (loc e, valw e: Val)) ws0))).
    apply (rev_ind P); subst P. 
    { simpl. rewrite app_nil_r. rewrite updI. constructor. }
    intros w ws' IH LW. rewrite !map_app. apply block_step_app.
    eexists. split.
    { apply IH. red. ins. by apply LW, in_app_l. }
    simpl. econstructor; [| by econstructor].
    rewrite app_assoc.
    
    remember (upd bufs thread (bufs thread ++ map (fun e => (loc e, valw e: Val)) ws')) as bufs'.
    remember (upd bufs thread
      ((bufs thread ++ map (fun e : Event => (loc e, valw e: Val)) ws') ++
                                                                     [(loc w, valw w: Val)])) as bufs''.
    assert (bufs'' = upd bufs' thread ((bufs' thread ++ [(loc w, valw w)]))).
    { extensionality thread'. destruct (classic (thread' = thread)).
      { subst thread' bufs'' bufs'. by rewrite !upds. }
      { subst bufs'' bufs'. by rewrite !updo. }
    }
    rewrite H. 
    specialize (LW w). specialize_full LW; [by apply in_app_r| ].
    destruct LW as [TIDw REGWw]. rewrite ENUMr in TIDw. simpl in TIDw.
    forward eapply (@reg_write_structure (inl w)) as REGWw'; [done| ].
    desc. inversion REGWw'. rewrite H1 in TIDw. simpl in TIDw. subst thread0. 
    unfold Events.loc, loc_l, valw. simpl. subst r. constructor. }
  
  simpl. econstructor; [| by econstructor].
  assert (exists w, rf G w r) as [w RFwr].
  { red in RF_COMPL. forward eapply (@RF_COMPL r); eauto. 
    split; [red in ENIr; desc; congruence| by subst r]. }
  remember (upd bufs thread
      (bufs thread ++
            map (fun e : Event => (loc e, valw e: Val)) (extra_events_list i))) as bufs'.
  destruct (Nat.eq_0_gt_0_cases (length (filter (fun loc_val => Nat.eqb (fst loc_val: Loc) l) (bufs' thread)))) as [FLT_BUF | FLT_BUF]. 
  { apply length_zero_iff_nil in FLT_BUF. 
    rewrite Heqr. apply tso_Read_mem; [by constructor| ].
    replace v with (valr r) by vauto. rewrite <- (wf_rfv WF _ _ RFwr).
    red in SIM. desc. simpl in MEM. rewrite MEM. f_equal.
    replace l with (loc w).
    2: { apply (wf_rfl WF) in RFwr. red in RFwr. vauto. }
    apply empty_buf_read; auto.
    { congruence. }

    erewrite filterP_ext.
    2: { ins. generalize x. apply set_equiv_exp_iff.
         rewrite <- set_inter_minus_l, set_interC. apply set_equiv_refl2. }
    rewrite filterP_split. rewrite tp_ext; auto. rewrite emiT; [| done].
    rewrite !filterP_app.

    specialize (BUFS thread). simpl in BUFS. 
    remember (filterP (is_regular_write' \₁ (fun e => In e (covered_events i))) (thread_prefix i thread)) as buf_events.
    rewrite Heqbufs', upds, filter_app in FLT_BUF.
    apply app_eq_nil in FLT_BUF. desc.
    apply app_eq_nil. split.
    { erewrite filterP_ext with (f := (is_regular_write' \₁ (fun e : Event => In e (covered_events (S i))))).
      2: { ins. generalize x. apply set_equiv_exp_iff. apply FILTER_HELPER.
           rewrite ENUMr, Heqr. unfolder'. intuition. }
      replace (tid (enum i)) with thread.
      2: { by rewrite ENUMr, Heqr. }
      rewrite BUFS in FLT_BUF.
      apply List.map_eq_nil with (f := (fun e => (loc e: Loc, valw e: Val))).
      rewrite filter_map in FLT_BUF.
      rewrite <- FLT_BUF. f_equal. simpl.
      subst buf_events. apply filter_filterP.
      replace (loc w) with l; [| by erewrite (wf_rfl WF); eauto; subst r; unfolder'].
      ins. symmetry. apply Nat.eqb_eq. }
    { rewrite filter_map in FLT_BUF0. 
      apply List.map_eq_nil with (f := (fun e => (loc e: Loc, valw e: Val))).
      rewrite <- FLT_BUF0. f_equal. simpl.
      erewrite ee_structure; eauto.
      2: { rewrite ENUMr; eauto. }
      apply filter_filterP.
      replace (loc w) with l; [| by erewrite (wf_rfl WF); eauto; subst r; unfolder'].
      ins. symmetry. apply Nat.eqb_eq. }
  }  

  rewrite Heqr. eapply tso_Read_buf.
  eapply latest_loc; [by apply eq_refl| ]. simpl.
  remember (filter (fun loc_val : Loc * Val => fst loc_val =? l) (bufs' thread)) as buf_flt.
  red in SIM. desc. specialize (BUFS thread). simpl in BUFS.
  rewrite Heqbufs', upds in Heqbuf_flt.
  rewrite BUFS, <- map_app in Heqbuf_flt.
  rewrite filter_map in Heqbuf_flt. simpl in Heqbuf_flt.
  replace (l, v) with (loc w, valw w: Val).
  (* replace (l, v) with ((fun e : Event => (loc e, valw e)) w).  *)
  2: { f_equal; [erewrite wf_rfl | erewrite wf_rfv]; eauto; subst r; by unfolder'. }
  rewrite Heqbuf_flt at 1. symmetry.
  apply map_nth_error with (f := (fun e => (loc e, valw e))).
  remember (filter (fun b => loc b =? l)
       (filterP
          (is_regular_write' \₁ (fun e : Event => In e (covered_events i)))
          (thread_prefix i thread) ++ extra_events_list i)) as evs_flt.
  subst buf_flt. rewrite map_length in FLT_BUF. rewrite map_length.
  
  
  assert (exists w', nth_error evs_flt (length evs_flt - 1) = Some w') as [w' LASTw'].
  { apply opt_val, nth_error_Some. lia. }

  forward eapply rf_co_latest as COw'w; eauto.
  { rewrite ENUMr. by subst r. }
  { rewrite ENUMr. eauto. }
  { eapply nth_error_In. subst evs_flt. eauto. }

  red in COw'w. des; [congruence| ]. exfalso. 

  forward eapply (@G_IND w) as [iw [DOMiw ENUMw]].
  { split.
    { apply (wf_coE WF) in COw'w. apply seq_eqv_lr in COw'w. by desc. }
    { red. ins. eapply wf_co_init; eauto. apply seq_eqv_r. split; eauto. }
  }
  
  assert ((E \₁ is_init) w' /\ ~ In w' (covered_events i)) as [ENIw' NCOVw'].
  { apply nth_error_In in LASTw'. subst evs_flt. apply in_filter_iff in LASTw'. desc.
    apply in_app_iff in LASTw'. des.
    { apply in_filterP_iff in LASTw'. desc. red in LASTw'1. desc. split; [| done].
      apply thread_prefix_properties in LASTw'. red in LASTw'. desc.
      eapply CE_E; eauto. }
    { apply eel_ee in LASTw'. do 2 red in LASTw'. desc.
      apply not_or_and in LASTw'1. desc. unfolder. splits; auto.
      red in LASTw'. desc. red in LASTw'. apply seq_eqv_lr in LASTw'. by desc. }
  }
  
  assert (exists iw', enum iw' = w' /\ i < iw' /\ NOmega.lt_nat_l iw' (set_size (E \₁ is_init))) as [iw' [ENUMw' [GT DOMw']]].
  { forward eapply (G_IND ENIw') as [iw' [ENUMw' GT]]. eexists. splits; eauto.
    pose proof (NPeano.Nat.lt_trichotomy i iw'). des; auto.
    { subst iw'. assert (r = w') by congruence. subst r.
      apply wf_coD, seq_eqv_lr in COw'w; auto.
      desc. rewrite <- H in COw'w. by unfolder. }
    { assert (In w' (covered_events i)); [| done].
      apply in_ce. eexists. split; eauto. }
  }
 
  forward eapply (@ENUM_ORDER iw' iw) as CO_LT; auto.
  { red. rewrite ENUMw, ENUMw'. apply ct_step. generalize COw'w. basic_solver. }
  apply rfi_union_rfe in RFwr. red in RFwr. des.
  2: { forward eapply (@ENUM_ORDER iw i) as LT; auto. 
       { red. rewrite ENUMw, ENUMr. apply ct_step. generalize RFwr. basic_solver. }
       lia. }
  destruct RFwr as [RFwr SBwr]. 
  
  destruct w.
  { eapply wf_co_init; eauto. apply seq_eqv_r. split; vauto. }
  remember (ThreadEvent thread0 index0 l0) as w. 
  destruct l0.
  { apply wf_coD, seq_eqv_lr in COw'w; eauto. subst w. by desc. }
  2: { forward eapply (@ENUM_ORDER iw i); auto; [| lia].
       rewrite ENUMw, ENUMr. red. apply ct_step. cut (implied_fence G w r); [basic_solver 10| ].
       red. right. apply seq_eqv_l. split; auto. by subst w. }

  assert (thread0 = thread /\ v0 = v /\ x = l); [| desc; subst thread0; subst v0; subst x]. 
  { subst w r. splits. 
    { apply seq_eqv_lr in SBwr. desc. simpl in SBwr0. by desc. } 
    { apply wf_rfv in RFwr; auto. }
    { apply wf_rfl in RFwr; auto. } }

  erewrite <- ee_structure in Heqevs_flt; eauto; [| by rewrite ENUMr; eauto].
  erewrite filterP_ext in Heqevs_flt. 
  2: { ins. generalize x. apply set_equiv_exp_iff. symmetry. apply FILTER_HELPER.
       rewrite ENUMr. subst r. unfolder'. intuition. }
  rewrite <- filterP_app in Heqevs_flt. 
  forward eapply tp_ext with (i := i) (thread := thread) as TP_EXT; eauto.
  rewrite emiT in TP_EXT; [| by rewrite ENUMr; subst r].
  rewrite <- TP_EXT in Heqevs_flt. 

  pose proof (G_INSET iw DOMiw) as ENIw. 

  assert (In w evs_flt) as INw.
  { rewrite Heqevs_flt. apply in_filter_iff. split.
    2: { subst w. unfolder'. apply Nat.eqb_refl. }
    apply in_filterP_iff. split.
    2: { split.
         { subst w. unfolder'. intuition. }
         { red. ins. apply in_ce in H. desc. 
           cut (j = iw); [lia| ].
           apply G_INJ; [| | congruence];  liaW (set_size (E \₁ is_init)). }
    }
    apply thread_prefix_properties. split; [| by subst w].
    exists r. apply seq_eqv_lr. splits; auto; [congruence| ]. 
    rewrite covered_ext, in_app_iff. subst r. vauto. 
  }

  apply In_nth_error in INw. desc.
  pose proof (Nat.lt_trichotomy n (length evs_flt - 1)). des.
  2: { subst n. rewrite LASTw' in INw. inversion INw.
       apply (co_irr WF w). congruence. }
  2: { forward eapply (proj2 (nth_error_None evs_flt n)); [lia| congruence]. }
  assert (sb G w w') as SBww'.
  2: { forward eapply (@ENUM_ORDER iw iw'); auto; [| lia].
       red. rewrite ENUMw, ENUMw'. apply ct_step. cut (ppo G w w'); [basic_solver 10| ].
       red. split; auto. apply or_not_and. right.
       apply nth_error_In in LASTw'. rewrite Heqevs_flt in LASTw'. 
       apply in_filter_iff in LASTw'. desc. apply in_filterP_iff in LASTw'. desc.
       red in LASTw'1. desc.
       generalize LASTw'1. unfolder'. destruct w'; vauto; destruct l0; intuition.
  }
  red. apply seq_eqv_lr. splits; try by unfolder'; desc.
  { unfolder'. desc. congruence. } 
  eapply sorted_ordered; eauto.
  subst evs_flt. apply StronglySorted_filter, StronglySorted_filterP.
  unfold thread_prefix. destruct (as_list _). desc. simpl in *. 
  apply sort_ninit with (thread := thread); auto.
  { rewrite <- a0, CE_E. basic_solver. }
  { rewrite <- a0. basic_solver. }
Qed.
  

Lemma r_simulation_preserved sh_mem bufs i thread index l v
      (DOM : NOmega.lt (NOnum i) (set_size (E \₁ is_init)))
      (SIM : simulates (sh_mem, bufs) i)
      (Heqei : enum i = ThreadEvent thread index (Aload l v)):
  simulates
    (sh_mem, upd bufs thread (bufs thread ++
                                   map (fun e : Event => (loc e, valw e))
                                   (extra_events_list i)))
    (S i). 
Proof.
  remember (ThreadEvent thread index (Aload l v)) as r. 
  red in SIM. desc. red. splits.
  { ins. rewrite MEM. f_equal. f_equal.
    rewrite covered_ext, filterP_app. simpl.
    rewrite emiF; [by rewrite app_nil_r| ].
    rewrite Heqei, Heqr. unfolder'. intuition. }
  { ins.
    destruct (classic (thread0 = thread)).
    2: { rewrite updo; auto. rewrite BUFS. f_equal.
         rewrite tp_ext; auto. rewrite emiF.
         2: { rewrite Heqei, Heqr. unfolder'. intuition. } 
         rewrite app_nil_r.
         apply filterP_ext. ins. generalize x. apply set_equiv_exp_iff. 
         symmetry. apply FILTER_HELPER. 
         rewrite Heqei, Heqr. unfolder'. intuition. }
    subst thread0. rewrite upds. rewrite BUFS.
    rewrite <- map_app. f_equal.
    erewrite <- ee_structure; auto; [| by rewrite Heqei; eauto].
    erewrite filterP_ext.
    2: { ins. generalize x. apply set_equiv_exp_iff. symmetry. apply FILTER_HELPER.
         rewrite Heqei. subst r. unfolder'. intuition. }
    rewrite <- filterP_app. f_equal.
    rewrite tp_ext; auto. rewrite emiT; [| by rewrite Heqei; subst r]. done.
  }
Qed.

Lemma simulation_step i st (SIM: simulates st i)
      (DOM: NOmega.lt (NOnum i) (set_size (E \₁ is_init))):
  exists st' : TSOMemory, TSO_block_step st (Bf i) st' /\ simulates st' (S i).
Proof.
  remember (enum i) as ei.
  pose proof (G_INSET i DOM) as ENIe.
  destruct ei.
  { red in ENIe. desc. rewrite <- Heqei in ENIe0. by unfolder'. }
  destruct st as [sh_mem bufs]. 
  destruct l.
  3: { exists (upd sh_mem x vw, bufs). split.
       { erewrite Bf_rmw; eauto.
         eapply TSO_block_step_next; vauto.
         eapply rmw_step; eauto. }
       { eapply rmw_simulation_preserved; eauto. }
  }
  { forward eapply Bf_r as BF_R; eauto.
    set (buf_ext := map (fun e => (loc e, valw e)) (extra_events_list i)). 
    exists (sh_mem, upd bufs thread (bufs thread ++ buf_ext)). 
    split. 
    { rewrite BF_R. eapply r_step; eauto. }
    { eapply r_simulation_preserved; eauto. }
  }
  { erewrite Bf_w; eauto.
    set (bufs_pre := upd bufs thread (bufs thread ++ opt_buf_ext i thread index x v)).
    exists (upd sh_mem x v, upd bufs_pre thread (tl (bufs_pre thread))). 
    split.
    { apply w_step; auto. }
    { apply w_simulation_preserved; auto. }
  }  
Qed.

Lemma Bf_enumerator: blocks_enumerator Bf.
Proof. 
  red. ins. splits.
  { rewrite (ce_ext i). generalize (Bf_ce_disjoint i). basic_solver 10.
    Unshelve. all: eauto. }
  { apply Bf_nodup. }
  { destruct (enum i) eqn:I. 
    { pose proof (G_INSET i DOM). rewrite I in H. unfolder'. intuition. }
    destruct l.
    { erewrite Bf_r; eauto.
      rewrite map_app. red. ins. apply List.app_eq_nil in H. by desc. }
    { erewrite Bf_w; eauto.
      red. ins. apply List.app_eq_nil in H. by desc. }
    { erewrite Bf_rmw; eauto. vauto.  }
  }
  { ins.
    cut (sb G (ThreadEvent thread index1 lbl1) (ThreadEvent thread index2 lbl2)).
    { ins. unfold sb in H. apply seq_eqv_lr in H. desc. simpl in H0. by desc. }
    unfold sb. apply seq_eqv_lr.
    assert (forall e k (NTH: nth_error (Bf i) k = Some (inl e)), E e) as EE. 
    { ins.
      assert (In (inl e) (Bf i)) as IN.
      { eapply nth_error_In; eauto. }
      apply Bf_ce_diff in IN; auto. red in IN. desc.
      apply CE_E in IN. red in IN. by desc. }
    splits.
    1, 3: by (eapply EE; eauto).      
    symmetry in E1, E2. eapply (@sorted_ordered _ (Bf_events i)); eauto.
    2, 3: by apply Bf_events_nth. 
    unfold Bf_events. destruct (as_list _). desc. simpl in *.
    eapply sort_ninit; auto. 
    { red. ins. red in H. desc. 
      apply a0 in H. red in H. desc. apply CE_E in H. red in H. by desc. }
    { rewrite <- a0, <- Bf_ce_diff. eapply Bf_thread; eauto. } }
Qed.

Lemma Bf_bst_sim:
  exists bst : nat -> TSOMemory,
  forall i,
    NOmega.le (NOnum i) (set_size (E \₁ is_init)) ->
    TSO_block_step TSO.Minit (flatten (block_trace_prefix Bf i)) (bst i) /\
    simulates (bst i) i.
Proof. 
  
  set (PP := fun i st =>
               NOmega.le (NOnum i) (set_size (E \₁ is_init)) ->
               TSO_block_step TSO.Minit (flatten (block_trace_prefix Bf i)) st /\
               simulates st i).
  apply (functional_choice PP).
  intros i. induction i as [| i [st IHi]]. 
  { exists TSO.Minit. red. ins. rewrite btp0. simpl.
    split; [constructor|].
    unfold TSO.Minit. red. simpl. splits; [done| ].
    unfold empty_buffer. ins. unfold thread_prefix.
    destruct (as_list _). desc. simpl in *.
    replace (sb_sort x) with (nil: list Event); [done| ].
    symmetry. apply Permutation_nil.
    replace [] with x.
    { unfold sb_sort. apply SBSort.Permuted_sort. }
    generalize dependent a0.
    unfold cur_events, covered_events. rewrite seq0. simpl.
    arewrite (⦗fun _ : Event => False⦘ ≡ ∅₂) by basic_solver.
    rewrite !seq_false_r, dom_empty, set_inter_empty_l.
    destruct x; auto. ins. exfalso. apply (proj2 a0 e). auto. }
  destruct (classic (NOmega.le (NOnum (S i)) (set_size (E \₁ is_init)))) as [DOM| ].
  2: { exists TSO.Minit. done. }
  red in IHi. specialize_full IHi; [liaW (set_size (E \₁ is_init))| ].
  desc. 
  forward eapply (simulation_step IHi0) as [st' [STEP SIM]]; [liaW (set_size (E \₁ is_init))| ].
  exists st'. red. ins. split; auto. 
  rewrite btpS, flatten_app. apply block_step_app.
  exists st. split.
  2: { simpl. by rewrite app_nil_r. }
  apply IHi. 
Qed. 

Definition Bst := proj1_sig (constructive_indefinite_description _ Bf_bst_sim). 

Lemma Bf_Bst_reach: 
  blocks_reach Bf Bst (set_size (E \₁ is_init)). 
Proof.
  red. unfold Bst. destruct (constructive_indefinite_description _ _) as (bst & BST). simpl. 
  ins. specialize (BST _ DOM). by desc.
Qed.

Lemma event_block e (ENIe: (E \₁ is_init) e):
  exists i, (cur_events (S i) \₁ cur_events i) e /\ NOmega.lt_nat_l i (set_size (E \₁ is_init)). 
Proof.
  pose proof (G_IND ENIe) as ENUM. desc.
  apply enum_CE in ENUM0; auto. 
  assert (set_finite (fun i => ~ (cur_events i e))) as NCUR_FIN.
  { contra INF. 
    apply (AuxProp.set_infinite_nat_exists_bigger (S i)) in INF. desc.
    apply event_block_closed with (j := m) in ENUM0; auto. }
  forward eapply AuxProp.set_finite_r_min_precise_bounded with (r := gt) (n := 0) as [bound [BOUND EXACT]]; eauto.
  1, 2: by red; ins; lia. 
  { simpl. unfold cur_events, covered_events. rewrite seq0. simpl.
    red. ins. red in H. desc. apply seq_eqv_lr in H. by desc. }
  simpl in BOUND. exists bound. split.
  2: { cut (bound <= i); [liaW (set_size (E \₁ is_init))| ].
       contra GE. apply event_block_closed with (j := bound) in ENUM0; [done| lia]. }
  red. split; auto.
  contra NCUR. specialize (EXACT _ NCUR). lia.  
Qed.

Definition tid_lbl (lbl: TSO_label) :=
  match lbl with
  | inl e => tid e
  | inr thread => thread
  end.

Notation "'LTid_' t" := (fun l => tid_lbl l = t) (at level 1).


Lemma enabled_nempty_buf st thread:
  enabled st thread <-> snd st thread <> [].
Proof.
  split.
  { red. ins. red in H. desc. inversion H. subst. simpl in *. by rewrite H0 in BUF. }
  ins. destruct st as [sh_mem bufs]. simpl in H.
  destruct (bufs thread) as [| [loc val] buf'] eqn:BUF; [done| ]. 
  red. exists (upd sh_mem loc val, upd bufs thread buf'). by constructor.
Qed.

Lemma construction_fairness 
  :
  block_TSO_fair_fun_lim Bf (set_size (E \₁ is_init)) Bst. 
Proof.
  pose proof Bf_enumerator as BLOCKS_ENUM.
  unfold Bst. destruct (constructive_indefinite_description _ _) as [bst BLOCK_REACH]. simpl.  
  
  red. intros i thread DOM ENABLED.
  apply enabled_nempty_buf in ENABLED.

  specialize (BLOCK_REACH _ DOM) as [_ SIM]. 

  red in SIM. desc. specialize (BUFS thread).
  rewrite BUFS in ENABLED.
  remember (filterP (is_regular_write' \₁ (fun e => In e (covered_events i)))
                    (thread_prefix i thread)) as uncov_ws.
  assert (exists w, In w uncov_ws) as [w UNCOV].
  { destruct uncov_ws; [by simpl in ENABLED| ].
    eexists. intuition. }
  subst uncov_ws. apply in_filterP_iff in UNCOV as [TPw [REGWw UNCOVw]].
  apply thread_prefix_properties in TPw. red in TPw. desc.
  forward eapply (@G_IND w) as [iw [DOMw ENUMw]].
  { eapply CE_E; eauto. }
  exists iw. splits; auto.
  { contra LT. apply NPeano.Nat.nle_gt in LT.
    apply UNCOVw, in_ce. eexists. eauto. }

  destruct w; [by unfolder'; intuition| ].
  destruct l; try (by unfolder'; intuition).
  simpl in TPw0. subst thread0.
  erewrite Bf_w; eauto. by apply in_app_r.
Qed. 

Lemma TSO_decl_implies_op_blocks:
    exists
      (bf : nat -> list TSO_label) bst,
      blocks_reach bf bst (set_size (E \₁ is_init)) /\
      (forall i (DOM: NOmega.lt_nat_l i (set_size (E \₁ is_init))), bf i <> []) /\
    (fun e : Event =>
     exists i d : nat,
       block_pos_fun bf i d (inl e) /\ NOmega.lt_nat_l i (set_size (E \₁ is_init)))
    ≡₁ E \₁ is_init /\
    block_trace_wf_prefix_fun bf (set_size (E \₁ is_init)) /\
    block_TSO_fair_fun_lim bf (set_size (E \₁ is_init)) bst.
Proof.
  exists Bf. exists Bst. pose proof (Bf_enumerator) as BLOCKS_ENUM. 
  splits.
  { apply Bf_Bst_reach. }
  { ins. red in BLOCKS_ENUM. specialize_full BLOCKS_ENUM; [eauto| ]. by desc. }
  { red. split.
    { red. intros e [i [d [BLOCK_POS DOM]]].
      red in BLOCKS_ENUM. specialize_full BLOCKS_ENUM; [edone| ]. desc.
      destruct BLOCKS as [BLOCKS _]. specialize (BLOCKS e). specialize_full BLOCKS.
      { eapply nth_error_In. eauto. }
      destruct BLOCKS as [CE _]. eapply CE_E. eauto. } 
    { red. intros e ENIe.
      forward eapply event_block as [i [Bi DOMi]]; eauto. 
      red in BLOCKS_ENUM.
      specialize_full BLOCKS_ENUM; [edone| ]. desc.
      destruct BLOCKS as [_ BLOCKS]. specialize (BLOCKS _ Bi). simpl in BLOCKS.
      apply In_nth_error in BLOCKS as [d BLOCK_POS]. 
      exists i. exists d. split; vauto. }
  }
  { red. ins.    
    destruct H as [LT | SAME_BLOCK].
    2: { desc.
         red in BLOCKS_ENUM. specialize_full BLOCKS_ENUM; [edone| ]. desc.
         subst j. eapply WFL; eauto. }
    red in BLOCKS_ENUM.
    remember (ThreadEvent thread index1 lbl1) as e1. remember (ThreadEvent thread index2 lbl2) as e2.
    assert ((cur_events (S i) \₁ cur_events i) e1) as CE1.
    { specialize (BLOCKS_ENUM i). specialize_full BLOCKS_ENUM.
      { liaW (set_size (E \₁ is_init)). }
      desc. eapply BLOCKS, nth_error_In. eauto. }
    assert ((cur_events (S j) \₁ cur_events j) e2) as CE2.
    { specialize_full BLOCKS_ENUM; [edone| ].
      desc. eapply BLOCKS, nth_error_In. eauto. }
    cut (cur_events j e1). 
    2: { apply event_block_closed with (i := (S i)); [| lia].
         red in CE1. by desc. }
    intros CE'1.
    forward eapply event_block_prefix as SB12; eauto.
    { by subst. }
    subst e1 e2. unfold sb in SB12. apply seq_eqv_lr in SB12. desc.
    simpl in SB0. by desc. }
  { apply construction_fairness; auto. }
Qed. 

Lemma TSO_decl_implies_op_fun:
  exists (f : nat -> TSO_label) (st : nat -> TSOMemory) (tr_size : nat_omega) 
    (LTS_FUN : LTS_fun_limP TSO_lts f tr_size st),
    (fun e : Event => exists i : nat, f i = inl e /\ NOmega.lt_nat_l i tr_size)
      ≡₁ E \₁ is_init /\ fun_wf_lim f tr_size /\ TSO_fair_fun_lim LTS_FUN.
Proof.   
  cut (let block_tr_size := (set_size (E \₁ is_init)) in
       exists (bf: nat -> list TSO_label) bst,
         blocks_reach bf bst (set_size (E \₁ is_init))  /\
         (forall i (DOM: NOmega.lt_nat_l i (set_size (E \₁ is_init))), bf i <> []) /\
    (fun e : Event => exists i d, block_pos_fun bf i d (inl e) /\ NOmega.lt_nat_l i block_tr_size) ≡₁ E \₁ is_init /\
    block_trace_wf_prefix_fun bf block_tr_size /\
    block_TSO_fair_fun_lim bf block_tr_size bst);
    [| apply TSO_decl_implies_op_blocks]. 

  intros [bf' [bst [BLOCK_REACH [NEMPTY' [EVENTS' [BLOCK_WF' BLOCK_FAIR']]]]]].
  remember (set_size (E \₁ is_init)) as block_tr_size.
  assert (exists bf, (forall i (DOM: NOmega.lt_nat_l i block_tr_size),
                    bf i = bf' i) /\
                forall i, bf i <> []) as [bf [EQ NEMPTY]]. 
  { exists (fun n => match (excluded_middle_informative (NOmega.lt_nat_l n block_tr_size)) with
             | left lt => bf' n
             | right ge => [inl (InitEvent 0)]
             end).
    split.
    { ins. destruct (excluded_middle_informative _); intuition. } 
    ins. destruct (excluded_middle_informative _); [by apply NEMPTY'| done]. }
  
  set (tr_size := match block_tr_size with
                  | NOinfinity => NOinfinity
                  | NOnum n => NOnum (length (flatten (block_trace_prefix bf n)))
                  end).
  exists (expanded bf NEMPTY).
  
  forward eapply (@fairness_trans bf bst block_tr_size NEMPTY) as [st [TSO_TRACE LTS_FUN]]; auto.
  { red. ins. red in BLOCK_REACH. specialize_full BLOCK_REACH; [eauto| ].
    replace (block_trace_prefix bf i) with (block_trace_prefix bf' i); auto.
    unfold block_trace_prefix. clear BLOCK_REACH. induction i; [done| ].
    rewrite !seqS, !map_app, !Nat.add_0_l, IHi; auto.
    2: { liaW block_tr_size. }
    f_equal. simpl. by rewrite EQ. }
  { red. ins.
    red in BLOCK_FAIR'. specialize (BLOCK_FAIR' i tid). specialize_full BLOCK_FAIR'; [done| done| ].
    desc. exists j. splits; auto. by rewrite EQ. }
  exists st. exists tr_size. exists TSO_TRACE.
  
  ins. desc. fold tr_size in TSO_TRACE.
  
  splits; auto. 
  { rewrite <- EVENTS'. split; red; ins; desc.
    { rename i into n.
      forward eapply expanded_src as [i [d [N SRC]]]; eauto.
      exists i. exists d.
      split; [| eapply DOM_HELPER; eauto]. 
      red. rewrite <- EQ; [auto| ].
      eapply DOM_HELPER; eauto. }
    exists (length (flatten (block_trace_prefix bf i)) + d). split.
    { erewrite expanded_dst; eauto. red in H. rewrite H. by rewrite EQ. }
    subst tr_size. destruct block_tr_size as [| nblocks]; [done| ]. simpl in *.
    apply lt_diff in H0 as [k DIFF]. subst nblocks.
    replace (i + S k) with (S i + k) by lia.
    unfold block_trace_prefix. rewrite seq_add, seqS. simpl.
    rewrite <- app_assoc, map_app, flatten_app, length_app.
    simpl. rewrite length_app.
    cut (d < length (bf i)); [ins; lia| ].
    apply nth_error_Some, opt_val. red in H. exists (inl x).
    rewrite H. rewrite EQ; [auto| lia].
  }
  { red. intros m n thread index1 index2 lbl1 lbl2 LT DOM EXPm EXPn.
    red in BLOCK_WF'.
    apply expanded_src in EXPm as [im [dm [M SRCm]]]. apply expanded_src in EXPn as [inn [dn [N SRCn]]].
    specialize (BLOCK_WF' im inn dm dn thread index1 index2 lbl1 lbl2). apply BLOCK_WF'; try done.
    2: { eapply DOM_HELPER; eauto. }
    2: { red. rewrite <- EQ; auto. eapply DOM_HELPER with (n := m); eauto.
         eapply NOmega.lt_lt_nat; eauto. }
    2: { red. rewrite <- EQ; auto. eapply DOM_HELPER with (n := n); eauto. }
    destruct (le_lt_dec inn im); [| by auto]. right.
    apply le_diff in l. desc. subst im.
    subst m n. unfold block_trace_prefix in LT.
    rewrite seq_app, map_app, flatten_app, length_app, Nat.add_0_l in LT. 
    rewrite <- Nat.add_assoc in LT. apply plus_lt_reg_l in LT.
    split; [| lia]. cut (d = 0); [ins; lia| ].
    destruct d; auto. exfalso.
    rewrite seqS_hd in LT. simpl in LT. rewrite length_app in LT.
    cut (length (bf inn) > dn); [ins; lia| ].
    red. apply nth_error_Some, opt_val. eauto. }
  
Qed.

Lemma trace_fun_states size
      (f: nat -> TSO_label) (tr: trace TSO_label)
      (st_tr st_f: nat -> TSOMemory)
      (EQUIV: fun_trace_equiv size f tr)
      (LTS_TR: LTS_trace_param TSO_lts st_tr tr)
      (LTS_FUN: LTS_fun_limP TSO_lts f size st_f):
  forall i (DOM_EXT' : NOmega.le (NOnum i) size),
    st_tr i = st_f i.
Proof.
  destruct EQUIV as [SIZE_EQ LABELS_EQ].
  apply LTS_trace_param' in LTS_TR as [TR0 TRi].
  destruct LTS_FUN as [FUN0 FUNi]. 
  intros i. induction i.
  { ins. congruence. }
  intros DOM.
  specialize_full IHi; [liaW size| ].
  specialize (FUNi i). specialize_full FUNi; [liaW size| ].
  specialize TRi with (i := i) (d := def_lbl). specialize_full TRi.
  { subst size. auto. }
  rewrite IHi, LABELS_EQ in TRi; auto. 
  eapply TSO_step_deterministic; eauto. 
Qed.

Theorem TSO_decl_implies_op:
  exists (tr: trace TSO_label) (st: nat -> TSOMemory),
    LTS_trace_param TSO_lts st tr /\
    (fun e => trace_elems tr (inl e)) ≡₁ acts G \₁ is_init /\
    TSO_trace_wf tr /\ 
    TSO_fair tr st.
Proof.
  cut (exists (f: nat -> TSO_label) st (tr_size: nat_omega)
         (LTS_FUN: LTS_fun_limP TSO_lts f tr_size st),
          (fun e => exists i, f i = inl e /\ NOmega.lt_nat_l i tr_size)
            ≡₁ acts G \₁ is_init /\
          fun_wf_lim f tr_size /\
          TSO_fair_fun_lim LTS_FUN);
    [| apply TSO_decl_implies_op_fun]. 
  intros [f [st [tr_size [LTS_FUN [EVENTS [WF_FUN F_FAIR]]]]]]. 
  pose proof (trace_of_fun tr_size f) as [tr [LEN EQ]].
  exists tr. exists st.
  assert (LTS_trace_param TSO_lts st tr) as LTS_TRACE. 
  { red. red in LTS_FUN. desc. destruct tr; splits; vauto.
    all: ins; rewrite EQ; auto. }
  splits; auto. 
  { rewrite <- EVENTS.
    split; red; ins; desc.
    { apply trace_in_nth with (d := def_lbl) in H. desc. 
      exists n. split; [| congruence]. erewrite <- EQ; eauto. congruence. }
    rewrite <- H, <- (EQ def_lbl); auto. apply trace_nth_in. congruence. }
  { red. red in WF_FUN. ins. 
    specialize (WF_FUN i j thread index1 index2 lbl1 lbl2). apply WF_FUN; auto.
    { congruence. }
    { erewrite <- EQ; eauto. eapply NOmega.lt_lt_nat; eauto. congruence. }
    { erewrite <- EQ; eauto. congruence. } }
  { red. ins.
    assert (NOmega.le (NOnum i) tr_size) as DOM_EXT'.
    { by rewrite LEN in DOM_EXT. }
    red in F_FAIR.
    specialize (F_FAIR i tid DOM_EXT'). specialize_full F_FAIR. 
    { erewrite <- trace_fun_states; vauto. }
    desc. exists j. splits; vauto. by rewrite EQ. }
Qed.

End Decl2Op. 
