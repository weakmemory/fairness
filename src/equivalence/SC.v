(******************************************************************************)
(** * SC memory subsystem   *)
(******************************************************************************)

From hahn Require Import Hahn.
From hahn Require Import HahnOmega.
Require Import PropExtensionality.
Require Import Lia.
Require Import Arith.
Require Import AuxRel.
Require Import Labels.
Require Import Events.
Require Import Execution.
Require Import AuxProp.
Require Import TraceWf.
Require Import SetSize.
Require Import IndefiniteDescription.
Require Import Backport. 

Set Implicit Arguments.

(******************************************************************************)
(** ** Operational SC machine   *)
(******************************************************************************)

Definition Memory := Loc -> Val.

Definition Minit : Memory := fun x => 0.

Inductive SC_step (M : Memory) (e: Event) (M' : Memory) : Prop :=
| SCstep_read t i x v (EQ: e = ThreadEvent t i (Aload x v))
               (VAL: M x = v) (MEM: M' = M)
| SCstep_write t i x v (EQ: e = ThreadEvent t i (Astore x v))
                (MEM: M' = upd M x v)
| SCstep_rmw t i x vr vw (EQ: e = ThreadEvent t i (Armw x vr vw))
              (VAL: M x = vr) (MEM: M' = upd M x vw).

Definition sc_lts :=
  {| LTS_init := eq Minit ;
     LTS_step := SC_step ;
     LTS_final := ∅ |}.

(******************************************************************************)
(** ** Declarative SC machine   *)
(******************************************************************************)

Definition Ginit :=
  {| acts := is_init ;
    rf := ∅₂ ;
    co := ∅₂ |}.

Definition SCG_step G e G' :=
  ⟪ EQacts: acts G' ≡₁ acts G ∪₁ eq e ⟫ /\
  ⟪ EQrf: rf G ⊆ rf G' ⟫ /\
  ⟪ EQco: co G ⊆ co G' ⟫ /\
  ⟪ MAXco: ⦗eq e⦘ ⨾ co G ⊆ ∅₂ ⟫.

Definition dsc_lts :=
  {| LTS_init := eq Ginit ;
     LTS_step := SCG_step ;
     LTS_final := ∅ |}.

Definition sc_consistent G := irreflexive (hb_sc G).

Lemma fsupp_hb_sc G (WF: Wf G) (FAIR : mem_fair G)
        (CONS: sc_consistent G)
        (THREADS: has_finite_antichains (acts G \₁ is_init) (⦗set_compl is_init⦘ ⨾ (sb G))) :
  fsupp (⦗set_compl is_init⦘ ⨾ (hb_sc G)).
Proof using.
  rewrite <- (rel_ninit_l G); [|rewrite wf_hb_scE; unfolder; tauto].

  unfold hb_sc.
  arewrite (⦗acts G \₁ is_init⦘ ⨾ (sb G ∪ rf G ∪ co G ∪ fr G)⁺ ≡
             (⦗acts G \₁ is_init⦘ ⨾ (sb G ∪ rf G ∪ co G ∪ fr G))⁺)
    by rewrite ct_rotl, !seq_union_l, sb_ninit, rf_ninit,
               co_ninit, fr_ninit, ct_end.
  eapply fsupp_ct.
  - by rewrite inclusion_seq_eqv_l.
  - by apply seq_doma, eqv_doma.
  - by repeat rewrite seq_union_r, <- inclusion_union_r1; rewrite sb_ninit_l.
  - repeat (rewrite seq_union_r; apply fsupp_union).
    2 - 4: auto using fsupp_seq_eqv_l, fsupp_rf, fsupp_co, fsupp_fr.
    eapply fsupp_mon; [| apply (fsupp_sb WF)].  basic_solver. 
Qed.

(******************************************************************************)
(** ** SC memory *)
(******************************************************************************)

Definition sc_rel G (mem : Memory) :=
  forall l e (Ee: acts G e) (We: is_w e) (LOCe: loc e = l)
         (MAXe: ~ exists e', co G e e'),
    valw e = mem l.

Definition get_max_co G dom l :=
  fold_right (rel_max (co G)) (InitEvent l)
            (filterP (fun e =>  (acts G \₁ is_init) e /\ is_w e /\ loc e = l) dom).

Lemma get_max_co_cons G a dom l :
  get_max_co G (a :: dom) l =
  if excluded_middle_informative ( (acts G \₁ is_init) a /\ is_w a /\ loc a = l)
  then rel_max (co G) a (get_max_co G dom l)
  else get_max_co G dom l.
Proof using.
  unfold get_max_co; ins; desf.
Qed.

Lemma total_ord_not A (d : A -> Prop) (r : relation A) (TOT: is_total d r)
      (T: transitive r) (IRR: irreflexive r)
      x (Dx : d x) y (Dy : d y) :
  ~ r x y <-> x = y \/ r y x.
Proof using.
  specialize (TOT _ Dx _ Dy); split; ins; desf; eauto; try tauto.
Qed.

Lemma get_max_coE G (WF: Wf G) dom l :
  acts G (get_max_co G dom l) /\
  (~ is_init (get_max_co G dom l) -> In (get_max_co G dom l) dom) /\
  is_w (get_max_co G dom l) /\ loc (get_max_co G dom l) = l /\
  ~ (exists e', In e' dom /\ co G (get_max_co G dom l) e').
Proof using.
  induction dom; try rewrite get_max_co_cons; unfold rel_max;
    ins; desf; splits; try intro; ins; desf; eauto.
  all: unfolder in *; desf.
  all: try solve [eapply co_irr, co_trans; eauto].
  { by unfold get_max_co; ins; apply WF. }
  2: { apply n; unfolder; splits; ins.
    apply wf_coE in H0; unfolder in H0; ins; desf.
    intro; eapply wf_co_init; unfolder; eauto.
    apply wf_coD in H0; unfolder in H0; ins; desf.
    apply wf_col in H0; unfold same_loc in *; congruence. }
  destruct WF; rewrite total_ord_not in n; eauto; desf; eauto.
  rewrite n in H0; eauto.
Qed.

Lemma sc_rel_uniq G (WF: Wf G) (FIN: set_finite (acts G \₁ is_init)) :
  exists ! mem, sc_rel G mem.
Proof using.
  red in FIN; desc.
  exists (fun l => valw (get_max_co G findom l)).
  assert (X := get_max_coE WF findom).
  split; unfold sc_rel; ins; desf.
  { specialize (X (loc e)); ins; desf.  
    f_equal; apply NNPP; intro NEQ; eapply wf_co_total in NEQ; desf; eauto;
      unfolder; ins.
    apply X3; eexists; split; eauto.
    apply FIN; split; ins; intro; eapply wf_co_init; unfolder; eauto. }
  extensionality l; specialize (X l); desf.
  eapply H; eauto; red; ins; desf.
  apply wf_coE in H0; unfolder in H0; desf.
  eapply X3; eexists; split; eauto.
  apply FIN; split; ins; intro; eapply wf_co_init; unfolder; eauto.
Qed.
  
Section SC.

  Variable G : execution.
  Hypothesis WF: Wf G.
  Variable nu : nat -> Event.
  Hypothesis ENUM : enumerates nu (acts G \₁ is_init).
  Hypothesis IMPL :
    forall i (LTi: lt_size i (acts G \₁ is_init))
           j (LTj: lt_size j (acts G \₁ is_init))
           (REL: hb_sc G (nu i) (nu j)), i < j.
  Hypothesis COMPL : rf_complete G.
  Hypothesis SC : sc_consistent G.

  Lemma pref_proj e j (LTj : lt_size j (acts G \₁ is_init))
        (REL: hb_sc G e (nu j))
      n (LT: j <= n) :
    (acts G ∩₁ (is_init ∪₁ (nu ↑₁ (fun x => x < n)))) e.
  Proof using WF ENUM IMPL.
    ins; eapply wf_hb_scE in REL; unfolder in REL; ins; desf.
    split; ins; red; classical_right.
    assert (X := ENUM); eapply enumeratesE in X; desf.
    forward eapply (SUR e) as LTi; ins; desf.
    exists i; eauto using Nat.lt_le_trans.
  Qed.

  Lemma sc_rel_init :
    sc_rel (exec_enum G nu 0) (fun _ => 0).
  Proof using.
    unfold exec_enum; red; ins; desf.
    unfold is_init in Ee; unfolder in Ee; desf; lia.
  Qed.

  Lemma sc_step_read_value n (LT: lt_size n (acts G \₁ is_init))
        mem (REL: sc_rel (exec_enum G nu n) mem)
        (Rn : is_r (nu n)) :
    valr (nu n) = mem (loc (nu n)).
  Proof using WF ENUM IMPL COMPL.
    assert (En: acts G (nu n)).
    { apply enumeratesE in ENUM; apply ENUM; eauto using lt_lt_size. }
    forward apply (@COMPL (nu n)) as (w & RF); ins.
      rewrite <- (wf_rfv WF _ _ RF).
      eapply REL; ins.
      - eapply pref_proj with (j := n); eauto using lt_lt_size.
        econs; unfolder; eauto.
      - apply wf_rfD in RF; unfolder in RF; desf.
      - apply wf_rfl in RF; unfolder in RF; desf.
      - intro X; desc; unfolder in X; desc.
        clear X.
        assert (NIe' : ~ is_init e')
          by (intro; eapply (wf_co_init WF); unfolder; edone).
        desf.
        cut (n < y); try lia.
        apply IMPL; eauto using lt_lt_size.
        econs; right; red; unfolder; split; eauto.
        intro; desf.
        apply enumeratesE in ENUM; apply ENUM in H; eauto using lt_lt_size;
          lia.
  Qed.

  Lemma sc_step_non_write n (LT: lt_size n (acts G \₁ is_init))
        mem (REL: sc_rel (exec_enum G nu n) mem)
        (NWn : ~ is_w (nu n)) :
    sc_rel (exec_enum G nu (S n)) mem.
  Proof using ENUM.
    assert (En: acts G (nu n)).
    { apply enumeratesE in ENUM; apply ENUM; eauto using lt_lt_size. }
    red; ins; desf; eapply REL; ins.
    unfolder in Ee; unfolder; desc; split; ins.
    desf; vauto; right; exists y; split; ins.
    destruct (eqP y n); desf; try lia.
    intro X; desc; unfolder in X; desc.
    destruct MAXe; exists e'; unfolder; splits; ins.
    clear X1; desf; eauto 6.
    clear X; desf; eauto 6.
  Qed.

  Lemma sc_step_write n (LT: lt_size n (acts G \₁ is_init))
        mem (REL: sc_rel (exec_enum G nu n) mem)
        (Wn : is_w (nu n)) :
    sc_rel (exec_enum G nu (S n)) (upd mem (loc (nu n)) (valw (nu n))).
  Proof using WF ENUM IMPL.
    assert (En: acts G (nu n)).
    { apply enumeratesE in ENUM; apply ENUM; eauto using lt_lt_size. }
    unfold upd; red; ins; desf.
    {
      destruct (classic (e = nu n)) as [|CO]; desf.
      destruct MAXe; unfolder in Ee; desc.
      eapply (wf_co_total WF) in CO.
      2-3: unfolder; splits; ins.
      destruct CO.
      - exists (nu n); unfolder; splits; ins; eauto 6.
      - exfalso.
        assert (NIe' : ~ is_init e)
          by (intro; eapply (wf_co_init WF); unfolder; edone).
        desf.
        forward eapply IMPL with (i := n) (j := y) as Y;
          eauto using lt_n_Sm_le, le_lt_size;
          try lia.
        econs; unfolder; eauto.
    }
    eapply REL; ins.
    unfolder in Ee; unfolder; desc; split; ins.
    desf; vauto; right; exists y; split; ins.
      destruct (eqP y n); desf; lia.
    intro X; desc; unfolder in X; desc.
    destruct MAXe; exists e'; unfolder; splits; ins.
    clear X1; desf; eauto 6.
    clear X; desf; eauto 6.
  Qed.

  Lemma sc_step_all n (LT: lt_size n (acts G \₁ is_init))
        mem (REL: sc_rel (exec_enum G nu n) mem) :
    exists mem', SC_step mem (nu n) mem' /\
                 sc_rel (exec_enum G nu (S n)) mem'.
  Proof using WF ENUM IMPL COMPL.
    assert (X := ENUM); apply enumeratesE in X; desc.
    forward eapply (RNG n) as X; eauto using lt_lt_size.
    red in X; desc.
    destruct (nu n) as [|thread index []] eqn: N; ins.
    - forward eapply sc_step_read_value; eauto; rewrite N in *; ins.
      eexists; split; [eapply SCstep_read|eapply sc_step_non_write]; eauto.
      rewrite N; ins.
    - eexists; split; [eapply SCstep_write|eapply sc_step_write]; eauto.
      all: rewrite N; ins.
    - forward eapply sc_step_read_value; eauto; rewrite N in *; ins.
      eexists; split; [eapply SCstep_rmw|eapply sc_step_write]; eauto.
      all: rewrite N; ins.
  Qed.

End SC.

Lemma exec_enum_too_big G (WF: Wf G) nu
      (ENUM : enumerates nu (acts G \₁ is_init))
      n (LT: ~ lt_size n (acts G \₁ is_init)) :
  exec_enum G nu (S n) = exec_enum G nu n.
Proof using.
  cut ((acts G ∩₁ (is_init ∪₁ nu ↑₁ (fun x : nat => x < S n))) ≡₁
       (acts G ∩₁ (is_init ∪₁ nu ↑₁ (fun x : nat => x < n)))).
  { unfold exec_enum; ins; f_equal; ins.
    by extensionality x; apply propositional_extensionality;
      split; ins; apply H.
    all: apply rel_extensionality; try rewrite (wf_rfE WF);
      try rewrite (wf_coE WF).
    all: rewrite ?seqA, <- ?id_inter, H; seq_rewrite <- id_inter.
    all: by rewrite set_interC, H, set_interC, id_inter, seqA.
  }
  tertium_non_datur (set_finite (acts G \₁ is_init)) as [FIN|INF].
  2: by destruct LT; apply lt_size_infinite.
  unfolder; split; ins; desf; splits; eauto with arith.
  classical_right.
  red in FIN; desc.
  rewrite enumeratesE in *; desc.
  forward eapply (SUR (nu y)); ins; desf.
  rewrite lt_size_of_finite in *; eauto.
  exists i; split; eauto; lia.
Qed.

Fixpoint SC_mem_trace G 
         (WF : Wf G)
         nu (ENUM : enumerates nu (acts G \₁ is_init))
         (STEP: forall n (LT: lt_size n (acts G \₁ is_init))
                 mem (REL: sc_rel (exec_enum G nu n) mem),
               exists mem', SC_step mem (nu n) mem' /\
                            sc_rel (exec_enum G nu (S n)) mem')
         n :
  { mem : Memory | sc_rel (exec_enum G nu n) mem } :=
  match n with
  | 0 => exist _ Minit (@sc_rel_init G nu)
  | S n' => 
    match
      excluded_middle_informative (lt_size n' (acts G \₁ is_init)) with
    | left LT' =>
      let m := SC_mem_trace WF ENUM STEP n' in
      let t :=
          IndefiniteDescription.constructive_indefinite_description
            _ (STEP n' LT' (proj1_sig m) (proj2_sig m)) in
      exist _ (proj1_sig t) (proj2 (proj2_sig t))
    | right PF =>
      eq_rect _ (fun x => { mem | sc_rel x mem })
              (SC_mem_trace WF ENUM STEP n') _
              (eq_sym (exec_enum_too_big WF ENUM PF)) 
    end
  end.


Lemma le_diff x y (LE: x <= y): exists d, y = x + d.
Proof.
  generalize dependent y. 
  induction x.
  { ins. eauto. }
  ins. destruct y; [lia | ].
  specialize (IHx y). specialize_full IHx; [lia| ]. desc.
  exists d. lia.
Qed. 

Lemma lt_diff x y (LT: x < y): exists d, y = x + S d.
Proof.
  unfold lt in LT. apply le_diff in LT. desc.
  exists d. lia. 
Qed.

Lemma nth_map_seq {A: Type} (f: nat -> A) k d len (DOM: k < len):
  nth k (map f (List.seq 0 len)) d = f k.
Proof. 
  apply lt_diff in DOM. desc. rewrite DOM, seq_app, map_app, app_nth2.
  2: { by rewrite map_length, seq_length. }
  by rewrite map_length, seq_length, Nat.sub_diag, seqS_hd.
Qed. 

Lemma nth_error_map_seq {A: Type} (f: nat -> A) k len (DOM: k < len):
  nth_error (map f (List.seq 0 len)) k = Some (f k).
Proof. 
  apply lt_diff in DOM. desc. rewrite DOM, seq_app, map_app, nth_error_app2.
  2: { by rewrite map_length, seq_length. }
  by rewrite map_length, seq_length, Nat.sub_diag, seqS_hd.
Qed. 


Lemma findom_perm {A: Type} (S: A -> Prop) l1 l2 
      (DOM1: forall x, S x -> In x l1)
      (DOM2: forall x, S x -> In x l2):
  length (undup (filterP S l1)) = length (undup (filterP S l2)).
Proof.
  apply Permutation_length, NoDup_Permutation.
  1, 2: by apply nodup_undup.
  ins. 
  etransitivity; [rewrite in_undup_iff; apply in_filterP_iff| ].
  etransitivity; [| symmetry; rewrite in_undup_iff; apply in_filterP_iff].
  intuition. 
Qed. 

Lemma SC_decl_implies_op G
      (WF : Wf G) (FAIR: mem_fair G)
      (B: bounded_threads G) (RFC : rf_complete G)
      (CONS: sc_consistent G) :
  exists t,
    LTS_trace sc_lts t /\
    trace_elems t ≡₁ acts G \₁ is_init /\
    trace_wf t.
Proof using.
  forward eapply exec_exists_enum with (r := hb_sc G) as (nu & ENUM & ORD);
    eauto using fsupp_hb_sc, has_finite_antichains_sb with hahn.
  assert (X := sc_step_all WF ENUM ORD RFC).
  assert (exists tr, LTS_trace sc_lts tr /\
                trace_elems tr ≡₁ acts G \₁ is_init /\
                trace_nodup tr /\
                forall i d (DOM: NOmega.lt_nat_l i (trace_length tr)),
                  trace_nth i tr d = nu i). 
  { 
    tertium_non_datur (set_finite (acts G \₁ is_init)) as [FIN|INF].
    { red in FIN; desc.
      exists (trace_fin
           (map nu (List.seq 0 (length (undup (filterP (acts G \₁ is_init)
                                                       findom)))))).
      splits.
      4: { ins. rewrite map_length, seq_length in DOM. 
           rewrite nth_map_seq; auto. }
      3: { remember (length (undup (filterP (acts G \₁ is_init) findom))) as len.
           apply trace_nodup_list, NoDup_nth_error.
           ins.        
           apply enumeratesE' in ENUM. desc. specialize INJ with (i := i) (j := j).
           unfold set_size in INJ. destruct (excluded_middle_informative _).
           2: { exfalso. apply n. red. eauto. }
           destruct (constructive_indefinite_description _ _). desc. simpl in *.
           rewrite !findom_perm with (l2 := findom), <- !Heqlen in INJ; auto.
           rewrite !map_length, !seq_length in *.
           assert (j < len) as LTj.
           { destruct (Nat.lt_ge_cases j len); [auto| ].
             rewrite nth_error_map_seq in H0; auto.
          forward eapply (nth_error_None (map nu (List.seq 0 len))) as [_ foo]. 
          rewrite foo in H0; [inversion H0| ].
          rewrite map_length, seq_length. congruence. }
           apply INJ; try lia. rewrite !nth_error_map_seq in H0; auto. clarify. }
      2: {
        rewrite enumeratesE in ENUM; desc.
        split; red; ins; in_simp; [apply RNG | apply SUR in H; desf];
          rewrite lt_size_of_finite in *; eauto.
        eexists; split; ins; in_simp.
      }
      
      exists (fun n => proj1_sig (SC_mem_trace WF ENUM X n)).
      split; ins; desf.
      all: rewrite length_map, length_seq in *; ins.
      all: try solve [exfalso; rewrite lt_size_of_finite in *; eauto; lia].
      unfold proj1_sig; simpl; desf.
      clear Heq Heq0; desf.
      rewrite nth_indep with (d' := nu 0).
      rewrite map_nth, seq_nth; ins.
      rewrite length_map, length_seq; ins.
    }
    exists (trace_inf nu); splits; ins.
    3: { red. ins. apply enumeratesE' in ENUM. desc.
         unfold set_size in INJ. destruct (excluded_middle_informative _); [done| ].
         red. ins. apply INJ in H; auto. lia. }  
    exists (fun n => proj1_sig (SC_mem_trace WF ENUM X n)).
    split; ins; unfold proj1_sig; desf; desf.
    exfalso; eauto using lt_size_infinite.
  rewrite enumeratesE in ENUM; desc.
  split; red; ins; desf; eauto using lt_size_infinite.
  apply SUR in H; desf; eauto.
  }
  
  desc. exists tr. splits; auto.
  eapply trace_wf_helper; eauto.
  ins. apply ORD; auto.
  red. apply ct_step. basic_solver.
Qed.


Lemma lts_ninit t
      (TR : LTS_trace sc_lts t) x
      (IN : trace_elems t x)
      (INIT : is_init x) : False.
Proof using.
  destruct t; ins; desf.
    apply In_nth with (d := InitEvent 0) in IN; desf.
    eapply TR0 with (d := InitEvent 0) in IN; destruct IN; rewrite EQ in *; ins.
  destruct (TR0 n); rewrite EQ in *; ins.
Qed.  

Lemma lts_nodup t
      (TR: LTS_trace sc_lts t)
      (WF: trace_wf t) :
  trace_nodup t.
Proof using.
  unfold trace_wf; repeat red; ins.
  forward eapply WF with (d := d); eauto;
  rewrite H; ins; lia . 
Qed.

#[local]
Hint Immediate lts_nodup : core. 

Lemma fsupp_restr_eq_init s :
  fsupp (restr_eq_rel loc (is_init × s)).
Proof using.
  unfolder; ins; exists (InitEvent (loc y) :: nil).
  unfold loc; ins; desf; destruct x; ins; auto.
Qed.

#[local]
Hint Resolve fsupp_restr_eq_init : core.

Lemma SC_step_same_mem m l m' (STEP : SC_step m l m') x
  (NWL : forall (W : is_w l) (NLOC : loc l = x), False) :
  m' x = m x.
Proof using.  
  destruct STEP; unfold upd in *; desf; destruct NWL; ins.
Qed.

Lemma SC_step_wval m l m' (STEP : SC_step m l m') (W : is_w l) :
  valw l = m' (loc l).
Proof using.  
  destruct STEP; unfold upd in *; desf; destruct NWL; ins.
Qed.

Lemma SC_step_rval m l m' (STEP : SC_step m l m') (W : is_r l) :
  valr l = m (loc l).
Proof using.  
  destruct STEP; unfold upd in *; desf; destruct NWL; ins.
Qed.

Lemma SC_op_implies_decl t
      (TR: LTS_trace sc_lts t)
      (WF : trace_wf t)
      (TWF : trace_no_init_tid t) :
  exists G,
    trace_elems t ≡₁ acts G \₁ is_init /\
    Wf G /\ mem_fair G /\
    rf_complete G /\
    sc_consistent G.
Proof using.
  set (co := restr_eq_rel loc (is_init × (trace_elems t ∩₁ is_w) ∪
                               ⦗ is_w ⦘ ⨾ trace_order t ⨾ ⦗ is_w ⦘) ). 

  set (rf := restr_eq_rel loc (is_init × (trace_elems t ∩₁ is_r) ∪
                                     ⦗ is_w ⦘ ⨾ trace_order t ⨾ ⦗ is_r ⦘)
                                \ co ⨾ trace_order t).

  assert (TOT : forall x,
             is_total
               ((is_init ∪₁ trace_elems t)
                  ∩₁ is_w
                  ∩₁ (fun a => loc a = x)) co).
  {
    unfold co; unfolder; ins; desf.
    - unfold loc in *; destruct a, b; ins; desf.
    - right; splits; eauto.
    - left; splits; eauto.
    - eapply trace_order_total in NEQ; eauto using lts_nodup.
      desf; eauto 10.
  }

  assert (FUNRF : functional rf⁻¹).
  { subst rf co; unfolder in *; ins; desf.
    unfold loc in *; destruct y, z; ins; desf.
    destruct H1; exists y; splits; eauto with hahn; congruence.
    destruct H3; exists z; splits; eauto with hahn; congruence.
    apply NNPP; intro NEQ; eapply TOT with (x := loc x) in NEQ;
      desf; eauto 8 with hahn.
  }

  assert (FR_IN:  rf⁻¹ ⨾ co \ ⦗fun _ => True⦘ ⊆ trace_order t).
  {
    subst rf co; unfolder; ins; desf; clarify_not.
    all: eapply trace_order_total in H0; desf; eauto with hahn;
      destruct H3; exists y; splits; eauto.
  }
  

  exists {| acts := is_init ∪₁ trace_elems t ;
            rf := rf ; co := co |}; splits; ins.
  { unfolder; intuition; eauto using lts_ninit. }
  { split; ins; desf; subst rf co.

    all: try apply dom_helper_2.
    all: try solve [unfolder; ins; desf; splits;
                    eauto with hahn; destruct x; ins].

    { unfold same_index in *; unfolder in *; desf; destruct a, b; ins; desf.
      1,2: by apply TWF in H; desf.
      red in WF.
      apply trace_in_nth with (d := InitEvent 0) in H; destruct H as (n & LTn & En).
      apply trace_in_nth with (d := InitEvent 0) in H0; destruct H0 as (m & LTm & Em).
      destruct (lt_eq_lt_dec n m) as [[LT|]|LT]; desf;
        try apply WF with (d := InitEvent 0) in LT; eauto;
          rewrite Em, En in *; ins; lia. }

    {
      clear TOT FUNRF FR_IN.
      destruct (LTS_traceE _ _ TR) as (mem & INIT & STEP).
      unfolder in RF; desf.
      {
        eapply trace_in_nth with (d := InitEvent 0) in RF2; desf.
        cut (forall i (LTi: i <= n),
                mem i (loc (trace_nth n t (InitEvent 0))) = 0).
        {
          erewrite SC_step_rval; try apply STEP; ins.
          destruct w; ins; rewrite H; ins.
        }
        induction i; ins; [rewrite <- INIT; ins|].
        rewrite Nat.le_succ_l in *.

        ins; erewrite SC_step_same_mem; try apply STEP; 
          eauto with hahn arith.
        instantiate (1 := InitEvent 0); ins.
        apply RF0.
        eexists (trace_nth i t (InitEvent 0)).
        rewrite trace_order_nth_nth; splits; ins;
          eauto 8 with hahn; try congruence.
      }
      {
        red in RF2; desf.
        cut (forall k (GTi : i < k) (LTi: k <= j),
                mem k (loc (trace_nth j t w)) = valw w).
        {
          erewrite SC_step_rval; try apply STEP; ins.
          destruct w; ins; rewrite H; ins; lia.
        }
        ins.
        induction k; ins; try lia.
        rewrite Nat.lt_succ_r, Nat.le_succ_l, Nat.le_lteq in *; desf.
        2: {
          rewrite <- RF1, <- RF6; symmetry; eapply SC_step_wval;
            eauto with hahn; congruence.
        }
        ins; erewrite SC_step_same_mem; try apply STEP; 
          eauto with hahn arith.
        instantiate (1 := w); ins.
        apply RF0.
        eexists (trace_nth k t w).
        rewrite trace_order_nth_nth; splits; ins;
          eauto with hahn; try congruence.
        right; splits; ins.
        rewrite <- RF6 at 1; rewrite trace_order_nth_nth; ins;
          eauto using NOmega.lt_lt_nat.
      }
    }
    { unfolder; ins; desf; splits;
        eauto using trace_order_trans with hahn; try congruence.
      exfalso; eauto using lts_ninit with hahn. }
    { unfolder; ins; desf; eauto using lts_ninit.
      eapply trace_order_irrefl in H0; ins. }
    { unfolder; split; ins; desf; eauto using lts_ninit with hahn. }
    unfold is_init. desf. ins. split; ins; desf.
    unfolder in ACT. desf. apply TWF in ACT. desf. }
  {
    red; ins; unfold fr; ins; rewrite FR_IN; unfold co. 
    rewrite !restr_eq_union; splits;
      repeat eapply fsupp_union; eauto with hahn.
  }
  {
    subst rf co; red; ins; unfolder.
    ins; desf.
    destruct x; ins.
    apply trace_in_nth with (d := InitEvent 0) in H; desf.
    forward apply exists_max with
        (cond := fun m => is_w (trace_nth m t (InitEvent 0)) /\
                 loc (trace_nth m t (InitEvent 0)) =
                 loc (trace_nth n t (InitEvent 0))) (n := n)
      as [X|X]; desc.
    - exists (InitEvent (loc (trace_nth n t (InitEvent 0))));
        splits; ins; eauto with hahn.
      unfold loc; intro Y; desf; ins.
        apply trace_in_nth with (d := InitEvent 0) in Y2; ins; desf.
        rewrite trace_order_nth_nth in *; desf; eapply X; eauto.
      eapply trace_order_in1, lts_ninit in Y2; ins.
    - exists (trace_nth m t (InitEvent 0)); splits; ins.
      rewrite trace_order_nth_nth; eauto with hahn.
      unfold loc; intro Y; desf; ins.
        eapply lts_ninit; try apply Y; eauto with hahn.
      assert (Z: trace_elems t z) by eauto with hahn.
      apply trace_in_nth with (d := InitEvent 0) in Z; desf.
      rewrite trace_order_nth_nth in *; desf; eauto with hahn.
      unfold loc in *; eapply (X1 n0); splits; ins; congruence.
  }
  {
    red; arewrite (hb_sc {| acts := is_init ∪₁ trace_elems t;
                       rf := rf; co := co |} ⊆
                    is_init × trace_elems t ∪ trace_order t).
    2: {
        unfolder; ins; desf; eauto using lts_ninit, trace_order_irrefl.
    }
    apply inclusion_t_ind; ins.
    2: {
      unfolder; ins; desf; eauto using trace_order_trans with hahn.
      exfalso; eauto using lts_ninit with hahn.
    }
    rewrite FR_IN.
    unfold sb, ext_sb; ins; unfold rf, co; unfolder;
      ins; desf; ins; desf; auto.
    right; split; eauto.
    apply trace_in_nth with (d := ThreadEvent thread0 index l) in H; desc.
    apply trace_in_nth with (d := ThreadEvent thread0 index l) in H1; desc.
    exists n, n0; splits; ins.
    destruct (lt_eq_lt_dec n n0) as [[]|LT]; desf.
    1: rewrite H0 in H3; desf; lia.
    red in WF; forward eapply WF with (d := ThreadEvent thread0 index l);
      try apply LT; try rewrite H0, H3; ins; lia.
  }
Qed.
