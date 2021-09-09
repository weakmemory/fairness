From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import AuxProp.
Require Import SC.
Require Import tso.TSO.
Require Import tso.TSO_decl_op.
Require Import tso.TSO_op_decl.
Require Import ra.RAop.
Require Import ra.RAopToDecl.
Require Import ra.RAdeclToOp.
Require Import strong_coh.SCOHop.
Require Import strong_coh.SCOHopToDecl.
Require Import strong_coh.SCOHdeclToOp.
Require Import TraceWf.
Require Import Lia.
Require Import Arith.
Require Import AltDefs.

Section DefEquivalence.
(****** This section provides a uniform way to state the equivalence of a
        memory model's operational and declarative definitions equivalence. ***)

(* Operational model is specified by its labeled transition system. *)
(* Note that the formalization of a 'run' is not a sequence of state pairs 
   but is rather just a sequence of states. *)
Variable State Label: Type. 
Variable lts: LTS State Label.

(* We formalize operational behavior as set of events contained in a trace. 
   The exact way of extracting events from a trace is model-specific. *)
Variable trace_events: trace Label -> (Event -> Prop).
(* In order to correctly represent behavior as events set we require that 
   events appear in a trace according to their indices. 
   This requirement is also model-specific. *)
Variable trace_well_formed: trace Label -> Prop.

(* A model-specific operational fairness condition. 
   It places requirements not only on labels, but also on states of a run. *)
Variable run_fair: trace Label -> (nat -> State) -> Prop.

(* A declarative model is specified by its consistency predicate. *)
Variable consistent: execution -> Prop.

(* The equivalence definition relating operational and declarative executions 
   via 'behavior' events set. *)
Definition op_decl_def_equiv :=
  forall (behavior: Event -> Prop)
    (* There are finite amount of threads: *)
    (BOUNDED_THREADS: exists n, forall e, behavior e -> tid e < n)
    (* Technical restriction on event's thread ID: *)
    (NO_TID0: forall e, behavior e -> tid e <> 0),
    (exists (trace: trace Label) (states: nat -> State),
        LTS_trace_param lts states trace /\
        trace_well_formed trace /\
        run_fair trace states /\
        trace_events trace ≡₁ behavior)
    <->
    (exists G,
        Wf G /\
        mem_fair G /\
        rf_complete G /\
        consistent G /\
        acts G \₁ is_init ≡₁ behavior).

End DefEquivalence.


Theorem SC_equiv:
  op_decl_def_equiv SC.Memory Event sc_lts 
                    (@trace_elems Event)
                    trace_wf
                    (fun _ _ => True)
                    sc_consistent.
Proof.
  red. ins. split.
  { ins. desc.
    forward eapply SC_op_implies_decl; eauto.
    { destruct trace; simpl in *; eauto. }
    { red. ins. by apply NO_TID0, H2. }
    ins. desc. exists G. splits; vauto.
    by rewrite <- H3. }
  { ins. desc. forward eapply SC_decl_implies_op; eauto.
    { red. exists (S n). ins. destruct x; [simpl; lia| ].
      etransitivity; [| apply Nat.lt_succ_diag_r]. 
      apply BOUNDED_THREADS, H3. split; vauto. }
    ins. desc. exists t. red in H4. destruct t; desc; exists fl'; splits; simpl in *; vauto.
    { rewrite <- H3. auto. }
    { rewrite H5. auto. }
  } 
Qed.


Theorem TSO_equiv:
  op_decl_def_equiv TSOMemory TSO_label TSO_lts 
                    (fun tr => fun e => trace_elems tr (inl e))
                    TSO_trace_wf
                    TSO_fair
                    TSO_consistent.
Proof.
  red. ins. 
  split.
  { ins. desc.    
    forward eapply (TSO_op_implies_decl H H0 H1); eauto.
    { unfold Eninit. ins. by apply NO_TID0, H2. }
    ins. desc. eexists. splits; eauto.
    simpl. symmetry in H3. eapply set_equiv_rel_Transitive; eauto. }
  { ins. desc. forward eapply TSO_decl_implies_op; eauto.
    { exists n. ins. by apply BOUNDED_THREADS, H3. }
    ins. desc. do 2 eexists. splits; eauto.
    eapply set_equiv_rel_Transitive; eauto. }
Qed.

Theorem RA_equiv:
  op_decl_def_equiv RAop.State RA_label ra_lts 
                    (fun tr => trace_elems (RAop.trproj tr))
                    (fun tr => trace_wf (RAop.trproj tr))                    
                    (fun tr st => RAop.run_fair st tr)
                    ra_consistent_alt.
Proof.
  red. ins. 
  split.
  { ins. desc.    
    forward eapply RA_op_implies_decl; eauto.
    { red. ins. apply NO_TID0. by apply H2. }
    ins. desc. exists G. splits; vauto.
    { by apply ra_consistent_defs_equivalence. }
    by rewrite <- H3. }
  { ins. desc.
    apply ra_consistent_defs_equivalence in H2; auto. 
    forward eapply RA_decl_implies_op; eauto.
    { red. exists (List.seq 0 (S n)). ins. apply in_seq0_iff.
      desc. subst. destruct x0; [simpl; lia| ].
      etransitivity; [| apply NPeano.Nat.lt_succ_diag_r]. 
      apply BOUNDED_THREADS. apply H3. vauto. }
    ins. desc. exists t. exists s. splits; vauto. by rewrite H6. }
Qed.

Theorem SCOH_equiv:
  op_decl_def_equiv SCOHop.State SCOH_label scoh_lts 
                    (fun tr => trace_elems (SCOHop.trproj tr))
                    (fun tr => trace_wf (SCOHop.trproj tr))                    
                    (fun tr st => SCOHop.run_fair st tr)
                    scoh_consistent_alt. 
Proof.
  red. ins. 
  split.
  { ins. desc.
    forward eapply SCOH_op_implies_decl; eauto.
    { red. ins. apply NO_TID0. by apply H2. }
    ins. desc. exists G. splits; vauto.
    { by apply scoh_consistent_defs_equiv. }
    by rewrite <- H3. }
  { ins. desc.
    apply scoh_consistent_defs_equiv in H2; auto. 
    forward eapply SCOH_decl_implies_op; eauto.
    { red. exists (List.seq 0 (S n)). ins. apply in_seq0_iff.
      desc. subst. destruct x0; [simpl; lia| ].
      etransitivity; [| apply NPeano.Nat.lt_succ_diag_r]. 
      apply BOUNDED_THREADS. apply H3. vauto. }
    ins. desc. exists t. exists s. splits; vauto. by rewrite H6. }
Qed.

Redirect "axioms_sc" Print Assumptions SC_equiv.
Redirect "axioms_tso" Print Assumptions TSO_equiv.
Redirect "axioms_ra" Print Assumptions RA_equiv.
Redirect "axioms_scoh" Print Assumptions SCOH_equiv. 


