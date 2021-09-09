Require Import Lia IndefiniteDescription Arith.
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Labels.
Require Import Events.
Require Import Execution.
Require Import View.

Set Implicit Arguments.

Record Message :=
  Msg {
      mloc : Loc ;
      mval : Val ;
      mts  : Timestamp ;
      mview : View }.

Definition Memory := (Message -> Prop).
Definition State := (Memory * (Tid -> View))%type.

Definition Minit : Memory :=
  fun m => mval m = 0 /\ mts m = 0 /\
           mview m = fun _ => 0.

Definition Vinit : View := fun x => 0.
Definition Sinit : State := (Minit, fun tid => Vinit).

Inductive SCOH_label :=
  | SCOH_event (e : Event) (tstamp : Timestamp) (view : View)
  | SCOH_internal (t : Tid) (x : Loc) (tstamp : Timestamp).

Definition deflabel : SCOH_label := SCOH_internal 0 0 0.

Definition read_ts x :=
  match x with
  | SCOH_event _ ts _ => ts
  | SCOH_internal _ _ _ => 0
  end.

Definition write_ts x :=
  match x with
  | SCOH_event _ ts _ => S ts
  | SCOH_internal _ _ _ => 0
  end.

Definition tid_of x :=
  match x with
  | SCOH_event e _ _ => tid e
  | SCOH_internal tid x _ => tid
  end.

Definition is_external x :=
  match x with
  | SCOH_event (ThreadEvent _ _ _) _ _ => True
  | _ => False
  end.

Definition proj_ev x :=
  match x with
  | SCOH_event e _ _ => e
  | SCOH_internal _ _ _ => InitEvent 0
  end.

Definition trproj t :=
  trace_map proj_ev (trace_filter is_external t).

Definition fresh_tstamp (m : Memory) x ts :=
  ~ exists v view, m (Msg x v ts view).

Inductive SCOH_step (MV : State) (e: SCOH_label) (MV' : State) : Prop :=
| SCOHstep_read t i x v tstamp view view'
              (EQ: e = SCOH_event (ThreadEvent t i (Aload x v)) tstamp view')
	      (MSG: fst MV (Msg x v tstamp view))
              (LEV: snd MV t x <= tstamp)
              (MEM: fst MV' = fst MV)
              (EQ': view' = upd (snd MV t) x tstamp)
	      (VIEW: snd MV' = upd (snd MV) t view')
| SCOHstep_write t i x v tstamp view'
               (EQ: e = SCOH_event (ThreadEvent t i (Astore x v)) tstamp view')
               (EQ': view' = upd (snd MV t) x (S tstamp))
               (LTV: snd MV t x < S tstamp)
               (MEM: fst MV' = fst MV ∪₁ eq (Msg x v (S tstamp) view'))
               (FRESH: fresh_tstamp (fst MV) x (S tstamp))
	       (VIEW: snd MV' = upd (snd MV) t view')
| SCOHstep_rmw t i x vr vw tstamp view view'
             (EQ: e = SCOH_event (ThreadEvent t i (Armw x vr vw)) tstamp view')
	     (MSG: fst MV (Msg x vr tstamp view))
             (LEV: snd MV t x <= tstamp)
             (EQ' : view' = upd (snd MV t) x (S tstamp))
             (MEM: fst MV' = fst MV ∪₁ eq (Msg x vw (S tstamp) view'))
             (FRESH: fresh_tstamp (fst MV) x (S tstamp))
             (VIEW: snd MV' = upd (snd MV) t view')
| SCOHstep_internal t x v tstamp view view'
                  (EQ: e = SCOH_internal t x tstamp)
		  (MSG: fst MV (Msg x v tstamp view))
                  (LEV: snd MV t x < tstamp)
                  (MEM: fst MV' = fst MV)
                  (EQ': view' = upd (snd MV t) x tstamp)
		  (VIEW: snd MV' = upd (snd MV) t view').

Definition scoh_lts :=
  {| LTS_init := eq Sinit ;
     LTS_step := SCOH_step ;
     LTS_final := ∅ |}.

Definition run_fair (states : nat -> State) t : Prop :=
  match t with
  | trace_fin _ => True
  | trace_inf fl =>
    exists (threads : Tid -> Prop),
    set_finite threads /\
    trace_elems t ⊆₁ tid_of ↓₁ threads /\
    forall i (tid : Tid) (TID: threads tid) x tstamp,
    exists j,
      i <= j /\
      (fl j = SCOH_internal tid x tstamp \/
       forall st'
              (STEP: SCOH_step (states j) (SCOH_internal tid x tstamp) st'),
         False)
  end.

Definition SCOH_is_w lab :=
  match lab with
  | SCOH_event (ThreadEvent _ _ (Astore _ _)) ts view => True
  | SCOH_event (ThreadEvent _ _ (Armw _ _ _)) ts view => True
  | _ => False
  end.

Definition SCOH_wmsg lab :=
  match lab with
  | SCOH_event (ThreadEvent t i (Astore x v)) ts view => Msg x v (S ts) view
  | SCOH_event (ThreadEvent t i (Armw x vr vw)) ts view => Msg x vw (S ts) view
  | _ => Msg 0 0 0 (fun _ => 0)
  end.

Definition view_of x :=
  match x with
  | SCOH_event _ _ view => view
  | SCOH_internal _ _ _ => fun _ => 0
  end.

Inductive match_ev (e : Event) (l : SCOH_label) : Prop :=
| ME_case t i lab tstamp view (EQe : e = ThreadEvent t i lab)
          (EQl : l = SCOH_event e tstamp view).

Definition view_of' t x :=
  match excluded_middle_informative
          (exists xl, match_ev x xl /\ trace_elems t xl) with
  | left IN =>
    view_of (proj1_sig
               (IndefiniteDescription.constructive_indefinite_description
                  _ IN))
  | right _ => fun _ => 0
  end.

Lemma view_of_init t x :
  view_of' t (InitEvent x) = fun _ => 0.
Proof using.
  unfold view_of'; desf.
  exfalso; desf; destruct e; desf.
Qed.

Lemma SCOH_step_view_mono mem lab mem'
      (STEP : SCOH_step mem lab mem') t :
  view_le (snd mem t) (snd mem' t).
Proof using.
  destruct STEP; ins; desf; ins.
  all: rewrite VIEW; clear VIEW; unfold upd; desf.
  all: try apply view_le_join_l.
  all: red; unfold upd; ins; desf; lia.
Qed.

Lemma SCOH_step_view_ext mem lab mem'
      (STEP : SCOH_step mem lab mem')
      (EXT : is_external lab) :
  view_le (snd mem (tid_of lab))
          (view_of lab) /\
  view_of lab = snd mem' (tid_of lab).
Proof using.
  destruct STEP; ins; desf; ins.
  all: rewrite VIEW, upds; split; ins.
  all: try apply view_le_join_l.
  all: red; unfold upd; ins; desf; lia.
Qed.

Lemma SCOH_view_mono mem lab
      (STEP : forall i, SCOH_step (mem i) (lab i) (mem (S i)))
      i j (LE : i <= j) mytid x :
  snd (mem i) mytid x <= snd (mem j) mytid x.
Proof using.
  induction j; rewrite Nat.le_lteq in LE; desf; try lia.
  rewrite Nat.lt_succ_r in *; intuition.
  eapply Nat.le_trans, SCOH_step_view_mono; eauto.
Qed.

Section RADeclarative.

Variable G: execution. 

Definition scoh_consistent :=
  SCpL G  /\
  irreflexive ((rf G)⁻¹ ⨾ (co G ⨾ (co G))) /\
  << PORF : irreflexive (hb G) >>.

Lemma hb_irr (CONS : scoh_consistent) : irreflexive (hb G).
Proof using. apply CONS. Qed.

Lemma scoh_rmw_atomicity (WF: Wf G) (CONS : scoh_consistent) :
  rmw_atomicity G.
Proof using.
  unfold scoh_consistent, rmw_atomicity in *; desc.
  rewrite wf_rfE, wf_rfD; ins; unfolder in *; ins; desf.
  destruct (classic (x = y)) as [|NEQ]; desf.
  { edestruct (CONS y). apply ct_step.
    basic_solver. }
  eapply (wf_co_total WF) in NEQ; ins; desf; ins.    
  { splits; ins; intro; desf; eauto 10. }
  { edestruct (CONS x). apply ct_ct.
    exists y; split; apply t_step; basic_solver. }
  unfolder. splits; auto.
  apply wf_rfl in H0; ins.
Qed.
 
Lemma scoh_rf_irr (CONS : scoh_consistent) : irreflexive (rf G).
Proof using. rewrite rf_in_hb. by apply hb_irr. Qed.

Lemma rf_w_in_co (WF: Wf G) (CONS : scoh_consistent) :
  (rf G) ⨾ ⦗is_w⦘ ⊆ (co G).
Proof using.
  unfolder. intros x y [RF WY].
  destruct (classic (x = y)) as [|NEQ]; subst.
  { exfalso. eapply scoh_rf_irr; eauto. }
  apply (wf_rfE WF) in RF. unfolder in RF. desf.
  apply (wf_rfD WF) in RF0. unfolder in RF0. desf.
  edestruct (wf_co_total WF) with (a:=x) (b:=y) as [|HH]; eauto.
  1,2: unfolder; splits; eauto.
  { symmetry. by apply (wf_rfl WF). }
  exfalso.
  cdes CONS. eapply CONS0.
  apply ct_ct. eexists. split; apply ct_step.
  all: basic_solver.
Qed.

(* TODO: move to more appropriate place or replace with co_ninit. *)
Lemma co_init_r (WF: Wf G)
      x y (CO : co G x y) (INITY : is_init y) :
  False.
Proof.
  apply co_ninit in CO; auto. unfolder in CO. desf.
Qed.

End RADeclarative.
