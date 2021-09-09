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
Require Import ChoiceFacts.
Require Import FinFun.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Backport.
Require Import SetSize.
Require Import ListSum.
Require Import AuxProp.
Require Import SC.
Require Import TSO.
Require Import RAop.
Require Import SCOHop.
Require Import ModelsRelationships.

Set Implicit Arguments.

Notation "'E' G" := (acts G) (at level 1).

Definition prefix_closed {A: Type} (r: relation A) (S: A -> Prop) :=
  dom_rel (r ⨾ ⦗S⦘) ⊆₁ S.

Lemma prefix_closed_incl {A: Type} (r1 r2: relation A) (S: A -> Prop)
      (INCL: r1 ⊆ r2)
      (CLOS2: prefix_closed r2 S):
  prefix_closed r1 S.
Proof. unfold prefix_closed in *. by rewrite INCL. Qed. 

Definition porf_prefix (G' G: execution) :=
  ⟪EV_PREF: prefix_closed (sb G ∪ rf G) (E G') ⟫ /\
  ⟪RF_PREF: rf G' ≡ restr_rel (E G') (rf G) ⟫ /\
  ⟪MO_PREF: co G' ≡ restr_rel (E G') (co G) ⟫.


Definition sbn (G: execution) := ⦗set_compl is_init⦘ ⨾ sb G.

Lemma Wf_subset_closed G S (WF: Wf G) (SUB: S ⊆₁ E G) (S_INIT: is_init ⊆₁ S):
  Wf {| acts := S; rf := restr_rel S (rf G); co := restr_rel S (co G) |}.
Proof.
  split; simpl. 
  { ins. desc. eapply wf_index; splits; eauto. }
  { rewrite <- restr_relE. basic_solver. }
  { rewrite wf_rfD; auto. basic_solver. }
  { etransitivity; [| apply wf_rfl]; basic_solver. }
  { ins. eapply wf_rfv; eauto. red in RF. by desc. }
  { eapply functional_mori; [red| apply wf_rff]; basic_solver. }
  { rewrite <- restr_relE. basic_solver. }
  { rewrite wf_coD; auto. basic_solver. }
  { etransitivity; [| apply wf_col]; basic_solver. }
  { generalize (co_trans WF). basic_solver. }
  { ins.
    red. ins. 
    forward eapply (@wf_co_total _ WF x) with (a := a) (b := b); auto. 
    1, 2: unfolder in *; desc; basic_solver.
    unfolder in *. ins. des; [left | right]; splits; vauto. }
  { eapply irreflexive_inclusion; [| apply co_irr]; basic_solver. }
  { auto. }
  { split; [| basic_solver]. etransitivity; [| apply wf_co_init]; basic_solver. }
  { ins. eapply wf_tid_init; basic_solver. }
Qed.     

Lemma porf_prefix_sb G G' (PREF: porf_prefix G' G) (INCL: E G' ⊆₁ E G):  
  sb G' ≡ restr_rel (E G') (sb G).
Proof. 
  unfold sb. rewrite <- !restr_relE, restr_restr.
  arewrite (E G' ≡₁ E G ∩₁ E G'); basic_solver. 
Qed. 
  
Lemma porf_prefix_fr G G' (WF: Wf G) (PREF: porf_prefix G' G)
      (INCL: E G' ⊆₁ E G):  
  restr_rel (E G') (fr G) ⊆ fr G'. 
Proof.
  unfold fr. simpl. red. ins. red in H. desc. do 2 (red in H; desc). 
  red. split; auto. red.
  red in PREF. desc. 
  assert (E G' z).
  { red in H. do 2 red in EV_PREF.
    specialize (EV_PREF z). specialize_full EV_PREF; auto.
    red. exists x. basic_solver. } 
  exists z. split.
  - red. apply RF_PREF. basic_solver.
  - apply MO_PREF. basic_solver.
Qed.   

Lemma porf_prefix_fr' G G' (PREF: porf_prefix G' G):
  fr G' ⊆ fr G.
Proof.
  cdes PREF. unfold fr. rewrite RF_PREF, MO_PREF. basic_solver.
Qed. 

Lemma sc_compactness G (BT: bounded_threads G) (WF: Wf G) (FPREF: fsupp (sbn G ∪ rf G)⁺)
      (FIN_CONS: forall G' (WF: Wf G') (SUB: E G' ⊆₁ E G) (FIN: set_finite (E G' \₁ is_init))
                   (PREF: porf_prefix G' G),
          sc_consistent G'):
  sc_consistent G.
Proof.
  red. red. intros e CYCLE.
  cdes CYCLE. unfold hb_sc in CYCLE0.
  apply ctEE in CYCLE0. destruct CYCLE0 as (n & _ & CYCLE0). 
  apply pow_rel_explicit in CYCLE0. desc.
  set (EG' := acts G ∩₁ (⋃₁ e' ∈ (fun e' => In e' l), fun e => (sbn G ∪ rf G)^* e e') ∪₁ is_init).
  set (G' := {| acts := EG'; rf := restr_rel EG' (rf G); co := restr_rel EG' (co G) |}).
  assert (porf_prefix G' G) as PREF.
  { red. splits; try basic_solver.
    red. red. ins. red. red in H. desc. apply seq_eqv_r in H. desc.
    eapply same_relation_exp in H.
    2: { rewrite wf_sbE, wf_rfE, <- !restr_relE, <- restr_union; eauto. }
    red in H. desc.
    destruct (classic (is_init x)); [basic_solver| ].
    left. split; auto.
    eapply same_relation_exp in H. 
    2: { rewrite no_rf_to_init, <- sb_ninit; auto. }
    do 2 red in H0. des.
    2: { unfolder in H. basic_solver. }
    red in H0. desc. red in H4. desc. 
    exists y0. split; auto. eapply transitive_rt; eauto. apply rt_step.
    unfold sbn. unfolder in H. basic_solver. }
  assert (EG' ⊆₁ E G) as E_INCL. 
  { apply set_subset_union_l. split; [basic_solver| by apply wf_initE]. } specialize (FIN_CONS G'). specialize_full FIN_CONS; auto.
  { unfold G'. apply Wf_subset_closed; auto.
    unfold EG'. basic_solver. }
  { simpl. subst EG'. eapply set_finite_mori.
    { red. rewrite set_minus_union_l, set_minusK, set_union_empty_r. 
      rewrite set_minus_subset, set_interC. apply set_inter_subset. }
    apply set_finite_bunion; [by vauto| ].
    ins. specialize (FPREF a). desc.
    exists (a :: findom). ins. apply clos_refl_transE in IN. des; [by vauto| ].
    right. by apply FPREF. }

  do 2 red in FIN_CONS. apply (FIN_CONS e). red.
  apply ctEE. exists n. split; auto. apply pow_rel_explicit. exists l. splits; auto.
  intros i DOMi. specialize (CYCLE2 i). specialize_full CYCLE2; auto. desc.
  exists a, b. splits; auto.
  eapply hahn_inclusion_exp.
  { simpl.
    enough (restr_rel EG' (fr G) ⊆ fr G').
    { rewrite <- H, (@porf_prefix_sb G G'); auto. simpl. 
      rewrite <- !restr_union. apply inclusion_refl. }
    arewrite (EG' ≡₁ E G'). eapply porf_prefix_fr; auto. }
  red. eapply same_relation_exp in CYCLE4.
  2: { rewrite wf_sbE, wf_rfE, wf_coE, wf_frE; try by apply WF.
       rewrite <- !restr_relE, <- !restr_union. auto. }
  red in CYCLE4. desc. 
  splits; auto; red; left; split; auto.
  1: exists a. 2: exists b. 
  all: split;[eapply nth_error_In; eauto| apply rt_refl].
Qed. 


Definition finitely_robust (B: (Event -> Prop) -> Prop) (M: execution -> Prop) :=
  forall (beh: Event -> Prop) (G: execution)
    (BT: bounded_threads G)
    (WF: Wf G)
    (FIN: set_finite beh)
    (BEH: B beh)
    (* (BEH_PREF_CLOS: forall G G' (WFG: Wf G) (WFG': Wf G') (B_G: B (E G \₁ is_init)) *)
    (BEH_PREF_CLOS: forall G G' (B_G: B (E G \₁ is_init))
                      (SUB: E G' ⊆₁ E G)
                      (SB_PREF: prefix_closed (sb G) (E G')),
        B (E G' \₁ is_init))
    (CONS: M G)
    (G_beh: E G \₁ is_init ≡₁ beh),
    sc_consistent G. 

Definition strongly_robust (B: (Event -> Prop) -> Prop) (M: execution -> Prop) :=
  forall (beh: Event -> Prop) (G: execution)
    (BT: bounded_threads G)
    (WF: Wf G)
    (BEH: B beh)
    (* (BEH_PREF_CLOS: forall G G' (WFG: Wf G) (WFG': Wf G') (B_G: B (E G \₁ is_init)) *)
    (BEH_PREF_CLOS: forall G G' (B_G: B (E G \₁ is_init))
                      (SUB: E G' ⊆₁ E G)
                      (SB_PREF: prefix_closed (sb G) (E G')),
        B (E G' \₁ is_init))
    (CONS: M G)
    (G_beh: E G \₁ is_init ≡₁ beh),
    sc_consistent G.

Lemma porf_bt G G' (PREF: porf_prefix G' G) (BT: bounded_threads G)
      (INCL: E G' ⊆₁ E G):
  bounded_threads G'.
Proof.
  unfold bounded_threads in *. desc. exists n.
  ins. apply BT. basic_solver.
Qed. 

Theorem finitely2strongly (M: execution -> Prop)
        (M_PORF_CLOS: forall G G' (CONS: M G) (SUB: E G' ⊆₁ E G)
                        (PREF: porf_prefix G' G), M G')
        (M_PREF: forall G (CONS: M G) (WF: Wf G) (BT: bounded_threads G),
            fsupp (sbn G ∪ rf G)⁺):
  forall (B: (Event -> Prop) -> Prop) (FIN_ROBUST: finitely_robust B M),
    strongly_robust B M.
Proof.
  ins. red. ins.
  red in FIN_ROBUST.
  apply sc_compactness; auto. 
  ins.
  
  apply FIN_ROBUST with (beh := acts G' \₁ is_init); auto.
  { eapply porf_bt; by vauto. }
  2: { eapply M_PORF_CLOS; eauto. }

  eapply BEH_PREF_CLOS with (G := G); auto. 
  { replace (E G \₁ is_init) with beh; auto. 
    apply set_extensionality. by rewrite G_beh. }
  cdes PREF. eapply prefix_closed_incl; eauto. basic_solver.
Qed. 

Lemma porf_prefix_fair G G' (PREF: porf_prefix G' G) (INCL: E G' ⊆₁ E G)
  (FAIR: mem_fair G):
  mem_fair G'. 
Proof.
  unfold mem_fair in *. cdes PREF.
  rewrite MO_PREF, porf_prefix_fr'; try by vauto.
  split; eapply fsupp_mon.
  2: by apply FAIR. 3: by apply FAIR0. 
  all: basic_solver.  
Qed.

Theorem program_robustness (B: (Event -> Prop) -> Prop) (M: execution -> Prop)
        (FIN_ROBUST: finitely_robust B M)
        (BEH_PREF_CLOS: forall G G' (B_G: B (E G \₁ is_init))
                          (SUB: E G' ⊆₁ E G)
                          (SB_PREF: prefix_closed (sb G) (E G')),
            B (E G' \₁ is_init))
        (SC_M: sc_consistent ∩₁ Wf ∩₁ mem_fair ⊆₁ M)
        (M_PORF_CLOS: forall G G' (CONS: M G) (SUB: E G' ⊆₁ E G)
                        (PREF: porf_prefix G' G), M G')
        (M_PREF: forall G (WF: Wf G) (CONS: M G) (BT: bounded_threads G)
          (FAIR: mem_fair G),
            fsupp (sbn G ∪ rf G)⁺):
  B ∩₁ (fun beh => exists G, Wf G /\ mem_fair G /\ M G /\ bounded_threads G /\ E G \₁ is_init ≡₁ beh) ≡₁
  B ∩₁ (fun beh => exists G, Wf G /\ mem_fair G /\ sc_consistent G /\ bounded_threads G /\ E G \₁ is_init ≡₁ beh).
Proof. 
  split. 
  2: { apply set_subset_inter; [basic_solver| ].
       red. ins. desc. exists G. splits; auto.
       by apply SC_M. }
  red. intros beh [Bbeh (G & WF & FAIR & MG & BT & G_BEH)].
  split; auto.
  assert (sc_consistent G) as SC_G; eauto. 
  { forward eapply finitely2strongly with (M := M ∩₁ mem_fair) (B := B); eauto.
    - ins. red in CONS. desc. split; [| eapply porf_prefix_fair; try by vauto].
      eapply M_PORF_CLOS; eauto.
    - ins. red in CONS. desc. eapply M_PREF; eauto.
    - red. ins. red in CONS. desc. eapply FIN_ROBUST; eauto.
    - ins. eapply H; eauto. vauto. }
  eexists. splits; eauto. 
Qed.

Lemma porf_prefix_rfe G G' (PREF: porf_prefix G' G) (INCL: E G' ⊆₁ E G):  
  rfe G' ≡ restr_rel (E G') (rfe G).
Proof.
  cdes PREF. unfold rfe. rewrite RF_PREF, porf_prefix_sb; try by vauto.
  by rewrite <- restr_minus. 
Qed.

  
Theorem program_robustness_models (B: (Event -> Prop) -> Prop) (M: execution -> Prop)
        (FIN_ROBUST: finitely_robust B M)
        (BEH_PREF_CLOS: forall G G' (B_G: B (E G \₁ is_init))
                          (SUB: E G' ⊆₁ E G)
                          (SB_PREF: prefix_closed (sb G) (E G')),
            B (E G' \₁ is_init))
        (MODELS: In M [sc_consistent; ra_consistent;
                      TSO_consistent; scoh_consistent]):
  B ∩₁ (fun beh => exists G, Wf G /\ mem_fair G /\ M G /\ bounded_threads G /\ E G \₁ is_init ≡₁ beh)
    ≡₁
  B ∩₁ (fun beh => exists G, Wf G /\ mem_fair G /\ sc_consistent G /\ bounded_threads G /\ E G \₁ is_init ≡₁ beh).
Proof. 
  apply program_robustness; auto.
  { simpl in MODELS. des; (try by done); subst M.
    - basic_solver. 
    - red. ins. unfolder in H. desc. apply tso_implies_ra, sc_implies_tso; auto.
    - red. ins. unfolder in H. desc. apply sc_implies_tso; auto.
    - red. ins. unfolder in H. desc. apply sc_implies_scoh; auto. }
  { ins. des; try done; subst M. 
    - unfold sc_consistent in *. arewrite (hb_sc G' ⊆ (hb_sc G)); auto.
      unfold hb_sc. apply clos_trans_mori. 
      red in PREF. desc. rewrite RF_PREF, MO_PREF, (@porf_prefix_sb G G'), (@porf_prefix_fr' G G'); try by vauto.
      basic_solver.
    - unfold ra_consistent in *. cdes PREF. rewrite MO_PREF, RF_PREF.
      arewrite (hb G' ⊆ (hb G)).
      2: { split; try rewrite (@porf_prefix_fr' G G'); auto; eapply irreflexive_inclusion.
           2: by apply CONS. 3: by apply CONS0. 
           all: basic_solver 10. }
      unfold hb. apply clos_trans_mori. 
      rewrite RF_PREF, (@porf_prefix_sb G G'); (try by vauto). basic_solver. 
    - unfold TSO_consistent, SCpL, TSO_hb, ppo, implied_fence in *. 
      cdes PREF. rewrite MO_PREF, RF_PREF, (@porf_prefix_sb G G'), (@porf_prefix_fr' G G'), (@porf_prefix_rfe G G'); try by vauto.
      split; eapply inclusion_acyclic.
      2: by apply CONS. 3: by apply CONS0.
      2: basic_solver 10.
      apply clos_trans_mori. rewrite !unionA.
      apply union_mori; basic_solver 10.
    - unfold scoh_consistent, SCpL, hb in *.
      cdes PREF. rewrite MO_PREF, RF_PREF, (@porf_prefix_sb G G'), (@porf_prefix_fr' G G'); try by vauto.
      splits.
      + eapply inclusion_acyclic; [| apply CONS]. basic_solver 10.
      + eapply irreflexive_inclusion; [| apply CONS0]. basic_solver 10.
      + rewrite RF_PREF, (@porf_prefix_sb G G'); try by vauto.
        eapply irreflexive_inclusion; [| apply PORF].
        apply clos_trans_mori. basic_solver. }
  { ins.
    enough (fsupp (⦗set_compl is_init⦘ ⨾ (sb G ∪ rf G))⁺) as FSUPP.
    { assert (fsupp (sbn G ∪ rf G)) as FSUPP1.
      { apply fsupp_union; [unfold sbn; apply fsupp_sb| apply fsupp_rf]; auto. }
      rewrite ct_begin, rtE, seq_union_r. apply fsupp_union.
      { by rewrite seq_id_r. }
      arewrite ((sbn G ∪ rf G) ⊆ (sbn G ∪ rf G) ⨾ ⦗set_compl is_init⦘).
      { apply domb_rewrite. apply union_domb.
        - unfold sbn. rewrite <- sb_ninit; basic_solver.
        - rewrite no_rf_to_init; basic_solver.
      }
      rewrite clos_trans_rotl.
      rewrite <- seqA with (r2 := (sbn G ∪ rf G)).
      rewrite <- seqA with (r3 := ⦗set_compl is_init⦘).
      rewrite <- ct_begin.
      apply fsupp_seq; auto.
      eapply fsupp_mon; [| by apply FSUPP].
      arewrite (sbn G ⊆ sb G).
      rewrite inclusion_seq_eqv_r. basic_solver. }
    enough ((scoh_consistent ∪₁ ra_consistent) G) as CONS'. 
    { 
      arewrite ((⦗set_compl is_init⦘ ⨾ (sb G ∪ rf G))⁺ ⊆ ⦗set_compl is_init⦘ ⨾ hb G).
      { rewrite inclusion_ct_seq_eqv_l. apply seq_mori; [basic_solver| ].
        apply clos_trans_mori. basic_solver. }
      eapply fsupp_hb; eauto.
      { red in CONS'. destruct CONS'; destruct H; desc; auto.
        eapply irreflexive_inclusion; [| apply H]. basic_solver. }
      apply has_finite_antichains_sb; auto. }
    des; try done; subst M. 
    - right. by apply tso_implies_ra, sc_implies_tso; auto. 
    - by right. 
    - right. by apply tso_implies_ra; auto. 
    - by left.
  }
Qed. 
