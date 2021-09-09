From hahn Require Import Hahn.
Require Import Execution.
Require Import Events. 

Require Import RAop.
Require Import SCOHop.

Section AltDefs.
  
Variable G: execution. 
Hypothesis WF: Wf G. 

Definition ra_loc := (hb G ∩ same_loc) ∪ rf G ∪ co G ∪ fr G.

Lemma transitive_inter {A: Type} (r1 r2: relation A)
      (T1: transitive r1) (T2: transitive r2):
  transitive (r1 ∩ r2).
Proof. basic_solver. Qed.

Lemma fr_co_fr (RFC: rf_complete G) (AT: rmw_atomicity G)
      (RA2: irreflexive ((rf G)⁻¹ ⨾ co G ⨾ co G)): 
  fr G ⨾ co G ⊆ fr G.
Proof. 
  unfold fr. red. ins. do 3 (red in H; desc).
  red. split.
  { exists z0. split; auto. eapply co_trans; eauto. }
  intros [-> _]. 
  edestruct (RA2 y). do 2 (eexists; split; eauto).
Qed.

Lemma co_fr_co (RFC: rf_complete G) (AT: rmw_atomicity G)
      (RA2: irreflexive ((rf G)⁻¹ ⨾ co G ⨾ co G)): 
  co G ⨾ fr G ⊆ co G.
Proof. 
  unfold fr. red. ins. red in H; desc. do 2 (red in H0; desc).
  destruct (classic (x = z0)) as [| NEQ]; [congruence| ]. 
  eapply co_trans; [auto| | apply H2].
  eapply same_relation_exp in H; [eapply same_relation_exp in H2| ]. 
  2, 3: rewrite wf_coD, wf_coE; auto.
  unfolder in H2. unfolder in H. desc. subst z1 z2 z3 z4.
  red in H0. pose proof (@wf_rfl _ WF _ _ H0) as SL1.
  pose proof (@wf_col _ WF _ _ H11) as SL2. pose proof (@wf_col _ WF _ _ H5) as SL3.
  forward eapply (exists_loc ) as [l Lx]. 
  forward eapply wf_co_total with (a := x) (b := z0) (x := l); try by vauto.
  { unfolder. splits; vauto. congruence. }
  ins. des; auto. 
  edestruct (RA2 z). do 2 (eexists; split; eauto).  
Qed.

Lemma fr_trans (RFC: rf_complete G) (AT: rmw_atomicity G)
      (RA2: irreflexive ((rf G)⁻¹ ⨾ co G ⨾ co G)):
  transitive (fr G). 
Proof.
  apply transitiveI. 
  rewrite wf_frD at 1; auto. rewrite !seqA. rewrite w_fr_in_co; auto.
  rewrite inclusion_seq_eqv_l. by apply fr_co_fr.
Qed. 
      

Lemma co_fr_ct (RFC: rf_complete G) (AT: rmw_atomicity G)
      (RA2: irreflexive ((rf G)⁻¹ ⨾ co G ⨾ co G)):
  (co G ∪ fr G)⁺ ⊆ co G ∪ fr G. 
Proof.
  rewrite unionC. rewrite ct_unionE.
  rewrite ct_of_trans, rt_of_trans; try by apply co_trans.
  apply inclusion_union_l; [basic_solver 10| ].
  hahn_frame.
  rewrite crE, seq_union_r, seq_id_r.
  rewrite fr_co_fr, unionK; auto.
  rewrite ct_of_trans; [| by apply fr_trans].
  rewrite seq_union_l, seq_id_l.
  rewrite co_fr_co; auto. basic_solver.   
Qed.

Lemma hb_co_fr_helper x r y
      (RA_CONS: ra_consistent G)
      (RFC: rf_complete G)
      (HBxr : hb G x r)
      (COFRry : (co G ∪ fr G) r y)
      (COyw: co G y x):
  False.
Proof. 
  destruct RA_CONS. destruct (H x). exists r. split; auto.
  right. red in COFRry. des.
  { left. eapply co_trans; eauto. }
  right. apply fr_co_fr; auto.
  { by apply ra_rmw_atomicity. }
  eexists. split; eauto.
Qed. 


Lemma hb_co_fr (RFC: rf_complete G) (RA_CONS: ra_consistent G):
  hb G ∩ same_loc ⨾ (co G ∪ fr G) ⊆ co G ∪ fr G.
Proof.
  red. ins. destruct H as (r & (HBxr & SLxr) & COFRry).
  destruct (exists_loc x) as (l & Lx).
  assert ((acts G ∩₁ is_w ∩₁ (fun a => loc a = l)) y) as Y.
  { eapply hahn_inclusion_exp in COFRry.
    2: { rewrite wf_coD, wf_coE, wf_frD, wf_frE.
         2-5: by eauto.
         rewrite !seqA, <- id_inter, <- !seqA, <- seq_union_l.
         repeat rewrite inclusion_seq_eqv_l.
         rewrite wf_col, wf_frl, unionK; eauto. 
         reflexivity. }
    unfolder in COFRry. desc. unfolder. splits; congruence.  }  
  destruct (r_or_w x) as [Rx | Wx].
  { right. destruct (classic (fr G x y)); auto.
    unfold fr, minus_rel in H. apply not_and_or in H. des.
    2: { apply NNPP in H. red in H. desc. subst.
         destruct RA_CONS. edestruct H. eexists. split; eauto. }
    destruct H.
    assert (exists w, rf G w x) as (w & RFwx).
    { apply RFC. split; auto. apply wf_hbE, seq_eqv_lr in HBxr; auto. by desc. }
    exists w. split; auto.
    forward eapply wf_co_total with (a := w) (b := y) (x := l); try by vauto.
    { eapply same_relation_exp in RFwx.
      2: { rewrite wf_rfD, wf_rfE; eauto. }
      unfolder in RFwx. desc. subst. unfolder. splits; vauto.
      apply wf_rfl in RFwx2; auto. }    
    { intros ->.
      destruct RA_CONS. destruct (H y). exists r. split; auto.
      apply rewrite_trans; [by apply hb_trans| ]. eexists. split; eauto.
      apply ct_step. basic_solver. }
    ins. des; auto.
    edestruct hb_co_fr_helper with (x := w); eauto.
    apply rewrite_trans; [by apply hb_trans| ].
    eexists. split; eauto.
    red. apply ct_step. basic_solver. }
  left.
  forward eapply wf_co_total with (a := x) (b := y) (x := l); try by vauto.
  { apply wf_hbE, seq_eqv_lr in HBxr; auto. desc.
    splits; vauto. }
  { intros ->. destruct RA_CONS. edestruct H. splits; basic_solver. }
  ins. des; auto.
  edestruct hb_co_fr_helper; eauto. 
Qed. 

Lemma co_fr_acyclic (CONS: ra_consistent G) (RFC: rf_complete G):
  acyclic (co G ∪ fr G).
Proof.
  forward eapply ra_rmw_atomicity as AT; eauto. cdes CONS.
  apply AuxRel.acyclic_union1.
  1, 2: unfold acyclic; repeat (rewrite ct_of_trans; auto using co_trans, co_irr, fr_trans, fr_irr).
  repeat (rewrite ct_of_trans; auto using co_trans, co_irr, fr_trans, fr_irr).
  repeat (rewrite ct_of_trans; auto using co_trans, co_irr, fr_trans, fr_irr).
  rewrite co_fr_co; auto. by apply co_acyclic.
Qed. 

Definition ra_consistent_alt := irreflexive ra_loc⁺. 

Lemma ra_consistent_implies_ra_consistent_alt (RFC: rf_complete G)
      (CONS: ra_consistent G):
  ra_consistent_alt. 
Proof. 
  red. cdes CONS. desc. unfold ra_loc.
  rewrite union_absorb_r with (r := rf G).
  2: { apply inclusion_inter_r; [| by apply wf_rfl]. 
       unfold hb. rewrite <- ct_step. basic_solver. }
  fold (acyclic (hb G ∩ same_loc ∪ co G ∪ fr G)).
  rewrite unionA. apply AuxRel.acyclic_union1.
  { unfold acyclic. rewrite ct_of_trans.
    2: { apply transitive_inter; auto using hb_trans, same_loc_trans. }
    eapply irreflexive_inclusion; [| apply CONS0].
    basic_solver. }
  { by apply co_fr_acyclic. }
  rewrite co_fr_ct; auto; [| by apply ra_rmw_atomicity]. 
  rewrite ct_of_trans.
  2: { apply transitive_inter; auto using hb_trans, same_loc_trans. }
  rewrite hb_co_fr; auto. by apply co_fr_acyclic.
Qed.

Lemma rft_co_co_helper (IRR: irreflexive (co G ∪ fr G)⁺):
  irreflexive ((rf G)⁻¹ ⨾ co G ⨾ co G).
Proof.
  red. ins. red in H. desc. red in H0. desc.
  destruct (classic (z0 = x)).
  { subst z0. edestruct co_irr; eauto. }
  destruct (IRR x). apply ctEE. exists 1. split; auto.
  simpl.
  exists z0. split.
  2: { generalize H1. basic_solver. }
  apply seq_eqv_l. split; auto. right. red. split; vauto.
  unfolder. by intros [-> _].
Qed. 

Lemma ra_consistent_alt_implies_ra_consistent (RFC: rf_complete G)
      (CONS: ra_consistent_alt):
  ra_consistent G.
Proof. 
  red in CONS. unfold ra_consistent, ra_loc in *. split.
  - red. intros x [y [HBxy COFRyx]].
    red in COFRyx. des.
    { subst y. destruct (CONS x). apply ct_step. by repeat left. }
    destruct (CONS x). apply ctEE. exists 1. split; auto.
    simpl. exists y. split; [| generalize COFRyx; basic_solver 10].
    apply seq_eqv_l. split; auto. repeat left. split; auto.
    apply same_loc_sym. eapply hahn_inclusion_exp; [| apply COFRyx].
    rewrite wf_col, wf_frl; auto. basic_solver. 
  - apply rft_co_co_helper.
    eapply irreflexive_inclusion; eauto.
    apply clos_trans_mori. basic_solver. 
Qed. 
    
Theorem ra_consistent_defs_equivalence (RFC: rf_complete G):
  ra_consistent G <-> ra_consistent_alt. 
Proof.
  split; auto using ra_consistent_alt_implies_ra_consistent, ra_consistent_implies_ra_consistent_alt.
Qed.

Definition scoh_consistent_alt := irreflexive (hb G) /\ SCpL G. 

Theorem scoh_consistent_defs_equiv (RFC: rf_complete G):
  scoh_consistent G <-> scoh_consistent_alt. 
Proof.
  unfold scoh_consistent, scoh_consistent_alt. 
  split.
  - ins. desc. split; auto. 
  - ins. desc. splits; auto.
    apply rft_co_co_helper. do 2 red in H0.
    eapply irreflexive_inclusion; eauto. apply clos_trans_mori. basic_solver. 
Qed. 

End AltDefs.
