From hahn Require Import Hahn.
From hahn Require Import HahnOmega.
Require Import Execution.
Require Import Events. 

Require Import TSO.
Require Import SC.
Require Import RAop.
Require Import SCOHop.

Section ModelsRelationships.
  
Variable G: execution. 
Hypothesis WF: Wf G. 

Lemma rel_union_minus_alt {A: Type} (r r': relation A):
  r ≡ r ∩ r' ∪ r \ r'.
Proof.
  split; [| basic_solver].
  red. intros x y Rxy.
  destruct (classic (r' x y)); basic_solver. 
Qed.

Lemma RFE_INCL: rfe G ⊆ TSO_hb G. 
Proof. unfold TSO_hb. rewrite <- ct_step. basic_solver. Qed. 

Lemma RF_INCL: rf G ⊆ sb G ∪ TSO_hb G.
Proof. rewrite rfi_union_rfe. unfold rfi. generalize RFE_INCL. basic_solver. Qed.

Lemma sb_rf_ct_tso_hb' (TSO: TSO_consistent G):
  (sb G ∪ rf G)⁺ ⊆ sb G ∪ TSO_hb G.
Proof.
  rewrite rfi_union_rfe, <- unionA.
  rewrite union_absorb_r with (r := rfi G); [| unfold rfi; basic_solver].  
  rewrite unionC, path_ut2; [| apply sb_trans].
  apply inclusion_union_l. 
  { unfold TSO_hb. apply inclusion_union_r. right.
    apply clos_trans_mori. basic_solver. }
  assert (sb G ⨾ rfe G ⊆ TSO_hb G) as HELPER.
  { unfold TSO_hb, ppo.
    rewrite rel_union_minus_alt with (r := sb G) (r' := is_w × is_r) at 1.
    rewrite seq_union_l. apply inclusion_union_l.
    2: { rewrite <- ct_unit. apply seq_mori; [| basic_solver].
         rewrite <- ct_step. basic_solver 10. }
    rewrite wf_rfeD at 1; eauto.
    rewrite <- ct_unit. rewrite <- seqA. apply seq_mori; [| basic_solver].
    rewrite <- ct_step. do 3 left. right.
    apply seq_eqv_r in H. desc. unfolder in H. desc. 
    red. left. apply seq_eqv_r; auto. split; auto.
    destruct y; [| destruct l]; vauto. }
  assert (⦗is_r⦘ ⨾ sb G ⊆ TSO_hb G) as R_SB_HELPER.
  { unfold TSO_hb. rewrite <- ct_step.
    red. ins. apply seq_eqv_l in H. desc. destruct x; [vauto| ].
    destruct l; try by vauto.
    { repeat left. red. split; auto. red. ins.
      unfolder in H1. type_solver. }
    { do 3 left. right. red. right. type_solver. }
  }
  rewrite rtE with (r := sb G ⨾ (rfe G)⁺), <- !seqA, seq_union_r.
  rewrite !seqA, seq_union_l. apply inclusion_union_l.
  2: { rewrite wf_rfeD at 2; auto. rewrite <- !seqA.
       rewrite inclusion_ct_seq_eqv_r, <- seqA.
       rewrite inclusion_ct_seq_eqv_r, !seqA.
       rewrite inclusion_seq_eqv_l with (dom := is_w).
       rewrite ct_begin with (r := rfe G), <- !seqA.
       rewrite HELPER, RFE_INCL, !seqA.
       rewrite <- seqA with (r2 := sb G), R_SB_HELPER.
       rewrite <- ct_begin, ct_of_ct, ct_ct, rt_ct.
       apply inclusion_union_r. right.
       apply inclusion_t_ind; [basic_solver | apply transitive_ct]. }
  rewrite seq_id_r. rewrite rtE. rewrite !seq_union_l, !seq_union_r.
  rewrite !seq_id_l, !seq_id_r. 
  rewrite wf_rfeD; auto. rewrite <- !seqA, !inclusion_ct_seq_eqv_r.
  rewrite !inclusion_seq_eqv_l with (dom := is_w), !seqA.
  repeat sin_rewrite R_SB_HELPER. rewrite !inclusion_seq_eqv_r.
  rewrite ct_begin at 1. sin_rewrite HELPER. rewrite !RFE_INCL.
  repeat sin_rewrite ct_unit. rewrite ct_ct, unionK, <- ct_begin, unionA, unionK.
  apply union_mori; [basic_solver| apply inclusion_t_ind; [basic_solver | apply transitive_ct]].
Qed. 

Theorem tso_implies_ra (TSO: TSO_consistent G):
  ra_consistent G.
Proof.
  red. unfold hb. split.
  2: { arewrite ((rf G)⁻¹ ⨾ co G ⊆ (fr G)^?).
       { rewrite crE. unfold fr.
         rewrite rel_union_minus_alt with (r' := ⦗fun _: Event => True⦘) at 1.
         basic_solver 10. }
       arewrite (fr G ⊆ TSO_hb G). arewrite (co G ⊆ TSO_hb G).
       rewrite rewrite_trans_seq_cr_l; [| apply transitive_ct].
       red in TSO. desc. rewrite ct_step. auto. }

  rewrite sb_rf_ct_tso_hb'; auto.   
  rewrite seq_union_l. apply irreflexive_union. split. 
  2: { arewrite ((co G ∪ fr G) ⊆ TSO_hb G).
       rewrite rewrite_trans_seq_cr_r; [| apply transitive_ct].
       red in TSO. desc. rewrite ct_step. auto. }
   rewrite crE, seq_union_r, !seq_id_r. apply irreflexive_union. split.
  { apply sb_irr. }
  red. intros x [y [SB REL]].
  red in TSO. desc.
  apply (TSO0 y). apply ct_begin. exists x. split; [destruct REL; basic_solver| ].
  apply rt_step. repeat left. split; auto. 
  destruct REL; [apply wf_col in H | apply wf_frl in H]; auto. 
Qed.

Theorem sc_implies_tso G_ (WF_: Wf G_) (SC: sc_consistent G_):
  TSO_consistent G_.
Proof. 
  clear dependent G. rename G_ into G. rename WF_ into WF.
  red.
  unfold Execution.SCpL. rewrite inclusion_restr_eq. 
  red in SC. unfold TSO_hb. unfold ppo, implied_fence.
  arewrite (sb G ⊆ hb_sc G).
  arewrite (rfe G ⊆ rf G). arewrite (rf G ⊆ hb_sc G).
  arewrite (co G ⊆ hb_sc G). arewrite (fr G ⊆ hb_sc G).
  rewrite !inclusion_seq_eqv_r, inclusion_seq_eqv_l.
  arewrite (hb_sc G \ is_w × is_r ⊆ hb_sc G).
  rewrite !unionK.
  rewrite ct_of_trans; [| apply transitive_ct].
  unfold acyclic. rewrite ct_of_trans; [| apply transitive_ct]. auto.
Qed.

(* TODO: prove that RA implies SCOH *)
Theorem sc_implies_scoh G_ (WF_: Wf G_) (SC: sc_consistent G_):
  scoh_consistent G_.
Proof.
  red. red in SC. unfold SCpL.
  arewrite ((rf G_)⁻¹ ⨾ co G_  ⊆ (fr G_)^?).
  { unfold fr. red. ins.
    destruct (classic (x = y)).
    { subst. basic_solver. }
    right. split; auto.
    red. ins. red in H1. by desc. }
  arewrite (sb G_ ⊆ hb_sc G_). arewrite (rf G_ ⊆ hb_sc G_).
  arewrite (co G_ ⊆ hb_sc G_). arewrite (fr G_ ⊆ hb_sc G_).
  rewrite inclusion_restr_eq, !unionK.
  rewrite rewrite_trans_seq_cr_l.
  2: { unfold hb_sc. by apply transitive_ct. }
  assert (acyclic (hb_sc G_)).
  { red. rewrite ct_of_trans; auto. unfold hb_sc. by apply transitive_ct. }
  splits; auto. by arewrite (hb G_ ⊆ hb_sc G_).  
Qed.     
    

End ModelsRelationships. 
