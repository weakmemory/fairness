Require Import Lia IndefiniteDescription Arith.
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Labels.
Require Import Events.
Require Import Execution.
Require Import View.
Require Import SCOHop.
Require Import TraceWf.

Set Implicit Arguments.

#[local]
Hint Immediate trace_wf_nodup : core.

Lemma match_evE x y :
  match_ev x y <-> is_external y /\ x = proj_ev y.
Proof using.
  split; ins; desf.
  destruct H; desf.
  destruct y; vauto. destruct e; vauto. 
Qed.

Definition myco t x y :=
  (⟪ INITx : is_init x ⟫ /\
   exists yl,
     ⟪ My : match_ev y yl ⟫ /\
     ⟪ ELy : trace_elems t yl ⟫ /\
     ⟪ Wy : is_w y ⟫ /\
     ⟪ LOC : loc x = loc y ⟫) \/
  (exists xl,
     ⟪ Mx : match_ev x xl ⟫ /\
     ⟪ ELx : trace_elems t xl ⟫ /\
     ⟪ Wx : is_w x ⟫ /\
     exists yl,
       ⟪ My : match_ev y yl ⟫ /\
       ⟪ ELy : trace_elems t yl ⟫ /\
       ⟪ Wy : is_w y ⟫ /\
       ⟪ LOC : loc x = loc y ⟫ /\
       ⟪ TS : write_ts xl < write_ts yl ⟫).

Definition myrf t x y :=
  (⟪ INITx : is_init x ⟫ /\
   exists yl,
     ⟪ My : match_ev y yl ⟫ /\
     ⟪ ELy : trace_elems t yl ⟫ /\
     ⟪ Ry : is_r y ⟫ /\
     ⟪ LOC : loc x = loc y ⟫ /\
     ⟪ TS : 0 = read_ts yl ⟫) \/
  (exists xl,
     ⟪ Mx : match_ev x xl ⟫ /\
     ⟪ ELx : trace_elems t xl ⟫ /\
     ⟪ Wx : is_w x ⟫ /\
     exists yl,
       ⟪ My : match_ev y yl ⟫ /\
       ⟪ ELy : trace_elems t yl ⟫ /\
       ⟪ Ry : is_r y ⟫ /\
       ⟪ LOC : loc x = loc y ⟫ /\
       ⟪ TS : write_ts xl = read_ts yl ⟫).

Definition uniq_ts (s : SCOH_label -> Prop) :=
  forall x e (INS: s e) (M : match_ev x e)
         x' e' (INS': s e') (M' : match_ev x' e')
         (W: is_w x)
         (W': is_w x')
         (LOC: loc x = loc x')
         (TS: write_ts e = write_ts e'),
    e = e'.

Lemma trace_elems_ext t xl :
  trace_elems (trace_filter is_external t) xl <->
  exists x, trace_elems t xl /\ match_ev x xl.
Proof using.
  rewrite trace_in_filter; split; ins; desf.
  { destruct xl; vauto. destruct e; vauto. eexists.
    split; [| econstructor; eauto]. vauto. }
  split; auto. destruct x, xl; inversion H0; vauto. 
Qed.

Lemma trace_elems_trproj t x :
  trace_elems (trproj t) x <->
  exists xl, trace_elems t xl /\ match_ev x xl.
Proof using.
  unfold trproj.
  rewrite trace_in_map; split; ins; desf.
  {
    rewrite trace_elems_ext in *; desf.
    eexists; split; eauto.
    destruct H0; ins; desf; econs; ins.
  }
  exists xl; rewrite trace_in_filter.
  destruct H0; desf.
Qed.



Lemma tr_scoh_nodup t (ND : trace_nodup (trproj t))
  x xl (Mx : match_ev x xl) (ELx : trace_elems t xl)
  yl (My : match_ev x yl) (ELy : trace_elems t yl) : xl = yl.
Proof using.
  assert (Nx : trace_elems (trace_filter is_external t) xl)
    by (rewrite trace_elems_ext; eauto).
  assert (Ny : trace_elems (trace_filter is_external t) yl)
    by (rewrite trace_elems_ext; eauto).

  unfold trproj in *.
  apply trace_in_nth with (d := deflabel) in Nx; desc.
  apply trace_in_nth with (d := deflabel) in Ny; desf.
  destruct Mx, My; desf.
  forward eapply trace_nodup_inj with
      (i := n) (j := n0) as X; eauto; desf; try lia.
  all: try rewrite trace_length_map; ins.
  rewrite !trace_nth_map, EQl, EQl0; ins.
Qed.

Lemma myco_irrefl t (ND: trace_nodup (trproj t)) :
  irreflexive (myco t).
Proof using.
  unfold myco; red; ins; desf; unnw.
  destruct My; desf.
  assert (xl = yl) by eauto using tr_scoh_nodup.
  desf; lia.
Qed.

Lemma myco_trans t (ND: trace_nodup (trproj t)) :
  transitive (myco t).
Proof using.
  unfold myco; red; ins; desf; unnw.
  all: try solve [destruct My0; desf].
  - left; eauto 8 using eq_trans.
  - assert (xl = yl0) by eauto using tr_scoh_nodup.
    desf; right; repeat first [eassumption | eapply ex_intro | apply conj];
        try lia.
Qed.

Lemma myco_total t (ND: trace_nodup (trproj t))
      (U : uniq_ts (trace_elems t)) x :
  is_total
    ((is_init ∪₁ trace_elems (trproj t))
       ∩₁ is_w ∩₁ (fun a => loc a = x)) (myco t).
Proof using.
  unfold myco; unfolder; ins; desf; unnw.
  all: try rewrite trace_elems_trproj in *; desc; eauto 8.
  { unfold loc in *; destruct a, b; ins; desf. }
  destruct (lt_eq_lt_dec (write_ts xl) (write_ts xl0)) as [[|EQ]|];
    eauto 12.
  red in U; eapply U with (x' := a) (x := b) in EQ; desf.
  destruct IWa0, IWb2; desf.
Qed.

Lemma myrf_func t (ND: trace_nodup (trproj t)) (U : uniq_ts (trace_elems t)) :
  functional (myrf t)⁻¹.
Proof using.
  unfold myrf; unfolder; ins; desf.
  { unfold loc in *; destruct y, z; ins; desf. }
  { assert (yl0 = yl) by eauto using tr_scoh_nodup; subst.
    rewrite <- TS in *; destruct Mx; desf.
  }
  { assert (yl0 = yl) by eauto using tr_scoh_nodup; subst.
    rewrite <- TS in *; destruct Mx; desf.
  }
  { assert (yl0 = yl) by eauto using tr_scoh_nodup; subst.
    rewrite <- TS in *.
    eapply U in TS0; eauto; desf; try congruence.
    destruct Mx, Mx0; desf.
  }
Qed.

Lemma SCOH_mem t mem (INIT : mem 0 = Sinit) d
      (STEP : forall i (LTi: NOmega.lt_nat_l i (trace_length t)),
          SCOH_step (mem i) (trace_nth i t d) (mem (S i)))
      n (LT: NOmega.lt_nat_l n (trace_length t)) :
  fst (mem n) ≡₁ Minit ∪₁
      ⋃₁ i < n, SCOH_wmsg ↑₁ (SCOH_is_w ∩₁ eq (trace_nth i t d)).
Proof using.
  induction n.
  rewrite INIT; ins; unfolder; split; ins; desf; eauto; lia.
  assert (LT' : NOmega.lt_nat_l n (trace_length t)).
  { destruct (trace_length t); ins; lia. }
  rewrite set_bunion_lt_S, <- set_unionA, <- IHn; ins; clear IHn.
  specialize (STEP n); specialize_full STEP; ins.

  destruct STEP; try rewrite MEM, EQ; ins; try rewrite VIEW.
  all: rewrite ?upds in *.
  all: unfolder; split; ins; desf; eauto.

  - right; eexists; splits; ins; ins; rewrite upds; ins.
  - right; eexists; splits; ins; ins.
Qed.

Lemma SCOH_uniq_ts t (T: LTS_trace scoh_lts t) :
  uniq_ts (trace_elems t).
Proof using.
  red; ins; apply LTS_traceE in T.
  eapply trace_in_nth with (d := deflabel) in INS; desf.
  eapply trace_in_nth with (d := deflabel) in INS'; desf.
  destruct M, M'; desf.
  unfold loc in *; ins.
  rewrite EQl, EQl0 in *; ins; desf; ins.
  destruct (lt_eq_lt_dec n n0) as [[LT|]|LT]; desf;
    try rewrite EQl in *; desf.
  {
    assert (N:= INS').
    eapply T0 with (d := deflabel) in N.
    rewrite EQl0 in *; destruct N; desf; ins; desf.
    all: exfalso; eapply FRESH.
    all: destruct lab; ins.
    all: do 2 eexists; eapply SCOH_mem; unfolder; ins; eauto.
    all: right; repeat eexists; eauto.
    all: rewrite EQl; ins; desf.
  }
  {
    assert (N:= INS).
    eapply T0 with (d := deflabel) in N.
    rewrite EQl in *; destruct N; desf; ins; desf.
    all: exfalso; eapply FRESH.
    all: destruct lab0; ins.
    all: do 2 eexists; eapply SCOH_mem; unfolder; ins; eauto.
    all: right; repeat eexists; eauto.
    all: rewrite EQl0; ins; desf.
  }
Qed.

Lemma view_of_match t (ND: trace_nodup (trproj t))
      x xl (M: match_ev x xl) (E: trace_elems t xl) :
  view_of' t x = view_of xl.
Proof using.
  unfold view_of'; desf; try solve [exfalso; eauto].
  destruct (IndefiniteDescription.constructive_indefinite_description);
    clear e; ins; desc; f_equal; eapply tr_scoh_nodup; eauto.
Qed.

Lemma SCOH_view t mem (INIT : mem 0 = Sinit) d
      (STEP : forall i (LTi: NOmega.lt_nat_l i (trace_length t)),
          SCOH_step (mem i) (trace_nth i t d) (mem (S i)))
      n (LT: NOmega.lt_nat_l n (trace_length t)) mytid :
  view_le (view_joinl
             (map view_of
                  (filterP (fun x => tid_of x = mytid)
                           (map (fun i => trace_nth i t d)
                                (List.seq 0 n)))))
          (snd (mem n) mytid).
Proof using.
  induction n; [by rewrite INIT, seq0; ins|].
  assert (LT': NOmega.lt_nat_l n (trace_length t))
    by eauto using NOmega.lt_lt_nat.
  specialize (STEP _ LT').
  assert (view_le (snd (mem n) mytid) (snd (mem (S n)) mytid)).
  {
    destruct STEP; rewrite VIEW; ins; desf;
    unfold upd; desf; try apply view_le_join_l; red; ins; desf; lia.
  }
  rewrite seqS; ins.
  repeat first [ rewrite map_app | rewrite filterP_app
                 | rewrite view_joinl_app ]; ins.
  eapply view_join_lub; eauto using view_le_trans.
  desf; ins; try apply view_join_lub; ins;
    try solve [red; auto with arith].
  destruct STEP; rewrite EQ, VIEW in *; ins; desf;
  unfold upd; desf; try apply view_join_lub; red; ins; desf; lia.
Qed.

Lemma view_le_same_tid t (TR: LTS_trace scoh_lts t)
      i j (Lij: i < j) (Lj: NOmega.lt_nat_l j (trace_length t)) d
      (EXT : is_external (trace_nth j t d))
      (TID: tid_of (trace_nth i t d) = tid_of (trace_nth j t d)) :
  view_le (view_of (trace_nth i t d))
          (view_of (trace_nth j t d)).
Proof using.
  destruct (LTS_traceE _ _ TR) as (mem & INIT & STEP); ins.
  eapply view_le_trans, SCOH_step_view_ext; eauto.
  eapply view_le_trans, SCOH_view with (d := d); eauto.
  rewrite (seq_split0 Lij).
  repeat first [rewrite map_app; ins | rewrite filterP_app; ins
                | rewrite view_joinl_app].
  desf; ins. apply view_le_join_r, view_le_join_l; ins.
Qed.


Definition index_of t x :=
  match excluded_middle_informative
          (exists n, NOmega.lt_nat_l n (trace_length t) /\
                     match_ev x (trace_nth n t (deflabel))) with
  | left IN =>
    S (proj1_sig
               (IndefiniteDescription.constructive_indefinite_description
                  _ IN))
  | right _ => 0
  end.

Lemma index_of_init t x :
  index_of t (InitEvent x) = 0.
Proof using.
  unfold index_of; desf; ins.
  exfalso; desf; destruct e0; ins.
Qed.

Lemma SCOH_sb_trord t
      (TR: LTS_trace scoh_lts t)
      (WF: trace_wf (trproj t)) x y
      (REL: (⦗is_init ∪₁ trace_elems (trproj t)⦘ ⨾ ext_sb ⨾
             ⦗is_init ∪₁ trace_elems (trproj t)⦘) x y) :
    index_of t x < index_of t y.
Proof using.
  unfold ext_sb in *; unfolder in *; ins; desf; desf.
  all: try rewrite index_of_init.
  all: unfold index_of; ins; desf; try lia.
  1-2,4: destruct n; rewrite trace_elems_trproj in *; desf;
    apply trace_in_nth with (d := deflabel) in REL1; desf; eauto.
  2: destruct n0; rewrite trace_elems_trproj in *; desf;
    apply trace_in_nth with (d := deflabel) in REL1; desf; eauto.
  repeat destruct (IndefiniteDescription.constructive_indefinite_description).
  clear e e0; ins; desf.
  rewrite match_evE in *; desc.
  assert (EXT1 := a1).
  assert (EXT2 := a2).
  eapply trace_nth_filter' in a2; eauto.
  eapply trace_nth_filter' in a1; eauto.
  destruct (lt_eq_lt_dec x x0) as [[]|LT]; desf; try lia.
    solve [rewrite <- a3 in a4; desf; lia].
  unfold trproj in *.
  change (fun r => is_external r) with is_external in *.
  forward eapply WF with
      (i := length
              (filterP is_external
                       (map (fun i => trace_nth i t (deflabel))
                            (List.seq 0 x0))))
      (j := length
              (filterP is_external
                       (map (fun i => trace_nth i t (deflabel))
                            (List.seq 0 x))))
      (d := InitEvent 0).
  rewrite (seq_split0 LT), map_app, filterP_app, length_app; ins; desf; ins;
    try lia.
    by rewrite trace_length_map; eapply trace_lt_length_filter; ins.
  all: change (InitEvent 0) with (proj_ev (deflabel));
    rewrite !trace_nth_map, a1, a2, <- a3, <- a4; ins; try lia.
Qed.

Lemma SCOH_rf_trord t
      (TR: LTS_trace scoh_lts t)
      (ND: trace_nodup (trproj t))
      (U : uniq_ts (trace_elems t)) x y
      (REL: myrf t x y) :
  index_of t x < index_of t y.
Proof using.
  destruct (LTS_traceE _ _ TR) as (mem & INIT & STEP); desf.
  unfold myrf in *; unfolder in *; ins; desf.
    destruct x; ins; rewrite index_of_init; ins.
    all: unfold index_of; desf; try lia.
  1,3,4: solve [exfalso;
                apply trace_in_nth with (d := deflabel) in ELy;
                desf; eauto].
  repeat destruct (IndefiniteDescription.constructive_indefinite_description).
  rename a into Vx; rename a0 into Vy.
  clear e e0; ins; desf.
  assert (xl = trace_nth x0 t (deflabel))
    by (eapply tr_scoh_nodup; eauto with hahn).
  assert (yl = trace_nth x1 t (deflabel))
    by (eapply tr_scoh_nodup; eauto with hahn).
  desf; clear ELx ELy Vx0 Vy0.
  destruct Mx, My; ins; desf.
  forward eapply (STEP x1) with (d := deflabel) as Sy; ins.
  forward eapply SCOH_mem with (d := deflabel) as X; eauto.
  destruct Sy; rewrite EQ in *; ins; desf.

  all: apply X in MSG; unfold Minit in MSG; unfolder in MSG; ins; desf;
    rewrite EQl in *; ins.
  all: assert (y = x0); desf; try lia.
  {
    assert (EQy: trace_nth y t (deflabel) =
                 trace_nth x0 t (deflabel)).
    {
      destruct (trace_nth y t (deflabel)) eqn: M; ins; desf.
      all: rewrite <- M.
      all: eapply U with (x := _); eauto using match_ev with hahn.
      all: rewrite M, EQl; ins.
    }
    eapply trace_nodup_filter_inj; eauto using trace_nodup_mapE with hahn.
    rewrite EQy, EQl; ins.
  }
  {
    assert (EQy: trace_nth y t (deflabel) =
                 trace_nth x0 t (deflabel)).
    {
      destruct (trace_nth y t (deflabel)) eqn: M; ins; desf.
      all: rewrite <- M.
      all: eapply U with (x := _); eauto using match_ev with hahn.
      all: rewrite M, EQl; ins.
    }
    eapply trace_nodup_filter_inj; eauto using trace_nodup_mapE with hahn.
    rewrite EQy, EQl; ins.
  }
Qed.

Lemma SCOH_hb_trord t
      (TR: LTS_trace scoh_lts t)
      (WF: trace_wf (trproj t)) x y
      (REL: hb {| acts := is_init ∪₁ trace_elems (trproj t);
                  rf := myrf t; co := myco t |} x y) :
  index_of t x < index_of t y.
Proof using.
  induction REL; eauto using Nat.lt_trans.
  destruct H;
    [ eapply SCOH_sb_trord | eapply SCOH_rf_trord ];
    eauto using SCOH_uniq_ts.
Qed.

Lemma SCOH_le_view_sb t
      (TR: LTS_trace scoh_lts t)
      (WF: trace_wf (trproj t)) x y
      (REL: (⦗is_init ∪₁ trace_elems (trproj t)⦘ ⨾ ext_sb ⨾
             ⦗is_init ∪₁ trace_elems (trproj t)⦘) x y) :
    view_le (view_of' t x) (view_of' t y).
Proof using.
  assert (ND: trace_nodup (trproj t)) by eauto.
  unfold ext_sb in *; unfolder in *; ins; desf;
    rewrite ?view_of_init.
  all: try (red; ins; lia).
  assert (Ex := REL); assert (Ey := REL1).
  clear REL REL1; desf.
  rewrite trace_elems_trproj in Ex, Ey; desf.
  erewrite !view_of_match in *; eauto.
  destruct Ex0, Ey0; desf.
  eapply trace_in_nth with (d := deflabel) in Ex; desf.
  eapply trace_in_nth with (d := deflabel) in Ey; desf.
  rewrite <- Ex0, <- Ey0.
  eapply view_le_same_tid; eauto.
  all: try rewrite Ex0; try rewrite Ey0; ins.
  destruct (lt_eq_lt_dec n n0) as [[]|LT]; desf.
  { rewrite Ex0 in *; desf; lia. }
  assert (EXT: is_external (trace_nth n t (deflabel))).
    by (rewrite Ex0; ins).
  assert (EXT0: is_external (trace_nth n0 t (deflabel))).
    by (rewrite Ey0; ins).
  rewrite <- trace_nth_filter' with (f := is_external) in Ex0; ins;
    try (by rewrite Ex0).
  rewrite <- trace_nth_filter' with (f := is_external) in Ey0; ins;
    try (by rewrite Ey0).
  unfold trproj in *.
  red in WF.
  forward eapply WF with
      (i := length
              (filterP is_external
                       (map (fun i => trace_nth i t (deflabel))
                            (List.seq 0 n0))))
      (j := length
              (filterP is_external
                       (map (fun i => trace_nth i t (deflabel))
                            (List.seq 0 n))))
      (d := InitEvent 0).
  rewrite (seq_split0 LT), map_app, filterP_app, length_app; ins; desf; ins;
    try lia.
  rewrite trace_length_map.
  {
    clear - Ex EXT.
    destruct t; ins; desf; ins.
    erewrite <- map_nth_seq
      with (a := 0) (l := l)
           (f := fun i => nth i l (deflabel)) at 1; auto using app_nth1.
    rewrite (seq_split0 Ex), map_app, filterP_app, length_app; ins; desf; ins;
      try lia.
    destruct (IndefiniteDescription.constructive_indefinite_description);
      ins; desf.
    specialize (l _ EXT).
    rewrite seqS, (seq_split0 l); ins.
    rewrite !map_app, !filterP_app, !length_app; ins; desf; ins; desf.
    all: rewrite <- !Nat.add_assoc; apply Nat.lt_add_pos_r; lia.
  }
  all: change (InitEvent 0) with (proj_ev (deflabel));
    rewrite !trace_nth_map, Ex0, Ey0; ins; try lia.
Qed.

(* Lemma SCOH_le_view_rf t *)
(*       (TR: LTS_trace scoh_lts t) *)
(*       (ND: trace_nodup (trproj t)) x y *)
(*       (REL: myrf t x y) : *)
(*     view_le (view_of' t x) (view_of' t y). *)
(* Proof using. *)
(*   destruct (LTS_traceE _ _ TR) as (mem & INIT & STEP); desf. *)
(*   unfold myrf in *; unfolder in *; ins; desf; *)
(*     rewrite ?view_of_init. *)
(*   { destruct x; ins; rewrite view_of_init; *)
(*       red; ins; lia. } *)
(*   erewrite !view_of_match in *; eauto. *)
(*   eapply trace_in_nth with (d := deflabel) in ELx; desf. *)
(*   eapply trace_in_nth with (d := deflabel) in ELy; desf. *)
(*   forward eapply SCOH_mem with (d := deflabel) as X; ins; eauto. *)

(*   assert (S := STEP _ ELy (deflabel)). *)
(*   destruct Mx; desf; ins. *)
(*   destruct My, S; ins; desf; rewrite EQ in *; ins; desf. *)
(*   all: apply X in MSG; unfold Minit in MSG; unfolder in MSG; desf. *)
(*   all: rewrite EQl in *; ins. *)
(*   all: assert (y = n); desf. *)
(*   2: { destruct (STEP _ ELx deflabel); ins; *)
(*        rewrite EQ0 in *; ins; desf. done. *)

(*   (* 2,4:  *) *)
(*   { *)
(*     assert (EQy: trace_nth y t (deflabel) = *)
(*                  trace_nth n t (deflabel)). *)
(*     { *)
(*       destruct (trace_nth y t (deflabel)) eqn: M; ins; desf. *)
(*       all: rewrite <- M. *)
(*       all: eapply SCOH_uniq_ts with (x := _); eauto using match_ev with hahn. *)
(*       all: rewrite M, EQl; ins. *)
(*     } *)
(*     eapply trace_nodup_filter_inj; eauto using trace_nodup_mapE with hahn. *)
(*     rewrite EQy, EQl; ins. *)
(*   } *)
(*   { *)
(*     assert (EQy: trace_nth y t (deflabel) = *)
(*                  trace_nth n t (deflabel)). *)
(*     { *)
(*       destruct (trace_nth y t (deflabel)) eqn: M; ins; desf. *)
(*       all: rewrite <- M. *)
(*       all: eapply SCOH_uniq_ts with (x := _); eauto using match_ev with hahn. *)
(*       all: rewrite M, EQl; ins. *)
(*     } *)
(*     eapply trace_nodup_filter_inj; eauto using trace_nodup_mapE with hahn. *)
(*     rewrite EQy, EQl; ins. *)
(*   } *)
(* Qed. *)

(* Lemma SCOH_le_view_hb t *)
(*       (TR: LTS_trace scoh_lts t) *)
(*       (WF: trace_wf (trproj t)) x y *)
(*       (REL: hb {| acts := is_init ∪₁ trace_elems (trproj t); *)
(*                   rf := myrf t; co := myco t |} x y) : *)
(*     view_le (view_of' t x) (view_of' t y). *)
(* Proof using. *)
(*   induction REL; eauto using view_le_trans. *)
(*   destruct H; *)
(*     [ eapply SCOH_le_view_sb | eapply SCOH_le_view_rf ]; eauto. *)
(* Qed. *)

Lemma view_of_msg_wf t mem (INIT : mem 0 = Sinit) d
      (STEP : forall i (LTi: NOmega.lt_nat_l i (trace_length t)),
          SCOH_step (mem i) (trace_nth i t d) (mem (S i)))
      n (LT: NOmega.lt_nat_l n (trace_length t)) msg
      (MEM : fst (mem n) msg) :
  mview msg (mloc msg) = mts msg.
Proof using.
  revert msg MEM; induction n; ins.
  { eapply SCOH_mem in MEM; eauto.
    unfold Minit in *; unfolder in MEM; desf; try lia.
    destruct msg; ins; desf. }
  assert (LT' : NOmega.lt_nat_l n (trace_length t)).
    by (destruct (trace_length t); ins; lia).
  eapply SCOH_mem in MEM; eauto.
  unfold Minit in *; unfolder in MEM; desf; try lia.
  destruct msg; ins; desf.
  rewrite Nat.lt_succ_r, Nat.le_lteq in MEM; desf.
    apply IHn; ins; eapply SCOH_mem; eauto;
      right; exists y; vauto.
  destruct (STEP n); ins; rewrite EQ in *; ins; desf.
  all: unfold view_join, upd in *; desf.
  (* rewrite Nat.max_l; ins. *)
  (* apply IHn in MSG; ins; desf; lia. *)
Qed.

Lemma view_of_write t (TR : LTS_trace scoh_lts t) y yl
      (My : match_ev y yl)
      (ELy : trace_elems t yl)
      (Wy : is_w y) :
  view_of yl (loc y) = write_ts yl.
Proof using.
  destruct (LTS_traceE _ _ TR) as (mem & INIT & STEP); desf.
  eapply trace_in_nth with (d := deflabel) in ELy; desf.
  assert (S := STEP _ ELy (deflabel)).
  destruct My; desf.
  rewrite EQl in *; ins.
  destruct S; ins; desf.
  all: unfold view_join, upd; desf.
  (* rewrite Nat.max_l; ins; rewrite e. *)
  (* eapply view_of_msg_wf with (d := deflabel) in MSG; *)
  (*   ins; desf; eauto. *)
Qed.

Lemma SCOH_view_co t
      (TR: LTS_trace scoh_lts t)
      (ND: trace_nodup (trproj t)) x y
      (REL: myco t x y) :
    (view_of' t x) (loc x) < (view_of' t y) (loc x).
Proof using.
  unfold myco in *; desf.
  destruct x; ins; ins; rewrite view_of_init.
  all: erewrite !view_of_match in *; eauto.
  { erewrite LOC, view_of_write; eauto.
    destruct My; ins; desf; ins; lia. }
  rewrite LOC at 2.
  erewrite !view_of_write; eauto.
Qed.

Lemma SCOH_view_rf_loc t
      (TR: LTS_trace scoh_lts t)
      (ND: trace_nodup (trproj t)) x y
      (REL: myrf t x y) :
  (view_of' t y) (loc x) = ifP is_w y then
                             S (view_of' t x (loc x))
                           else
                             view_of' t x (loc x).
Proof using.
  unfold myrf in *; desf.
  1-2: destruct x; ins; ins; rewrite view_of_init.
  all: erewrite !view_of_match in *; try eassumption; eauto.
  all: try erewrite view_of_write with (yl := xl) (y := x); eauto.
  1: erewrite LOC, view_of_write; eauto.
  3: rewrite LOC at 1; erewrite view_of_write; eauto.
  all: rewrite match_evE in *; desf.
  all: destruct (LTS_traceE _ _ TR) as (mem & INIT & STEP); desf.
  all: eapply trace_in_nth with (d := deflabel) in ELy;
       destruct ELy as (m & M); desc.
  all: destruct (STEP) with (i := m) (d := deflabel);
    ins; rewrite EQ in *; ins; desf.
  all: ins; desf.
  all: unfold view_join, upd; ins; desf.
  all: eapply Nat.max_l.
  all: eapply view_of_msg_wf with (d := deflabel) in MSG; eauto.
  all: ins; lia.
Qed.

Lemma SCOH_view_fr t
      (TR: LTS_trace scoh_lts t)
      (ND: trace_nodup (trproj t)) x y
      (REL: fr {|
         acts := fun x => is_init x \/ trace_elems (trproj t) x;
         rf := myrf t;
         co := myco t |} x y) :
    (view_of' t x) (loc x) < (view_of' t y) (loc x).
Proof using.
  red in REL; ins; unfolder in REL; desf; clarify_not.
  assert (RF:= REL); apply SCOH_view_rf_loc in REL; ins.
  assert (LEQ: loc x = loc z) by (unfold myrf in *; desf).
  rewrite LEQ.
  assert (CO:= REL1); apply SCOH_view_co in REL1; ins; desf; try lia.
  destruct (classic (view_of' t x (loc z) = view_of' t y (loc z)))
    as [VEQ|]; try lia.
  destruct REL0.
  assert (is_w y) by (unfold myco in *; desf).
  assert (LEQ': loc y = loc z) by (unfold myco in *; desf).
  assert (INx: is_init x \/ trace_elems (trproj t) x).
    by rewrite trace_elems_trproj; unfold myrf in *; desf; eauto.
  assert (INy: is_init y \/ trace_elems (trproj t) y).
    by rewrite trace_elems_trproj; unfold myco in *; desf; eauto.
  rewrite <- LEQ' in *; clear LEQ' REL REL1 RF CO.
  rewrite trace_elems_trproj in *.
  unfold is_init in *; desf;
    try solve [unfold loc in *; ins; desf].
  all: try rewrite ?view_of_init in *.
  all: erewrite !view_of_match in *; eauto.
  erewrite <- LEQ, view_of_write in VEQ; eauto; destruct INx0; desf.
  erewrite view_of_write in VEQ; eauto; destruct INy0; desf.

  rewrite <- LEQ in VEQ at 1;
    erewrite !view_of_write in VEQ; eauto.
  eapply SCOH_uniq_ts in VEQ; eauto.
  destruct INx0, INy0; ins; desf.
Qed.

Lemma SCOHG_wf t
      (TR: LTS_trace scoh_lts t)
      (WF : trace_wf (trproj t))
      (TWF : trace_no_init_tid (trproj t)) :
  Wf {| acts := is_init ∪₁ trace_elems (trproj t);
        rf := myrf t; co := myco t |}.
Proof using.
  assert (ND: trace_nodup (trproj t)) by auto.

  assert (U : uniq_ts (trace_elems t))
    by eauto using SCOH_uniq_ts.

  split; ins; desf;
    eauto using myco_trans, myco_irrefl, myco_total, myrf_func.
  all: try apply dom_helper_2.
  all: unfold myco, myrf in *.
  all: try solve [unfolder; ins; desf; splits;
                  try rewrite trace_elems_trproj;
                  eauto with hahn;
                  destruct x; ins].
  3: solve [split; ins; unfolder; ins; desf; destruct My; desf].
  3: { unfold is_init; desf. split; desf. ins; desf.
       unfolder in ACT. simpls. desf.
       apply TWF in ACT. desf. }
  {
    unfold same_index in *; unfolder in *; desf; destruct a, b; ins; desf.
    1,2: by apply TWF in H; desf.
    red in WF.
    apply trace_in_nth with (d := InitEvent 0) in H; destruct H as (n & LTn & En).
    apply trace_in_nth with (d := InitEvent 0) in H0; destruct H0 as (m & LTm & Em).
    destruct (lt_eq_lt_dec n m) as [[LT|]|LT]; desf;
      try apply WF with (d := InitEvent 0) in LT; eauto;
        rewrite Em, En in *; ins; lia.
  }
  {
    destruct (LTS_traceE _ _ TR) as (mem & INIT & STEP); desf.
    {
      eapply trace_in_nth with (d := deflabel) in ELy; desf.
      unfold valw, valr; destruct w; ins.
      forward eapply SCOH_mem with (d := deflabel) as X; ins; eauto.
      unfold Minit in X.
      specialize (STEP _ ELy (deflabel)).
      destruct My, STEP; ins; rewrite EQ in *; ins; desf;
        apply X in MSG; unfolder in MSG; ins; desf.
      all: destruct (trace_nth y t (deflabel)); ins; desf.
    }
    {
      eapply trace_in_nth with (d := deflabel) in ELy; desf.
      unfold valw, valr.
      forward eapply SCOH_mem with (n := n) (d := deflabel) as X;
        ins; eauto.
      unfold Minit in X.
      destruct Mx, My; ins; desf; ins.
      rewrite EQl0 in *; ins; desf.
      specialize (STEP _ ELy (deflabel)).
      destruct STEP;
        rewrite EQ in *; ins; desf;
          apply X in MSG; unfolder in MSG; ins; desf;
            clear EQ.
      all: destruct (trace_nth y t (deflabel)) eqn: M; ins; desf.
      all: forward eapply U with
          (e := SCOH_event (ThreadEvent t0 i lab) tstamp view)
          (e' := trace_nth y t (deflabel))
          (x := ThreadEvent t0 i lab) as Z;
        eauto using match_ev, trace_nth_in with hahn; ins;
      try rewrite M; ins; rewrite <- Z in *; desf.
    }
  }
Qed.

Lemma SCOHG_rfcomplete t
      (TR: LTS_trace scoh_lts t)
      (WF : trace_wf (trproj t)) :
  rf_complete
    {| acts := is_init ∪₁ trace_elems (trproj t);
       rf := myrf t;
       co := myco t |}.
Proof using.
  unfold myrf; red; unfolder; ins; desf; unnw.
  1: by destruct x; ins.
  destruct (LTS_traceE _ _ TR) as (mem & INIT & STEP); desf.
  rewrite trace_elems_trproj in H; desc.
  eapply trace_in_nth with (d := deflabel) in H; desf.
  forward eapply SCOH_mem with (d := deflabel) as Y; ins; eauto.
  unfold Minit in Y.
  assert (M:=H1); destruct H1; desf.
  specialize (STEP _ H (deflabel)).
  rewrite EQl in STEP; destruct STEP; ins; desf;
    apply Y in MSG; clear Y; unfolder in MSG; ins; desf.
  1,3: eexists (InitEvent x); left; splits; ins; eexists; splits;
    eauto using trace_nth_in; try rewrite EQl; ins.
  all: red in MSG0; desf; ins; desf.
  all: eexists; right; exists (trace_nth y t (deflabel));
    splits; eauto using trace_nth_in, match_ev with hahn.
  all: eexists; splits; eauto using trace_nth_in;
    rewrite Heq, EQl; ins.
Qed.

Lemma SCOHG_consistent t
      (TR: LTS_trace scoh_lts t)
      (WF : trace_wf (trproj t)) :
  scoh_consistent {| acts := is_init ∪₁ trace_elems (trproj t);
                   rf := myrf t;
                   co := myco t |}.
Proof using.
  destruct (LTS_traceE _ _ TR) as (mem & INIT & STEP); desf.
  assert (irreflexive (hb {| acts := is_init ∪₁ trace_elems (trproj t);
                             rf := myrf t;
                             co := myco t |})) as PORF.
  { red; unfolder; splits; ins; desf.
    forward apply SCOH_hb_trord; eauto; lia. }
  red; unfolder; splits; ins; desf.
  2: { forward apply SCOH_view_fr; eauto.
       { split.
         { exists z. split; eauto. }
         intros HH. unfolder in HH. desf.
         eapply myco_irrefl; eauto. }
       forward apply SCOH_view_co; (try by apply H1); eauto.
       arewrite (loc z0 = loc x); [|lia].
       red in H1. desf. }
  red; ins. rewrite unionA.
  apply acyclic_union.
  { rewrite inclusion_restr_eq. apply PORF. }
  unfold fr; ins.
  intros x HH. apply ct_end in HH. destruct HH as [y [HH SS]].
  assert (forall p q
                 (PQ : (restr_eq_rel
                          loc
                          (sb
                             {|
                               acts :=
                                 fun x : Event => is_init x \/ trace_elems (trproj t) x;
                               rf := myrf t;
                               co := myco t
                             |}) ∪ myrf t)＊ p q),
             (view_of' t p) (loc p) <= (view_of' t q) (loc p) /\ loc p = loc q) as CC.
  { clear dependent x. clear y.
    ins. rename p into z. rename q into x.
    apply clos_rt_rt1n in PQ.
    induction PQ as [|x w p IND]; auto.
    desf.
    assert (loc x = loc w) as BB.
    { destruct IND as [AA|AA]; [by apply AA|].
      red in AA. desf. }
    rewrite BB. split; auto.
    etransitivity; [|by apply IHPQ].
    destruct IND as [[AA _]|AA].
    { apply SCOH_le_view_sb; auto. }
    apply SCOH_view_rf_loc in AA; auto.
    rewrite <- BB. rewrite AA.
    desf. lia. }
  assert (forall p q
                 (PQ : ((myco t ∪ (myrf t)⁻¹ ⨾ myco t \ ⦗fun _ : Event => True⦘)
                          ⨾ (restr_eq_rel
                               loc
                               (sb
                                  {|
                                    acts :=
                                      fun x : Event => is_init x \/ trace_elems (trproj t) x;
                                    rf := myrf t;
                                    co := myco t
                                  |}) ∪ myrf t)＊) p q),
             (view_of' t p) (loc p) < (view_of' t q) (loc p) /\ loc p = loc q) as AA.
  { clear dependent x. clear y.
    ins. rename p into y. rename q into x.
    destruct PQ as [z [S1 S2]].
    assert (view_of' t y (loc y) < view_of' t z (loc y) /\ loc y = loc z) as BB.
    { split.
      2: { destruct S1 as [S1|S1]; unfolder in S1; desf.
           { red in S1. desf. }
           red in S1; red in S3; desf.
           all: by rewrite <- LOC0. }
      destruct S1 as [S1|S1].
      { eapply SCOH_view_co; eauto. }
      eapply SCOH_view_fr; eauto. }
    desf. rewrite BB0.
    apply CC in S2. desf. splits; auto.
    rewrite BB0 in BB. lia. }
  apply AA in SS. desf.
  enough (view_of' t x (loc x) <= view_of' t y (loc x)).
  { rewrite SS0 in SS. lia. }
  clear SS SS0.
  enough (view_of' t x (loc x) <= view_of' t y (loc x) /\ loc x = loc y) as BB.
  { apply BB. }
  clear CC.
  apply clos_rt_rt1n in HH.
  induction HH as [|x w p IND]; auto.
  desf. clear HH. apply AA in IND. clear AA. desf.
  split.
  2: by etransitivity; eauto.
  rewrite IND0 in *. lia.
Qed.

Lemma set_finite_helper_inh A (s : A -> Prop) :
  (forall a, s a -> set_finite s) -> set_finite s.
Proof using.
  tertium_non_datur (exists a, s a); desf; eauto.
  exists nil; ins; eauto.
Qed.

Lemma set_finite_singl A (s : A -> Prop)
      (INJ: forall a (Sa : s a) b (Sb : s b), a = b) :
  set_finite s.
Proof using.
  ins; apply set_finite_helper_inh; ins.
  exists (a :: nil); ins; eauto.
Qed.

Lemma fsupp_co t (TR : LTS_trace scoh_lts t)
      (ND : trace_nodup (trproj t)) :
  fsupp (myco t).
Proof using.
  red; ins.
  destruct (classic (trace_elems (trproj t) y)) as [N|N];
    rewrite trace_elems_trproj in *; desf.
  2:{ exists nil; unfold myco; ins; desf; unfolder in *; desf; eauto. }
  destruct N0; desf.
  assert (FIN:
            set_finite (trace_elems t
                          ∩₁ is_external
                          ∩₁ proj_ev ↓₁ is_w
                          ∩₁ proj_ev ↓₁ (fun x => loc x = loc_l lab)
                          ∩₁ (fun x => write_ts x < S tstamp))).
  {
    arewrite ((fun x => write_ts x < S tstamp) ≡₁
              ⋃₁ y < S tstamp, fun x => write_ts x = y)
      by (unfolder; intuition; desf; eauto).
    repeat first [rewrite <- set_bunion_inter_compat_l |
                  rewrite <- set_bunion_inter_compat_r ].
    rewrite set_finite_bunion; auto with hahn; intros ts TS.

    apply set_finite_singl; unfolder; ins; desf.
    eapply SCOH_uniq_ts; try eapply match_evE; eauto; congruence.
  }
  unfolder in FIN; desc.
  exists (InitEvent (loc_l lab) :: map proj_ev findom).
  unfold myco; ins; desf.
  { unfold loc in *; destruct x; ins; desf; eauto. }
  assert (yl = SCOH_event (ThreadEvent t0 i lab) tstamp view)
    by (eapply tr_scoh_nodup; vauto); desf.
  specialize (FIN xl); destruct Mx; desf; ins.
  right; rewrite in_map_iff; eexists (SCOH_event _ _ _);
    split; ins; apply FIN; splits; ins.
Qed.

Lemma fsupp_rfr s t (TR : LTS_trace_param scoh_lts s t)
      (FAIR : run_fair s t)
      (ND : trace_nodup (trproj t)) :
  fsupp (⦗fun x => ~ is_w x⦘ ⨾ (myrf t)⁻¹ ⨾ myco t).
Proof using.
  unfolder; ins.
  destruct (classic (trace_elems (trproj t) y /\ is_w y)) as [N|N];
    rewrite trace_elems_trproj in *; desf.
  2:{ exists nil; unfold myco; ins; desf; unfolder in *; desf; eauto. }
  destruct N1; desf.

  assert (FIN:
            set_finite (trace_elems t
                          ∩₁ is_external
                          ∩₁ (fun x => view_of x (loc_l lab) < S tstamp))).
  {
    arewrite ((fun x => view_of x (loc_l lab) < S tstamp) ≡₁
              ⋃₁ y < S tstamp, fun x => view_of x (loc_l lab) = y)
      by (unfolder; intuition; desf; eauto).
    repeat first [rewrite <- set_bunion_inter_compat_l |
                  rewrite <- set_bunion_inter_compat_r ].
    rewrite set_finite_bunion; auto with hahn; intros ts TS.
    destruct t; [exists l; unfolder; ins; desf; done|]; ins; desf.
    apply set_finite_nat_bounded in FAIR. desf.

    arewrite ((fun a => exists n0 : nat, a = fl n0) ∩₁ is_external ≡₁
                 (fun a => exists n0 : nat, a = fl n0) ∩₁ is_external
                 ∩₁ ⋃₁ i < bound, fun x => tid_of x = i).
    { unfolder; intuition; desf; eauto.
      eexists. splits; [|by eauto].
      apply FAIR. apply FAIR0; eauto. }

    repeat first [rewrite <- set_bunion_inter_compat_l |
                  rewrite <- set_bunion_inter_compat_r ].
    rewrite set_finite_bunion; auto with hahn; intros t' TID.
    apply set_finite_helper_inh; intros a A.
    unfolder in A; desf.
    
    edestruct FAIR1
      with (i := Nat.max n0 (S n)) (tid := tid (proj_ev (fl n0)))
           (x := loc_l lab)
           (tstamp := S tstamp)
      as [j F]; clear FAIR1; desf.
    { destruct (fl n0) eqn:HH; ins; desf.
      arewrite (thread = tid_of (fl n0)) by (by rewrite HH).
      apply FAIR0; eauto. }
    {
      eapply Nat.max_lub_l in F.
      exists (map fl (List.seq 0 (S j))); unfolder; ins; desf.
      in_simp; eexists; split; ins; in_simp.
      rewrite Nat.le_lteq in F; desf; [|by rewrite F0 in *].
      rewrite <- Nat.le_succ_l in F.
      eapply SCOH_view_mono
        with (mytid := tid_of (fl n0)) (x := loc_l lab) in F;
        eauto.
      forward eapply SCOH_step_view_ext with (lab := fl n0) as [_ VEQ]; eauto.
      rewrite Nat.lt_succ_r.
      destruct (TR0 j); ins; rewrite F0 in *; desf; ins.
      destruct (le_lt_dec n1 j) as [|LT]; ins; try lia; exfalso.
      rewrite <- Nat.le_succ_l in LT.
      eapply SCOH_view_mono
        with (mytid := tid (proj_ev (fl n0))) (x := loc_l lab) in LT;
        eauto.
      rewrite VIEW, !upds in LT; ins; clear VIEW.
      forward eapply SCOH_step_view_ext with (lab := fl n1) as [Y YY]; eauto.
      specialize (Y (loc_l lab)).

      destruct (fl n); ins; desf; destruct (fl n0); ins.
      destruct (fl n1); ins; desf.
      simpl in *. clarify. lia. 
    }

    (* destruct (constructive_indefinite_description); ins. *)
    (* clear fl; rename x into fl', a into TR; desc. *)
    exists (map fl (List.seq 0 (S j))); unfolder; ins; desf.
    in_simp; eexists; split; ins; in_simp.
    rewrite Nat.lt_succ_r.
    destruct (le_lt_dec n1 j) as [|LT]; ins; try lia; exfalso.
    apply Nat.lt_le_incl in LT.
    eapply SCOH_view_mono
      with (mytid := tid_of (fl n0)) (x := loc_l lab) in LT;
      eauto.
    edestruct SCOH_step_view_ext with (lab := fl n1) as [X _]; eauto.
    specialize (X (loc_l lab)).
    forward eapply (SCOH_mem (trace_inf fl))
      with (n := j) (d := deflabel) as MEM; ins; eauto.
    apply proj2 in MEM.
    rewrite set_subset_union_l in MEM; apply proj2 in MEM.
    
    specialize (MEM (SCOH_wmsg (fl n))); specialize_full MEM.
    { apply Nat.max_lub_r in F; exists n; split; try lia.
      rewrite <- N; unfolder; eexists; splits; ins.
      destruct lab; ins. }
    
    rewrite <- N in MEM.
    destruct (s j) eqn:SJ, (s n1) eqn:SN1. simpl in *.
    destruct (fl n) eqn:FLn; [| vauto]. destruct (fl n0) eqn:FLn0; [| vauto]. destruct (fl n1) eqn:FLn1; [| vauto]. simpl in *.
    clarify.
    destruct e0, e1; try done. simpl in *. clarify.
    destruct lab; simpl in *; [done | |]. 
    all: eapply F0 with (_, _), SCOHstep_internal; try eassumption; ins; lia. 
  }
  assert (LTS_trace scoh_lts t) as LTSTR.
  { red. desf; exists s; apply TR. }
  clear FAIR.
  unfolder in FIN; desc.
  exists (map proj_ev findom); ins; desf; in_simp.
  assert (LEQ: loc z = loc_l lab) by (red in REL1; desf; ins).
  eapply SCOH_view_co in REL1; ins.
  assert (RF := REL0); eapply SCOH_view_rf_loc in REL0; ins; desf.
  rewrite <- REL0 in REL1; clear REL0.
  erewrite view_of_match with (x := ThreadEvent t0 i lab) in REL1;
    vauto; ins.
  eapply view_of_write in N; vauto; unfold loc in N; ins.
  rewrite <- LEQ in *; rewrite N in *.
  red in RF; desf; exists yl; split;
    try apply FIN; splits; ins;
      try solve [destruct My; ins; desf];
      erewrite view_of_match in REL1; eauto.
Qed.


Lemma SCOH_op_implies_decl s t
      (TR: LTS_trace_param scoh_lts s t)
      (WF : trace_wf (trproj t))
      (TWF : trace_no_init_tid (trproj t))
      (FAIR: run_fair s t) :
  exists G,
    trace_elems (trproj t) ≡₁ acts G \₁ is_init /\
    Wf G /\ mem_fair G /\
    rf_complete G /\
    scoh_consistent G.
Proof using.
  assert (ND: trace_nodup (trproj t)) by auto.
  assert (LTS_trace scoh_lts t) as LTSTR.
  { red. desf; exists s; apply TR. }
  assert (U : uniq_ts (trace_elems t)) by eauto using SCOH_uniq_ts.

  exists {| acts := is_init ∪₁ trace_elems (trproj t) ;
            rf := myrf t ; co := myco t |}; splits; ins;
    eauto using SCOHG_wf, SCOHG_rfcomplete, SCOHG_consistent.
  { unfolder; intuition.
    rewrite trace_elems_trproj in *; desf.
    destruct H1; desf. }
  split; ins; eauto using fsupp_co.
  rewrite frE; ins; eauto using SCOHG_wf, SCOHG_rfcomplete,
                    scoh_rmw_atomicity, SCOHG_consistent.
  unfold rfr; ins; eauto using fsupp_co, fsupp_rfr with hahn.
Qed.
