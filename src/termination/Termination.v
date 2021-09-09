Require Import Coq.Unicode.Utf8.
Parameter address : Type.
Implicit Types x y z a b : address.
Parameter value : Type.
Parameter dummy_value : value.
Implicit Types v w : value.

Parameter thread : Type.
Implicit Types T U : thread.

Implicit Types i j n m : nat.

Definition event := (thread * nat)%type.
Implicit Types e : event.

Inductive label := W x v | R x | bug | empty.
Implicit Types l : label.


Record graph := {
  events : event -> label;
  rf : event -> event;
  mo_max : address -> option event;
  size : thread -> option nat;
}.

Implicit Types G H : graph.

Definition eval_write G e :=
  match events G e with
  | W _ v => v
  | _ => dummy_value
  end.

Definition eval G e := 
  match events G e with
  | R _ => eval_write G (rf G e)
  | _ => dummy_value
  end.

Parameter register : Type.
Implicit Type r : register.
Definition state := register -> value.
Implicit Type s : state.

Definition update := register -> option value.
Implicit Type u : update.


Inductive instruction :=
| gen_event (ε : state -> label) (δ : state -> value -> update)
| await_while (κ : state -> bool) n
| terminated.

Definition apply_update s u r :=
  match u r with
  | Some v => v
  | None => s r
  end.


Definition program := (list instruction).
Require Import List.
Import ListNotations.

Require Import Lia.
Definition nth_Inst (p : program) n := nth n p terminated.
Coercion nth_Inst :  program >-> Funclass.

Parameter P : thread -> program.
Parameter initial_state : thread -> state.

Record complete_state := {
  pc : nat;
  local_state : state;
}.

Infix "<<" := apply_update (at level 100).


Fixpoint comp G n T := match n with
  | 0 => {| pc := 0 ; local_state := initial_state T |}
  | S n' => match P T (pc (comp G n' T)) with
    | gen_event ε δ => {| 
        pc := 1 + pc  (comp G n' T); 
        local_state := (local_state (comp G n' T)) << δ (local_state (comp G n' T)) (eval G (T,n'));
      |}
    | await_while κ n => {| 
        pc := if κ (local_state (comp G n' T)) then pc (comp G n' T) - n else 1 + pc (comp G n' T);
        local_state := local_state (comp G n' T);
      |}
    | terminated => comp G n' T
    end
  end.

Definition generated_label G n T := 
  match P T (pc (comp G n T)) with
  | gen_event ε δ => ε (local_state (comp G n T))
  | _ => empty
  end.

Definition await_length G n T :=
  match P T (pc (comp G n T)) with
  | await_while _ i => i
  | _ => 0
  end.

Definition await_failed G n T := 
  match P T (pc (comp G n T)) with
  | await_while κ _ => κ (local_state (comp G n T)) = true
  | _ => False
  end.

Definition in_size G T n :=
  match size G T with
  | None => True
  | Some s => s > n
  end.

Definition get_size G T := match size G T with None => 0 | Some n => n end.

Lemma not_in_size_has_size G T n : ¬ in_size G T n -> size G T = Some (get_size G T).
unfold in_size, get_size. destruct (size _ _) ; tauto.
Qed.

Lemma not_in_size_lt_size G T n : ¬ in_size G T n -> n ≥ get_size G T.
unfold in_size, get_size. destruct (size _ _) ; try tauto.
lia.
Qed.


Definition tid e := let (T,_) := e in T.
Definition idx e := let (_,n) := e in n.

Notation in_graph G e := (in_size G (tid e) (idx e)).


Definition valid G := forall e x, in_graph G e -> 
    events G e = R x -> 
      in_graph G (rf G e) ∧ (tid e = tid (rf G e) -> idx (rf G e) < idx e) ∧ ∃ v, events G (rf G e) = W x v.

Definition finite G := forall T, size G T ≠ None.

Lemma in_size_step G T n : in_size G T (S n) -> in_size G T n.
unfold in_size.
destruct (size _ _) ; eauto.
lia.
Qed.

Lemma in_size_monotonic G n T m : in_size G T m -> m ≥ n -> in_size G T n.
intros insz. induction 1 ; eauto using in_size_step.
Qed.


Lemma in_size_lt G n T m : in_size G T m -> m > n -> in_size G T n.
intros. eapply in_size_monotonic ; eauto. lia.
Qed.

#[local]
Hint Extern 1 =>
  match goal with
  | H : in_size ?myG ?myT ?mym |- in_size ?myG ?myT ?myn => 
    assert (myn ≤ mym) by eauto with math_help ; apply in_size_monotonic with (m:=mym) ; auto
  end : size_help.

Require Import PeanoNat.
Import Nat.



Lemma in_size_dec G T n : {in_size G T n} + {¬ in_size G T n}.
unfold in_size.
destruct (size _ _) as [m|]; eauto.
destruct (Compare_dec.le_lt_dec m n) ; eauto.
right. lia.
Qed.

Definition new_replace G T n e e' := if in_size_dec G T n then e else e'.

Definition repeat_index G T n := 
  let L := await_length G (get_size G T - 1) T in
    get_size G T - (L+1) + (n - get_size G T) mod (L+1).

Definition repeat_event G e := let (T,n) := e in new_replace G T n e
  (T,repeat_index G T n).

Lemma in_size_repeat G T n : in_size G T n -> repeat_event G (T,n) = (T,n).
intros.
unfold repeat_event.
unfold new_replace, repeat_index.
destruct (in_size_dec _ _) ; try tauto.
Qed.

Corollary in_graph_repeat G e : in_graph G e -> repeat_event G e = e.
destruct e.
apply in_size_repeat.
Qed.

Lemma fin_not_in_size G T n : finite G -> n ≥ get_size G T -> ¬ in_size G T n.
intros fin n_ge in_sz.
specialize (fin T).
unfold get_size, in_size in *.
destruct (size _ _) ; auto.
lia.
Qed.

#[local]
Hint Resolve in_size_step : induction_helpers.


Ltac size_dec := match goal with
| |- context [in_size_dec ?myG ?myT ?myn] => try (assert (¬ in_size myG myT myn) by eauto using fin_not_in_size with math_help) ; 
  destruct (in_size_dec myG myT myn) ; try tauto
end.


Definition is_await G n T := exists κ i,  P T (pc (comp G n T)) = await_while κ i.
Definition is_gen_event G n T := exists δ ε,  P T (pc (comp G n T)) = gen_event δ ε.
Definition is_terminated G n T := P T (pc (comp G n T)) = terminated.
Lemma full_inst_set G n T : is_await G n T \/ is_gen_event G n T \/ is_terminated G n T.
unfold is_await, is_gen_event, is_terminated.
edestruct (P _ _) ; eauto.
Qed.

Definition cons_P G := forall n T,
  in_size G T n -> events G (T, n) = generated_label G n T.



Lemma await_failed_is_await G n T : await_failed G n T -> is_await G n T.
unfold await_failed, is_await.
destruct (P _ _) ; eauto.
all: intros ; now exfalso.
Qed.

Axiom no_rf_from_failed_await : forall G n T m U k, valid G -> cons_P G ->
  in_size G U k -> in_size G T m ->
  (exists x, events G (U,k) = R x) -> rf G (U,k) = (T,n) -> await_failed G m T -> m - await_length G m T <= n <= m -> 
    T = U /\ m - await_length G m T <= k <= m.


Axiom no_nested_await : forall G n T m,
  await_failed G m T -> m - await_length G m T <= n < m -> ~ is_await G n T.


Lemma no_term_in_await G n T m :
  await_failed G m T -> m - await_length G m T <= n <= m -> ~ is_terminated G n T.
remember (m - n) as i.
revert n m Heqi.
unfold is_terminated.
induction i.
- intros n m Heqi in_F inbetween.
  replace n with m by lia.
  intros PC.
  unfold await_failed in *.
  rewrite PC in in_F.
  eauto.
- intros n m Heqi in_F inbetween.
  intros PC.
  apply IHi with (m:=m) (n:= S n) ; eauto ; try lia.
  simpl.
  now rewrite PC.
Qed.

Lemma failed_gen_event G n T m :
  await_failed G m T -> m - await_length G m T <= n < m -> is_gen_event G n T.
intros in_F in_between.
edestruct full_inst_set as [ C | [C | C] ]; eauto.
- exfalso.
  eapply no_nested_await ; eauto.
- exfalso.
  eapply no_term_in_await ; eauto.
  lia.
Qed.



Axiom not_too_long : forall G m T, await_length G m T <= pc (comp G m T).

Lemma slow_PC G m T : pc (comp G m T) <= m.
induction m ; eauto.
simpl.
destruct (P _ _) ; simpl ; try lia.
destruct κ ; lia.
Qed.


#[local]
Hint Extern 0 => 
    match goal with 
    | |- context [idx (?myT,?myn)] => unfold idx, tid in *
    | |- context [tid (?myT,?myn)] => unfold idx, tid in *
    | H : context [idx (?myT,?myn)] |- _ => unfold idx, tid in *
    | H : context [tid (?myT,?myn)] |- _ => unfold idx, tid in *
    end : math_help.
(*
Hint Extern 0 => 
    match goal with
    | H : (?myU,?mym) = rf ?myG ?mye |- context [rf ?myG ?mye] => rewrite <- H in *
    | H : (?myU,?mym) = rf ?myG ?mye, H' : context [tid (rf ?myG ?mye)] |- _ => rewrite <- H in H' ; simpl in H'
    | H : (?myU,?mym) = rf ?myG ?mye, H' : context [idx (rf ?myG ?mye)] |- _ => rewrite <- H in H' ; simpl in H'
    end : math_help. *)
#[local]
Hint Extern 0 =>
    now (match goal with 
    | |- context [await_length ?myG ?mym ?myT] => pose (not_too_long myG mym myT); pose (slow_PC myG mym myT)
    | _ => idtac
    end ; lia) : math_help.

Lemma failed_step G T m i :
  await_failed G m T -> i <= await_length G m T -> pc (comp G (i + m - await_length G m T) T) = i + pc (comp G (m - await_length G m T) T) .
intros in_F le_l.
induction i ; eauto.
replace (S i + m - await_length G m T) with (S (i + m - await_length G m T)) by eauto with math_help.
simpl. 
edestruct failed_gen_event with (n:=(i + m - await_length G m T)) as (δ & ε & is_gen) ; eauto with math_help.
rewrite is_gen. 
simpl.
lia. (* uses IH *)
Qed.

Corollary failed_full G T m :
  await_failed G m T -> pc (comp G (m - await_length G m T) T) = pc (comp G m T) - await_length G m T.
intros in_F.
replace m with (await_length G m T + m - await_length G m T) at 3 by eauto with math_help. 
rewrite failed_step ; eauto.
lia.
Qed.

Lemma after_failed G n T m i :
  await_failed G m T -> 
  i <= await_length G m T -> pc (comp G (i + 1 + m) T) = i + pc (comp G m T) - await_length G m T.
intros in_F in_repeat.
replace (i + pc (comp G m T) - await_length G m T) with (i + (pc (comp G m T) - await_length G m T)) by eauto with math_help.
induction i.
- simpl.
  edestruct await_failed_is_await as (κ & i & is_aw) ; eauto.
  unfold await_failed in in_F.
  unfold await_length.
  rewrite is_aw in *.
  now rewrite in_F.
- simpl.
  rewrite IHi ; try lia.
  rewrite <- failed_full ; eauto.
  rewrite <- failed_step ; eauto ; try lia.
  pose (slow_PC G m T).
  edestruct failed_gen_event with (n:=(i + m - await_length G m T))
    as (δ & ε & is_gen) ; eauto with math_help.
  now rewrite is_gen.
Qed.

  

  
   


Lemma failed_repeat_pc G n T m : 
  await_failed G m T -> 
  m - await_length G m T <= n <= m -> pc (comp G n T) = pc (comp G (await_length G m T + 1+n) T).
intros.
replace n with (n-(m-await_length G m T) + m-await_length G m T) at 1 by eauto with math_help.
rewrite failed_step ; eauto with math_help.
rewrite failed_full ; eauto.
replace (await_length G m T + 1 + n) with (await_length G m T + n - m + 1  + m) by eauto with math_help.
rewrite after_failed ; eauto with math_help.
Qed.

Lemma failed_repeat_pc_simple G n T m i : 
  await_failed G m T -> i = await_length G m T + 1+n ->
  m - await_length G m T <= n <= m -> pc (comp G n T) = pc (comp G i T).
intros.
subst.
now apply failed_repeat_pc.
Qed.






Definition independent_on {X} (f : state -> X) (R : register -> Prop) :=
  forall s s' : state, (forall r, ~ R r -> s r = s' r) -> f s = f s'.

Module show_equivalence_depends_on.
  Definition depends_on {X} (f : state -> X) (R : register -> Prop) :=
    exists s s' : state, (forall r, ~ R r -> s r = s' r) /\ f s <> f s'.
  Goal forall X (f : _ -> X) R, (forall x y : X, x = y \/ x <> y) -> independent_on f R <-> ~ depends_on f R.
    intros X f R dec.
    split.
    - intros indp (s & s' & same & neq).
      eauto.
    - intros ndep s s' same.
      edestruct dec ; eauto.
      destruct ndep.
      exists s, s'.
      eauto.
  Qed.
End show_equivalence_depends_on.

Definition inst_independent_on inst R :=
  match inst with
  | gen_event ε δ   => independent_on ε R /\ independent_on δ R
  | await_while κ _ => independent_on κ R
  | _ => True
  end.


Infix "∪" := (fun A B r => A r \/ B r) (at level 90).
Infix "∩" := (fun A B r => A r /\ B r) (at level 90).
Notation "∁ A" := (fun r => ~ A r) (at level 85).
Notation "∅" := (fun r => False).

Axiom empty_independent : forall U i, inst_independent_on (P U i) ∅.


Definition out G n T r := 
  match P T (pc (comp G n T)) with
  | gen_event _ δ => δ (local_state (comp G n T)) (eval G (T,n)) r <> None
  | _ => False
  end.





Fixpoint total_out G n T i :=
  match i with
  | 0 => ∅
  | S i' => total_out G n T i' ∪ out G (i'+n) T
  end.

Module alternative_visible_out.
  Fixpoint visible_out' G n T i :=
    match i with 
    | 0 => out G n T
    | S i' => visible_out' G n T i' ∩ ∁ out G (n+i) T
    end.
  Goal forall G n T i r, visible_out' G n T i r <-> (out G n T ∩ ∁ total_out G (1+n) T i) r.
    induction i ; simpl ; eauto.
    - tauto.
    - intros r.
      rewrite IHi.
      simpl.
      replace (n + S i) with (i + S n) by lia.
      tauto.
  Qed.
End alternative_visible_out.

Definition no_rrf G n m T :=
  inst_independent_on (P T (pc (comp G m T))) (out G n T ∩ ∁ total_out G (1+n) T (m-n-1)).


(* this axiom might be too strong, it would be better to have a version that uses cons_P, valid, in_size G T k *)
Axiom no_rrf_failed_await : forall G n m T, 
  await_failed G m T -> m - await_length G m T <= n <= m -> forall k, k > m -> no_rrf G n k T.

Lemma only_out_changed G n T i : 
  forall r,  (∁ total_out G n T i) r -> local_state (comp G (i + n) T) r = local_state (comp G n T) r.
induction i ; eauto.
simpl.
intros r no_total_out.
assert (no_out_before : ¬ total_out G n T i r) by tauto.
assert (no_out_now : ¬ out G (i+n) T r) by eauto.
remember (P T (pc (comp G (i + n) T))) as inst.
destruct inst ; simpl ; eauto.
unfold out in *.
rewrite <- Heqinst in *.
assert (not_changed : δ (local_state (comp G (i + n) T)) (eval G (T, i + n)) r = None).
{ destruct (δ _ _) ; eauto.
  exfalso. apply no_out_now. discriminate. 
}
unfold apply_update.
rewrite not_changed.
eauto.
Qed.

Definition parallel_invariant G G' n n' T R := 
  (forall r, (∁ R) r -> local_state (comp G n T) r = local_state (comp G' n' T) r) /\  pc (comp G n T) = pc (comp G' n' T).

Lemma parallel_invariant_stable G G' n n' T (R R' : register -> Prop) :
  (forall r, R r -> R' r) ->
  parallel_invariant G G' n n' T R -> parallel_invariant G G' n n' T R'.
unfold parallel_invariant.
intuition.
Qed.


Lemma run_parallel_independent_gen G G' n n' T R :
  parallel_invariant G G' n n' T R ->
  inst_independent_on (P T (pc (comp G n T))) R ->
    generated_label G n T = generated_label G' n' T.
intros (same_state & same_pc) indep.
unfold inst_independent_on in *.
unfold out, generated_label, is_gen_event in *.
rewrite <- same_pc.
destruct (P T _) ; repeat split ; eauto ; simpl ; try now intuition.
Qed.



Lemma run_parallel_independent G G' n n' T R :
  parallel_invariant G G' n n' T R ->
  (eval G (T,n) = eval G' (T,n')) ->
  inst_independent_on (P T (pc (comp G n T))) R ->
    out G n T = out G' n' T
    ∧ parallel_invariant G G' (S n) (S n') T (R ∩ ∁ out G n T).
intros (same_state & same_pc) same_lres indep.
unfold inst_independent_on in *.
unfold out, generated_label, is_gen_event in *.
unfold parallel_invariant.
simpl.
rewrite <- same_pc.
destruct (P T _) ; repeat split ; eauto ; simpl ; try now intuition.
all : try (assert (eval_eq : eval G (T, n) = eval G' (T, n')) by eauto ; rewrite <- eval_eq).
- destruct indep as (indep_event & indep_state).
  rewrite same_lres.
  erewrite indep_state ; eauto.
- destruct indep as (indep_event & indep_state).
  erewrite indep_state in * ; eauto.
  intros r.
  intros set_step.
  unfold apply_update.
  destruct (δ _ _) ; simpl ; eauto 8.
- erewrite indep ; eauto.
Qed.

Corollary run_parallel_independent_simple G G' n n' T R :
  parallel_invariant G G' n n' T R ->
  (eval G (T,n) = eval G' (T,n')) ->
  inst_independent_on (P T (pc (comp G n T))) R ->
    parallel_invariant G G' (S n) (S n') T R.
intros.
eapply parallel_invariant_stable with (R:=R ∩ _) ; try apply run_parallel_independent ; eauto.
tauto.
Qed.

Lemma failed_dec G m T : {await_failed G m T}+{¬ await_failed G m T}.
unfold await_failed.
destruct (P _ _) ; eauto.
destruct (κ _) ; eauto.
Qed.

Lemma terminated_permanent G n T : is_terminated G n T -> is_terminated G (1+n) T.
unfold is_terminated.
intros Q.
simpl. now rewrite Q.
Qed.

Axiom eq_thread_dec : forall T U, {T=U} + {T ≠ U}.

Definition relabel_nat G n T m U := if eq_thread_dec T U then if Compare_dec.le_lt_dec (n - await_length G n T) m then
      m + await_length G n T + 1
    else
      m
  else m.

Definition relabel G n T e := match e with (U,m) => 
  (U, relabel_nat G n T m U) end.

Definition unlabel_nat G n T m U := if eq_thread_dec T U then
    if Compare_dec.le_lt_dec (n - await_length G n T) m then
      m - await_length G n T - 1
    else
      m
  else m.

Definition unlabel G n T e := match e with (U,m) => 
  (U, unlabel_nat G n T m U) end.

Lemma inv_label_nat G n T m U : unlabel_nat G n T (relabel_nat G n T m U) U = m.
unfold unlabel_nat, relabel_nat.
destruct (eq_thread_dec _ _) ; eauto.
destruct (Compare_dec.le_lt_dec _ m).
all  : destruct (Compare_dec.le_lt_dec _ _) ; try lia ; eauto.
Qed.

Lemma inv_label G n T e : unlabel G n T (relabel G n T e) = e.
destruct e as (U,m).
simpl.
now rewrite inv_label_nat.
Qed.
Arguments relabel_nat /.
Arguments unlabel_nat /.

Definition deleted G n T e := let (U,m) := e in
  T = U ∧ n - await_length G n T <= m <= n.


Lemma inv_unlabel G n T e : ¬ deleted G n T e -> relabel G n T (unlabel G n T e) = e.
destruct e as (U,m) ; simpl.
unfold deleted, unlabel.
intros not_del.
f_equal.
destruct (eq_thread_dec _ _) ; eauto with math_help.
destruct (Compare_dec.le_lt_dec _ m).
all  : destruct (Compare_dec.le_lt_dec _ _) ; eauto with math_help. 
- assert (Q :n < m ∨ n ≥ m) by lia.
  destruct Q ; eauto with math_help.
  exfalso ; eauto with math_help.
- exfalso ; eauto with math_help.
Qed.

Definition delete_one G m T := {|
  events := λ e , events G (relabel G m T e);
  rf := λ e, unlabel G m T (rf G (relabel G m T e));
  mo_max (* not used in the safety proof *) 
    := mo_max G;  
  size := λ U, match size G U with
              | None => None
              | Some s => Some (if eq_thread_dec T U then s - await_length G m T - 1 else s)
              end;
|}.

Lemma delete_one_no_label_change G m T e :
 ¬ deleted G m T e -> events (delete_one G m T) (unlabel G m T e) = events G e.
intros not_del.
unfold delete_one ; simpl.
rewrite inv_unlabel ; eauto.
Qed.




Lemma delete_one_no_eval_change G m T e:
 ¬ deleted G m T e -> (∀ x, events G e = R x -> ¬ deleted G m T (rf G e)) -> eval (delete_one G m T) (unlabel G m T e) = eval G e.
intros not_del_e not_del_rf.
unfold eval, eval_write.
simpl.
rewrite inv_unlabel ; eauto.
destruct (events G e) as [ | e' | | ]; eauto.
simpl.
rewrite inv_unlabel ; eauto.
Qed.


Lemma no_delete_other G m T U n :
  T ≠ U -> ¬ deleted G m T (U,n).
unfold deleted.
tauto. Qed.

Lemma no_relabel_other G m T U n :
  T ≠ U -> relabel_nat G m T n U = n.
intros.
simpl. destruct eq_thread_dec ; eauto.
tauto.
Qed.


Lemma no_unlabel_other G m T U n :
  T ≠ U -> unlabel_nat G m T n U = n.
intros.
simpl. destruct eq_thread_dec ; eauto.
tauto.
Qed.

Lemma no_unlabel_before G m T n :
  n < m - await_length G m T -> unlabel_nat G m T n T = n.
intros.
simpl. destruct eq_thread_dec ; eauto.
destruct (Compare_dec.le_lt_dec _ _) ; eauto.
lia.
Qed.

Lemma unlabel_after G m T n :
  n ≥ m - await_length G m T -> unlabel_nat G m T n T = n-await_length G m T-1.
intros.
simpl. destruct eq_thread_dec ; try tauto.
destruct (Compare_dec.le_lt_dec _ _) ; eauto.
lia.
Qed.



Lemma no_delete_before G m T n :
  n < m - await_length G m T -> ¬ deleted G m T (T,n).
unfold deleted.
lia.
Qed.

Lemma no_delete_after G m T n :
  n > m -> ¬ deleted G m T (T,n).
unfold deleted.
lia.
Qed.


Lemma no_relabel_before G m T n :
  n < m - await_length G m T -> relabel_nat G m T n T = n.
intros.
simpl. destruct eq_thread_dec ; eauto.
destruct (Compare_dec.le_lt_dec _ _) ; eauto.
lia.
Qed.





Lemma no_delete G m T e :
  await_failed G m T -> cons_P G -> valid G -> in_graph G e -> in_size G T m ->
  ¬ deleted G m T e -> (exists x, events G e = R x) -> ¬ deleted G m T (rf G e).
unfold deleted in *.
remember (rf G e) as e'.
destruct e' as (U',k').
destruct e as (U,k).
intros has_F consG val e_inG d_inG not_del is_r (T_eq_U & in_between ).
apply not_del.
subst.
eauto using no_rf_from_failed_await.
Qed.

Lemma no_delete_same_early G n T m :
  await_failed G m T -> n < m -> valid G -> in_size G T m ->
  ¬ deleted G m T (T,n) -> (exists x, events G (T,n) = R x) -> ¬ deleted G m T (rf G (T,n)).
unfold deleted in *.
intros has_F early val d_inG not_del isr.
remember (rf G (T,n)) as e.
destruct e as (U,k).
intros (T_eq_U & in_between ).
assert (k < n).
{ destruct isr as (x & isr).
  destruct val with (e:=(T,n)) (x:=x) as (inGr & mon & samex) ; eauto with size_help.
  rewrite <- Heqe in *.
  eauto with math_help size_help.
}
eauto with math_help.
Qed.

Lemma not_relabel_delete G n T m U : ¬ deleted G m T (relabel G m T (U,n)).
simpl.
destruct eq_thread_dec ; try tauto.
destruct Compare_dec.le_lt_dec ; try eauto with math_help.
Qed.


Lemma delete_one_no_eval_change_graph G m T e:
  await_failed G m T -> cons_P G -> valid G -> in_graph G e -> in_size G T m ->
 ¬ deleted G m T e -> eval (delete_one G m T) (unlabel G m T e) = eval G e.
intros awF consG valG inGe iszwe not_del_e.
apply delete_one_no_eval_change ; eauto using no_delete.
Qed.


(* insert possible unlabels *)
Ltac insert_missing_unlabel := match goal with
| |- context [ generated_label (delete_one ?myG ?mym ?myT) ?myn ?myU] =>
  replace (myn) with (unlabel_nat myG mym myT myn myU) ; [| now (unfold unlabel ; eauto using no_unlabel_before, no_unlabel_other with math_help) ]
| |- context [_ (delete_one ?myG ?mym ?myT) (?myU, ?myn)] =>
  replace ((myU,myn)) with (unlabel myG mym myT (myU,myn)) ; [| now (unfold unlabel ; eauto using no_unlabel_before, no_unlabel_other with math_help) ]
| |- context [ generated_label (delete_one ?myG ?mym ?myT) (?myn-await_length ?myG ?mym ?myT -1) ?myU] =>
  replace (myn-await_length myG mym myT -1) with (unlabel_nat myG mym myT myn myU) ; [| now (unfold unlabel ; eauto using unlabel_after with math_help) ]
| |- context[_ (delete_one ?myG ?mym ?myT) (?myU, ?myn-await_length ?myG ?mym ?myT -1)] =>
  replace ((myU,myn-await_length myG mym myT -1)) with (unlabel myG mym myT (myU,myn)) ; [| now (unfold unlabel ; eauto using unlabel_after with math_help) ]
end.
Ltac reduce_delete :=
(* reduce the expression *)
first [ rewrite delete_one_no_eval_change ; eauto 10 using not_relabel_delete, no_delete_before, no_delete_after, no_delete_other, no_delete, no_delete_same_early with math_help size_help
      | rewrite delete_one_no_label_change ; eauto using not_relabel_delete, no_delete_before, no_delete_after, no_delete_other with math_help
      (* | rewrite delete_one_no_rf_change ; eauto using not_relabel_delete, no_delete_before, no_delete_after, no_delete_other with math_help *)
      ].
Ltac delete_redundant_unlabel :=
(* clean up by removing unnecessary unlabels *)
unfold unlabel ; first 
  [ rewrite no_unlabel_before ; [| now eauto with math_help ]
  | rewrite no_unlabel_other ; [| now eauto with math_help ]
  | rewrite unlabel_after ; [| now eauto with math_help ]
  ].

Ltac simplify_delete := insert_missing_unlabel ; reduce_delete ; delete_redundant_unlabel.





Lemma delete_one_no_early_effect G n T m : cons_P G -> valid G -> in_size G T m ->
  await_failed G m T -> n ≤ m - await_length G m T -> comp (delete_one G m T) n T = comp G n T.
intros consG val f_inG has_F le_del.
induction n ; eauto.
simpl.
rewrite ! IHn ; try lia.
assert (eval G (T, n) = eval (delete_one G m T) (T,n)).
{ 
  unfold eval.
  simpl.
  destruct eq_thread_dec as [X|X] ; try contradiction.
  destruct Compare_dec.le_lt_dec ; try eauto with math_help.
  remember (events G (T,n)) as e.
  destruct e as [| | |]; eauto.
  simpl.
  unfold eval_write.
  rewrite delete_one_no_label_change ; eauto.

  assert (in_graph G (T,n)).
  { eapply in_size_lt ; eauto with math_help. }
  eapply no_delete ; eauto using no_delete_before.
}

assert (in_size G T n).
{ eapply in_size_lt ; eauto with math_help. }

destruct (P _ _) ; simpl ; eauto.
now rewrite H.
Qed.

Lemma independence_split X R R' (f : _ -> X) : (forall r, {R r} + {¬ R r}) -> independent_on f R -> independent_on f R' -> independent_on f (R ∪ R').
unfold independent_on.
intros inR_dec indR indR' s s' same_state.
pose (s'' := fun r => if inR_dec r then s' r else s r).
assert (forall r, ¬ R r -> s r = s'' r). 
{ unfold s''. intros r notInR.
  destruct (inR_dec _) ; eauto.
}
rewrite indR with (s':=s'') ; eauto.
apply indR'.
intros r notInR'.
unfold s''.
destruct (inR_dec _) ; eauto.
apply same_state.
intuition.
Qed.

Lemma independence_sub X (R R' : _ -> Prop) (f : _ -> X) : (forall r, R' r -> R r) -> independent_on f R -> independent_on f R'.
cbv.
eauto 10.
Qed.

Arguments minus : simpl nomatch.

Lemma out_dec G n T r : {out G n T r} + {¬ out G n T r}.
unfold out.
destruct (P _ _) ; eauto.
destruct (δ _ _) ; eauto.
left. discriminate.
Qed.

Lemma total_out_dec G n T i r : {total_out G n T i r} + {¬ total_out G n T i r}.
induction i ; eauto.
simpl.
destruct IHi ; eauto.
destruct (out_dec G (i+n) T r) ; eauto.
right.
tauto.
Qed.

Lemma and_dec A B : {A}+{¬ A} -> {B}+{¬ B} -> {A ∧ B} + {¬ (A ∧ B)}.
intros [] [] ; eauto.
all : right.
all : tauto.
Qed.

Lemma not_dec A : {A}+{¬ A} -> {¬ A} + {¬ ¬ A}.
intros [] ; eauto.
Qed.


Lemma total_out_split G n T i j r :
  total_out G n T (j+i) r <-> total_out G n T i r \/ total_out G (i+n) T j r.
induction j. 
- simpl. tauto. 
- simpl.
  replace (j + (i+n)) with (j+i+n) by lia.
  tauto.
Qed.



Lemma independence_split_total_out X (f : _ -> X) G n m T k :
    n <= m <= k ->
    (forall n', n <= n' <= m -> independent_on f (out G n' T ∩ ∁ total_out G (1 + n') T (k - n'))) ->
      independent_on f (total_out G n T (1+m-n) ∩ ∁ total_out G (1 + m) T (k - m)).
intros [n_le_m m_le_k].
revert m_le_k.
pattern m.
revert m n_le_m.
apply Coq.Init.Peano.le_ind.
- intros n_le_k indp.
  replace (1+n-n) with 1 by lia.
  simpl.
  eapply independence_sub ; eauto.
  tauto.
- intros m n_le_m IHm m_lt_k indp.
  replace (1 + (S m) - n) with (S (S m - n)) by lia.
  simpl.
  replace (S m - n + n) with (S m) by lia.
  apply independence_sub with (R:=λ r : register, out G (S m) T r ∧ ¬ total_out G (S (S m)) T (k - S m) r ∨ total_out G n T (S m - n) r ∧ ¬ out G (S m) T r ∧ ¬ total_out G (S (S m)) T (k - S m) r).
  { intros r.
    destruct (out_dec G (S m) T r) ; tauto.
  }
  apply independence_split ; eauto.
  + eauto using and_dec, out_dec, not_dec, total_out_dec.
  + apply independence_sub with (R:= λ r : register, total_out G n T (1 + m - n) r ∧ ¬ total_out G (1 + m) T (k - m) r).
    * simpl. intros r (t_bef & n_now & n_t_after).
      split ; auto.
      intros t_after.
      replace (k - m) with (k - S m + 1) in t_after by lia.
      rewrite total_out_split in t_after.
      destruct t_after as [n_bef | n_aft] ; eauto.
      apply n_now.
      simpl in n_bef.
      tauto.
    * apply IHm ; try lia.
      intros n' inbet.
      apply indp.
      lia.
Qed.



Corollary inst_independence_split_total_out I G n m T k :
    n <= m <= k ->
    (forall n', n <= n' <= m -> inst_independent_on I (out G n' T ∩ ∁ total_out G (1 + n') T (k - n'))) ->
      inst_independent_on I (total_out G n T (1+m-n) ∩ ∁ total_out G (1 + m) T (k - m)).
intros inbet indp.
destruct I ; simpl in * ; eauto.
all: repeat split.
all: apply independence_split_total_out ; eauto.
all: apply indp.
Qed.


Lemma delete_parallel_before G m T n : 
  cons_P G ->
  valid G ->
  in_size G T m ->
  await_failed G m T -> 
    n ≤ m - await_length G m T ->
    parallel_invariant G  (delete_one G m T) n n T ∅.
intros.
unfold parallel_invariant.
rewrite delete_one_no_early_effect ; eauto.
Qed.


Lemma failed_inst_independence_total_out G n T m k: 
  k ≥ m -> await_failed G m T -> m - await_length G m T <= n <= m -> 
      inst_independent_on (P T (pc (comp G (k+1) T))) (total_out G n T (1+m-n) ∩ ∁ total_out G (1 + m) T (k - m)).
intros.
apply inst_independence_split_total_out.
- lia.
- intros n' inbet.
  replace (k-n') with (k+1-n'-1) by lia.
  eapply no_rrf_failed_await ; eauto ; lia.
Qed.

Lemma failed_inst_independence_total_out_simple G n T m k i j : 
  k ≥ m -> await_failed G m T -> m - await_length G m T <= n <= m -> 
  i = (1+m-n) ->
  j = k - m ->
      inst_independent_on (P T (pc (comp G (k+1) T))) (total_out G n T i ∩ ∁ total_out G (1 + m) T j).
intros. subst.
now apply failed_inst_independence_total_out.
Qed.


Lemma failed_repeat_state G m T i : 
  cons_P G ->
  valid G ->
  in_graph G (T, i + m + 1) -> 
  await_failed G m T -> 
    parallel_invariant G  (delete_one G m T) (i+m+1) (unlabel_nat G m T (i+m+1) T)  T (total_out G (m - await_length G m T) T (await_length G m T+1) ∩ ∁ total_out G (S m) T i).
intros consG val f_inG in_F.
simpl. destruct (eq_thread_dec _ _) ; try tauto.
destruct (Compare_dec.le_lt_dec _ _) ; try lia.
replace (i + m + 1 - await_length G m T - 1) 
   with (i + (m - await_length G m T)) by eauto with math_help. 
induction i.
- simpl.
  unfold parallel_invariant.
  rewrite delete_one_no_early_effect ; eauto using in_size_monotonic with math_help.
  split ; eauto.
  + intros r not_out.
    replace (m+1) with (await_length G m T+1 + (m-await_length G m T)) at 1 by eauto with math_help.
    rewrite only_out_changed ; eauto.
  + rewrite failed_repeat_pc with (m:=m) (n:=m-_) ; eauto with math_help.
    f_equal. f_equal. eauto with math_help.

- simpl plus. simpl total_out.
  apply parallel_invariant_stable with (R := λ r : register,
     (total_out G (m - await_length G m T) T (await_length G m T + 1) r ∧ ¬ total_out G (S m) T i r) ∧ ¬ out G (i + S m) T r) ; try now intuition.
  replace (i + S m) with (i + m + 1) by lia.
  assert (m - await_length G m T ≤ i + m + 1) by lia.
  apply run_parallel_independent ; eauto using failed_inst_independence_total_out_simple with math_help induction_helpers.
  replace (i+(m-await_length G m T)) with (i+m+1-await_length G m T-1) by eauto with math_help.
  erewrite <- delete_one_no_eval_change_graph ; eauto using no_delete_after with size_help math_help.
  f_equal.
  simpl.
  destruct eq_thread_dec ; try contradiction.
  destruct Compare_dec.le_lt_dec ; eauto with math_help.
Qed.


Corollary failed_repeat_state_simpl G m T n : 
  cons_P G ->
  valid G ->
  in_graph G (T, n + 1) -> 
  await_failed G m T -> 
  n ≥ m ->
    parallel_invariant G  (delete_one G m T) (n+1) (unlabel_nat G m T (n+1) T)  T (total_out G (m - await_length G m T) T (await_length G m T+1) ∩ ∁ total_out G (S m) T (n-m)).
intros.
remember (n - m) as i.
replace (n+1) with (i+m+1) in * by lia.
now apply failed_repeat_state.
Qed.

Lemma delete_no_effect_others G m T n U : 
  cons_P G ->
  valid G ->
  in_size G T m ->
  in_size G U n ->
  await_failed G m T -> 
    T ≠ U -> 
    parallel_invariant G  (delete_one G m T) n n U ∅.
intros.
induction n. 
- unfold parallel_invariant. eauto.
- apply run_parallel_independent_simple ; eauto using empty_independent with size_help.
  erewrite <- delete_one_no_eval_change_graph ; eauto using no_delete_other with size_help.
  f_equal.
  simpl.
  destruct eq_thread_dec ; now try contradiction.
Qed.


Lemma in_size_delete G n T m U : in_size (delete_one G m T) U n -> in_size G U (relabel_nat G m T n U).
unfold in_size in *.
simpl in *.
remember (size G U) as s.
destruct s as [s|] ; eauto.
destruct (eq_thread_dec _ _) ; try lia.
destruct (Compare_dec.le_lt_dec _ _) ; try lia.
Qed.



Lemma not_deleted_parallel G n T m U :
  cons_P G -> 
  valid G ->
  in_size G T m ->
  await_failed G m T -> 
  ¬ deleted G m T (U,n) -> 
  in_size G U n ->
    ∃ R, parallel_invariant G (delete_one G m T) n (unlabel_nat G m T n U) U R ∧ inst_independent_on (P U (pc (comp G n U))) R.
intros consG val F_inG has_F not_del in_sz.
destruct n.
{ exists ∅.
  split ; eauto using empty_independent.
  simpl. destruct (eq_thread_dec _ _). 1: destruct (Compare_dec.le_lt_dec _ _).
  all : unfold parallel_invariant.
  all : eauto.
}
replace (S n) with (n+1) in *  by lia.
unfold unlabel_nat in *.
destruct (eq_thread_dec _ _).
- subst U.
  destruct (Compare_dec.le_lt_dec _ _).
  + assert (n ≥ m).
    { unfold deleted in *. 
      assert (¬ (m - await_length G m T ≤ n + 1 ∧ n + 1 ≤ m)) by tauto.
      lia.
    }
    exists ((total_out G (m - await_length G m T) T (await_length G m T + 1) ∩ ∁ total_out G (S m) T (n - m))).
    split.
    * rewrite <- unlabel_after ; eauto.
      unfold deleted in *.
      apply failed_repeat_state_simpl ; eauto with math_help.
    * apply failed_inst_independence_total_out_simple; eauto with math_help.
  + exists ∅.
    split.
    * apply delete_parallel_before ; eauto with math_help.
    * apply empty_independent.
- exists ∅.
  split.
  + apply delete_no_effect_others ; eauto with math_help.
  + apply empty_independent.
Qed.


Theorem cons_stable_delete G m T :
  valid G -> cons_P G -> in_size G T m -> await_failed G m T -> 
  cons_P (delete_one G m T).
unfold cons_P.
intros val gen_label in_F is_F n U in_size_del.
assert (in_size_before_del := in_size_delete _ _ _ _ _ in_size_del).
edestruct not_deleted_parallel with (m:=m) as (REG & par & indp) ; eauto using not_relabel_delete with math_help.
  rewrite inv_label_nat in *.
erewrite <- run_parallel_independent_gen  ; eauto.
rewrite <- gen_label ; eauto.
Qed.

Definition repeat_iteration_limit G m T limit :=
  forall i, i < limit -> eval G (T,i+m+1) = eval G (T,i+m-await_length G m T).

Notation repeat_iteration G m T := (repeat_iteration_limit G m T (await_length G m T + 1)).

Lemma parallel_invariant_transitive G G' G'' n n' n'' T R :
  parallel_invariant G G' n n' T R ->  parallel_invariant G' G'' n' n'' T R ->  parallel_invariant G G'' n n'' T R.
unfold parallel_invariant.
intros (p1A & p1B) (p2A & p2B).
split ; eauto.
- intros.
  rewrite p1A ; eauto.
- etransitivity ; eauto.
Qed.

Lemma parallel_invariant_symmetric G G' n n' T R :
  parallel_invariant G G' n n' T R ->   parallel_invariant G' G n' n T R.
unfold parallel_invariant.
intros (p1A & p1B).
split ; eauto.
intros.
rewrite p1A ; eauto.
Qed.


Lemma run_repeat_iteration_limit G m T i n n' j limit :
  await_failed G m T ->
  repeat_iteration_limit G m T limit ->
  n = i+m+1 ->
  n' = i+m-await_length G m T ->
  j = await_length G m T + 1 - i ->
  limit ≤ await_length G m T + 1 ->
  i ≤ limit ->
    parallel_invariant G G n n' T (total_out G n' T j ∩ ∁ total_out G (1 + m) T i).
intros.
subst.
induction i.
- simpl.
  replace (await_length G m T + 1 - 0) with (await_length G m T + 1) by lia.
  split ; eauto.
  + intros.
    replace (m+1) with (await_length G m T + 1 + (m - await_length G m T)) by eauto with math_help.
    apply only_out_changed.
    tauto.
  + erewrite failed_repeat_pc with (n:=m - await_length G m T) ; eauto with math_help.
    do 2 f_equal.
    eauto with math_help.
- replace (S i + m - await_length G m T) with (S (i + m - await_length G m T))  by eauto with math_help.
  simpl.
  eapply parallel_invariant_stable with (R:= (total_out G (S (i + m - await_length G m T)) T (await_length G m T + 1 - S i) ∩ ∁ total_out G (S m) T i) ∩ ∁ out G (i + S m) T) ; try tauto.
  eapply parallel_invariant_stable with (R:= (total_out G (i + m - await_length G m T) T (await_length G m T + 1 - i) ∩ ∁ total_out G (S m) T i) ∩ ∁ out G (i + S m) T).
  { intros r ((inout & n_t_out) & n_out).
    repeat split ; eauto.
    replace (await_length G m T + 1 -i) with (await_length G m T - i+1) in * by lia.
    rewrite total_out_split in inout.
    destruct inout as [ Q | Q ] ; eauto.
    - simpl in Q. destruct Q ; try tauto.
      exfalso. apply n_out.
      replace (i + S m) with (i+m+1) by lia.
      edestruct run_parallel_independent as (same_out & _ & _) ; eauto using failed_inst_independence_total_out_simple  with math_help.
      now rewrite same_out.

    - now replace (await_length G m T + 1 - S i) with (await_length G m T - i) by lia.
  }
  replace (i + S m) with (i+ m +1) in * by lia.

  apply run_parallel_independent ; eauto with math_help.
  apply failed_inst_independence_total_out_simple ; eauto with math_help.
Qed.




Theorem run_repeat_iteration G m T i n n' j :
  await_failed G m T ->
  repeat_iteration G m T ->
  n = i+m+1 ->
  n' = i+m-await_length G m T ->
  j = await_length G m T + 1 - i ->
  i ≤ await_length G m T + 1 ->
    parallel_invariant G G n n' T (total_out G n' T j ∩ ∁ total_out G (1 + m) T i).
intros.
eapply run_repeat_iteration_limit ; eauto with math_help.
Qed.






Lemma deleted_bug_repeats G n T m U :
  await_failed G m T -> 
  repeat_iteration G m T ->
  deleted G m T (U,n) -> 
  generated_label G n U = bug ->
    generated_label G (n + await_length G m T + 1) U = bug.
intros has_F rep (is_U & inbetween) has_bug.
subst U.
rewrite <- has_bug.
eapply run_parallel_independent_gen ; eauto.
- eapply run_repeat_iteration with (i:=n - (m - await_length G m T)); eauto with math_help.
    
- eauto using failed_inst_independence_total_out_simple with math_help.
Qed.


Theorem deleted_bug_preserved G n T m U :
  cons_P G ->
  valid G ->
  in_graph G (U,n+await_length G m T+1) ->
  await_failed G m T -> 
  repeat_iteration G m T ->
  deleted G m T (U,n) -> 
  generated_label G n U = bug ->
    generated_label (delete_one G m T) n U = bug.
intros consG val in_sz has_F rep del_e has_bug.
destruct (del_e) as (is_U & inbetween).
subst U.
erewrite <- deleted_bug_repeats ; eauto.
symmetry.
replace n with (n+await_length G m T+1 - await_length G m T - 1) at 2 by eauto with math_help.
eapply run_parallel_independent_gen ; eauto.
- rewrite <- unlabel_after ; try lia.
  eapply failed_repeat_state_simpl ; eauto with math_help size_help.
- eauto using failed_inst_independence_total_out_simple with math_help.
Qed.

Theorem not_deleted_bug_preserved G n T m U :
  cons_P G -> 
  valid G ->
  in_size G T m ->
  in_size G U n ->  
  await_failed G m T -> 
  ¬ deleted G m T (U,n) -> 
  generated_label G n U = bug ->
    generated_label (delete_one G m T) (unlabel_nat G m T n U) U = bug.
intros consG val F_in in_sz has_F  no_del has_bug.
erewrite <- has_bug.
symmetry.
edestruct not_deleted_parallel with (m:=m) as (R & pi & indp) ; eauto with math_help.
eapply run_parallel_independent_gen ; eauto.
Qed.

(** safety proof complete: skipping a finite number of failed awaits 
  which repeat never changes the final state *)




Lemma await_failed_repeat G m T :
  await_failed G m T -> repeat_iteration G m T -> await_failed G (await_length G m T + m + 1) T.
intros has_F rep.
edestruct run_repeat_iteration with (n' := m) (j:=1) (n:=await_length G m T + m + 1) as (state_same & pc_same) ; eauto with math_help.

assert (has_F' : await_failed G m T) by auto.
unfold await_failed in has_F.
unfold await_failed.


specialize no_rrf_failed_await with (G:=G) (n:=m) (k:=await_length G m T + m+1) (T:=T) (m:=m).
unfold no_rrf.
simpl.
rewrite pc_same.
intros Q.


remember (P T (pc (comp G m T))) as I.
destruct I ; try tauto.

rewrite Q ; eauto with math_help.
intros r notR.
apply state_same.
replace (await_length G m T + m + 1 - m - 1) with (await_length G m T) in * by lia.
simpl.
tauto.
Qed.

Lemma await_failed_repeat_simple G m T i :
  await_failed G m T -> repeat_iteration G m T -> 
  i = await_length G m T + m + 1 -> await_failed G i T.
intros. subst.
now apply await_failed_repeat.
Qed.

Definition done G T := P T (pc (comp G (get_size G T) T)) = terminated.
Definition no_ext G :=
  (∃T, ¬ done G T) ∧
  (∀T, ¬ done G T -> get_size G T > 0 ∧ let m := get_size G T - 1 in await_failed G m T ∧ 
          ∀ n a x, m - await_length G m T <= n <= m -> 
                events G (T,n) = R x ->  Some (rf G (T,n)) = mo_max G x).

Lemma done_dec G T : {done G T} + {¬ done G T}.
unfold done.
destruct (P _ _) ; eauto.
all: right.
all: discriminate.
Qed.



(* greatly simplify proof by assuming no writes at all in failed iterations *)
Axiom no_write_from_failed_await : forall G n T m, valid G -> cons_P G ->
  in_size G T m ->
  await_failed G m T -> m - await_length G m T <= n <= m -> ∀ x v, events G (T,m) ≠ W x v.


Parameter dummy_address : address.
Definition address_of G e := match events G e with 
  | W a _ | R a => a 
  | _ => dummy_address
  end.


Definition fill_event G e := let (T,n) := e in new_replace G T n (rf G e)
    (rf G (repeat_event G e)).

(*
let (T,n) := e in new_replace G T n (rf G e)
  (let (e',_) := observable_non_empty G T n (address_of G (repeat_event G e)) in e').
*)

Definition extend G := {|
  events := λ e ,  events G (repeat_event G e);
  rf := λ e, rf G (repeat_event G e);
  mo_max := mo_max G;
  size := fun T => if done_dec G T then size G T else None;
|}.

Lemma same_address G e : address_of (extend G) e = address_of G (repeat_event G e).
reflexivity.
Qed.


Lemma ext_eval G T : valid G -> finite G -> no_ext G -> ∀ n, in_size G T n -> 
  eval G (T,n) = eval (extend G) (T,n).
intros val fin bug n insz.
unfold eval, eval_write. simpl.
specialize (val (T,n)).
unfold fill_event, repeat_event, new_replace.
destruct (in_size_dec _ _ _) ; try tauto.
destruct (rf G (T,n)) as (U,m).
destruct (events G (T,n)) ; eauto.
edestruct val ; eauto with size_help.
destruct (in_size_dec _ _ _) ; try tauto.
Qed.


Lemma in_size_repeat_index G T n : get_size G T > 0 -> in_size G T (repeat_index G T n).
intros has_sz.
unfold repeat_index.
unfold in_size.
unfold get_size in *.
destruct size as [SZ|] ; eauto.
assert (modL : _) by (apply mod_upper_bound with (a:=n - SZ) (b:=await_length G (SZ-1) T + 1) ; eauto with math_help).
eauto with math_help.
Qed.


Lemma in_graph_repeat_event G e : get_size G (tid e) > 0 -> in_graph G (repeat_event G e).
unfold repeat_event.
destruct e as (T,n).
unfold new_replace.
size_dec.
simpl.
now apply in_size_repeat_index.
Qed.


Lemma eval_rep G T e : get_size G (tid e) > 0 -> valid G ->
  eval G (repeat_event G e)  = eval (extend G) e.
intros inGe valG.
unfold eval.
simpl.
remember (events G (repeat_event G e)) as e'. 
destruct e' ; auto.
unfold eval_write.
simpl.
rewrite in_graph_repeat with (e:=rf G (repeat_event G e)) ; eauto.
edestruct valG as (inGr & _ & _) ; eauto using in_graph_repeat_event with size_help.
Qed.

Lemma ext_parallel G T : cons_P G -> valid G -> finite G -> no_ext G -> ∀ n, in_size G T n -> parallel_invariant G (extend G) n n T ∅.
intros consG val fin bug.
induction n ; eauto.
- intros _. unfold parallel_invariant. eauto.
- intros insz.
  apply run_parallel_independent_simple ; eauto using empty_independent with induction_helpers.
  eauto using ext_eval with size_help.
Qed.


Lemma ext_await G T :  cons_P G -> valid G -> finite G -> no_ext G -> ¬ done G T -> ∀ n, in_size G T n -> await_length G n T = await_length (extend G) n T.
intros.
unfold await_length.
edestruct ext_parallel as (same_state & same_pc) ; eauto.
now rewrite <- same_pc.
Qed.

Lemma no_ext_has_size G T : ¬ done G T -> no_ext G -> get_size G T > 0.
intros ndone (_ & allndone).
destruct allndone with (T:=T) ; eauto.
Qed.


#[local]
Hint Extern 0 =>
    now (match goal with 
    | |- context [get_size ?myG ?myT] => 
      assert _ by (apply no_ext_has_size with (G:=myG) (T:=myT) ; eauto)
    | _ => idtac
    end ; lia) : math_help.

Lemma no_ext_in_size G T : ¬ done G T -> no_ext G -> in_size G T (get_size G T - 1).
intros.
assert _ by (apply no_ext_has_size ; eauto).
unfold in_size, get_size in *.
destruct (size G T) ; eauto with math_help.
Qed.

#[local]
Hint Resolve no_ext_in_size : size_help.


Lemma no_ext_failed_await G T : cons_P G -> valid G -> finite G -> no_ext G -> ¬ done G T -> await_failed (extend G) (get_size G T - 1) T.
intros consG val fin bug ndoneG.
edestruct ext_parallel as (same_state & same_pc) ; eauto using ext_await, no_ext_in_size with size_help.
unfold await_failed.
rewrite <- same_pc.
unfold no_ext in bug.
destruct bug as [_ bug].
destruct (bug T) as (_ & has_F & _) ; eauto.
unfold await_failed in has_F.
remember (P _ _) as aw_instr.
destruct aw_instr ; eauto.
specialize empty_independent with (U:=T) (i:=pc (comp G (get_size G T - 1) T)).
rewrite <- Heqaw_instr.
simpl.
intros same_kappa.
rewrite <- same_kappa ; eauto.
Qed.


Lemma ext_repeat G T : cons_P G -> valid G -> finite G -> no_ext G -> ¬ done G T -> repeat_iteration (extend G) (get_size G T - 1) T.
intros consG val fin bug ndoneG.
unfold repeat_iteration. 
intros i in_F.
assert (await_failed (extend G) (get_size G T - 1) T) by eauto using no_ext_failed_await.

rewrite <- ! eval_rep ; eauto using no_ext_has_size.
f_equal.
unfold repeat_event, new_replace, repeat_index.
size_dec.
replace (i + (get_size G T - 1) + 1 - get_size G T) with i by eauto with math_help.
rewrite <- ext_await in * ; eauto with math_help size_help.
rewrite mod_small ; eauto with math_help.
replace (i + (get_size G T - 1) - await_length G (get_size G T - 1) T -
   get_size G T)
  with (i - (await_length G (get_size G T - 1) T + 1)) by eauto with math_help.
rewrite mod_small ; eauto with math_help.
assert (in_size G T
       (i + (get_size G T - 1) - await_length G (get_size G T - 1) T)).
{ eapply in_size_monotonic ;
 eauto with size_help math_help.
}
size_dec.
eauto with math_help.
Qed.





Lemma repeat_run_complete G m T :
    await_failed G m T ->
    repeat_iteration G m T ->
      parallel_invariant G G (await_length G m T + m + 1) m T ∅.
intros in_F rep.
eapply parallel_invariant_stable ; eauto using run_repeat_iteration with math_help.
intros r [outA outB].
replace (_ + 1 - _) with 1 in * by lia.
simpl in outA.
unfold out in *.
unfold await_failed in *.
destruct (P  _ _); try tauto.
Qed.


Lemma await_failed_parallel G G' n n' T :
  parallel_invariant G G' n n' T ∅ -> await_failed G n T -> await_failed G' n' T.
intros par has_F.
unfold await_failed in *.
destruct (par) as [same_state same_pc]. (* parentheses keep original version *)
rewrite <- same_pc.
specialize empty_independent with (U:=T) (i:=pc (comp G n T)).
unfold inst_independent_on.
destruct (P _ _) ; eauto.
intros indep.
rewrite <- indep ; eauto.
Qed.



Theorem ext_await_iter G T k : cons_P G -> valid G -> finite G -> no_ext G -> ¬ done G T -> 
  parallel_invariant (extend G) (extend G) 
    (get_size G T - 1) 
    (get_size G T - 1 + k * (await_length G (get_size G T - 1) T + 1)) T ∅
  ∧ await_failed (extend G) (get_size G T - 1 + k * (await_length G (get_size G T - 1) T + 1)) T
  ∧ repeat_iteration (extend G) (get_size G T - 1  + k * (await_length G (get_size G T - 1) T + 1)) T
  ∧ await_length G (get_size G T - 1) T = await_length (extend G) (get_size G T - 1 + k * (await_length G (get_size G T - 1) T + 1)) T.
intros consG val fin bug ndoneG.
induction k.
- replace (get_size G T - 1 + _) with (get_size G T - 1) by lia.
  repeat split ; eauto using ext_repeat, ext_await, no_ext_failed_await with size_help.

- destruct IHk as (par & F' & rep & aw).

  assert (F''  : await_failed (extend G) (get_size G T-1 + (S k) * (await_length G (get_size G T - 1) T + 1)) T)
  by eauto using await_failed_repeat_simple with math_help.

  assert (aw' : await_length G (get_size G T - 1) T =
    await_length (extend G) (get_size G T - 1 + S k * (await_length G (get_size G T - 1) T + 1)) T).
  { simpl.
    replace (get_size G T - 1 +
       (await_length G (get_size G T - 1) T + 1 + k * (await_length G (get_size G T - 1) T + 1)))
    with  (await_length G (get_size G T - 1) T + 1 + (get_size G T - 1 + k * (await_length G (get_size G T - 1) T + 1)))
    by eauto with math_help.
    unfold await_length at 2.
    rewrite after_failed ; eauto with math_help.
    rewrite <- aw.
    replace (await_length G (get_size G T - 1) T +
     pc (comp (extend G) (get_size G T - 1 + k * (await_length G (get_size G T - 1) T + 1)) T) -
     await_length G (get_size G T - 1) T)
    with (pc (comp (extend G) (get_size G T - 1 + k * (await_length G (get_size G T - 1) T + 1)) T))
    by eauto with math_help.
    now rewrite aw at 1.
  }
  
  assert (repeat_iteration (extend G) (get_size G T - 1 + S k * (await_length G (get_size G T - 1) T + 1)) T).
  {
    unfold repeat_iteration. 
    rewrite <- aw'.
    intros i in_F.
    unfold eval, eval_write.
    replace (S k) with (k+1) by lia.
    simpl.
    unfold new_replace.
    size_dec.
    size_dec.
    unfold repeat_index.

    rewrite <- mod_unique with (r:=i) (q:=k+1);  eauto with math_help.

    rewrite <- mod_unique with (r:=i) (q:=k);  eauto with math_help.
  }
  split ; [|split] ; eauto.
  eapply parallel_invariant_transitive ; eauto.
  apply parallel_invariant_symmetric.

  replace (get_size G T - 1 + S k * (await_length G (get_size G T - 1) T + 1))
  with (await_length G (get_size G T - 1) T + (get_size G T - 1 + k * (await_length G (get_size G T - 1) T + 1)) + 1)
  by lia.
  rewrite aw at 1.
  eapply repeat_run_complete ; eauto.
Qed.



Corollary ext_eval_iter G T i n m k :
  cons_P G -> valid G -> finite G -> no_ext G -> ¬ done G T ->
  i ≤ await_length G (get_size G T - 1) T ->
  n = get_size G T - (await_length G (get_size G T - 1) T + 1) + i ->
  m = get_size G T + k * (await_length G (get_size G T - 1) T + 1) + i ->
    eval (extend G) (T, m) = eval (extend G) (T, n).
intros.
subst.
induction k.
- simpl.
  edestruct ext_await_iter with (k:=0) as (par & F' & rep & aw) ; eauto.
  simpl in *.
  replace (get_size G T - 1 + 0) with (get_size G T- 1) in * by lia.
  replace (get_size G T + 0 + i) with (i + (get_size G T - 1) + 1) in * by eauto with math_help size_help.
  rewrite aw in *.
  rewrite rep ; eauto with math_help size_help.
  f_equal.
  f_equal.
  eauto with math_help size_help.
- edestruct ext_await_iter with (k:=S k) as (par & F' & rep & aw) ; eauto.

  rewrite <- IHk ; eauto.
  replace (get_size G T + k * (await_length G (get_size G T - 1) T + 1) + i)
    with ((get_size G T + (S k) * (await_length G (get_size G T - 1) T + 1) + i) - (await_length G (get_size G T - 1) T + 1)) 
    by eauto with math_help.
  rewrite aw at 3.
  replace (get_size G T + S k * (await_length G (get_size G T - 1) T + 1) + i) 
    with (i + (get_size G T - 1 + S k * (await_length G (get_size G T - 1) T + 1))+1)
    in *
    by eauto with math_help.
  rewrite rep ; eauto with math_help.
  f_equal.
  f_equal.

  eauto with math_help size_help.
Qed.


Lemma terminated_monotonic G T n m : P T (pc (comp G n T)) = terminated -> n ≤ m -> P T (pc (comp G m T)) = terminated.
intros term.
induction 1 ; eauto.
simpl.
now rewrite IHle.
Qed.

Theorem ext_infinite G T : cons_P G ->  valid G -> finite G -> no_ext G -> ¬ done G T -> ¬ ∃ n, P T (pc (comp (extend G) n T)) = terminated.
intros cons val fin bug ndoneG (n & term).
edestruct ext_await_iter with (k:=n) as ([same_state same_pc] & _ & _); eauto with math_help.
assert (is_term : P T (pc (comp (extend G) (get_size G T - 1) T)) = terminated).
{ rewrite same_pc.
  eauto using terminated_monotonic with math_help.
}
eassert _ by (apply no_ext_failed_await ; eauto).
unfold await_failed in *.
now rewrite is_term in *.
Qed.

Lemma fin_has_size G T : finite G -> size G T = Some (get_size G T).
unfold get_size, finite.
intros fin.
specialize (fin T).
now destruct (size _  _).
Qed.

Lemma inv_is_gen_event G G' n n' T R : parallel_invariant G G' n n' T R -> is_gen_event G' n' T -> is_gen_event G n T.
intros [_ same_pc].
unfold is_gen_event.
now rewrite same_pc.
Qed.

Lemma await_not_gen G n T : await_failed G n T -> ¬ is_gen_event G n T.
unfold await_failed, is_gen_event.
destruct (P _ _) ; eauto.
intros _ (δ & ε & bogus).
discriminate.
Qed.




Lemma repeat_run_same_out G m T i j n n' :
    await_failed G m T ->
    repeat_iteration G m T ->
    j ≤ await_length G m T + 1 - i ->
    n' = n - await_length G m T - 1 ->
    n = i + m + 1 ->
    i ≤ await_length G m T + 1 -> 
    forall r, 
      (total_out G n T j) r  ↔  (total_out G n' T j) r.
intros has_F rep defj defn' defn in_F.
subst n. subst n'.
replace (i+m+_-await_length G m T-_) with (i+m-await_length G m T) in * by lia.
revert i in_F defj.
induction j ; intros.
{ simpl. tauto. }
replace (S j) with (j+1) by lia.
rewrite ! total_out_split.
replace (1+(i+m+1)) with (S i + m+1) by eauto with math_help.
rewrite IHj ; eauto with math_help.
replace (S i + m - await_length G m T)
  with (S (i + m - await_length G m T))
  by eauto with math_help.
simpl. 
edestruct run_parallel_independent with (n' := i + m - await_length G m T) (n :=i + m + 1) as (same_out & _ & _) ; eauto using  run_repeat_iteration,      failed_inst_independence_total_out_simple with math_help.
now rewrite same_out.
Qed.


Lemma size_await G T :  ¬ done G T -> no_ext G ->  get_size G T ≥ await_length G (get_size G T - 1) T + 1.
intros. assert (get_size G T - 1 ≥ await_length G (get_size G T - 1) T) ; eauto with math_help.
Qed.

#[local]
Hint Resolve size_await : math_help.

Lemma ext_await_iter_all G T k n n' i j : cons_P G -> valid G -> finite G -> no_ext G -> ¬ done G T -> 
  n = get_size G T - (await_length G (get_size G T - 1) T + 1) + i ->
  n' = n + k * (await_length G (get_size G T - 1) T + 1) ->
  j ≤ await_length G (get_size G T - 1) T + 1 - i ->
  i ≤ await_length G (get_size G T - 1) T + 1 ->
  (∀ r, total_out (extend G) n' T j r ↔ total_out (extend G) n T j r) ∧ 
  (j = await_length G (get_size G T - 1) T + 1 - i -> parallel_invariant (extend G) (extend G) n n' T (total_out (extend G) n' T j ∩ ∁ total_out (extend G) (get_size G T - (await_length G (get_size G T - 1) T + 1) + k * (await_length G (get_size G T - 1) T + 1)) T i)).
intros consG val fin noext ndoneG.
revert n n' i j.
induction k.
- intros. subst. simpl.
  replace (get_size G T - (await_length G (get_size G T - 1) T + 1) + i + 0)
    with (get_size G T - (await_length G (get_size G T - 1) T + 1) + i) by lia.
  unfold parallel_invariant.
  tauto.
- assert (ISk_out : ∀ n n' i j : nat,
        n = get_size G T - (await_length G (get_size G T - 1) T + 1) + i
        → n' = n + (S k) * (await_length G (get_size G T - 1) T + 1)
          → j ≤ await_length G (get_size G T - 1) T + 1 - i
            → i ≤ await_length G (get_size G T - 1) T + 1
              → (∀ r : register,
                   total_out (extend G) n' T j r
                   ↔ total_out (extend G) n T j r)).
  { intros.
    edestruct IHk as (out_sub & par) ; eauto.
    rewrite <- out_sub.
    edestruct ext_await_iter with (k:=k) as (par' & F' & rep' & aw') ; eauto with math_help.
    eapply repeat_run_same_out with (i:=i) ; eauto with math_help.
  }

  intros.
  edestruct IHk as (out_sub & par) ; eauto.
  subst.
  split ; eauto.
  intros.

  (* want to apply one repeated iteration. need to: 
      1. transform into correct total_out 
      2. compare sz + .. + k * L vs sz + .. + (S k) * L
    To get to step 2), we need to use transitivity + IH which requires 
      total_out ( ... + k * ... )
    To prove they are equal, we need to use 
      total_out (... + (S k) * ... )
    *)

  assert (out_step : ∀ r, total_out (extend G)
           (get_size G T - (await_length G (get_size G T - 1) T + 1) +
            S k * (await_length G (get_size G T - 1) T + 1)) T i r ↔
          total_out (extend G)
           (get_size G T - (await_length G (get_size G T - 1) T + 1) +
            k * (await_length G (get_size G T - 1) T + 1)) T i r).
  { intros.
    rewrite ISk_out with (j:=i) (i:=0) (n:=get_size G T - (await_length G (get_size G T - 1) T + 1)) ; eauto 1 with math_help.
    edestruct IHk with (j:=i) (i:=0) (n:=get_size G T - (await_length G (get_size G T - 1) T + 1))  as (out_sub' & _) ; eauto 1 with math_help.
    rewrite <- out_sub'.
    reflexivity.
  }



  eapply parallel_invariant_stable.
  { intros r inR.
    rewrite ISk_out with (i:=i) ; auto.
    rewrite <- out_sub.
    rewrite out_step.
    apply inR.
  }

  eapply parallel_invariant_transitive ; eauto.

  eapply parallel_invariant_stable.
  { intros r inR.
    rewrite <- out_step.

    replace (get_size G T - (await_length G (get_size G T - 1) T + 1) + S k * (await_length G (get_size G T - 1) T + 1)) 
      with (1 + (get_size G T - 1  
              + k * (await_length G (get_size G T - 1) T + 1))) by eauto with math_help size_help.
    apply inR.
  }

  apply parallel_invariant_symmetric.

  edestruct ext_await_iter with (k:=k) as (par' & F' & rep' & aw') ; eauto.
  apply run_repeat_iteration; eauto with math_help.
Qed.


Theorem ext_await_iter_out G T k n n' i j : cons_P G -> valid G -> finite G -> no_ext G -> ¬ done G T -> 
  n = get_size G T - (await_length G (get_size G T - 1) T + 1)  + i ->
  n' = n + k * (await_length G (get_size G T - 1) T + 1) ->
  j = await_length G (get_size G T - 1) T + 1 - i ->
  i ≤ await_length G (get_size G T - 1) T + 1 ->
    ∀ r, total_out (extend G) n' T j r ↔ total_out (extend G) n T j r.
intros.
eapply ext_await_iter_all ; eauto with math_help.
Qed.

Theorem ext_await_iter_parallel G T k n n' i j : cons_P G -> valid G -> finite G -> no_ext G -> ¬ done G T -> 
  n = get_size G T - (await_length G (get_size G T - 1) T + 1) + i ->
  n' = n + k * (await_length G (get_size G T - 1) T + 1) ->
  j = await_length G (get_size G T - 1) T + 1 - i ->
  i ≤ await_length G (get_size G T - 1) T + 1 ->
    parallel_invariant (extend G) (extend G) n n' T (total_out (extend G) n' T j ∩ ∁ total_out (extend G) (get_size G T - (await_length G (get_size G T - 1) T + 1) + k * (await_length G (get_size G T - 1) T + 1)) T i).
intros.
eapply ext_await_iter_all ; eauto with math_help.
Qed.

Lemma inst_independent_on_sub I (R R' : register -> Prop) :
  (∀ r : register, R' r → R r) → inst_independent_on I R → inst_independent_on I R'.
intros sub_R.
destruct I ; simpl ; eauto using independence_sub.
intros [].
eauto using independence_sub.
Qed.

Theorem ext_consistent G : cons_P G ->  valid G -> finite G -> no_ext G -> cons_P (extend G).
intros consG val fin bug n T insz.
simpl.
unfold new_replace.
size_dec.
- eassert (par : _) by (eapply ext_parallel with (n:=n) ; eauto with math_help size_help).
  erewrite <- run_parallel_independent_gen ;  eauto using ext_eval, empty_independent with size_help.
- assert (¬ done G T).
  { intros doneG.
    unfold in_size, done, get_size in *.
    simpl in *.
    destruct (done_dec _ _) ; try tauto.
  }
  remember (await_length G (get_size G T - 1) T + 1) as L.
  eassert (n_split : _) by (apply div_mod with (x:=n-get_size G T) (y:=L) ; eauto with math_help).
  eassert (i_eq : _) by (apply mod_eq with (a:= n -get_size G T) (b:=L) ; eauto with math_help).
  remember ((n - get_size G T) /
           L) as k.
  remember ((n - get_size G T) mod L) as i.
  assert (n ≥ get_size G T).
  { unfold in_size in *.
    unfold get_size.
    clear insz.
    destruct (size _ _) ; try tauto.
    eauto with math_help.
  }
  assert (i < L). 
  { subst.  eauto using mod_upper_bound with math_help. }


  (** Note: this was an old part of the proof,
         when the final failed await was not in the graph.

  assert (i <  await_length G (get_size G T - 1) T).
  { assert (i ≠ await_length G (get_size G T - 1) T) ; eauto with math_help.
    intros bogus_eq.

    assert (n_simple : n  = get_size G T - 1 + (S k) * (await_length G (get_size G T - 1) T + 1))
    by eauto with math_help.

    edestruct ext_await_iter
      with (k:=S k)
      as (par & F' & rep & aw) ; eauto.

    rewrite <- n_simple in *.
    eapply await_not_gen ; eauto using no_ext_failed_await, inv_is_gen_event.
  }
  *)
    assert (n_simple : n  = get_size G T + k * L + i)
      by eauto with math_help.
    replace (repeat_index G T n) with (get_size G T - L + i).
    2 : {
      unfold repeat_index.
      rewrite <- HeqL.
      erewrite <- mod_unique  ; eauto with math_help.
    }
    assert (in_size G T (get_size G T - L + i)).
    { (* let lia know about L *) subst. 
      eapply in_size_monotonic ; eauto with size_help math_help.
    }
      

    rewrite consG ; eauto with size_help math_help.

    assert (same_eval : eval G (T, get_size G T - L + i) =
            eval (extend G) (T,n)). 
    { rewrite ext_eval ; eauto. symmetry. subst L. eapply ext_eval_iter with (i:=i) ; eauto with math_help. }

    assert (par_inv : parallel_invariant G (extend G) (get_size G T - L + i) n T
      (total_out (extend G) n T (L - i) ∩ ∁ total_out (extend G) (get_size G T - L + S k * L) T i)).
    { 
      eapply parallel_invariant_transitive.
      - apply parallel_invariant_stable with (R:=∅) ; eauto using ext_parallel.
        tauto.
      - assert (get_size G T ≥ L) by (subst ; eauto with math_help). subst L.
        apply ext_await_iter_parallel with (k:=S k) (i:=i) ; eauto with math_help.
    }
    
    eapply run_parallel_independent_gen with (G:=G) (n':=n) (n:=get_size G T - L + i) ; eauto.
    replace (n - get_size G T - L * k) with i by eauto with math_help.
    assert (get_size G T ≥ L) by (subst ; eauto with math_help).
    replace (get_size G T - L + S k * L)
      with (get_size G T  + k * L)
      by lia.
    replace (get_size G T + k * L)
      with ( 1 + (get_size G T - 1 + k * L))
      by eauto with math_help.
    replace (pc (comp G (get_size G T - L + i) T))
      with (pc (comp (extend G) (get_size G T + k * L + i) T)).
    2: { 
      destruct par_inv as (_ & same_pc).
      rewrite same_pc.
      now subst n.
    }

    eapply inst_independent_on_sub.
    { intros r Q.
      rewrite ext_await_iter_out with (n:=get_size G T - L + i) (k:=S k) in Q; eauto with math_help.
      rewrite <- ext_await_iter_out with (n:=get_size G T - L + i) (k:=k) in Q; eauto with math_help.
      rewrite <- HeqL in *.
      replace (get_size G T - L + i + S (S k) * L)
        with (get_size G T + i + (S k) * L)
        in *
        by eauto with math_help.
      apply Q.
    }


    replace (get_size G T + k * L + i)
      with ((get_size G T - 1+ k * L + i) + 1)
      by lia.

      
    edestruct ext_await_iter as (_ & is_F & _ & same_L) ; eauto with math_help.
  
    eapply failed_inst_independence_total_out_simple ; eauto 2 with math_help.
    + subst L. eauto.
    + split ; eauto with math_help.
      subst L.
      eauto with math_help.
Qed.








(*** no false positive complete. ***)



Lemma no_af_fwd G T n : (∀ m, m ≥ n -> ¬ await_failed G m T) -> ∀ i, pc (comp G (i+n) T) = i + pc (comp G n T) ∨ 
P T (pc (comp G (i+n) T)) = terminated.
intros nof.
induction i ; eauto.
simpl.
destruct IHi as [E|E].
- assert _ by (apply nof with (m:=i+n) ; eauto with math_help).
  rewrite <- E.
  unfold await_failed in *.
  remember (P _ _) as I.
  destruct I ; eauto.
  destruct (κ _) ; tauto.
- rewrite E ; eauto.
Qed.



Lemma out_of_P T n : n ≥ length (P T) -> P T n = terminated.
intros.
unfold nth_Inst.
replace (P T) with (P T ++ nil) by eauto using app_nil_end.
rewrite app_nth2 ; eauto.
destruct (n-_) ; eauto.
Qed.

Lemma finite_af_term G T : (∃ n, ∀ m, m ≥ n -> ¬ await_failed G m T) -> ∃ n, P T (pc (comp G n T)) = terminated.
intros (h & nfa).
exists (length (P T)+h).
destruct no_af_fwd with (i:=length (P T)) (G:=G) (n:=h) (T:=T) as [E|E] ; eauto.
rewrite E.
rewrite out_of_P ; eauto with math_help.
Qed.


Lemma dec_awf G m T  : {await_failed G m T} + { ¬ await_failed G m T}.
unfold await_failed.
destruct (P _ _) ; try now (right ; eauto with math_help).
destruct κ ; try now (right ; eauto with math_help).
left. eauto.
Qed.

Lemma dec_ge_awf m n G T : {m ≥ n ∧ await_failed G m T} + { ¬ (m ≥ n ∧ await_failed G m T)}.
destruct (Compare_dec.le_lt_dec n m) ; try now (right ; eauto with math_help).
destruct (dec_awf G m T) ; try now (right ; eauto with math_help).
eauto.
Qed.

Lemma finite_af_term_inv G T : 
  ¬ (∃ n, P T (pc (comp G n T)) = terminated) -> 
    (∀ n, ∃ m, m ≥ n ∧ await_failed G m T).
intros no_term n.
assert (term_eventually : ∀ k, pc (comp G (k+n) T) = k + pc (comp G n T) ∨ ∃ m : nat, m ≥ n ∧ await_failed G m T).
{ 
  induction k ; eauto.
  destruct IHk as [PC|]; eauto.
  simpl.
  remember (P _ _) as I.
  assert (I ≠ terminated) by (subst ; eauto).
  destruct I ; simpl ; eauto with math_help ; try tauto.
  remember (κ _) as K.
  destruct K ; eauto.
  right.
  exists (k+n).
  split ; eauto with math_help.
  unfold await_failed.
  now rewrite <- HeqI.
}
destruct (term_eventually (length (P T))) ; eauto.
exfalso.
apply no_term.
exists (length (P T) + n) ; eauto using out_of_P with math_help.
Qed.

Require Import Coq.Logic.ConstructiveEpsilon.

Lemma inf_constructive G :
  (∀ T, done G T ∨ size G T = None ∧ ¬ ∃ n, P T (pc (comp G n T)) = terminated)
    -> ∀ T, ((size G T = None) * ∀ n, { m : nat | m ≥ n ∧ await_failed G m T }) + {done G T}.
intros inf T.
destruct (done_dec G T) as [D|nD] ; eauto.
left.
assert (Q : size G T = None ∧ ¬ (∃ n : nat, P T (pc (comp G n T)) = terminated)).
{ destruct (inf T) ; tauto. }
destruct Q as (inf_sz & no_term).
split ; eauto.
intros n.
apply constructive_indefinite_ground_description_nat_Acc ; eauto using dec_ge_awf.
apply finite_af_term_inv ; eauto.
Qed.



Definition fair G := ∀ T x,
  ∃ n, ∀ m, m ≥ n -> events G (T,m) = R x -> mo_max G x ≠ None -> Some (rf G (T,m)) = mo_max G x.
(* 
  (∀ n, ∃ m, m ≥ n ∧ events G (T,m) = R x) -> ∃ n, events G (T,n) = R x ∧ rf G (T,n) = mo_max G x. *)

(* can not return to an earlier write from mo-max *)
Definition mo_max_correct G := ∀ e x, events G e = R x -> 
    Some (rf G e) = mo_max G x -> ∀ n, n ≥ idx e -> events G (tid e, n) = R x ->  Some (rf G (tid e,n)) = mo_max G x.


Definition await_success G n T := 
  match P T (pc (comp G n T)) with
  | await_while κ _ => κ (local_state (comp G n T)) = false
  | _ => False
  end.

Definition mo_max_await G T limit m := ∀ n, m - await_length G m T ≤ n ∧ n < m - await_length G m T + limit -> 
    ∀ x, events G (T, n) = R x -> Some (rf G (T, n)) = mo_max G x.


Lemma awf_same_length G m T : await_failed G m T -> await_length G m T = await_length G (m + (await_length G m T + 1)) T.
intros.
unfold await_length at 2.
replace (m + (await_length G m T + 1)) with (await_length G m T + 1 + m) by lia.
rewrite <- failed_repeat_pc ; eauto with math_help.
Qed.




Lemma same_ev G T m i : cons_P G -> await_failed G m T -> in_size G T (m + await_length G m T + 1) -> repeat_iteration_limit G m T i ->
  i ≤ await_length G m T -> ∀ n n', n = i + m+1 -> n' = m + i - await_length G m T -> events G (T,n) = events G (T,n').
intros consG. intros.
subst.
rewrite ! consG ; eauto with size_help math_help.
eapply run_parallel_independent_gen ; eauto using  run_repeat_iteration_limit, failed_inst_independence_total_out_simple with math_help.
Qed.

Lemma mo_max_await_repeat G T : cons_P G -> mo_max_correct G ->
  ∀ m limit, in_size G T (m + await_length G m T + 1) -> await_failed G m T -> mo_max_await G T limit m ->
    limit ≤ await_length G m T + 1 -> repeat_iteration_limit G m T limit.
intros consG mo_corrG m limit in_sz awFm mo_max_L.
intros limit_safe.
assert (∀ i, i ≤ limit -> repeat_iteration_limit G m T i) ; eauto.
induction i.
- intros _. unfold repeat_iteration_limit.
  eauto with math_help.
- intros.
  intros j jltSi.
  assert (Q : j = i ∨ j < i) by lia.
  destruct Q.
  2: { apply IHi ; eauto with math_help. }
  subst.
  unfold eval.
  remember (events G _) as l.
  remember (events G (T, i+m-_)) as l'.
  assert (same_l : l = l').
  { subst.
    eapply same_ev ; eauto with math_help.
  }
  destruct same_l.
  destruct l ; eauto.
  assert (rfe : Some (rf G _) = mo_max G x) by (eauto with math_help).
  assert (rfe' : Some (rf G (T,i+m+1)) = mo_max G x).
  {
    unfold mo_max_correct in *.
    erewrite mo_corrG with (e:=(T,i+m-await_length G m T)) ; eauto with math_help.
  }
  simpl in *.
  replace (rf G (T, i + m - await_length G m T))
    with (rf G (T, i + m + 1)) ; eauto.
  rewrite <- rfe in rfe'.
  now inversion rfe'.
Qed.


Lemma repeat_limit_monotonic G m T limit limit' : limit' ≤ limit -> repeat_iteration_limit G m T limit ->  repeat_iteration_limit G m T limit'.
unfold repeat_iteration_limit.
eauto with math_help.
Qed.

Lemma mo_max_await_cons G m T limit : mo_max_await G T limit m -> (∀ x : address, events G (T, m - await_length G m T+limit) = R x → Some (rf G (T, m - await_length G m T +limit)) = mo_max G x) -> mo_max_await G T (S limit) m.
intros rf_before_lim rf_lim.
unfold mo_max_await in *.
intros n [inawf befSlim].
assert (Q: n = m - await_length G m T + limit ∨ n < m - await_length G m T + limit) by lia.
destruct Q ; subst ; eauto.
Qed.


Lemma mo_max_await_stable G T : cons_P G -> mo_max_correct G ->
  ∀ m limit,  await_failed G m T -> mo_max_await G T limit m -> in_size G T (m + (await_length G m T + 1)) -> limit ≤ await_length G m T + 1 ->
     await_failed G (m + (await_length G m T + 1)) T ∧ mo_max_await G T limit (m + (await_length G m T + 1)) ∨ ¬ await_failed G (m + (await_length G m T + 1)) T.
intros consG mo_corrG m limit awFm mo_max_L in_sz limit_safe.
destruct (dec_awf G (m + (await_length G m T + 1)) T) ; eauto.
left.
split ; eauto.
intros n [in_awfn bef_limit_n].



rewrite <- awf_same_length in * ; eauto.
replace (m + _ - _) with (m + 1) in * by lia. 
intros x rfx.
assert (events G (T, n - (await_length G m T + 1)) = R x).
{ assert (repeat_iteration_limit G m T (n-(m+1))). 
  { eapply repeat_limit_monotonic with (limit:=limit) ; eauto with math_help.
    apply mo_max_await_repeat ; eauto with size_help math_help.
  }
  erewrite <- same_ev with (m:=m) ; eauto with math_help size_help.
}  
apply mo_corrG with (e:=(T,n - (await_length G m T + 1))) ; simpl ; eauto with math_help.
Qed.


Lemma event_eq_dec e e' : {e=e'} + {e ≠ e'}.
Proof with  try now (right ; inversion 1).
destruct e as [T n], e' as [T' n'].
destruct (eq_thread_dec T T')...
destruct (eq_dec n n')...
subst. eauto.
Qed.

Lemma rf_max_dec G T n : {∀ x, events G (T,n) = R x -> Some (rf G (T,n)) = mo_max G x} + {∃ x, events G (T,n) = R x ∧ Some (rf G (T,n)) ≠ mo_max G x}.
destruct (events G _) ; try now (left ; discriminate).
assert (Q: {Some (rf G (T, n)) = mo_max G x} + {Some (rf G (T, n)) ≠ mo_max G x}).
{ 
  remember (mo_max G x) as opt_m.
  destruct opt_m as [e|] ; try now right.
  destruct (event_eq_dec (rf G (T,n)) e).
  - subst. eauto.
  - right. now inversion 1.
}
destruct Q ; eauto.
left.
inversion 1.
now subst.
Qed.

Lemma no_size_in_size G T n : size G T = None -> in_size G T n.
unfold in_size.
intros Q. rewrite Q. eauto.
Qed.

#[local]
Hint Resolve no_size_in_size : size_help.


Require Import Wf_nat.




Lemma mo_max_await_stable_iter G T : cons_P G -> mo_max_correct G ->
  ∀ m limit,  await_failed G m T -> mo_max_await G T limit m -> limit ≤ await_length G m T ->
     ∀ k, in_size G T (m + (S k) * (await_length G m T + 1)) -> 
      let m' := m + k * (await_length G m T + 1) in
      (events G (T,m- await_length G m T + limit) = events G (T,m'- await_length G m T + limit)) ∧ await_length G m' T = await_length G m T ∧ await_failed G m' T ∧ mo_max_await G T limit m' ∨ ∃ k', ¬ await_failed G (m + k' * (await_length G m T + 1)) T.
intros.
induction k.
- replace m' with m by lia. eauto.
- destruct IHk as [(same_ev' & same_l & awf' & momax')|awf_done] ; eauto with size_help.
  assert (Q: _) by (eapply mo_max_await_stable with (m:=m + k * (await_length G m T + 1)); eauto with size_help math_help).
  rewrite same_l in *.
  assert (same_l' := same_l).
  rewrite awf_same_length in same_l' ; eauto.
  rewrite same_l in *.
  replace (m + _ + _) with (m + S k * (await_length G m T + 1)) in * by lia.
  destruct Q as [(awf'' & momax'')|] ; eauto.
  left.
  subst m'.
  repeat split ; eauto.
  rewrite same_ev'.
  symmetry.
  apply same_ev with (m:=m + k * (await_length G m T + 1)) (i:=limit) ; eauto using mo_max_await_repeat with size_help math_help.
Qed.

Lemma go_to_await_inc_limit G T : cons_P G -> fair G -> mo_max_correct G ->
  ∀ m limit, await_failed G m T -> mo_max_await G T limit m -> size G T = None -> 
    limit ≤ await_length G m T -> 
      ∃ k, (∃ i x, i ≤ await_length G m T + 1 ∧  events G (T,m + k * (await_length G m T + 1) + i) = R x ∧ mo_max G x = None) ∨ mo_max_await G T (S limit) (m + k * (await_length G m T + 1)) ∨ ¬ await_failed G (m + k * (await_length G m T + 1)) T.
intros consG fairG mo_corrG m limit awf mo_maxL in_sz limit_safe.
destruct (rf_max_dec G T (m - await_length G m T + limit)) as [already_mo_max | (x & isr & Q)] .
{ exists 0.
  right. left.
  replace (m+_) with m by lia.
  apply mo_max_await_cons ; eauto.
}
remember (mo_max G x) as pot_mo_max.
destruct pot_mo_max.
2: { 
  edestruct mo_max_await_stable_iter with (k:=2) as [ (same_e' & len_awf' & awf' & momax')| (k' & aws') ] ; eauto with size_help math_help.
  exists 1.
  left. exists (limit+1), x.
  repeat split ; eauto with math_help.
  rewrite same_e' in isr.
  rewrite <- isr.
  do 2 f_equal.
  eauto with math_help.
}

destruct (fairG T x) as [n rf_mo_max].
remember ((n-m) / (await_length G m T + 1) + 2) as k.
edestruct mo_max_await_stable_iter with (k:=k) as [ (same_e' & len_awf' & awf' & momax')| (k' & aws') ] ; eauto with size_help math_help.
exists k.
right. left. 
apply mo_max_await_cons ; eauto.
intros x'. rewrite len_awf'.
intros l_Rx'.
assert (x = x').
{ rewrite <- same_e' in l_Rx'.
  rewrite isr in l_Rx'.
  now inversion l_Rx'.
}
subst x'.
apply rf_mo_max ; eauto with math_help.
2: { rewrite <- Heqpot_mo_max. discriminate. }
subst k.
remember (await_length G m T + 1) as L.
replace (m + _ - _) with (m + L + 1 + (n - m) / L * L) by lia.
replace (_ / _ * _) with ((n - m) - (n - m) mod L).
2: {
  assert (n - m  = L * ((n - m) / L) + (n - m) mod L) ; eauto using div_mod with math_help.
}
remember (_ mod _) as M.
assert (M < L). 
{ subst. eauto using mod_upper_bound with math_help. }
lia.
Qed.


Lemma mo_max_await_zero G T m : mo_max_await G T 0 m.
intros x. lia. Qed.

Lemma go_to_await_end G T : cons_P G -> fair G -> mo_max_correct G ->
  ∀ limit m,
    await_failed G m T ->
    size G T = None ->
    limit ≤ await_length G m T + 1 ->
  ∃ k,
    (∃ i x, i ≤ await_length G m T + 1 ∧
            events G (T,m + k * (await_length G m T + 1) + i) = R x ∧
            mo_max G x = None) ∨
    (await_failed G (m + k * (await_length G m T + 1)) T ∧
     mo_max_await G T limit (m + k * (await_length G m T + 1))) ∨
    ¬ await_failed G (m + k * (await_length G m T + 1)) T.
intros consG fairG momaxG.
induction limit.
- intros. exists 0.
  right. left.
  replace (m + _) with m by lia.
  split ; auto.
  unfold mo_max_await.
  lia.
- intros.
  edestruct IHlimit as [k [blocked  | [[awf mo_limit] | awf_done ]]] ; eauto with math_help.
  edestruct mo_max_await_stable_iter with (k:=k) (m:=m) (limit:=0) as [(_ & same_l' & _ & _)|(k' & donek') ]; eauto using mo_max_await_zero with math_help size_help.
  edestruct go_to_await_inc_limit with (m:=m + k * (await_length G m T + 1)) as [k' IHk']; eauto with math_help.
  rewrite same_l' in *.
  replace (_ + _ + _) with (m + (k+k') * (await_length G m T + 1)) in * by lia.
  destruct IHk' as [IHk'|IHk'] ; eauto.
  destruct IHk' ; eauto.
  edestruct mo_max_await_stable_iter with (k:=k+k') (m:=m) (limit:=0) as [(_ & _ & awf'' & _)|(k'' & donek'') ]; eauto using mo_max_await_zero with math_help size_help.
Qed.
