Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Lemma nth_error_None_iff: forall {A} (l: list A) n, nth_error l n = None <-> n >= length l.
Proof.
  intros.
  revert n; induction l; intros; destruct n; simpl.
  + split; [intros _; omega | auto].
  + split; [intros _; omega | auto].
  + split; [intros; inversion H | omega].
  + rewrite IHl.
    omega.
Qed.

Class RandomOracle: Type := {
  ro_question: Type;
  ro_answer: ro_question -> Type;
  ro_default_question: ro_question;
  ro_default_answer: ro_answer ro_default_question
}.

Definition RandomQA {ora: RandomOracle}: Type := {q: ro_question & ro_answer q}.

Definition RandomHistory {ora: RandomOracle}: Type := {h: nat -> option RandomQA | forall x y, x < y -> h x = None -> h y = None}.

Definition history_get {ora: RandomOracle} (h: RandomHistory) (n: nat) := proj1_sig h n.

Coercion history_get: RandomHistory >-> Funclass.

Lemma history_sound1: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x <= y -> h x = None -> h y = None.
Proof.
  intros ? [h ?] ? ? ?.
  destruct H; auto; simpl.
  apply (e x (S m)).
  omega.
Qed.

Lemma history_sound2: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x <= y -> (exists a, h y = Some a) -> (exists a, h x = Some a).
Proof.
  intros.
  pose proof history_sound1 h x y H.
  destruct (h x), (h y), H0; eauto.
  specialize (H1 eq_refl).
  congruence.
Qed.

Definition fin_history {ora: RandomOracle} (h: list RandomQA) : RandomHistory.
  exists (fun n => nth_error h n).
  intros.
  rewrite nth_error_None_iff in H0 |- *.
  omega.
Defined.

Definition inf_history {ora: RandomOracle} (h: nat -> RandomQA) : RandomHistory.
  exists (fun n => Some (h n)).
  intros.
  congruence.
Defined.

Definition fstn_history {ora: RandomOracle} (n: nat) (h: RandomHistory) : RandomHistory.
  exists (fun m => if le_lt_dec n m then None else h m).
  intros.
  destruct (le_lt_dec n x), (le_lt_dec n y); try congruence.
  + omega.
  + apply (history_sound1 h x y); auto; omega.
Defined.

Definition history_coincide {ora: RandomOracle} (n: nat) (h1 h2: RandomHistory): Prop :=
  forall m, m < n -> h1 m = h2 m.

(*
Definition history_cons {ora: RandomOracle} (h1: RandomHistory) (a: RandomQA) (h2: RandomHistory): Prop :=
  exists n,
    history_coincide n h1 h2 /\
    h1 n = None /\
    h2 n = Some a /\
    h2 (S n) = None.
*)

Definition history_app {ora: RandomOracle} (h1 h2 h: RandomHistory): Prop :=
  exists n,
    h1 n = None /\
    history_coincide n h1 h /\
    (forall m, h (m + n) = h2 m).

Definition is_fin_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  exists n, h n = None.

Definition is_inf_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  forall n, h n <> None.

Definition is_n_history {ora: RandomOracle} (n: nat) (h: RandomHistory): Prop :=
  h n = None /\ forall n', n' < n -> h n' <> None.

Lemma fin_history_fin {ora: RandomOracle}: forall l, is_fin_history (fin_history l).
Proof.
  intros.
  exists (length l).
  simpl.
  rewrite nth_error_None_iff; auto.
Qed.

Lemma inf_history_inf {ora: RandomOracle}: forall f, is_inf_history (inf_history f).
Proof.
  intros; hnf; intros.
  simpl.
  congruence.
Qed.

Definition prefix_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  forall n, h1 n = None \/ h1 n = h2 n.

Definition strict_prefix_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  prefix_history h1 h2 /\ exists n, h1 n <> h2 n.

Definition n_bounded_prefix_history {ora: RandomOracle} (m: nat) (h1 h2: RandomHistory): Prop :=
  forall n, (h1 n = None /\ h2 (n + m) = None) \/ h1 n = h2 n.

Definition n_conflict_history {ora: RandomOracle} (n: nat) (h1 h2: RandomHistory): Prop :=
  match h1 n, h2 n with
  | Some a1, Some a2 => projT1 a1 <> projT1 a2
  | Some _, None => True
  | None, Some _ => True
  | None, None => False
  end.

Definition conflict_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  exists n, history_coincide n h1 h2 /\ n_conflict_history n h1 h2.

Definition strict_conflict_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  exists n,
    history_coincide n h1 h2 /\
    match h1 n, h2 n with
    | Some a1, Some a2 => projT1 a1 <> projT1 a2
    | _, _ => False
    end.

Lemma history_coincide_sym {ora: RandomOracle}: forall h1 h2 n,
  history_coincide n h1 h2 ->
  history_coincide n h2 h1.
Proof.
  intros.
  hnf; intros.
  specialize (H m H0); congruence.
Qed.

Lemma conflict_history_sym {ora: RandomOracle}: forall h1 h2,
  conflict_history h1 h2 ->
  conflict_history h2 h1.
Proof.
  unfold conflict_history; intros.
  destruct H as [n [? ?]].
  exists n; split.
  + apply history_coincide_sym; auto.
  + hnf in H0 |- *; destruct (h1 n), (h2 n); auto.
Qed.

Lemma history_coincide_trans {ora: RandomOracle}: forall h1 h2 h3 n,
  history_coincide n h1 h2 ->
  history_coincide n h2 h3 ->
  history_coincide n h1 h3.
Proof.
  intros.
  hnf; intros.
  specialize (H m H1);
  specialize (H0 m H1); congruence.
Qed.

Lemma is_0_history_non_conflict {ora: RandomOracle}: forall h1 h2,
  is_n_history 0 h1 ->
  is_n_history 0 h2 ->
  conflict_history h1 h2 ->
  False.
Proof.
  intros.
  destruct H1 as [n [? ?]].
  destruct H as [? _], H0 as [? _].
  hnf in H2.
  rewrite (history_sound1 h1 0 n) in H2 by (auto; omega).
  rewrite (history_sound1 h2 0 n) in H2 by (auto; omega).
  auto.
Qed.

Lemma fstn_history_Some {ora: RandomOracle}: forall n m h, m < n -> (fstn_history n h) m = h m.
Proof.
  intros; simpl.
  destruct (le_lt_dec n m); auto; omega.
Qed.

Lemma fstn_history_None {ora: RandomOracle}: forall n m h, n <= m -> (fstn_history n h) m = None.
Proof.
  intros; simpl.
  destruct (le_lt_dec n m); auto; omega.
Qed.

Lemma history_coincide_weaken {ora: RandomOracle}: forall n m h1 h2,
  n <= m ->
  history_coincide m h1 h2 ->
  history_coincide n h1 h2.
Proof.
  intros.
  intros n0 ?.
  apply H0.
  omega.
Qed.

Lemma is_n_history_None {ora: RandomOracle}: forall n m h, n <= m -> is_n_history n h -> h m = None.
Proof.
  intros.
  destruct H0.
  apply (history_sound1 h n m); auto.
Qed.

Lemma fstn_history_is_n_history {ora: RandomOracle}: forall n m h,
  m <= n ->
  is_n_history n h ->
  is_n_history m (fstn_history m h).
Proof.
  intros.
  destruct H0.
  split.
  + rewrite fstn_history_None by auto; auto.
  + intros.
    rewrite fstn_history_Some by omega.
    apply H1; omega.
Qed.

Lemma fstn_history_coincide {ora: RandomOracle}: forall n h,
  history_coincide n h (fstn_history n h).
Proof.
  intros.
  intros m ?.
  rewrite fstn_history_Some by omega.
  auto.
Qed.

(* TODO: put this in lib *)
Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Definition history_set_consi {ora: RandomOracle} (P: RandomHistory -> Prop) : Prop :=
  forall h1 h2,
    conflict_history h1 h2 ->
    P h1 ->
    P h2 ->
    False.

Class LegalRandomVarDomain {ora: RandomOracle} (d: RandomHistory -> Prop) : Prop := {
  rand_consi: history_set_consi d
}.

Record RandomVarDomain {ora: RandomOracle}: Type := {
  raw_domain: RandomHistory -> Prop;
  raw_domain_legal: LegalRandomVarDomain raw_domain
}.

Record RandomVariable {ora: RandomOracle} (A: Type): Type := {
  raw_var: RandomHistory -> option A;
  raw_var_legal: LegalRandomVarDomain (Basics.compose isSome raw_var)
}.

Definition rand_var_get {ora: RandomOracle} {A: Type} (v: RandomVariable A) (h: RandomHistory): option A := raw_var A v h.

Definition in_domain {ora: RandomOracle} (d: RandomVarDomain) (h: RandomHistory): Prop := raw_domain d h.

Coercion rand_var_get: RandomVariable >-> Funclass.

Coercion in_domain: RandomVarDomain >-> Funclass.

Definition join {ora: RandomOracle} {A: Type} (v1 v2 v: RandomVariable A): Prop :=
  forall h, (v1 h = None /\ v2 h = v h) \/ (v2 h = None /\ v1 h = v h).
(*
Definition Forall_RandomHistory {ora: RandomOracle} {A: Type} (P: A -> Prop) (v: RandomVariable A): Prop :=
  forall h,
    match v h with
    | None => True
    | Some a => P a
    end.
*)

Definition unit_space_var {ora: RandomOracle} {A: Type} (v: A): RandomVariable A.
  refine (Build_RandomVariable _ _ (fun h => match h 0 with None => Some v | Some _ => None end) _).
  constructor; hnf; intros.
  unfold Basics.compose in *.
  destruct H as [n [? ?]].
  hnf in H2.
  destruct n.
  + destruct (h1 0), (h2 0); try solve [inversion H0 | inversion H1].
    auto.
  + pose proof (H 0 (le_n_S _ _ (le_0_n _))).
    destruct (h1 0) eqn:?H, (h2 0) eqn:?H; try solve [inversion H0 | inversion H1].
    destruct (h1 (S n)) eqn:?H; [| destruct (h2 (S n)) eqn:?H].
    - pose proof history_sound2 h1 0 (S n) (le_0_n _).
      specialize (H7 (ex_intro _ r H6)).
      destruct H7; rewrite H4 in H7; congruence.
    - pose proof history_sound2 h2 0 (S n) (le_0_n _).
      specialize (H8 (ex_intro _ r H7)).
      destruct H8; rewrite H5 in H8; congruence.
    - auto.
Defined.

Definition RandomVarMap {ora: RandomOracle} {A B: Type} (f: A -> B) (v: RandomVariable A): RandomVariable B.
  refine (Build_RandomVariable _ _ (fun h => match v h with Some a => Some (f a) | None => None end) _).
  constructor.
  destruct v as [v [consi]]; simpl in *.
  hnf; intros; unfold Basics.compose in *.
  specialize (consi h1 h2 H); simpl in consi.
  destruct (v h1), (v h2); auto.
Defined.

Lemma RandomVarMap_sound: forall {ora: RandomOracle} {A B: Type} (f: A -> B) (v: RandomVariable A) h,
  RandomVarMap f v h =
  match v h with
  | Some a => Some (f a)
  | None => None
  end.
Proof. intros. reflexivity. Qed.

Definition DomainOfVar {ora: RandomOracle} {A: Type} (v: RandomVariable A): RandomVarDomain :=
  Build_RandomVarDomain _ (Basics.compose isSome (raw_var _ v)) (raw_var_legal _ v).

Definition unit_space_domain {ora: RandomOracle}: RandomVarDomain := DomainOfVar (unit_space_var tt).

Definition future_domain {ora: RandomOracle} (present future: RandomVarDomain): Prop :=
  forall h, future h ->
  exists h', prefix_history h' h -> present h'.

Definition n_bounded_future_domain {ora: RandomOracle} (n: nat) (present future: RandomVarDomain): Prop :=
  forall h, future h ->
  exists h', n_bounded_prefix_history n h' h -> present h'.

Definition bounded_future_domain {ora: RandomOracle} (present future: RandomVarDomain): Prop :=
  exists n, n_bounded_future_domain n present future.

Definition same_covered_domain {ora: RandomOracle} (d1 d2: RandomVarDomain): Prop :=
  forall h, is_inf_history h ->
    ((exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ d1 h') <->
     (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ d2 h')).

(*
(* TODO: seems no use *)
Definition single_update {ora: RandomOracle} {A: Type} (h0: RandomHistory) (a1 a2: A) (v1 v2: RandomVariable A): Prop :=
  v1 h0 = Some a1 /\
  v2 h0 = Some a2 /\
  forall h, h0 <> h -> v1 h = v2 h.

Definition single_expand {ora: RandomOracle} {A: Type} (h0: RandomHistory) (a1: A) (a2: {q: ro_question & ro_answer q -> A}) (v1 v2: RandomVariable A): Prop :=
  v1 h0 = Some a1 /\
  v2 h0 = None /\
  (forall (a: ro_answer (projT1 a2)) h,
     history_cons h0 (existT ro_answer (projT1 a2) a) h ->
     v1 h = None /\ v2 h = Some (projT2 a2 a)) /\
  (forall h,
     h0 <> h ->
     (forall (a: ro_answer (projT1 a2)), ~ history_cons h0 (existT ro_answer (projT1 a2) a) h) ->
     v2 h = v1 h).
*)