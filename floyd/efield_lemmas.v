Require Import floyd.base2.
Require Import floyd.client_lemmas.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.fieldlist.
Local Open Scope logic.

Inductive efield : Type :=
  | eArraySubsc: forall i: expr, efield
  | eStructField: forall i: ident, efield
  | eUnionField: forall i: ident, efield.

Section CENV.

Context {cs: compspecs}.

Fixpoint nested_efield (e: expr) (efs: list efield) (tts: list type) : expr :=
  match efs, tts with
  | nil, _ => e
  | _, nil => e
  | cons ef efs', cons t0 tts' =>
    match ef with
    | eArraySubsc ei => Ederef (Ebinop Oadd (nested_efield e efs' tts') ei (tptr t0)) t0
    | eStructField i => Efield (nested_efield e efs' tts') i t0
    | eUnionField i => Efield (nested_efield e efs' tts') i t0
    end
  end.

Definition compute_lr e (efs: list efield) :=
  match typeof e, length efs with
  | Tpointer _ _, S _ => RRRR
  | Tarray _ _ _, _ => RRRR (* This line can be either L or R, but R is consistent with LR_of_type *)
  | _, _ => LLLL
  end.

Inductive array_subsc_denote {cs: compspecs}: expr -> Z -> environ -> Prop :=
  | array_subsc_denote_intro:
      forall e i rho, Vint (Int.repr i) = eval_expr e rho -> array_subsc_denote e i rho.

Inductive efield_denote {cs: compspecs}: list efield -> list gfield -> environ -> Prop :=
  | efield_denote_nil: forall rho, efield_denote nil nil rho
  | efield_denote_ArraySubsc: forall ei efs i gfs rho,
      is_int_type (typeof ei) = true ->
      array_subsc_denote ei i rho ->
      efield_denote efs gfs rho ->
      efield_denote (eArraySubsc ei :: efs) (ArraySubsc i :: gfs) rho
  | efield_denote_StructField: forall i efs gfs rho,
      efield_denote efs gfs rho ->
      efield_denote (eStructField i :: efs) (StructField i :: gfs) rho
  | efield_denote_UnionField: forall i efs gfs rho,
      efield_denote efs gfs rho ->
      efield_denote (eUnionField i :: efs) (UnionField i :: gfs) rho.

Fixpoint typecheck_efield {cs: compspecs} (Delta: tycontext) (efs: list efield) : tc_assert :=
  match efs with
  | nil => tc_TT
  | eArraySubsc ei :: efs' =>
    tc_andp (typecheck_expr Delta ei) (typecheck_efield Delta efs')
  | eStructField i :: efs' =>
    typecheck_efield Delta efs'
  | eUnionField i :: efs' =>
    typecheck_efield Delta efs'
  end.

Definition tc_efield {cs: compspecs} (Delta: tycontext) (efs: list efield) : environ -> mpred := denote_tc_assert (typecheck_efield Delta efs).

(* Null Empty Path situation *)
Definition type_almost_match e t lr:=
  match typeof e, t, lr with
  | _, Tarray t1 _ a1, RRRR => eqb_type (typeconv (typeof e)) (Tpointer t1 noattr)
  | _, _, LLLL => eqb_type (typeof e) t
  | _, _, _ => false
  end.

(* Empty Path situation *)
Definition type_almost_match' e t lr:=
  match typeof e, t, lr with
  | _, _, LLLL => eqb_type (typeof e) t
  | _, _, _ => false
  end.

Fixpoint legal_nested_efield_rec t_root (gfs: list gfield) (tts: list type): bool :=
  match gfs, tts with
  | nil, nil => true
  | nil, _ => false
  | _ , nil => false
  | gf :: gfs0, t0 :: tts0 => (legal_nested_efield_rec t_root gfs0 tts0 && eqb_type (nested_field_type t_root gfs) t0)%bool
  end.

Definition legal_nested_efield t_root e gfs tts lr :=
 (match gfs with
  | nil => type_almost_match' e t_root lr
  | _ => type_almost_match e t_root lr
  end &&
  legal_nested_efield_rec t_root gfs tts)%bool.

Lemma legal_nested_efield_rec_cons: forall t_root gf gfs t tts,
  legal_nested_efield_rec t_root (gf :: gfs) (t :: tts) = true ->
  legal_nested_efield_rec t_root gfs tts = true.
Proof.
  intros.
  simpl in H.
  rewrite andb_true_iff in H.
  tauto.
Qed.

Lemma tc_efield_ind: forall {cs: compspecs} (Delta: tycontext) (efs: list efield),
  tc_efield Delta efs =
  match efs with
  | nil => TT
  | eArraySubsc ei :: efs' =>
    tc_expr Delta ei && tc_efield Delta efs'
  | eStructField i :: efs' =>
    tc_efield Delta efs'
  | eUnionField i :: efs' =>
    tc_efield Delta efs'
  end.
Proof.
  intros.
  destruct efs; auto.
  destruct e; auto.
  unfold tc_efield.
  simpl typecheck_efield.
  extensionality rho.
  rewrite denote_tc_assert_andp.
  auto.
Qed.

Lemma typeof_nested_efield': forall rho t_root e ef efs gf gfs t tts,
  legal_nested_efield_rec t_root (gf :: gfs) (t :: tts) = true ->
  efield_denote (ef :: efs) (gf :: gfs) rho ->
  nested_field_type t_root (gf :: gfs) = typeof (nested_efield e (ef :: efs) (t :: tts)).
Proof.
  intros.
  simpl in H.
  rewrite andb_true_iff in H; destruct H.
  apply eqb_type_true in H1; subst.
  destruct ef; reflexivity.
Qed.

Lemma typeof_nested_efield: forall rho t_root e efs gfs tts lr,
  legal_nested_efield t_root e gfs tts lr = true ->
  efield_denote efs gfs rho ->
  nested_field_type t_root gfs = typeof (nested_efield e efs tts).
Proof.
  intros.
  unfold legal_nested_efield in H.
  rewrite andb_true_iff in H.
  destruct H.
  inversion H0; subst; destruct tts;
  try solve [inversion H1 | simpl; auto | destruct e0; simpl; auto].
  + destruct lr; try discriminate.
    apply eqb_type_true in H; subst.
    reflexivity.
  + eapply typeof_nested_efield'; eauto.
  + eapply typeof_nested_efield'; eauto.
  + eapply typeof_nested_efield'; eauto.
Qed.

Lemma offset_val_sem_add_pi: forall ofs t0 e rho i,
   offset_val ofs
     (force_val (sem_add_pi t0 (eval_expr e rho) (Vint (Int.repr i)))) =
   offset_val ofs
     (offset_val (sizeof t0 * i) (eval_expr e rho)).
Proof.
  intros.
  destruct (eval_expr e rho); try reflexivity.
  rewrite sem_add_pi_ptr by (simpl; auto).
  reflexivity.
Qed.

Lemma By_reference_eval_expr: forall Delta e rho,
  access_mode (typeof e) = By_reference ->
  tc_environ Delta rho ->
  tc_lvalue Delta e rho |--
  !! (eval_expr e rho = eval_lvalue e rho).
Proof.
  intros.
  eapply derives_trans. apply typecheck_lvalue_sound; auto.
  normalize.
  destruct e; try contradiction; simpl in *;
  reflexivity.
Qed.

Lemma By_reference_tc_expr: forall Delta e rho,
  access_mode (typeof e) = By_reference ->
  tc_environ Delta rho ->
  tc_lvalue Delta e rho |--  tc_expr Delta e rho.
Proof.
  intros.
  unfold tc_lvalue, tc_expr.
  destruct e; simpl in *; try apply @FF_left; rewrite H; auto.
Qed.

Definition LR_of_type (t: type) :=
  match access_mode t with
  | By_reference => RRRR
  | _ => LLLL
  end.

Lemma legal_nested_efield_weaken: forall t_root e gfs tts,
  legal_nested_efield t_root e gfs tts (LR_of_type t_root) = true ->
  legal_nested_efield_rec t_root gfs tts = true /\
  type_almost_match e t_root (LR_of_type t_root) = true.
Proof.
  intros.
  unfold legal_nested_efield in H.
  rewrite andb_true_iff in H.
  split; [tauto |].
  destruct gfs; [| tauto].
  destruct H as [? _].
  unfold type_almost_match' in H.
  unfold type_almost_match.
  destruct (LR_of_type t_root), t_root, (typeof e); simpl in H |- *;
  try inv H; auto.
Qed.

Lemma weakened_legal_nested_efield_spec: forall t_root e gfs efs tts rho,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  efield_denote efs gfs rho ->
  typeconv (nested_field_type t_root gfs) = typeconv (typeof (nested_efield e efs tts)).
Proof.
  intros.
  inversion H1; subst; destruct tts; try solve [inv H].
  + rewrite nested_field_type_ind.
    simpl typeof.
    unfold type_almost_match in H0.
    destruct (LR_of_type t_root), t_root, (typeof e); try solve [inv H0]; auto;
    apply eqb_type_spec in H0; rewrite H0; auto.
  + f_equal.
    eapply typeof_nested_efield'; eauto.
  + f_equal.
    eapply typeof_nested_efield'; eauto.
  + f_equal.
    eapply typeof_nested_efield'; eauto.
Qed.

Lemma classify_add_add_case_pi: forall ei ty t n a,
  is_int_type (typeof ei) = true ->
  typeconv (Tarray t n a) = typeconv ty ->
  classify_add ty (typeof ei) = add_case_pi t.
Proof.
  intros.
  destruct (typeof ei); try solve [inversion H].
  simpl.
  rewrite <- H0.
  destruct i; reflexivity.
Qed.

Lemma isBinOpResultType_add_ptr: forall e t n a t0 ei,
  is_int_type (typeof ei) = true ->
  typeconv (Tarray t0 n a) = typeconv (typeof e) ->
  complete_type cenv_cs t0 = true ->
  isBinOpResultType Oadd e ei (tptr t) = tc_isptr e.
Proof.
  intros.
  unfold isBinOpResultType.
  erewrite classify_add_add_case_pi by eauto.
  rewrite tc_andp_TT2.
  rewrite H1, tc_andp_TT2.
  auto.
Qed.

Lemma array_op_facts: forall ei rho t_root e efs gfs tts t n a t0 p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  is_int_type (typeof ei) = true ->
  nested_field_type t_root gfs = Tarray t n a ->
  field_compatible t_root gfs p ->
  efield_denote efs gfs rho ->
  classify_add (typeof (nested_efield e efs tts)) (typeof ei) = add_case_pi t /\
  isBinOpResultType Oadd (nested_efield e efs tts) ei (tptr t0) = tc_isptr (nested_efield e efs tts).
Proof.
  intros.
  pose proof (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H0 H4).
  rewrite H2 in H5.
  split.
  + eapply classify_add_add_case_pi; eauto.
  + eapply isBinOpResultType_add_ptr; eauto.
    destruct H3 as [_ [_ [_ [? [_ [_ [_ ?]]]]]]].
    eapply nested_field_type_complete_type with (gfs0 := gfs) in H3; auto.
    rewrite H2 in H3.
    exact H3.
Qed.

Lemma array_ind_step: forall Delta ei i rho t_root e efs gfs tts t n a t0 p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  is_int_type (typeof ei) = true ->
  array_subsc_denote ei i rho ->
  nested_field_type t_root gfs = Tarray t0 n a ->
  tc_environ Delta rho ->
  efield_denote efs gfs rho ->
  field_compatible t_root gfs p ->
  tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho
  |-- !! (field_address t_root gfs p = eval_LR (nested_efield e efs tts) (LR_of_type (Tarray t0 n a)) rho) &&
          tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (Tarray t0 n a)) rho ->
  tc_LR_strong Delta e (LR_of_type t_root) rho &&
  tc_efield Delta (eArraySubsc ei :: efs) rho
  |-- !! (offset_val (gfield_offset (nested_field_type t_root gfs) (ArraySubsc i))
          (field_address t_root gfs p) =
          eval_lvalue (nested_efield e (eArraySubsc ei :: efs) (t :: tts)) rho) &&
          tc_lvalue Delta (nested_efield e (eArraySubsc ei :: efs) (t :: tts)) rho.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?
         LEGAL_NESTED_EFIELD_REC TYPE_MATCH ? ? NESTED_FIELD_TYPE TC_ENVIRON EFIELD_DENOTE FIELD_COMPATIBLE IH.
  destruct (array_op_facts _ _ _ _ _ _ _ _ _ _ t _ LEGAL_NESTED_EFIELD_REC TYPE_MATCH H NESTED_FIELD_TYPE FIELD_COMPATIBLE EFIELD_DENOTE) as [CLASSIFY_ADD ISBINOP].
  pose proof field_address_isptr _ _ _ FIELD_COMPATIBLE as ISPTR.
  rewrite tc_efield_ind; simpl.
  rewrite andp_comm, andp_assoc.
  eapply derives_trans; [apply andp_derives; [apply derives_refl | rewrite andp_comm; exact IH] | ].
  rewrite (add_andp _ _ (typecheck_expr_sound _ _ _ TC_ENVIRON)).
  unfold_lift.
  normalize.
  apply andp_right1; [apply prop_right | normalize].
  + inversion H0; subst.
    rewrite <- H3.
    unfold force_val2, force_val.
    unfold sem_add.
    rewrite CLASSIFY_ADD.
    rewrite sem_add_pi_ptr.
    2: simpl in H2; rewrite <- H2; auto.
    unfold gfield_offset; rewrite NESTED_FIELD_TYPE, H2.
    reflexivity.
  + unfold tc_lvalue.
    Opaque isBinOpResultType. simpl. Transparent isBinOpResultType.
    rewrite ISBINOP.
    normalize.
    rewrite !denote_tc_assert_andp.
    repeat apply andp_right.
    - apply prop_right.
      simpl in H2; rewrite <- H2; auto.
    - solve_andp.
    - solve_andp.
    - apply prop_right.
      simpl; unfold_lift.
      rewrite <- H3.
      normalize.
Qed.

Lemma in_members_Ctypes_offset: forall i m e, in_members i m -> Ctypes.field_offset cenv_cs i m = Errors.Error e -> False.
Proof.
  intros.
  unfold Ctypes.field_offset in H0.
  revert H0; generalize 0; induction m as [| [? ?] ?]; intros.
  + inv H.
  + simpl in H0.
    if_tac in H0; inv H0.
    spec IHm.
    - destruct H; [simpl in H; congruence | auto].
    - apply IHm in H3; auto.
Qed.

Lemma struct_op_facts: forall Delta t_root e gfs efs tts i a i0 t rho,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  in_members i0 (co_members (get_co i)) ->
  nested_field_type t_root gfs = Tstruct i a ->
  efield_denote efs gfs rho ->
  tc_lvalue Delta (nested_efield e efs tts) rho =
  tc_lvalue Delta (nested_efield e (eStructField i0 :: efs) (t :: tts)) rho /\
  eval_field (typeof (nested_efield e efs tts)) i0 =
      offset_val (field_offset cenv_cs i0 (co_members (get_co i))).
Proof.
  intros.
  pose proof (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H0 H3).
  rewrite H2 in H4; simpl in H4.
  destruct (typeof (nested_efield e efs tts)) eqn:?H; inv H4.
  1: destruct i1; inv H7.
  unfold tc_lvalue, eval_field.
  simpl.
  rewrite H5.
  unfold field_offset, fieldlist.field_offset.
  unfold get_co in *.
  destruct (cenv_cs ! i1); [| inv H1].
  destruct (Ctypes.field_offset cenv_cs i0 (co_members c)) eqn:?H.
  + split; auto.
    rewrite denote_tc_assert_andp; simpl.
    apply add_andp, prop_right; auto.
  + exfalso.
    pose proof in_members_Ctypes_offset i0 (co_members c) e0; auto.
Qed.

Lemma struct_ind_step: forall Delta t_root e gfs efs tts i a i0 t rho p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  in_members i (co_members (get_co i0)) ->
  nested_field_type t_root gfs = Tstruct i0 a ->
  tc_environ Delta rho ->
  efield_denote efs gfs rho ->
  field_compatible t_root gfs p ->
  tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho
  |-- !! (field_address t_root gfs (eval_LR e (LR_of_type t_root) rho) =
          eval_LR (nested_efield e efs tts) (LR_of_type (Tstruct i0 a)) rho) &&
          tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (Tstruct i0 a)) rho ->
  tc_LR_strong Delta e (LR_of_type t_root) rho &&
  tc_efield Delta (eStructField i :: efs) rho
  |-- !! (offset_val (gfield_offset (nested_field_type t_root gfs) (StructField i))
            (field_address t_root gfs (eval_LR e (LR_of_type t_root) rho)) =
          eval_lvalue (nested_efield e (eStructField i :: efs) (t :: tts)) rho) &&
      tc_lvalue Delta (nested_efield e (eStructField i :: efs) (t :: tts)) rho.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ?
         LEGAL_NESTED_EFIELD_REC TYPE_MATCH ? NESTED_FIELD_TYPE TC_ENVIRON EFIELD_DENOTE FIELD_COMPATIBLE IH.
  destruct (struct_op_facts Delta _ _ _ _ _ _ _ _ t _ LEGAL_NESTED_EFIELD_REC TYPE_MATCH H NESTED_FIELD_TYPE EFIELD_DENOTE) as [TC EVAL].
  rewrite tc_efield_ind; simpl.
  eapply derives_trans; [exact IH | ].
  unfold_lift.
  normalize.
  apply andp_right1; [apply prop_right | normalize].
  + rewrite EVAL, H0, NESTED_FIELD_TYPE.
    reflexivity.
  + simpl in TC; rewrite <- TC.
    auto.
Qed.

Lemma union_op_facts: forall Delta t_root e gfs efs tts i a i0 t rho,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  in_members i0 (co_members (get_co i)) ->
  nested_field_type t_root gfs = Tunion i a ->
  efield_denote efs gfs rho ->
  tc_lvalue Delta (nested_efield e efs tts) rho =
  tc_lvalue Delta (nested_efield e (eUnionField i0 :: efs) (t :: tts)) rho /\
  eval_field (typeof (nested_efield e efs tts)) i0 = offset_val 0.
Proof.
  intros.
  pose proof (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H0 H3).
  rewrite H2 in H4; simpl in H4.
  destruct (typeof (nested_efield e efs tts)) eqn:?H; inv H4.
  1: destruct i1; inv H7.
  unfold tc_lvalue, eval_field.
  simpl.
  rewrite H5.
  unfold get_co in *.
  destruct (cenv_cs ! i1); [| inv H1].
  split; [| normalize; auto].
  rewrite denote_tc_assert_andp; simpl.
  apply add_andp, prop_right; auto.
Qed.

Lemma union_ind_step: forall Delta t_root e gfs efs tts i a i0 t rho p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  in_members i (co_members (get_co i0)) ->
  nested_field_type t_root gfs = Tunion i0 a ->
  tc_environ Delta rho ->
  efield_denote efs gfs rho ->
  field_compatible t_root gfs p ->
  tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho
  |-- !! (field_address t_root gfs (eval_LR e (LR_of_type t_root) rho) =
          eval_LR (nested_efield e efs tts) (LR_of_type (Tstruct i0 a)) rho) &&
          tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (Tstruct i0 a)) rho ->
  tc_LR_strong Delta e (LR_of_type t_root) rho &&
  tc_efield Delta (eUnionField i :: efs) rho
  |-- !! (offset_val (gfield_offset (nested_field_type t_root gfs) (UnionField i))
            (field_address t_root gfs (eval_LR e (LR_of_type t_root) rho)) =
          eval_lvalue (nested_efield e (eUnionField i :: efs) (t :: tts)) rho) &&
      tc_lvalue Delta (nested_efield e (eUnionField i :: efs) (t :: tts)) rho.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ?
         LEGAL_NESTED_EFIELD_REC TYPE_MATCH ? NESTED_FIELD_TYPE TC_ENVIRON EFIELD_DENOTE FIELD_COMPATIBLE IH.
  destruct (union_op_facts Delta _ _ _ _ _ _ _ _ t _ LEGAL_NESTED_EFIELD_REC TYPE_MATCH H NESTED_FIELD_TYPE EFIELD_DENOTE) as [TC EVAL].
  rewrite tc_efield_ind; simpl.
  eapply derives_trans; [exact IH | ].
  unfold_lift.
  normalize.
  apply andp_right1; [apply prop_right | normalize].
  + rewrite EVAL, H0, NESTED_FIELD_TYPE.
    reflexivity.
  + simpl in TC; rewrite <- TC.
    auto.
Qed.

Definition lvalue_LR_of_type: forall Delta rho P p t e,
  t = typeof e ->
  tc_environ Delta rho ->
  P |-- !! (p = eval_lvalue e rho) && tc_lvalue Delta e rho ->
  P |-- !! (p = eval_LR e (LR_of_type t) rho) && tc_LR_strong Delta e (LR_of_type t) rho.
Proof.
  intros.
  destruct (LR_of_type t) eqn:?H.
  + exact H1.
  + rewrite (add_andp _ _ H1); clear H1.
    simpl; normalize.
    apply andp_left2.
    unfold LR_of_type in H2.
    subst.
    destruct (access_mode (typeof e)) eqn:?H; inv H2.
    apply andp_right.
    - eapply derives_trans; [apply By_reference_eval_expr |]; auto.
      normalize.
    - apply By_reference_tc_expr; auto.
Qed.

Lemma eval_lvalue_nested_efield_aux: forall Delta t_root e efs gfs tts p,
  field_compatible t_root gfs p ->
  legal_nested_efield t_root e gfs tts (LR_of_type t_root) = true ->
  local (`(eq p) (eval_LR e (LR_of_type t_root))) &&
  tc_LR Delta e (LR_of_type t_root) &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  local (`(eq (field_address t_root gfs p))
   (eval_LR (nested_efield e efs tts) (LR_of_type (nested_field_type t_root gfs)))) &&
  tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (nested_field_type t_root gfs)).
Proof.
  (* Prepare *)
  intros Delta t_root e efs gfs tts p FIELD_COMPATIBLE LEGAL_NESTED_EFIELD.
  unfold local, lift1; simpl; intro rho.
  unfold_lift.
  normalize.
  rename H into EFIELD_DENOTE, H0 into TC_ENVIRON.
  apply derives_trans with (tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho).
  Focus 1. {
    repeat (apply andp_derives; auto).
    eapply derives_trans; [| apply tc_LR_tc_LR_strong].
    rewrite andp_comm, prop_true_andp by auto.
    auto.
  } Unfocus.
  pose proof legal_nested_efield_weaken _ _ _ _ LEGAL_NESTED_EFIELD as [LEGAL_NESTED_EFIELD_REC TYPE_ALMOST_MATCH].
  rewrite field_compatible_field_address by auto.
  clear LEGAL_NESTED_EFIELD.

  (* Induction *)
  revert tts LEGAL_NESTED_EFIELD_REC; induction EFIELD_DENOTE; intros;
  destruct tts; try solve [inversion LEGAL_NESTED_EFIELD_REC];
  [normalize | | |];
  pose proof FIELD_COMPATIBLE as FIELD_COMPATIBLE_CONS;
  apply field_compatible_cons in FIELD_COMPATIBLE;
  destruct (nested_field_type t_root gfs) eqn:NESTED_FIELD_TYPE; try solve [inv FIELD_COMPATIBLE];
  rename LEGAL_NESTED_EFIELD_REC into LEGAL_NESTED_EFIELD_REC_CONS;
  pose proof (proj1 (proj1 (andb_true_iff _ _) LEGAL_NESTED_EFIELD_REC_CONS) : legal_nested_efield_rec t_root gfs tts = true) as LEGAL_NESTED_EFIELD_REC;
  (spec IHEFIELD_DENOTE; [tauto |]);
  (spec IHEFIELD_DENOTE; [auto |]);
  specialize (IHEFIELD_DENOTE tts LEGAL_NESTED_EFIELD_REC);
  (apply lvalue_LR_of_type; [eapply typeof_nested_efield'; eauto; econstructor; eauto | eassumption |]);
  destruct FIELD_COMPATIBLE as [? FIELD_COMPATIBLE];
  rewrite offset_val_nested_field_offset_ind by auto;
  rewrite <- field_compatible_field_address in IHEFIELD_DENOTE |- * by auto.
  + eapply array_ind_step; eauto.
  + eapply struct_ind_step; eauto.
  + eapply union_ind_step; eauto.
Qed.

Lemma eval_lvalue_nested_efield: forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  type_is_by_value (nested_field_type t_root gfs) = true ->
  local (`(eq p) (eval_LR e lr)) &&
  tc_LR Delta e lr &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  local (`(eq (field_address t_root gfs p)) (eval_lvalue (nested_efield e efs tts))).
Proof.
  intros.
  subst lr.
  eapply derives_trans; [apply eval_lvalue_nested_efield_aux; eauto |].
  apply andp_left1.
  destruct (LR_of_type (nested_field_type t_root gfs)) eqn:?H; auto.
  unfold LR_of_type in H0.
  destruct (nested_field_type t_root gfs) as [| [| | |] [|] | | [|] | | | | |]; inv H2; inv H0.
Qed.

Lemma tc_lvalue_nested_efield: forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  type_is_by_value (nested_field_type t_root gfs) = true ->
  local (`(eq p) (eval_LR e lr)) &&
  tc_LR Delta e lr &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  tc_lvalue Delta (nested_efield e efs tts).
Proof.
  intros.
  subst lr.
  eapply derives_trans; [apply eval_lvalue_nested_efield_aux; eauto |].
  apply andp_left2.
  destruct (LR_of_type (nested_field_type t_root gfs)) eqn:?H; auto.
  unfold LR_of_type in H0.
  destruct (nested_field_type t_root gfs) as [| [| | |] [|] | | [|] | | | | |]; inv H2; inv H0.
Qed.

Definition compute_nested_efield {cs: compspecs}: expr -> expr * list efield * list type * LLRR :=
  fix compute_nested_efield e :=
  match e with
  | Efield e' id t =>
    match typeof e' with
    | Tstruct id_str _ =>
      if eqb_type (field_type id (co_members (get_co id_str))) t
      then match compute_nested_efield e' with
           | (e'', efs, tts, lr) => (e'', eStructField id :: efs, t :: tts, lr)
           end
      else (e, nil, nil, LLLL)
    | Tunion id_uni _ =>
      if eqb_type (field_type id (co_members (get_co id_uni))) t
      then match compute_nested_efield e' with
           | (e'', efs, tts, lr) => (e'', eUnionField id :: efs, t :: tts, lr)
           end
      else (e, nil, nil, LLLL)
    | _ => (e, nil, nil, LLLL)
    end
  | Ederef (Ebinop Oadd e' ei (Tpointer t a)) t' =>
    match typeof e', eqb_type t t', eqb_attr a noattr with
    | Tarray _ _ _, true, true =>
      match compute_nested_efield e' with
      | (e'', efs, tts, lr) => (e'', eArraySubsc ei :: efs, t :: tts, lr)
      end
    | Tpointer _ _, true, true => (e', eArraySubsc ei :: nil, t :: nil, RRRR)
    | _, _, _ => (e, nil, nil, LLLL)
    end
  | _ => (e, nil, nil, LLLL)
  end.

Inductive compute_root_type: forall (t_from_e: type) (lr: LLRR) (t_root: type), Prop :=
  | compute_root_type_lvalue: forall t, compute_root_type t LLLL t
  | compute_root_type_expr: forall t a1 n a2, compute_root_type (Tpointer t a1) RRRR (Tarray t n a2).

Lemma compute_nested_efield_aux: forall e t,
  match compute_nested_efield e with
  | (e', gfs, tts, lr) => nested_efield e' gfs tts = e
  end /\
  match compute_nested_efield (Ederef e t) with
  | (e', gfs, tts, lr) => nested_efield e' gfs tts = Ederef e t
  end.
Proof.
  intros.
  revert t.
  induction e; intros; split; try reflexivity.
  + destruct (IHe t).
    exact H0.
  + clear IHe2.
    destruct (IHe1 t) as [? _]; clear IHe1.
    simpl; destruct b, t; try reflexivity.
    destruct (compute_nested_efield e1) as (((?, ?), ?), ?); try reflexivity.
    destruct (typeof e1); try reflexivity.
    - destruct (eqb_type t t0) eqn:?H; try reflexivity.
      apply eqb_type_spec in H0.
      destruct (eqb_attr a noattr) eqn:?H; try reflexivity.
      apply eqb_attr_spec in H1.
      subst.
      reflexivity.
    - destruct (eqb_type t t0) eqn:?H; try reflexivity.
      apply eqb_type_spec in H0.
      destruct (eqb_attr a noattr) eqn:?H; try reflexivity.
      apply eqb_attr_spec in H1.
      subst.
      reflexivity.
  + destruct (IHe t) as [? _]; clear IHe.
    simpl.
    destruct (compute_nested_efield e) as (((?, ?), ?), ?); try reflexivity.
    destruct (typeof e); try reflexivity.
    - if_tac; auto. simpl. rewrite <- H. reflexivity.
    - if_tac; auto. simpl. rewrite <- H. reflexivity.
Qed.

Lemma compute_nested_efield_lemma: forall e,
  match compute_nested_efield e with
  | (e', gfs, tts, lr) => nested_efield e' gfs tts = e
  end.
Proof.
  intros.
  destruct (compute_nested_efield_aux e Tvoid).
  auto.
Qed.

End CENV.
