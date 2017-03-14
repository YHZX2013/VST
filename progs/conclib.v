Require Export msl.predicates_sl.
Require Export concurrency.semax_conc_pred.
Require Export concurrency.semax_conc.
Require Export floyd.proofauto.
Require Import floyd.library.
Require Export floyd.sublist.

(* general list lemmas *)
Notation vint z := (Vint (Int.repr z)).

Lemma app_cons_assoc : forall {A} l1 (x : A) l2, l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
Proof.
  intros; rewrite <- app_assoc; auto.
Qed.

Lemma Forall_forall_Znth : forall {A} (P : A -> Prop) l d,
  Forall P l <-> forall i, 0 <= i < Zlength l -> P (Znth i l d).
Proof.
  split; intros; [apply Forall_Znth; auto|].
  induction l; auto.
  rewrite Zlength_cons in *.
  constructor.
  - specialize (H 0); rewrite Znth_0_cons in H; apply H.
    pose proof (Zlength_nonneg l); omega.
  - apply IHl; intros.
    specialize (H (i + 1)).
    rewrite Znth_pos_cons, Z.add_simpl_r in H by omega.
    apply H; omega.
Qed.

Lemma Zmod_smallish : forall x y, y <> 0 -> 0 <= x < 2 * y ->
  x mod y = x \/ x mod y = x - y.
Proof.
  intros.
  destruct (zlt x y); [left; apply Zmod_small; omega|].
  rewrite <- Z.mod_add with (b := -1) by auto.
  right; apply Zmod_small; omega.
Qed.

Lemma Zmod_plus_inv : forall a b c d (Hc : c > 0) (Heq : (a + b) mod c = (d + b) mod c),
  a mod c = d mod c.
Proof.
  intros; rewrite Zplus_mod, (Zplus_mod d) in Heq.
  pose proof (Z_mod_lt a c Hc).
  pose proof (Z_mod_lt b c Hc).
  pose proof (Z_mod_lt d c Hc).
  destruct (Zmod_smallish (a mod c + b mod c) c), (Zmod_smallish (d mod c + b mod c) c); omega.
Qed.

Lemma Znth_app : forall {A} (l1 l2 : list A) i d, Zlength l1 = i -> Znth i (l1 ++ l2) d = Znth 0 l2 d.
Proof.
  intros; subst; rewrite app_Znth2, Zminus_diag; auto; omega.
Qed.

Corollary Znth_app1 : forall {A} l1 (x : A) l2 i d, Zlength l1 = i -> Znth i (l1 ++ x :: l2) d = x.
Proof.
  intros; rewrite Znth_app, Znth_0_cons; auto.
Qed.

Definition complete MAX l := l ++ repeat (vint 0) (Z.to_nat MAX - length l).

Lemma upd_complete : forall l x MAX, Zlength l < MAX ->
  upd_Znth (Zlength l) (complete MAX l) x = complete MAX (l ++ [x]).
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app2, Zminus_diag.
  rewrite app_length; simpl plus.
  rewrite Zlength_correct, Z2Nat.inj_lt, Nat2Z.id in H; try omega.
  destruct (Z.to_nat MAX - length l)%nat eqn: Hminus; [omega|].
  replace (Z.to_nat MAX - (length l + 1))%nat with n by omega.
  unfold upd_Znth, sublist; simpl.
  rewrite Zlength_cons.
  unfold Z.succ; rewrite Z.add_simpl_r.
  rewrite Zlength_correct, Nat2Z.id, firstn_exact_length.
  rewrite <- app_assoc; auto.
  { repeat rewrite Zlength_correct; omega. }
Qed.

Lemma Znth_complete : forall n l d MAX, n < Zlength l -> Znth n (complete MAX l) d = Znth n l d.
Proof.
  intros; apply app_Znth1; auto.
Qed.

Lemma remove_complete : forall l x MAX, Zlength l < MAX ->
  upd_Znth (Zlength l) (complete MAX (l ++ [x])) (vint 0) = complete MAX l.
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app1; [|repeat rewrite Zlength_correct; rewrite app_length; simpl; Omega0].
  rewrite app_length; simpl plus.
  rewrite upd_Znth_app2, Zminus_diag; [|rewrite Zlength_cons; simpl; omega].
  unfold upd_Znth, sublist.sublist.
  rewrite Zminus_diag; simpl firstn.
  rewrite Zlength_correct, Z2Nat.inj_lt, Nat2Z.id in H; try omega.
  destruct (Z.to_nat MAX - length l)%nat eqn: Hminus; [omega|].
  replace (Z.to_nat MAX - (length l + 1))%nat with n by omega.
  simpl.
  rewrite <- app_assoc; auto.
Qed.

Lemma Forall_app : forall {A} (P : A -> Prop) l1 l2,
  Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; split; auto; intros.
  - destruct H; auto.
  - inversion H as [|??? H']; subst.
    rewrite IHl1 in H'; destruct H'; split; auto.
  - destruct H as (H & ?); inv H; constructor; auto.
    rewrite IHl1; split; auto.
Qed.

Lemma repeat_plus : forall {A} (x : A) i j, repeat x (i + j) = repeat x i ++ repeat x j.
Proof.
  induction i; auto; simpl; intro.
  rewrite IHi; auto.
Qed.

Definition remove_at {A} i (l : list A) := firstn i l ++ skipn (S i) l.

Lemma Forall_firstn : forall {A} (P : A -> Prop) l i, Forall P l ->
  Forall P (firstn i l).
Proof.
  intros; rewrite Forall_forall in *.
  intros ? Hin; pose proof (firstn_In _ _ _ Hin); auto.
Qed.

Lemma Forall_skipn : forall {A} (P : A -> Prop) l i, Forall P l ->
  Forall P (skipn i l).
Proof.
  intros; rewrite Forall_forall in *.
  intros ? Hin; pose proof (skipn_In _ _ _ Hin); auto.
Qed.

Lemma Forall_upd_Znth : forall {A} (P : A -> Prop) x l i, Forall P l -> P x ->
  Forall P (upd_Znth i l x).
Proof.
  intros; unfold upd_Znth.
  rewrite Forall_app; split; [|constructor; auto]; apply Forall_sublist; auto.
Qed.

Lemma last_cons : forall {A} (d : A) l x, l <> [] -> last (x :: l) d = last l d.
Proof.
  intros.
  destruct l; auto.
  contradiction H; auto.
Qed.

Lemma nth_last : forall {A} (d : A) l, nth (length l - 1) l d = last l d.
Proof.
  induction l; auto.
  simpl nth.
  destruct (length l) eqn: Hlen.
  { destruct l; simpl in *; [auto | omega]. }
  rewrite last_cons; simpl in *; [|intro; subst; discriminate].
  rewrite NPeano.Nat.sub_0_r in IHl; auto.
Qed.

Lemma Znth_last : forall {A} l (d : A), Znth (Zlength l - 1) l d = last l d.
Proof.
  intros; unfold Znth.
  destruct (zlt (Zlength l - 1) 0).
  - destruct l; auto.
    rewrite Zlength_correct in *; simpl length in *.
    rewrite Nat2Z.inj_succ in *; omega.
  - rewrite Z2Nat.inj_sub; [|omega].
    rewrite Zlength_correct, Nat2Z.id; simpl.
    apply nth_last.
Qed.

Lemma Forall2_In_l : forall {A B} (P : A -> B -> Prop) x l1 l2, Forall2 P l1 l2 -> In x l1 ->
  exists y, In y l2 /\ P x y.
Proof.
  induction 1; intro Hin; destruct Hin; simpl.
  - subst; eauto.
  - destruct IHForall2 as (? & ? & ?); eauto.
Qed.

Lemma Forall2_In_r : forall {A B} (P : A -> B -> Prop) x l1 l2, Forall2 P l1 l2 -> In x l2 ->
  exists y, In y l1 /\ P y x.
Proof.
  induction 1; intro Hin; destruct Hin; simpl.
  - subst; eauto.
  - destruct IHForall2 as (? & ? & ?); eauto.
Qed.

Lemma last_snoc : forall {A} (d : A) x l, last (l ++ [x]) d = x.
Proof.
  induction l; auto; simpl.
  destruct (l ++ [x]) eqn: Heq; auto.
  contradiction (app_cons_not_nil l [] x); auto.
Qed.

Lemma sepcon_app : forall l1 l2, fold_right sepcon emp (l1 ++ l2) =
  fold_right sepcon emp l1 * fold_right sepcon emp l2.
Proof.
  induction l1; simpl; intros.
  - rewrite emp_sepcon; auto.
  - rewrite IHl1, sepcon_assoc; auto.
Qed.

Definition rotate {A} (l : list A) n m := sublist (m - n) (Zlength l) l ++
  sublist 0 (m - n) l.

Lemma sublist_of_nil : forall {A} i j, sublist i j (@nil A) = [].
Proof.
  intros; unfold sublist.
  rewrite skipn_nil, firstn_nil; auto.
Qed.

Lemma sublist_0_cons : forall {A} j x (l : list A), j > 0 ->
  sublist 0 j (x :: l) = x :: sublist 0 (j - 1) l.
Proof.
  intros; unfold sublist; simpl.
  destruct (Z.to_nat (j - 0)) eqn: Hminus.
  - apply Z.gt_lt in H; rewrite Z2Nat.inj_lt in H; try omega.
    rewrite Z2Nat.inj_sub in Hminus; omega.
  - simpl; repeat f_equal.
    rewrite Z.sub_0_r in *.
    rewrite Z2Nat.inj_sub, Hminus; simpl; omega.
Qed.

Lemma sublist_S_cons : forall {A} i j x (l : list A), i > 0 ->
  sublist i j (x :: l) = sublist (i - 1) (j - 1) l.
Proof.
  intros; unfold sublist; simpl.
  destruct (Z.to_nat i) eqn: Hi.
  - apply Z.gt_lt in H; rewrite Z2Nat.inj_lt in H; omega.
  - simpl.
    f_equal; f_equal; try omega.
    rewrite Z2Nat.inj_sub, Hi; simpl; omega.
Qed.

Lemma upd_rotate : forall {A} i (l : list A) n m x (Hl : Zlength l = m) (Hlt : 0 <= n <= m)
  (Hi : 0 <= i < Zlength l),
  upd_Znth i (rotate l n m) x = rotate (upd_Znth ((i - n) mod m) l x) n m.
Proof.
  intros; unfold rotate.
  rewrite upd_Znth_Zlength by (subst; apply Z_mod_lt; omega).
  destruct (zlt i (Zlength l - (m - n))).
  - rewrite upd_Znth_app1 by (rewrite Zlength_sublist; omega).
    assert ((i - n) mod m = m + i - n) as Hmod.
    { rewrite <- Z.mod_add with (b := 1) by omega.
      rewrite Zmod_small; omega. }
    rewrite Hmod, sublist_upd_Znth_lr, sublist_upd_Znth_l by (auto; omega).
    replace (m + i - n - (m - n)) with i by omega; auto.
  - rewrite upd_Znth_app2; rewrite ?Zlength_sublist; try omega.
    assert ((i - n) mod m = i - n) as Hmod.
    { rewrite Zmod_small; omega. }
    rewrite Hmod, sublist_upd_Znth_r, sublist_upd_Znth_lr by omega.
    replace (i - (Zlength l - (m - n))) with (i - n - 0) by omega; auto.
Qed.

Lemma Znth_cons_eq : forall {A} (d : A) i x l, Znth i (x :: l) d = if eq_dec i 0 then x else Znth (i - 1) l d.
Proof.
  intros.
  destruct (eq_dec i 0); [subst; apply Znth_0_cons|].
  destruct (zlt i 0); [rewrite !Znth_underflow; auto; omega|].
  apply Znth_pos_cons; omega.
Qed.

Lemma Znth_rotate : forall {A} (d : A) i l n, 0 <= n <= Zlength l -> 0 <= i < Zlength l ->
  Znth i (rotate l n (Zlength l)) d = Znth ((i - n) mod Zlength l) l d.
Proof.
  intros; unfold rotate.
  destruct (zlt i n).
  - rewrite app_Znth1 by (rewrite Zlength_sublist; omega).
    rewrite Znth_sublist by omega.
    rewrite <- Z_mod_plus with (b := 1), Zmod_small by omega.
    f_equal; omega.
  - rewrite app_Znth2; (rewrite Zlength_sublist; try omega).
    rewrite Znth_sublist by omega.
    rewrite Zmod_small by omega.
    f_equal; omega.
Qed.

Lemma rotate_nil : forall {A} n m, rotate (@nil A) n m = [].
Proof.
  intros; unfold rotate; rewrite !sublist_of_nil; auto.
Qed.

Lemma Forall_sublist_le : forall {A} (P : A -> Prop) i j l d
  (Hrangei : 0 <= i) (Hrangej : j <= Zlength l) (Hi : ~P (Znth i l d)) (Hj : Forall P (sublist 0 j l)),
  j <= i.
Proof.
  intros.
  destruct (Z_le_dec j i); auto.
  eapply Forall_Znth with (i0 := i) in Hj; [|rewrite Zlength_sublist; omega].
  rewrite Znth_sublist, Z.add_0_r in Hj by omega.
  contradiction Hi; eauto.
Qed.

Corollary Forall_sublist_first : forall {A} (P : A -> Prop) i j l d
  (Hrangei : 0 <= i <= Zlength l) (Hi : Forall P (sublist 0 i l)) (Hi' : ~P (Znth i l d))
  (Hrangej : 0 <= j <= Zlength l) (Hj : Forall P (sublist 0 j l)) (Hj' : ~P (Znth j l d)),
  i = j.
Proof.
  intros.
  apply Z.le_antisymm; eapply Forall_sublist_le; eauto; omega.
Qed.

Lemma Znth_In : forall {A} i l (d : A), 0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); [omega|].
  apply nth_In; rewrite Zlength_correct in *; Omega0.
Qed.

Lemma NoDup_Znth_inj : forall {A} (d : A) l i j (HNoDup : NoDup l)
  (Hi : 0 <= i < Zlength l) (Hj : 0 <= j < Zlength l) (Heq : Znth i l d = Znth j l d),
  i = j.
Proof.
  induction l; intros.
  { rewrite Zlength_nil in *; omega. }
  inv HNoDup.
  rewrite Zlength_cons in *.
  rewrite !Znth_cons_eq in Heq.
  destruct (eq_dec i 0), (eq_dec j 0); subst; auto.
  - contradiction H1; apply Znth_In; omega.
  - contradiction H1; apply Znth_In; omega.
  - exploit (IHl (i - 1) (j - 1)); auto; omega.
Qed.

Lemma rotate_In : forall {A} (x : A) n m l, 0 <= m - n <= Zlength l -> In x (rotate l n m) <-> In x l.
Proof.
  unfold rotate; intros.
  replace l with (sublist 0 (m - n) l ++ sublist (m - n) (Zlength l) l) at 4
    by (rewrite sublist_rejoin, sublist_same; auto; omega).
  rewrite !in_app; tauto.
Qed.

Lemma rotate_map : forall {A B} (f : A -> B) n m l, rotate (map f l) n m = map f (rotate l n m).
Proof.
  intros; unfold rotate.
  rewrite !sublist_map, Zlength_map, map_app; auto.
Qed.

Lemma combine_app : forall {A B} (l1 l2 : list A) (l1' l2' : list B), length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1; destruct l1'; intros; try discriminate; auto; simpl in *.
  rewrite IHl1; auto.
Qed.

Lemma Forall_rotate : forall {A} P (l : list A) n m, Forall P l ->
  Forall P (rotate l m n).
Proof.
  intros; unfold rotate.
  rewrite Forall_app; split; apply Forall_sublist; auto.
Qed.

Lemma Forall_repeat : forall {A} (P : A -> Prop) x n, P x -> Forall P (repeat x n).
Proof.
  induction n; simpl; auto.
Qed.

Lemma Forall_complete : forall P l m, Forall P l -> P (vint 0) ->
  Forall P (complete m l).
Proof.
  intros; unfold complete.
  rewrite Forall_app; split; [|apply Forall_repeat]; auto.
Qed.

Lemma app_eq_inv : forall {A} (l1 l2 l3 l4 : list A)
  (Heq : l1 ++ l2 = l3 ++ l4) (Hlen : length l1 = length l3), l1 = l3 /\ l2 = l4.
Proof.
  induction l1; simpl; intros; destruct l3; try discriminate; auto.
  inv Heq; inv Hlen.
  exploit IHl1; eauto; intros (? & ?); subst; auto.
Qed.

Lemma rotate_inj : forall {A} (l1 l2 : list A) n m, rotate l1 n m = rotate l2 n m ->
  length l1 = length l2 -> 0 <= n <= m -> m <= Zlength l1 -> l1 = l2.
Proof.
  unfold rotate; intros.
  destruct (app_eq_inv _ _ _ _ H) as (Hskip & Hfirst).
  { unfold sublist; repeat rewrite firstn_length, skipn_length.
    repeat rewrite Zlength_correct; rewrite H0; omega. }
  erewrite <- sublist_same with (al := l1), <- sublist_rejoin with (mid := m - n); auto; try omega.
  rewrite Hfirst, Hskip, sublist_rejoin, sublist_same; auto; try omega.
  repeat rewrite Zlength_correct in *; rewrite H0 in *; omega.
Qed.

Lemma complete_inj : forall l1 l2 m, complete m l1 = complete m l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  unfold complete; intros.
  destruct (app_eq_inv _ _ _ _ H); auto.
Qed.

Lemma length_complete : forall l m, Zlength l <= m -> length (complete m l) = Z.to_nat m.
Proof.
  intros; unfold complete.
  rewrite app_length, repeat_length; rewrite Zlength_correct in H; Omega0.
Qed.

Lemma Zlength_rotate : forall {A} (l : list A) n m, 0 <= n <= m -> m <= Zlength l ->
  Zlength (rotate l n m) = Zlength l.
Proof.
  intros; unfold rotate.
  rewrite Zlength_app; repeat rewrite Zlength_sublist; omega.
Qed.

Lemma Zlength_repeat : forall {A} (x : A) n, Zlength (repeat x n) = Z.of_nat n.
Proof.
  intros; rewrite Zlength_correct, repeat_length; auto.
Qed.

Lemma Zlength_complete : forall l m, Zlength l <= m -> Zlength (complete m l) = m.
Proof.
  intros; unfold complete.
  rewrite Zlength_app, Zlength_repeat; rewrite Zlength_correct in *; Omega0.
Qed.

Lemma combine_eq : forall {A B} (l : list (A * B)), combine (map fst l) (map snd l) = l.
Proof.
  induction l; auto; simpl.
  destruct a; rewrite IHl; auto.
Qed.

Lemma signed_inj : forall i1 i2, Int.signed i1 = Int.signed i2 -> i1 = i2.
Proof.
  intros.
  apply int_eq_e.
  rewrite Int.eq_signed, H.
  apply zeq_true.
Qed.

Lemma mods_repr : forall a b, 0 <= a <= Int.max_signed -> 0 < b <= Int.max_signed ->
  Int.mods (Int.repr a) (Int.repr b) = Int.repr (a mod b).
Proof.
  intros.
  unfold Int.mods.
  pose proof Int.min_signed_neg.
  rewrite Zquot.Zrem_Zmod_pos; repeat rewrite Int.signed_repr; auto; omega.
Qed.

Lemma repeat_list_repeat : forall {A} n (x : A), repeat x n = list_repeat n x.
Proof.
  induction n; auto; simpl; intro.
  rewrite IHn; auto.
Qed.

Lemma sublist_repeat : forall {A} i j k (v : A), 0 <= i -> i <= j <= k ->
  sublist i j (repeat v (Z.to_nat k)) = repeat v (Z.to_nat (j - i)).
Proof.
  intros; repeat rewrite repeat_list_repeat; apply sublist_list_repeat; auto.
Qed.

Lemma Znth_head : forall reqs head m d, Zlength reqs <= m -> 0 <= head < m ->
  Zlength reqs > 0 ->
  Znth head (rotate (complete m reqs) head m) d = Znth 0 reqs d.
Proof.
  intros; unfold rotate.
  assert (Zlength (sublist (m - head) (Zlength (complete m reqs)) (complete m reqs)) = head) as Hlen.
  { rewrite Zlength_sublist; rewrite Zlength_complete; omega. }
  rewrite app_Znth2; rewrite Hlen; [|omega].
  rewrite Zminus_diag.
  rewrite Znth_sublist; try omega.
  rewrite Znth_complete; auto; omega.
Qed.

Lemma Znth_repeat : forall {A} (x : A) n i, Znth i (repeat x n) x = x.
Proof.
  induction n; simpl; intro.
  - apply Znth_nil.
  - destruct (Z_lt_dec i 0); [apply Znth_underflow; auto|].
    destruct (eq_dec i 0); [subst; apply Znth_0_cons | rewrite Znth_pos_cons; eauto; omega].
Qed.

Lemma rotate_1 : forall v l n m, 0 <= n < m -> Zlength l < m ->
  rotate (upd_Znth 0 (complete m (v :: l)) (vint 0)) n m =
  rotate (complete m l) ((n + 1) mod m) m.
Proof.
  intros.
  unfold complete at 1; simpl.
  unfold upd_Znth; simpl.
  rewrite Zlength_cons; simpl.
  rewrite sublist_1_cons, sublist_same; auto; [|omega].
  unfold rotate.
  rewrite Zlength_cons; simpl.
  rewrite sublist_S_cons; [|omega].
  rewrite sublist_0_cons; [|omega].
  destruct (eq_dec (n + 1) m).
  - subst; rewrite Z.mod_same; [|omega].
    autorewrite with sublist.
    rewrite Zlength_complete, sublist_nil; [|omega].
    rewrite sublist_same; auto; [|rewrite Zlength_complete; omega].
    rewrite <- app_assoc; unfold complete.
    repeat rewrite Z2Nat.inj_add; try omega.
    rewrite NPeano.Nat.add_sub_swap with (p := length l); [|rewrite Zlength_correct in *; Omega0].
    rewrite repeat_plus; simpl; do 3 f_equal; omega.
  - rewrite Zmod_small; [|omega].
    rewrite (sublist_split (m - (n + 1)) (Zlength (complete m l) - 1)); try rewrite Zlength_complete; try omega.
    rewrite <- app_assoc, (sublist_one (m - 1)) with (d := vint 0); try rewrite Zlength_complete; try omega; simpl.
    assert (length l < Z.to_nat m)%nat by (rewrite Zlength_correct in *; Omega0).
    unfold complete.
    replace (Z.to_nat m - length l)%nat with (Z.to_nat m - S (length l) + 1)%nat; [|omega].
    rewrite repeat_plus, app_assoc; simpl.
    repeat rewrite Zlength_app.
    assert (m - 1 = Zlength l + Zlength (repeat (vint 0) (Z.to_nat m - S (Datatypes.length l)))) as Heq.
    { rewrite Zlength_repeat, Nat2Z.inj_sub, Z2Nat.id, Nat2Z.inj_succ, <- Zlength_correct; omega. }
    rewrite (sublist_app1 _ _ _ (_ ++ _)); try rewrite Zlength_app; try omega.
    rewrite (sublist_app1 _ _ _ (_ ++ _)); try rewrite Zlength_app; try omega.
    f_equal; f_equal; try omega.
    + rewrite app_Znth2, Zlength_app, Heq, Zminus_diag, Znth_0_cons; auto.
      rewrite Zlength_app; omega.
    + f_equal; omega.
Qed.

Lemma upd_complete_gen : forall {A} (l : list A) x n y, Zlength l < n ->
  upd_Znth (Zlength l) (l ++ repeat y (Z.to_nat (n - Zlength l))) x =
  (l ++ [x]) ++ repeat y (Z.to_nat (n - Zlength (l ++ [x]))).
Proof.
  intros.
  rewrite upd_Znth_app2, Zminus_diag.
  destruct (Z.to_nat (n - Zlength l)) eqn: Hn.
  - apply Z2Nat.inj with (m := 0) in Hn; omega.
  - simpl; rewrite upd_Znth0, Zlength_cons, sublist_1_cons.
    unfold Z.succ; rewrite Z.add_simpl_r, sublist_same; auto.
    rewrite <- app_assoc, Zlength_app, Zlength_cons, Zlength_nil; simpl.
    rewrite Z.sub_add_distr, Z2Nat.inj_sub, Hn by computable; simpl.
    rewrite Nat.sub_0_r; auto.
  - pose proof (Zlength_nonneg (repeat y (Z.to_nat (n - Zlength l)))); omega.
Qed.

Lemma upd_complete' : forall l x n, (length l < n)%nat ->
  upd_Znth (Zlength l) (map Vint (map Int.repr l) ++ repeat Vundef (n - length l)) (Vint (Int.repr x)) =
  map Vint (map Int.repr (l ++ [x])) ++ repeat Vundef (n - length (l ++ [x])).
Proof.
  intros.
  rewrite upd_Znth_app2; [|repeat rewrite Zlength_map; repeat rewrite Zlength_correct; omega].
  repeat rewrite Zlength_map.
  rewrite Zminus_diag.
  rewrite app_length; simpl plus.
  destruct (n - length l)%nat eqn: Hminus; [omega|].
  replace (n - (length l + 1))%nat with n0 by omega.
  rewrite upd_Znth0, !map_app, <- app_assoc; simpl.
  rewrite sublist_1_cons, Zlength_cons, sublist_same; auto; omega.
Qed.

Lemma Znth_indep : forall {A} i (l : list A) d d', 0 <= i < Zlength l -> Znth i l d = Znth i l d'.
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); [omega|].
  apply nth_indep.
  rewrite Zlength_correct in *; Omega0.
Qed.

Fixpoint upto n :=
  match n with
  | O => []
  | S n' => 0 :: map Z.succ (upto n')
  end.

Opaque Z.of_nat.

Lemma upto_app : forall n m, upto (n + m) = upto n ++ map (fun i => Z.of_nat n + i) (upto m).
Proof.
  induction n; simpl; intro.
  - rewrite map_id; auto.
  - rewrite IHn, map_app, map_map, Nat2Z.inj_succ; f_equal; f_equal.
    apply map_ext; intro; omega.
Qed.

Lemma upto_length : forall n, length (upto n) = n.
Proof.
  induction n; auto; simpl.
  rewrite map_length, IHn; auto.
Qed.

Corollary Zlength_upto : forall n, Zlength (upto n) = Z.of_nat n.
Proof.
  intro; rewrite Zlength_correct, upto_length; auto.
Qed.

Lemma skipn_cons : forall {A} n (l : list A) d, (length l > n)%nat ->
  skipn n l = Znth (Z.of_nat n) l d :: skipn (S n) l.
Proof.
  induction n; intros; simpl; destruct l; simpl in *; try omega; auto.
  { inversion H. }
  rewrite Nat2Z.inj_succ.
  rewrite Znth_pos_cons; [|omega].
  unfold Z.succ; rewrite Z.add_simpl_r.
  erewrite IHn; auto; omega.
Qed.

Lemma Znth_map' : forall {A B} i (f : A -> B) al b, Znth i (map f al) (f b) = f (Znth i al b).
Proof.
  unfold Znth; intros.
  destruct (zlt i 0); auto.
  apply map_nth.
Qed.

Lemma Znth_upto : forall m n, 0 <= n <= Z.of_nat m -> Znth n (upto m) (Z.of_nat m) = n.
Proof.
  induction m; simpl; intros.
  - rewrite Znth_nil; simpl in *; rewrite Nat2Z.inj_0 in *; omega.
  - destruct (eq_dec n 0).
    + subst; apply Znth_0_cons.
    + rewrite Nat2Z.inj_succ in *.
      erewrite Znth_pos_cons, Znth_map', IHm; try omega.
Qed.

Transparent Z.of_nat.

Lemma In_Znth : forall {A} l (x d : A), In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros.
  destruct (In_nth _ _ d H) as (n & ? & ?).
  exists (Z.of_nat n); unfold Znth.
  split; [rewrite Zlength_correct; Omega0|].
  rewrite Nat2Z.id; destruct (zlt (Z.of_nat n) 0); auto; omega.
Qed.

Lemma Znth_combine : forall {A B} i l1 l2 (a : A) (b : B), Zlength l1 = Zlength l2 ->
  Znth i (combine l1 l2) (a, b) = (Znth i l1 a, Znth i l2 b).
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); auto.
  apply combine_nth.
  rewrite !Zlength_correct in *; Omega0.
Qed.

Lemma Zlength_combine : forall {A B} (l : list A) (l' : list B),
  Zlength (combine l l') = Z.min (Zlength l) (Zlength l').
Proof.
  intros; rewrite !Zlength_correct, combine_length, Nat2Z.inj_min; auto.
Qed.

Lemma nth_Znth : forall {A} i l (d : A), nth i l d = Znth (Z.of_nat i) l d.
Proof.
  intros; unfold Znth.
  destruct (zlt (Z.of_nat i) 0); [omega|].
  rewrite Nat2Z.id; auto.
Qed.

Lemma upd_Znth_cons : forall {A} i a l (x : A), i > 0 ->
  upd_Znth i (a :: l) x = a :: upd_Znth (i - 1) l x.
Proof.
  intros; unfold upd_Znth, sublist.sublist; simpl.
  repeat rewrite Z.sub_0_r.
  destruct (Z.to_nat i) eqn: Hi.
  { exploit Z2Nat_inj_0; eauto; omega. }
  rewrite Zlength_cons; repeat rewrite Z2Nat.inj_add; try omega.
  repeat rewrite Z2Nat.inj_sub; try omega.
  rewrite Hi; simpl.
  rewrite Nat.sub_0_r.
  do 4 f_equal.
  rewrite Z2Nat.inj_succ; [|rewrite Zlength_correct; omega].
  repeat rewrite Z2Nat.inj_add; try omega.
  rewrite Z2Nat.inj_sub; try omega.
  simpl plus; omega.
Qed.

Lemma upd_Znth_triv : forall {A} i (l : list A) x d (Hi : 0 <= i < Zlength l),
  Znth i l d = x -> upd_Znth i l x = l.
Proof.
  intros; unfold upd_Znth.
  setoid_rewrite <- (firstn_skipn (Z.to_nat i) l) at 4.
  erewrite skipn_cons, Z2Nat.id, H; try omega; [|rewrite Zlength_correct in *; Omega0].
  unfold sublist.
  rewrite Z.sub_0_r, Z2Nat.inj_add, NPeano.Nat.add_1_r; try omega.
  setoid_rewrite firstn_same at 2; auto.
  rewrite Z2Nat.inj_sub, Zlength_correct, Nat2Z.id, Z2Nat.inj_add, skipn_length; simpl; omega.
Qed.

Lemma combine_upd_Znth : forall {A B} (l1 : list A) (l2 : list B) i x1 x2, 0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 -> combine (upd_Znth i l1 x1) (upd_Znth i l2 x2) = upd_Znth i (combine l1 l2) (x1, x2).
Proof.
  induction l1; simpl; intros; [rewrite Zlength_nil in *; omega|].
  destruct l2; [rewrite Zlength_nil in *; omega|].
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0).
  - subst; rewrite !upd_Znth0, !Zlength_cons, !sublist_1_cons, !sublist_same; auto; omega.
  - rewrite !upd_Znth_cons; try omega; simpl.
    rewrite IHl1; auto; omega.
Qed.

Corollary combine_upd_Znth1 : forall {A B} (l1 : list A) (l2 : list B) i x d, 0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 -> combine (upd_Znth i l1 x) l2 = upd_Znth i (combine l1 l2) (x, Znth i l2 d).
Proof.
  intros; rewrite <- combine_upd_Znth by auto.
  erewrite upd_Znth_triv with (l := l2); eauto; omega.
Qed.

Corollary combine_upd_Znth2 : forall {A B} (l1 : list A) (l2 : list B) i x d, 0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 -> combine l1 (upd_Znth i l2 x) = upd_Znth i (combine l1 l2) (Znth i l1 d, x).
Proof.
  intros; rewrite <- combine_upd_Znth by auto.
  erewrite upd_Znth_triv with (l := l1); eauto; omega.
Qed.

Lemma sepcon_rev : forall l, fold_right sepcon emp (rev l) = fold_right sepcon emp l.
Proof.
  induction l; simpl; auto.
  rewrite sepcon_app; simpl.
  rewrite sepcon_emp, sepcon_comm, IHl; auto.
Qed.

Lemma incl_nil : forall {A} (l : list A), incl [] l.
Proof.
  repeat intro; contradiction.
Qed.
Hint Resolve incl_nil.

Lemma In_upto : forall n i, In i (upto n) <-> 0 <= i < Z.of_nat n.
Proof.
  induction n; intro.
  - simpl; split; try contradiction; omega.
  - rewrite Nat2Z.inj_succ; simpl.
    rewrite in_map_iff; split.
    + intros [? | ?]; [omega|].
      destruct H as (? & ? & ?); subst; rewrite IHn in *; omega.
    + intro; destruct (eq_dec i 0); [auto | right].
      exists (i - 1); rewrite IHn; omega.
Qed.

Lemma combine_fst : forall {A B} (l : list A) (l' : list B), length l = length l' ->
  map fst (combine l l') = l.
Proof.
  induction l; destruct l'; try discriminate; auto; intros.
  inv H; simpl; rewrite IHl; auto.
Qed.

Lemma combine_snd : forall {A B} (l : list A) (l' : list B), length l = length l' ->
  map snd (combine l l') = l'.
Proof.
  induction l; destruct l'; try discriminate; auto; intros.
  inv H; simpl; rewrite IHl; auto.
Qed.

Lemma rev_combine : forall {A B} (l1 : list A) (l2 : list B), length l1 = length l2 ->
  rev (combine l1 l2) = combine (rev l1) (rev l2).
Proof.
  induction l1; destruct l2; try discriminate; auto; simpl; intros.
  inv H; rewrite combine_app; [|rewrite !rev_length; auto].
  rewrite IHl1; auto.
Qed.

Lemma combine_map_snd : forall {A B C} (l1 : list A) (l2 : list B) (f : B -> C),
  combine l1 (map f l2) = map (fun x => let '(a, b) := x in (a, f b)) (combine l1 l2).
Proof.
  induction l1; auto; simpl; intros.
  destruct l2; auto; simpl.
  rewrite IHl1; auto.
Qed.

Lemma combine_const1 : forall {A B} (l1 : list A) (x : B) n, Z.of_nat n >= Zlength l1 ->
  combine l1 (repeat x n) = map (fun a => (a, x)) l1.
Proof.
  induction l1; auto; simpl; intros.
  rewrite Zlength_cons in *; destruct n; [rewrite Zlength_correct in *; simpl in *; omega | simpl].
  rewrite IHl1; auto.
  rewrite Nat2Z.inj_succ in *; omega.
Qed.

Lemma combine_const2 : forall {A B} (x : A) n (l2 : list B), Z.of_nat n >= Zlength l2 ->
  combine (repeat x n) l2 = map (fun b => (x, b)) l2.
Proof.
  induction n; destruct l2; auto; intros; rewrite ?Nat2Z.inj_succ, ?Zlength_nil, ?Zlength_cons in *;
    simpl in *; try (rewrite Zlength_correct in *; omega).
  rewrite IHn; auto; omega.
Qed.

Lemma In_upd_Znth : forall {A} i l (x y : A), In x (upd_Znth i l y) -> x = y \/ In x l.
Proof.
  unfold upd_Znth; intros.
  rewrite in_app in H; destruct H as [? | [? | ?]]; auto; right; eapply sublist_In; eauto.
Qed.

Lemma upd_Znth_In : forall {A} i l (x : A), In x (upd_Znth i l x).
Proof.
  intros; unfold upd_Znth.
  rewrite in_app; simpl; auto.
Qed.

Lemma NoDup_Znth_iff : forall {A} (l : list A) d,
  NoDup l <-> forall i j (Hi : 0 <= i < Zlength l) (Hj : 0 <= j < Zlength l), Znth i l d = Znth j l d -> i = j.
Proof.
  split; intros; [eapply NoDup_Znth_inj; eauto|].
  induction l; rewrite ?Zlength_cons in *; constructor.
  - intro Hin; eapply In_Znth in Hin; destruct Hin as (j & ? & Hj).
    exploit (H 0 (j + 1)); try omega.
    rewrite !Znth_cons_eq; simpl.
    if_tac; [omega|].
    rewrite Z.add_simpl_r; eauto.
  - apply IHl; intros.
    exploit (H (i + 1) (j + 1)); try omega.
    rewrite !Znth_cons_eq, !Z.add_simpl_r.
    if_tac; [omega|].
    if_tac; [omega | auto].
Qed.

Lemma Forall2_Znth : forall {A B} (P : A -> B -> Prop) l1 l2 d1 d2 (Hall : Forall2 P l1 l2) i
  (Hi : 0 <= i < Zlength l1), P (Znth i l1 d1) (Znth i l2 d2).
Proof.
  induction 1; intros.
  { rewrite Zlength_nil in *; omega. }
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0).
  - subst; rewrite !Znth_0_cons; auto.
  - rewrite !Znth_pos_cons; try omega.
    apply IHHall; omega.
Qed.

Lemma Forall2_app_inv : forall {A B} (P : A -> B -> Prop) l1 l2 l3 l4 (Hlen : length l1 = length l3),
  Forall2 P (l1 ++ l2) (l3 ++ l4) -> Forall2 P l1 l3 /\ Forall2 P l2 l4.
Proof.
  induction l1; destruct l3; try discriminate; auto; intros.
  inv H; inv Hlen.
  exploit IHl1; eauto; intros (? & ?); split; [constructor|]; auto.
Qed.

Lemma sublist_nil_gen : forall {A} (l : list A) i j, j <= i -> sublist i j l = [].
Proof.
  intros; unfold sublist.
  replace (Z.to_nat (j - i)) with O; auto.
  destruct (eq_dec (j - i) 0); try Omega0.
  rewrite Z2Nat_neg; auto; omega.
Qed.

Lemma Forall2_firstn : forall {A B} (P : A -> B -> Prop) l1 l2 n, Forall2 P l1 l2 ->
  Forall2 P (firstn n l1) (firstn n l2).
Proof.
  intros; revert n; induction H; intro.
  - rewrite !firstn_nil; auto.
  - destruct n; simpl; auto.
Qed.

Lemma Forall2_upd_Znth : forall {A B} (P : A -> B -> Prop) l1 l2 i x1 x2, Forall2 P l1 l2 ->
  P x1 x2 -> 0 <= i <= Zlength l1 -> Forall2 P (upd_Znth i l1 x1) (upd_Znth i l2 x2).
Proof.
  intros; unfold upd_Znth.
  pose proof (mem_lemmas.Forall2_Zlength H) as Hlen.
  erewrite <- sublist_same with (al := l1), sublist_split with (mid := i) in H; auto; try omega.
  erewrite <- sublist_same with (al := l2), sublist_split with (al := l2)(mid := i) in H; auto; try omega.
  apply Forall2_app_inv in H.
  destruct H as (? & Hall); apply Forall2_app; auto.
  constructor; auto.
  destruct (eq_dec i (Zlength l1)).
  - rewrite !sublist_nil_gen; auto; omega.
  - rewrite Z.add_comm.
    replace (Zlength l1) with (Zlength l1 - i + i) by omega.
    replace (Zlength l2) with (Zlength l2 - i + i) by omega.
    erewrite <- !sublist_sublist with (j := Zlength l1); try omega.
    inversion Hall as [Hl1 Hl2 | ?????? Hl1 Hl2].
    + rewrite !Hlen, <- Hl2.
      unfold sublist; rewrite !skipn_nil, !firstn_nil; auto.
    + rewrite sublist_1_cons, !Hlen, <- Hl2, sublist_1_cons.
      unfold sublist; simpl; apply Forall2_firstn; auto.
  - apply Nat2Z.inj; rewrite <- !Zlength_correct.
    autorewrite with sublist; auto.
Qed.

Lemma sublist_max_length : forall {A} i j (al : list A), Zlength (sublist i j al) <= Zlength al.
Proof.
  intros; unfold sublist.
  rewrite Zlength_firstn, Zlength_skipn.
  rewrite Z.min_le_iff; right.
  pose proof (Zlength_nonneg al).
  apply Z.max_lub; try omega.
  rewrite <- Z.le_sub_nonneg; apply Z.le_max_l.
Qed.

Lemma Forall2_sublist : forall {A B} (P : A -> B -> Prop) l1 l2 i j, Forall2 P l1 l2 -> 0 <= i ->
  Forall2 P (sublist i j l1) (sublist i j l2).
Proof.
  intros; revert j; revert dependent i; induction H; intros.
  - rewrite !sublist_of_nil; constructor.
  - destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto; constructor|].
    destruct (eq_dec i 0).
    + subst; rewrite !sublist_0_cons by omega.
      constructor; auto.
    + rewrite !sublist_S_cons by omega.
      apply IHForall2; omega.
Qed.

Lemma Forall_last : forall {A} (P : A -> Prop) d l, Forall P l -> P d -> P (last l d).
Proof.
  destruct l; auto.
  exploit (@app_removelast_last _ (a :: l) d); [discriminate | intro Hlast].
  intros; rewrite Forall_forall in H; apply H.
  rewrite Hlast at 2; rewrite in_app; simpl; auto.
Qed.

Lemma last_map : forall {A B} (f : A -> B) d l, f (last l d) = last (map f l) (f d).
Proof.
  induction l; auto; simpl.
  destruct l; auto.
Qed.

Lemma Forall2_upd_Znth_l : forall {A B} (P : A -> B -> Prop) l1 l2 i x d, Forall2 P l1 l2 ->
  P x (Znth i l2 d) -> 0 <= i < Zlength l1 -> Forall2 P (upd_Znth i l1 x) l2.
Proof.
  intros.
  erewrite <- upd_Znth_triv with (l := l2)(i0 := i); eauto.
  apply Forall2_upd_Znth; eauto; omega.
  apply mem_lemmas.Forall2_Zlength in H; omega.
Qed.

Lemma Forall2_upd_Znth_r : forall {A B} (P : A -> B -> Prop) l1 l2 i x d, Forall2 P l1 l2 ->
  P (Znth i l1 d) x -> 0 <= i < Zlength l1 -> Forall2 P l1 (upd_Znth i l2 x).
Proof.
  intros.
  erewrite <- upd_Znth_triv with (l := l1)(i0 := i) by (eauto; omega).
  apply Forall2_upd_Znth; eauto.
  apply mem_lemmas.Forall2_Zlength in H; omega.
Qed.

Lemma Forall2_eq_upto : forall {A B} (P : A -> B -> Prop) d1 d2 l1 l2, Forall2 P l1 l2 <->
  Zlength l1 = Zlength l2 /\ Forall (fun i => P (Znth i l1 d1) (Znth i l2 d2)) (upto (Z.to_nat (Zlength l1))).
Proof.
  induction l1; destruct l2; rewrite ?Zlength_cons, ?Zlength_nil; try solve [split; intro H; inv H;
    try (rewrite Zlength_correct in *; omega)]; simpl.
  - change (upto 0) with (@nil Z); split; auto.
  - rewrite Z2Nat.inj_succ by (apply Zlength_nonneg).
    rewrite <- Nat.add_1_l, upto_app, Forall_app, Forall_map.
    change (upto 1) with [0]; split; intro H.
    + inversion H as [|????? Hall]; subst.
      rewrite IHl1 in Hall; destruct Hall as (? & Hall).
      split; [congruence|].
      split; auto.
      rewrite Forall_forall in *; intros ? Hin.
      specialize (Hall _ Hin); simpl.
      rewrite In_upto in Hin.
      rewrite !Znth_pos_cons, Z.add_simpl_l by omega; auto.
    + destruct H as (? & Ha & Hall); inversion Ha as [|?? HP]; subst.
      rewrite !Znth_0_cons in HP.
      constructor; auto.
      rewrite IHl1; split; [omega|].
      rewrite Forall_forall in *; intros ? Hin.
      specialize (Hall _ Hin); simpl in *.
      rewrite In_upto in Hin.
      rewrite !Znth_pos_cons, Z.add_simpl_l in Hall by omega; auto.
Qed.

Lemma Znth_inbounds : forall {A} i (l : list A) d, Znth i l d <> d -> 0 <= i < Zlength l.
Proof.
  intros.
  destruct (zlt i 0); [contradiction H; apply Znth_underflow; auto|].
  destruct (Z_lt_dec i (Zlength l)); [omega|].
  rewrite Znth_overflow in H; [contradiction H; auto | omega].
Qed.

Lemma sublist_next : forall {A} i j l (d : A), 0 <= i < j -> j <= Zlength l ->
  sublist i j l = Znth i l d :: sublist (i + 1) j l.
Proof.
  intros.
  rewrite Znth_cons_sublist; [|omega].
  apply sublist_split; omega.
Qed.

Lemma upd_init : forall {A} (l : list A) i b v v', i < b -> Zlength l = i ->
  upd_Znth i (l ++ repeat v (Z.to_nat (b - i))) v' = l ++ v' :: repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_Znth_app2; rewrite ?Zlength_repeat, ?Z2Nat.id; try omega.
  subst; rewrite Zminus_diag, upd_Znth0.
  destruct (Z.to_nat (b - Zlength l)) eqn: Hi.
  { change O with (Z.to_nat 0) in Hi; apply Z2Nat.inj in Hi; omega. }
  simpl; rewrite sublist_1_cons, sublist_same; try rewrite Zlength_cons, !Zlength_repeat; try omega.
  replace (Z.to_nat (b - (Zlength l + 1))) with n; auto.
  rewrite Z.sub_add_distr, Z2Nat.inj_sub; try omega.
  setoid_rewrite Hi; simpl; omega.
Qed.

Corollary upd_init_const : forall {A} i b (v v' : A), 0 <= i < b ->
  upd_Znth i (repeat v' (Z.to_nat i) ++ repeat v (Z.to_nat (b - i))) v' =
  repeat v' (Z.to_nat (i + 1)) ++ repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_init; try rewrite Zlength_repeat, Z2Nat.id; auto; try omega.
  rewrite Z2Nat.inj_add, repeat_plus, <- app_assoc; auto; omega.
Qed.

Lemma list_Znth_eq : forall {A} d (l : list A), l = map (fun j => Znth j l d) (upto (length l)).
Proof.
  induction l; simpl; intros; auto.
  rewrite Znth_0_cons, IHl, map_map, map_length, upto_length.
  f_equal; apply map_ext_in; intros.
  rewrite Znth_pos_cons, <- IHl.
  unfold Z.succ; rewrite Z.add_simpl_r; auto.
  { rewrite In_upto in *; omega. }
Qed.

Arguments eq_dec _ _ _ _ : simpl never.

Lemma upd_Znth_eq : forall {A} {EqDec : EqDec A} (x d : A) (l : list A) i, 0 <= i < Zlength l ->
  upd_Znth i l x = map (fun j => if eq_dec j i then x else Znth j l d) (upto (length l)).
Proof.
  induction l; simpl; intros.
  { rewrite Zlength_nil in *; omega. }
  destruct (eq_dec 0 i).
  - subst; rewrite upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same; auto; try omega.
    rewrite list_Znth_eq with (l0 := l)(d0 := d) at 1.
    rewrite map_map.
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec (Z.succ a0) 0); [omega|].
    rewrite Znth_pos_cons; [|omega].
    f_equal; omega.
  - rewrite Znth_0_cons, upd_Znth_cons; [|omega].
    rewrite Zlength_cons in *.
    rewrite IHl, map_map; [|omega].
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec a0 (i - 1)), (eq_dec (Z.succ a0) i); try omega; auto.
    rewrite Znth_pos_cons; [|omega].
    f_equal; omega.
Qed.

Lemma upd_Znth_diff' : forall {A} i j l (u : A) d, 0 <= j < Zlength l -> i <> j ->
  Znth i (upd_Znth j l u) d = Znth i l d.
Proof.
  intros.
  destruct (zlt i 0).
  { rewrite !Znth_underflow; auto. }
  destruct (zlt i (Zlength l)).
  apply upd_Znth_diff; auto; omega.
  { rewrite !Znth_overflow; auto.
    rewrite upd_Znth_Zlength; auto. }
Qed.

Lemma list_nth_error_eq : forall {A} (l1 l2 : list A)
  (Heq : forall j, nth_error l1 j = nth_error l2 j), l1 = l2.
Proof.
  induction l1; destruct l2; auto; intros; try (specialize (Heq O); simpl in Heq; discriminate).
  erewrite IHl1.
  - specialize (Heq O); inv Heq; eauto.
  - intro j; specialize (Heq (S j)); auto.
Qed.

Lemma list_Znth_eq' : forall {A} d (l1 l2 : list A)
  (Hlen : Zlength l1 = Zlength l2)
  (Heq : forall j, 0 <= j < Zlength l1 -> Znth j l1 d = Znth j l2 d), l1 = l2.
Proof.
  induction l1; destruct l2; intros; rewrite ?Zlength_cons in *; rewrite ?Zlength_nil in *;
    auto; try (rewrite Zlength_correct in *; omega).
  exploit (Heq 0); [rewrite Zlength_correct; omega|].
  rewrite !Znth_0_cons; intro; subst.
  f_equal; apply IHl1; [omega|].
  intros; specialize (Heq (j + 1)); rewrite !Znth_pos_cons in Heq; try omega.
  rewrite !Z.add_simpl_r in *; apply Heq; omega.
Qed.

Corollary upd_Znth_eq' : forall {A} x d (l1 l2 : list A) i (Hi : 0 <= i < Zlength l1)
  (Hlen : Zlength l1 = Zlength l2)
  (Heq : forall j, 0 <= j < Zlength l1 -> j <> i -> Znth j l1 d = Znth j l2 d),
  upd_Znth i l1 x = upd_Znth i l2 x.
Proof.
  intros.
  assert (Zlength (upd_Znth i l1 x) = Zlength (upd_Znth i l2 x)).
  { rewrite !upd_Znth_Zlength; auto; omega. }
  apply list_Znth_eq' with (d0 := d); auto.
  intros ? Hj; destruct (eq_dec j i).
  - subst; rewrite !upd_Znth_same; auto; omega.
  - rewrite !upd_Znth_diff'; rewrite upd_Znth_Zlength in Hj; auto; omega.
Qed.

Lemma upd_Znth_twice : forall {A} i l (x y : A), 0 <= i < Zlength l ->
  upd_Znth i (upd_Znth i l x) y = upd_Znth i l y.
Proof.
  intros; unfold upd_Znth.
  rewrite !sublist_app; rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_sublist; try omega.
  rewrite 2Z.min_l, 2Z.min_r, 2Z.max_r, 2Z.max_l; try omega.
  rewrite !sublist_nil, app_nil_r; simpl.
  rewrite sublist_S_cons, !sublist_sublist; try omega.
  f_equal; f_equal; [|f_equal]; omega.
Qed.

Lemma hd_Znth : forall {A} d (l : list A), hd d l = Znth 0 l d.
Proof.
  destruct l; auto.
Qed.

Lemma NoDup_filter : forall {A} (f : A -> bool) l, NoDup l -> NoDup (filter f l).
Proof.
  induction l; simpl; intros; auto.
  inv H.
  destruct (f a); auto.
  constructor; auto.
  rewrite filter_In; intros (? & ?); contradiction.
Qed.

Lemma list_in_count : forall {A} {A_eq : EqDec A} (l l' : list A), NoDup l' ->
  (length (filter (fun x => if in_dec eq_dec x l then true else false) l') <= length l)%nat.
Proof.
  intros.
  apply NoDup_incl_length; [apply NoDup_filter; auto|].
  intros ? Hin.
  rewrite filter_In in Hin; destruct Hin.
  destruct (in_dec eq_dec a l); [auto | discriminate].
Qed.

Lemma filter_length : forall {A} (f : A -> bool) l,
  length l = (length (filter f l) + length (filter (fun x => negb (f x)) l))%nat.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl.
  destruct (f a); simpl; omega.
Qed.

Lemma NoDup_upto : forall n, NoDup (upto n).
Proof.
  induction n; simpl; constructor.
  - rewrite in_map_iff.
    intros (? & ? & ?); rewrite In_upto in *; omega.
  - apply FinFun.Injective_map_NoDup; auto.
    intros ???; omega.
Qed.

Lemma list_pigeonhole : forall l n, Zlength l < n -> exists a, 0 <= a < n /\ ~In a l.
Proof.
  intros.
  pose proof (filter_length (fun x => if in_dec eq_dec x l then true else false) (upto (Z.to_nat n))) as Hlen.
  rewrite upto_length in Hlen.
  assert (length (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n))) > 0)%nat.
  { exploit (list_in_count l (upto (Z.to_nat n))).
    { apply NoDup_upto. }
    rewrite Zlength_correct in H.
    apply Z2Nat.inj_lt in H; try omega.
    rewrite Nat2Z.id in H; omega. }
  destruct (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n))) eqn: Hfilter;
    [simpl in *; omega|].
  assert (In z (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n)))) as Hin
    by (rewrite Hfilter; simpl; auto).
  rewrite filter_In, In_upto, Z2Nat.id in Hin; [|rewrite Zlength_correct in *; omega].
  destruct Hin; destruct (in_dec eq_dec z l); try discriminate; eauto.
Qed.

Lemma In_sublist_upto : forall n x i j, In x (sublist i j (upto n)) -> 0 <= i ->
  i <= x < j /\ x < Z.of_nat n.
Proof.
  induction n; intros.
  - unfold sublist in H; rewrite skipn_nil, firstn_nil in H; contradiction.
  - rewrite Nat2Z.inj_succ; simpl in *.
    destruct (zlt 0 j).
    destruct (eq_dec i 0).
    + subst; rewrite sublist_0_cons in H; try omega; destruct H; [omega|].
      rewrite sublist_map, in_map_iff in H; destruct H as (? & ? & H); subst.
      destruct (zlt 0 (j - 1)).
      exploit IHn; eauto; omega.
      { rewrite sublist_nil_gen in H; [contradiction | omega]. }
    + rewrite sublist_S_cons in H; [|omega].
      rewrite sublist_map, in_map_iff in H; destruct H as (? & ? & H); subst.
      destruct (zlt 0 (j - 1)).
      exploit IHn; eauto; omega.
      { rewrite sublist_nil_gen in H; [contradiction | omega]. }
    + rewrite sublist_nil_gen in H; [contradiction | omega].
Qed.

Lemma incl_cons_iff : forall {A} (a : A) b c, incl (a :: b) c <-> In a c /\ incl b c.
Proof.
  split; intro.
  - split; [|eapply incl_cons_inv; eauto].
    specialize (H a); apply H; simpl; auto.
  - destruct H; intros ? [? | ?]; subst; auto.
Qed.

Lemma NoDup_app : forall {A} (l1 l2 : list A), NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2 /\ forall x, In x l1 -> ~In x l2.
Proof.
  induction l1; intros.
  - repeat split; auto; constructor.
  - inv H.
    exploit IHl1; eauto; intros (? & ? & ?).
    rewrite in_app in *.
    repeat split; auto.
    + constructor; auto.
    + intros ? [? | ?]; auto; subst; auto.
Qed.

Lemma lt_le_1 : forall i j, i < j <-> i + 1 <= j.
Proof.
  intros; omega.
Qed.

Lemma firstn_all : forall {A} n (l : list A), (length l <= n)%nat -> firstn n l = l.
Proof.
  induction n; destruct l; auto; simpl; intros; try omega.
  rewrite IHn; auto; omega.
Qed.

Lemma sublist_all : forall {A} i (l : list A), Zlength l <= i -> sublist 0 i l = l.
Proof.
  intros; unfold sublist; simpl.
  apply firstn_all.
  rewrite Zlength_correct in *; Omega0.
Qed.

Lemma sublist_prefix : forall {A} i j (l : list A), sublist 0 i (sublist 0 j l) = sublist 0 (Z.min i j) l.
Proof.
  intros.
  destruct (Z_le_dec i 0).
  { rewrite !sublist_nil_gen; auto.
    rewrite Z.min_le_iff; auto. }
  destruct (Z.min_spec i j) as [(? & ->) | (? & ->)].
  - rewrite sublist_sublist, !Z.add_0_r by omega; auto.
  - apply sublist_all.
    destruct (Z_le_dec j 0); [rewrite sublist_nil_gen; auto; rewrite Zlength_nil; omega|].
    destruct (Z_le_dec j (Zlength l)).
    rewrite Zlength_sublist; try omega.
    { pose proof (sublist_max_length 0 j l); omega. }
Qed.

Lemma sublist_suffix : forall {A} i j (l : list A), 0 <= i -> 0 <= j ->
  sublist i (Zlength l - j) (sublist j (Zlength l) l) = sublist (i + j) (Zlength l) l.
Proof.
  intros.
  destruct (Z_le_dec (Zlength l - j) i).
  { rewrite !sublist_nil_gen; auto; omega. }
  rewrite sublist_sublist by omega.
  rewrite Z.sub_simpl_r; auto.
Qed.

Lemma sublist_parts1 : forall {A} i j (l : list A), 0 <= i -> sublist i j l = sublist i j (sublist 0 j l).
Proof.
  intros.
  destruct (Z_le_dec j i).
  { rewrite !sublist_nil_gen; auto. }
  rewrite sublist_sublist by omega.
  rewrite !Z.add_0_r; auto.
Qed.

Lemma sublist_parts2 : forall {A} i j (l : list A), 0 <= i -> j <= Zlength l ->
  sublist i j l = sublist 0 (j - i) (sublist i (Zlength l) l).
Proof.
  intros.
  destruct (Z_le_dec j i).
  { rewrite !sublist_nil_gen; auto; omega. }
  rewrite sublist_sublist; try omega.
  rewrite Z.add_0_l, Z.sub_simpl_r; auto.
Qed.

Lemma Forall_Forall2 : forall {A} (P : A -> Prop) Q l1 l2 (HP : Forall P l1) (HQ : Forall2 Q l1 l2)
  (Htransfer : forall x y, P x -> Q x y -> P y), Forall P l2.
Proof.
  induction 2; auto; intros.
  inv HP.
  constructor; eauto.
Qed.

Lemma Forall_suffix_max : forall {A} (P : A -> Prop) l1 l2 i j
  (Hi : 0 <= i <= Zlength l1) (Hj : 0 <= j <= Zlength l1)
  (Hl1 : Forall P (sublist j (Zlength l1) l1))
  (Hl2 : sublist i (Zlength l1) l1 = sublist i (Zlength l2) l2),
  Forall P (sublist (Z.max i j) (Zlength l2) l2).
Proof.
  intros.
  destruct (eq_dec i (Zlength l1)).
  { subst; rewrite sublist_nil in Hl2.
    rewrite Z.max_l by omega.
    rewrite <- Hl2; auto. }
  assert (Zlength l1 = Zlength l2) as Heq.
  { assert (Zlength (sublist i (Zlength l1) l1) = Zlength (sublist i (Zlength l2) l2)) as Heq by congruence.
    destruct (Z_le_dec (Zlength l2) i).
    { rewrite sublist_nil_gen with (l0 := l2), Zlength_nil in Heq; auto.
      rewrite !Zlength_sublist in Heq; omega. }
    rewrite !Zlength_sublist in Heq; omega. }
  intros; destruct (Z.max_spec i j) as [(? & ->) | (? & ->)].
  - replace (sublist _ _ _) with (sublist (j - i) (Zlength l2 - i) (sublist i (Zlength l2) l2)).
    rewrite <- Hl2, sublist_sublist, !Z.sub_simpl_r by omega.
    rewrite <- Heq; auto.
    { rewrite sublist_sublist, !Z.sub_simpl_r by omega; auto. }
  - rewrite <- Hl2.
    replace (sublist _ _ _) with (sublist (i - j) (Zlength l1 - j) (sublist j (Zlength l1) l1)).
    apply Forall_sublist; auto.
    { rewrite sublist_sublist, !Z.sub_simpl_r; auto; omega. }
Qed.

Fixpoint extend {A} (l : list A) ls :=
  match l, ls with
  | x :: xs, y :: ys => (x :: y) :: extend xs ys
  | _, _ => ls
  end.

Lemma Zlength_extend : forall {A} (l : list A) ls, Zlength (extend l ls) = Zlength ls.
Proof.
  induction l; destruct ls; auto; simpl.
  rewrite !Zlength_cons, IHl; auto.
Qed.

Lemma Znth_extend_in : forall {A} (l : list A) ls i d d', 0 <= i < Zlength l -> Zlength l <= Zlength ls ->
  Znth i (extend l ls) d = Znth i l d' :: Znth i ls d.
Proof.
  induction l; destruct ls; simpl; intros; try rewrite Zlength_nil in *; try omega.
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0); subst; auto.
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
Qed.

Lemma Znth_extend_ge : forall {A} (l : list A) ls i d, Zlength l <= i ->
  Znth i (extend l ls) d = Znth i ls d.
Proof.
  induction l; destruct ls; auto; simpl; intros.
  destruct (zlt i 0); [rewrite !Znth_underflow; auto|].
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0); [rewrite Zlength_correct in *; omega|].
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
Qed.

Fixpoint extendr {A} (l : list A) ls :=
  match l, ls with
  | x :: xs, y :: ys => (y ++ [x]) :: extendr xs ys
  | _, _ => ls
  end.

Lemma Zlength_extendr : forall {A} (l : list A) ls, Zlength (extendr l ls) = Zlength ls.
Proof.
  induction l; destruct ls; auto; simpl.
  rewrite !Zlength_cons, IHl; auto.
Qed.

Lemma Znth_extendr_in : forall {A} (l : list A) ls i d d', 0 <= i < Zlength l -> Zlength l <= Zlength ls ->
  Znth i (extendr l ls) d = Znth i ls d ++ [Znth i l d'].
Proof.
  induction l; destruct ls; simpl; intros; try rewrite Zlength_nil in *; try omega.
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0); subst; auto.
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
Qed.

Lemma Znth_extendr_ge : forall {A} (l : list A) ls i d, Zlength l <= i ->
  Znth i (extendr l ls) d = Znth i ls d.
Proof.
  induction l; destruct ls; auto; simpl; intros.
  destruct (zlt i 0); [rewrite !Znth_underflow; auto|].
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0); [rewrite Zlength_correct in *; omega|].
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
Qed.

Lemma list_join_eq : forall (b : list share) a c c'
  (Hc : sepalg_list.list_join a b c) (Hc' : sepalg_list.list_join a b c'), c = c'.
Proof.
  induction b; intros; inv Hc; inv Hc'; auto.
  assert (w0 = w1) by (eapply sepalg.join_eq; eauto).
  subst; eapply IHb; eauto.
Qed.

Lemma readable_share_list_join : forall sh shs sh', sepalg_list.list_join sh shs sh' ->
  readable_share sh \/ Exists readable_share shs -> readable_share sh'.
Proof.
  induction 1; intros [? | Hexists]; try inv Hexists; auto.
  - apply IHfold_rel; left; eapply readable_share_join; eauto.
  - apply IHfold_rel; left; eapply readable_share_join; eauto.
Qed.

Lemma sublist_0_cons' : forall {A} i j (x : A) l, i <= 0 -> j > i -> sublist i j (x :: l) =
  x :: sublist i (j - 1) l.
Proof.
  intros; unfold sublist.
  replace (Z.to_nat i) with O; simpl.
  assert (0 < j - i) as Hgt by omega.
  rewrite Z2Nat.inj_lt in Hgt; try omega.
  destruct (Z.to_nat (j - i)) eqn: Hj; [omega|].
  simpl; f_equal; f_equal.
  replace (j - 1 - i) with (j - i - 1) by omega.
  rewrite Z2Nat.inj_sub; simpl; omega.
  destruct (eq_dec i 0); subst; auto.
  rewrite Z2Nat_neg; auto; omega.
Qed.

Lemma sublist_combine : forall {A B} (l1 : list A) (l2 : list B) i j,
  sublist i j (combine l1 l2) = combine (sublist i j l1) (sublist i j l2).
Proof.
  induction l1; simpl; intros.
  - unfold sublist; rewrite !skipn_nil, !firstn_nil; auto.
  - destruct l2.
    + unfold sublist at 1 3; rewrite !skipn_nil, !firstn_nil.
      destruct (sublist i j (a :: l1)); auto.
    + destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try omega.
        simpl; rewrite IHl1; auto.
      * rewrite !sublist_S_cons; try omega.
        apply IHl1; omega.
Qed.

Lemma extend_nil : forall {A} (l : list A), extend l [] = [].
Proof.
  destruct l; auto.
Qed.

Lemma extend_cons : forall {A} (l : list A) l1 ls, extend l (l1 :: ls) =
  match l with [] => l1 :: ls | a :: l' => (a :: l1) :: extend l' ls end.
Proof.
  destruct l; auto.
Qed.

Lemma sublist_extend : forall {A} (l : list A) ls i j,
  sublist i j (extend l ls) = extend (sublist i j l) (sublist i j ls).
Proof.
  induction l; simpl; intros.
  - unfold sublist; rewrite skipn_nil, firstn_nil; auto.
  - destruct ls.
    + unfold sublist; rewrite skipn_nil, firstn_nil, extend_nil; auto.
    + destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try omega.
        rewrite IHl; auto.
      * rewrite !sublist_S_cons; auto; omega.
Qed.

Lemma extendr_nil : forall {A} (l : list A), extendr l [] = [].
Proof.
  destruct l; auto.
Qed.

Lemma extendr_cons : forall {A} (l : list A) l1 ls, extendr l (l1 :: ls) =
  match l with [] => l1 :: ls | a :: l' => (l1 ++ [a]) :: extendr l' ls end.
Proof.
  destruct l; auto.
Qed.

Lemma sublist_extendr : forall {A} (l : list A) ls i j,
  sublist i j (extendr l ls) = extendr (sublist i j l) (sublist i j ls).
Proof.
  induction l; simpl; intros.
  - unfold sublist; rewrite skipn_nil, firstn_nil; auto.
  - destruct ls.
    + unfold sublist; rewrite skipn_nil, firstn_nil, extendr_nil; auto.
    + destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try omega.
        rewrite IHl; auto.
      * rewrite !sublist_S_cons; auto; omega.
Qed.

Lemma sublist_over : forall {A} (l : list A) i j, Zlength l <= i -> sublist i j l = [].
Proof.
  intros; unfold sublist.
  rewrite skipn_short, firstn_nil; auto.
  rewrite Zlength_correct in *; Omega0.
Qed.

Lemma lookup_distinct : forall {A B} (f : A -> B) a l t (Ha : In a l) (Hdistinct : NoDup (map fst l)),
  (fold_right (fun v : ident * A => PTree.set (fst v) (f (snd v))) t l) ! (fst a) =
  Some (f (snd a)).
Proof.
  induction l; simpl; intros; [contradiction|].
  inv Hdistinct.
  rewrite PTree.gsspec.
  destruct (peq (fst a) (fst a0)) eqn: Heq; setoid_rewrite Heq.
  - destruct Ha; [subst; auto|].
    contradiction H1; rewrite in_map_iff; eauto.
  - apply IHl; auto.
    destruct Ha; auto; subst.
    contradiction n; auto.
Qed.

Lemma lookup_out : forall {A B} (f : A -> B) a l t (Ha : ~In a (map fst l)),
  (fold_right (fun v : ident * A => PTree.set (fst v) (f (snd v))) t l) ! a = t ! a.
Proof.
  induction l; simpl; intros; auto.
  rewrite PTree.gsspec.
  destruct (peq a (fst a0)) eqn: Heq; setoid_rewrite Heq.
  - contradiction Ha; auto.
  - apply IHl.
    intro; contradiction Ha; auto.
Qed.

Lemma data_at__eq : forall {cs : compspecs} sh t p, data_at_ sh t p = data_at sh t (default_val t) p.
Proof.
  intros; unfold data_at_, data_at, field_at_; auto.
Qed.

Lemma func_tycontext_sub : forall f V G V2 G2 (HV : incl V V2) (HG : incl G G2)
  (Hdistinct : NoDup (map fst V2 ++ map fst G2)),
  tycontext_sub (func_tycontext f V G) (func_tycontext f V2 G2).
Proof.
  intros.
  unfold func_tycontext, make_tycontext, tycontext_sub; simpl.
  apply NoDup_app in Hdistinct; destruct Hdistinct as (? & ? & Hdistinct); auto.
  repeat split; auto; intro.
  - destruct (PTree.get _ _); auto.
    destruct p; rewrite orb_comm, orb_negb_r; auto.
  - unfold make_tycontext_g.
    revert dependent G2; revert dependent V2; revert V; induction G; simpl.
    + induction V; simpl; intros.
      * rewrite PTree.gempty; simpl; auto.
      * rewrite incl_cons_iff in HV; destruct HV.
        rewrite PTree.gsspec.
        destruct (peq id (fst a)); eauto; subst; simpl.
        rewrite lookup_out.
        apply lookup_distinct with (f0 := id); auto.
        { apply Hdistinct.
          rewrite in_map_iff; eexists; split; eauto. }
    + intros.
      rewrite incl_cons_iff in HG; destruct HG.
      rewrite PTree.gsspec.
      destruct (peq id (fst a)); eauto; subst; simpl.
      apply lookup_distinct; auto.
  - unfold make_tycontext_s.
    revert dependent G2; induction G; simpl; intros.
    + rewrite PTree.gempty; simpl; auto.
    + intros.
      rewrite incl_cons_iff in HG; destruct HG.
      rewrite PTree.gsspec.
      destruct (peq id (fst a)); eauto; subst; simpl.
      apply lookup_distinct with (f0 := id); auto.
Qed.

(* This lets us use a library as a client. *)
Lemma semax_body_mono : forall V G {cs : compspecs} f s V2 G2
  (HV : incl V V2) (HG : incl G G2) (Hdistinct : NoDup (map fst V2 ++ map fst G2)),
  semax_body V G f s -> semax_body V2 G2 f s.
Proof.
  unfold semax_body; intros.
  destruct s, f0.
  intros; eapply semax_extensionality_Delta, H.
  apply func_tycontext_sub; auto.
Qed.

(* We could also consider an alpha-renaming axiom, although this may be unnecessary. *)

(* precise and positive *)
Lemma weak_precise_positive_conflict : forall P,
  predicates_hered.derives ((weak_precise_mpred P && emp) * (weak_positive_mpred P && emp) * P * P) FF.
Proof.
  repeat intro.
  destruct H as (r1 & r2 & ? & (? & ? & Hj1 & (? & ? & Hj2 & (Hprecise & Hemp1) & (Hpositive & Hemp2)) & ?) & ?).
  specialize (Hemp1 _ _ Hj2); subst.
  specialize (Hemp2 _ _ Hj1); subst.
  destruct (age_sepalg.join_level _ _ _ Hj1), (age_sepalg.join_level _ _ _ Hj2),
    (age_sepalg.join_level _ _ _ H).
  exploit (Hprecise a r1 r2); simpl; try (split; auto; omega).
  { exists r2; auto. }
  { exists r1; apply sepalg.join_comm; auto. }
  intro; subst.
  pose proof (sepalg.join_self H); subst.
  destruct (Hpositive a) as (l & ? & ? & ? & ? & HYES); [split; auto; omega|].
  apply compcert_rmaps.RML.resource_at_join with (loc := l) in H.
  pose proof (sepalg.unit_identity _ H) as Hid.
  rewrite HYES in Hid; apply compcert_rmaps.RML.YES_not_identity in Hid; contradiction.
Qed.

Lemma precise_positive_conflict : forall P (Hprecise : precise P) (Hpositive : positive_mpred P), P * P |-- FF.
Proof.
  intros.
  apply derives_trans with (Q := (weak_precise_mpred P && emp) * (weak_positive_mpred P && emp) * P * P);
    [|apply weak_precise_positive_conflict].
  cancel.
  rewrite <- sepcon_emp at 1; apply sepcon_derives; apply andp_right; auto; apply derives_trans with (Q := TT);
    auto; [apply precise_weak_precise | apply positive_weak_positive]; auto.
Qed.

Lemma precise_sepcon : forall (P Q : mpred) (HP : precise P) (HQ : precise Q), precise (P * Q).
Proof.
  unfold precise; intros ??????? (l1 & r1 & Hjoin1 & HP1 & HQ1) (l2 & r2 & Hjoin2 & HP2 & HQ2)
    Hsub1 Hsub2.
  specialize (HP w _ _ HP1 HP2); specialize (HQ w _ _ HQ1 HQ2).
  rewrite HP, HQ in Hjoin1.
  eapply sepalg.join_eq; eauto.
  - apply sepalg.join_sub_trans with (b := w1); auto.
    eapply sepalg.join_join_sub'; eauto.
  - apply sepalg.join_sub_trans with (b := w2); auto.
    eapply sepalg.join_join_sub'; eauto.
  - apply sepalg.join_sub_trans with (b := w1); auto.
    eapply sepalg.join_join_sub; eauto.
  - apply sepalg.join_sub_trans with (b := w2); auto.
    eapply sepalg.join_join_sub; eauto.
Qed.

Lemma precise_andp1 : forall P Q (HP : precise P), precise (P && Q).
Proof.
  intros ?????? (? & ?) (? & ?) ??; eauto.
Qed.

Lemma precise_andp2 : forall P Q (HQ : precise Q), precise (P && Q).
Proof.
  intros ?????? (? & ?) (? & ?) ??; eauto.
Qed.

Lemma ex_address_mapsto_precise: forall ch sh l,
  precise (EX v : val, res_predicates.address_mapsto ch v sh l).
Proof.
  intros.
  eapply derives_precise, res_predicates.VALspec_range_precise.
  repeat intro.
  destruct H.
  eapply res_predicates.address_mapsto_VALspec_range; eauto.
Qed.

Lemma lock_inv_precise : forall v sh R, precise (lock_inv sh v R).
Proof.
  intros ?????? (b1 & o1 & Hv1 & Hlock1) (b2 & o2 & Hv2 & Hlock2) ??.
  rewrite Hv2 in Hv1; inv Hv1.
  eapply res_predicates.LKspec_precise; eauto.
Qed.

Lemma lock_inv_positive : forall sh v R,
  positive_mpred (lock_inv sh v R).
Proof.
  repeat intro.
  destruct H as (b & o & Hv & Hlock).
  simpl in Hlock.
  specialize (Hlock (b, Int.unsigned o)).
  if_tac [r|nr] in Hlock.
  - if_tac [e|ne] in Hlock.
    + destruct Hlock; eauto 6.
    + contradiction ne; auto.
  - contradiction nr; unfold adr_range; split; auto.
    unfold lksize.LKSIZE in *.
    omega.
Qed.

Lemma selflock_precise : forall R sh v, precise R -> precise (selflock R v sh).
Proof.
  intros.
  rewrite selflock_eq.
  apply precise_sepcon; auto.
  apply lock_inv_precise.
Qed.

(* This need not hold; specifically, when an rmap is at level 0, |> P holds vacuously for all P. *)
Lemma later_positive : forall P, positive_mpred P -> positive_mpred (|> P)%logic.
Admitted. (* still needed in verif_incr.v and verif_cond.v *)

Lemma positive_sepcon1 : forall P Q (HP : positive_mpred P),
  positive_mpred (P * Q).
Proof.
  repeat intro.
  destruct H as (? & ? & ? & HP1 & ?).
  specialize (HP _ HP1).
  destruct HP as (l & sh & rsh & k & p & HP).
  apply compcert_rmaps.RML.resource_at_join with (loc := l) in H.
  rewrite HP in H; inversion H; eauto 6.
Qed.

Lemma positive_sepcon2 : forall P Q (HQ : positive_mpred Q),
  positive_mpred (P * Q).
Proof.
  repeat intro.
  destruct H as (? & ? & ? & ? & HQ1).
  specialize (HQ _ HQ1).
  destruct HQ as (l & sh & rsh & k & p & HQ).
  apply compcert_rmaps.RML.resource_at_join with (loc := l) in H.
  rewrite HQ in H; inversion H; eauto 6.
Qed.

Lemma positive_andp1 : forall P Q (HP : positive_mpred P),
  positive_mpred (P && Q).
Proof.
  intros ???? (? & ?); auto.
Qed.

Lemma positive_andp2 : forall P Q (HQ : positive_mpred Q),
  positive_mpred (P && Q).
Proof.
  intros ???? (? & ?); auto.
Qed.

Lemma selflock_positive : forall R sh v, positive_mpred (selflock R v sh).
Proof.
  intros.
  rewrite selflock_eq.
  apply positive_sepcon2, lock_inv_positive.
Qed.

Lemma positive_FF : positive_mpred FF.
Proof.
  repeat intro; contradiction.
Qed.

Lemma derives_positive : forall P Q (Hderives : P |-- Q) (HQ : positive_mpred Q), positive_mpred P.
Proof.
  repeat intro.
  specialize (Hderives _ H); auto.
Qed.

Lemma ex_address_mapsto_positive: forall ch sh l,
  positive_mpred (EX v : val, res_predicates.address_mapsto ch v sh l).
Proof.
  intros ???? (? & ? & ? & Hp); simpl in Hp.
  specialize (Hp l); destruct (adr_range_dec _ _ _).
  destruct Hp; eauto 6.
  { contradiction n; unfold adr_range.
    destruct l; repeat split; auto; try omega.
    destruct ch; simpl; omega. }
Qed.

Corollary mapsto_positive : forall sh t p v, readable_share sh -> positive_mpred (mapsto sh t p v).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try apply positive_FF.
  destruct (type_is_volatile t); try apply positive_FF.
  destruct p; try apply positive_FF.
  destruct (readable_share_dec sh); [|contradiction n; auto].
  eapply derives_positive, ex_address_mapsto_positive.
  apply orp_left; entailer.
  - Exists v; eauto.
  - Exists v2'; auto.
Qed.

Corollary data_at__positive : forall {cs} sh t p (Hsh : readable_share sh)
  (Hval : type_is_by_value t = true) (Hvol : type_is_volatile t = false),
  positive_mpred (@data_at_ cs sh t p).
Proof.
  intros; unfold data_at_, field_at_, field_at, at_offset; rewrite by_value_data_at_rec_nonvolatile; auto;
    simpl.
  rewrite repinject_default_val.
  apply positive_andp2, mapsto_positive; auto.
Qed.

Corollary data_at_positive : forall {cs} sh t v p (Hsh : readable_share sh)
  (Hval : type_is_by_value t = true) (Hvol : type_is_volatile t = false),
  positive_mpred (@data_at cs sh t v p).
Proof.
  intros; eapply derives_positive, data_at__positive; eauto.
  apply data_at_data_at_.
Qed.

Lemma ex_positive : forall t P, (forall x, positive_mpred (P x)) -> positive_mpred (EX x : t, P x).
Proof.
  intros ???? (? & ?).
  eapply H; eauto.
Qed.

Lemma precise_emp : precise emp.
Proof.
  apply precise_emp.
Qed.

Lemma derives_precise' : forall (P Q : mpred), P |-- Q -> precise Q -> precise P.
Proof.
  intros; eapply derives_precise; [|eassumption]; auto.
Qed.

Lemma precise_FF : precise FF.
Proof.
  repeat intro; contradiction.
Qed.

Hint Resolve precise_emp precise_FF.

Lemma mapsto_precise : forall sh t p v, precise (mapsto sh t p v).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); auto.
  destruct (type_is_volatile t); auto.
  destruct p; auto.
  destruct (readable_share_dec sh).
  - eapply derives_precise, ex_address_mapsto_precise; intros ? [(? & ?) | (? & ? & ?)]; eexists; eauto.
  - apply precise_andp2, res_predicates.nonlock_permission_bytes_precise.
Qed.
Hint Resolve mapsto_precise.

Corollary memory_block_precise : forall sh n v, precise (memory_block sh n v).
Proof.
  destruct v; auto; apply precise_andp2.
  forget (Int.unsigned i) as o; forget (nat_of_Z n) as z; revert o; induction z; intro; simpl.
  - apply precise_emp.
  - apply precise_sepcon; auto.
    apply mapsto_precise.
Qed.
Hint Resolve memory_block_precise.

Corollary field_at__precise : forall {cs : compspecs} sh t gfs p,
  precise (field_at_ sh t gfs p).
Proof.
  intros; rewrite field_at__memory_block; auto.
Qed.
Hint Resolve field_at__precise.

Corollary data_at__precise : forall {cs : compspecs} sh t p, precise (data_at_ sh t p).
Proof.
  intros; unfold data_at_; auto.
Qed.
Hint Resolve data_at__precise.

Corollary field_at_precise : forall {cs : compspecs} sh t gfs v p,
  precise (field_at sh t gfs v p).
Proof.
  intros; eapply derives_precise, field_at__precise; apply field_at_field_at_.
Qed.
Hint Resolve field_at_precise.

Corollary data_at_precise : forall {cs : compspecs} sh t v p, precise (data_at sh t v p).
Proof.
  intros; unfold data_at; auto.
Qed.
Hint Resolve data_at_precise.

Lemma cond_var_precise : forall {cs} sh p, readable_share sh ->
  precise (@cond_var cs sh p).
Proof.
  intros; apply data_at__precise; auto.
Qed.

Lemma cond_var_positive : forall {cs} sh p, readable_share sh ->
  positive_mpred (@cond_var cs sh p).
Proof.
  intros; unfold cond_var, data_at_, field_at_, field_at, at_offset; simpl.
  destruct p; try (rewrite prop_false_andp; [|intros (? & ?); contradiction]; apply positive_FF).
  apply positive_andp2.
  rewrite data_at_rec_eq; simpl.
  apply mapsto_positive; auto.
Qed.

Lemma lock_inv_isptr : forall sh v R, lock_inv sh v R = !!isptr v && lock_inv sh v R.
Proof.
  intros.
  eapply local_facts_isptr with (P := fun v => lock_inv sh v R); eauto.
  unfold lock_inv; Intros b o.
  subst; simpl; entailer.
Qed.

Lemma cond_var_isptr : forall {cs} sh v, @cond_var cs sh v = !! isptr v && cond_var sh v.
Proof.
  intros; apply data_at__isptr.
Qed.

Lemma cond_var_share_join : forall {cs} sh1 sh2 sh v (Hjoin : sepalg.join sh1 sh2 sh),
  @cond_var cs sh1 v * cond_var sh2 v = cond_var sh v.
Proof.
  intros; unfold cond_var; apply data_at__share_join; auto.
Qed.

Lemma precise_fold_right : forall l, Forall precise l -> precise (fold_right sepcon emp l).
Proof.
  induction l; simpl; auto; intros.
  inv H; apply precise_sepcon; auto.
Qed.

Lemma precise_False : precise (!!False).
Proof.
  repeat intro.
  inversion H.
Qed.

(* Sometimes, in order to prove precise, we actually need to know that the data is the same as well. *)
Lemma mapsto_inj : forall sh t v1 v2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (mapsto sh t p v1) r1)
  (Hp2 : predicates_hered.app_pred (mapsto sh t p v2) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : v1 <> Vundef) (Hdef2 : v2 <> Vundef),
  r1 = r2 /\ v1 = v2.
Proof.
  unfold mapsto; intros.
  destruct (access_mode t); try contradiction.
  destruct (type_is_volatile t); [contradiction|].
  destruct p; try contradiction.
  destruct (readable_share_dec sh); [|contradiction n; auto].
  destruct Hp1 as [(? & ?) | (? & ?)]; [|contradiction Hdef1; auto].
  destruct Hp2 as [(? & ?) | (? & ?)]; [|contradiction Hdef2; auto].
  assert (r1 = r2); [|split; auto].
  - eapply ex_address_mapsto_precise; eauto; eexists; eauto.
  - subst; eapply res_predicates.address_mapsto_value_cohere'; eauto.
Qed.

Lemma data_at_int_array_inj : forall {cs} sh z a1 a2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (@data_at_rec cs sh (tarray tint z) a1 p) r1)
  (Hp2 : predicates_hered.app_pred (@data_at_rec cs sh (tarray tint z) a2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : Forall (fun v => v <> Vundef) a1) (Hdef2 : Forall (fun v => v <> Vundef) a2)
  (Hlen1 : Zlength a1 = z) (Hlen2 : Zlength a2 = z),
  r1 = r2 /\ a1 = a2.
Proof.
  intros until z.
  remember (Z.to_nat z) as l; revert dependent z.
  induction l; intros.
  - destruct a1; [|rewrite <- Hlen1, Zlength_cons, Zlength_correct, Z2Nat.inj_succ in Heql; omega].
    rewrite Zlength_nil in Hlen1.
    destruct a2; [split; auto | rewrite Zlength_cons, Zlength_correct in Hlen2; omega].
    rewrite <- Hlen1 in *.
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite array_pred_len_0 in Hp1, Hp2; auto.
    apply sepalg.same_identity with (a := r); auto.
    + destruct Hr1 as (? & H); specialize (Hp1 _ _ H); subst; auto.
    + destruct Hr2 as (? & H); specialize (Hp2 _ _ H); subst; auto.
  - destruct a1 as [|x1 l1].
    { rewrite <- Hlen1, Zlength_nil in Heql; discriminate. }
    destruct a2 as [|x2 l2].
    { rewrite <- Hlen2, Zlength_nil in Heql; discriminate. }
    unfold tarray in *.
    rewrite Zlength_cons in *.
    assert (0 <= 1 <= z).
    { rewrite Zlength_correct in *; omega. }
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [|rewrite Zlength_cons; omega].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [|rewrite Zlength_cons; omega].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one with (d := x1), array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try omega.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by omega.
    assert (Zlength l2 = z - 1) by omega.
    rewrite sublist_same in Ht1, Ht2; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; omega. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    { auto. }
    { omega. }
    intros (? & ?); subst.
    rewrite by_value_data_at_rec_nonvolatile in Hh1, Hh2; auto.
    exploit (mapsto_inj sh tint x1 x2); eauto.
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    intros (? & ?); subst.
    split; [eapply sepalg.join_eq|]; auto.
Qed.

Lemma data_at_ptr_array_inj : forall {cs} sh t z a1 a2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (@data_at_rec cs sh (tarray (tptr t) z) a1 p) r1)
  (Hp2 : predicates_hered.app_pred (@data_at_rec cs sh (tarray (tptr t) z) a2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : Forall (fun v => v <> Vundef) a1) (Hdef2 : Forall (fun v => v <> Vundef) a2)
  (Hlen1 : Zlength a1 = z) (Hlen2 : Zlength a2 = z),
  r1 = r2 /\ a1 = a2.
Proof.
  intros until z.
  remember (Z.to_nat z) as l; revert dependent z.
  induction l; intros.
  - destruct a1; [|rewrite <- Hlen1, Zlength_cons, Zlength_correct, Z2Nat.inj_succ in Heql; omega].
    rewrite Zlength_nil in Hlen1.
    destruct a2; [split; auto | rewrite Zlength_cons, Zlength_correct in Hlen2; omega].
    rewrite <- Hlen1 in *.
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite array_pred_len_0 in Hp1, Hp2; auto.
    apply sepalg.same_identity with (a := r); auto.
    + destruct Hr1 as (? & H); specialize (Hp1 _ _ H); subst; auto.
    + destruct Hr2 as (? & H); specialize (Hp2 _ _ H); subst; auto.
  - destruct a1 as [|x1 l1].
    { rewrite <- Hlen1, Zlength_nil in Heql; discriminate. }
    destruct a2 as [|x2 l2].
    { rewrite <- Hlen2, Zlength_nil in Heql; discriminate. }
    unfold tarray in *.
    rewrite Zlength_cons in *.
    assert (0 <= 1 <= z).
    { rewrite Zlength_correct in *; omega. }
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [|rewrite Zlength_cons; omega].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [|rewrite Zlength_cons; omega].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one with (d := x1), array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try omega.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by omega.
    assert (Zlength l2 = z - 1) by omega.
    rewrite sublist_same in Ht1, Ht2; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; omega. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    { auto. }
    { omega. }
    intros (? & ?); subst.
    rewrite by_value_data_at_rec_nonvolatile in Hh1, Hh2; auto.
    exploit (mapsto_inj sh (tptr t) x1 x2); eauto.
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    intros (? & ?); subst.
    split; [eapply sepalg.join_eq|]; auto.
Qed.

Hint Resolve lock_inv_precise lock_inv_positive selflock_precise selflock_positive
  cond_var_precise cond_var_positive positive_FF mapsto_precise mapsto_positive
  data_at_precise data_at_positive data_at__precise data_at__positive selflock_rec.

Lemma eq_dec_refl : forall {A B} {A_eq : EqDec A} (a : A) (b c : B), (if eq_dec a a then b else c) = b.
Proof.
  intros; destruct (eq_dec a a); [|contradiction n]; auto.
Qed.

(* shares *)
Lemma LKspec_readable lock_size :
  0 < lock_size ->
  forall R sh p, predicates_hered.derives (res_predicates.LKspec lock_size R sh p)
  (!!(readable_share sh)).
Proof.
  intros pos R sh p a H.
  specialize (H p); simpl in H.
  destruct (adr_range_dec p lock_size p).
  destruct (eq_dec p p); [|contradiction n; auto].
  destruct H; auto.
  { contradiction n; unfold adr_range.
    destruct p; split; auto.
    omega. }
Qed.

Lemma lock_inv_share_join : forall sh1 sh2 sh v R (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2)
  (Hjoin : sepalg.join sh1 sh2 sh),
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.
Proof.
  intros; unfold lock_inv.
  rewrite exp_sepcon1; f_equal; extensionality b.
  rewrite exp_sepcon1; f_equal; extensionality o.
  destruct v; try solve [repeat rewrite prop_false_andp; try discriminate; rewrite FF_sepcon; auto].
  destruct (eq_dec b0 b); [|repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n; auto);
    rewrite FF_sepcon; auto].
  destruct (eq_dec i o); [subst | repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n; auto);
    rewrite FF_sepcon; auto].
  repeat rewrite prop_true_andp; auto.
  evar (P : mpred); replace (exp _) with P.
  - subst P; apply slice.LKspec_share_join; eauto.
  - subst P.
    erewrite exp_uncurry, exp_congr, <- exp_andp1, exp_prop, prop_true_andp; eauto.
    { instantiate (1 := fun x => Vptr b o = Vptr (fst x) (snd x)); exists (b, o); auto. }
    intros (?, ?); simpl.
    destruct (eq_dec b0 b); [subst |
      repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    destruct (eq_dec i o); [|repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    subst; repeat rewrite prop_true_andp; auto.
Qed.

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Admitted.

Lemma split_Ews :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Ews.
Proof.
  apply split_readable_share; auto.
Qed.

Definition remove_Znth {A} i (al : list A) := sublist 0 i al ++ sublist (i + 1) (Zlength al) al.

Lemma remove_Znth0 : forall {A} (l : list A), remove_Znth 0 l = sublist 1 (Zlength l) l.
Proof.
  intros; unfold remove_Znth.
  rewrite sublist_nil; auto.
Qed.

Lemma remove_Znth_cons : forall {A} i a (l : list A), i > 0 ->
  remove_Znth i (a :: l) = a :: remove_Znth (i - 1) l.
Proof.
  intros; unfold remove_Znth.
  rewrite sublist_0_cons, sublist_S_cons, Zlength_cons; auto; try omega.
  simpl; f_equal; f_equal; f_equal; omega.
Qed.

Lemma Zlength_remove_Znth : forall {A} i (l : list A), 0 <= i < Zlength l ->
  Zlength (remove_Znth i l) = Zlength l - 1.
Proof.
  intros; unfold remove_Znth.
  rewrite Zlength_app, !Zlength_sublist; omega.
Qed.

Lemma join_shares_nth : forall shs sh1 sh i, sepalg_list.list_join sh1 shs sh -> 0 <= i < Zlength shs ->
  exists sh', sepalg_list.list_join (Znth i shs Share.bot) (remove_Znth i shs) sh' /\ sepalg.join sh1 sh' sh.
Proof.
  induction shs; simpl; intros.
  { rewrite Zlength_nil in *; omega. }
  inv H.
  destruct (eq_dec i 0).
  - subst; rewrite remove_Znth0, sublist_1_cons, Zlength_cons, sublist_same, Znth_0_cons; auto; try omega.
    eapply sepalg_list.list_join_assoc1; eauto.
  - rewrite Zlength_cons in *; exploit (IHshs w1 sh (i - 1)); auto; try omega.
    intros (sh2 & ? & ?).
    rewrite Znth_pos_cons, remove_Znth_cons; try omega.
    exploit (sepalg.join_sub_joins_trans(a := a)(b := sh2)(c := w1)); eauto.
    { eexists; eapply sepalg.join_comm; eauto. }
    intros (sh' & ?); exists sh'; split.
    + exploit (sepalg_list.list_join_assoc2(a := a)(b := Znth (i - 1) shs Share.bot)
        (cl := remove_Znth (i - 1) shs)(e := sh')(f := sh2)); auto.
      intros (d & ? & ?).
      econstructor; eauto.
    + pose proof (sepalg.join_assoc(a := sh1)(b := a)(c := sh2)(d := w1)(e := sh)) as X.
      repeat match goal with X : ?a -> _, H : ?a |- _ => specialize (X H) end.
      destruct X as (f & Ha' & ?).
      assert (f = sh') by (eapply sepalg.join_eq; eauto).
      subst; auto.
Qed.

Lemma list_join_comm : forall (l1 l2 : list share) a b, sepalg_list.list_join a (l1 ++ l2) b ->
  sepalg_list.list_join a (l2 ++ l1) b.
Proof.
  induction l1; intros; [rewrite app_nil_r; auto|].
  inversion H as [|????? H1 H2]; subst.
  apply IHl1, sepalg_list.list_join_unapp in H2.
  destruct H2 as (c & Hl2 & Hl1).
  apply sepalg.join_comm in H1.
  destruct (sepalg_list.list_join_assoc1 H1 Hl2) as (? & ? & ?).
  eapply sepalg_list.list_join_app; eauto.
  econstructor; eauto.
Qed.

(* Split a share into an arbitrary number of subshares. *)
Lemma split_shares : forall n sh, readable_share sh ->
  exists sh1 shs, Zlength shs = Z.of_nat n /\ readable_share sh1 /\ Forall readable_share shs /\
                  sepalg_list.list_join sh1 shs sh.
Proof.
  induction n; intros.
  - exists sh, []; repeat split; auto.
    apply sepalg_list.fold_rel_nil.
  - destruct (split_readable_share _ H) as (sh1 & sh2 & H1 & ? & ?).
    destruct (IHn _ H1) as (sh1' & shs & ? & ? & ? & ?).
    exists sh1', (shs ++ [sh2]).
    rewrite Nat2Z.inj_succ, Zlength_app, Zlength_cons, Zlength_nil; split; [omega|].
    rewrite Forall_app; repeat split; auto.
    eapply sepalg_list.list_join_app; eauto.
    rewrite <- sepalg_list.list_join_1; auto.
Qed.

Lemma data_at_shares_join : forall {cs} sh t v p shs sh1 (Hsplit : sepalg_list.list_join sh1 shs sh),
  @data_at cs sh1 t v p * fold_right_sepcon (map (fun sh => data_at sh t v p) shs) =
  data_at sh t v p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    rewrite sepcon_emp; auto.
  - inv Hsplit.
    erewrite <- sepcon_assoc, data_at_share_join; eauto.
Qed.

(* These lemmas should probably be in veric. *)
Lemma mpred_ext : forall (P Q : mpred) (Hd1 : P |-- Q) (Hd2 : Q |-- P), P = Q.
Proof.
  intros; apply (predicates_hered.pred_ext _ _ _ Hd1); auto.
Qed.

Lemma mapsto_value_cohere: forall sh1 sh2 t p v1 v2,
  readable_share sh1 -> readable_share sh2 ->
  mapsto sh1 t p v1 * mapsto sh2 t p v2 |-- mapsto sh1 t p v1 * mapsto sh2 t p v1.
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try simple apply derives_refl.
  destruct (type_is_volatile t); try simple apply derives_refl.
  destruct p; try simple apply derives_refl.
  destruct (readable_share_dec sh1); [|contradiction n; auto].
  destruct (readable_share_dec sh2); [|contradiction n; auto].
  destruct (eq_dec v1 Vundef).
  - subst; rewrite !prop_false_andp with (P := tc_val t Vundef), !FF_orp, prop_true_andp; auto;
      try apply tc_val_Vundef.
    cancel.
    rewrite prop_true_andp with (P := Vundef = Vundef); auto.
    apply orp_left; Intros; auto.
    Exists v2; auto.
  - rewrite !prop_false_andp with (P := v1 = Vundef), !orp_FF; auto; Intros.
    apply andp_right; [apply prop_right; auto|].
    eapply derives_trans with (Q := _ * EX v2' : val,
      res_predicates.address_mapsto m v2' _ _);
      [apply sepcon_derives; [apply derives_refl|]|].
    + destruct (eq_dec v2 Vundef).
      * subst; rewrite prop_false_andp with (P := tc_val t Vundef), FF_orp;
          try apply tc_val_Vundef.
        rewrite prop_true_andp with (P := Vundef = Vundef); auto.
      * rewrite prop_false_andp with (P := v2 = Vundef), orp_FF; auto; Intros.
        Exists v2; auto.
    + Intro v2'.
      assert_PROP (v1 = v2') by (apply res_predicates.address_mapsto_value_cohere).
      subst; auto.
Qed.

Lemma data_at_rec_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  data_at_rec sh1 t v1 p * data_at_rec sh2 t v2 p |--
  data_at_rec sh1 t v1 p * data_at_rec sh2 t v1 p.
Proof.
  intros until t; type_induction.type_induction t; intros; rewrite !data_at_rec_eq; simpl; auto;
    try solve [destruct (type_is_volatile _); [cancel | apply mapsto_value_cohere; auto]].
  - unfold array_pred, aggregate_pred.array_pred.
    rewrite sepcon_andp_prop, !sepcon_andp_prop'.
    repeat (apply derives_extract_prop; intro); entailer'.
    rewrite Z.sub_0_r in *.
    set (lo := 0) at 1 3 5 7; clearbody lo.
    forget (Z.to_nat z) as n; revert lo; induction n; simpl; intro; [cancel|].
    rewrite !sepcon_assoc, <- (sepcon_assoc _ (at_offset _ _ _)), (sepcon_comm _ (at_offset _ _ _)).
    rewrite <- (sepcon_assoc _ (at_offset _ _ _)), (sepcon_comm _ (at_offset _ _ _)).
    rewrite !sepcon_assoc, <- !(sepcon_assoc (at_offset _ _ _) (at_offset _ _ _)).
    apply sepcon_derives; unfold at_offset; auto.
  - admit.
  - admit.
Admitted.

Corollary data_at_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p, readable_share sh1 ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |--
  data_at sh1 t v1 p * data_at sh2 t v1 p.
Proof.
  intros; destruct (readable_share_dec sh2).
  - unfold data_at, field_at, at_offset; Intros; entailer'.
    apply data_at_rec_value_cohere; auto.
  - assert_PROP (value_fits t v1 /\ value_fits t v2) by entailer!.
    setoid_rewrite nonreadable_data_at_eq at 2; eauto; tauto.
Qed.

Corollary data_at__cohere : forall {cs : compspecs} sh1 sh2 t v p, readable_share sh1 ->
  data_at sh1 t v p * data_at_ sh2 t p =
  data_at sh1 t v p * data_at sh2 t v p.
Proof.
  intros; apply mpred_ext.
  - rewrite data_at__eq; apply data_at_value_cohere; auto.
  - entailer!.
Qed.

Lemma data_at__shares_join : forall {cs} sh t v p shs sh1 (Hsplit : sepalg_list.list_join sh1 shs sh)
  (Hreadable1 : readable_share sh1) (Hreadable : Forall readable_share shs),
  @data_at cs sh1 t v p * fold_right sepcon emp (map (fun sh => data_at_ sh t p) shs) |--
  data_at sh t v p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    rewrite sepcon_emp; auto.
  - inv Hsplit.
    inv Hreadable.
    rewrite <- sepcon_assoc, data_at__cohere; auto.
    erewrite data_at_share_join; eauto.
    apply IHshs; auto.
    eapply readable_share_join; eauto.
Qed.

Lemma extract_nth_sepcon : forall l i, 0 <= i < Zlength l ->
  fold_right sepcon emp l = Znth i l FF * fold_right sepcon emp (upd_Znth i l emp).
Proof.
  intros.
  erewrite <- sublist_same with (al := l) at 1; auto.
  rewrite sublist_split with (mid := i); try omega.
  rewrite sublist_next with (i0 := i)(d := FF); try omega.
  rewrite sepcon_app; simpl.
  rewrite <- sepcon_assoc, (sepcon_comm _ (Znth i l FF)).
  unfold upd_Znth; rewrite sepcon_app, sepcon_assoc; simpl.
  rewrite emp_sepcon; auto.
Qed.

Lemma replace_nth_sepcon : forall P l i, P * fold_right sepcon emp (upd_Znth i l emp) =
  fold_right sepcon emp (upd_Znth i l P).
Proof.
  intros; unfold upd_Znth.
  rewrite !sepcon_app; simpl.
  rewrite emp_sepcon, <- !sepcon_assoc, (sepcon_comm P); auto.
Qed.

Lemma sepcon_derives_prop : forall P Q R, P |-- !!R -> P * Q |-- !!R.
Proof.
  intros; eapply derives_trans; [apply saturate_aux20 with (Q' := True); eauto|].
  - entailer!.
  - apply prop_left; intros (? & ?); apply prop_right; auto.
Qed.

Lemma sepcon_map : forall {A} P Q (l : list A), fold_right sepcon emp (map (fun x => P x * Q x) l) =
  fold_right sepcon emp (map P l) * fold_right sepcon emp (map Q l).
Proof.
  induction l; simpl.
  - rewrite sepcon_emp; auto.
  - rewrite !sepcon_assoc, <- (sepcon_assoc (fold_right _ _ _) (Q a)), (sepcon_comm (fold_right _ _ _) (Q _)).
    rewrite IHl; rewrite sepcon_assoc; auto.
Qed.

Lemma sepcon_list_derives : forall l1 l2 (Hlen : Zlength l1 = Zlength l2)
  (Heq : forall i, 0 <= i < Zlength l1 -> Znth i l1 FF |-- Znth i l2 FF),
  fold_right sepcon emp l1 |-- fold_right sepcon emp l2.
Proof.
  induction l1; destruct l2; auto; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega).
  apply sepcon_derives.
  - specialize (Heq 0); rewrite !Znth_0_cons in Heq; apply Heq.
    rewrite Zlength_correct; omega.
  - apply IHl1; [omega|].
    intros; specialize (Heq (i + 1)); rewrite !Znth_pos_cons, !Z.add_simpl_r in Heq; try omega.
    apply Heq; omega.
Qed.

Lemma field_at_array_inbounds : forall {cs : compspecs} sh t z a i v p,
  field_at sh (Tarray t z a) [ArraySubsc i] v p |-- !!(0 <= i < z).
Proof.
  intros; entailer!.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & ?); auto.
Qed.

Lemma andp_emp_derives_dup : forall (P : mpred),
  predicates_hered.derives (P && emp) ((P && emp) * (P && emp)).
Proof.
  intros ???.
  exists a; exists a; split; auto.
  setoid_rewrite <- sepalg.identity_unit_equiv; destruct H; auto.
Qed.

Corollary andp_emp_dup : forall (P : mpred), P && emp = (P && emp) * (P && emp).
Proof.
  intro; apply mpred_ext.
  - apply andp_emp_derives_dup.
  - entailer!.
    apply andp_left2; auto.
Qed.

Lemma approx_imp : forall n P Q, compcert_rmaps.RML.R.approx n (predicates_hered.imp P Q) =
  compcert_rmaps.RML.R.approx n (predicates_hered.imp (compcert_rmaps.RML.R.approx n P) (compcert_rmaps.RML.R.approx n Q)).
Proof.
  intros; apply predicates_hered.pred_ext; intros ? (? & Himp); split; auto; intros ? Ha' HP.
  - destruct HP; split; auto.
  - apply Himp; auto; split; auto.
    pose proof (ageable.necR_level _ _ Ha'); omega.
Qed.

Lemma approx_idem : forall n P, compcert_rmaps.R.approx n (compcert_rmaps.R.approx n P) =
  compcert_rmaps.R.approx n P.
Proof.
  intros.
  transitivity (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) P); auto.
  rewrite compcert_rmaps.RML.approx_oo_approx; auto.
Qed.

(* tactics *)
Lemma void_ret : ifvoid tvoid (` (PROP ( )  LOCAL ()  SEP ()) (make_args [] []))
  (EX v : val, ` (PROP ( )  LOCAL ()  SEP ()) (make_args [ret_temp] [v])) = emp.
Proof.
  extensionality; simpl.
  unfold liftx, lift, PROPx, LOCALx, SEPx; simpl; normalize.
Qed.

Lemma malloc_compat : forall {cs : compspecs} sh t p, legal_alignas_type t = true ->
  legal_cosu_type t = true ->
  complete_type cenv_cs t = true -> (alignof t | natural_alignment) ->
  malloc_token sh (sizeof t) p = !!field_compatible t [] p && malloc_token sh (sizeof t) p.
Proof.
  intros; rewrite andp_comm; apply add_andp; entailer!.
  apply malloc_compatible_field_compatible; auto.
Qed.

Ltac lock_props := rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
  [repeat apply andp_right; auto; eapply derives_trans;
   try (apply precise_weak_precise || apply positive_weak_positive || apply rec_inv_weak_rec_inv); auto |
   try timeout 20 cancel].

Ltac join_sub := repeat (eapply sepalg.join_sub_trans;
  [eexists; first [eassumption | simple eapply sepalg.join_comm; eassumption]|]); eassumption.

Ltac join_inj := repeat match goal with H1 : sepalg.join ?a ?b ?c, H2 : sepalg.join ?a ?b ?d |- _ =>
    pose proof (sepalg.join_eq H1 H2); clear H1 H2; subst; auto end.

Ltac fast_cancel := rewrite ?sepcon_emp, ?emp_sepcon; rewrite ?sepcon_assoc;
  repeat match goal with |- _ |-- ?P * _ =>
    try (rewrite <- !sepcon_assoc, (sepcon_comm _ P), !sepcon_assoc);
    try simple apply derives_refl; repeat (apply sepcon_derives; [simple apply derives_refl|]) end;
  try cancel_frame.

Ltac forward_spawn sig wit := let Frame := fresh "Frame" in evar (Frame : list mpred);
  try match goal with |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip end;
  rewrite <- ?seq_assoc; eapply semax_seq';
  [match goal with |- semax _ (PROP () (LOCALx ?locals _)) _ _ => eapply semax_pre, semax_call_id0 with
      (argsig := [(_f, tptr voidstar_funtype); (_args, tptr tvoid)])(P := [])
      (Q := locals)(R := Frame)(ts := [sig])
      (A := spawn_arg_type)(x := wit); try reflexivity end |
   after_forward_call; unfold spawn_post; rewrite void_ret; subst Frame; normalize].

Lemma semax_fun_id'' id f Espec {cs} Delta P Q R Post c :
  (var_types Delta) ! id = None ->
  (glob_specs Delta) ! id = Some f ->
  (glob_types Delta) ! id = Some (type_of_funspec f) ->
  @semax cs Espec Delta
    (EX v : val, PROPx P
      (LOCALx (gvar id v :: Q)
      (SEPx ((func_ptr' f v) :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros V G GS SA.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply SA; [ clear SA |
  intros; simpl; unfold local, lift1; entailer! ].
go_lowerx.
apply exp_right with (eval_var id (type_of_funspec f) rho).
entailer.
apply andp_right.
- (* about gvar *)
  apply prop_right.
  unfold gvar_denote, eval_var, Map.get.
  destruct H as (_ & _ & DG & DS).
  destruct (DS id _ GS) as [-> | (t & E)]; [ | congruence].
  destruct (DG id _ GS) as (? & -> & ?); auto.
- (* about func_ptr/func_ptr' *)
  unfold func_ptr'.
  rewrite <- andp_left_corable, andp_comm; auto.
  apply corable_func_ptr.
Qed.

Ltac get_global_function'' _f :=
eapply (semax_fun_id'' _f); try reflexivity.

(* revised start_function that mostly works for dependent specs *)
Ltac start_dep_function := 
  match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH u : unit
               PRE  [] main_pre _ nil u
               POST [ tint ] main_post _ nil u) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec DependedTypeList [a b] 
   | (fun i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with 
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP; 
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH 
                 | Share.t => intros ?SH 
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax.
