(*
 * Copyright (c) 2009-2012, Andrew Appel, Robert Dockins and Aquinas Hobor.
 * This presentation of Permission Algebras and Separation Algebras
 * includes ideas from a discussion with Jonas Jensen and also from
 * a paper by Francois Pottier.
 *)
Require Import msl.Extensionality.

Set Implicit Arguments.

Class Join (t: Type) : Type := join: t -> t -> t -> Prop.

(* "Permission Algebra": commutative semigroup,
   such that if units exist, they must have certain properties. *)
Class Perm_alg (t: Type) {J: Join t} : Type :=
  mkPerm   {
   join_eq: forall {x y z z'}, join x y z -> join x y z' -> z = z';
   join_assoc: forall {a b c d e}, join a b d -> join d c e ->
                    {f : t & join b c f /\ join a f e};
   join_comm: forall {a b c}, join a b c -> join b a c;
   join_positivity: forall {a a' b b'}, join a a' b -> join b b' a -> a=b
}.
Arguments Perm_alg _ [J].

Definition unit_for {t}{J: Join t} (e a: t) := join e a a.
Definition identity {t} {J: Join t} (e: t) := forall a b, join e a b -> a=b.

Hint Extern 2 (@join _ _ _ _ _) =>
   (eapply join_comm; trivial;
     try eassumption;
     (* This next line looks superfluous, but it is not: it catches the
      case where H is join at a function type, where the goal is
      join at an applied function. *)
     match goal with H: @join _ _ _ _ _ |- _ => apply H end).
 (* Hint Immediate @join_comm. *)

Hint Unfold unit_for.

Lemma join_assoc_uniq:
  forall {t} {J: Join t} (PA1 PA2: @Perm_alg t J),
      forall a b c d e H H',
         (projT1 (@join_assoc _ _ PA1  a b c d e H H'))
        = (projT1 (@join_assoc _ _ PA2  a b c d e H H')).
Proof.
  intros.
  destruct (@join_assoc _ _ PA1  a b c d e H H') as [f [? ?]].
  destruct (@join_assoc _ _ PA2  a b c d e H H') as [g [? ?]].
  simpl. apply (join_eq j j1).
Qed.

  (* Sep_alg: additional properties that makes a Permission Algebra
     into a Separation Algebra.  The notion of "core" comes from
    F. Pottier, "Syntactic soundness proof of a type-and-capability
      system with hidden state" *)
  Class Sep_alg A {J: Join A} : Type :=
    mkSep {
      the_unit: A;
      join_unit: forall {a}, join the_unit a a
    }.
Arguments Sep_alg _ [J].

Lemma unit_uniq {t} {J: Join t}{PA: Perm_alg t}:
   forall (SA1: @Sep_alg _ J)
          (SA2: @Sep_alg _ J),
     @the_unit _ _ SA1 = @the_unit _ _ SA2.
Proof.
 intros.
 pose proof (@join_unit _ _ SA1 (@the_unit _ _ SA2)).
 pose proof (@join_unit _ _ SA2 (@the_unit _ _ SA1)).
 eapply join_eq; eauto.
Qed.

Lemma   unit_identity {A}{J: Join A}{PA: Perm_alg A}{SA: Sep_alg A} :
        identity the_unit.
Proof.
 repeat intro.
 eapply join_eq; eauto.
 apply join_unit.
Qed.

Lemma join_unit_unit {A}`{PA: Perm_alg A}{SA : Sep_alg A} : forall e, join e the_unit the_unit -> e = the_unit.
Proof.
  intros; eapply join_positivity, join_unit; eauto.
Qed.

Lemma identity_unit {A}`{PA: Perm_alg A}{SA : Sep_alg A} : forall e, identity e -> e = the_unit.
Proof.
  intros.
  symmetry; apply H.
  apply join_comm, join_unit.
Qed.

(* Disj_alg: adds the property that no nonempty element can join with itself. *)
Class Disj_alg  (t: Type) {J: Join t} :=
   join_self: forall {a b}, join a a b -> a = b.
Arguments Disj_alg _ [J].

  (* Positive Permission Algebra: there are no units, every element is nonempty *)
  Class Pos_alg  {A} {J: Join A} :=
    no_units: forall e a, ~unit_for e a.
Arguments Pos_alg _ [J].

(* Has the "cross-split" property described in Dockins et al,
    "A fresh look at separation algebras and share accounting", 2009 *)
Class Cross_alg (t: Type)  `{J: Join t} :=
   cross_split :
      forall a b c d z : t,
       join a b z ->
       join c d z ->
    { x:(t*t*t*t) &  match x with (ac,ad,bc,bd) =>
         join ac ad a /\ join bc bd b /\ join ac bc c /\ join ad bd d
       end
    }.
Arguments Cross_alg _ [J].

(* Has the "triple join" property  *)
Class Trip_alg {A} {J: Join A} :=
  triple_join_exists:
  forall (a b c ab bc ac : A), join a b ab -> join b c bc -> join a c ac ->
       {abc | join ab c abc}.
Arguments Trip_alg _ [J].

(* We do NOT yet introduce "emp" as a notation or synonym for "identity".
  This is because "emp" is a predicate of Separation Logic, but this file
  contains only Separation Algebras.  Some separation logics have
  predicates that are not just "t -> Prop", and therefore it is premature
  in this file to define "emp".
*)

(** * Lemmas about separation algebras. *)

Lemma  join_ex_units{A}{J: Join A}{SA: Sep_alg A}:
    forall a, {e : A & unit_for e a }.
Proof.
 intros. exists the_unit. apply join_unit.
Qed.

  (** Elements [a] and [b] join. *)
  Definition joins {A} {J: Join A} (a b : A) : Prop :=
    exists c, join a b c.

  Definition overlap {A}{J: Join A} (a b: A) := ~(joins a b).

  Lemma join_joins {A} {J: Join A}: forall {a b c},
    join a b c -> joins a b.
  Proof. intros; econstructor; eauto.
  Qed.

  Lemma join_joins' {A} {J: Join A} {PA: Perm_alg A}: forall {a b c},
    join a b c -> joins b a.
  Proof.
    intros; econstructor. eauto.
  Qed.

  Lemma joins_sym {A}  {J: Join A} {PA: Perm_alg A}: forall a b,
    joins a b <-> joins b a.
  Proof.
    intros.
    split; intro; destruct H;
      exists x; apply join_comm; trivial.
  Qed.

  Lemma joins_sym': forall {A} `{Perm_alg A} {phi1 phi2}, joins phi1 phi2 -> joins phi2 phi1.
  Proof.
   intros.
   apply joins_sym. auto.
  Qed.

  (** Elememt [a] is a subelement of [c] .  This relation forms a partial order. *)
  Definition join_sub {A} `{Join A} (a c : A) : Prop :=
    exists b, join a b c.

  Lemma join_join_sub {A} `{Perm_alg A}: forall {a b c},
    join a b c ->
    join_sub a c.
  Proof.
    intros; econstructor; eauto.
  Qed.

  Lemma join_join_sub' {A} `{Perm_alg A}: forall {a b c},
    join a b c ->
    join_sub b c.
  Proof.
    intros; econstructor; eauto.
  Qed.

  Lemma join_sub_refl {A} {J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: forall a,
    join_sub a a.
  Proof.
    intros.
    exists the_unit.
    apply join_comm, join_unit.
  Qed.

  Hint Resolve @join_sub_refl.

  Lemma join_sub_trans {A} {J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: forall a b c,
    join_sub a b ->
    join_sub b c ->
    join_sub a c.
  Proof.
 pose proof I. (* hack: shift up auto-named hyps *)
    intros. destruct H0; destruct H1.
    destruct (join_assoc H0 H1) as [f [? ?]].
    econstructor; eauto.
  Qed.

  Lemma join_sub_joins {A} `{HA: Perm_alg A}: forall {a b},
    join_sub a b -> joins a b -> joins a a.
  Proof.
    intros a b [? ?] [? ?].
    apply join_comm in H0.
    destruct (join_assoc H H0) as [? [? ?]].
    destruct (join_assoc H1 (join_comm H2)) as [? [? ?]].
    econstructor; eauto.
  Qed.
  (* Note: there are two other conceivable conclusions from the above
     premises: "joins b b" and "join_sub b a".  Neither must follow, since
     neither is true on the bools, but also neither is a contradiction
     since both are true on Z *)

  Lemma join_sub_joins_trans {A} `{HA: Perm_alg A}: forall {a b c},
    join_sub a c -> joins c b -> joins a b.
  Proof.
    intros.
    destruct H as [wx ?].
    destruct H0 as [wy ?].
    destruct (join_assoc (join_comm H) H0) as [wf [? ?]].
    econstructor; eauto.
  Qed.

  Lemma join_sub_joins'  {A} `{HA: Perm_alg A}:
    forall {a a' b b' : A},
      join_sub a a' -> join_sub b b' -> joins a' b' -> joins a b.
  Proof.
    intros.
    destruct H; destruct H0; destruct H1.
    destruct (join_assoc (join_comm H) H1) as [f [? ?]].
    destruct (join_assoc (join_comm H0) (join_comm H2)) as [g [? ?]].
    exists g; apply join_comm; auto.
  Qed.

  Definition sub_silhouette {A} `{Perm_alg A} (a b: A) : Prop :=
    forall c, joins c b -> joins c a.

  Definition same_silhouette {A} `{Perm_alg A} (a b: A) : Prop :=
    forall c, joins c a <-> joins c b.

  Lemma sub_silhouette_refl {A} `{Perm_alg A}: forall a, sub_silhouette a a.
  Proof. unfold sub_silhouette; intuition. Qed.

  Lemma sub_silhouette_trans {A} `{Perm_alg A}: forall a b c,
    sub_silhouette a b -> sub_silhouette b c -> sub_silhouette a c.
  Proof. unfold sub_silhouette; intuition. Qed.

  Lemma same_silhouette_refl {A} `{Perm_alg A}: forall a, same_silhouette a a.
  Proof. unfold same_silhouette; intuition. Qed.

  Lemma same_silhouette_sym {A} `{Perm_alg A}: forall a b,
    same_silhouette a b -> same_silhouette b a.
  Proof.  unfold same_silhouette; intros; split; apply H0; auto.
  Qed.

  Lemma same_silhouette_trans {A} `{Perm_alg A}: forall a b c,
    same_silhouette a b -> same_silhouette b c -> same_silhouette a c.
 Proof. unfold same_silhouette; intros; split; intros;
             destruct (H0 c0); destruct (H1 c0);   auto. Qed.

  Lemma same_silhouette_sub1{A} `{Perm_alg A}: forall a b,
    same_silhouette a b -> sub_silhouette a b.
  Proof. unfold same_silhouette, sub_silhouette; intros; intuition; destruct (H0 c); auto. Qed.

  Lemma same_silhouette_sub2 {A} `{Perm_alg A}: forall a b,
     same_silhouette a b -> sub_silhouette b a.
  Proof. unfold same_silhouette, sub_silhouette; intros; intuition; destruct (H0 c); auto. Qed.

  Lemma sub_same_silhouette {A} `{Perm_alg A}:
    forall a b, sub_silhouette a b -> sub_silhouette b a -> same_silhouette a b.
  Proof. unfold same_silhouette, sub_silhouette; intuition; destruct (H0 c); auto. Qed.

  Lemma same_silhouette_join {A} `{HA: Perm_alg A}:
    forall phi phi' phiy phiz phiz',
      same_silhouette phi phi' ->
      join phi phiy phiz ->
      join phi' phiy phiz' ->
      same_silhouette phiz phiz'.
  Proof.
    intros.
    intro phiu.
    split; intros [phix ?].
    destruct (join_assoc H0 (join_comm H2)) as [phif [? ?]].
    specialize (H phif).
    destruct H.
    assert (exists phiz, join phi phif phiz) by eauto.
    assert (joins phif phi) by (apply joins_sym;  auto).
    specialize (H H7).
    clear H5 H6 H7.
    destruct H as [phix' ?].
    destruct (join_assoc (join_comm H3) H) as [phig [? ?]].
    generalize (join_eq H1 (join_comm H5)); intro.
    rewrite <- H7 in *. clear phig H7 H5.
    exists phix'.
    auto.
    destruct (join_assoc H1 (join_comm H2)) as [phif [? ?]].
    specialize (H phif).
    destruct H.
    assert (exists phiz, join phi' phif phiz) by eauto.
    assert (joins phif phi') by (apply joins_sym;  auto).
    specialize (H5 H7).
    clear H H6 H7.
    destruct H5 as [phix' ?].
    destruct (join_assoc (join_comm H3) H) as [phig [? ?]].
    generalize (join_eq H0 (join_comm H5)); intro.
    rewrite <- H7 in *; clear phig H7 H5.
    exists phix'.
    auto.
  Qed.

Hint Resolve @join_joins @join_joins' @join_join_sub @join_join_sub'.

  Definition nonidentity {A} `{Perm_alg A} (a: A) := ~(identity a).

Lemma split_unit {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} :
  forall a b, join a b the_unit -> a = the_unit.
Proof.
  intros.
  eapply join_positivity, join_unit; eauto.
Qed.

  Lemma join_sub_antisym {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: forall x y,
    join_sub x y ->
    join_sub y x ->
    x = y.
  Proof.
    intros ? ? [? ?] [? ?].
    eapply join_positivity; eauto.
  Qed.

(** The opposite of identity is maximal or full *)

Definition full {A} {JA: Join A}(sigma : A) : Prop :=
   forall sigma', joins sigma sigma' -> identity sigma'.

Definition maximal {A} {JA: Join A} (sigma : A) : Prop :=
  forall sigma', join_sub sigma sigma' -> sigma = sigma'.

Lemma join_unit1 {A} `{Perm_alg A}:
  forall x y z, unit_for x z -> y = z -> join x y z.
Proof.
intros. rewrite H1 in *; auto.
Qed.

Lemma join_unit2 {A} `{Perm_alg A}:
  forall x y z, unit_for y z -> x = z -> join x y z.
Proof.
intros. rewrite  H1 in *;  clear x H1. apply join_comm; auto.
Qed.

Lemma join_unit1_e {A} `{Perm_alg A}{SA: Sep_alg A}:
  forall x y z, identity x -> join x y z -> y = z.
Proof.
intros.
eapply join_eq; eauto.
apply identity_unit in H0; subst.
apply join_unit.
Qed.

Lemma join_unit2_e {A} `{Perm_alg A}{SA: Sep_alg A}:
  forall x y z, identity y -> join x y z -> x = z.
Proof.
intros.
apply join_comm in H1.
eapply join_unit1_e; eauto.
Qed.

Lemma PermAlg_ext:
  forall (T: Type) (J: @Join T) (sa1 sa2: @Perm_alg T J), sa1=sa2.
Proof. intros.
destruct sa1, sa2.
f_equal; try apply proof_irr.
extensionality a b c d e H1 H2.
destruct (join_assoc1 a b c d e H1 H2) as [f [? ?]].
destruct (join_assoc0 a b c d e H1 H2) as [f0 [? ?]].
apply existT_ext.
eapply join_eq0; eauto.
Qed.

Lemma Sep_alg_ext {T} {J} {PA: @Perm_alg _ J}:
   forall (sa1 sa2: @Sep_alg T J), sa1=sa2.
Proof.
intros.
generalize (@unit_uniq _ J _ sa1 sa2); intro.
destruct sa1; destruct sa2.
simpl in H; subst.
f_equal.
apply proof_irr.
Qed.

Definition nonunit {A} `{Join A}  (a: A) := forall x, ~ unit_for a x.

Lemma nonunit_nonidentity {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall x, nonunit x -> ~identity x.
Proof. intros. intro X.
  apply identity_unit in X; subst.
  eapply (H the_unit), join_unit.
Qed.
