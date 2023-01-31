Require Import Ensembles.
Require Import Finite_sets.
Require Import ZArith.
Require Import Lia.
Local Open Scope Z_scope.

Definition relation (X: Type) := X -> X -> Prop.
Check relation.

Definition reflexive {X: Type} (R: relation X) := forall a: X, R a a.
Definition symmetric {X: Type} (R: relation X) := forall a b: X, R a b -> R b a.
Definition transitive {X: Type} (R: relation X) := forall a b c: X,
    R a b /\ R b c -> R a c.

Definition equivalence {X: Type} (R: relation X) :=
  reflexive R /\ symmetric R /\ transitive R.

Check equivalence.

Inductive equiv_class {X: Type} (R: relation X) (a: X) : Ensemble X :=
  equiv_class_intro : forall b: X, equivalence R ->
                                   R a b ->
                                   In X (equiv_class R a) b.

Inductive quotient {X: Type} (R: relation X) : Ensemble (Ensemble X) :=
  quotient_intro : forall a: X,
    In (Ensemble X) (quotient R) (equiv_class R a).

Check quotient.

Proposition equiv_class_strong: forall (X: Type) (R: relation X) (x y: X),
    equivalence R ->
    R x y -> equiv_class R x = equiv_class R y.
Proof.
  intros X R x y ER xRy. assert (ER' := ER). destruct ER' as [ref].
  destruct H as [sym]. rename H into tra.
  apply Extensionality_Ensembles. unfold Same_set. split.
  + unfold Included. intros xp xp_in_EQx.
    assert (R y xp).
  - destruct xp_in_EQx as [xp].
    unfold symmetric in sym. specialize sym with (a := x) (b := y).
    apply sym in xRy. rename xRy into yRx.
    unfold transitive in tra. specialize tra with (a := y) (b := x) (c := xp).
    apply tra. now split.
  - now constructor.
    + unfold Included. intros yp yp_in_EQy.
      assert (R x yp).
  - destruct yp_in_EQy as [yp].
    unfold transitive in tra. specialize tra with (a := x) (b := y) (c := yp).
    apply tra. now split.
  - now constructor.
Qed.

Proposition equiv_class_uniq: forall (X: Type) (R: relation X) (x y: X),
    equivalence R ->
    equiv_class R x = equiv_class R y -> R x y.
Proof.
  intros X R x y ER Rx_eq_Ry.
  assert (In X (equiv_class R x) x).
  - constructor.
    + assumption.
    + destruct ER. unfold reflexive in H. specialize H with (a := x). assumption.
  - rewrite Rx_eq_Ry in H. destruct H as [x]. destruct H. destruct H1.
    unfold symmetric in H1. specialize H1 with (a := y) (b := x).
    now apply H1 in H0.
Qed.

Proposition equiv_class_ident: forall (X: Type) (R: relation X) (x y: X),
    equivalence R ->
    equiv_class R x = equiv_class R y <-> R x y.
  intros. split.
  + intro. now apply equiv_class_uniq.
  + intro. now apply equiv_class_strong.
Qed.

Check equiv_class_ident.

Definition z_cong (n a b: Z) := n >= 2 /\ exists k: Z, a = n * k + b.

Check cardinal.

Inductive one_set : Ensemble Z :=
  first_three: forall n: Z, n > 0 /\ n < 2 -> In Z one_set n.

Proposition one_set_card: cardinal Z one_set 1.
Proof.
  assert (Add Z (Empty_set Z) 1 = one_set).
  apply Extensionality_Ensembles. unfold Same_set. unfold Included. split.
  1: {
    intros. inversion H. inversion H0. constructor. now inversion H0.
  }
  1: {
    intros. constructor 2. inversion H. assert (x=1). lia. now rewrite H2.
  }
  rewrite <- H. constructor. constructor.
  easy.
Qed.

Print equiv_class.

Inductive n_element (n: Z) : Ensemble Z :=
  n_element_intro: forall m: Z, m >= 0 -> m < n -> In Z (n_element n) m.

Proposition case_2: forall n: Z, (exists k: Z, 2 * k = n) \/ (exists k: Z, 2 * k + 1 = n).
Proof.
  intro. destruct n. left. exists 0. reflexivity.
  destruct p.
  1: {
    right. exists (Z.pos p). lia.
  }
  1: {
    left. exists (Z.pos p). lia.
  }
  1: {
    right. exists 0. reflexivity.
  }
  destruct p.
  + right. exists (Z.neg p - 1). lia.
  + left. exists (Z.neg p). lia.
  + right. exists (-1). reflexivity.
Qed.

Proposition z_cong_in_base: ~ In (Ensemble Z)
                              (quotient (z_cong 2))
                              (n_element 2).
Proof.
  intro. inversion H.
  assert ((exists k: Z, 2 * k = a) \/ (exists k: Z, 2 * k + 1 = a)).
  apply (case_2 a).
  destruct H0.
  + destruct H0.
    (* a is even. so one is not in the equiv_class (z_cong 2) a *)
    assert (~ In Z (equiv_class (z_cong 2) a) 1).
    intro. inversion H2. inversion H4. destruct H7. lia.
    assert (In Z (n_element 2) 1).
    constructor; easy.
    now rewrite <- H1 in H3.
  + destruct H0.
    (* a is odd. so zero is not in the equiv_class (z_cong 2) a *)
    assert (~ In Z (equiv_class (z_cong 2) a) 0).
    intro. inversion H2. inversion H4. destruct H7. lia.
    assert (In Z (n_element 2) 0).
    constructor; easy.
    now rewrite <- H1 in H3.
Qed.

Proposition z_cong_reduce: forall n: Z,
    n >= 2 -> forall m: Z, exists r: Z,
        equiv_class (z_cong n) m = equiv_class (z_cong n) r.
Proof.
  intros. exists (m - n). apply Extensionality_Ensembles. unfold Same_set.
  split.
  - unfold Included; intros. constructor.
    + now inversion H0.
    + constructor. assumption.
      inversion H0. inversion H2. destruct H5. exists (x0 - 1). lia.
  - unfold Included; intros. constructor.
    + now inversion H0.
    + constructor. assumption. inversion H0. inversion H2. destruct H5.
      exists (x0 + 1). lia.
Qed.

Proposition z_cong_eq_rel: forall n, n >= 2 -> equivalence (z_cong n).
Proof.
  intros. unfold equivalence. split.
  1: {
    unfold reflexive. intro. unfold z_cong. split. assumption.
    exists 0. lia.
  }
  split.
  1: {
    unfold symmetric. intros. unfold z_cong. split. assumption.
    unfold z_cong in H0. destruct H0. destruct H1 as [k].
    exists (-k). lia.
  }
  1: {
    unfold transitive. intros. destruct H0. unfold z_cong. split. assumption.
    unfold z_cong in H0, H1. destruct H0, H1.
    destruct H2 as [k]. destruct H3 as [kp].
    exists (k + kp). lia.
  }
Qed.

Goal forall (n a a' b b': Z), n >= 2 -> z_cong n a a' /\ z_cong n b b' ->
                              z_cong n (a * b) (a' * b').
Proof.
  intros. destruct H0. unfold z_cong. split. assumption.
  unfold z_cong in H0, H1. destruct H0, H1.
  destruct H2 as [k]. destruct H3 as [kp].
  exists (n*k*kp + k*b' + kp*a'). lia.
Qed.

Goal forall (n a a' b b': Z), n >= 2 -> z_cong n a a' /\ z_cong n b b' ->
                              z_cong n (a + b) (a' + b').
Proof.
  intros. destruct H0. unfold z_cong. split. assumption.
  unfold z_cong in H0, H1. destruct H0, H1.
  destruct H2 as [k]. destruct H3 as [kp].
  exists (k + kp). lia.
Qed.
