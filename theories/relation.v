Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

Section Relation.
  Variable A: Type. (* the type of states *)
  Variable R: A -> A -> Prop. (* the transition relation between states *)

  Inductive star : A -> A -> Prop :=
  | star_refl: forall a, star a a
  | star_step: forall a b c, R a b -> star b c -> star a c.

  Lemma star_one:
    forall (a b: A), R a b -> star a b.
  Proof.
    eauto using star.
  Qed.

  Lemma star_trans:
    forall (a b: A), star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; eauto using star.
  Qed.

  Definition deterministic R :=
  forall x y1 y2 : A, R x y1 -> R x y2 -> y1 = y2.

  Lemma star_star_inv:
    deterministic R ->
    forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
  Proof.
    induction 2; intros.
    - auto.
    - inversion H2; subst.
      + right. eauto using star.
      + assert (b = b0) by (eapply H; eauto). subst b0.
        apply IHstar; auto.
  Qed.
End Relation.

#[export]
Hint Constructors star : core.
