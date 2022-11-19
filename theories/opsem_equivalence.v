Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import opsem_systemF opsem_systemF_ctx syntax_systemF.

Lemma is_val_canonical e:
  is_val e -> exists v, e = (of_val v).
Proof.
  intros.
  induction H.
  - exists val_unit; auto.
  - destruct IHis_val1; subst.
    destruct IHis_val2; subst.
    eexists (val_pair _ _); auto.
  - eexists (val_abs _ _); auto.
  - eexists (val_tabs _); auto.
Qed.

Theorem op_semantic_eq:
  forall e e',
   opsem_systemF_ctx.step e e' <-> opsem_systemF.step e e'.
Proof.
Hint Resolve is_val_of_val.
  intros.
  split; intros.
  - induction H.
    subst.
    induction K; intros; subst; simpl;
      try (by inversion H1; subst; auto).
  - induction H;
    match goal with
      | h: _ ~> _ |- ?e1 ~> ?e2 => idtac
      | h: _ |- ?e1 ~> ?e2 =>
          eapply (Step _ _ EmptyCtx e1 e2 ); auto
      end.
    + inversion IHstep; subst.
      eapply (Step _ _ (FstCtx K) e1' e2' ); auto.
    + inversion IHstep; subst.
      eapply (Step _ _ (SndCtx K) e1' e2' ); auto.
    + inversion IHstep; subst.
      eapply (Step _ _ (LPairCtx K _) _ _); auto.
    + inversion IHstep; subst.
      apply is_val_canonical in H ; destruct H as [v' Hv]; subst.
      eapply (Step _ _ (RPairCtx K v') e1' e2'); auto.
    + inversion IHstep; subst.
      eapply (Step _ _ (LAppCtx K _) _ _); auto.
    + inversion IHstep; subst.
      apply is_val_canonical in H ; destruct H as [v' Hv]; subst.
      eapply (Step _ _ (RAppCtx K _) e1' e2'); auto.
    + inversion IHstep; subst.
      eapply (Step _ _ (TAppCtx K) _ _); auto.
Qed.
