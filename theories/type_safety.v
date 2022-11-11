Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import systemF.

Definition safe (e: expr) :=
  forall e', e ~>* e' ->
        (is_val e') \/ (exists e'', e' ~> e'').


(* TODO move to systemF.v, because they are properties of the language *)
Lemma is_val_step : forall e , is_val e -> e ~>* e.
Admitted.

Lemma is_val_stuck : forall e e', is_val e -> not (e ~> e').
Proof.
  intros e e' val_e.
  generalize dependent e'.
  induction e; intros e' step; try inversion val_e;inversion step; subst.
  - destruct K; subst; simpl in *; try discriminate H.
    rewrite <- H in H1; inversion H1.
  - destruct K; subst; simpl in *; try discriminate H3.
    eapply IHe1 with e2' in H1.
    admit.
    inversion H3; subst.
    admit.
    admit.
  - destruct K; subst; simpl in *; try discriminate H3.
    rewrite <- H in H3; inversion H3.
    all:try discriminate H.
  - destruct K; subst; simpl in *; try discriminate H3.
    rewrite <- H in H2; inversion H2.
    all: try discriminate H.
Admitted.

Theorem type_safety :
  forall e t, nil ; empty ⊢ e ∈ t -> safe e.
Proof.
  intros.
  induction H; unfold safe; intros.
  - (* unit *)
    left.
    inversion H; subst.
    apply v_unit.
    apply is_val_stuck in H0; [contradiction|].
    apply v_unit.
  - (* var *) admit.
  - (* pair *) admit.
  - (* fst *) admit.
  - (* snd *) admit.
  - (* abs *) admit.
  - (* app *)
Abort.

(** Naive Induction --- Fail *)
Theorem type_safety :
  forall e t, nil ; empty ⊢ e ∈ t -> safe e.
Proof.
  intros.
  induction H; unfold safe; intros.
  - (* unit *)
    left.
    inversion H; subst.
    apply v_unit.
    apply is_val_stuck in H0; [contradiction|].
    apply v_unit.
  - (* var *) admit.
  - (* pair *) admit.
  - (* fst *) admit.
  - (* snd *) admit.
  - (* abs *) admit.
  - (* app *)
Abort.

(** Progress and preservation *)

(** Logical relation and free theorems --- new files *)
