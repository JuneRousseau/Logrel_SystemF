Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From stdpp Require Import list relations.
Require Import Autosubst.Autosubst.
From logical_relation Require Import syntax_systemF.

(*** Operational semantic of SystemF
     --- w/o evaluation context *)

(** This version is short and incomplete on purpose, as it is used for
    only as an equivalent semantic of the version with evaluation context
    to prove determinism *)

Reserved Notation "t '~>' t'" (at level 60).
Inductive step : expr -> expr -> Prop :=
| step_fst_red : forall v1 v2,
  is_val v1 ->
  is_val v2 ->
  <{ fst ⟨ v1, v2 ⟩ }> ~>  <{ v1 }>
| step_snd_red : forall v1 v2,
  is_val v1 ->
  is_val v2 ->
  <{ snd ⟨ v1, v2 ⟩ }> ~>  <{ v2 }>
| step_lam_red : forall e v,
  is_val v ->
  <{ (λ _, e) v }> ~>  e.[v/]
| step_tlam_red : forall e,
  <{ (Λ e) _ }> ~>  <{ e }>
| step_fst : forall e e',
  e ~> e' ->
  <{ fst e }> ~>  <{ fst e' }>
| step_snd : forall e e',
  e ~> e' ->
  <{ snd e }> ~>  <{ snd e' }>
| step_pairL : forall e1 e1' e2,
  e1 ~> e1' ->
  <{ ⟨ e1, e2 ⟩ }> ~>  <{ ⟨ e1', e2 ⟩  }>
| step_pairR : forall v e e',
  is_val v ->
  e ~> e' ->
  <{ ⟨ v, e ⟩ }> ~>  <{ ⟨ v, e' ⟩  }>
| step_lam_head : forall f f' e,
  f ~> f' ->
  <{ f e }> ~>  <{ f' e }>
| step_lam_arg : forall f e e',
  is_val f ->
  e ~> e' ->
  <{ f e }> ~>  <{ f e' }>
| step_tlam_head : forall e e',
  e ~> e' ->
  <{ e _ }> ~>  <{ e' _ }>
where "t '~>' t'" := (step t t').
Hint Constructors step : core.

(** Properties in the operational semantic *)
Lemma is_val_stuck : forall e e', is_val e -> not (e ~> e').
Proof.
  intros e e' val_e.
  generalize dependent e'.
  induction e; intros e' step; try inversion val_e;inversion step; subst.
  - eapply IHe1 in H1; eapply H1; eauto.
  - eapply IHe2 in H2; eapply H2; eauto.
Qed.

Lemma sf_deterministic : forall e e1 e2, e ~> e1 -> e ~> e2 -> e1 = e2.
Proof.
  intros e e' e'' step_e' step_e''.
  generalize dependent e''.
  induction step_e'; intros e'' step_e''.
  - inversion step_e''; subst; auto.
    + inversion H2; subst; apply is_val_stuck in H2; auto; contradiction.
  - inversion step_e''; subst; auto.
    inversion H2; subst; apply is_val_stuck in H2; auto; contradiction.
  - inversion step_e''; subst; auto.
    + inversion H3.
    + apply is_val_stuck in H4; auto; contradiction.
  - inversion step_e''; subst; auto.
    apply is_val_stuck in H0; auto; contradiction.
  - inversion step_e'';subst.
    apply is_val_stuck in step_e'; auto; contradiction.
    eapply IHstep_e' in H0; subst;auto.
  - inversion step_e'';subst.
    apply is_val_stuck in step_e'; auto; contradiction.
    eapply IHstep_e' in H0; subst;auto.
  - inversion step_e'';subst.
    eapply IHstep_e' in H2; subst;auto.
    apply is_val_stuck in step_e'; auto; contradiction.
  - inversion step_e'';subst.
    apply is_val_stuck in H3; auto; contradiction.
    eapply IHstep_e' in H4; subst;auto.
  - inversion step_e'';subst.
    apply is_val_stuck in step_e'; auto; contradiction.
    eapply IHstep_e' in H2; subst;auto.
    apply is_val_stuck in step_e'; auto; contradiction.
  - inversion step_e'';subst.
    apply is_val_stuck in step_e'; auto; contradiction.
    apply is_val_stuck in H3; auto; contradiction.
    eapply IHstep_e' in H4; subst;auto.
  - inversion step_e'';subst.
    apply is_val_stuck in step_e'; auto; contradiction.
    eapply IHstep_e' in H0; subst;auto.
Qed.
