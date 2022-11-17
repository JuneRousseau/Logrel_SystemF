Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import syntax.

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
| step_lam_red : forall x e v,
  is_val v ->
  <{ (λ x, e) v }> ~>  <{ [x / v]e }>
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

Definition mstep := star expr step.
Notation "t '~>*' t'" := (mstep t t') (at level 60).

(* Definition reducible (e : expr) := *)
(*   ∃ e', step e e'. *)

(** Examples *)
Goal <{ (λ x , x) tt }> ~>* <{tt}>.
Proof.
  eapply star_one.
  apply step_lam_red.
  apply v_unit.
Qed.

Goal <{ fst ((λ x , ( ⟨ (λ y , tt) x , (λ y , x) tt⟩ )) tt)}> ~>* <{tt}>.
Proof.
  eapply star_trans with <{ fst ( ⟨ (λ y , tt) tt , (λ y , tt) tt⟩ )}>.
  eapply star_one.
  eapply step_fst; eapply step_lam_red ; apply v_unit.

  eapply star_trans with <{ fst ( ⟨ tt , (λ y , tt) tt⟩ )}>.
  eapply star_one.
  eapply step_fst; eapply step_pairL; eapply (step_lam_red y <{ tt }> ); apply v_unit.

  eapply star_trans with <{ fst ( ⟨ tt , tt⟩ )}>.
  eapply star_one.
  eapply step_fst; eapply step_pairR;[apply v_unit|];
    eapply (step_lam_red y <{ tt }> ); apply v_unit.

  eapply star_one.
  eapply step_fst_red; apply v_unit.
Qed.

Lemma identity : forall v e, e = (of_val v) -> <{ (λ x , x) e }> ~>* <{e}>.
Proof.
  intros v e ->.
  eapply star_one.
  apply step_lam_red.
  apply is_val_of_val.
Qed.

Lemma is_val_stuck : forall e e', is_val e -> not (e ~> e').
Proof.
  intros e e' val_e.
  generalize dependent e'.
  induction e; intros e' step; try inversion val_e;inversion step; subst.
  - eapply IHe1 in H1; eapply H1; eauto.
  - eapply IHe2 in H2; eapply H2; eauto.
Qed.

Lemma is_val_step : forall e e', is_val e -> e ~>* e' -> e' = e.
  intros e e' val_e mstep.
  inversion mstep; subst; auto.
  by apply is_val_stuck in H.
Qed.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
                      match type of T with Prop =>
                                             solve [
                                                 inversion H;
                                                 match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
                      end end.

Lemma sf_deterministic : deterministic expr step.
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

Lemma step_deterministic_multiple : forall e e' e'',
  e ~> e'
  -> e ~>* e''
  -> e' ~>* e''.
Proof.
  intros e e' e'' step_e mstep_e.
Admitted.
