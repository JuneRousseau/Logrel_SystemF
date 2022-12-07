Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
Require Import Autosubst.Autosubst.
From logical_relation Require Import relation syntax_stlc.

Reserved Notation "t '~>' t'" (at level 60).
Inductive step : expr -> expr -> Prop :=
| step_if_true : forall e1 e2,
  <{ if true then e1 else e2 }> ~> <{ e1 }>
| step_if_false : forall e1 e2,
  <{ if false then e1 else e2 }> ~> <{ e2 }>

| step_lam_red : forall e v,
  is_val v ->
  <{ (λ _, e) v }> ~> e.[v/]

| step_if : forall e e' e1 e2,
  e ~> e' ->
  <{ if e then e1 else e2 }> ~> <{ if e' then e1 else e2 }>
| step_lam_head : forall f f' e,
  f ~> f' ->
  <{ f e }> ~>  <{ f' e }>
| step_lam_arg : forall f e e',
  is_val f ->
  e ~> e' ->
  <{ f e }> ~>  <{ f e' }>
where "t '~>' t'" := (step t t').
Hint Constructors step : core.

Definition mstep := star expr step.
Notation "t '~>*' t'" := (mstep t t') (at level 60).

(* Definition reducible (e : expr) := *)
(*   ∃ e', step e e'. *)

(** Examples *)
Lemma identity : forall v e, e = (of_val v) -> <{ (λ _ , #0) e }> ~>* <{e}>.
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
Qed.

Lemma is_val_step : forall e e', is_val e -> e ~>* e' -> e' = e.
  intros e e' val_e mstep.
  inversion mstep; subst; auto.
  by apply is_val_stuck in H.
Qed.

Ltac solve_by_inverts n :=
  match goal with
  | H : ?T |- _ =>
      match type of T with Prop =>
      solve [inversion H; match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
      end
  end.

Lemma stlc_deterministic : deterministic expr step.
Proof.
  intros e e' e'' step_e' step_e''.
  generalize dependent e''.
  induction step_e'; intros e'' step_e''.
  - inversion step_e''; subst; auto.
    + inversion H3; subst; apply is_val_stuck in H3; auto; contradiction.
  - inversion step_e''; subst; auto.
    inversion H3; subst; apply is_val_stuck in H3; auto; contradiction.
  - inversion step_e''; subst; auto.
    + inversion H3.
    + apply is_val_stuck in H4; auto; contradiction.
  - inversion step_e''; subst; auto.
    + apply is_val_stuck in step_e'; auto; contradiction.
    + apply is_val_stuck in step_e'; auto; contradiction.
    + eapply IHstep_e' in H3; subst;auto.
  - inversion step_e'';subst.
    apply is_val_stuck in step_e'; auto; contradiction.
    eapply IHstep_e' in H2; subst;auto.
    apply is_val_stuck in step_e'; auto; contradiction.
  - inversion step_e'';subst.
    apply is_val_stuck in step_e'; auto; contradiction.
    apply is_val_stuck in H3; auto; contradiction.
    eapply IHstep_e' in H4; subst;auto.
Qed.

Lemma star_step : forall e e2 e3,
  e ~>* e2 ->
  e2 ~> e3 ->
  (exists e1, e ~> e1 /\ e1 ~>* e2) \/ e = e3.
Proof.
  intros.

  (* eapply star_star_inv in H. ; eauto. *)

  (* inversion H; subst e2; subst. *)
  (* left. exists e3. *)
  (* apply star_trans with (a:= e3) in H. *)
  (* split ; eauto. *)
  (* apply star_trans with (a:= e3) in H; auto. *)

Admitted.

Lemma step_deterministic_multiple : forall e e' e'',
  e ~> e'
  -> e ~>* e''
  -> e' ~>* e''.
Proof.
  intros e e' e'' step_e mstep_e.
  inversion mstep_e; subst.
  - eapply star_step in mstep_e; eauto.
    destruct mstep_e as [ (e0& mstep_e& mstep_eO) | mstep_e ].
    eapply stlc_deterministic in step_e. apply step_e in mstep_e. subst.
    done.
    subst; constructor.
  -
Admitted.


Lemma is_val_inversion : forall e, is_val e -> exists v, e = (of_val v).
Proof.
  intros.
  destruct e;inversion H;[ exists val_true | exists val_false | eexists (val_lam _) ]; eauto.
Qed.

Lemma mstep_app_arg: forall e v f,
  is_val f ->
  e ~>* v ->
  <{ f e }> ~>*
  <{ f v }>.
Proof.
  intros * f_val H.
  induction H using star_ind.
  - apply star_refl.
  - eapply relation.star_step with (b := <{ f b }>); auto.
Qed.

Lemma mstep_if: forall e e' e1 e2,
  e ~>* e' ->
  <{ if e then e1 else e2}> ~>*
  <{ if e' then e1 else e2}>.
Proof.
  intros.
  induction H using star_ind.
  - apply star_refl.
  - eapply relation.star_step with (b := <{ if b then e1 else e2 }>); auto.
Qed.

Lemma mstep_if_true: forall e e1 e2,
  e ~>* <{ true }> ->
  <{ if e then e1 else e2}> ~>*
  <{ e1 }>.
Proof.
  intros.
  eapply relation.star_trans with (b := <{ if true then e1 else e2 }>).
  apply mstep_if; auto.
  eapply star_one;auto.
Qed.

Lemma mstep_if_false: forall e e1 e2,
  e ~>* <{ false }> ->
  <{ if e then e1 else e2}> ~>*
  <{ e2 }>.
Proof.
  intros.
  eapply relation.star_trans with (b := <{ if false then e1 else e2 }>).
  apply mstep_if; auto.
  eapply star_one;auto.
Qed.
