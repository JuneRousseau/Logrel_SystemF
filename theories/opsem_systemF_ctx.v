Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import relation syntax_systemF.


Reserved Notation "t '-h->' t'" (at level 60).
Inductive pure_step : expr -> expr -> Prop :=
| step_fst : forall v1 v2,
  is_val v1 ->
  is_val v2 ->
  <{ fst ⟨ v1, v2 ⟩ }> -h->  <{ v1 }>
| step_snd : forall v1 v2,
  is_val v1 ->
  is_val v2 ->
  <{ snd ⟨ v1, v2 ⟩ }> -h->  <{ v2 }>
| step_lam : forall x e v,
  is_val v ->
  <{ (λ x, e) v }> -h->  <{ [x / v]e }>
| step_tlam : forall e,
  <{ (Λ e) _ }> -h->  <{ e }>
where "t '-h->' t'" := (pure_step t t').

Hint Constructors pure_step : core.

Inductive ectx : Type :=
| EmptyCtx : ectx
| FstCtx : ectx -> ectx
| SndCtx : ectx -> ectx
| LPairCtx : ectx -> expr -> ectx
| RPairCtx : ectx -> val -> ectx
| LAppCtx : ectx -> expr -> ectx
| RAppCtx : ectx -> val -> ectx
| TAppCtx : ectx -> ectx.

Fixpoint fill (c : ectx) (e : expr) : expr :=
  match c with
  | EmptyCtx => e
  | FstCtx K => expr_fst (fill K e)
  | SndCtx K => expr_snd (fill K e)
  | LPairCtx K t => expr_pair (fill K e) t
  | RPairCtx K v => expr_pair (of_val v) (fill K e)
  | LAppCtx K t => expr_app (fill K e) t
  | RAppCtx K v => expr_app (of_val v) (fill K e)
  | TAppCtx K => expr_tapp (fill K e)
  end.

Reserved Notation "t '~>' t'" (at level 60).
Inductive step e1 e2 : Prop :=
| Step K e1' e2' :
  e1 = fill K e1' ->
  e2 = fill K e2' ->
  e1' -h-> e2' ->
  e1 ~> e2
where "e1 '~>' e2" := (step e1 e2).
Hint Constructors step : core.

Definition mstep := star expr step.
Notation "t '~>*' t'" := (mstep t t') (at level 60).

(* Definition reducible (e : expr) := *)
(*   ∃ e', step e e'. *)

Lemma fill_empty e : fill EmptyCtx e = e.
Proof. done. Qed.

(** Examples *)
Goal <{ (λ x , x) tt }> ~>* <{tt}>.
Proof.
  eapply star_one.
  eapply (Step _ _ EmptyCtx) ;
    [ done | done |].
  apply step_lam.
  apply v_unit.
Qed.

Goal <{ fst ((λ x , ( ⟨ (λ y , tt) x , (λ y , x) tt⟩ )) tt)}> ~>* <{tt}>.
Proof.
  eapply star_trans with <{ fst ( ⟨ (λ y , tt) tt , (λ y , tt) tt⟩ )}>.
  eapply star_one.
  eapply (Step _ _ (FstCtx EmptyCtx) ).
  1,2: simpl; done.
  eapply step_lam; apply v_unit.

  eapply star_trans with <{ fst ( ⟨ tt , (λ y , tt) tt⟩ )}>.
  eapply star_one.
  eapply (Step _ _ (FstCtx (LPairCtx EmptyCtx _)) ).
  1,2: simpl; done.
  eapply (step_lam y <{ tt }> ); apply v_unit.

  eapply star_trans with <{ fst ( ⟨ tt , tt⟩ )}>.
  eapply star_one.
  eapply (Step _ _ (FstCtx (RPairCtx EmptyCtx val_unit)) ).
  1,2: simpl;done.
  eapply (step_lam y <{ tt }> ); apply v_unit.

  eapply star_one.
  eapply (Step _ _ EmptyCtx).
  1,2: simpl; done.
  apply step_fst; apply v_unit.
Qed.

Lemma identity : forall v e, e = (of_val v) -> <{ (λ x , x) e }> ~>* <{e}>.
Proof.
  intros v e ->.
  eapply star_one.
  eapply (Step _ _ EmptyCtx).
  1,2: done.
  apply step_lam.
  apply is_val_of_val.
Qed.


Lemma is_val_stuck : forall e e', is_val e -> not (e ~> e').
Proof.
  intros e e' val_e.
  generalize dependent e'.
  induction e; intros e' step; try inversion val_e;inversion step; subst.
  - destruct K; subst; simpl in *; try discriminate H.
    rewrite <- H in H1; inversion H1.
  - destruct K; subst; simpl in *; try discriminate H3.
    + rewrite <- H3 in H5.
      inversion H5.
    + eapply IHe1 with (fill K e2') in H1.
      apply H1.
      inversion H3; subst.
      eapply (Step _ _ K); auto.
    + eapply IHe2 with (fill K e2') in H2.
      apply H2.
      inversion H3; subst.
      eapply (Step _ _ K); auto.
  - destruct K; subst; simpl in *; try discriminate H3.
    rewrite <- H in H3; inversion H3.
    all:try discriminate H.
  - destruct K; subst; simpl in *; try discriminate H3.
    rewrite <- H in H2; inversion H2.
    all: try discriminate H.
Qed.

Lemma is_val_step : forall e e', is_val e -> e ~>* e' -> e' = e.
  intros e e' val_e mstep.
  inversion mstep; subst; auto.
  by apply is_val_stuck in H.
Qed.
