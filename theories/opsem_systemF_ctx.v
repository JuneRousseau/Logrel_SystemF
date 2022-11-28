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

Fixpoint comp_ectx (K: ectx) (K' : ectx) : ectx :=
  match K with
  | EmptyCtx => K'
  | FstCtx K => FstCtx (comp_ectx K K')
  | SndCtx K => SndCtx (comp_ectx K K')
  | LPairCtx K v => LPairCtx (comp_ectx K K') v
  | RPairCtx K v => RPairCtx (comp_ectx K K') v
  | LAppCtx K v => LAppCtx (comp_ectx K K') v
  | RAppCtx K v => RAppCtx (comp_ectx K K') v
  | TAppCtx K => TAppCtx (comp_ectx K K')
  end.


Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; simpl; congruence. Qed.

Lemma pure_contextual_step e1 e2 :
  pure_step e1 e2 → step e1 e2.
Proof. eapply (Step _ _ EmptyCtx) ; by rewrite ?fill_empty. Qed.

Lemma fill_contextual_step K e1 e2 :
  step e1 e2 → step (fill K e1) (fill K e2).
Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
Qed.

(* Lemma about the context *)
Lemma cstep_app_r' f e e':
  step e e' →
  step (expr_app (of_val f) e) (expr_app (of_val f) e').
Proof.
  intros Hstep.
  by apply (fill_contextual_step (RAppCtx EmptyCtx f)) in Hstep.
Qed.

Lemma cstep_app_r f e e':
  is_val f ->
  step e e' →
  step (expr_app f e) (expr_app f e').
Proof.
  intros Hv Hstep.
  apply is_val_inversion in Hv; destruct Hv; subst.
  by apply cstep_app_r'.
Qed.

Lemma cstep_app_l e1 e1' e2:
  step e1 e1' →
  step (expr_app e1 e2) (expr_app e1' e2).
Proof.
  intros Hstep.
  by eapply (fill_contextual_step (LAppCtx EmptyCtx e2)).
Qed.

Lemma cstep_tapp e e':
  step e e' →
  step (expr_tapp e) (expr_tapp e').
Proof.
  intros Hstep.
  by eapply (fill_contextual_step (TAppCtx EmptyCtx)).
Qed.

Lemma cstep_fst e e':
  step e e' →
  step (expr_fst e) (expr_fst e').
Proof.
  intros Hstep.
  by eapply (fill_contextual_step (FstCtx EmptyCtx)).
Qed.

Lemma cstep_snd e e':
  step e e' →
  step (expr_snd e) (expr_snd e').
Proof.
  intros Hstep.
  by eapply (fill_contextual_step (SndCtx EmptyCtx)).
Qed.

Lemma cstep_pair_l e1 e1' e2:
  step e1 e1' →
  step (expr_pair e1 e2) (expr_pair e1' e2).
Proof.
  intros Hstep.
  by eapply (fill_contextual_step (LPairCtx EmptyCtx e2)).
Qed.

Lemma cstep_pair_r' v e e':
  step e e' →
  step (expr_pair (of_val v) e) (expr_pair (of_val v) e').
Proof.
  intros Hstep.
  by apply (fill_contextual_step (RPairCtx EmptyCtx v)) in Hstep.
Qed.

Lemma cstep_pair_r v e e':
  is_val v ->
  step e e' →
  step (expr_pair v e) (expr_pair v e').
Proof.
  intros Hv Hstep.
  apply is_val_inversion in Hv; destruct Hv; subst.
  by apply cstep_pair_r'.
Qed.

Lemma pure_step_deterministic : deterministic expr pure_step.
Proof.
  intros e e1 e2 step1 step2.
  induction step1;inversion_clear step2;auto.
Qed.

Lemma sf_deterministic : deterministic expr step.
Proof.
  intros e e1 e2 step1 step2.
  inversion step1 ; subst.
  inversion step2; subst.
Admitted.

#[export]
  Hint Resolve
  cstep_app_l
  cstep_app_r
  cstep_tapp
  cstep_fst
  cstep_snd
  cstep_pair_l
  cstep_pair_r : core.
