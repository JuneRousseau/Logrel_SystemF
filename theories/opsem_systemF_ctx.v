Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Relations.Relation_Operators.
From stdpp Require Import gmap list.
Require Import Autosubst.Autosubst.
From logical_relation Require Import syntax_systemF opsem_systemF.

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
| step_lam : forall e v,
  is_val v ->
  <{ (λ _, e) v }> -h-> e.[v/]
| step_tlam : forall e,
  <{ (Λ e) _ }> -h-> e
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

Definition mstep :=  clos_refl_trans_1n expr step.
Notation "t '~>*' t'" := (mstep t t') (at level 60).

Lemma fill_empty e : fill EmptyCtx e = e.
Proof. done. Qed.

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
    rewrite <- H in H2; inversion H2.
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

Lemma pure_step_deterministic : forall e e1 e2,
  e -h-> e1 -> e -h-> e2 -> e1 = e2.
Proof.
  intros e e1 e2 step1 step2.
  induction step1;inversion_clear step2;auto.
Qed.

Lemma step_fill K : forall e e',
    e ~> e' ->
    fill K e ~> fill K e'.
Proof.
  intros.
  inversion H; subst.
  rewrite! fill_comp.
  eapply Step; eauto.
Qed.

Lemma mstep_fill K : forall e e',
  e ~>* e' ->
  fill K e ~>* fill K e'.
Proof.
  intros. generalize dependent K.
  induction H; intros.
  + constructor.
  + apply (step_fill K) in H.
    econstructor;eauto.
    firstorder.
Qed.


Lemma is_val_fill K e :
  is_val (fill K e) -> is_val e.
Proof.
  intros.
  induction K; inversion H; cbn in *; subst;auto.
Qed.

(* If pure step from (fill K e), then either
   - e is a value
   - K is empty
 *)
Lemma pure_step_fill :
∀ K e e', (fill K e) -h-> e' → (∀ e'', (fill K e'') = e'') ∨ is_val e.
Proof.
  induction K;intros.
  - (* Empty *)
    left; cbn in *;intros;auto.
  - (* Fst *)
    destruct K; inversion H; subst; right.
    econstructor; eauto.
    by eapply is_val_fill.
    by eapply is_val_fill.
  - (* Snd *)
    destruct K; inversion H; subst; right.
    econstructor; eauto.
    by eapply is_val_fill.
    by eapply is_val_fill.
  - (* PairL *)
    destruct K; inversion H; subst; right.
  - (* PairR *)
    destruct K; inversion H; subst; right.
  - (* AppL *)
    destruct K; inversion H; subst; right; constructor.
  - (* AppR *)
    inversion H; subst; right.
    by eapply is_val_fill.
  - (* TApp *)
    destruct K; inversion H; subst; right; constructor.
Qed.

Lemma of_val_injective : forall e1 e2,
of_val e1 = of_val e2 -> e1 = e2.
Proof.
  induction e1; intros; destruct e2;cbn in H; auto; try discriminate;injection H
  ;intros.
  - apply IHe1_1 in H1;subst.
    apply IHe1_2 in H0;subst.
    reflexivity.
  - by subst.
  - by subst.
Qed.

Lemma ectx_decompose K1 K2 e1 e2 :
  (fill K1 e1) = (fill K2 e2) →
  ¬ is_val e1 →
  ¬ is_val e2 →
  (∃ K3, forall e3, (fill K1 e3) = (fill K2 (fill K3 e3)))
  ∨ (∃ K3, forall e3, (fill K2 e3) = (fill K1 (fill K3 e3))).
Proof.
  revert e1 e2 K2.
  induction K1; intros e1 e2 K2 Heq Hnv1 Hnv2; cbn in Heq.
  - (* EmptyCtx *)
    right. by exists K2; intros e3; cbn.
  - (* FstCtx *)
     destruct K2.
     all: try (by left; exists (FstCtx K1); cbn in *; auto).
     cbn in *.
     injection Heq; intro HeqK.
     apply IHK1 in HeqK; auto.
     destruct HeqK as [(K3 & HeqK)|(K3 & HeqK)]
     ;[left|right]; exists K3; intros; by rewrite HeqK.
  - (* SndCtx *)
     destruct K2.
     all: try (by left; exists (SndCtx K1); cbn in *; auto).
     cbn in *.
     injection Heq; intro HeqK.
     apply IHK1 in HeqK; auto.
     destruct HeqK as [(K3 & HeqK)|(K3 & HeqK)]
     ;[left|right]; exists K3; intros; by rewrite HeqK.
  - (* LPairCtx *)
     destruct K2.
     all: try (by left; exists (LPairCtx K1 e); cbn in *; auto).
     + cbn in *.
       injection Heq; intros -> HeqK.
       apply IHK1 in HeqK; auto.
       destruct HeqK as [(K3 & HeqK)|(K3 & HeqK)]
       ;[left|right]; exists K3; intros; by rewrite HeqK.
     + cbn in *.
       injection Heq; intros -> HeqK.
       pose proof (is_val_of_val v) as contra.
       rewrite <- HeqK in contra.
       apply is_val_fill in contra. contradiction.
  - (* RPairCtx *)
     destruct K2.
     all: try (by left; exists (RPairCtx K1 v); cbn in *; auto).
     + cbn in *.
       injection Heq; intros <- HeqK.
       pose proof (is_val_of_val v) as contra.
       rewrite HeqK in contra.
       apply is_val_fill in contra. contradiction.
     + cbn in *.
       injection Heq; intros HeqK HeqV.
       apply of_val_injective in HeqV ; subst.
       apply IHK1 in HeqK; auto.
       destruct HeqK as [(K3 & HeqK)|(K3 & HeqK)]
       ;[left|right]; exists K3; intros; by rewrite HeqK.
  - (* LAppCtx *)
     destruct K2.
     all: try (by left; exists (LAppCtx K1 e); cbn in *; auto).
     + cbn in *.
       injection Heq; intros <- HeqK.
       apply IHK1 in HeqK; auto.
       destruct HeqK as [(K3 & HeqK)|(K3 & HeqK)]
       ;[left|right]; exists K3; intros; by rewrite HeqK.
     + cbn in *.
       injection Heq; intros -> HeqK.
       pose proof (is_val_of_val v) as contra.
       rewrite <- HeqK in contra.
       apply is_val_fill in contra; contradiction.
  - (* RAppCtx *)
     destruct K2.
     all: try (by left; exists (RAppCtx K1 v); cbn in *; auto).
     + cbn in *.
       injection Heq; intros <- HeqK.
       pose proof (is_val_of_val v) as contra.
       rewrite HeqK in contra.
       apply is_val_fill in contra; contradiction.
     + cbn in *.
       injection Heq; intros HeqK HeqV.
       apply of_val_injective in HeqV ; subst.
       apply IHK1 in HeqK; auto.
       destruct HeqK as [(K3 & HeqK)|(K3 & HeqK)]
       ;[left|right]; exists K3; intros; by rewrite HeqK.
  - (* TAppCtx *)
     destruct K2.
     all: try (by left; exists (TAppCtx K1); cbn in *; auto).
     cbn in *.
     injection Heq; intros HeqK.
     apply IHK1 in HeqK; auto.
     destruct HeqK as [(K3 & HeqK)|(K3 & HeqK)]
     ;[left|right]; exists K3; intros; by rewrite HeqK.
Qed.

Lemma fill_K_injective K : forall e e',
 fill K e = fill K e' -> e = e'.
Proof.
  intros.
  induction K;cbn in *;auto;apply IHK; by injection H.
Qed.

Theorem opsem_equivalent:
  forall e e',
   opsem_systemF_ctx.step e e' <-> opsem_systemF.step e e'.
Proof.
Hint Resolve is_val_of_val : core.
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
      apply is_val_inversion in H ; destruct H as [v' Hv]; subst.
      eapply (Step _ _ (RPairCtx K v') e1' e2'); auto.
    + inversion IHstep; subst.
      eapply (Step _ _ (LAppCtx K _) _ _); auto.
    + inversion IHstep; subst.
      apply is_val_inversion in H ; destruct H as [v' Hv]; subst.
      eapply (Step _ _ (RAppCtx K _) e1' e2'); auto.
    + inversion IHstep; subst.
      eapply (Step _ _ (TAppCtx K) _ _); auto.
Qed.

Lemma sf_deterministic : forall e e1 e2, e ~> e1 -> e ~> e2 -> e1 = e2.
Proof.
  intros.
  apply opsem_systemF.sf_deterministic with (e:=e) ; by apply opsem_equivalent.
Qed.

Lemma step_ectx (K : ectx) e e' :
    (fill K e) ~> e' →
    (is_val e) ∨ (∃ e'', e ~> e'' ∧ e' = (fill K e'')).
Proof.
  intros Hstep.
  destruct (is_val_dec e) ; [left|right]; auto.
  inversion Hstep as [K' e1 e2 HeqK ? Hpstep]; subst.
  pose proof HeqK as HeqK0.
  apply ectx_decompose in HeqK;[|assumption| ];cycle 1.
  - intro contra. apply (is_val_stuck _ e2) in contra. apply contra.
    by apply pure_contextual_step.
  - destruct HeqK as [ ( K'' & HeqK ) | ( K'' & HeqK )]
    ; rewrite HeqK in Hstep.
    + rewrite HeqK in HeqK0.
      apply fill_K_injective in HeqK0.
      subst.
      pose proof Hpstep as Hpstep2.
      apply pure_step_fill in Hpstep.
      destruct Hpstep.
      * rewrite H0 in Hstep.
        rewrite H0 in Hpstep2.
        exists e2.
        split; [by apply pure_contextual_step|].
        rewrite HeqK.
        by rewrite H0.
      * tauto.
    + rewrite HeqK in HeqK0.
      apply fill_K_injective in HeqK0.
      exists (fill K'' e2); split; [| by rewrite HeqK].
      eapply Step;eauto.
Qed.

Inductive nstep : nat → expr → expr → Prop :=
| no_step e : nstep 0 e e
| next_step n e1 e2 e3 : step e1 e2 → nstep n e2 e3 → nstep (S n) e1 e3.

Lemma mstep_nstep e e' : mstep e e' → ∃ n, nstep n e e'.
Proof.
  intros. induction H as [| ????? IHstar].
  - exists 0 ; constructor.
  - destruct IHstar as (n & IH). exists (S n).
    econstructor;eauto.
Qed.

Lemma nstep_mstep n e e' : nstep n e e' → mstep e e'.
Proof.
  induction 1; econstructor;eauto.
Qed.

Lemma mstep_ectx (K : ectx) e e' :
    (fill K e) ~>* e' →
    (∃ e'', e' = (fill K e'') ∧ e ~>* e'')
    ∨ (∃ v , is_val v ∧ e ~>* v ∧ (fill K v) ~>* e').
Proof.
  intros.
  apply mstep_nstep in H.
  destruct H as [n Hnstep].
  revert e e' Hnstep.
  induction n; intros e e' Hnstep.
  - inversion Hnstep; subst; left; exists e ; split; auto; constructor.
  - inversion Hnstep as [|n' e1 e2 e3 HfillK Hnstep2];subst.
    apply step_ectx in HfillK.
    destruct HfillK as [HfillK | (e'' & Hstep_e & ->)].
    + right; exists e.
      split;auto.
      split;[constructor|].
      eapply nstep_mstep;eauto.
    + apply IHn in Hnstep2.
      destruct Hnstep2 as [ (e3 &?) | (e3 &?) ]
      ; [left | right]; exists e3; firstorder; econstructor;eauto.
Qed.

Lemma step_fst_val v1 v2:
  is_val v1 ->
  is_val v2 ->
  <{ fst (⟨ v1, v2 ⟩) }> ~> v1.
Proof.
  intros; eapply (Step _ _ EmptyCtx); eauto.
Qed.

Lemma step_snd_val v1 v2:
  is_val v1 ->
  is_val v2 ->
  <{ snd (⟨ v1, v2 ⟩) }> ~> v2.
Proof.
  intros; eapply (Step _ _ EmptyCtx); eauto.
Qed.

Lemma step_app_val e v:
  is_val v ->
  <{ (λ _, e) v }> ~>  e.[v/].
Proof.
  intros; eapply (Step _ _ EmptyCtx); eauto.
Qed.

#[export] Hint Resolve step_fst_val step_snd_val step_app_val : core.
