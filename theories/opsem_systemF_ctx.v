Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
Require Import Autosubst.Autosubst.
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
| step_lam : forall e v,
  is_val v ->
  <{ (λ _, e) v }> -h-> e.[v/]
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
  + apply star_refl.
  + apply (step_fill K) in H.
    eapply star_step; eauto.
    apply IHstar.
Qed.

Definition is_val_dec :
  ∀ e, is_val e ∨ ¬ is_val e.
Proof.
   induction e; try (by right; inversion 1).
   - left; constructor.
   - destruct IHe1; [|by right; inversion 1].
     destruct IHe2; [|by right; inversion 1].
     by left; constructor.
   - left; constructor.
   - left; constructor.
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
      * tauto. (* TODO why does tauto work here ? *)
    + rewrite HeqK in HeqK0.
      apply fill_K_injective in HeqK0.
      exists (fill K'' e2); split; [| by rewrite HeqK].
      eapply Step;eauto.
Qed.

Lemma mstep_ectx (K : ectx) e e' :
    (fill K e) ~>* e' →
    (∃ e'', e' = (fill K e'') ∧ e ~>* e'')
    ∨ (∃ v , is_val v ∧ e ~>* v ∧ (fill K v) ~>* e').
Proof.
  intros.
  (* induction H. *)
  (* - induction e. *)
  (*   destruct (is_val_dec a). *)
  (*   + (* a is a value *) *)
  (*     right. exists a. *)
  (*     pose proof pure_step_fill. *)
  (* - destruct IHstar as [(e'' & -> & Hstep) | (v& Hval & Hmstep & Hstep)] *)
  (*   ; [left; exists e'' |right ; exists v]; firstorder. *)
  inversion H;subst.
  - left. exists e. split;auto;constructor.
  - fold (mstep b e') in H1.
    apply step_ectx in H0.
    destruct H0 as [Hv | (e'' & Hstep & ->)].
    + right. exists e; firstorder. constructor.
    (* + induction H1. *)
    (*   ++ destruct (is_val_dec e''). *)
    (*      +++ right. exists e''. *)
    (*          assert (e ~>* e'') by (econstructor;eauto). *)
    (*          firstorder. *)
    (*          apply mstep_fill with (K:= K) in H1. *)
    (*          admit. *)
    (*      +++ right. *)
    (*        admit. *)
    (*   ++ apply IHstar in H. apply H. *)

    + left. exists e; firstorder. 2: constructor.
      (* TODO I finally end up in the same issue than previously
         e --->* ef
         |       ^*
         v       |
         e' -----|
         which is true because determinism
         but I don't know how to prove it, because the reflexive path does not give anything. *)
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
