Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import syntax_systemF opsem_systemF.

Definition safe (e: expr) :=
  forall e', e ~>* e' ->
        (is_val e') \/ (exists e'', e' ~> e'').


(* TODO move to systemF.v, because they are properties of the language *)

(** Naive Induction --- Fail *)
Theorem type_safety :
  forall e t, nil ; empty ⊢ e ∈ t -> safe e.
Proof.
  intros.
  induction H; unfold safe; intros.
  - (* unit *)
    left.
    apply is_val_step in H; subst; apply v_unit.
  - (* var *) admit.
  - (* pair *) admit.
  - (* fst *) admit.
  - (* snd *) admit.
  - (* abs *) admit.
  - (* app *)
Abort.

Lemma is_val_inversion: forall e, is_val e -> ∃ v, e = (of_val v).
Proof.
Admitted.

(** Progress and preservation *)
Theorem progress : ∀ e t,
  nil; empty ⊢ e ∈ t ->
       is_val e ∨ ∃ e', e ~> e'.
Proof.
  intros.
  induction H.
  - (* unit *) left; apply v_unit.
  - (* var *) admit.
  - (* pair *)
    destruct IHtyping_judgment1, IHtyping_judgment2; [left|right..].
    + apply v_pair;auto.
    + destruct H2 as [e2' H2].
      exists <{ ⟨ e1, e2' ⟩ }>.
      apply is_val_inversion in H1; destruct H1.
      rewrite H1.
      apply step_pairR. apply is_val_of_val. auto.
    + destruct H1 as [e1' H1].
      exists <{ ⟨ e1', e2 ⟩ }>.
      apply step_pairL; auto.
    + destruct H1 as [e1' H1].
      exists <{ ⟨ e1', e2 ⟩ }>.
      apply step_pairL; auto.
  - (* fst *)
    destruct IHtyping_judgment; right.
    + inversion H0; try (rewrite <- H1 in H; inversion H).
    eexists; apply step_fst_red; auto.
    + destruct H0 as [e' H0].
      eexists; eapply step_fst; eauto.
  - (* snd *)
    destruct IHtyping_judgment; right.
    + inversion H0; try (rewrite <- H1 in H; inversion H).
    eexists; apply step_snd_red; auto.
    + destruct H0 as [e' H0].
      eexists; eapply step_snd; eauto.
  - (* abs *) left; apply v_abs.
  - (* app *)
    destruct IHtyping_judgment1, IHtyping_judgment2; right.
    + (* e has to be λ e' *)
      inversion H1;
      match goal with
      | h: ?val = e |- _ => rewrite <- h in H
      end;subst ; try inversion H.
      eexists; apply step_lam_red; auto.
    + destruct H2 as [e2 H2].
      eexists; eapply step_lam_arg ; eauto.
    + destruct H1 as [e1 H1].
      eexists; eapply step_lam_head ; eauto.
    + destruct H1 as [e1 H1].
      eexists; eapply step_lam_head ; eauto.
  - (* tabs *) left; apply v_tabs.
  - (* tapp *)
    destruct IHtyping_judgment; right.
    + (* e has to be Λ e' *)
      inversion H0;
      match goal with
      | h: ?val = e |- _ => rewrite <- h in H
      end;subst ; try inversion H.
      eexists; apply step_tlam_red; auto.
    + destruct H0 as [e' H0].
      eexists; eapply step_tlam_head; eauto.
Admitted.


Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.


Lemma canonical_form_pair:
  forall Δ Γ e t1 t2,
  Δ; Γ ⊢ e ∈ (t1 × t2)
     -> is_val e
     -> exists e1 e2, e = <{⟨ e1, e2 ⟩}>.
Proof.
  intros * HT val_e.
  destruct val_e;
  inversion HT; subst.
  eexists; eexists; eauto.
Qed.

Lemma not_free_context_weakening:
  forall α Γ Γ',
  Γ ⊆ Γ' →
  not_free_context α Γ →
  not_free_context α Γ'.
Proof.
  intros.
  unfold not_free_context in *.
Admitted.

Lemma weakening : ∀ Δ Δ' Γ Γ' e t,
  Γ ⊆ Γ' →
  Δ ; Γ ⊢ e ∈ t →
  Δ' ; Γ' ⊢ e ∈ t.
Proof.
  intros * H Ht.
  generalize dependent Γ'.
  generalize dependent Δ'.
  induction Ht; intros; eauto.
  - eapply lookup_weaken with (m2 := Γ') in H; eauto.
  - apply T_Lam. apply IHHt.
    by apply insert_mono.
  - apply T_TLam. apply IHHt; eauto.
    eapply not_free_context_weakening; eauto.
Qed.

Lemma weakening_empty : ∀ Δ Γ e t, nil ; empty ⊢ e ∈ t -> Δ ; Γ ⊢ e ∈ t.
Proof.
  intros.
  eapply weakening with nil empty.
  - apply map_empty_subseteq.
  - done.
Qed.

Lemma substitution_preserves_typing : ∀ Δ Γ x tx e v t,
  Δ ; <[x := tx]> Γ ⊢ e ∈ t ->
  nil ; empty ⊢ v ∈ tx ->
  Δ ; Γ ⊢ [x/v] e ∈ t.
Proof.
  intros * Ht Hv.
  generalize dependent Γ. generalize dependent t.
  generalize dependent Δ.
  induction e; intros * H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (x =? y)%string eqn:Heq; subst.
    + (* x=y *)
      (* rewrite update_eq in H3. *)
      (* injection H2 as H2; subst. *)
      (* apply weakening_empty. assumption. *)
      admit.
    + (* x<>y *)
      apply T_Var.
      apply eqb_neq in Heq.
      eapply lookup_insert_ne with (x:=tx) (m := Γ) in Heq.
      by setoid_rewrite Heq in H3.
  - (* abs *)
    admit.
  - (* tabs *)
    admit.
Admitted.

Theorem preservation : ∀ e e' t,
  nil ; empty ⊢ e ∈ t →
  e ~> e' →
  nil ; empty ⊢ e' ∈ t.
Proof.
  intros e e' t HTe step.
  generalize dependent e'.
  induction HTe; intros.
  - (* unit *)
    replace e' with <{ tt }>. apply T_Unit.
    symmetry; apply (is_val_step <{ tt }> e').
    apply v_unit.
    by apply star_one.
  - (* var *) admit.
  - (* pair *)
    inversion step; subst.
    apply IHHTe1 in H2; apply T_Prod; auto.
    apply IHHTe2 in H3; apply T_Prod; auto.
  - (* fst *)
    inversion step; subst.
    inversion HTe; subst; auto.
    apply IHHTe in H0.
    by eapply T_Fst.
  - (* snd *)
    inversion step; subst.
    inversion HTe; subst; auto.
    apply IHHTe in H0.
    by eapply T_Snd.
  - (* abs *)
    inversion step; subst.
  - (* app *)
    inversion step; subst.
    + inversion HTe1; subst; auto.
      admit.
    + apply IHHTe1 in H2.
      eapply T_App; eauto.
    + apply IHHTe2 in H3.
      eapply T_App; eauto.
  - (* tabs *)
    inversion step; subst.
  - (* tapp *)
    inversion step; subst.
    + inversion HTe; subst; auto.
      admit.
    + apply IHHTe in H0.
      eapply T_TApp; eauto.
Admitted.

Theorem type_safety_progress_preservation:
  forall e t, nil ; empty ⊢ e ∈ t -> safe e.
Proof.
  intros e T HT e' P. induction P.
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (e := a); auto.
Qed.

(** Logical relation and free theorems --- new files *)

Definition safe_parametrized (P : expr -> Prop) (e : expr) :
  forall e', e ~>* e' ->
        (is_val e' /\ P e) \/ (exists e'', e' ~> e'').
