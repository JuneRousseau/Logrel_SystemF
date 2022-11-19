Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import relation syntax_stlc opsem_stlc.

Implicit Types Γ : context.
Implicit Types τ : ty.

Definition substitution := list (string*val).
Implicit Types γ : substitution.
Fixpoint domain γ :=
  match γ with
    | nil => []
    | (x,v)::γ' => x::(domain γ')
  end.

Fixpoint substitute γ e :=
  match γ with
  | nil => e
  | (x,v)::γ' => substitute γ' (subst_term x (of_val v) e)
  end.

Definition normalize_to_v e v :=
  is_val v -> e ~>* v.

Definition normalize e :=
  exists v, normalize_to_v e v.
Notation "⇓ e" := (normalize e) (at level 99).

Fixpoint sn (τ : ty) (e : expr) :=
 match τ with
 | Ty_Bool => (∅ ⊢ e ∈ Bool) /\ ⇓ e
 | Ty_Arrow t1 t2 =>
    (∅ ⊢ e ∈ (t1 -> t2))
    /\ (⇓ e)
    /\ (forall e', sn t1 e' -> sn t2 <{ e e' }> )
 end.

Definition sem_subst γ Γ :=
  Forall (fun x => sn (match (Γ !! x) with
                      | None => Ty_Bool
                      | Some t => t
                    end)
                  (substitute γ (expr_var x)))
    (domain γ).
  (* dom Γ = domain γ. *)
Notation " γ ⊨ Γ" := (sem_subst γ Γ) (at level 99).
Lemma sn_safe : forall τ e, sn τ e -> ⇓ e.
Proof.
  intros.
  destruct τ; simpl in H ; firstorder.
Qed.

Lemma substitution_lemma Γ γ τ e :
  Γ ⊢ e ∈ τ ->
  γ ⊨ Γ ->
  (typing_judgment ∅ (substitute γ e) τ).
Admitted.

Lemma sn_backward τ e e':
 (∅ ⊢ e ∈ τ) ->
 e ~> e' ->
 (sn τ e' -> sn τ e).
Admitted.

Lemma sn_backward_star τ e e':
 (∅ ⊢ e ∈ τ) ->
 e ~>* e' ->
 (sn τ e' -> sn τ e).
Admitted.

Lemma sn_forward τ e e':
 (∅ ⊢ e ∈ τ) ->
 e ~> e' ->
 (sn τ e -> sn τ e').
Admitted.

Lemma sn_forward_star τ e e':
 (∅ ⊢ e ∈ τ) ->
 e ~>* e' ->
 (sn τ e -> sn τ e').
Admitted.

Lemma sn_well_typed τ e: sn τ e -> (∅ ⊢ e ∈ τ).
Proof.
  intros. destruct τ; simpl in *;firstorder.
Qed.

Lemma substitute_true γ :
(substitute γ <{ true }> ) = <{true}>.
Admitted.
Lemma substitute_false γ :
(substitute γ <{ false }> ) = <{false}>.
Admitted.

Lemma substitute_app γ e e' :
(substitute γ <{ e e' }>) =
  expr_app (substitute γ <{ e }>) (substitute γ <{ e' }>).
Admitted.

Lemma substitute_if γ e e1 e2 :
(substitute γ <{ if e then e1 else e2 }>) =
  expr_if (substitute γ <{ e }>) (substitute γ <{ e1 }>) (substitute γ <{ e2 }>).
Admitted.

Lemma fundamental : forall Γ γ τ e,
  (Γ ⊢ e ∈ τ) ->
  γ ⊨ Γ ->
  sn τ (substitute γ e).
Proof.
  induction 1 ; simpl in *; intros.
  - (* true *)
    split; rewrite substitute_true; auto.
    eexists; intro; eapply star_refl.
  - (* false *)
    split; rewrite substitute_false; auto.
    eexists; intro; eapply star_refl.
  - (* var *) admit.
  - (* lam *)
    split.
    apply substitution_lemma with (Γ := Γ);auto.
    split. admit.
    intros.
    admit.
  - (* app *)
    pose proof H1 as H2.
    apply IHtyping_judgment1 in H1
    ; clear IHtyping_judgment1
    ; destruct H1 as (IH1_type & IH1_norm & IH1_sn).
    apply IHtyping_judgment2 in H2; clear IHtyping_judgment2.
    rewrite substitute_app.
    by apply IH1_sn.
  - (* if *)
    pose proof H2 as H3;
    pose proof H2 as H4.
    apply IHtyping_judgment1 in H2
    ; clear IHtyping_judgment1
    ; destruct H2 as [H_bool H_norm].
    apply IHtyping_judgment2 in H3
    ; clear IHtyping_judgment2.
    apply IHtyping_judgment3 in H4
    ; clear IHtyping_judgment3.

    destruct H_norm as [v H_norm].
    assert (Hv : (substitute γ e) ~>* <{ true }>
                 \/ (substitute γ e) ~>* <{ false }> ).
    { admit. }
    destruct Hv.
    + (* true *)
      apply sn_backward_star
        with (e' := expr_if expr_true (substitute γ e1) (substitute γ e2)).
      rewrite substitute_if.
      apply T_If; auto;
      apply sn_well_typed;auto.
      rewrite substitute_if.
      admit.
      apply sn_backward_star with (e' := (substitute γ e1));auto.
      admit.
      apply star_one; auto.
    + (* false *)
      apply sn_backward_star
        with (e' := expr_if expr_false (substitute γ e1) (substitute γ e2)).
      rewrite substitute_if.
      apply T_If; auto;
      apply sn_well_typed;auto.
      rewrite substitute_if.
      admit.
      apply sn_backward_star with (e' := (substitute γ e2));auto.
      admit.
      apply star_one; auto.
Admitted.


Lemma well_typed_sn: forall τ e, (∅ ⊢ e ∈ τ) -> sn τ e.
