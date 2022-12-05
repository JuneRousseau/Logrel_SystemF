Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import syntax_stlc opsem_stlc.

Definition normalize e := exists v, is_val v /\ e ~>* v.
Notation "'⇓' e" := (normalize e) (at level 50).

Fixpoint logrel (τ : ty) (e: expr) : Prop:=
  match τ with
  | Ty_Bool => ∅ ⊢ e ∈ Bool /\ ⇓ e
  | Ty_Arrow τ1 τ2 => ∅ ⊢ e ∈ <{ τ1 -> τ2 }>
                         /\ ⇓ e
                         /\ (forall e', logrel τ1 e' -> logrel τ2 <{e e'}>)
  end.

Lemma logrel_wt (τ : ty) (e: expr) :
  logrel τ e -> ∅ ⊢ e ∈ τ.
Admitted.

Lemma logrel_sn (τ : ty) (e: expr) :
  logrel τ e -> ⇓ e.
Admitted.


Fixpoint substitute_list γ e :=
  match γ with
  | nil => e
  | (x,v)::γ' => substitute_list γ' <{[x/v] e}>
  end.

Definition substitute (γ : gmap string expr) e :=
  substitute_list (map_to_list γ) e.

Definition substitution_satisfaction (γ : gmap string expr) (Γ : context) :=
  dom Γ = dom γ
  /\ forall x, match (Γ !! x) with
         | None => True
         | Some t => logrel t (substitute γ (expr_var x))
         end.

Notation "γ '⊨' Γ" := (substitution_satisfaction γ Γ) (at level 50).

Lemma substitution_lemma γ Γ e τ :
  (Γ ⊢ e ∈ τ /\ γ ⊨ Γ) ->
  typing_judgment ∅ (substitute γ e) τ.
Admitted.

(* Lemma backward_prop  *)

Lemma subst_true γ :
 substitute γ <{ true }> = <{ true }>.
Admitted.
Lemma subst_false γ :
 substitute γ <{ false }> = <{ false }>.
Admitted.

Lemma subst_ife γ e e1 e2 :
 substitute γ <{ if e then e1 else e2 }> =
   (expr_if
      (substitute γ e)
      (substitute γ e1)
      (substitute γ e2)).
Admitted.

Lemma subst_lam γ x e :
  substitute γ (expr_abs x e)
  =
    (expr_abs x ( substitute γ e)).
Admitted.

Lemma subst_app γ e e' :
  substitute γ (expr_app e e')
  =
  (expr_app (substitute γ e) (substitute γ e')).
Admitted.


Lemma backward_presevartion e e' τ:
  ∅ ⊢ e ∈ τ -> e ~>* e' -> logrel τ e' -> logrel τ e.
Admitted.

Theorem ftlr : forall Γ e τ γ,
  Γ ⊢ e ∈ τ -> γ ⊨ Γ -> logrel τ (substitute γ e).
Proof.
  intros.
  generalize dependent γ.
  induction H; intros;simpl.
  - rewrite subst_true.
    split. constructor. exists <{ true }>. split;auto;constructor.
  - rewrite subst_false.
    split. constructor. exists <{ false }>. split;auto;constructor.
  - destruct H0 as [Hdom Hx].
    by specialize (Hx x) ; rewrite H in Hx.
  - split;[|split].
    + eapply substitution_lemma; eauto.
    + rewrite subst_lam. exists (expr_abs x (substitute γ e)).
      split ; constructor.
    + intros.
      rewrite subst_lam.
      pose proof H2 as H2'.
      apply logrel_sn in H2; destruct H2 as (v & Hv & Hstepe').
      apply (backward_presevartion
               _
               (subst_term x v (substitute γ e))).
      admit.
      admit.
      replace (subst_term x v (substitute γ e)) with
         (substitute (<[x := v ]> γ) e) by admit.
      apply IHtyping_judgment.
      split; destruct H1.
      set_solver. intros.
      destruct (strings.string_eq_dec x x0);subst.
      admit.
      admit.
    + admit.
    + intros. admit.
    admit.
  - admit.
  - pose proof H2 as Hbool.
    pose proof H2 as He1.
    rename H2 into He2.
    apply IHtyping_judgment1 in Hbool.
    apply IHtyping_judgment2 in He1.
    apply IHtyping_judgment3 in He2.
    rewrite subst_ife.
    simpl in Hbool.
    destruct Hbool as (Hwt_bool & vb & Hvb & Hstepb).
    pose proof He1 as He1_wt.
    pose proof He2 as He2_wt.
    apply logrel_wt in He1_wt.
    apply logrel_wt in He2_wt.
    apply canonical_forms_bool in Hvb; auto.
    destruct Hvb; subst.
    + apply (backward_presevartion _
               (expr_if
                  expr_true
                  (substitute γ e1)
                  (substitute γ e2)
               ));auto.
      admit.
      apply (backward_presevartion _ (substitute γ e1));auto.
      econstructor;eauto;constructor.
    + apply (backward_presevartion _
               (expr_if
                  expr_false
                  (substitute γ e1)
                  (substitute γ e2)
               ));auto.
      admit.
      apply (backward_presevartion _ (substitute γ e2));auto.
      econstructor;eauto;constructor.
    + admit.
Admitted.
