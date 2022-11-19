Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import syntax_systemF opsem_systemF.

Implicit Types Δ : tcontext.
Implicit Types Γ : context.
Implicit Types τ : ty.

Definition substitution := gmap string (expr -> Prop).
Implicit Types ξ : substitution.

(** Logical relation and free theorems --- new files *)
Definition safe_parametrized (P : expr -> Prop) (e : expr) :=
  forall e', e ~>* e' ->
        (is_val e' /\ P e') \/ (exists e'', e' ~> e'').

Lemma safe_mono (P Q : expr -> Prop) e:
  (forall e, is_val e -> P e -> Q e)
  -> safe_parametrized P e
  -> safe_parametrized Q e.
Proof.
  unfold safe_parametrized.
  intros mono_val safe_P e' step.
  apply safe_P in step; destruct step as [ [val_e' Pe'] | Hstep ]
  ;[left;split|] ;auto.
  Qed.

Lemma safe_val (P : expr -> Prop) e:
  is_val e -> P e -> safe_parametrized P e.
Proof.
  unfold safe_parametrized.
  intros e_val P_e e' step.
  apply is_val_step in step;subst;auto.
Qed.

Lemma safe_step (P : expr -> Prop) e e' :
  e ~> e' ->
  safe_parametrized P e' ->
  safe_parametrized P e.
Proof.
  unfold safe_parametrized.
  intros step safe_e' e'' step'.
  assert (step'': e' ~>* e'').
  apply step_deterministic_multiple with (e'' := e'') in step; auto.
  apply safe_e' in step''; destruct step'' as [ [val_e'' Pe''] | Hstep ]; auto.
Qed.


Fixpoint safe_lr (Δ : tcontext) (ξ : substitution) (τ : ty) (v : expr) :=
  is_val v /\
 match τ with
 | Ty_Var α => match (ξ !! α) with | None => False | Some P => P v end
 | Ty_Unit => v = <{ tt }>
 | Ty_Pair t1 t2 =>
     exists e1 e2, is_val e1
              /\ is_val e2
              /\ v = <{ ⟨ e1, e2 ⟩ }>
              /\ safe_lr Δ ξ t1 e1
              /\ safe_lr Δ ξ t2 e2
 | Ty_Arrow t1 t2 =>
     exists x e, v = <{ λ x, e }>
            /\ (forall v', safe_lr Δ ξ t1 v' -> safe_parametrized (safe_lr Δ ξ t2) ( <{[ x / v] e}>))
 | Ty_Forall α t =>
     exists e, v = <{ Λ e }>
            /\ forall (P: expr -> Prop), safe_parametrized (safe_lr (α::Δ) (<[α := P]> ξ) t) e
 (* | Ty_Forall α t => *)
 (*     exists e, v = <{ Λ e }> *)
 (*                /\ ∀ t', safe_parametrized (safe_lr Δ ξ (subst_type α t' t)) e *)
 end.

Lemma safe_is_val Δ ξ v τ : safe_lr Δ ξ τ v -> is_val v.
Proof.
  induction τ; simpl ; intros; destruct H;auto.
Qed.

Lemma logrel_subst Δ ξ τ τ' v α :
  (safe_lr Δ ξ (subst_type α τ' τ) v)
  <-> (safe_lr (α::Δ) (<[α := safe_lr Δ ξ τ']> ξ) τ v).
Proof.
  split; intros Hsafe.
  generalize dependent τ'.
  generalize dependent v.
  generalize dependent ξ.
  generalize dependent Δ.
  induction τ; intros * Hsafe; simpl in *; auto.
  - admit.
  - (* pair *)
    destruct Hsafe as (Hval & v1 & v2 & Hval1 & Hval2 & -> & Hsafe1 & Hsafe2).
    split;auto.
    exists v1, v2.
    repeat(split;auto).
  - (* lambda *)
    destruct Hsafe as (Hval & x & e & -> & Hsafe).
    split;auto.
    exists x, e.
    split;auto.
    intros.
    admit.
  - (* poly *)
    destruct (α =? s)%string eqn:Heq ; simpl in Hsafe
    ;destruct Hsafe as (Hval & e & Hv & Hsafe); split;auto; exists e
    ; split; auto
    ; intros;
    specialize (Hsafe P).
    (* I need to be able to swap α and s *)
    admit.
Admitted.

Lemma logrel_weaken Δ ξ τ v α P :
  free α τ ->
  ((safe_lr Δ ξ τ v) <->
  (safe_lr Δ  (<[α := P]> ξ) τ v)).
Proof.

  split; intros Hsafe;
  generalize dependent v;
  induction τ; intros; simpl in *;
  destruct Hsafe; split; auto.
  - admit.
  - destruct H1 as (v1 & v2 & Hv1 & Hv2 & Hv& Hsafe1 & Hsafe2).
    exists v1, v2.
    repeat(split;auto); inversion H; subst.
    apply IHτ1;auto.
    apply IHτ2;auto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

(* TODO *)
Fixpoint logrel_seq Δ Γ ξ (vs : list expr) := True.

Definition context_var Γ : list string :=
  map (fun x => match x with (x1,x2) => x1 end) (gmap_to_list Γ).

Theorem fundamental_theorem Δ Γ τ e :
  Δ;Γ ⊢ e ∈ τ -> (forall ξ vs, logrel_seq Δ Γ ξ vs
                         -> safe_lr Δ ξ τ (subst_term_seq (context_var Γ) vs e)).
Proof.
  induction 1; intros; simpl in *.
  - (* T_Unit *)
    split ; auto.
  - (* T_Var *)
    admit.
  - (* T_Prod *)
    admit.
  - (* T_Fst *)
    admit.
  - (* T_Snd *)
    admit.
  - (* T_Lam *)
    admit.
  - (* T_App *)
    admit.
  - (* T_TLam *)
    admit.
  - (* T_TApp *)
    admit.
Admitted.
