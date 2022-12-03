Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
Require Import Autosubst.Autosubst.
From logical_relation Require Import relation.

Inductive ty : Type :=
| Ty_Var : var -> ty
| Ty_Unit : ty
| Ty_Pair : ty -> ty -> ty
| Ty_Arrow : ty -> ty -> ty
| Ty_Forall : {bind ty} -> ty.

Instance Ids_ty : Ids ty. derive. Defined.
Instance Rename_ty : Rename ty. derive. Defined.
Instance Subst_ty : Subst ty. derive. Defined.
Instance SubstLemmas_ty : SubstLemmas ty. derive. Qed.

Inductive expr : Type :=
| expr_var : var -> expr
| expr_unit : expr
| expr_pair : expr -> expr -> expr
| expr_fst : expr -> expr
| expr_snd : expr -> expr
| expr_app : expr -> expr -> expr
| expr_lam : {bind expr} -> expr
| expr_tapp : expr -> expr
| expr_tlam : expr -> expr.
Inductive val :=
| val_unit : val
| val_pair : val -> val -> val
| val_lam : {bind expr} -> val
| val_tlam : expr -> val.

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Fixpoint of_val (v : val) : expr :=
  match v with
  | val_unit => expr_unit
  | val_pair v1 v2 => expr_pair (of_val v1) (of_val v2)
  | val_lam e => expr_lam e
  | val_tlam e => expr_tlam e
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | expr_unit => Some val_unit
  | expr_lam e => Some (val_lam e)
  | expr_tlam e => Some (val_tlam e)
  | expr_pair e1 e2 =>
      match (to_val e1) with
      | None => None
      | Some v1 =>
          match (to_val e2) with
          | None => None
          | Some v2 => Some (val_pair v1 v2)
          end
      end
  | _ => None
  end.

Inductive is_val : expr -> Prop :=
| v_unit : is_val expr_unit
| v_pair : forall e1 e2, is_val e1 -> is_val e2 -> is_val (expr_pair e1 e2)
| v_lam : forall e, is_val (expr_lam e)
| v_tlam : forall e, is_val (expr_tlam e).

Hint Constructors is_val : core.

(** Equality  *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e ev : to_val e = Some ev → of_val ev = e.
Proof.
  revert ev; induction e; intros ev ?; simplify_option_eq; auto with f_equal.
  destruct (to_val e1); simpl;[|  discriminate].
  destruct (to_val e2); simpl;[|  discriminate].
  simplify_option_eq; auto with f_equal.
Qed.

Lemma is_val_of_val: forall v, is_val (of_val v).
Proof.
  intros.
  induction v; simpl.
  apply v_unit.
  apply v_pair; done.
  apply v_lam.
  apply v_tlam.
Qed.


Declare Custom Entry sf.
Notation "<{ e }>" := e (e custom sf at level 99).
Notation "x" := x (in custom sf at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom sf at level 50, right associativity).
Notation "S × T" := (Ty_Pair S T) (in custom sf at level 50, right associativity).
Notation "'()'" := Ty_Unit (in custom sf at level 0).
Notation "∀ '_' , T" := (Ty_Forall T) (in custom sf at level 50).
Coercion expr_var : var >-> expr.
Notation "'tt'" := expr_unit (in custom sf at level 0).
Notation "'⟨' e1 ',' e2 '⟩'" := (expr_pair e1 e2) (in custom sf at level 90,
                                      e1 at level 99,
                                      e2 at level 99).
Notation "'fst' e" := (expr_fst e) (in custom sf at level 2).
Notation "'snd' e" := (expr_snd e) (in custom sf at level 2).
Notation "e1 e2" := (expr_app e1 e2) (in custom sf at level 1, left associativity).
Notation "'λ' '_' ',' y" :=
  (expr_lam y) (in custom sf at level 90,
        y custom sf at level 99,
        left associativity).
Notation "e1 '_'" := (expr_tapp e1) (in custom sf at level 1, left associativity).
Notation "'Λ' e" :=
  (expr_tlam e) (in custom sf at level 90,
        e custom sf at level 99,
        left associativity).


(* Use gmap ? My own partial map ? list ? *)
Definition context := gmap var ty.
(* Definition tcontext := gset var. *)

(* Inductive appears_free_in (x : var) : expr → Prop := *)
(* | afi_var : appears_free_in x (EVar x) *)
(* | afi_pair1 : ∀ e1 e2, *)
(*   appears_free_in x e1 → *)
(*   appears_free_in x (EPair e1 e2) *)
(* | afi_pair2 : ∀ e1 e2, *)
(*   appears_free_in x e2 → *)
(*   appears_free_in x (EPair e1 e2) *)
(* | afi_app1 : ∀ e1 e2, *)
(*   appears_free_in x e1 → *)
(*   appears_free_in x (EApp e1 e2) *)
(* | afi_app2 : ∀ e1 e2, *)
(*   appears_free_in x e2 → *)
(*   appears_free_in x (EApp e1 e2) *)
(* | afi_abs : ∀ y e1, *)
(*   y ≠ x → *)
(*   appears_free_in x e1 → *)
(*   appears_free_in x (EAbs y e1). *)
(*   <{ λ y, t1}>. *)

Reserved Notation "Δ '⊢' t '∈' T"
  (at level 101, t custom sf, T custom sf at level 0).

Require Import List.
Definition tcontext := list ty.
Inductive typing_judgment : tcontext -> expr -> ty -> Prop :=
| T_Unit: forall Δ, Δ ⊢ tt ∈ ()
| T_Var: forall Δ x, x < length Δ -> Δ ⊢ (expr_var x) ∈ (nth x Δ (ids 0))
| T_Prod: forall Δ e1 τ1 e2 τ2,
  Δ ⊢ e1 ∈ τ1 ->
    Δ ⊢ e2 ∈ τ2 ->
      Δ ⊢ ⟨e1, e2⟩ ∈ <{ τ1 × τ2 }>
| T_Fst: forall Δ e τ1 τ2,
  Δ ⊢ e ∈ <{ τ1 × τ2 }> ->
    Δ ⊢ fst e ∈ τ1
| T_Snd: forall Δ e τ1 τ2,
  Δ ⊢ e ∈ <{ τ1 × τ2 }> ->
    Δ ⊢ snd e ∈ τ2
| T_Lam: forall Δ e τ1 τ2,
  (τ1 :: Δ) ⊢ e ∈ τ2 ->
    Δ ⊢ (expr_lam e) ∈ <{ τ1 -> τ2 }>
| T_App: forall Δ f e τ1 τ2,
  Δ ⊢ f ∈ <{ τ1 -> τ2 }> ->
    Δ ⊢ e ∈ τ1 ->
      Δ ⊢ f e ∈ τ2
| T_TLam: forall Δ e τ,
  Δ..[ren (+1)] ⊢ e ∈ τ ->
          Δ ⊢ Λ e ∈ <{ ∀ _ , τ }>
| T_TApp: forall Δ e τ τ',
  Δ ⊢ e ∈ <{ ∀ _ , τ }> ->
  typing_judgment Δ (expr_tapp e) τ.[τ'/]
where "Δ '⊢' e '∈' τ" := (typing_judgment Δ e τ).

Notation "( x )" := x (in custom sf, x at level 99).

Lemma is_val_inversion : forall e, is_val e -> exists v, e = (of_val v).
Proof.
  intros.
  induction e;inversion H
  ;[ exists val_unit | | eexists (val_lam _ )
     | eexists (val_tlam _) ]; eauto.
  apply IHe1 in H2; apply IHe2 in H3.
  destruct H2; destruct H3; subst.
  exists (val_pair x x0); eauto.
Qed.
