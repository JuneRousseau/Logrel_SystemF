Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import relation.

Inductive ty : Type :=
| Ty_Bool : ty
| Ty_Arrow : ty -> ty -> ty.

Inductive expr : Type :=
| expr_var : string -> expr
| expr_true : expr
| expr_false : expr
| expr_if : expr -> expr -> expr -> expr
| expr_app : expr -> expr -> expr
| expr_abs : string -> expr -> expr.
Inductive val :=
| val_true : val
| val_false : val
| val_abs : string -> expr -> val.

Definition of_val (v : val) : expr :=
  match v with
  | val_true => expr_true
  | val_false => expr_false
  | val_abs s e => expr_abs s e
  end.

Definition to_val (e : expr) : option val :=
  match e with
  | expr_true => Some val_true
  | expr_false => Some val_false
  | expr_abs s e => Some (val_abs s e)
  | _ => None
  end.

Inductive is_val : expr -> Prop :=
| v_true : is_val expr_true
| v_false : is_val expr_false
| v_abs : forall x t1, is_val (expr_abs x t1).

Hint Constructors is_val : core.


(** Equality  *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

Lemma is_val_of_val: forall v, is_val (of_val v).
Proof.
  intros.
  induction v; simpl; auto.
Qed.


Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "'Bool'" := Ty_Bool (in custom stlc at level 50, right associativity).
Coercion expr_var : string >-> expr.
Notation "'true'" := expr_true (in custom stlc at level 0).
Notation "'false'" := expr_false (in custom stlc at level 0).
Notation "e1 e2" := (expr_app e1 e2) (in custom stlc at level 1, left associativity).
Notation "'λ' x ',' y" :=
  (expr_abs x y) (in custom stlc at level 90, x at level 99,
        y custom stlc at level 99,
        left associativity).
Notation "'if' x 'then' y 'else' z" :=
  (expr_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Fixpoint subst_term (x : string) (s : expr) (t : expr) : expr :=
  match t with
  | expr_var y =>
      if String.eqb x y then s else t
  | <{ true }> =>  <{ true }>
  | <{ false }> =>  <{ false }>
  | <{ if e then e1 else e2 }> =>
      <{ if (subst_term x s e) then (subst_term x s e1) else (subst_term x s e2) }>
  | <{ t1 t2 }> =>
      <{ (subst_term x s t1) (subst_term x s t2) }>
  | <{ λ y, t1 }> =>
      if String.eqb x y then t else <{ λ y, (subst_term x s t1) }>
  end.

Notation "'[' x '/' s ']' t" := (subst_term x s t) (in custom stlc at level 20).

Definition context := gmap string ty.

(* TODO notation / definition for the empty context and tcontext *)

Reserved Notation " Γ '⊢' t '∈' T"
  (at level 101, t custom stlc, T custom stlc at level 0).

Inductive appears_free_in (x : string) : expr → Prop :=
| afi_var : appears_free_in x <{x}>
| afi_if_cond : ∀ e e1 e2,
  appears_free_in x e →
  appears_free_in x <{ if e then e1 else e2 }>
| afi_if1 : ∀ e e1 e2,
  appears_free_in x e1 →
  appears_free_in x <{ if e then e1 else e2 }>
| afi_if2 : ∀ e e1 e2,
  appears_free_in x e2 →
  appears_free_in x <{ if e then e1 else e2 }>
| afi_app1 : ∀ t1 t2,
  appears_free_in x t1 →
  appears_free_in x <{t1 t2}>
| afi_app2 : ∀ t1 t2,
  appears_free_in x t2 →
  appears_free_in x <{t1 t2}>
| afi_abs : ∀ y t1,
  y ≠ x →
  appears_free_in x t1 →
  appears_free_in x <{ λ y, t1}>.

Inductive typing_judgment : context -> expr -> ty -> Prop :=
| T_True: forall Γ, Γ ⊢ true ∈ Bool
| T_False: forall Γ, Γ ⊢ false ∈ Bool
| T_Var: forall Γ τ (x : string), Γ !! x = Some τ -> Γ ⊢ x ∈ τ
| T_Lam: forall Γ x e τ1 τ2,
  x ∉ dom Γ ->
  (<[x:=τ1]> Γ) ⊢ e ∈ τ2 ->
    Γ ⊢ <{ λ x , e }> ∈ <{ τ1 -> τ2 }>
| T_App: forall Γ e e' τ1 τ2,
  Γ ⊢ e ∈ <{ τ1 -> τ2 }> ->
    Γ ⊢ e' ∈ τ1 ->
      Γ ⊢ e e' ∈ τ2
| T_If: forall Γ e e1 e2 τ,
    Γ ⊢ e ∈ <{ Bool }> ->
    Γ ⊢ e1 ∈ τ ->
    Γ ⊢ e2 ∈ τ ->
      Γ ⊢ <{ if e then e1 else e2 }> ∈ τ
where "Γ '⊢' t '∈' T" := (typing_judgment Γ t T).
Hint Constructors typing_judgment : core.

Notation "( x )" := x (in custom stlc, x at level 99).

Lemma canonical_forms_bool : ∀ e,
  ∅ ⊢ e ∈ Bool →
  is_val e →
  (e = <{true}>) ∨ (e = <{false}>).
Proof.
  intros.
  destruct H0;auto. inversion H.
Qed.

 Lemma canonical_forms_fun : ∀ t T1 T2,
  ∅ ⊢ t ∈ <{  (T1 -> T2) }> →
  is_val t →
  ∃ x u, t = <{ λ x, u }>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| |] ; inversion HT; subst.
  exists x0, t1. reflexivity.
Qed.
