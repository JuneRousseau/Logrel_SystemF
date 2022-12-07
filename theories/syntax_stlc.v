Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
Require Import Autosubst.Autosubst.
From logical_relation Require Import relation.

Inductive ty : Type :=
(* | Ty_Unit : ty *)
| Ty_Bool : ty
(* | Ty_Pair : ty -> ty -> ty *)
| Ty_Arrow : ty -> ty -> ty.

Inductive expr : Type :=
(* | expr_unit : expr *)
| expr_true : expr
| expr_false : expr
| expr_var : var -> expr
| expr_ife : expr -> expr -> expr -> expr
(* | expr_pair : expr -> expr -> expr *)
(* | expr_fst : expr -> expr *)
(* | expr_snd : expr -> expr *)
| expr_app : expr -> expr -> expr
| expr_lam : {bind expr} -> expr.
Inductive val :=
(* | val_unit : val *)
| val_true : val
| val_false : val
(* | val_pair : val -> val -> val *)
| val_lam : {bind expr} -> val.

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Fixpoint of_val (v : val) : expr :=
  match v with
  (* | val_unit => expr_unit *)
  | val_true => expr_true
  | val_false => expr_false
  (* | val_pair v1 v2 => expr_pair (of_val v1) (of_val v2) *)
  | val_lam e => expr_lam e
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  (* | expr_unit => Some val_unit *)
  | expr_lam e => Some (val_lam e)
  | expr_true => Some (val_true)
  | expr_false => Some (val_false)
  (* | expr_pair e1 e2 => *)
  (*     match (to_val e1) with *)
  (*     | None => None *)
  (*     | Some v1 => *)
  (*         match (to_val e2) with *)
  (*         | None => None *)
  (*         | Some v2 => Some (val_pair v1 v2) *)
  (*         end *)
  (*     end *)
  | _ => None
  end.

Inductive is_val : expr -> Prop :=
(* | v_unit : is_val expr_unit *)
| v_true : is_val expr_true
| v_false : is_val expr_false
(* | v_pair : forall e1 e2, is_val e1 -> is_val e2 -> is_val (expr_pair e1 e2) *)
| v_lam : forall e, is_val (expr_lam e).

Hint Constructors is_val : core.

(** Equality  *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e ev : to_val e = Some ev → of_val ev = e.
Proof.
  revert ev; induction e; intros ev ?; simplify_option_eq; auto with f_equal.
  (* destruct (to_val e1); simpl;[|  discriminate]. *)
  (* destruct (to_val e2); simpl;[|  discriminate]. *)
  (* simplify_option_eq; auto with f_equal. *)
Qed.

Lemma is_val_of_val: forall v, is_val (of_val v).
Proof.
  intros.
  induction v; simpl;constructor.
Qed.


Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
(* Notation "'()'" := Ty_Unit (in custom stlc at level 0). *)
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
(* Notation "S × T" := (Ty_Pair S T) (in custom stlc at level 50, right associativity). *)
(* Coercion expr_var : var >-> expr. *)
Notation "'#' n" := (expr_var n) (in custom stlc at level 50).
(* Notation "'tt'" := expr_unit (in custom stlc at level 0). *)
Notation "'true'" := expr_true (in custom stlc at level 0).
Notation "'false'" := expr_false (in custom stlc at level 0).
(* Notation "'⟨' e1 ',' e2 '⟩'" := (expr_pair e1 e2) (in custom stlc at level 90, *)
(*                                       e1 at level 99, *)
(*                                       e2 at level 99). *)
(* Notation "'fst' e" := (expr_fst e) (in custom stlc at level 2). *)
(* Notation "'snd' e" := (expr_snd e) (in custom stlc at level 2). *)
Notation "'if' e 'then' e1 'else' e2" :=
  (expr_ife e e1 e2)
    (in custom stlc at level 90,
        e custom stlc at level 99,
        e1 custom stlc at level 99,
        e2 custom stlc at level 99,
        left associativity).
Notation "e1 e2" := (expr_app e1 e2) (in custom stlc at level 1, left associativity).
Notation "'λ' '_' ',' y" :=
  (expr_lam y) (in custom stlc at level 90,
        y custom stlc at level 99,
        left associativity).


(* Use gmap ? My own partial map ? list ? *)
Require Import List.
Definition get {T} (Gamma : list T) (n : var) : option T :=
  nth_error Gamma n.
Definition context := list ty.

(** The typing context Γ is an ordered list of type,
    where the nth element is the type of (expr_var n) *)
(** There is no context of type variable Δ because they are managed by
    (ty_var n) where n is an autosubst variable. *)

Reserved Notation "Γ '⊢' t '∈' T"
  (at level 101, t custom stlc, T custom stlc at level 0).
Inductive typing_judgment : context -> expr -> ty -> Prop :=
(* | T_Unit: forall Γ , Γ ⊢ tt ∈ () *)
| T_True : forall Γ, Γ ⊢ true ∈ Bool
| T_False : forall Γ, Γ ⊢ false ∈ Bool
| T_Ife : forall Γ b et ef τ,
  Γ ⊢ b ∈ Bool ->
  Γ ⊢ et ∈ τ ->
  Γ ⊢ ef ∈ τ ->
  Γ ⊢ if b then et else ef ∈ τ
(* A variable is well-typed if it exists a type in the typing context Γ *)
| T_Var: forall Γ x τ, (get Γ x) = Some τ -> Γ ⊢ #x ∈ τ
(* | T_Prod: forall Γ e1 τ1 e2 τ2, *)
(*   Γ ⊢ e1 ∈ τ1 *)
(*   -> Γ ⊢ e2 ∈ τ2 *)
(*   -> Γ ⊢ ⟨e1, e2⟩ ∈ <{ τ1 × τ2 }> *)
(* | T_Fst: forall Γ e τ1 τ2, *)
(*   Γ ⊢ e ∈ <{ τ1 × τ2 }> *)
(*   -> Γ ⊢ fst e ∈ τ1 *)
(* | T_Snd: forall Γ e τ1 τ2, *)
(*   Γ ⊢ e ∈ <{ τ1 × τ2 }> *)
(*   -> Γ ⊢ snd e ∈ τ2 *)
| T_Lam: forall Γ e τ1 τ2,
  (τ1 :: Γ) ⊢ e ∈ τ2
  -> Γ ⊢ (λ _, e) ∈ <{ τ1 -> τ2 }>
| T_App: forall Γ f e τ1 τ2,
  Γ ⊢ f ∈ <{ τ1 -> τ2 }>
  -> Γ ⊢ e ∈ τ1
  -> Γ ⊢ f e ∈ τ2
where "Γ '⊢' e '∈' τ" := (typing_judgment Γ e τ).


Lemma is_val_inversion : forall e, is_val e -> exists v, e = (of_val v).
Proof.
  intros.
  induction e;inversion H
  ;[(* exists val_unit | *)
       exists val_true
     | exists val_false
     | eexists (val_lam _ )]; eauto.
  (* apply IHe1 in H2; apply IHe2 in H3. *)
  (* destruct H2; destruct H3; subst. *)
  (* exists (val_pair x x0); eauto. *)
Qed.
