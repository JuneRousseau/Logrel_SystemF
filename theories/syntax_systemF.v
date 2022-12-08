Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From stdpp Require Import list.
Require Import Autosubst.Autosubst.

(*** Syntax of SystemF *)

Inductive ty : Type :=
| Ty_Var : var -> ty
| Ty_Unit : ty
| Ty_Pair : ty -> ty -> ty
| Ty_Arrow : ty -> ty -> ty
| Ty_Forall : {bind ty} -> ty.

#[export] Instance Ids_ty : Ids ty. derive. Defined.
#[export] Instance Rename_ty : Rename ty. derive. Defined.
#[export] Instance Subst_ty : Subst ty. derive. Defined.
#[export] Instance SubstLemmas_ty : SubstLemmas ty. derive. Qed.

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

#[export] Instance Ids_expr : Ids expr. derive. Defined.
#[export] Instance Rename_expr : Rename expr. derive. Defined.
#[export] Instance Subst_expr : Subst expr. derive. Defined.
#[export] Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

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

(** Lemmas about value *)
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
  induction v; simpl; by constructor.
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

Declare Custom Entry sf.
Declare Custom Entry ty.
Notation "<{ e }>" := e (e custom sf at level 99).
Notation "<{{ e }}>" := e (e custom ty at level 99).
Notation "( x )" := x (in custom sf, x at level 99).
Notation "( x )" := x (in custom ty, x at level 99).
Notation "x" := x (in custom sf at level 0, x constr at level 0).
Notation "x" := x (in custom ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom ty at level 50, right associativity).
Notation "S × T" := (Ty_Pair S T) (in custom ty at level 50, right associativity).
Notation "'()'" := Ty_Unit (in custom ty at level 0).
Notation "∀ '_' , T" := (Ty_Forall T) (in custom ty at level 50).
Notation "'$' n" := (Ty_Var n) (in custom ty at level 50).

Notation "'tt'" := expr_unit (in custom sf at level 0).
Notation "'#' n" := (expr_var n) (in custom sf at level 50).
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

Definition get {T} (Γ : list T) (n : var) : option T := nth_error Γ n.

Lemma get_app_l {T} (Γ Γ' : list T) n : n < length Γ -> get (Γ++Γ') n = get Γ n.
Proof. apply nth_error_app1. Qed.

Lemma get_app_r {T} (Γ Γ' : list T) n
  : length Γ <= n  -> get (Γ++Γ') n = get Γ' (n - length Γ).
Proof. apply nth_error_app2. Qed.

Lemma get_nil {T} : forall n, get ([] : list T) n = None.
Proof. intros; induction n ; auto. Qed.

(** The typing context Γ is an ordered list of type,
    where the n-th element is the type of <{ n }> *)
Definition typing_context := list ty.
Implicit Types Γ : typing_context.

Reserved Notation "Γ '⊢' e '∈' τ"
  (at level 101, e custom sf, τ custom ty at level 0).
(** There is no context of type variable Δ, because they are managed
    by (ty_var n) where n is an autosubst variable. *)
Inductive typing_judgment : typing_context -> expr -> ty -> Prop :=
| T_Unit: forall Γ , Γ ⊢ tt ∈ ()
(* A variable is well-typed if it exists a type in the typing context Γ *)
| T_Var: forall Γ x τ, (get Γ x) = Some τ -> Γ ⊢ (# x) ∈ τ
| T_Prod: forall Γ e1 τ1 e2 τ2,
  Γ ⊢ e1 ∈ τ1
  -> Γ ⊢ e2 ∈ τ2
  -> Γ ⊢ ⟨e1, e2⟩ ∈ (τ1 × τ2)
| T_Fst: forall Γ e τ1 τ2,
  Γ ⊢ e ∈ (τ1 × τ2)
  -> Γ ⊢ fst e ∈ τ1
| T_Snd: forall Γ e τ1 τ2,
  Γ ⊢ e ∈ (τ1 × τ2)
  -> Γ ⊢ snd e ∈ τ2
(* A lambda abstraction (λx.e) is well-typed if, by adding the type of the
   argument in the typing context, the expression e is well-typed.
   The binding is managed by the order in the typing list.
   Indeed, 'x' will be transformed to '0', and all occurences of (expr_var 0)
   will represents the binding to this 'x'. *)
| T_Lam: forall Γ e τ1 τ2,
  (τ1 :: Γ) ⊢ e ∈ τ2
  -> Γ ⊢ (λ _, e) ∈ (τ1 -> τ2)
| T_App: forall Γ f e τ1 τ2,
  Γ ⊢ f ∈ (τ1 -> τ2)
  -> Γ ⊢ e ∈ τ1
  -> Γ ⊢ f e ∈ τ2
(* A type-lambda abstraction {(Λ e) : ∀ α, τ} is well-typed if, by adding the
   type variable in the typing variable context, the term e is of type τ.
   With the de Bruijn indices, adding a new variable in the typing variable
   context means increment all the indices of the type variable by 1.
   Thus, in our typing context, we rename (ie. increment) all the type
   variable. *)
| T_TLam: forall Γ e τ,
  (map (rename (+1)) Γ) ⊢ e ∈ τ
  -> Γ ⊢ Λ e ∈ ( ∀ _ , τ )
| T_TApp: forall Γ e τ τ',
  Γ ⊢ e ∈ ( ∀ _ , τ )
  -> typing_judgment Γ (expr_tapp e) τ.[τ'/]
where "Γ '⊢' e '∈' τ" := (typing_judgment Γ e τ).

Lemma is_val_inversion : forall e, is_val e <-> exists v, e = (of_val v).
Proof.
  split;intros.
  - (* -> *)
    induction e;inversion H
    ;[ exists val_unit | | eexists (val_lam _ ) | eexists (val_tlam _) ]
    ; eauto.
    apply IHe1 in H2; apply IHe2 in H3.
    destruct H2; destruct H3; subst.
    exists (val_pair x x0); eauto.
  - (* <- *) destruct H as [? ->];apply is_val_of_val.
Qed.
