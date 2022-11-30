Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import relation.

Inductive ty : Type :=
| Ty_Var : string -> ty
| Ty_Unit : ty
| Ty_Pair : ty -> ty -> ty
| Ty_Arrow : ty -> ty -> ty
| Ty_Forall : string -> ty -> ty.

Inductive expr : Type :=
| expr_var : string -> expr
| expr_unit : expr
| expr_pair : expr -> expr -> expr
| expr_fst : expr -> expr
| expr_snd : expr -> expr
| expr_app : expr -> expr -> expr
| expr_abs : string -> expr -> expr
| expr_tapp : expr -> expr
| expr_tabs : expr -> expr.
Inductive val :=
| val_unit : val
| val_pair : val -> val -> val
| val_abs : string -> expr -> val
| val_tabs : expr -> val
.

Fixpoint of_val (v : val) : expr :=
  match v with
  | val_unit => expr_unit
  | val_pair v1 v2 => expr_pair (of_val v1) (of_val v2)
  | val_abs s e => expr_abs s e
  | val_tabs e => expr_tabs e
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | expr_unit => Some val_unit
  | expr_abs s e => Some (val_abs s e)
  | expr_tabs e => Some (val_tabs e)
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
| v_pair : forall v1 v2, is_val v1 -> is_val v2 -> is_val (expr_pair v1 v2)
| v_abs : forall x t1, is_val (expr_abs x t1)
| v_tabs : forall t1, is_val (expr_tabs t1).

Hint Constructors is_val : core.


(** Equality  *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
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
  apply v_abs.
  apply v_tabs.
Qed.


Declare Custom Entry sf.
Notation "<{ e }>" := e (e custom sf at level 99).
Notation "x" := x (in custom sf at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom sf at level 50, right associativity).
Notation "S × T" := (Ty_Pair S T) (in custom sf at level 50, right associativity).
Notation "'()'" := Ty_Unit (in custom sf at level 0).
Notation "∀ α , T" := (Ty_Forall α T) (in custom sf at level 50).
Coercion expr_var : string >-> expr.
Notation "'tt'" := expr_unit (in custom sf at level 0).
Notation "'⟨' e1 ',' e2 '⟩'" := (expr_pair e1 e2) (in custom sf at level 90,
                                      e1 at level 99,
                                      e2 at level 99).
Notation "'fst' e" := (expr_fst e) (in custom sf at level 2).
Notation "'snd' e" := (expr_snd e) (in custom sf at level 2).
Notation "e1 e2" := (expr_app e1 e2) (in custom sf at level 1, left associativity).
Notation "'λ' x ',' y" :=
  (expr_abs x y) (in custom sf at level 90, x at level 99,
        y custom sf at level 99,
        left associativity).
Notation "e1 '_'" := (expr_tapp e1) (in custom sf at level 1, left associativity).
Notation "'Λ' e" :=
  (expr_tabs e) (in custom sf at level 90,
        e custom sf at level 99,
        left associativity).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition α : string := "α".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold α : core.

Fixpoint subst_term (x : string) (s : expr) (t : expr) : expr :=
  match t with
  | expr_var y =>
      if String.eqb x y then s else t
  | <{ tt }> =>  <{ tt }>
  | <{ ⟨t1, t2⟩ }> =>
      <{ ⟨ (subst_term x s t1) , (subst_term x s t2) ⟩ }>
  | <{fst t1}> => <{fst (subst_term x s t1)}>
  | <{snd t1}> => <{snd (subst_term x s t1)}>
  | <{ t1 t2 }> =>
      <{ (subst_term x s t1) (subst_term x s t2) }>
  | <{ λ y, t1 }> =>
      if String.eqb x y then t else <{ λ y, (subst_term x s t1) }>
  | <{ t1 _ }> => <{ (subst_term x s t1) _ }>
  | <{ Λ t1 }> => <{ Λ (subst_term x s t1) }>
  end.

Notation "'[' x '/' s ']' t" := (subst_term x s t) (in custom sf at level 20).

Fixpoint subst_type (α : string) (s : ty) (t : ty) : ty :=
  match t with
  | Ty_Var β => if String.eqb α β then s else t
  | Ty_Unit => Ty_Unit
  | <{ τ1 × τ2 }> => <{ (subst_type α s τ1) × (subst_type α s τ2) }>
  | <{ τ1 -> τ2 }> => <{ (subst_type α s τ1) -> (subst_type α s τ2) }>
  | <{ ∀ β , τ1  }> => if String.eqb α β then t else <{ ∀ β , (subst_type α s τ1) }>
  end.
Notation "'[' α ':=' s ']' t" := (subst_type α s t) (in custom sf at level 20).

(* TODO simultaneous substitution ?? better way ?*)
Fixpoint replace_var xs vs y t : expr :=
  match xs,vs with
  | nil, _ => t
  | x::xs', nil => t
  | x::xs', v::vs' =>
      if String.eqb x y
      then v
      else replace_var xs' vs' y t
  end.

Fixpoint subst_term_seq (xs : list string) (vs : list expr) (t : expr) : expr :=
  match t with
  | expr_var y => replace_var xs vs y t
  | <{ tt }> =>  <{ tt }>
  | <{ ⟨t1, t2⟩ }> =>
      <{ ⟨ (subst_term_seq xs vs t1) , (subst_term_seq xs vs t2) ⟩ }>
  | <{fst t1}> => <{fst (subst_term_seq xs vs t1)}>
  | <{snd t1}> => <{snd (subst_term_seq xs vs t1)}>
  | <{ t1 t2 }> =>
      <{ (subst_term_seq xs vs t1) (subst_term_seq xs vs t2) }>
  | <{ λ y, t1 }> =>
      match List.find (String.eqb y) xs with
      | None => <{ λ y, (subst_term_seq xs vs t1) }>
      | Some x => t
      end
  | <{ t1 _ }> => <{ (subst_term_seq xs vs t1) _ }>
  | <{ Λ t1 }> => <{ Λ (subst_term_seq xs vs t1) }>
  end.

(* autosubbst check iris lr *)

(* Use gmap ? My own partial map ? list ? *)
Definition context := gmap string ty.
Definition tcontext := list string.

(* TODO notation / definition for the empty context and tcontext *)

Reserved Notation "Δ ';' Γ '⊢' t '∈' T"
  (at level 101, t custom sf, T custom sf at level 0).

Inductive appears_free_in (x : string) : expr → Prop :=
| afi_var : appears_free_in x <{x}>
| afi_pair1 : ∀ t1 t2,
  appears_free_in x t1 →
  appears_free_in x <{ ⟨t1, t2⟩ }>
| afi_pair2 : ∀ t1 t2,
  appears_free_in x t2 →
  appears_free_in x <{ ⟨t1, t2⟩ }>
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

Inductive free (α : string) : ty -> Prop :=
| free_var : free α (Ty_Var α)
| free_pair1 : forall τ1 τ2, free α τ1 -> free α <{ τ1 × τ2 }>
| free_pair2 : forall τ1 τ2, free α τ2 -> free α <{ τ1 × τ2 }>
| free_arrow1 : forall τ1 τ2, free α τ1 -> free α <{ τ1 -> τ2 }>
| free_arrow2 : forall τ1 τ2, free α τ2  -> free α <{ τ1 -> τ2 }>
| free_forall : forall τ β, α ≠ β -> free α τ -> free α <{ ∀ β, τ }>.

Definition not_free α (Γ : context) (t : string * ty) : Prop :=
  let (k,_) := t in
  match (Γ !! k) with
  | None => True
  | Some τ => not (free α τ)
  end.

(* TODO better way than using gmap_to_list ? *)
Definition not_free_context (α : string) (Γ : context) :=
forall x y, Γ !! x = Some y -> not (free α y).

Inductive typing_judgment : tcontext -> context -> expr -> ty -> Prop :=
| T_Unit: forall Δ Γ, Δ;Γ ⊢ tt ∈ ()
| T_Var: forall Δ Γ τ (x : string), Γ !! x = Some τ -> Δ;Γ ⊢ x ∈ τ
| T_Prod: forall Δ Γ e1 τ1 e2 τ2,
  Δ;Γ ⊢ e1 ∈ τ1 ->
    Δ;Γ ⊢ e2 ∈ τ2 ->
      Δ;Γ ⊢ ⟨e1, e2⟩ ∈ <{ τ1 × τ2 }>
| T_Fst: forall Δ Γ e τ1 τ2,
  Δ;Γ ⊢ e ∈ <{ τ1 × τ2 }> ->
    Δ;Γ ⊢ fst e ∈ τ1
| T_Snd: forall Δ Γ e τ1 τ2,
  Δ;Γ ⊢ e ∈ <{ τ1 × τ2 }> ->
    Δ;Γ ⊢ snd e ∈ τ2
| T_Lam: forall Δ Γ x e τ1 τ2,
  Δ;(<[x:=τ1]> Γ) ⊢ e ∈ τ2 ->
    Δ;Γ ⊢ <{ λ x , e }> ∈ <{ τ1 -> τ2 }>
| T_App: forall Δ Γ e e' τ1 τ2,
  Δ;Γ ⊢ e ∈ <{ τ1 -> τ2 }> ->
    Δ;Γ ⊢ e' ∈ τ1 ->
      Δ;Γ ⊢ e e' ∈ τ2
| T_TLam: forall Δ Γ e α τ,
  (α :: Δ);Γ ⊢ e ∈ τ ->
          not_free_context α Γ ->
          Δ;Γ ⊢ Λ e ∈ <{ ∀ α , τ }>
| T_TApp: forall Δ Γ e α τ1 τ2,
  Δ;Γ ⊢ e ∈ <{ ∀ α , τ1 }> ->
    Δ;Γ ⊢ e _ ∈ <{ [ α := τ1 ] τ2 }>
where "Δ ; Γ '⊢' t '∈' T" := (typing_judgment Δ Γ t T).

Notation "( x )" := x (in custom sf, x at level 99).

Lemma is_val_inversion : forall e, is_val e -> exists v, e = (of_val v).
Proof.
  intros.
  induction e;inversion H
  ;[ exists val_unit | | eexists (val_abs _ _)
     | eexists (val_tabs _) ]; eauto.
  apply IHe1 in H2; apply IHe2 in H3.
  destruct H2; destruct H3; subst.
  exists (val_pair x0 x1); eauto.
Qed.
