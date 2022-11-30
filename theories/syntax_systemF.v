Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
Require Import Autosubst.Autosubst.
From logical_relation Require Import relation.

Inductive ty : Type :=
| TUnit : ty
| TVar : var -> ty
| TPair : ty -> ty -> ty
| TArrow : ty -> ty -> ty
| TForall : {bind ty} -> ty.

Instance Ids_ty : Ids ty. derive. Defined.
Instance Rename_ty : Rename ty. derive. Defined.
Instance Subst_ty : Subst ty. derive. Defined.
Instance SubstLemmas_ty : SubstLemmas ty. derive. Qed.

Inductive expr : Type :=
| EUnit : expr
| EVar : var -> expr
| EPair : expr -> expr -> expr
| EFst : expr -> expr
| ESnd : expr -> expr
| EApp : expr -> expr -> expr
| EAbs : {bind expr} -> expr
| ETApp : expr -> expr
| ETAbs : expr -> expr.
Inductive val :=
| VUnit : val
| VPair : val -> val -> val
| VAbs : {bind expr} -> val
| VTAbs : expr -> val
.

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Fixpoint of_val (v : val) : expr :=
  match v with
  | VUnit => EUnit
  | VPair v1 v2 => EPair (of_val v1) (of_val v2)
  | VAbs s => EAbs s
  | VTAbs e => ETAbs e
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | EUnit => Some VUnit
  | EAbs s => Some (VAbs s)
  | ETAbs e => Some (VTAbs e)
  | EPair e1 e2 =>
      match (to_val e1) with
      | None => None
      | Some v1 =>
          match (to_val e2) with
          | None => None
          | Some v2 => Some (VPair v1 v2)
          end
      end
  | _ => None
  end.

Inductive is_val : expr -> Prop :=
| is_val_unit : is_val EUnit
| is_val_pair : forall v1 v2, is_val v1 -> is_val v2 -> is_val (EPair v1 v2)
| is_val_abs : forall t1, is_val (EAbs t1)
| is_val_tabs : forall t1, is_val (ETAbs t1).

Hint Constructors is_val : core.


(** Equality  *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v' ?; simplify_option_eq; auto with f_equal.
  destruct (to_val e1); simpl;[|  discriminate].
  destruct (to_val e2); simpl;[|  discriminate].
  simplify_option_eq; auto with f_equal.
Qed.

Lemma is_val_of_val: forall v, is_val (of_val v).
Proof.
  intros.
  induction v; simpl.
  apply is_val_unit.
  apply is_val_pair; done.
  apply is_val_abs.
  apply is_val_tabs.
Qed.

(* Use gmap ? My own partial map ? list ? *)
Definition context := gmap var ty.
Definition tcontext := list var.

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

(* Inductive free (α : string) : ty -> Prop := *)
(* | free_var : free α (Ty_Var α) *)
(* | free_pair1 : forall τ1 τ2, free α τ1 -> free α <{ τ1 × τ2 }> *)
(* | free_pair2 : forall τ1 τ2, free α τ2 -> free α <{ τ1 × τ2 }> *)
(* | free_arrow1 : forall τ1 τ2, free α τ1 -> free α <{ τ1 -> τ2 }> *)
(* | free_arrow2 : forall τ1 τ2, free α τ2  -> free α <{ τ1 -> τ2 }> *)
(* | free_forall : forall τ β, α ≠ β -> free α τ -> free α <{ ∀ β, τ }>. *)

(* Definition not_free α (Γ : context) (t : string * ty) : Prop := *)
(*   let (k,_) := t in *)
(*   match (Γ !! k) with *)
(*   | None => True *)
(*   | Some τ => not (free α τ) *)
(*   end. *)

(* (* TODO better way than using gmap_to_list ? *) *)
(* Definition not_free_context (α : string) (Γ : context) := *)
(* forall x y, Γ !! x = Some y -> not (free α y). *)

Inductive typing_judgment : tcontext -> context -> expr -> ty -> Prop :=
| T_Unit: forall Δ Γ,
  typing_judgment Δ Γ EUnit TUnit
| T_Var: forall Δ Γ τ (x : var),
  Γ !! x = Some τ ->
  typing_judgment Δ Γ (EVar x) τ
| T_Prod: forall Δ Γ e1 τ1 e2 τ2,
  typing_judgment Δ Γ e1 τ1 ->
  typing_judgment Δ Γ e2 τ2 ->
  typing_judgment Δ Γ (EPair e1 e2) (TPair τ1 τ2)
| T_Fst: forall Δ Γ e τ1 τ2,
  typing_judgment Δ Γ e (TPair τ1 τ2) ->
  typing_judgment Δ Γ (EFst e) τ1
| T_Snd: forall Δ Γ e τ1 τ2,
  typing_judgment Δ Γ e (TPair τ1 τ2) ->
  typing_judgment Δ Γ (ESnd e) τ2
| T_Lam: forall Δ Γ (x :var) e τ1 τ2,
  typing_judgment Δ (<[x:=τ1]> Γ) e τ2 ->
  typing_judgment Δ Γ (EAbs e) (TArrow τ1 τ2)
| T_App: forall Δ Γ e e' τ1 τ2,
  typing_judgment Δ Γ e (TArrow τ1 τ2) ->
  typing_judgment Δ Γ e' τ1 ->
  typing_judgment Δ Γ (EApp e e') τ2
| T_TLam: forall Δ Γ e τ,
  typing_judgment Δ (fmap (rename (+1)) Γ) e τ ->
  typing_judgment Δ Γ (ETAbs e) (TForall τ)
| T_TApp: forall Δ Γ e τ1 τ2,
  typing_judgment Δ Γ e (TForall τ1) ->
  typing_judgment Δ Γ (ETApp e) τ1.[τ2/].

Lemma is_val_inversion : forall e, is_val e -> exists v, e = (of_val v).
Proof.
  intros.
  induction e;inversion H
  ;[ exists VUnit | | eexists (VAbs _)
     | eexists (VTAbs _) ]; eauto.
  apply IHe1 in H2; apply IHe2 in H3.
  destruct H2; destruct H3; subst.
  exists (VPair x x0); eauto.
Qed.
