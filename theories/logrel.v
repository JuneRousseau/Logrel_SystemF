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
            /\ (forall v', safe_lr Δ ξ t1 v' -> safe_parametrized (safe_lr Δ ξ t2) ( <{[ x / v'] e}>))
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

Fixpoint logrel_seq_list Δ (lΓ : list (string*ty))  ξ (vs : list expr) : Prop :=
  match lΓ with
  | nil => List.length vs = 0
  | (x,τ)::Γ' =>
      exists v vs', vs = v::vs'
               /\ safe_lr Δ ξ τ v
               /\ logrel_seq_list Δ Γ' ξ vs'
  end.

Definition logrel_seq Δ Γ ξ (vs : list expr) : Prop :=
  logrel_seq_list Δ (map_to_list Γ) ξ vs.

Lemma logrel_seq_weaken Δ Γ ξ P vs α :
not_free_context α Γ ->
( logrel_seq Δ Γ ξ vs
 <->
  logrel_seq (α::Δ) Γ (<[α := P]>ξ) vs
).
Proof.
  intros.
  split; intros.
  - generalize dependent Δ.
    generalize dependent ξ.
    generalize dependent α.
    generalize dependent P.
    generalize dependent vs.
    induction Γ using map_ind
    ; intros
    ; unfold logrel_seq in *.
    + setoid_rewrite map_to_list_empty in H0.
      setoid_rewrite map_to_list_empty.
      by cbn in *.
    + admit.
      (* setoid_rewrite map_to_list_insert. *)
      (* apply IHΓ. *)
Admitted.


Definition context_var Γ : list string :=
  map (fun x => match x with (x1,x2) => x1 end) (gmap_to_list Γ).

Lemma subst_term_seq_insert Γ vs x τ v e :
  (subst_term_seq (context_var (<[x:=τ]> Γ)) (v :: vs) e) =
    subst_term x v (subst_term_seq (context_var Γ) (vs) e).
Admitted.
Theorem fundamental_theorem Δ Γ τ e :
  Δ;Γ ⊢ e ∈ τ -> (forall ξ vs, logrel_seq Δ Γ ξ vs
                         -> safe_parametrized
                           (safe_lr Δ ξ τ) (subst_term_seq (context_var Γ) vs e)).
Proof.
  induction 1; intros.
  - (* T_Unit *)
    apply safe_val; auto.
    simpl in * ; split ; auto.
  - (* T_Var *)
    admit.
  - (* T_Prod *)
    rewrite subst_term_seq_pair.
    repeat intro.
    pose proof H1 as H1'.
    apply IHtyping_judgment1 in H1.
    apply IHtyping_judgment2 in H1'.
    unfold safe_parametrized in H1,H1'.
    admit.
  - (* T_Fst *)
    rewrite subst_term_seq_fst; cbn.
    (* apply IHtyping_judgment in H0. *)
    (* destruct H0 as (is_val_e & e1 & e2 & is_val_e1 & is_val_e2 & v_pair *)
    (*                 & Hsafe_e1 & Hsafe_e2). *)
    (* rewrite v_pair. *)
    (* backward safe_lr, because fst(e1,e2) -> e1, it suffices to show on e1 *)
    admit.
  - (* T_Snd *)
    (* rewrite subst_term_seq_snd; cbn in *. *)
    (* apply IHtyping_judgment in H0. *)
    (* destruct H0 as (is_val_e & e1 & e2 & is_val_e1 & is_val_e2 & v_pair *)
    (*                 & Hsafe_e1 & Hsafe_e2). *)
    (* rewrite v_pair. *)
    admit.
  - (* T_Lam *)
    rewrite subst_term_seq_lam.
    apply safe_val;auto.
    split;auto.
    exists x. exists (subst_term_seq (context_var Γ) vs e). split; auto.
    intros.
    assert ( logrel_seq Δ (<[x := τ1]> Γ) ξ (v'::vs)). admit.
    apply IHtyping_judgment in H2. simpl in H2.
    cbn in H2.
    unfold subst_term_seq in H2.
    rewrite subst_term_seq_insert in H2.
    apply H2.
  - (* T_App *)
    admit.
  - (* T_TLam *)
    admit.
  - (* T_TApp *)
    admit.
Admitted.
