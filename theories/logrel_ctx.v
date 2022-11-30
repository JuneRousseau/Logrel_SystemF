Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Export relation.
From logical_relation Require Import syntax_systemF opsem_systemF_ctx.

(** Logical relation for type soundness *)
Implicit Types Δ : tcontext.
Implicit Types Γ : context.
Implicit Types τ : ty.

(* TODO gmap ? *)
Definition substitution := gmap string (expr -> Prop).
Implicit Types ξ : substitution.

(** Safe parametrized by P
    cf Section 4. Safe_{P}(e) *)
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
  generalize dependent e'.
  induction step'; intros.
  - (* Reflexive *) right; eexists ; eauto.
  - (* Transitive *)
    eapply sf_deterministic in step. eapply step in H.
    subst. clear step.
    by apply safe_e'.
Qed.

Lemma safe_bind K e P Q :
  safe_parametrized Q e ->
  (forall v, Q v -> safe_parametrized P (fill K v)) ->
  safe_parametrized P (fill K e).
Proof.
  intros safeQ safeP.
  intros e' Hstep.
  apply mstep_ectx in Hstep as [(e'' & -> & Hstep)|(v & Hv & Hv1 & Hv2)].
  - apply safeQ in Hstep.
    destruct Hstep as [(Hv & HQv)|(e3 & He3)].
    + apply safeP in HQv; apply HQv. apply star_refl.
    + right. eexists. eapply step_fill; eauto.
  - apply safeQ in Hv1.
    destruct Hv1 as [(_ & HQv)|(e3 & He3)].
    + apply safeP in HQv; apply HQv. auto.
    + eapply is_val_stuck in Hv. by apply Hv in He3.
Qed.


(** Logical relation for type safety defined using safe parametrized
    cf Section 5. Predicates on values *)
(* TODO Note that we are implicitly assuming that the domain of the partial mapping ξ in
[∆ ⊢ τ ]ξ is always ∆ *)
Fixpoint logrel_safe (Δ : tcontext) (ξ : substitution) (τ : ty) (v : expr) :=
  is_val v /\
 match τ with
 | Ty_Var α => match (ξ !! α) with | None => True | Some P => P v end
 | Ty_Unit => v = <{ tt }>
 | Ty_Pair t1 t2 =>
     exists e1 e2, is_val e1
              /\ is_val e2
              /\ v = <{ ⟨ e1, e2 ⟩ }>
              /\ logrel_safe Δ ξ t1 e1
              /\ logrel_safe Δ ξ t2 e2
 | Ty_Arrow t1 t2 =>
     exists x e, v = <{ λ x, e }>
            /\ (forall v', logrel_safe Δ ξ t1 v' -> safe_parametrized (logrel_safe Δ ξ t2) ( <{[ x / v'] e}>))
 | Ty_Forall α t =>
     exists e, v = <{ Λ e }>
            /\ forall (P: expr -> Prop), safe_parametrized (logrel_safe ({[α]}∪ Δ) (<[α := P]> ξ) t) e
 end.

Lemma safe_is_val Δ ξ v τ : logrel_safe Δ ξ τ v -> is_val v.
Proof.
  induction τ; simpl ; intros; destruct H;auto.
Qed.

Lemma logrel_subst Δ ξ τ τ' v α :
  (logrel_safe Δ ξ (subst_type α τ' τ) v)
  <-> (logrel_safe ({[α]} ∪ Δ) (<[α := logrel_safe Δ ξ τ']> ξ) τ v).
Proof.
  split; intros Hsafe.
  - generalize dependent τ'.
    generalize dependent α.
    generalize dependent v.
    generalize dependent ξ.
    generalize dependent Δ.
    induction τ; intros * Hsafe; simpl in *; auto.
  + split; [by apply safe_is_val in Hsafe|].
    destruct (α =? s)%string eqn:Heq.
    * apply String.eqb_eq in Heq; subst.
      assert (Heq: <[s:=logrel_safe Δ ξ τ']> ξ !! s = Some (logrel_safe Δ ξ τ'))
      by apply lookup_insert.
      by rewrite Heq.
    * cbn in Hsafe ; destruct Hsafe as [_ Hsafe].
      apply String.eqb_neq in Heq.
      assert (Hmap: <[α:=logrel_safe Δ ξ τ']> ξ !! s = ξ !! s)
      by (apply lookup_insert_ne;auto).
      rewrite Hmap.
      apply Hsafe.
  + (* pair *)
    destruct Hsafe as (Hval & v1 & v2 & Hval1 & Hval2 & -> & Hsafe1 & Hsafe2).
    split;auto.
    exists v1, v2.
    repeat(split;auto).
  + (* lambda *)
    destruct Hsafe as (Hval & x & e & -> & Hsafe).
    split;auto.
    exists x, e.
    split;auto.
    set ( ξ' := (<[α:=logrel_safe Δ ξ τ']> ξ) ).
    intros.
    intros e' Hstep.
    admit.
  + (* poly *)
    destruct (α =? s)%string eqn:Heq ; simpl in Hsafe
    ;destruct Hsafe as (Hval & e & Hv & Hsafe); split;auto; exists e
    ; split; auto
    ; intros;
      specialize (Hsafe P).
    replace ( {[s]} ∪ ({[α]} ∪ Δ)) with ({[α]} ∪ ({[s]} ∪ Δ)) by set_solver.
    intros e' Hstep.
    apply Hsafe in Hstep.
    destruct Hstep; [left|right].
    (* I need to be able to swap α and s *)
    admit.
    admit.
    admit.
  - admit.
Admitted.

Lemma logrel_weaken Δ ξ τ v α P :
  not (free α τ) ->
  ((logrel_safe Δ ξ τ v) <->
  (logrel_safe Δ  (<[α := P]> ξ) τ v)).
Proof.

  split; intros Hsafe;
  generalize dependent v;
  induction τ; intros; simpl in *;
  destruct Hsafe; split; auto.
  - unfold not in H.
    destruct (decide (α = s)%string); subst.
    + (* \alpha = s --> contradiction with free *)
      exfalso; apply H; apply free_var.
    + replace (<[α:=P]> ξ !! s) with (ξ !! s)
    by (symmetry ; apply lookup_insert_ne;auto).
    auto.
  - destruct H1 as (v1 & v2 & Hv1 & Hv2 & Hv& Hsafe1 & Hsafe2).
    exists v1, v2.
    repeat(split;auto).
    apply IHτ1;auto; intro; apply H; by apply free_pair1.
    apply IHτ2;auto; intro; apply H; by apply free_pair2.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

(* TODO better way to define the sequence ? *)
Fixpoint logrel_seq_list Δ (lΓ : list (string*ty))  ξ (vs : list expr) : Prop :=
  match lΓ with
  | nil => List.length vs = 0
  | (x,τ)::Γ' =>
      exists v vs', vs = v::vs'
               /\ logrel_safe Δ ξ τ v
               /\ logrel_seq_list Δ Γ' ξ vs'
  end.

Definition logrel_seq Δ Γ ξ (vs : list expr) : Prop :=
  logrel_seq_list Δ (map_to_list Γ) ξ vs.

Lemma logrel_seq_weaken Δ Γ ξ P vs α :
not_free_context α Γ ->
( logrel_seq Δ Γ ξ vs
 <->
  logrel_seq ({[α]} ∪ Δ) Γ (<[α := P]>ξ) vs
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
  (* (gmap_to_list Γ).*1 . *)

Lemma subst_term_seq_insert Γ vs x τ v e :
  (subst_term_seq (context_var (<[x:=τ]> Γ)) (v :: vs) e) =
    subst_term x v (subst_term_seq (context_var Γ) (vs) e).
Proof.
  generalize dependent Γ.
  generalize dependent vs.
  generalize dependent x.
  generalize dependent τ.
  generalize dependent v.
  induction e; intros ; auto; cbn.
  - (* var *)
    induction Γ using map_ind.
    + replace (context_var (<[x:=τ]> ∅)) with [x].
      replace (context_var ∅) with ([] : list string).
      reflexivity.
      unfold context_var.
      (* rewrite map_to_list_empty. *)
      admit.
      admit.
    + admit.
  - (* pair *)
    by rewrite IHe1, IHe2.
  - (* fst *)
    by rewrite IHe.
  - (* snd *)
    by rewrite IHe.
  - (* app *)
    by rewrite IHe1, IHe2.
  - (* abs *)
    rewrite IHe.
    (* TODO do I miss an hypothesis about Γ ? *)
    (* destruct (decide (s = x)); subst. *)
    (* + (* s = x*) *)
    admit.

  - (* tapp *)
    by rewrite IHe.
  - (* tabs *)
    by rewrite IHe.
Admitted.

Theorem fundamental_theorem Δ Γ τ e :
  Δ;Γ ⊢ e ∈ τ -> (forall ξ vs, logrel_seq Δ Γ ξ vs
                         -> safe_parametrized
                           (logrel_safe Δ ξ τ) (subst_term_seq (context_var Γ) vs e)).
Proof.
  induction 1; intros.
  - (* T_Unit *)
    apply safe_val; auto.
    simpl in * ; split ; auto.
  - (* T_Var *)
    induction Γ using map_ind.
    unfold replace_var.
    (* TODO from H, we know that x \in (context_var \Gamma), and thus we can replace
       the variable *)
    admit.
    admit.
  - (* T_Prod *)
    (* TODO how to cbn just subst_term_seq ? *)
    (* eapply (safe_bind (LPairCtx EmptyCtx _ )); econstructor; eauto. *)
    (* 2:{ cbn in *. inversion H3; cbn.  } *)
    cbn.
    repeat intro.
    pose proof H1 as H1'.
    apply IHtyping_judgment1 in H1.
    apply IHtyping_judgment2 in H1'.
    unfold safe_parametrized in H1,H1'.
    admit.
  - (* T_Fst *)

    cbn.
    (* apply IHtyping_judgment in H0. *)
    (* destruct H0 as (is_val_e & e1 & e2 & is_val_e1 & is_val_e2 & v_pair *)
    (*                 & Hsafe_e1 & Hsafe_e2). *)
    (* rewrite v_pair. *)
    (* backward logrel_safe, because fst(e1,e2) -> e1, it suffices to show on e1 *)
    admit.
  - (* T_Snd *)
    cbn.
    (* rewrite subst_term_seq_snd; cbn in *. *)
    (* apply IHtyping_judgment in H0. *)
    (* destruct H0 as (is_val_e & e1 & e2 & is_val_e1 & is_val_e2 & v_pair *)
    (*                 & Hsafe_e1 & Hsafe_e2). *)
    (* rewrite v_pair. *)
    admit.
  - (* T_Lam *)
    cbn.
    set( v :=
           match find (String.eqb x) (context_var Γ) with
           | Some _ => <{ λ x, e }>
           | None => (expr_abs x (subst_term_seq (context_var Γ) vs e))
           end
       ).
    assert (is_val v).
    { destruct (find (String.eqb x) (context_var Γ)) ; subst v; auto. }
    apply safe_val;auto.
    split;auto.
    exists x. exists (subst_term_seq (context_var Γ) vs e).
    split.
    + subst v. admit.
    + intros.
      assert ( logrel_seq Δ (<[x := τ1]> Γ) ξ (v'::vs)). admit.
    (* apply IHtyping_judgment in H2. simpl in H2. *)
    (* cbn in H2. *)
    (* unfold subst_term_seq in H2. *)
    (* rewrite subst_term_seq_insert in H2. *)
    (* apply H2. *)
      admit.
  - (* T_App *)
    admit.
  - (* T_TLam *)
    admit.
  - (* T_TApp *)
    admit.
Admitted.
