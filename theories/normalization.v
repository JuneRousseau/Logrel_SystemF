Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
From logical_relation Require Import relation syntax_stlc opsem_stlc.

Implicit Types Γ : context.
Implicit Types τ : ty.

Definition substitution := list (string*val).
Implicit Types γ : substitution.
Fixpoint domain γ :=
  match γ with
    | nil => []
    | (x,v)::γ' => x::(domain γ')
  end.

Fixpoint substitute γ e :=
  match γ with
  | nil => e
  | (x,v)::γ' => substitute γ' (subst_term x (of_val v) e)
  end.

Definition normalize_to_v e v :=
  is_val v /\ e ~>* v.

Definition normalize e :=
  exists v, normalize_to_v e v.
Notation "⇓ e" := (normalize e) (at level 99).

Fixpoint sn (τ : ty) (e : expr) :=
 match τ with
 | Ty_Bool => (∅ ⊢ e ∈ Bool) /\ ⇓ e
 | Ty_Arrow t1 t2 =>
    (∅ ⊢ e ∈ (t1 -> t2))
    /\ (⇓ e)
    /\ (forall e', sn t1 e' -> sn t2 <{ e e' }> )
 end.

Definition sem_subst γ Γ :=
  Forall (fun x => sn (match (Γ !! x) with
                      | None => Ty_Bool
                      | Some t => t
                    end)
                  (substitute γ (expr_var x)))
    (domain γ) /\
  (map_to_list Γ).*1 = domain γ.
Notation " γ ⊨ Γ" := (sem_subst γ Γ) (at level 99).
Lemma sn_safe : forall τ e, sn τ e -> ⇓ e.
Proof.
  intros.
  destruct τ; simpl in H ; firstorder.
Qed.

Lemma substitution_lemma Γ γ τ e :
  Γ ⊢ e ∈ τ ->
  γ ⊨ Γ ->
  (typing_judgment ∅ (substitute γ e) τ).
Proof.
Admitted.

Lemma substitution_preserves_typing :
  ∀ (Γ : context) (x: string) v τx e τ,
  is_val v ->
  (typing_judgment (<[x := τx]> Γ) e τ) ->
  (typing_judgment ∅ v τx) ->
  (typing_judgment Γ (subst_term x v e) τ).
Proof.
Admitted.


Lemma preservation :
  forall e e' τ, (∅ ⊢ e ∈ τ) ->
            e ~> e' ->
            (∅ ⊢ e' ∈ τ).
Proof.
  intros * Ht ?.
  generalize dependent e'.
  remember empty as Γ.
  induction Ht;
       intros * HE; subst;
       try solve [inversion HE; subst; auto].
  inversion_clear HE; subst;eauto.
  eapply substitution_preserves_typing; eauto.
    admit.
Admitted.


Lemma sn_backward τ e e':
 (∅ ⊢ e ∈ τ) ->
 e ~> e' ->
 (sn τ e' -> sn τ e).
Proof.
Admitted.

Lemma sn_backward_star τ e e':
 (∅ ⊢ e ∈ τ) ->
 e ~>* e' ->
 (sn τ e' -> sn τ e).
Proof.
  intros.
  induction H0 using star_ind; auto.
  eapply sn_backward; eauto.
  apply IHstar;auto.
  eapply preservation;eauto.
Qed.

Lemma sn_forward τ e e':
 (∅ ⊢ e ∈ τ) ->
 e ~> e' ->
 (sn τ e -> sn τ e').
Admitted.

Lemma sn_forward_star τ e e':
 (∅ ⊢ e ∈ τ) ->
 e ~>* e' ->
 (sn τ e -> sn τ e').
Proof.
  intros.
  induction H0 using star_ind; auto.
  apply IHstar;auto.
  eapply preservation;eauto.
  eapply sn_forward; eauto.
Qed.

Lemma sn_well_typed τ e: sn τ e -> (∅ ⊢ e ∈ τ).
Proof.
  intros. destruct τ; simpl in *;firstorder.
Qed.

Lemma substitute_true γ :
(substitute γ <{ true }> ) = <{true}>.
Admitted.
Lemma substitute_false γ :
(substitute γ <{ false }> ) = <{false}>.
Admitted.

Lemma substitute_abs γ x e  :
(substitute γ <{ λ x, e }>) =
  expr_abs x (substitute γ <{ e }>).
Admitted.

Lemma substitute_app γ e e' :
(substitute γ <{ e e' }>) =
  expr_app (substitute γ <{ e }>) (substitute γ <{ e' }>).
Admitted.

Lemma substitute_if γ e e1 e2 :
(substitute γ <{ if e then e1 else e2 }>) =
  expr_if (substitute γ <{ e }>) (substitute γ <{ e1 }>) (substitute γ <{ e2 }>).
Admitted.

Lemma substitute_neq_commute γ x1 x2 e e1 e2:
  (x1 ≠ x2)%string ->
  substitute γ <{ [x1 / e1] ([x2 / e2] e) }>
    =
  substitute γ <{ [x2 / e2] ([x1 / e1] e) }>.
Admitted.

Lemma substitute_eq_update γ x e e1 e2:
  substitute γ <{ [x / e1] ([x / e2] e) }>
    =
  substitute γ <{ [x / e1] e }>.
Admitted.

Lemma subst_term_substitute:
  ∀ γ (x : string) (e : expr) (v : val),
  subst_term x (of_val v) (substitute γ e)
  = substitute ((x, v) :: γ) e.
Proof.
  intros; cbn.
  generalize dependent x.
  generalize dependent v.
  generalize dependent e.
  induction γ;auto;intros.
  destruct a;cbn.
  destruct (s =? x)%string eqn:Heq.
  - apply String.eqb_eq in Heq; subst.
    rewrite substitute_eq_update.
    rewrite <- IHγ.
    admit.
  -apply String.eqb_neq in Heq; subst.
    rewrite substitute_neq_commute; auto.
Admitted.

Lemma sem_subst_empty Γ :
 [] ⊨ Γ -> Γ = ∅.
Proof.
  intros.
  inversion H.
  simpl in*.
  apply fmap_nil_inv in H1.
  by apply map_to_list_empty_iff.
Qed.

Lemma sem_subst_cons: forall Γ γ x v τ,
  γ ⊨ Γ ->
  sn τ (of_val v) ->
  (x, v) :: γ ⊨ <[x:=τ]> Γ.
Proof.
  induction γ;intros.
  - apply sem_subst_empty in H ; subst.
    unfold sem_subst ; cbn.
    split.
    + apply Forall_singleton.
    replace (<[x:=τ]> ∅ !! x) with (Some τ) by
                                   (symmetry; apply lookup_insert).
    rewrite String.eqb_refl; auto.
    + replace (<[x:=τ]> ∅) with (singletonM x τ : gmap string ty) by auto.
    setoid_rewrite map_to_list_singleton; auto.
  - destruct a as [x' v'].
    admit.
    (* inversion_clear H. *)
Admitted.

Lemma some_in_context :
  forall l Γ x τ,
  Γ !! x = Some τ ->
  (map_to_list Γ).*1 = l ->
  x ∈ l.
Proof.
  induction l; intros.
  - apply fmap_nil_inv in H0.
    apply map_to_list_empty_iff in H0;subst.
    discriminate H.
  - assert ( Hinv: exists Γ' τ', Γ = <[ a := τ']> Γ' ).
    admit.
    destruct Hinv as ( Γ' & τ' & -> ).
    assert ( (map_to_list Γ').*1 = l). admit.
    destruct (x =? a)%string eqn:Heq.
    + apply String.eqb_eq in Heq; subst.
      apply elem_of_list_here.
    +  apply String.eqb_neq in Heq; subst.
      apply elem_of_list_further.
      eapply (IHl Γ' _ τ); auto.
      setoid_rewrite lookup_insert_ne in H; auto.
Admitted.

Lemma fundamental : forall Γ γ τ e,
  γ ⊨ Γ ->
  (Γ ⊢ e ∈ τ) ->
  sn τ (substitute γ e).
Proof.
  intros; generalize dependent γ.
  induction H0; intros ; simpl in *.
  - (* true *)
    split; rewrite substitute_true; auto.
    eexists;split;try eapply star_refl;eauto.
  - (* false *)
    split; rewrite substitute_false; auto.
    eexists;split;try eapply star_refl;eauto.
  - (* var *)
    destruct H0 as [ ? Hdom ].
    assert (Hx: x ∈ (domain γ)) by (eapply some_in_context; eauto).
    eapply Forall_forall in H0;eauto.
    by rewrite H in H0.

  - (* lam *)
    split.
    apply substitution_lemma with (Γ := Γ);auto.
    rewrite substitute_abs.
    split.
    eexists;split;try eapply star_refl;eauto.
    intros e' sn_e'.
    pose proof sn_e' as Hsn_e'.
    apply sn_safe in sn_e'; destruct sn_e' as (v & v_val & step_e').
    apply sn_backward_star with (e' := expr_app (expr_abs x (substitute γ e)) v);auto.
    admit.
    apply mstep_app_arg; auto.
    apply sn_backward_star with (e' := subst_term x v (substitute γ e));auto.
    admit.
    apply star_one; auto.
    apply is_val_inversion in v_val ; destruct v_val; subst.
    rewrite subst_term_substitute.
    apply IHtyping_judgment.
    apply sem_subst_cons;auto.
    eapply sn_forward_star in Hsn_e';eauto; apply sn_well_typed;assumption.

  - (* app *)
    pose proof H as H'.
    apply IHtyping_judgment1 in H
    ; clear IHtyping_judgment1
    ; destruct H as (IH1_type & IH1_norm & IH1_sn).
    apply IHtyping_judgment2 in H'; clear IHtyping_judgment2.
    rewrite substitute_app.
    by apply IH1_sn.

  - (* if *)
    pose proof H as H1;
    pose proof H as H2.
    apply IHtyping_judgment1 in H
    ; clear IHtyping_judgment1
    ; destruct H as [H_bool H_norm].
    apply IHtyping_judgment2 in H1
    ; clear IHtyping_judgment2.
    apply IHtyping_judgment3 in H2
    ; clear IHtyping_judgment3.

    destruct H_norm as [v H_norm].
    assert (Hv : (substitute γ e) ~>* <{ true }>

    { admit. }
    destruct Hv.
    + (* true *)
      apply sn_backward_star
        with (e' := expr_if expr_true (substitute γ e1) (substitute γ e2)).
      rewrite substitute_if.
      apply T_If; auto; apply sn_well_typed;auto.
      rewrite substitute_if.
      apply mstep_if;auto.
      apply sn_backward_star with (e' := (substitute γ e1));auto.
      apply T_If;auto; apply sn_well_typed;auto.
      apply star_one; auto.
    + (* false *)
      apply sn_backward_star
        with (e' := expr_if expr_false (substitute γ e1) (substitute γ e2)).
      rewrite substitute_if.
      apply T_If; auto; apply sn_well_typed;auto.
      rewrite substitute_if.
      apply mstep_if;auto.
      apply sn_backward_star with (e' := (substitute γ e2));auto.
      apply T_If;auto; apply sn_well_typed;auto.
      apply star_one; auto.
Admitted.


Lemma well_typed_sn: forall τ e, (∅ ⊢ e ∈ τ) -> sn τ e.
