Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
Require Import Autosubst.Autosubst.
From logical_relation Require Import relation syntax_stlc opsem_stlc.

Implicit Types Γ : context.
Implicit Types τ : ty.

(* Definition substitution := list val. *)
(* Implicit Types γ : substitution. *)
(* Fixpoint domain γ := *)
(*   match γ with *)
(*     | nil => [] *)
(*     | v::γ' => x::(domain γ') *)
(*   end. *)

Definition substitution := list expr.
Implicit Types γ : substitution.

Fixpoint env_subst γ : var → expr :=
  match γ with
  | [] => ids
  | v::γ' => v .: env_subst γ'
  end.

Definition normalize_to_v e v :=
  is_val v /\ e ~>* v.

Definition normalize e :=
  exists v, normalize_to_v e v.
Notation "⇓ e" := (normalize e) (at level 99).

Fixpoint sn (τ : ty) (e : expr) :=
 match τ with
 | Ty_Bool => ( [] ⊢ e ∈ Bool) /\ ⇓ e
 | Ty_Arrow t1 t2 =>
    ( [] ⊢ e ∈ (t1 -> t2))
    /\ (⇓ e)
    /\ (forall e', sn t1 e' -> sn t2 <{ e e' }> )
 end.

Definition sem_subst γ Γ : Prop :=
  Forall2 sn Γ γ.

Notation " γ ⊨ Γ" := (sem_subst γ Γ) (at level 99).
Lemma sn_safe : forall τ e, sn τ e -> ⇓ e.
Proof.
  intros.
  destruct τ; simpl in H ; firstorder.
Qed.

Lemma sn_typed : forall τ e, sn τ e -> [] ⊢ e ∈ τ.
Proof.
  intros.
  destruct τ; simpl in H ; firstorder.
Qed.


Lemma get_nil {T} : forall x, (get ([] : list T) x) = None.
Proof.
  by induction x; cbn.
Qed.

Lemma sem_subst_nil_r :
  forall γ, γ ⊨ [] -> γ = [].
Proof.
  intros; by inversion H.
Qed.

Lemma sem_subst_nil_l :
  forall Γ, [] ⊨ Γ -> Γ = [].
Proof.
  intros; by inversion H.
Qed.

Lemma sem_subst_cons_r_inv Γ γ τ :
  γ ⊨ (τ :: Γ) ->
 exists e γ', γ = (e::γ')
         /\ sn τ e
         /\ (γ' ⊨ Γ).
Proof.
  intros; inversion H;subst; exists y, l'; firstorder.
Qed.

Lemma sem_subst_cons_l_inv Γ γ e :
  (e::γ) ⊨ Γ ->
 exists τ Γ', Γ = (τ::Γ')
         /\ sn τ e
         /\ (γ ⊨ Γ').
Proof.
  intros; inversion H;subst; exists x, l; firstorder.
Qed.

Lemma typed_weaken_r :
  forall Γ Γ' e τ, Γ ⊢ e ∈ τ -> Γ++Γ' ⊢ e ∈ τ.
Proof.
  intros * Htyped.
  revert Γ'.
  induction Htyped; intros; try (constructor;auto).
  - unfold get in H.
    assert (Hget : nth_error Γ x ≠ None) by congruence.
    apply nth_error_Some in Hget.
    rewrite nth_error_app1; auto.
  - apply IHHtyped.
  - econstructor;auto.
Qed.


Lemma upn_ext n f x : upn n f x = if Nat.ltb x n then ids x else (f (x - n)).[ren (+n)].
Proof.
  revert x f. induction n as [|n IHn]; intros x f.
  + asimpl. rewrite PeanoNat.Nat.sub_0_r; trivial.
  + destruct x; [asimpl; reflexivity|].
    asimpl.
    rewrite IHn.
    destruct n; asimpl; [reflexivity|].
    destruct Nat.leb; [asimpl; reflexivity|].
    asimpl; trivial.
Qed.

Lemma typed_weaken :
  forall Γ Γ0 Γ1 e τ,
  Γ ⊢ e ∈ τ
  -> typing_judgment (Γ0 ++ Γ ++Γ1) (e.[upn (length Γ0) ids]) τ.
Proof.
  (* intros * Htyped. *)
  (* revert Γ0 Γ1. *)
  (* induction Htyped; intros; try (constructor;auto;fail). *)
  (* - asimpl. *)
  (*   rewrite upn_ext. *)

  (*   destruct Nat.ltb eqn:Hlt. *)
  (*   + apply PeanoNat.Nat.ltb_lt in Hlt. *)
  (*     constructor. *)
  (*     rewrite nth_error_app1. *)
  (*     repeat (rewrite lookup_app_l; [|assumption]); tauto. *)
  (*   + apply PeanoNat.Nat.ltb_ge in Hlt. *)
  (*     destruct (PeanoNat.Nat.eq_dec X (length Δ1)) as [->|]. *)
  (*     * rewrite PeanoNat.Nat.sub_diag; asimpl. *)
  (*       unfold rel_in_env. *)
  (*       rewrite lookup_app_r; [|lia]. *)
  (*       rewrite PeanoNat.Nat.sub_diag; simpl. *)
  (*       rewrite <- val_rel_weaken; intuition; eauto using val_rel_is_val. *)
  (*     * simpl; unfold rel_in_env; simpl. *)
  (*       rewrite lookup_app_r; [|lia]. *)
  (*       destruct (X - length Δ1) as [|z] eqn:Heq; [lia|]. *)
  (*       simpl; unfold rel_in_env; simpl. *)
  (*       rewrite lookup_app_r; [|lia]. *)
  (*       replace (length Δ1 + z - length Δ1) with z by lia. *)
  (*       tauto. *)





  (*   constructor;auto. *)
  (*   unfold get in H. *)
  (*   assert (Hget : nth_error Γ x ≠ None) by congruence. *)
  (*   apply nth_error_Some in Hget. *)
  (*   cbn. *)
  (*   rewrite nth_error_app2;[| lia]. *)
  (*   replace (length Γ0 + x - length Γ0) with x by lia. *)
  (*   by rewrite nth_error_app1. *)
  (* - constructor;auto. *)
  (*   asimpl in *. *)
  (*   specialize (IHHtyped Γ0 []). *)
  (*   simpl in IHHtyped. *)
  (*   rewrite app_nil_r in IHHtyped. *)
  (*   asimpl in IHHtyped. *)
  (*   apply IHHtyped in Htyped. *)
  (*   admit. *)
  (* - econstructor;auto. *)
Admitted.


Lemma env_subst_cons :
  forall e e' γ,
  e.[env_subst (e' :: γ)] = e.[env_subst [e']].[env_subst γ].
Proof.
Admitted.

Lemma substitution_lemma_gen :
  forall Γ1 Γ2 γ τ (e : expr),
  Γ1++Γ2 ⊢ e ∈ τ ->
  γ ⊨ (Γ1++Γ2) ->
  (typing_judgment Γ2 (e.[env_subst γ]) τ).
Proof.
  (* intros *. revert Γ1 Γ2 τ e. *)
  (* intros ?? ; revert Γ1. *)
  (* induction Γ2;intros * Htyped Hsem_subst. *)
  (* - simpl in *. *)
  (*   apply sem_subst_nil_r in Hsem_subst; subst. *)
  (*   asimpl. *)
  (*   apply (typed_weaken [] [] Γ2 e τ) in Htyped;simpl in Htyped. *)
  (*   rewrite upn0 in Htyped. asimpl in Htyped. assumption. *)
  (* - simpl in *. *)
  (*   apply sem_subst_cons_r_inv in Hsem_subst. *)
  (*   destruct Hsem_subst as (e' & γ' & -> & Hsn & Hsem_subst). *)
  (*   (* eapply  (IHΓ1 Γ2 γ' τ (e.[env_subst [e']])) in Hsem_subst;eauto. *) *)
    (* rewrite <- env_subst_cons in Hsem_subst. *)
    (* pose proof (typed_weaken (a::Γ1) [] Γ2 e τ). *)
    (*   in Hsem_subst;simpl in Hsem_subst. *)
    (* apply (typed_weaken (Γ1) [a] Γ2 e τ) in Hsem_subst;simpl in Hsem_subst. *)
    (* rewrite upn0 in Htyped. asimpl in Htyped. assumption. *)
    (* eapply typed_weaken with (Γ := Γ1) (Γ' := Γ2) ;eauto. *)
Admitted.


Lemma substitution_lemma :
  forall  Γ γ τ (e : expr),
  Γ ⊢ e ∈ τ ->
  γ ⊨ Γ ->
  (typing_judgment [] (e.[env_subst γ]) τ).
Proof.
  intros.
  eapply (substitution_lemma_gen Γ []); by rewrite app_nil_r.
Qed.

(* Lemma substitution_preserves_typing : *)
(*   ∀ (Γ : context) v τx e τ, *)
(*   is_val v -> *)
(*   (typing_judgment (<[x := τx]> Γ) e τ) -> *)
(*   (typing_judgment ∅ v τx) -> *)
(*   (typing_judgment Γ e.[v] τ). *)
(* Proof. *)
(* Admitted. *)


Lemma preservation :
  forall e e' τ, ([] ⊢ e ∈ τ) ->
            e ~> e' ->
            ([] ⊢ e' ∈ τ).
Proof.
  intros * Ht ?.
  generalize dependent e'.
  (* remember empty as Γ. *)
  (* induction Ht; *)
  (*      intros * HE; subst; *)
  (*      try solve [inversion HE; subst; auto]. *)
  (* inversion_clear HE; subst;eauto. *)
  (* eapply substitution_preserves_typing; eauto. *)
  (*   admit. *)
Admitted.


Lemma sn_backward τ e e':
 ([] ⊢ e ∈ τ) ->
 e ~> e' ->
 (sn τ e' -> sn τ e).
Proof.
Admitted.

Lemma sn_backward_star τ e e':
 ([] ⊢ e ∈ τ) ->
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
 ([] ⊢ e ∈ τ) ->
 e ~> e' ->
 (sn τ e -> sn τ e').
Admitted.

Lemma sn_forward_star τ e e':
 ([] ⊢ e ∈ τ) ->
 e ~>* e' ->
 (sn τ e -> sn τ e').
Proof.
  intros.
  induction H0 using star_ind; auto.
  apply IHstar;auto.
  eapply preservation;eauto.
  eapply sn_forward; eauto.
Qed.

Lemma sn_well_typed τ e: sn τ e -> ([] ⊢ e ∈ τ).
Proof.
  intros. destruct τ; simpl in *;firstorder.
Qed.

Lemma sem_subst_get:
  forall Γ γ x τ,
  γ ⊨ Γ ->
  get Γ x = Some τ ->
  exists e, get γ x = Some e /\ sn τ e.
Proof.
  intros.
  revert x τ H0.
  induction H; intros * HsomeΓ.
  - destruct x;cbn in HsomeΓ;discriminate.
  - destruct x0;cbn in *;eauto.
    eexists;split;eauto.
    by injection HsomeΓ;intros;subst.
Qed.

Lemma env_subst_get :
  forall γ x e, get γ x = Some e → env_subst γ x = e.
Proof.
  induction γ; intros * Hsome;simpl in *.
  - induction x;cbn in Hsome;discriminate.
  - destruct x;cbn in *.
    + by injection Hsome.
    + by apply IHγ.
Qed.

Lemma fundamental : forall Γ γ τ e,
  γ ⊨ Γ ->
  (Γ ⊢ e ∈ τ) ->
  sn τ e.[env_subst γ].
Proof.
  intros; generalize dependent γ.
  induction H0; intros.
  - (* true *)
    split; auto;[constructor|].
    eexists;split;try eapply star_refl;eauto.
  - (* false *)
    split; auto;[constructor|].
    eexists;split;try eapply star_refl;eauto.
  - (* ife *)
    specialize (IHtyping_judgment1 γ H).
    specialize (IHtyping_judgment2 γ H).
    specialize (IHtyping_judgment3 γ H).
    destruct IHtyping_judgment1 as [Htyped_b b_val].
    destruct b_val as (bv & (Hbv_val & Hbv)).
    set (s_et := (et.[env_subst γ])) in *.
    set (s_ef := (ef.[env_subst γ])) in *.
    eapply sn_backward_star with
      (e' := <{ if bv then s_et else s_ef }>);auto.
    constructor;auto; by apply sn_typed.
    apply mstep_if; firstorder.
    assert (Hbv_values : bv = expr_true \/ bv = expr_false) by admit.
    destruct Hbv_values as [ -> | -> ]
    ; [eapply sn_backward_star with (e' := <{ s_et }>)
        | eapply sn_backward_star with (e' := <{ s_ef }>)]
    ; auto
    ; match goal with
      | h:_ |- ( _ ⊢ _ ∈ _ ) =>
          (constructor;auto; try (by apply sn_typed) ; constructor)
      | _ => econstructor;constructor
      end.
  - (* var *)
    eapply sem_subst_get in H;eauto.
    destruct H as (e' & Hget & Hsn).
    by apply env_subst_get in Hget ; subst.
  - (* lam *)
    set (eγ := env_subst γ) in *.
    split.
    apply substitution_lemma with (Γ := Γ);auto; by constructor.
    split.
    eexists;split; asimpl;try eapply star_refl;eauto.
    intros e' sn_e'.
    pose proof sn_e' as Hsn_e'.
    apply sn_safe in sn_e'; destruct sn_e' as (v & v_val & step_e').
    apply sn_backward_star with (e' := expr_app (expr_lam e.[up eγ]) v);auto.
    admit.
    asimpl.
    apply mstep_app_arg; auto.
    apply sn_backward_star with (e' := (e.[up eγ].[v/]));auto.
    admit.
    apply star_one; auto.
    apply is_val_inversion in v_val ; destruct v_val; subst.
    specialize (IHtyping_judgment ((of_val x)::γ)).
    asimpl in *.
    apply IHtyping_judgment.
    constructor;auto.
    eapply sn_forward_star; eauto.
    by apply sn_typed.
  - (* app *)
    pose proof H as H'.
    apply IHtyping_judgment1 in H
    ; clear IHtyping_judgment1
    ; destruct H as (IH1_type & IH1_norm & IH1_sn).
    apply IHtyping_judgment2 in H'; clear IHtyping_judgment2.
    by apply IH1_sn.
Admitted.


Lemma well_typed_sn: forall τ e, (∅ ⊢ e ∈ τ) -> sn τ e.
