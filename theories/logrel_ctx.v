Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
Require Import Autosubst.Autosubst.
From logical_relation Require Export relation.
From logical_relation Require Import syntax_systemF opsem_systemF_ctx.

(** Logical relation for type soundness *)
Implicit Types Γ : context.
Implicit Types τ : ty.

Definition substitution := list (expr -> Prop).
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
  unfold safe_parametrized in safeQ.
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

(** ξ is a substitution, ie. it is a function that maps a variable to
    an expression property. *)
Fixpoint logrel_safe (ξ : substitution) (τ : ty) (v : expr) :=
  match τ with
  | Ty_Var α => is_val v
               /\ match (get ξ α) with
                 | None => True
                 | Some P => P v
                 end
  | Ty_Unit => v = <{ tt }>
    | Ty_Pair t1 t2 =>
        exists e1 e2, is_val e1
                 /\ is_val e2
                 /\ v = <{ ⟨ e1, e2 ⟩ }>
                 /\ logrel_safe ξ t1 e1
                 /\ logrel_safe ξ t2 e2
    | Ty_Arrow t1 t2 =>
        exists e, v = <{ λ _, e }>
               /\ (forall v', logrel_safe ξ t1 v' ->
                        safe_parametrized (logrel_safe ξ t2) (<{v v'}>))
    | Ty_Forall t =>
        exists e, v = <{ Λ e }>
             /\ forall (P: expr -> Prop), safe_parametrized (logrel_safe (P :: ξ) t) e
end.

Definition logrel_context (Γ: context) (ξ: substitution) (σ : var -> expr) : Prop :=
    forall (x : var), match (get Γ x) with
                 | None => True
                 | Some τ => logrel_safe ξ τ (σ x)
                 end.

Lemma safe_is_val ξ v τ : logrel_safe ξ τ v -> is_val v.
Proof.
  induction τ; simpl ; intros; try destruct H as (?&?);auto.
  - subst; constructor.
  - destruct H as (?&?&?&?&?); subst; by constructor.
  - destruct H as (?&?); subst; by constructor.
  - destruct H as (?&?); subst; by constructor.
Qed.

Lemma logrel_subst_generalized τ :
  forall ξ1 ξ2 τ' v,
  (logrel_safe (ξ1++ξ2) τ.[upn (length ξ1) (τ'.: ids)] v)
  <-> (logrel_safe (ξ1 ++ (logrel_safe ξ2 τ')::ξ2) τ v).
Proof.
  induction τ; intros *.
  + (* var *)
    rename v into x.
    rename v0 into v.
    asimpl.
    (* revert x ξ1 ξ2 τ' v. *)
    (* induction ξ1;intros;cbn. *)
    admit.
  + (* unit *)
    auto.
  + (* pair *)
    split; intro Hsafe
    ; destruct Hsafe as (v1 & v2 & Hval1 & Hval2 & -> & Hsafe1 & Hsafe2)
    ; exists v1, v2
    ; repeat(split;auto).
    all: (try by apply IHτ1).
    all: (try by apply IHτ2).
  + (* lambda *)
    split; intros [? Hsafe];simpl
    ; destruct Hsafe as (-> & Hsafe)
    ; exists x; split; auto;intros.
    all: eapply safe_mono;[intros|eapply Hsafe].
    all: (try by apply IHτ1).
    all: (try by apply IHτ2).
  + (* poly *)
    split ; intros [? Hsafe] ;simpl
    ; destruct Hsafe as (-> & Hsafe)
    ; exists x; split;auto;intros.
    all: eapply safe_mono;[intros|eapply (Hsafe P)].
    all: try by eapply (IHτ (_::_)).
Admitted.


(* Cannot be done naively: the induction hypothesis for type lambda abstraction
   is not strong enough ! *)
Lemma logrel_subst ξ τ τ' v :
  (logrel_safe ξ τ.[τ'/] v )
  <-> (logrel_safe ((logrel_safe ξ τ')::ξ) τ v).
Proof.
  apply logrel_subst_generalized with (ξ1 := nil).
Qed.

Lemma logrel_context_cons_inv Γ τ ξ σ :
 logrel_context (τ :: Γ) ξ σ ->
 exists x σ', σ = (x .: σ')
         /\ logrel_safe ξ τ x
         /\ logrel_context Γ ξ σ'.
Proof.
  revert Γ τ σ.
  induction ξ; intros.
Admitted.

Lemma logrel_context_cons:
  ∀ (Γ : context) (ξ : substitution) σ (e : expr) τ,
  logrel_context Γ ξ σ
  → logrel_safe ξ τ e
  → logrel_context (τ :: Γ) ξ (e .: σ).
Proof.
  intros * Hcontext Hsafe.
  unfold logrel_context in *.
  intro.
  destruct x.
  - by simpl.
  - simpl; apply Hcontext.
Qed.

Lemma logrel_safe_incr_generalized τ :
  forall ξ1 ξ2 e P,
  logrel_safe (ξ1 ++ ξ2) τ e ↔
  logrel_safe (ξ1 ++ P :: ξ2) (τ.[upn (length ξ1) (ren (+ 1))]) e.
Proof.
  induction τ;intros.
  - (* Var *)
  (*   split;intros H; destruct H; split;auto. *)
  (* - (* Unit *) by cbn in *. *)
  (* - (* Pair *) cbn in *. *)
  (*   split;intros H *)
  (*   ; destruct H as (e1&e2&Hval1&Hval2&->&Hsafe1&Hsafe2) *)
  (*   ; eapply IHτ1 in Hsafe1 *)
  (*   ; eapply IHτ2 in Hsafe2 *)
  (*   ; exists e1, e2; repeat(split;eauto). *)
  (* - (* Arrow *) *)
  (*   cbn in *. *)
  (*   split; intros H *)
  (*   ; destruct H as (e'& ->& Hsafe) *)
  (*   ; exists e'; split;auto *)
  (*   ; intros *)
  (*   ; eapply safe_mono *)
  (*   ; match goal with *)
  (*     | h: _ |- safe_parametrized _ _ => eapply Hsafe *)
  (*     | h: _ |- _ => idtac *)
  (*   end *)
  (*   ; intros *)
  (*   ; try (by eapply IHτ1) *)
  (*   ; try (by eapply IHτ2). *)
  (* - (* Forall *) *)
  (*   cbn in *. *)
  (*   split; intros H *)
  (*   ; destruct H as (e'&->&Hsafe) ; exists e' *)
  (*   ; split;auto *)
  (*   ; intros. *)
  (*   + eapply safe_mono. *)
  (*     2: apply Hsafe. *)
  (*     intros; eapply (IHτ (P::ξ) e P0) in H0. *)
  (*     admit. *)
  (*   + eapply safe_mono. *)
  (*     2: apply Hsafe. *)
  (*     intros. eapply IHτ. *)
  (*     admit. *)
Admitted.

Lemma logrel_safe_incr :
  forall τ ξ e P,
  logrel_safe ξ τ e <->
  logrel_safe (P :: ξ) (rename (+1) τ) e.
Proof.
  intros.
  pose proof (logrel_safe_incr_generalized τ nil ξ e P) as H; simpl in H.
  rewrite upn0 in H; asimpl in *.
  apply H.
Qed.

Lemma logrel_context_weaken :
  forall Γ ξ σ P,
  logrel_context Γ ξ σ ->
  logrel_context (map (rename (+1)) Γ) (P :: ξ) σ.
Proof.
  intros.
  generalize dependent σ.
  induction Γ;intros.
  - unfold logrel_context in H.
    intro x; cbn.
    by replace (get ([] : context) x) with (None : option ty)
    by (by destruct x; auto).
  - apply logrel_context_cons_inv in H.
    destruct H as (e & σ' & -> & Hsafe & Hcontext).
    apply logrel_context_cons;auto.
    by apply logrel_safe_incr.
Qed.

Theorem fundamental_theorem :
  forall Γ τ e ,
  Γ ⊢ e ∈ τ ->
  (forall ξ σ,
     logrel_context Γ ξ σ -> safe_parametrized (logrel_safe ξ τ) e.[σ]).
Proof.
  induction 1; intros.
  - (* T_Unit *)
    apply safe_val; auto.
    simpl in * ; split ; auto.
  - (* T_Var *)
    cbn.
    specialize (H0 x); rewrite H in H0.
    intro.
    pose proof H0 as Hval.
    apply safe_is_val in H0.
    apply safe_val;auto.
  - (* T_Prod *)
    simpl subst.
    pose proof H1 as H1'.
    apply IHtyping_judgment1 in H1.
    apply IHtyping_judgment2 in H1'.
    set (es1 := e1.[σ]) in *.
    set (es2 := e2.[σ]) in *.
    replace (expr_pair es1 es2) with (fill (LPairCtx EmptyCtx es2) es1) by auto.
    eapply safe_bind;eauto.
    intros ve1 Hsafe_ve1.
    simpl fill.
    assert (is_val ve1) by (by eapply safe_is_val).
    apply is_val_inversion in H2. destruct H2 as [v1 ->].
    replace (expr_pair (of_val v1) es2) with (fill (RPairCtx EmptyCtx v1) es2)
    by auto.
    eapply safe_bind;eauto.
    intros ve2 Hsafe_ve2.
    assert (is_val ve2) by (by eapply safe_is_val).
    apply is_val_inversion in H2. destruct H2 as [v2 ->].
    simpl fill.
    intros e' He'.
    assert (Hval_pair: (is_val (expr_pair (of_val v1) (of_val v2)))) by
    (constructor; apply is_val_of_val).
    apply is_val_step in He'; auto;subst.
    left. split; auto.
    simpl.
    (* split;[by eapply safe_domain; eassumption|split;auto]. *)
    exists (of_val v1). exists (of_val v2).
    repeat (split;auto using is_val_of_val).
  - (* T_Fst *)
    cbn.
    apply IHtyping_judgment in H0.
    replace (expr_fst (e.[σ]))
              with (fill (FstCtx EmptyCtx) (e.[σ])) by auto.
    eapply safe_bind;eauto .
    intros v Hrel.
    cbn in Hrel.
    destruct Hrel as (v1 & v2 & Hv1 & Hv2 & -> & Hrel1 & Hrel2).
    cbn.
    eapply safe_step with (e' := v1);auto.
    repeat intro.
    apply is_val_step in H1;subst;auto.
  - (* T_Snd *)
    cbn.
    apply IHtyping_judgment in H0.
    replace (expr_snd (e.[σ]))
              with (fill (SndCtx EmptyCtx) (e.[σ])) by auto.
    eapply safe_bind;eauto .
    intros v Hrel.
    cbn in Hrel.
    destruct Hrel as (v1 & v2 & Hv1 & Hv2 & -> & Hrel1 & Hrel2).
    cbn.
    eapply safe_step with (e' := v2);auto.
    repeat intro.
    apply is_val_step in H1;subst;auto.
  - (* T_Lam *)
    simpl subst.
    apply safe_val;[constructor|].
    exists (e.[up σ]).
    split; auto.
    intros e' Hsafe.
    pose proof Hsafe as Hval_e'.
    apply safe_is_val in Hval_e'.
    eapply safe_step with (e' := (e.[up σ].[e'/])) ; eauto.
    asimpl.
    eapply IHtyping_judgment.
    by apply logrel_context_cons.
  - (* T_App *)
    simpl subst.
    pose proof H1 as H1'.
    apply IHtyping_judgment1 in H1.
    apply IHtyping_judgment2 in H1'.
    set (fs := (f.[σ])) in *.
    set (arg := (e.[σ])) in *.
    replace (expr_app fs arg)
              with (fill (LAppCtx EmptyCtx arg) fs) by auto.
    eapply safe_bind;eauto .
    intros fv Hfv.
    simpl fill.
    assert (is_val fv) by (by eapply safe_is_val).
    apply is_val_inversion in H2. destruct H2 as [vf ->].
    replace (expr_app (of_val vf) arg) with (fill (RAppCtx EmptyCtx vf) arg)
    by auto.
    eapply safe_bind;eauto.
    intros argv Hargv.
    simpl fill.
    assert (is_val argv) by (by eapply safe_is_val).
    apply is_val_inversion in H2. destruct H2 as [v ->].
    destruct Hfv as (fe & -> & Hsafe_app).
    by apply Hsafe_app.
  - (* T_TLam *)
    simpl subst.
    apply safe_val; [constructor|cbn].
    eexists;split;[reflexivity|].
    intros.
    apply IHtyping_judgment.
    apply logrel_context_weaken;auto.
  - (* T_TApp *)
    simpl subst.
    apply IHtyping_judgment in H0.
    set (es := e.[σ]) in *.
    replace (expr_tapp es)
              with (fill (TAppCtx EmptyCtx) es) by auto.
    eapply safe_bind ;eauto.
    intros ev Hev.
    simpl fill.
    destruct Hev as (f & -> & Hsafe_app).
    eapply safe_step with (e' := f).
    eapply (Step _ _ EmptyCtx); eauto; econstructor.
    specialize (Hsafe_app (logrel_safe ξ τ')).
    eapply safe_mono.
    2: apply Hsafe_app.
    intros; by apply logrel_subst.
Qed.


Lemma logrel_context_nil:
  forall Γ,
  logrel_context Γ [] ids.
Proof.
  induction Γ.
  - intro; induction x;cbn;auto.
  - intro.
Admitted.

Theorem type_safety Γ e τ :
  Γ ⊢ e ∈ τ ->
  safe_parametrized (fun e => True) e.
Proof.
  intros.
  eapply safe_mono;[by intros|].
  Unshelve. 2: exact (logrel_safe [] τ).
  eapply fundamental_theorem with (ξ := nil) (σ := ids) in H
  ; asimpl in *; auto.
  apply logrel_context_nil.
Qed.


(** Free theorems *)

Lemma identity_function :
  forall e ev v, ev = (of_val v)
            -> [] ⊢ e ∈ <{ ∀ _ , (#0 -> #0) }>
            -> safe_parametrized (fun e => e = ev) <{ (e _ ) ev}>.
Proof.
  intros e ev v Hev Htyped.
  eapply fundamental_theorem with (ξ := nil) (σ := ids) in Htyped
  ;[| apply logrel_context_nil].
  replace e.[ids] with e in Htyped by (by asimpl).
  replace <{ e _ ev }> with (fill (LAppCtx (TAppCtx EmptyCtx) ev) e) by auto.
  eapply safe_bind;eauto.
  intros;cbn.
  destruct H as (f & -> & Hsafe).
  eapply safe_step.
  eapply Step with (K:= (LAppCtx EmptyCtx ev));eauto.
  specialize (Hsafe (λ e0 : expr, e0 = ev)).
  eapply safe_bind;eauto.
  intros fv Hsafe_fv;cbn.
  destruct Hsafe_fv as (fe & -> & Hsafe_fv).
  assert (logrel_safe [λ e0 : expr, e0 = ev] <{ # 0 }> ev)
  by (simpl;rewrite Hev ; split ; [apply is_val_of_val|reflexivity]).
  apply Hsafe_fv in H.
  simpl in H.
  eapply safe_mono; [|eassumption].
  intros; simpl in *;firstorder.
Qed.

Lemma empty_type :
  forall e, [] ⊢ e ∈ <{ ∀ _ , #0 }>
       -> safe_parametrized (fun e => False) <{ (e _ )}>.
Proof.
  intros e Htyped.
  eapply fundamental_theorem with (ξ := nil) (σ := ids) in Htyped
  ;[| apply logrel_context_nil].
  replace e.[ids] with e in Htyped by (by asimpl).
  replace <{ e _ }> with (fill (TAppCtx EmptyCtx ) e) by auto.
  eapply safe_bind;eauto.
  intros v (f & -> & Hsafe_f).
  specialize (Hsafe_f (fun e => False)).
  eapply safe_step.
  eapply Step with (K:= EmptyCtx) (e1' := <{ (Λ f) _ }>);eauto.
  simpl in *.
  eapply safe_mono; [|eassumption].
  intros; simpl in *;firstorder.
Qed.
