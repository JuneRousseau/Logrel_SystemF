Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap list.
Require Import Autosubst.Autosubst.
From logical_relation Require Export relation.
From logical_relation Require Import syntax_systemF opsem_systemF_ctx.

(*** Logical relation for type
     soundness of SystemF *)

Implicit Types Γ : typing_context.
Implicit Types τ : ty.

Definition subst_interpretation := list (expr -> Prop).
Implicit Types ξ : subst_interpretation.

Definition substitution := list expr.
Implicit Types γ : substitution.

(* We can turn the substitution γ into a function from variables
   to expression *)
Fixpoint fun_subst (γ : substitution) : var → expr :=
  match γ with
  | [] => ids
  | e::γ' => e .: fun_subst γ'
  end.

Lemma env_subst_get :
  forall γ x e, get γ x = Some e → fun_subst γ x = e.
Proof.
  induction γ; intros * Hsome;simpl in *.
  - induction x;cbn in Hsome;discriminate.
  - destruct x;cbn in *.
    + by injection Hsome.
    + by apply IHγ.
Qed.

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

(** ξ is a name, ie. it is a function that maps a variable to
    an expression property. *)
Fixpoint logrel_val ξ τ v :=
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
                 /\ logrel_val ξ t1 e1
                 /\ logrel_val ξ t2 e2
    | Ty_Arrow t1 t2 =>
        exists e, v = <{ λ _, e }>
               /\ (forall v', logrel_val ξ t1 v' ->
                        safe_parametrized (logrel_val ξ t2) (<{v v'}>))
    | Ty_Forall t =>
        exists e, v = <{ Λ e }>
             /\ forall (P: expr -> Prop), safe_parametrized (logrel_val (P :: ξ) t) e
end.

Notation "V[ ξ ]" := (logrel_val ξ) (at level 0, format "V[ ξ ]").

(** We define the semantic substitution.
We say that the substitution γ satisfies the typing context Γ. *)
Definition sem_subst P γ Γ : Prop := Forall2 P Γ γ.
Notation "γ '⊨(' P ')' Γ" := (sem_subst P γ Γ) (at level 0, format "γ '⊨(' P ')' Γ").

Lemma safe_is_val ξ v τ :
  logrel_val ξ τ v -> is_val v.
Proof.
  induction τ; simpl ; intros; try destruct H as (?&?);auto.
  - subst; constructor.
  - destruct H as (?&?&?&?&?); subst; by constructor.
  - destruct H as (?&?); subst; by constructor.
  - destruct H as (?&?); subst; by constructor.
Qed.

(* If γ satisfies Γ, and the variable x is in Γ, then
   x is also in γ, and respect the right property *)
Lemma get_sem_subst:
  forall P Γ γ (x : var) τ,
  γ ⊨(P) Γ ->
  get Γ x = Some τ ->
  exists e, get γ x = Some e /\ P τ e.
Proof.
  intros.
  revert x τ H0.
  induction H; intros * HsomeΓ.
  - destruct x;cbn in HsomeΓ;discriminate.
  - destruct x0;cbn in *;eauto.
    eexists;split;eauto.
    by injection HsomeΓ;intros;subst.
Qed.

Lemma sem_subst_cons_r_inv P Γ γ τ :
  (γ ⊨(P) (τ::Γ)) ->
  exists e γ', γ = (e::γ')
          /\ P τ e
          /\ (γ' ⊨(P) Γ).
Proof.
  inversion 1;eauto.
Qed.

Lemma sem_subst_cons_l_inv P Γ γ e :
  ((e::γ) ⊨(P) Γ) ->
  exists τ Γ', Γ = (τ::Γ')
          /\ P τ e
          /\ (γ ⊨(P) Γ').
Proof.
  inversion 1;eauto.
Qed.

Lemma sem_subst_cons P Γ γ e τ:
  (γ ⊨(P) Γ)
  → P τ e
  → ((e::γ) ⊨(P) (τ :: Γ)).
Proof.
  intros * Hcontext Hsafe; by constructor.
Qed.

Lemma upn_lt n (f : var -> ty) x :
  x < n ->
  upn n f x = ids x.
Proof.
  revert f x.
  induction n;intros.
  - lia.
  - destruct x; asimpl;auto.
    apply Nat.succ_lt_mono in H.
    apply (IHn f) in H.
    rewrite H.
    by asimpl.
Qed.

Lemma upn_ge n (f : var -> ty) x :
  x >= n ->
  upn n f x = (f (x - n)).[ren (+n)].
Proof.
  revert f x.
  induction n;intros.
  - replace (x-0) with x by lia.
    asimpl; auto.
  - destruct x; asimpl;auto;try lia.
    assert (x >= n) by lia.
    apply (IHn f) in H0.
    rewrite H0.
    by asimpl.
Qed.




Lemma logrel_val_weaken_generalized :
  forall ξ ξ1 ξ2 τ e,
  logrel_val (ξ1 ++ ξ2) τ e ↔
  logrel_val (ξ1 ++ ξ ++ ξ2) (τ.[upn (length ξ1) (ren (+ (length ξ)))]) e.
Proof.
  intros * ; revert ξ ξ1 ξ2 e.
  induction τ;intros.
  - (* Var *)
    asimpl.
    rename v into x.
    destruct (dec_lt x (length ξ1)) as [Hx|Hx].
    + (* x is in ξ1 *)
      pose proof Hx as H; eapply upn_lt in H; erewrite H;clear H.
      replace (ids x) with (Ty_Var x);auto;cbn.
      rewrite !nth_error_app1;eauto.
    + (* x is not in ξ1 *)
      apply not_lt in Hx.
      pose proof Hx as H; eapply upn_ge in H; erewrite H;clear H.
      apply le_lt_or_eq in Hx.
      destruct Hx as [Hx | Hx] ;cycle 1.
      * (* x is exactly after ξ1, ie it gets τ' *)
        rewrite nth_error_app2;[|lia].
        subst.
        rewrite Nat.sub_diag;asimpl.
        replace (ids (length ξ1 + length ξ)) with (Ty_Var (length ξ1 + length ξ));auto;cbn.
        rewrite nth_error_app2;[|lia].
        rewrite nth_error_app2;[|lia].
        replace (length ξ1 + length ξ - length ξ1 - length ξ) with 0 by lia.
        firstorder.
      * (* x is in ξ2 *)
        cbn.
        rewrite nth_error_app2;[|lia].
        destruct (x - length ξ1) eqn:contra;try lia;clear contra.
        match goal with
        | h: _ |- _ <-> V[_] ?t e =>
            replace t with (Ty_Var (S (length ξ1 + length ξ + n))) by (asimpl;auto)
        end.
        destruct (list_eq_nil_dec (ξ1 ++ ξ ++ ξ2)) as [Heq|Hneq].
        ** rewrite Heq
           ; apply app_eq_nil in Heq
           ; destruct Heq as [_ Heq]
           ; apply app_eq_nil in Heq
           ; destruct Heq as [_ Heq]; subst; auto.
        ** unfold logrel_val.
        rewrite nth_error_app2;[|lia].
        rewrite nth_error_app2;[|lia].
        replace (S (length ξ1 + length ξ + n) - length ξ1 - length ξ)
          with (S n) by lia.
        firstorder.
  - (* Unit *) by cbn in *.
  - (* Pair *) cbn in *.
    split;intros H
    ; destruct H as (e1&e2&Hval1&Hval2&->&Hsafe1&Hsafe2)
    ; eapply IHτ1 in Hsafe1
    ; eapply IHτ2 in Hsafe2
    ; exists e1, e2; repeat(split;eauto).
  - (* Arrow *)
    cbn in *.
    split; intros H
    ; destruct H as (e'& ->& Hsafe)
    ; exists e'; split;auto
    ; intros
    ; eapply safe_mono
    ; match goal with
      | h: _ |- safe_parametrized _ _ => eapply Hsafe
      | h: _ |- _ => idtac
    end
    ; intros
    ; try (by eapply IHτ1)
    ; try (by eapply IHτ2).
  - (* Forall *)
    cbn in *.
    split; intros H
    ; destruct H as (e'&->&Hsafe) ; exists e'
    ; split;auto
    ; intros
    ; eapply safe_mono
    ; match goal with
      | h: _ |- safe_parametrized _ _ => eapply Hsafe
      | h: _ |- _ => idtac
    end
    ; intros
    ; specialize (IHτ ξ (P::ξ1) ξ2 e); asimpl in *
    ; by eapply IHτ.
Qed.

Lemma logrel_val_weaken ξ1 ξ2 τ e :
  logrel_val ξ2 τ e <->
  logrel_val (ξ1++ξ2) τ.[ren (+length ξ1)] e.
Proof.
  erewrite (logrel_val_weaken_generalized ξ1 nil ξ2 _ e); simpl; by asimpl.
Qed.

(* The renaming ensures that the type does not appears free *)
Lemma logrel_val_weaken' ξ τ e P :
  logrel_val ξ τ e <->
  logrel_val (P :: ξ) (rename (+1) τ) e.
Proof.
  asimpl in *; apply (logrel_val_weaken [P] ξ τ e).
Qed.

Lemma logrel_subst_generalized τ :
  forall ξ1 ξ2 τ' v,
  (logrel_val (ξ1++ξ2) τ.[upn (length ξ1) (τ'.: ids)] v)
  <-> (logrel_val (ξ1 ++ (logrel_val ξ2 τ')::ξ2) τ v).
Proof.
  induction τ; intros *.
  + (* var *)
    rename v into x.
    rename v0 into v.
    asimpl.
    destruct (dec_lt x (length ξ1)) as [Hx|Hx].
    - (* x is in ξ1 *)
      pose proof Hx as H; eapply upn_lt in H; erewrite H;clear H.
      replace (ids x) with (Ty_Var x);auto;cbn.
      unfold get.
      rewrite nth_error_app1;eauto.
      rewrite nth_error_app1;eauto.
    - (* x is not in ξ1 *)
      apply not_lt in Hx.
      pose proof Hx as H; eapply upn_ge in H; erewrite H;clear H.
      apply le_lt_or_eq in Hx.
      destruct Hx as [Hx | Hx] ;cycle 1.
      * (* x is exactly after ξ1, ie it gets τ' *)
        rewrite nth_error_app2;[|lia].
        subst.
        rewrite Nat.sub_diag;asimpl.
        rewrite <- logrel_val_weaken.
        firstorder. by eapply safe_is_val.
      * (* x is in ξ2 *)
        cbn.
        rewrite nth_error_app2;[|lia].
        destruct (x - length ξ1) eqn:contra;try lia;clear contra.
        asimpl in *.
        replace (V[ξ1 ++ ξ2] (ids (length ξ1 + n)) v)
          with (is_val v ∧
                  match nth_error (ξ1 ++ ξ2) (length ξ1 + n) with
                  | Some P => P v
                  | None => True
                  end) by auto.
        rewrite nth_error_app2;[|lia].
        replace (length ξ1 + n - length ξ1) with n by lia.
        auto.
  + (* Unit *) auto.
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
Qed.


(* Cannot be done naively: the induction hypothesis for type lambda abstraction
   is not strong enough ! *)
Lemma logrel_subst ξ τ τ' v :
  (logrel_val ξ τ.[τ'/] v )
  <-> (logrel_val ((logrel_val ξ τ')::ξ) τ v).
Proof.
  apply logrel_subst_generalized with (ξ1 := nil).
Qed.

Lemma sem_subst_weaken :
  forall ξ Γ γ P,
  (γ ⊨(V[ξ]) Γ) ->
  (γ ⊨(V[P::ξ]) (map (rename (+1)) Γ)).
Proof.
  intros.
  generalize dependent γ.
  induction Γ;intros.
  - by inversion H; subst; apply Forall2_nil.
  - apply sem_subst_cons_r_inv in H.
    destruct H as (e & σ' & -> & Hsafe & Hcontext).
    apply sem_subst_cons;auto.
    by apply logrel_val_weaken'.
Qed.


Theorem fundamental_theorem :
  forall Γ τ e ,
  Γ ⊢ e ∈ τ ->
  (forall ξ γ,
     γ ⊨(V[ξ]) Γ
     -> safe_parametrized (logrel_val ξ τ) e.[fun_subst γ]).
Proof.
  induction 1; intros; set (fγ := fun_subst γ).
  - (* T_Unit *)
    apply safe_val; auto.
    simpl in * ; split ; auto.
  - (* T_Var *)
    cbn.
    eapply get_sem_subst in H;eauto.
    destruct H as (e& ? & Hsafe).
    replace (fγ x) with e by (by symmetry; apply env_subst_get).
    assert (Hval: is_val e) by (by eapply safe_is_val).
    apply safe_val;auto.
  - (* T_Prod *)
    simpl subst.
    pose proof H1 as H1'.
    apply IHtyping_judgment1 in H1.
    apply IHtyping_judgment2 in H1'.
    set (es1 := e1.[fγ]) in *.
    set (es2 := e2.[fγ]) in *.
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
    exists (of_val v1). exists (of_val v2).
    repeat (split;auto using is_val_of_val).
  - (* T_Fst *)
    cbn.
    apply IHtyping_judgment in H0.
    replace (expr_fst (e.[fγ]))
              with (fill (FstCtx EmptyCtx) (e.[fγ])) by auto.
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
    replace (expr_snd (e.[fγ]))
              with (fill (SndCtx EmptyCtx) (e.[fγ])) by auto.
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
    exists (e.[up fγ]).
    split; auto.
    intros e' Hsafe.
    pose proof Hsafe as Hval_e'.
    apply safe_is_val in Hval_e'.
    eapply safe_step with (e' := (e.[up fγ].[e'/])) ; eauto.
    subst fγ; asimpl.
    Unset Printing Notations.
    apply (sem_subst_cons V[ξ] Γ γ e' τ1) in H0;auto.
    by apply IHtyping_judgment in H0;cbn in H0.
  - (* T_App *)
    simpl subst.
    pose proof H1 as H1'.
    apply IHtyping_judgment1 in H1.
    apply IHtyping_judgment2 in H1'.
    set (fs := (f.[fγ])) in *.
    set (arg := (e.[fγ])) in *.
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
    apply sem_subst_weaken;auto.
  - (* T_TApp *)
    simpl subst.
    apply IHtyping_judgment in H0.
    set (es := e.[fγ]) in *.
    replace (expr_tapp es)
              with (fill (TAppCtx EmptyCtx) es) by auto.
    eapply safe_bind ;eauto.
    intros ev Hev.
    simpl fill.
    destruct Hev as (f & -> & Hsafe_app).
    eapply safe_step with (e' := f).
    eapply (Step _ _ EmptyCtx); eauto; econstructor.
    specialize (Hsafe_app (logrel_val ξ τ')).
    eapply safe_mono.
    2: apply Hsafe_app.
    intros; by apply logrel_subst.
Qed.

Theorem type_safety e τ :
  [] ⊢ e ∈ τ ->
  safe_parametrized (fun e => True) e.
Proof.
  intros.
  eapply safe_mono;[by intros|].
  Unshelve. 2: exact (logrel_val [] τ).
  eapply fundamental_theorem with (ξ := nil) (γ := nil) in H
  ; asimpl in *; auto; constructor.
Qed.

(** Free theorems *)

Lemma identity_function :
  forall e ev v, ev = (of_val v)
            -> [] ⊢ e ∈ (∀ _ , ($0 -> $0))
            -> safe_parametrized (fun e => e = ev) <{ (e _ ) ev}>.
Proof.
  intros e ev v Hev Htyped.
  eapply fundamental_theorem with (ξ := nil) (γ := nil) in Htyped
  ;[| constructor].
  replace e.[fun_subst []] with e in Htyped by (by asimpl).
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
  assert (logrel_val [λ e0 : expr, e0 = ev] <{{$ 0}}> ev)
  by (simpl;rewrite Hev ; split ; [apply is_val_of_val|reflexivity]).
  apply Hsafe_fv in H.
  simpl in H.
  eapply safe_mono; [|eassumption].
  intros; simpl in *;firstorder.
Qed.

Lemma empty_type :
  forall e, [] ⊢ e ∈ ( ∀ _ , $0 )
       -> safe_parametrized (fun e => False) <{ (e _ )}>.
Proof.
  intros e Htyped.
  eapply fundamental_theorem with (ξ := nil) (γ:= nil) in Htyped
  ;[| constructor].
  replace e.[fun_subst []] with e in Htyped by (by asimpl).
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
