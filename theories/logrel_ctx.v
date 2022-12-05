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
                        safe_parametrized (logrel_safe ξ t2) (<{e v'}>))
    | Ty_Forall t =>
        exists e, v = <{ Λ e }>
             /\ forall (P: expr -> Prop), safe_parametrized (logrel_safe (P :: ξ) t) e
end.

Lemma safe_is_val ξ v τ : logrel_safe ξ τ v -> is_val v.
Proof.
  induction τ; simpl ; intros; try destruct H as (?&?);auto.
  - subst; constructor.
  - destruct H as (?&?&?&?&?); subst; by constructor.
  - destruct H as (?&?); subst; by constructor.
  - destruct H as (?&?); subst; by constructor.
Qed.

Lemma logrel_subst ξ τ τ' v :
  (logrel_safe ξ τ.[τ'/] v )
  <-> (logrel_safe ((logrel_safe ξ τ')::ξ) τ v).
Proof.
  generalize dependent τ'.
  generalize dependent v.
  generalize dependent ξ.
  induction τ; intros *.
  + (* var *)
    rename v into x.
    rename v0 into v.
    admit.
  + (* unit *)
    auto; tauto.
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
    split; intros [? Hsafe];simpl
    ; destruct Hsafe as (-> & Hsafe)
    ; exists x; split; auto;intros.
    all: eapply safe_mono;[intros|eapply (Hsafe P)].
    admit.
    admit.
Admitted.

(* Lemma logrel_weaken ξ τ v P : *)
(*   not (free α τ) -> *)
(*   ((logrel_safe Δ ξ τ v) <-> *)
(*   (logrel_safe Δ  (<[α := P]> ξ) τ v)). *)
(* Proof. *)
(*   split; intros Hsafe; *)
(*   generalize dependent v; *)
(*   induction τ; intros; simpl in *; *)
(*   destruct Hsafe as (Hdom & Hval & Hsafe). *)
(*   - (* Var *) *)
(*     split; [|split]; auto. *)
(*     destruct (decide (α = s)%string); subst. *)
(*     exfalso; apply H; apply free_var. *)
(*     admit. *)
(*     unfold not in H. *)
(*     destruct (decide (α = s)%string); subst. *)
(*     + (* \alpha = s --> contradiction with free *) *)
(*       exfalso; apply H; apply free_var. *)
(*     + replace (<[α:=P]> ξ !! s) with (ξ !! s) *)
(*     by (symmetry ; apply lookup_insert_ne;auto). *)
(*     auto. *)
(*   - split;[admit|];auto. *)
(*   - split;[admit|split];auto. *)
(*     destruct Hsafe as (v1 & v2 & Hv1 & Hv2 & Hv& Hsafe1 & Hsafe2). *)
(*     exists v1, v2. *)
(*     repeat(split;auto). *)
(*     apply IHτ1;auto; intro; apply H; by apply free_pair1. *)
(*     apply IHτ2;auto; intro; apply H; by apply free_pair2. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(* Admitted. *)

(* TODO better way to define the sequence ? *)
(* Fixpoint logrel_seq_list Δ (lΓ : list (string*ty))  ξ (vs : list expr) : Prop := *)
(*   match lΓ with *)
(*   | nil => List.length vs = 0 *)
(*   | (x,τ)::Γ' => *)
(*       exists v vs', vs = v::vs' *)
(*                /\ logrel_safe Δ ξ τ v *)
(*                /\ logrel_seq_list Δ Γ' ξ vs' *)
(*   end. *)
(* Require Import Coq.Program.Wf. *)
(* Program Fixpoint logrel_seq Δ Γ ξ (vs : list expr) *)
(*   {measure (List.length (map_to_list Γ))} : Prop := *)
(*   forall x τ, Γ !! x = Some τ -> *)
(*          exists v vs', vs = v::vs' *)
(*                   /\ logrel_safe Δ ξ τ v *)
(*                   /\ logrel_seq Δ (delete x Γ) ξ vs'. *)
(* Next Obligation. *)
(*   intros. *)
(*   setoid_rewrite <- map_to_list_delete. *)

(* Definition logrel_seq Δ Γ ξ (vs : list expr) := *)
(*   logrel_seq_list Δ (map_to_list Γ) ξ vs. *)

(* Lemma logrel_seq_weaken Δ Γ ξ P vs α : *)
(* not_free_context α Γ -> *)
(* ( logrel_seq Δ Γ ξ vs *)
(*  <-> *)
(*   logrel_seq ({[α]} ∪ Δ) Γ (<[α := P]>ξ) vs *)
(* ). *)
(* Proof. *)
(*   intros. *)
(*   split; intros. *)
(*   - generalize dependent Δ. *)
(*     generalize dependent ξ. *)
(*     generalize dependent α. *)
(*     generalize dependent P. *)
(*     generalize dependent vs. *)
(*     induction Γ using map_ind *)
(*     ; intros *)
(*     ; unfold logrel_seq in *. *)
(*     + setoid_rewrite map_to_list_empty in H0. *)
(*       setoid_rewrite map_to_list_empty. *)
(*       by cbn in *. *)
(*     + admit. *)
(*       (* setoid_rewrite map_to_list_insert. *) *)
(*       (* apply IHΓ. *) *)
(* Admitted. *)


(* Definition context_var Γ : list string := *)
(*   map (fun x => match x with (x1,x2) => x1 end) (gmap_to_list Γ). *)
(*   (* (gmap_to_list Γ).*1 . *) *)

(* Lemma subst_term_seq_insert e : *)
(*   forall Γ vs x τ v, *)
(*   (subst_term_seq (context_var (<[x:=τ]> Γ)) (v :: vs) e) = *)
(*     subst_term x v (subst_term_seq (context_var Γ) (vs) e). *)
(* Proof. *)
(*   induction e; intros ; auto; cbn. *)
(*   - (* var *) *)
(*     induction Γ using map_ind. *)
(*     + replace (context_var (<[x:=τ]> ∅)) with [x]. *)
(*       replace (context_var ∅) with ([] : list string). *)
(*       reflexivity. *)
(*       unfold context_var. *)
(*       (* rewrite map_to_list_empty. *) *)
(*       admit. *)
(*       admit. *)
(*     + admit. *)
(*   - (* pair *) *)
(*     by rewrite IHe1, IHe2. *)
(*   - (* fst *) *)
(*     by rewrite IHe. *)
(*   - (* snd *) *)
(*     by rewrite IHe. *)
(*   - (* app *) *)
(*     by rewrite IHe1, IHe2. *)
(*   - (* abs *) *)
(*     rewrite IHe. *)
(*     (* TODO do I miss an hypothesis about Γ ? *) *)
(*     (* destruct (decide (s = x)); subst. *) *)
(*     (* + (* s = x*) *) *)
(*     admit. *)

(*   - (* tapp *) *)
(*     by rewrite IHe. *)
(*   - (* tabs *) *)
(*     by rewrite IHe. *)
(* Admitted. *)

(* Lemma logrel_safe_list_dom: forall Δ Γ ξ vs, *)
(*   logrel_seq Δ Γ ξ vs -> dom ξ = Δ. *)
(* Admitted. *)

(* Lemma var_safe : *)
(*   forall Γ Δ ξ vs x τ, *)
(*   Γ !! x = Some τ -> *)
(*   logrel_seq Δ Γ ξ vs -> *)
(*   safe_parametrized (logrel_safe Δ ξ τ) (replace_var (context_var Γ) vs x x). *)
(* Proof. *)
(*   intros. *)
(*   induction Γ using map_ind. *)
(*   + exfalso. *)
(*     by eapply lookup_empty_is_Some; eexists. *)
(*   + unfold logrel_seq, logrel_seq_list in H0. cbn in H0. *)

(*     destruct ( strings.string_eq_dec i x). *)
(*     - admit. *)
(*     - setoid_rewrite lookup_insert_ne in H; auto. *)
(* Admitted. *)

Theorem fundamental_theorem :
  forall Γ τ e ,
  Γ ⊢ e ∈ τ ->
  (forall ξ vs, logrel_safe Γ ξ vs -> safe_parametrized (logrel_safe ξ τ) e.[vs/]).
Proof.
  induction 1; intros.
  - (* T_Unit *)
    apply safe_val; auto.
    simpl in * ; split ; auto.
    by eapply logrel_safe_list_dom.
  - (* T_Var *)
    cbn.
    apply var_safe; auto.
  - (* T_Prod *)
    pose proof H1 as H1'.
    apply IHtyping_judgment1 in H1.
    apply IHtyping_judgment2 in H1'.
    simpl subst_term_seq.
    set (e1' := (subst_term_seq (context_var Γ) vs e1) ) in *.
    set (e2' := (subst_term_seq (context_var Γ) vs e2) ) in *.
    replace (expr_pair e1' e2') with (fill (LPairCtx EmptyCtx e2') e1') by auto.
    eapply safe_bind;eauto.
    intros ve1 Hsafe_ve1.
    simpl fill.
    assert (is_val ve1) by (by eapply safe_is_val).
    apply is_val_inversion in H2. destruct H2 as [v1 ->].
    replace (expr_pair (of_val v1) e2') with (fill (RPairCtx EmptyCtx v1) e2')
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
    split;[by eapply safe_domain; eassumption|split;auto].
    exists (of_val v1). exists (of_val v2).
    repeat (split;auto using is_val_of_val).
  - (* T_Fst *)
    cbn.
    apply IHtyping_judgment in H0.
    replace (expr_fst (subst_term_seq (context_var Γ) vs e))
              with (fill (FstCtx EmptyCtx) (subst_term_seq (context_var Γ) vs e)) by auto.
    eapply safe_bind;eauto .
    intros v Hrel.
    cbn in Hrel.
    destruct Hrel as (Hdom & Hval & v1 & v2 & Hv1 & Hv2 & -> & Hrel1 & Hrel2).
    cbn.
    eapply safe_step with (e' := v1);auto.
    repeat intro.
    apply is_val_step in H1;subst;auto.
  - (* T_Snd *)
    cbn.
    apply IHtyping_judgment in H0.
    replace (expr_snd (subst_term_seq (context_var Γ) vs e))
              with (fill (SndCtx EmptyCtx) (subst_term_seq (context_var Γ) vs e)) by auto.
    eapply safe_bind;eauto .
    intros v Hrel.
    cbn in Hrel.
    destruct Hrel as (Hdom & Hval & v1 & v2 & Hv1 & Hv2 & -> & Hrel1 & Hrel2).
    cbn.
    eapply safe_step with (e' := v2);auto.
    repeat intro.
    apply is_val_step in H1;subst;auto.
  - (* T_Lam *)
    apply safe_val.
    { simpl.
      destruct (find (String.eqb x) (context_var Γ)); constructor. }
    split; eauto using logrel_safe_list_dom.
    split;[simpl;destruct (find (String.eqb x) (context_var Γ)); constructor|].
    destruct (find (String.eqb x) (context_var Γ)) eqn:Heq.
    + simpl. rewrite Heq.
      eexists;eexists;split;eauto.
      intros.
      assert (logrel_seq Δ (<[x:= τ1]>Γ) ξ (v'::vs)).
      { unfold logrel_seq.
        admit.
      }
      apply IHtyping_judgment in H2. admit.
    + simpl. rewrite Heq.
      eexists;eexists;split;eauto.
      intros.
      assert (logrel_seq Δ (<[x:= τ1]>Γ) ξ (v'::vs)).
      { unfold logrel_seq.
        admit.
      }
      apply IHtyping_judgment in H2.
      admit.
  - (* T_App *)
    simpl subst_term_seq.
    pose proof H1 as H1'.
    apply IHtyping_judgment1 in H1.
    apply IHtyping_judgment2 in H1'.
    set (fs := (subst_term_seq (context_var Γ) vs e)) in *.
    set (arg := (subst_term_seq (context_var Γ) vs e')) in *.
    replace (expr_app fs arg)
              with (fill (LAppCtx EmptyCtx arg) fs) by auto.
    eapply safe_bind;eauto .
    intros fv Hfv.
    simpl fill.
    assert (is_val fv) by (by eapply safe_is_val).
    apply is_val_inversion in H2. destruct H2 as [f ->].
    replace (expr_app (of_val f) arg) with (fill (RAppCtx EmptyCtx f) arg)
    by auto.
    eapply safe_bind;eauto.
    intros argv Hargv.
    simpl fill.
    assert (is_val argv) by (by eapply safe_is_val).
    apply is_val_inversion in H2. destruct H2 as [v ->].
    destruct Hfv as (Hdom & Hvalf & x & fe & -> & Hsafe_app).
    eapply safe_step with (e' := subst_term x (of_val v) fe).
    eapply (Step _ _ EmptyCtx); eauto; econstructor. apply is_val_of_val.
    by apply Hsafe_app.
  - (* T_TLam *)
    simpl subst_term_seq.
    apply safe_val; [constructor|cbn].
    split; eauto using logrel_safe_list_dom.
    split;[constructor|].
    eexists;split;[reflexivity|].
    intros.
    apply IHtyping_judgment.
    apply logrel_seq_weaken;auto.
  - (* T_TApp *)
    simpl subst_term_seq.
    apply IHtyping_judgment in H0.
    set (es := (subst_term_seq (context_var Γ) vs e)) in *.
    replace (expr_tapp es)
              with (fill (TAppCtx EmptyCtx) es) by auto.
    eapply safe_bind ;eauto.
    intros ev Hev.
    simpl fill.
    destruct Hev as (Hdom & Hvalv & f & -> & Hsafe_app).
    eapply safe_step with (e' := f).
    eapply (Step _ _ EmptyCtx); eauto; econstructor.
    specialize (Hsafe_app (logrel_safe Δ ξ τ')).
    eapply safe_mono.
    2: apply Hsafe_app.
    intros; by apply logrel_subst.
Admitted.
