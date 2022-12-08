Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From stdpp Require Import list relations.
Require Import Autosubst.Autosubst.
From logical_relation Require Import syntax_systemF opsem_systemF_ctx logrel.

(*** Free theorems *)

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
