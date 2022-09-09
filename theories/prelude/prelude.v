From Coq.ssr Require Export ssreflect.
From stdpp Require Export prelude.
From iris.prelude Require Import options.
Global Open Scope general_if_scope.
Global Set SsrOldRewriteGoalsOrder. (* See Coq issue #5706 *)
Ltac done := stdpp.tactics.done.


(** Iris itself and many dependencies still rely on this coercion. *)
Coercion Z.of_nat : nat >-> Z.




(* some basic definitions and lemmas *)
Inductive rc {A} (R: A → A → Prop) (x: A) (y: A):  Prop :=
| rc_refl: x = y → rc R x y
| rc_subrel: R x y → rc R x y.
Global Hint Constructors rc : core.

Global Instance rc_reflexive {A} (R : A → A → Prop) : Reflexive (rc R).
Proof. intros ?; by apply rc_refl. Qed.
Global Instance rc_subrelation {A} (R : A → A → Prop): subrelation R (rc R).
Proof. intros ? ? ?; by apply rc_subrel. Qed.

Lemma rc_iff {A} (R: A → A → Prop) x y: rc R x y ↔ R x y ∨ x = y.
Proof.
  split; destruct 1; eauto.
Qed.

Global Instance rc_transitive {A} (R: A → A → Prop) `{!Transitive R}: Transitive (rc R).
Proof.
  intros x y z [] []; subst; eauto.
Qed.



(* this is not classical, but useful *)
Lemma ex_impl X (P: X → Prop) (Q: Prop): ((∃ x, P x) → Q) ↔ ∀ x, P x → Q.
Proof.
  split.
  - intros H x Px; eapply H; by exists x.
  - intros HPQ [x Px]; eauto.
Qed.