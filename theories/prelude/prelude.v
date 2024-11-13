From iris.prelude Require Export prelude.
From iris.prelude Require Import options.
Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.

(* some basic definitions and lemmas
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
Qed. *)



(* this is not classical, but useful *)
Lemma ex_impl X (P: X → Prop) (Q: Prop): ((∃ x, P x) → Q) ↔ ∀ x, P x → Q.
Proof.
  split.
  - intros H x Px; eapply H; by exists x.
  - intros HPQ [x Px]; eauto.
Qed.



(* some classical reasoning principles *)
Lemma classic_or_to_sum (P Q : Prop) : P ∨ Q → P + Q.
Proof.
  intros HPQ. assert (exists (b : bool), if b then P else Q) as Hex.
  { destruct HPQ; by [exists true|exists false]. }
  apply constructive_indefinite_description in Hex as [[] ?]; eauto.
Qed.

Lemma classic_dn (X : Prop) : ¬ (¬ X) ↔ X.
Proof.
  destruct (classic X); tauto.
Qed.

Lemma classic_forall_exists_dn (X : Type) (P : X → Prop): (∀ x, P x) ↔ ¬ (∃ x, ¬ (P x)).
Proof.
  split.
  - intros H (x & H1). eauto.
  - intros H x. destruct (classic (P x)) as [| ?]; first done.
    exfalso; apply H; eauto.
Qed.

Lemma classic_not_forall X (P: X → Prop): ¬ (∀ x: X, P x) ↔ ∃ x: X, ¬ P x.
Proof.
  by rewrite classic_forall_exists_dn classic_dn.
Qed.

Lemma classic_not_exists X (P: X → Prop): ¬ (∃ x: X, P x) ↔ ∀ x: X, ¬ P x.
Proof.
  by rewrite classic_forall_exists_dn; split; intros H [x ?]; eauto using classic_dn.
Qed.

Lemma classic_not_impl (P Q: Prop): ¬ (P → Q) ↔ P ∧ ¬ Q.
Proof.
  destruct (classic P); tauto.
Qed.

Lemma classic_find_least {X: Type} (R: X → X → Prop) (P: X → Prop) x:
  well_founded R →
  (∀ x y, R x y → P x → P y) →
  P x →
  ∃ y, P y ∧ ∀ x, R x y → ¬ P x.
Proof.
  intros Hwf HP. induction (Hwf x) as [x _ IH].
  intros Hx. destruct (classic (∀ y, R y x → ¬ P y)) as [|Hn]; first by eauto.
  revert Hn; rewrite classic_not_forall=> [[y]]; rewrite classic_not_impl classic_dn.
  intros []; eauto.
Qed.


(* we use classical logic to define a normalizer function
  for building quotients *)
Section quotients.

  Context {X: Type} (R: X → X → Prop) `{Equivalence X R}.
  Definition norm (x: X) := epsilon (inhabits x) (R x).

  Lemma rel_norm x y: R x y → norm x = norm y.
  Proof using Type*.
    intros HR; unfold norm; f_equal.
    - apply proof_irrelevance.
    - eapply functional_extensionality; intros u; eapply propositional_extensionality.
      by rewrite HR.
  Qed.

  Lemma norm_pi s (Hq Hq': norm s = s): Hq = Hq'.
  Proof.
    apply proof_irrelevance.
  Qed.

  Lemma rel_norm_intro x: R x (norm x).
  Proof using Type*.
    unfold norm; eapply epsilon_spec; exists x; reflexivity.
  Qed.

  (* derived lemmas *)
  Lemma norm_idem x: norm (norm x) = norm x.
  Proof using Type*.
    eapply rel_norm; symmetry; eapply rel_norm_intro.
  Qed.

  Lemma norm_rel x y: norm x = norm y → R x y.
  Proof using Type*.
    by intros Heq; rewrite (rel_norm_intro x) (rel_norm_intro y) Heq.
  Qed.

  Lemma norm_iff x y: norm x = norm y ↔ R x y.
  Proof using Type*.
    split; eauto using rel_norm, norm_rel.
  Qed.

  Global Instance norm_proper : Proper (R ==> R) norm.
  Proof using Type*.
    intros x y HR. by rewrite -(rel_norm_intro x) -(rel_norm_intro y).
  Qed.

End quotients.
