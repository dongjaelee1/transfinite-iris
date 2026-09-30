From iris.algebra Require Import proofmode_classes.
From iris.proofmode Require Import classes.
From transfinite.base_logic Require Export derived.
From iris.prelude Require Import options.
Import base_logic.bi.uPred.

(* Setup of the proof mode *)
Section class_instances.
  Context {SI : sidx} {M : ucmra}.
  Implicit Types P Q R : uPred M.

  Global Instance from_sep_ownM (a b1 b2 : M) :
    IsOp a b1 b2 →
    FromSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
  Proof. intros. by rewrite /FromSep -ownM_op -is_op. Qed.
  (* TODO: Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_ownM (a b1 b2 : M) :
    IsOp a b1 b2 →
    CombineSepAs (uPred_ownM b1) (uPred_ownM b2) (uPred_ownM a) | 60.
  Proof. intros. by rewrite /CombineSepAs -ownM_op -is_op. Qed.
  (* TODO: Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_ownM (b1 b2 : M) :
    CombineSepGives (uPred_ownM b1) (uPred_ownM b2) (✓ (b1 ⋅ b2)).
  Proof.
    intros. rewrite /CombineSepGives -ownM_op ownM_valid.
    by apply: bi.persistently_intro.
  Qed.
  Global Instance from_sep_ownM_core_id (a b1 b2 : M) :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
  Proof.
    intros ? H. rewrite /FromAnd (is_op a) ownM_op.
    destruct H; by rewrite bi.persistent_and_sep.
  Qed.

  Global Instance into_and_ownM p (a b1 b2 : M) :
    IsOp a b1 b2 → IntoAnd p (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
  Proof.
    intros. apply bi.intuitionistically_if_mono. by rewrite (is_op a) ownM_op bi.sep_and.
  Qed.

  Global Instance into_sep_ownM (a b1 b2 : M) :
    IsOp a b1 b2 → IntoSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
  Proof. intros. by rewrite /IntoSep (is_op a) ownM_op. Qed.

  (** Upstream's instances [into_or_later] and [into_or_laterN] require
  [SIdxFinite] (for [bi.later_or]). For [uPred], [later_or] holds at any
  step-index type, so (as in the parametric-index fork, where these instances
  were unconditional) we can destruct disjunctions under laters. *)
  Global Instance into_or_later_uPred P Q1 Q2 :
    IntoOr P Q1 Q2 → IntoOr (PROP:=uPredI M) (▷ P) (▷ Q1) (▷ Q2).
  Proof. rewrite /IntoOr=>->. by rewrite uPred.later_or. Qed.
  Global Instance into_or_laterN_uPred n P Q1 Q2 :
    IntoOr P Q1 Q2 → IntoOr (PROP:=uPredI M) (▷^n P) (▷^n Q1) (▷^n Q2).
  Proof. rewrite /IntoOr=>->. by rewrite uPred.laterN_or. Qed.
End class_instances.

(** Destructing [∗] and [∃] under a later, for TIMELESS bodies, at every step index.
Upstream's [into_sep_later] and [into_exist_later] require [SIdxFinite] (they use
[later_sep_1] / [later_exist_false], which fail at limit ordinals). For a timeless [P] the
same splits hold at any index, through the except-0 modality:
[▷ P ⊢ ◇ P] ([timeless_except_0]), [◇ (Q1 ∗ Q2) ⊢ ◇ Q1 ∗ ◇ Q2] ([except_0_sep]),
[◇ ∃ a, Φ a ⊢ ∃ a, ◇ Φ a] for inhabited [A] ([except_0_exist]) and [◇ Q ⊢ ▷ Q]
([except_0_into_later]). So an invariant with a timeless body can still be opened with
[iInv … as (x) "(H1 & >H2)"]; a body with a non-timeless part (an arbitrary client
predicate, a stored WP) still cannot, and needs a real change. *)
Section later_timeless.
  Context {SI : sidx} {PROP : bi}.
  Implicit Types P Q : PROP.

  Global Instance into_sep_later_timeless P Q1 Q2 :
    IntoSep P Q1 Q2 → Timeless P → IntoSep (▷ P) (▷ Q1) (▷ Q2).
  Proof.
    rewrite /IntoSep=> HP ?. rewrite (bi.timeless_except_0 P) HP bi.except_0_sep.
    by rewrite !bi.except_0_into_later.
  Qed.

  Global Instance into_exist_later_timeless {A} P (Φ : A → PROP) name :
    IntoExist P Φ name → Inhabited A → Timeless P →
    IntoExist (▷ P) (λ a, ▷ (Φ a))%I name.
  Proof.
    rewrite /IntoExist=> HP ? ?. rewrite (bi.timeless_except_0 P) HP bi.except_0_exist.
    apply bi.exist_mono=> a. by rewrite bi.except_0_into_later.
  Qed.

  (** Splitting off a PERSISTENT part under a later, at every index: in an affine BI
  [▷ (Q1 ∗ Q2) ⊢ ▷ (Q1 ∧ Q2) ⊢ ▷ Q1 ∧ ▷ Q2 ⊢ ▷ Q1 ∗ ▷ Q2] when [Q1] or [Q2] is persistent
  ([sep_and], [later_and], [persistent_and_sep_1]). The other part may be anything, so an
  invariant [T ∗ □ X] or [P ∗ ⌜φ⌝] still gives up its persistent facts when opened. *)
  Global Instance into_sep_later_persistent `{!BiAffine PROP} P Q1 Q2 :
    IntoSep P Q1 Q2 → TCOr (Persistent Q1) (Persistent Q2) → IntoSep (▷ P) (▷ Q1) (▷ Q2).
  Proof.
    rewrite /IntoSep=> HP HQ. rewrite HP bi.sep_and bi.later_and.
    destruct HQ; by rewrite bi.persistent_and_sep_1.
  Qed.
End later_timeless.
