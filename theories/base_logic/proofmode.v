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
