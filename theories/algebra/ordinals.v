From transfinite.stepindex Require Import ordinal_arith existential_properties.
From transfinite.prelude Require Import prelude.
From iris.algebra Require Export cmra local_updates proofmode_classes.
From iris.prelude Require Import options.

(** Ordinals *)
Section ordinals.
  Context `{SI : indexT}.

  Local Open Scope ordinals.
  Canonical Structure ordO := leibnizO ordinals.ord.
  Instance ord_valid : Valid ord := λ x, True.
  Instance ord_validI : ValidN ord := λ α x, True.
  Instance ord_pcore : PCore ord := λ x, Some zero.
  Instance ord_op : Op ord := nadd.
  Instance ord_inhabited : Inhabited ord := populate zero.
  Definition ord_op_plus (x y: ord) : x ⋅ y = (x ⊕ y) := eq_refl.
  Definition ord_equiv_eq (x y: ord) : (x ≡ y) = (x = y) := eq_refl.

  Lemma ord_ra_mixin : RAMixin ord.
  Proof.
    split; try by eauto.
    - by intros ??? ->.
    - intros ???. rewrite !ord_op_plus ord_equiv_eq; simpl.
      by rewrite -(natural_addition_assoc).
    - intros ??. by rewrite !ord_op_plus -natural_addition_comm.
    - intros x cx; injection 1 as <-. by rewrite ord_op_plus natural_addition_zero_left_id.
    - intros x cx; by injection 1 as <-.
    - intros x y cx Hleq; injection 1 as <-.
      exists zero; split; eauto.
      exists zero. by rewrite !ord_op_plus natural_addition_zero_left_id.
  Qed.

  Canonical Structure ordR : cmra := discreteR ord ord_ra_mixin.

  Global Instance ord_cmra_discrete : CmraDiscrete ordR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance ord_cancelable (x : ord) : Cancelable x.
  Proof.
    intros α y z Hv H. eapply natural_addition_cancel.
    rewrite natural_addition_comm [z ⊕ _]natural_addition_comm.
    by apply H.
  Qed.

  Global Instance ord_zero_left_id: LeftId eq zero nadd.
  Proof.
    intros ?. by rewrite natural_addition_zero_left_id.
  Qed.

  Global Instance ord_unit : Unit ord := zero.
  Lemma ord_ucmra_mixin : UcmraMixin ord.
  Proof.
    split; apply _ || done.
  Qed.

  Canonical Structure ordUR : ucmra := Ucmra ord ord_ucmra_mixin.
End ordinals.

