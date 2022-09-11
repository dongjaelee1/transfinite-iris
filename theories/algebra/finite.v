From iris.stepindex Require Export stepindex.
From iris.stepindex Require Import existential_properties.


Global Existing Instance natI | 0.


Global Instance fininte_bounded_existential_nat: FiniteBoundedExistential natI.
Proof.
  intros P [|n] Hdown Hex.
  - exists true. simpl. intros ?; lia.
  - destruct (Hex n) as [x HP].
    + apply: index_succ_greater.
    + exists x. simpl; intros m Hm.
      assert (m = n ∨ m < n) as [->|] by lia; eauto.
Qed.


