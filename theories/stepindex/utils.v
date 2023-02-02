From iris.algebra Require Import stepindex.



(* Reflexive Closure *)
(* TODO: upstream into stdpp *)
Inductive rc {A} (R: A → A → Prop) (x: A) (y: A):  Prop :=
| rc_refl: x = y → rc R x y
| rc_subrel: R x y → rc R x y.
Global Hint Constructors rc : core.

Global Instance rc_reflexive {A} (R : A → A → Prop) :
  Reflexive (rc R) | 10.
Proof. intros ?; by apply rc_refl. Qed.
Global Instance rc_subrelation {A} (R : A → A → Prop):
  subrelation R (rc R) | 10.
Proof. intros ? ? ?; by apply rc_subrel. Qed.

Lemma rc_iff {A} (R: A → A → Prop) x y: rc R x y ↔ R x y ∨ x = y.
Proof.
  split; destruct 1; eauto.
Qed.

Global Instance rc_transitive {A} (R: A → A → Prop) `{!Transitive R}:
  Transitive (rc R) | 10.
Proof.
  intros x y z [] []; subst; eauto.
Qed.


Section index_minimum.
  Context `{SI: indexT}.

  Definition index_min α β := if index_le_total α β then α else β.
  Lemma index_min_eq α β: index_min α β = α ∨ index_min α β = β.
  Proof.
    unfold index_min; destruct index_le_total; eauto.
  Qed.

  Lemma index_min_le_l α β : index_min α β ⪯ᵢ α.
  Proof.
    unfold index_min. destruct index_le_total; eauto with stepindex.
  Qed.
  Lemma index_min_le_r α β : index_min α β ⪯ᵢ β.
  Proof.
    unfold index_min. destruct index_le_total; eauto with stepindex.
  Qed.

  Lemma index_min_l α β : α ⪯ᵢ β → index_min α β = α.
  Proof.
    intros H. unfold index_min. destruct (index_le_total α β) as [_ | Hle]; [easy | ].
    by apply index_le_ge_eq.
  Qed.

  Lemma index_min_r α β : α ⪯ᵢ β → index_min β α = α.
  Proof.
    intros H. unfold index_min. destruct (index_le_total β α) as [Hle | ]; [| easy].
    by apply index_le_ge_eq.
  Qed.

  Lemma index_min_comm α β : index_min β α = index_min α β.
  Proof.
    unfold index_min.
    destruct (index_le_total β α) as [H1 | H1], (index_le_total α β) as [H2 | H2].
    - by apply index_le_ge_eq.
    - reflexivity.
    - reflexivity.
    - by apply index_le_ge_eq.
  Qed.

  Lemma index_min_mono_r γ β α: γ ⪯ᵢ β → index_min α γ ⪯ᵢ index_min α β.
  Proof.
    intros H. unfold index_min. destruct (index_le_total α γ) as [H1 | H1];
    destruct (index_le_total α β) as [H2 | H2]; try by eauto with stepindex.
    etrans; done.
  Qed.

End index_minimum.


Section stepindex_lemmas.
  Context `{SI: indexT}.

  Lemma index_le_zero α: α ⪯ᵢ zero → α = zero.
  Proof.
    by intros [->|[]%index_zero_least]%index_le_eq_or_lt.
  Qed.


End stepindex_lemmas.




Section ordinal_match.
  Context {SI : indexT}.
  Definition ord_match (P : index → Type) : P zero → (∀ α, P (succ α)) → (∀ α : limit_idx, P α) → ∀ α, P α :=
    λ s f lim α,
      match index_is_zero α with
      | left EQ => eq_rect_r P s EQ
      | right NT =>
          match index_dec_limit α with
          | inl (exist _ β EQ) => eq_rect_r P (f β) EQ
          | inr Hlim => lim (mklimitidx α Hlim NT)
          end
      end.
End ordinal_match.






Create HintDb index.
Global Hint Extern 1 False => eapply index_lt_irrefl : index.
Global Hint Resolve -> index_succ_iff : index.
Global Hint Constructors rc : index.
(* TODO: maybe remove the transitivity stuff *)
(*Global Hint Extern 2 (_ ≺ _) => etransitivity : index.*)
(*Global Hint Resolve index_le_lt_trans : index.*)
(*Global Hint Resolve index_lt_le_trans : index.*)
Global Hint Resolve index_succ_greater : index.
Global Hint Resolve index_le_succ_inj : index.
Global Hint Resolve index_lt_succ_mono : index.
Global Hint Immediate index_zero_minimum : index.

(** subst fails in some settings with dependent typing, when that happens, we have to do stuff manually *)
Ltac subst_with H :=
  match type of H with
  | ?a = ?b =>
    tryif (match b with context[?c] => constr_eq a c end) then fail else
    (match goal with
    | H0 : _ ≺ᵢ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ ⪯ᵢ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ = _ |- _ => assert_fails (constr_eq H H0); progress (try rewrite H in H0)
    end;
    repeat match goal with
    | H0 : _ ≺ᵢ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ ⪯ᵢ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ = _ |- _ => assert_fails (constr_eq H H0); progress (try rewrite H in H0)
    end)
  end.
Ltac subst_assmpt :=
subst +
(repeat match goal with
| H : ?a = ?b |- _ => is_var a; subst_with H; clear H
| H : ?a = ?b |- _ => is_var b; let H' := fresh H in specialize (symmetry H) as H'; try clear H; subst_with H'; clear H'
end).

Ltac hypot_exists H :=
  match type of H with ?t =>
    match goal with
    | H0 : t |- _ => assert_fails (constr_eq H0 H)
    end
  end.

(* index_contra_solve: solve directly contadictory goals using assumptions on index order*)

Ltac normalise_hypot H :=
  try match type of H with
  | succ ?a ≺ᵢ succ ?b => apply index_lt_succ_inj in H
  | succ ?a = succ ?b => apply index_succ_inj in H; repeat subst_assmpt
  end.
Ltac index_contra_solve_core cont :=
  subst_assmpt;
  match goal with
  | [H : ?a ≺ᵢ ?a |- _] => specialize (index_lt_irrefl _ H) as []
  | [H : ?a ≺ᵢ zero |- _] => by apply index_zero_least in H
  | [H : ?a = succ ?a |- _] => apply index_succ_neq in H as []
  | [H : succ ?a = ?a |- _] => symmetry in H; cont
  | [H : ?a ⪯ᵢ zero, H1 : ?b ≺ᵢ ?a |- _] => eapply index_zero_least, index_lt_le_trans; [apply H1 | apply H]
  | [H1 : ?a ≺ᵢ ?b, H2 : ?b ≺ᵢ succ ?a |- _] => specialize (index_lt_succ_tight _ _ H1 H2) as []
  | [H1 : ?a ⪯ᵢ ?b, H2 : ?b ≺ᵢ ?a |- _] => eapply index_lt_irrefl, index_le_lt_trans; [apply H1 | apply H2]
  | [H : succ ?a = zero |- _] => destruct (index_succ_not_zero _ H) as []
  | [H : zero = succ ?a |- _] => symmetry in H; destruct (index_succ_not_zero _ H) as []
  | [H : succ ?a ≺ᵢ ?a |- _] =>
      let H1 := fresh "H" in
        specialize (index_lt_trans _ _ _ H (index_succ_greater a)) as H1;
        apply index_lt_irrefl in H1 as []
  | [H : succ ?a ≺ᵢ succ ?b |- _ ] => normalise_hypot H; cont
  | [H : succ ?a = succ ?b |- _ ] => normalise_hypot H; cont
  | [H : succ ?a ⪯ᵢ ?b |- _] => apply index_succ_le_lt in H; cont
  end.
(* infer by transitivity -- might be very expensive when many inferences can be done or even diverge *)
Ltac index_contra_solve_infer cont :=
  match goal with
  | [H1 : ?a ≺ᵢ ?b, H2 : ?b ≺ᵢ ?c |- _] =>
      let H := fresh "H" in
        specialize (index_lt_trans _ _ _ H1 H2) as H; normalise_hypot H;
        tryif (hypot_exists H) then fail else cont
  end.

Ltac index_contra_solve :=
  exfalso;
  index_contra_solve_core index_contra_solve + index_contra_solve_infer index_contra_solve.

(* Do not do any transitivity inferences. A smarter strategy would be to give it a budget for transitivity inferences, but that would be more complicated *)
Ltac index_contra_solve_fast :=
  exfalso; index_contra_solve_core index_contra_solve_core.
