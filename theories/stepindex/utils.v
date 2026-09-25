From iris.algebra Require Import stepindex.

Local Open Scope sidx_scope.

(** * Step-index lemmas of the (old) parametric-index Iris fork

The Transfinite Iris development was originally built against a fork of Iris
with a different step-index interface ([indexT]). Upstream Iris now provides
the interface [sidx] (see [iris.algebra.stepindex]). The lemmas below are
derived lemmas of the fork's interface that have no identically-stated
counterpart in upstream's [SIdx] module; they are proved here from upstream's
interface with their original statements (and names). *)
Section index_compat.
  Context {SI : sidx}.
  Implicit Types (n m p : SI).

  Lemma index_lt_eq_lt_dec n m : (n < m) + (n = m) + (m < n).
  Proof. destruct (trichotomyT (<) n m) as [[|]|]; auto. Qed.

  Lemma index_le_eq_or_lt n m : n ≤ m → n = m ∨ n < m.
  Proof. rewrite SIdx.le_lteq; intros [|]; eauto. Qed.

  Lemma index_le_refl_auto n m (H : n = m) : n ≤ m.
  Proof. rewrite H. reflexivity. Qed.

  Lemma index_le_total n m : {n ≤ m} + {m ≤ n}.
  Proof.
    destruct (index_lt_eq_lt_dec n m) as [[|]|].
    - left. by apply SIdx.lt_le_incl.
    - left. by apply index_le_refl_auto.
    - right. by apply SIdx.lt_le_incl.
  Qed.

  Lemma index_le_lt_dec n m : {n ≤ m} + {m < n}.
  Proof.
    edestruct (index_lt_eq_lt_dec n m) as [[H | H] | H].
    - left. by apply SIdx.lt_le_incl.
    - left. by apply index_le_refl_auto.
    - by right.
  Defined.

  Lemma index_lt_irrefl n : ¬ (n < n).
  Proof. apply (irreflexivity (<)). Qed.

  Lemma index_zero_is_unique n : (∀ m, ¬ (m < n)) → n = 0ᵢ.
  Proof.
    intros Hleast. destruct (index_le_total n 0ᵢ)
      as [[]%index_le_eq_or_lt|[]%index_le_eq_or_lt]; auto; exfalso.
    - by eapply SIdx.nlt_0_r.
    - by eapply Hleast.
  Qed.

  Lemma index_is_zero n : {n = 0ᵢ} + {0ᵢ < n}.
  Proof.
    destruct (index_lt_eq_lt_dec n 0ᵢ) as [[]|]; auto.
    exfalso; by eapply SIdx.nlt_0_r.
  Qed.

  Lemma index_lt_dec_minimum n : (∀ m, ¬ (m < n)) + { m | m < n}.
  Proof.
    destruct (index_lt_eq_lt_dec n 0ᵢ) as [[]|].
    - exfalso; by eapply SIdx.nlt_0_r.
    - subst; left; exact SIdx.nlt_0_r.
    - right; by eexists.
  Qed.

  Lemma index_le_ge_eq n n' : n ≤ n' → n' ≤ n → n = n'.
  Proof. intros. by apply (anti_symm (≤)). Qed.

  Lemma index_succ_iff n m : n ≤ m ↔ n < Sᵢ m.
  Proof. by rewrite SIdx.lt_succ_r. Qed.

  Lemma index_lt_succ_mono n m : n < m → Sᵢ n < Sᵢ m.
  Proof. apply SIdx.succ_lt_mono. Qed.

  Lemma index_lt_succ_inj n m : Sᵢ n < Sᵢ m → n < m.
  Proof. apply SIdx.succ_lt_mono. Qed.

  Lemma index_succ_inj n m : Sᵢ n = Sᵢ m → n = m.
  Proof. apply (inj Sᵢ). Qed.

  Lemma index_le_succ_inj n m : Sᵢ n ≤ Sᵢ m → n ≤ m.
  Proof. apply SIdx.succ_le_mono. Qed.

  Lemma index_lt_succ_tight n m : n < m → m < Sᵢ n → False.
  Proof.
    intros H1%SIdx.le_succ_l H2. eapply index_lt_irrefl, SIdx.le_lt_trans; eauto.
  Qed.

  (** Limit indices, including [0ᵢ] (cf. [SIdx.limit], which excludes [0ᵢ]). *)
  Definition index_is_limit n := ∀ m, m < n → Sᵢ m < n.

  Lemma index_limit_not_succ m : index_is_limit m → ∀ n, m ≠ Sᵢ n.
  Proof.
    intros H n Hn. specialize (H n). rewrite Hn in H.
    eapply index_lt_irrefl. apply H, SIdx.lt_succ_diag_r.
  Qed.
End index_compat.

(** Bundled limit indices (the fork's [limit_idx]), using upstream's notion of
(proper, i.e., non-zero) limit indices [SIdx.limit]. *)
Record limit_idx {SI : sidx} := _mklimitidx {
  limit_index :> SI;
  limit_index_is_proper :> SIdx.limit limit_index;
}.
Global Arguments _mklimitidx {_}.
Definition mklimitidx {SI : sidx} (n : SI) (Hlim : index_is_limit n)
    (Hz : 0ᵢ < n) : limit_idx :=
  _mklimitidx n (SIdx.Limit n Hlim (proj2 (SIdx.neq_0_lt_0 n) Hz)).

Lemma limit_index_is_limit {SI : sidx} (n : limit_idx) : index_is_limit n.
Proof. intros m. apply SIdx.limit_gt_S, limit_index_is_proper. Qed.
Lemma limit_index_not_zero {SI : sidx} (n : limit_idx) : 0ᵢ < n.
Proof. apply SIdx.limit_lt_0, limit_index_is_proper. Qed.

(** ** Automation (the fork's [si_solver] hint database and [stepindex] tactic) *)
Create HintDb si_solver.

Ltac si_solver := idtac.
Global Hint Extern 1 => si_solver : si_solver.

Tactic Notation "stepindex" "using" uconstr(H) := eauto using H with si_solver.
Tactic Notation "stepindex" := eauto with si_solver.

Global Hint Immediate SIdx.le_0_l : si_solver.
Global Hint Resolve SIdx.lt_succ_diag_r : si_solver.
Global Hint Resolve <- index_succ_iff : si_solver.

Global Hint Extern 1 (?a ≤ ?a) => reflexivity : si_solver.
Global Hint Extern 2 (?a ≤ ?b) => apply index_le_refl_auto : si_solver.
Global Hint Extern 1 (?a ≤ ?b) => apply SIdx.lt_le_incl : si_solver.

Global Hint Extern 1 False => eapply index_lt_irrefl : si_solver.
Global Hint Resolve -> index_succ_iff : si_solver.
Global Hint Resolve index_le_succ_inj : si_solver.
Global Hint Resolve index_lt_succ_mono : si_solver.



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
  Context {SI : sidx}.

  Definition index_min α β := if index_le_total α β then α else β.
  Lemma index_min_eq α β: index_min α β = α ∨ index_min α β = β.
  Proof.
    unfold index_min; destruct index_le_total; eauto.
  Qed.

  Lemma index_min_le_l α β : index_min α β ≤ α.
  Proof.
    unfold index_min. destruct index_le_total; eauto with si_solver.
  Qed.
  Lemma index_min_le_r α β : index_min α β ≤ β.
  Proof.
    unfold index_min. destruct index_le_total; eauto with si_solver.
  Qed.

  Lemma index_min_l α β : α ≤ β → index_min α β = α.
  Proof.
    intros H. unfold index_min. destruct (index_le_total α β) as [_ | Hle]; [easy | ].
    by apply index_le_ge_eq.
  Qed.

  Lemma index_min_r α β : α ≤ β → index_min β α = α.
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

  Lemma index_min_mono_r γ β α: γ ≤ β → index_min α γ ≤ index_min α β.
  Proof.
    intros H. unfold index_min. destruct (index_le_total α γ) as [H1 | H1];
    destruct (index_le_total α β) as [H2 | H2]; try by eauto with si_solver.
    etrans; done.
  Qed.

End index_minimum.


Section si_solver_lemmas.
  Context {SI : sidx}.

  Lemma index_le_zero α: α ≤ 0ᵢ → α = 0ᵢ.
  Proof.
    by intros [->|[]%SIdx.nlt_0_r]%index_le_eq_or_lt.
  Qed.


End si_solver_lemmas.




Section ordinal_match.
  Context {SI : sidx}.
  Definition ord_match (P : SI → Type) : P 0ᵢ → (∀ α, P (Sᵢ α)) → (∀ α : limit_idx, P α) → ∀ α, P α :=
    λ s f lim α,
      match index_is_zero α with
      | left EQ => eq_rect_r P s EQ
      | right NT =>
          match SIdx.weak_case α with
          | inl (exist _ β EQ) => eq_rect_r P (f β) EQ
          | inr Hlim => lim (mklimitidx α Hlim NT)
          end
      end.
End ordinal_match.






Create HintDb index.
Global Hint Extern 1 False => eapply index_lt_irrefl : index.
Global Hint Resolve index_succ_iff_proj_l2r : index. (* = [-> index_succ_iff] *)
Global Hint Constructors rc : index.
(* TODO: maybe remove the transitivity stuff *)
(*Global Hint Extern 2 (_ ≺ _) => etransitivity : index.*)
(*Global Hint Resolve SIdx.le_lt_trans : index.*)
(*Global Hint Resolve SIdx.lt_le_trans : index.*)
Global Hint Resolve SIdx.lt_succ_diag_r : index.
Global Hint Resolve index_le_succ_inj : index.
Global Hint Resolve index_lt_succ_mono : index.
Global Hint Immediate SIdx.le_0_l : index.

(** subst fails in some settings with dependent typing, when that happens, we have to do stuff manually *)
Ltac subst_with H :=
  match type of H with
  | ?a = ?b =>
    tryif (match b with context[?c] => constr_eq a c end) then fail else
    (match goal with
    | H0 : _ < _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ ≤ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ = _ |- _ => assert_fails (constr_eq H H0); progress (try rewrite H in H0)
    end;
    repeat match goal with
    | H0 : _ < _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ ≤ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
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
  | Sᵢ ?a < Sᵢ ?b => apply index_lt_succ_inj in H
  | Sᵢ ?a = Sᵢ ?b => apply index_succ_inj in H; repeat subst_assmpt
  end.
Ltac index_contra_solve_core cont :=
  subst_assmpt;
  match goal with
  | [H : ?a < ?a |- _] => specialize (index_lt_irrefl _ H) as []
  | [H : ?a < 0ᵢ |- _] => by apply SIdx.nlt_0_r in H
  | [H : ?a = Sᵢ ?a |- _] => apply SIdx.succ_neq in H as []
  | [H : Sᵢ ?a = ?a |- _] => symmetry in H; cont
  | [H : ?a ≤ 0ᵢ, H1 : ?b < ?a |- _] => eapply SIdx.nlt_0_r, SIdx.lt_le_trans; [apply H1 | apply H]
  | [H1 : ?a < ?b, H2 : ?b < Sᵢ ?a |- _] => specialize (index_lt_succ_tight _ _ H1 H2) as []
  | [H1 : ?a ≤ ?b, H2 : ?b < ?a |- _] => eapply index_lt_irrefl, SIdx.le_lt_trans; [apply H1 | apply H2]
  | [H : Sᵢ ?a = 0ᵢ |- _] => destruct (SIdx.neq_succ_0 _ H) as []
  | [H : 0ᵢ = Sᵢ ?a |- _] => symmetry in H; destruct (SIdx.neq_succ_0 _ H) as []
  | [H : Sᵢ ?a < ?a |- _] =>
      let H1 := fresh "H" in
        specialize (SIdx.lt_trans _ _ _ H (SIdx.lt_succ_diag_r a)) as H1;
        apply index_lt_irrefl in H1 as []
  | [H : Sᵢ ?a < Sᵢ ?b |- _ ] => normalise_hypot H; cont
  | [H : Sᵢ ?a = Sᵢ ?b |- _ ] => normalise_hypot H; cont
  | [H : Sᵢ ?a ≤ ?b |- _] => apply SIdx.le_succ_l in H; cont
  end.
(* infer by transitivity -- might be very expensive when many inferences can be done or even diverge *)
Ltac index_contra_solve_infer cont :=
  match goal with
  | [H1 : ?a < ?b, H2 : ?b < ?c |- _] =>
      let H := fresh "H" in
        specialize (SIdx.lt_trans _ _ _ H1 H2) as H; normalise_hypot H;
        tryif (hypot_exists H) then fail else cont
  end.

Ltac index_contra_solve :=
  exfalso;
  index_contra_solve_core index_contra_solve + index_contra_solve_infer index_contra_solve.

(* Do not do any transitivity inferences. A smarter strategy would be to give it a budget for transitivity inferences, but that would be more complicated *)
Ltac index_contra_solve_fast :=
  exfalso; index_contra_solve_core index_contra_solve_core.
