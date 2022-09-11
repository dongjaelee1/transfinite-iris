From iris.prelude Require Export prelude.


Structure IndexMixin {A} {R: A → A → Prop} {zero: A} {succ: A → A} :=
  {
    index_mixin_lt_trans: Transitive R;
    index_mixin_lt_wf: wf R;
    index_mixin_lt_strict_total α β: (R α β) + (α = β) + (R β α);
    index_mixin_zero_least: nf (flip R) zero;
    index_mixin_succ_greater α: R α (succ α);
    index_mixin_succ_least α β: R α β → rc R (succ α) β;
    index_mixin_dec_limit α:
      {β | α = succ β} + (∀ β, R β α → R (succ β) α);
  }.
Arguments IndexMixin : clear implicits.

Class indexT :=
  IndexT {
    index : Type;
    index_lt : relation index;
    index_zero : index;
    index_succ : index → index;
    index_mixin : IndexMixin index index_lt index_zero index_succ;
  }.

Notation "(≺)" := (index_lt).
Notation "(≻)" := (flip (index_lt)).

Notation zero := (index_zero).
Notation succ α := (index_succ α).
Notation "α ≺ β" := (index_lt α β) (at level 80).

Polymorphic Definition index_le `{SI : indexT} : relation index := rc (index_lt).
Notation "(⪯)" := (index_le).
Notation "α ⪯ β" := (index_le α β) (at level 80).

Global Instance index_le_refl `{SI : indexT} : Reflexive (index_le) := _.
Global Instance index_lt_le_subrel `{SI : indexT}: subrelation (index_lt) (index_le) := _.
Lemma index_le_refl_auto `{SI : indexT} (α β : index) (H : α = β): α ⪯ β.
Proof. rewrite H. apply index_le_refl. Qed.
Global Hint Extern 1 (?a ⪯ ?a) => apply index_le_refl : core.
Global Hint Extern 2 (?a ⪯ ?b) => apply index_le_refl_auto : core.
Global Hint Extern 1 (?a ⪯ ?b) => apply index_lt_le_subrel : core.

Lemma index_le_eq_or_lt `{SI : indexT} (α β : index) : α ⪯ β → α = β ∨ α ≺ β.
Proof. intros [H | H]; auto. Qed.

Section index_laws.
  Context `{SI : indexT}.
  Global Instance index_lt_trans : Transitive (index_lt).
  Proof. eapply index_mixin_lt_trans, index_mixin. Qed.
  Lemma index_lt_wf : wf (index_lt).
  Proof. eapply index_mixin_lt_wf, index_mixin. Qed.
  Lemma index_lt_eq_lt_dec (α β : index) : (α ≺ β) + (α = β) + (β ≺ α).
  Proof. eapply index_mixin_lt_strict_total, index_mixin. Qed.
  Lemma index_zero_least : nf (flip (index_lt)) zero.
  Proof. eapply index_mixin_zero_least, index_mixin. Qed.
  Lemma index_succ_greater (α : index) : α ≺ succ α.
  Proof. eapply index_mixin_succ_greater, index_mixin. Qed.
  Lemma index_succ_least (α β : index) : α ≺ β → succ α ⪯ β.
  Proof. eapply index_mixin_succ_least, index_mixin. Qed.
  Lemma index_dec_limit (α: index) : { β | α = succ β } + (∀ β, β ≺ α → succ β ≺ α).
  Proof. eapply index_mixin_dec_limit, index_mixin. Qed.
End index_laws.
(* Arguments index_zero_least : clear implicits.
Arguments index_lt_wf : clear implicits. *)

Definition index_is_limit {SI : indexT} (α : index) := ∀ β, β ≺ α → succ β ≺ α.
(* proper limit indices that are not zero*)
Record index_is_proper_limit {SI : indexT} (α : index) := mkproperlim {
  proper_limit_is_limit : index_is_limit α;
  proper_limit_not_zero : zero ≺ α;
}.
Arguments mkproperlim {_} _ _ _.
Arguments proper_limit_not_zero {_ _} _.
Arguments proper_limit_is_limit {_ _} _.

Record limit_idx {SI: indexT} := _mklimitidx {
  limit_index :> index;
  limit_index_is_proper :> index_is_proper_limit limit_index;
}.
Arguments _mklimitidx {_}.
Definition mklimitidx {SI : indexT} (α : index) Hlim Hz := _mklimitidx α (mkproperlim α Hlim Hz).

Lemma limit_index_is_limit {SI: indexT} (α : limit_idx) : index_is_limit α.
Proof. apply limit_index_is_proper. Qed.
Lemma limit_index_not_zero {SI : indexT} (α : limit_idx) : zero ≺ α.
Proof. apply limit_index_is_proper. Qed.


Section StepIndexProperties.
  Context {SI: indexT}.
  Implicit Type (α β γ : index).

  Global Instance: Inhabited index.
  Proof. constructor. exact zero. Qed.

  Global Instance: PreOrder (index_le).
  Proof.
    split; [by constructor|].
    intros ??? [] []; subst; eauto.
    right; transitivity y; auto.
  Qed.

  Lemma index_le_total α β: {α ⪯ β} + {β ⪯ α}.
  Proof.
    destruct (index_lt_eq_lt_dec α β) as [[|]|]; eauto.
  Qed.

  Lemma index_le_lt_dec α β : {α ⪯ β} + {β ≺ α}.
  Proof.
    edestruct (index_lt_eq_lt_dec α β) as [[H | H] | H]; eauto.
  Defined.

  Lemma index_zero_minimum α: zero ⪯ α.
  Proof.
    destruct (index_le_total zero α) as [|[]]; eauto.
    exfalso; eapply (index_zero_least); eauto.
  Qed.

  Lemma index_lt_zero_is_normal α: ¬ (α ≺ zero).
  Proof.
    specialize (index_zero_least) as H.
    intros R; apply H; unfold red, flip; eauto.
  Qed.

  Lemma index_zero_is_unique α: (∀ β, ¬ (β ≺ α)) → α = zero.
  Proof.
    intros H; destruct (index_le_total α zero) as [[]|[]]; eauto; exfalso.
      by eapply index_lt_zero_is_normal. by eapply H.
  Qed.

  Lemma index_is_zero α: {α = zero} + {zero ≺ α}.
  Proof.
    destruct (index_lt_eq_lt_dec α zero) as [[]|]; eauto.
    exfalso; by eapply index_lt_zero_is_normal.
  Qed.

  Lemma index_lt_dec_minimum α: (∀ β, ¬ (β ≺ α)) + { β | β ≺ α}.
  Proof.
    destruct (index_lt_eq_lt_dec α zero) as [[]|].
    - exfalso; by eapply index_lt_zero_is_normal.
    - subst; left; exact index_lt_zero_is_normal.
    - right; by eexists.
  Qed.

  Lemma index_lt_irrefl α: ¬ (α ≺ α).
  Proof.
    induction α using (well_founded_ind (index_lt_wf)).
    intros H1; apply H in H1 as H2; eauto.
  Qed.

  Lemma index_lt_le_trans α β γ: α ≺ β → β ⪯ γ → α ≺ γ.
  Proof. intros ? []; subst; eauto. by transitivity β. Qed.

  Lemma index_le_lt_trans α β γ: α ⪯ β → β ≺ γ → α ≺ γ.
  Proof. intros [] ?; subst; eauto. by transitivity β. Qed.

  Lemma index_le_lt_contradict α α' : α ⪯ α' → α' ≺ α → False.
  Proof.
    intros H1 H2. enough (α ≺ α) by (by eapply index_lt_irrefl).
    by eapply index_le_lt_trans.
  Qed.

  Lemma index_lt_le_contradict α α' : α ≺ α' → α' ⪯ α → False.
  Proof.
    intros H1 H2. enough (α ≺ α) by (by eapply index_lt_irrefl).
    by eapply index_lt_le_trans.
  Qed.

  Lemma index_le_ge_eq α α' : α ⪯ α' → α' ⪯ α → α = α'.
  Proof.
    intros [-> | H1] [H2 | H2]; try by eauto.
    exfalso; eapply index_lt_irrefl. by eapply index_lt_trans.
  Qed.

  Lemma index_succ_iff α β: α ⪯ β ↔ α ≺ succ β.
  Proof.
    split; intros H.
    - destruct H; subst. 2: transitivity β.
      all: eauto; eapply index_succ_greater.
    - destruct (index_le_total α β) as [|[|H1]]; eauto.
      apply index_succ_least in H1.
      eapply index_lt_le_trans in H1; eauto.
      exfalso; eapply index_lt_irrefl; eauto.
  Qed.

  Lemma index_le_lt_eq_dec α β : α ⪯ β → {α ≺ β} + {α = β}.
  Proof.
    intros Hle. destruct (index_lt_eq_lt_dec α β) as [[H | H] | H].
    - by left.
    - by right.
    - exfalso. eapply index_lt_irrefl with (α := α). by eapply index_le_lt_trans.
  Qed.

  Lemma index_lt_succ_mono α β: α ≺ β → succ α ≺ succ β.
  Proof.
    intros. by eapply index_succ_iff, index_succ_least.
  Qed.

  Lemma index_le_succ_mono α β: α ⪯ β → succ α ⪯ succ β.
  Proof.
    intros [->|H % index_lt_succ_mono]; eauto.
  Qed.

  Lemma index_succ_greater' α β: α = succ β → β ≺ α.
  Proof. intros ->; by apply index_succ_greater. Qed.

  Lemma index_succ_neq α : α ≠ succ α.
  Proof.
    intros H%index_succ_greater'. by eapply index_lt_irrefl.
  Qed.

  Lemma index_lt_succ_inj α β: succ α ≺ succ β → α ≺ β.
  Proof.
    destruct (index_le_total α β) as [[]|H].
    - subst; intros [] % index_lt_irrefl.
    - auto.
    - intros H'. apply index_le_succ_mono in H.
      specialize (index_le_lt_trans _ _ _ H H') as [] % index_lt_irrefl.
  Qed.

  Lemma index_succ_inj α β: succ α = succ β → α = β.
  Proof.
    intros H. destruct (index_lt_eq_lt_dec α β) as [[H'|]|H']; eauto; exfalso.
    all: eapply index_lt_succ_mono in H'; rewrite H in H'; by eapply index_lt_irrefl.
  Qed.

  Lemma index_le_succ_inj α β : succ α ⪯ succ β → α ⪯ β.
  Proof.
    intros [Heq | Hlt].
    - apply index_succ_inj in Heq. by left.
    - apply index_lt_succ_inj in Hlt. by right.
  Qed.

  Lemma index_eq_dec α β: {α = β} + {α ≠ β}.
  Proof.
    destruct (index_lt_eq_lt_dec α β) as [[H|H]|H]; subst.
    - right; intros ->; by eapply index_lt_irrefl.
    - by left.
    - right; intros ->; by eapply index_lt_irrefl.
  Qed.

  Lemma index_succ_le_lt α β : succ α ⪯ β ↔ α ≺ β.
  Proof.
    split.
    - intros [<- | H1]; [eapply index_succ_greater | ].
      eapply index_lt_trans; [ eapply index_succ_greater | eauto ].
    - intros H. destruct (index_lt_eq_lt_dec (succ α) β) as [[Hlt | Heq] | Hgt].
      + by right.
      + by left.
      + exfalso. eapply index_succ_least in Hgt.
        apply index_le_succ_inj in Hgt.
        eapply index_lt_irrefl. by eapply index_lt_le_trans.
  Qed.

  Lemma index_succ_le α β : succ α ⪯ β → α ⪯ β.
  Proof.
    right. by apply index_succ_le_lt.
  Qed.

  Lemma index_lt_succ_tight α β : α ≺ β → β ≺ succ α → False.
  Proof.
    intros H1%index_succ_le_lt H2. eapply index_lt_irrefl, index_le_lt_trans; eauto.
  Qed.

  Lemma index_succ_not_zero α: succ α ≠ zero.
  Proof.
    intros H. eapply index_lt_zero_is_normal, index_succ_greater'. by symmetry.
  Qed.

  Lemma index_succ_not_limit β: ¬ (∀ α, α ≺ succ β → succ α ≺ succ β).
  Proof.
    intros H. eapply index_lt_irrefl, H. apply index_succ_greater.
  Qed.

  Lemma index_limit_not_succ β  : index_is_limit β → ∀ α, β ≠ succ α.
  Proof.
    intros H α Hα. specialize (H α). rewrite Hα in H. eapply index_lt_irrefl. apply H, index_succ_greater.
  Qed.

  Definition index_min α β := if index_le_total α β then α else β.
  Lemma index_min_eq α β: index_min α β = α ∨ index_min α β = β.
  Proof.
    unfold index_min; destruct index_le_total; eauto.
  Qed.

  Lemma index_min_le_l α β : index_min α β ⪯ α.
  Proof.
    unfold index_min. destruct index_le_total; eauto.
  Qed.
  Lemma index_min_le_r α β : index_min α β ⪯ β.
  Proof.
    unfold index_min. destruct index_le_total; eauto.
  Qed.

  Lemma index_min_l α β : α ⪯ β → index_min α β = α.
  Proof.
    intros H. unfold index_min. destruct (index_le_total α β) as [_ | Hle]; [easy | ].
    by apply index_le_ge_eq.
  Qed.

  Lemma index_min_r α β : α ⪯ β → index_min β α = α.
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

  Lemma index_min_mono_r γ β α: γ ⪯ β → index_min α γ ⪯ index_min α β.
  Proof.
    intros H. unfold index_min. destruct (index_le_total α γ) as [H1 | H1];
    destruct (index_le_total α β) as [H2 | H2]; try by auto.
    left. eapply index_le_ge_eq; auto. etransitivity; eauto.
  Qed.
End StepIndexProperties.

Global Hint Immediate index_zero_minimum : core.
Global Hint Resolve index_succ_greater : core.
Global Hint Resolve <- index_succ_iff : core.

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

Section ordinal_recursor.
  Context {SI: indexT}.

  Definition index_rec (P: index → Type): P zero → (∀ α, P α → P (succ α)) → (∀ α: limit_idx, (∀ β, β ≺ α → P β) → P α) → ∀ α, P α :=
    λ s f lim, Fix (index_lt_wf) _ (λ α IH,
        match index_is_zero α with
        | left EQ => eq_rect_r P s EQ
        | right NZ =>
          match index_dec_limit α with
          | inl (exist _ β EQ) => eq_rect_r P (f β (IH β (index_succ_greater' α β EQ))) EQ
          | inr Hlim => lim (mklimitidx α Hlim NZ) IH
          end
        end
      ).

  Lemma index_type_dec (α : index) :
    (α = zero) + { α' | α = succ α'} + ( index_is_limit α).
  Proof.
    revert α. apply index_rec.
    - by left; left.
    - intros α _; left; right. by exists α.
    - intros α _. right. apply limit_index_is_limit.
  Defined.

  Class index_rec_lim_ext {P: index → Type} (lim: ∀ α: limit_idx, (∀ β, β ≺ α → P β) → P α) := {
    index_rec_lim_ext_proofs α H1 H2 f: lim α f = lim (mklimitidx α H2 H1) f;
    index_rec_lim_ext_function α f g: (∀ β Hβ, f β Hβ = g β Hβ) → lim α f = lim α g
  }.

  Lemma index_rec_unfold P s f lim `{index_rec_lim_ext P lim} α:
    index_rec P s f lim α =
    match index_is_zero α with
    | left EQ => eq_rect_r P s EQ
    | right NZ =>
      match index_dec_limit α with
      | inl (exist _ β EQ) => eq_rect_r P (f β (index_rec P s f lim β)) EQ
      | inr Hlim => lim (mklimitidx α Hlim NZ) (λ β _, index_rec P s f lim β)
      end
    end.
  Proof.
    unfold index_rec at 1. rewrite Fix_eq.
    - reflexivity.
    - intros β g h EQ. destruct index_is_zero; eauto.
      destruct index_dec_limit as [[γ EQ']|].
      + by rewrite EQ.
      + erewrite index_rec_lim_ext_function; eauto.
  Qed.

  Lemma index_rec_zero P s f lim `{index_rec_lim_ext P lim}: index_rec P s f lim zero = s.
  Proof.
    rewrite index_rec_unfold; eauto.
    destruct index_is_zero as [EQ|NT].
    - symmetry. apply Eqdep_dec.eq_rect_eq_dec, index_eq_dec.
    - exfalso; by eapply index_lt_irrefl.
  Qed.

  Lemma index_rec_succ P s f lim `{index_rec_lim_ext P lim} α: index_rec P s f lim (succ α) = f α (index_rec P s f lim α).
  Proof.
    rewrite index_rec_unfold; eauto.
    destruct index_is_zero as [EQ|NT];[|destruct index_dec_limit as [[β EQ]|Hlim]].
    - exfalso. by eapply index_succ_not_zero.
    - eapply index_succ_inj in EQ as EQ'. subst α.
      symmetry. apply Eqdep_dec.eq_rect_eq_dec, index_eq_dec.
    - exfalso. eapply index_lt_irrefl, Hlim, index_succ_greater.
  Qed.

  Lemma index_rec_lim P s f lim `{index_rec_lim_ext P lim} (α: limit_idx):
    index_rec P s f lim α = lim α (λ β _, index_rec P s f lim β).
  Proof.
    rewrite index_rec_unfold; eauto.
    destruct index_is_zero as [EQ|NT];[|destruct index_dec_limit as [[β EQ]|Hlim]].
    - exfalso. specialize (limit_index_not_zero α). rewrite EQ. by apply index_lt_irrefl.
    - exfalso. specialize (limit_index_is_limit α β (index_succ_greater' _ _ EQ)).
      rewrite EQ. by apply index_lt_irrefl.
    - simpl. symmetry. apply index_rec_lim_ext_proofs.
  Qed.
End ordinal_recursor.

Section ordinal_cumulative_recursor.

  Context {SI: indexT}.
  Variable (P: index → Type) (Q: ∀ α, (∀ β, β ≺ α → P β) → Type).

  Let R α := {f: ∀ β, β ≺ α → P β & Q α f}.

  Lemma index_cumulative_rec (F: ∀ α, R α → P α):
    (∀ α G, Q α (λ β Hβ, F β (G β Hβ))) → (∀ α, R α).
  Proof.
    intros IH. apply (Fix (index_lt_wf)).
    intros α G. unfold R. unshelve econstructor.
    - intros β Hβ. by eapply F, G.
    - by apply IH.
  Defined.

  Lemma index_cumulative_rec_dep (F: ∀ α, R α → P α):
    (∀ α G, Q α (λ β Hβ, F β (G β Hβ))) → (∀ α (H : Acc (≺) α), R α).
  Proof.
    intros IH. apply (Fix_F).
    intros α G. unfold R. unshelve econstructor.
    - intros β Hβ. by eapply F, G.
    - by apply IH.
  Defined.

  Lemma index_cumulative_rec_dep_step F step β succs:
    index_cumulative_rec_dep F step β (Acc_intro β succs) =
    existT (λ γ Hγ, F γ (index_cumulative_rec_dep F step γ (succs γ Hγ)))
      (step β (λ γ Hγ, index_cumulative_rec_dep F step γ (succs γ Hγ))).
  Proof. reflexivity. Qed.

  Lemma index_cumulative_rec_unfold F step (M : ∀ α, R α → Prop) :
    (∀ β succs, (∀ γ (Hγ: γ ≺ β), M γ (index_cumulative_rec_dep F step γ (succs γ Hγ))) → M β (index_cumulative_rec_dep F step β (Acc_intro β succs)))
    → ∀ β, M β (index_cumulative_rec F step β).
  Proof.
    intros H β. unfold index_cumulative_rec, Fix.
    pattern β, (index_lt_wf β). eapply Acc_inv_dep. clear β.
    intros β succs Hβ.
    unfold index_cumulative_rec_dep in H.
    eapply H. apply Hβ.
  Qed.
  Global Opaque index_cumulative_rec_dep.
  Global Opaque index_cumulative_rec.
End ordinal_cumulative_recursor.


(* finite indicies are exactly the natural numbers *)
Class FiniteIndex (SI: indexT) :=
  finite_index (α: index): α = zero ∨ ∃ β, α = succ β.

(* Canonical instances: natural numbers, pairs *)
Section nat_index.
  Lemma le_rc_lt x y: le x y ↔ rc lt x y.
  Proof.
    split.
    - intros [| ->] % le_lt_or_eq; [ by right| by left].
    - intros []; lia.
  Qed.

  Lemma nat_index_mixin: IndexMixin nat lt 0 S.
  Proof.
    constructor.
    - typeclasses eauto.
    - exact lt_wf.
    - intros m n. destruct (lt_eq_lt_dec m n) as [[]|]; eauto.
    - unfold flip; intros [n]; lia.
    - intros; lia.
    - intros; eapply le_rc_lt; auto.
    - intros [|n].
      + right; intros; lia.
      + left; by (exists n).
  Qed.

  Definition natI : indexT := IndexT nat lt 0 S nat_index_mixin.
  Global Instance nat_finite_index: FiniteIndex natI.
  Proof. intros [|n]; eauto. Qed.
End nat_index.


Section pair_index.
  Variable (SI SJ: indexT).

  Notation I := (@index SI).
  Notation J := (@index SJ).

  Definition pair_zero : I * J := (zero, zero).

  Definition pair_succ : (I * J) → I * J := λ '(n, m), (n, succ m).

  Definition pair_lt : I * J → I * J → Prop :=
    λ '(n1, m1) '(n2, m2), n1 ≺ n2 ∨ (n1 = n2 ∧ m1 ≺ m2).

  Instance pair_lt_trans: Transitive pair_lt.
  Proof.
    intros [] [] []; simpl; intros [|[]] [|[]]; subst; firstorder.
    - left; etransitivity; eauto.
    - right; split; eauto; by etransitivity.
  Qed.

  Lemma pair_lt_wf: wf pair_lt.
  Proof.
    intros [m n]. revert n; induction m using (well_founded_ind (index_lt_wf)).
    intros n; induction n using (well_founded_ind (index_lt_wf)).
    constructor. intros [m' n'] [|[->]]; eauto.
  Qed.

  Lemma pair_index_mixin: IndexMixin (I * J) pair_lt pair_zero pair_succ.
  Proof.
    constructor.
    - typeclasses eauto.
    - apply pair_lt_wf.
    - intros [m1 n1] [m2 n2]; simpl.
      destruct (index_lt_eq_lt_dec m1 m2) as [[]|];
        destruct (index_lt_eq_lt_dec n1 n2) as [[]|].
      all: subst; firstorder.
    - intros [[m n] [H1 | [_ H1]]].
      + eapply (@index_zero_least SI); eauto.
      + eapply (@index_zero_least SJ); eauto.
    - intros [m n]; simpl. right; split; eauto.
    - intros [m1 n1] [m2 n2]; simpl; intros [|[]]; subst.
      + right. by left.
      + destruct (index_succ_least n1 n2); eauto; subst.
        * by left.
        * right. right. by split.
    - intros [m n]. destruct (index_dec_limit n) as [[n' ->]|].
      + left. by (exists (m, n')).
      + right; intros [m' n']; simpl; intros []; firstorder.
  Qed.

  Local Instance pairI : indexT := IndexT (I * J) pair_lt pair_zero pair_succ pair_index_mixin.

  Lemma pair_rc_right n m m': (n, m) ⪯ (n, m') ↔ m  ⪯ m'.
  Proof.
    split; intros [Heq | Heq].
    - injection Heq. auto.
    - destruct Heq as [[]%index_lt_irrefl | H]. right; apply H.
    - subst; auto.
    - right. right; auto.
  Qed.
End pair_index.

(** ** Automation *)

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
    | H0 : _ ≺ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ ⪯ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ = _ |- _ => assert_fails (constr_eq H H0); progress (try rewrite H in H0)
    end;
    repeat match goal with
    | H0 : _ ≺ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
    | H0 : _ ⪯ _ |- _ => assert_fails (constr_eq H H0); rewrite H in H0
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
  | succ ?a ≺ succ ?b => apply index_lt_succ_inj in H
  | succ ?a = succ ?b => apply index_succ_inj in H; repeat subst_assmpt
  end.
Ltac index_contra_solve_core cont :=
  subst_assmpt;
  match goal with
  | [H : ?a ≺ ?a |- _] => specialize (index_lt_irrefl _ H) as []
  | [H : ?a ≺ zero |- _] => by apply index_lt_zero_is_normal in H
  | [H : ?a = succ ?a |- _] => apply index_succ_neq in H as []
  | [H : succ ?a = ?a |- _] => symmetry in H; cont
  | [H : ?a ⪯ zero, H1 : ?b ≺ ?a |- _] => eapply index_lt_zero_is_normal, index_lt_le_trans; [apply H1 | apply H]
  | [H1 : ?a ≺ ?b, H2 : ?b ≺ succ ?a |- _] => specialize (index_lt_succ_tight _ _ H1 H2) as []
  | [H1 : ?a ⪯ ?b, H2 : ?b ≺ ?a |- _] => eapply index_lt_irrefl, index_le_lt_trans; [apply H1 | apply H2]
  | [H : succ ?a = zero |- _] => destruct (index_succ_not_zero _ H) as []
  | [H : zero = succ ?a |- _] => symmetry in H; destruct (index_succ_not_zero _ H) as []
  | [H : succ ?a ≺ ?a |- _] =>
      let H1 := fresh "H" in
        specialize (index_lt_trans _ _ _ H (index_succ_greater a)) as H1;
        apply index_lt_irrefl in H1 as []
  | [H : succ ?a ≺ succ ?b |- _ ] => normalise_hypot H; cont
  | [H : succ ?a = succ ?b |- _ ] => normalise_hypot H; cont
  | [H : succ ?a ⪯ ?b |- _] => destruct H; cont
  end.
(* infer by transitivity -- might be very expensive when many inferences can be done or even diverge *)
Ltac index_contra_solve_infer cont :=
  match goal with
  | [H1 : ?a ≺ ?b, H2 : ?b ≺ ?c |- _] =>
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
