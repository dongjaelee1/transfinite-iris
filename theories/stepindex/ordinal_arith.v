
From iris.prelude Require Import options.
From transfinite.prelude Require Import prelude.
From iris.algebra Require Import stepindex.
From transfinite.stepindex Require Export ordinals utils.


(* Natural Addition, also called Hessenberg Addition *)
Polymorphic Class NaturalAddition (A : Type) := nadd : A → A → A.
Global Hint Mode NaturalAddition ! : typeclass_instances.
Infix "⊕" := nadd (at level 60) : stdpp_scope.
Notation "(⊕)" := nadd (only parsing) : stdpp_scope.
Global Instance: Params (@nadd) 1 := {}.



Section ordinals.
  Local Open Scope ordinals.
  Set Universe Polymorphism.
  Polymorphic Universe i.
  Implicit Types α β γ δ : ord@{i}.


  (* general step-index lemmas *)
  Lemma ord_linear α β: α ≺ β ∨ α = β ∨ β ≺ α.
  Proof.
    destruct (ordinal_linear α β) as [|[Heq % ord_extensional|]]; eauto.
  Qed.

  Lemma ord_leq_eq α β: α ⪯ β ∧ β ⪯ α → α = β.
  Proof.
    intros [H1 % ord_leq_unfold H2 % ord_leq_unfold].
    by apply ord_extensional, eq_ext.
  Qed.

  (* better names*)
  Lemma ord_lt_leq α β γ: α ≺ β → β ⪯ γ → α ≺ γ.
  Proof.
    intros ? [->|?]; eauto; etransitivity; eauto.
  Qed.

  Lemma ord_leq_lt α β γ: α ⪯ β → β ≺ γ → α ≺ γ.
  Proof.
    intros [->|?] ?; eauto; etransitivity; eauto.
  Qed.

  Lemma succ_mono_leq α β: α ⪯ β → succ α ⪯ succ β.
  Proof.
    intros H; by eapply succ_least_greater, index_succ_iff.
  Qed.

  Lemma succ_mono_lt α β: α ≺ β → succ α ≺ succ β.
  Proof.
    intros Hα. eapply ord_leq_lt; last eapply succ_greater.
    by eapply succ_least_greater.
  Qed.

  Lemma succ_inj α β: succ α = succ β → α = β.
  Proof.
    intros Hα. destruct (ord_linear α β) as [H % succ_mono_lt|[|H%succ_mono_lt]]; auto.
    all: rewrite Hα in H; exfalso; eapply index_lt_irrefl; eapply H.
  Qed.

  Lemma succ_inj_lt α β: succ α ≺ succ β → α ≺ β.
  Proof.
    rewrite succ_leq_iff; intros [<-|Hα].
    - apply succ_greater.
    - eapply ord_lt_leq; first apply succ_greater; auto.
  Qed.

  Lemma succ_inj_leq α β: succ α ⪯ succ β → α ⪯ β.
  Proof.
    intros [H % succ_inj|H % succ_inj_lt]; eauto.
  Qed.

  Lemma zero_succ α: zero ≺ succ α.
  Proof.
    eapply ord_lt_leq; first apply succ_greater.
    eapply succ_mono_leq, SIdx.le_0_l.
  Qed.


  (* set ordinal specific *)
  Lemma zero_no_elements : typeof zero → False.
  Proof.
    intros x. eapply zero_least, (ordinals_lt _ x).
  Qed.

  Lemma one_elements_are_zero x: ordinals (succ zero) x = zero.
  Proof.
    apply ord_leq_eq; split; last apply SIdx.le_0_l.
    apply succ_inj_leq, succ_least_greater, ordinals_lt.
  Qed.

  (* ordinals and Well-Founded Relations *)
  Section well_founded.
    Context {X: Type} {R: X → X → Prop}.

    Record successors (x: X) := successors_of {
      next:> X;
      is_successor: R next x
    }.
    Arguments next {_} _.
    Arguments successors_of {_} _.
    Arguments is_successor {_} _.

    Fixpoint acc_ord {x} (a: Acc R x) : ord :=
      match a with
      | Acc_intro _ f => limit (λ (y: successors x), succ (acc_ord (f y (is_successor y))))
      end.

    Lemma acc_ord_unfold {x} (a: Acc R x):
      acc_ord a = limit (λ (y: successors x), succ (@acc_ord y (Acc_inv a (is_successor y)))) .
    Proof.
      eapply Acc_inv_dep with (a :=  a); simpl; clear a x. auto.
    Qed.


    Lemma acc_ord_pi {x} (a b: Acc R x): acc_ord a = acc_ord b.
    Proof.
      revert b. eapply Acc_inv_dep with (a :=  a); simpl; clear a x.
      intros x f IH; intros [g]; simpl.
      apply limit_ext.
      intros []; f_equal; apply IH.
    Qed.


    Lemma acc_ord_lt {x y} (a: Acc R x) (b: Acc R y):
      R y x → acc_ord b ≺ acc_ord a.
    Proof.
      intros Hr; rewrite (acc_ord_unfold a).
      eapply ord_lt_leq; first apply succ_greater.
      eapply limit_upper_bound_strong.
      intros β Hlt. exists (successors_of _ Hr); simpl.
      by rewrite acc_ord_pi.
    Qed.

    Corollary acc_ord_lt' {x y} (a: Acc R x) (H: R y x):
      acc_ord (Acc_inv a H) ≺ acc_ord a.
    Proof.
      apply (acc_ord_lt _ _ H).
    Qed.

    (* A single ordinal for an entire well-founded relation *)
    Definition wf_ord (wf: well_founded R) := limit (λ x, succ (acc_ord (wf x))).

    Lemma wf_ord_is_larger (wf: well_founded R) x:
      acc_ord (wf x) ≺ wf_ord wf.
    Proof.
      rewrite /wf_ord.
      eapply ord_lt_leq; first apply succ_greater.
      eapply limit_upper_bound_strong.
      intros β Hlt. by exists x.
    Qed.

  End well_founded.
  Arguments next {_ _ _} _.
  Arguments successors_of {_ _ _} _.
  Arguments is_successor {_ _ _} _.

  Section well_founded_embedding.
    Variable (X Y: Type) (R: X → X → Prop) (S: Y → Y → Prop) (sim: X → Y → Prop).
    Hypothesis (embed: ∀ x x' y, R x' x → sim x y → ∃ y', S y' y ∧ sim x' y').

    Lemma embed_acc {y} (b: Acc S y): ∀ x, sim x y → Acc R x.
    Proof using R S X Y embed sim.
      induction b as [y _ IH]. intros x Hsim. constructor.
      intros x' Hr. edestruct embed as [y' [HS Hsim']]; eauto.
    Qed.

    Lemma acc_ord_embed' y (b: Acc S y):
      ∀ x (H: sim x y), acc_ord (embed_acc b _ H) ⪯ acc_ord b.
    Proof.
      eapply Acc_inv_dep with (a :=  b); simpl; clear y b.
      intros y a IH x Hsim. rewrite acc_ord_unfold. eapply limit_mono_strong.
      intros [x' Hstep]. edestruct embed as [y' [HS Hsim']]; first apply Hstep; first apply Hsim.
      exists (successors_of y' HS). apply succ_mono_leq; simpl.
      transitivity (acc_ord (embed_acc (a y' HS) x' Hsim')).
      - left. apply acc_ord_pi.
      - apply IH.
    Qed.

    Lemma acc_ord_embed x y (b: Acc S y) (a: Acc R x): sim x y → acc_ord a ⪯ acc_ord b.
    Proof using R S X Y embed sim.
      intros Hsim. etransitivity; last eapply (acc_ord_embed' _ _ x Hsim).
      left. apply acc_ord_pi.
    Qed.

    Lemma acc_ord_strict y y' (b: Acc S y') x (a: Acc R x):
      S y y' → sim x y → acc_ord a ≺ acc_ord b.
    Proof using R S X Y embed sim.
      intros H Hsim. eapply ord_leq_lt with (β := acc_ord (Acc_inv b H)).
      - by eapply acc_ord_embed.
      - eapply acc_ord_lt; auto.
    Qed.

    Lemma wf_ord_embed (wfS: well_founded S) (wfR: well_founded R): (∀ x, ∃ y, sim x y) → wf_ord wfR ⪯ wf_ord wfS.
    Proof using R S X Y embed sim.
      intros Hsim. eapply limit_mono_strong. intros x. destruct (Hsim x) as [y Hsim']. exists y.
      by eapply succ_mono_leq, acc_ord_embed.
    Qed.

    (* With functions it is trivial to construct the simulation relation *)
    Definition im_rel (f: X → Y) x y := y = f x.

    Lemma im_rel_ex f: ∀ x, ∃ y, im_rel f x y.
    Proof. intros x. by exists (f x). Qed.

    Lemma im_rel_embed f:
      (∀ x x', R x x' → S (f x) (f x')) →
      (∀ x x' y, R x' x → im_rel f x y → ∃ y', S y' y ∧ im_rel f x' y').
    Proof.
      intros Hrel x x' y Hr ->. exists (f x'). split; by eauto.
    Qed.

  End well_founded_embedding.


  Section simultaneous_induction.
  Inductive interleave {X Y} (R: X → X → Prop) (S: Y → Y → Prop): (X * Y) → (X * Y) → Prop :=
  | interleave_L (x x': X) (y: Y): R x x' → interleave R S (x, y) (x', y)
  | interleave_R x y y': S y y' → interleave R S (x, y) (x, y').

  Lemma interleave_wf {X Y} (R: X → X → Prop) (S: Y → Y → Prop): well_founded R → well_founded S → well_founded (interleave R S).
  Proof.
    intros wfR wfS. intros [x y].
    revert y; induction (wfR x) as [x _ IHx]; intros y.
    induction (wfS y) as [y _ IHy].
    constructor. intros p H. inversion H; subst; eauto.
  Qed.


  Definition ord_rect2 := Fix (interleave_wf _ _ wf_ord_lt wf_ord_lt).

  (* TODO: add to stdpp *)
  Lemma rtc_acc {X} (R: X → X → Prop) x y: rtc R y x → Acc R x → Acc R y.
  Proof.
    induction 1; auto.
    intros Hacc. apply IHrtc; auto.
  Qed.

  Lemma tc_inv_rtc {X} (R: X → X → Prop) x y: tc R x y → ∃ z, rtc R x z ∧ R z y.
  Proof.
    induction 1.
    - exists x; split; by auto.
    - destruct IHtc as [z' [Hr Hrtc]].
      exists z'; split; auto. by econstructor 2.
  Qed.

  Lemma rtc_embed_tc {X} (R: X → X → Prop) x y: rtc R x y → rtc (tc R) x y.
  Proof.
    induction 1; first reflexivity.
    econstructor 2; eauto using tc_once.
  Qed.

  Lemma tc_wf {X} (R: X → X → Prop): well_founded R → well_founded (tc R).
  Proof.
    intros H x. specialize (H x). induction H as [x H IH].
    constructor. intros y [z [Hrtc Hr]] % tc_inv_rtc.
    eapply rtc_acc; last apply IH; eauto. by eapply rtc_embed_tc.
  Qed.

  Lemma interleave_tc_wf {X Y} (R: X → X → Prop) (S: Y → Y → Prop): well_founded R → well_founded S → well_founded (tc (interleave R S)).
  Proof.
    intros wfR wfS. by apply tc_wf, interleave_wf.
  Qed.

  Definition ord_rect2_strong := Fix (interleave_tc_wf _ _ wf_ord_lt wf_ord_lt).

  End simultaneous_induction.


  Section natural_addition.

  Definition natural_addition α β: ord@{i} :=
    ord_rect2 (λ _, ord) (λ '(α, β) add,
      limit (λ (s: typeof α + typeof β),
      match s with
      | inl a => succ (add (ordinals α a, β) (interleave_L _ _ _ _ _ (ordinals_lt α a)))
      | inr b => succ (add (α, ordinals β b) (interleave_R _ _ _ _ _ (ordinals_lt β b)))
      end))
      (* max (limitO a (λ γ Hγ, succ (IH (γ, b) (interleave_L _ _ _ _ _ Hγ)))) (limitO b (λ γ Hγ, succ (IH (a, γ) (interleave_R _ _ _ _ _ Hγ))))) *)
    (α, β).



    Global Instance natural_addition_operator: NaturalAddition ord := natural_addition.

    Lemma natural_addition_nadd α β: α ⊕ β = natural_addition α β.
    Proof. reflexivity. Qed.

    Lemma natural_addition_unfold α β:
      α ⊕ β = limit (λ (s: typeof α + typeof β),
      match s with
      | inl a => succ (ordinals α a ⊕ β)
      | inr b => succ (α ⊕ ordinals β b)
      end).
    Proof.
      rewrite natural_addition_nadd /natural_addition /ord_rect2 Fix_eq; first reflexivity.
      intros [x y] f g H. eapply limit_ext.
      all: intros []; f_equal; eauto.
    Qed.



    Lemma natural_addition_zero_left_id α: zero ⊕ α = α.
    Proof.
      induction α as [α IH] using ord_ind.
      rewrite natural_addition_unfold; apply ord_leq_eq; split.
      - apply limit_least_upper_bound; intros [t| a]; first destruct (zero_no_elements t).
        rewrite IH; last apply ordinals_lt.
        apply succ_least_greater, ordinals_lt.
      - apply limit_upper_bound_strong. intros β [x Hβ] % in_inv_elements.
        exists (inr x). rewrite IH; last apply ordinals_lt.
        rewrite ord_lt_unfold Hβ. apply succ_greater.
    Qed.

    Lemma natural_addition_comm α β: α ⊕ β = β ⊕ α.
    Proof.
      revert β; induction α as [α IHα] using ord_ind; intros β.
      induction β as [β IHβ] using ord_ind.
      rewrite !natural_addition_unfold; eapply ord_leq_eq.
      split; eapply limit_mono_strong.
      - intros [a|b]; first exists (inr a); last exists (inl b).
        + rewrite IHα; eauto; apply ordinals_lt.
        + rewrite IHβ; eauto; apply ordinals_lt.
      - intros [b|a]; first exists (inr b); last exists (inl a).
      + rewrite IHβ; eauto; apply ordinals_lt.
      + rewrite (IHα (ordinals α a)); eauto; apply ordinals_lt.
    Qed.

    Lemma natural_addition_zero_right_id α: α ⊕ zero = α.
    Proof.
      by rewrite natural_addition_comm natural_addition_zero_left_id.
    Qed.

    Lemma natural_addition_strict_compat α β γ: α ≺ β → α ⊕ γ ≺ β ⊕ γ.
    Proof.
      intros Hle. rewrite [β ⊕ γ]natural_addition_unfold.
      eapply union_set_characteristic. exists (succ (α ⊕ γ)); split.
      { apply succ_leq_iff. by left. }
      apply ord_lt_inv_ordinals in Hle as [b ->].
      by eapply (in_intro _ (inl b)).
    Qed.

    Lemma natural_addition_strict_compat' α β γ: α ≺ β → γ ⊕ α ≺ γ ⊕ β.
    Proof.
      intros H. rewrite [γ ⊕ α]natural_addition_comm [γ ⊕ β]natural_addition_comm.
      by eapply natural_addition_strict_compat.
    Qed.

    Global Instance natural_addition_lt_proper: Proper (ord_lt ==> ord_lt ==> ord_lt) nadd.
    Proof.
      intros α β Hαβ γ δ Hγδ; etransitivity; first apply natural_addition_strict_compat; eauto using natural_addition_strict_compat'.
    Qed.

    Lemma natural_addition_compat α β γ: α ⪯ β → α ⊕ γ ⪯ β ⊕ γ.
    Proof.
      intros [->|]; eauto using natural_addition_strict_compat.
    Qed.

    Lemma natural_addition_compat' α β γ: α ⪯ β → γ ⊕ α ⪯ γ ⊕ β.
    Proof.
      intros [->|]; eauto using natural_addition_strict_compat'.
    Qed.

    Global Instance natural_addition_leq_proper: Proper (rc ord_lt ==> rc ord_lt ==> rc ord_lt) nadd.
    Proof.
      intros α β Hαβ γ δ Hγδ; etransitivity; first apply natural_addition_compat; eauto using natural_addition_compat'.
    Qed.

    Lemma natural_addition_increase α β: α ⪯ α ⊕ β.
    Proof.
      Set Printing All.
      replace α with (zero ⊕ α) at 1 by apply natural_addition_zero_left_id.
      rewrite [α ⊕ β]natural_addition_comm.
      apply natural_addition_compat, SIdx.le_0_l.
    Qed.

    Lemma natural_addition_cancel α β γ: α ⊕ γ = β ⊕ γ → α = β.
    Proof.
      intros Heq. destruct (ord_linear α β) as [H|[|H]]; auto; exfalso.
      all: eapply (natural_addition_strict_compat _ _ γ) in H; rewrite Heq in H; eapply index_lt_irrefl; eauto.
    Qed.

    Lemma natural_addition_cancel_lt α β γ: α ⊕ γ ≺ β ⊕ γ → α ≺ β.
    Proof.
      intros Heq. destruct (ord_linear α β) as [H|[|H]]; auto; exfalso.
      - subst α. by eapply index_lt_irrefl.
      - eapply (natural_addition_strict_compat _ _ γ) in H.
        eapply index_lt_irrefl. etransitivity; eauto.
    Qed.

    Lemma natural_addition_cancel_leq α β γ: α ⊕ γ ⪯ β ⊕ γ → α ⪯ β.
    Proof.
      intros [?%natural_addition_cancel |? % natural_addition_cancel_lt]; eauto.
    Qed.


    Lemma natural_addition_limit (X: Type@{i}) (f: X → ord@{i}) (α : ord@{i}):
      limit (λ x, f x ⊕ α) ⪯ limit f ⊕ α .
    Proof.
      eapply limit_least_upper_bound. intros x.
      eapply natural_addition_compat, limit_upper_bound.
    Qed.


    Lemma nat_add_inv α β γ: γ ≺ α ⊕ β → ∃ δ, (δ ≺ α ∧ γ ≺ succ (δ ⊕ β)) ∨ (δ ≺ β ∧ γ ≺ succ (α ⊕ δ)).
    Proof.
      intros H. rewrite natural_addition_unfold in H.
      eapply union_set_characteristic in H as [s [Hs Hin]].
      eapply ordinals.in_inv in Hin as [[a|b] ->].
      - exists (ordinals α a). left; split; auto using ordinals_lt.
      - exists (ordinals β b); right; split; auto using ordinals_lt.
    Qed.


    Lemma natural_addition_succ_1 α β: succ α ⊕ β ⪯ succ (α ⊕ β).
    Proof.
      induction β as [β IHβ] using ord_ind.
      apply ord_leq_ords. intros γ Hγ.
      apply nat_add_inv in Hγ as [δ [[Hδα Hlt]|[Hδβ Hlt]]].
      + eapply ord_lt_leq; first apply Hlt.
        eapply succ_least_greater in Hδα.
        eapply succ_mono_leq. eapply succ_inj_leq in Hδα.
        by eapply natural_addition_compat.
      + eapply ord_lt_leq; eauto.
        eapply succ_mono_leq. etransitivity.
        * eapply IHβ; auto.
        * by eapply succ_least_greater, natural_addition_strict_compat'.
    Qed.

    Lemma natural_addition_succ_2 α β: succ (α ⊕ β) ⪯ succ α ⊕ β.
    Proof.
      eapply succ_least_greater, natural_addition_strict_compat, succ_greater.
    Qed.

    Lemma natural_addition_succ α β: succ α ⊕ β = succ (α ⊕ β).
    Proof.
      eapply ord_leq_eq; split; eauto using natural_addition_succ_1, natural_addition_succ_2.
    Qed.


    Lemma natural_addition_assoc_1 α β γ: (α ⊕ β) ⊕ γ ⪯ α ⊕ (β ⊕ γ).
    Proof.
      revert β γ; induction α as [α IHα] using ord_ind; intros β.
      induction β as [β IHβ] using ord_ind; intros γ.
      induction γ as [γ IHγ] using ord_ind.
      rewrite natural_addition_unfold.
      eapply limit_least_upper_bound. intros [ab|c].
      - destruct (nat_add_inv _ _ _ (ordinals_lt _ ab)) as [δ [[Hδα Hlt]|[Hδβ Hlt]]].
        + specialize (IHα _ Hδα). apply succ_least_greater.
          eapply ord_lt_leq; first apply natural_addition_strict_compat, Hlt.
          rewrite natural_addition_succ. apply succ_least_greater.
          eapply ord_leq_lt; first eapply IHα.
          by eapply natural_addition_strict_compat.
        + specialize (IHβ _ Hδβ). apply succ_least_greater.
          eapply ord_lt_leq; first apply natural_addition_strict_compat, Hlt.
          rewrite natural_addition_succ. apply succ_least_greater.
          eapply ord_leq_lt; first eapply IHβ.
          eapply natural_addition_strict_compat'.
          by eapply natural_addition_strict_compat.
      - etransitivity.
        + eapply succ_mono_leq, IHγ; auto; apply ordinals_lt.
        + apply succ_least_greater.
          do 2 eapply natural_addition_strict_compat'; auto using ordinals_lt.
    Qed.

    Lemma natural_addition_assoc_2 α β γ: α ⊕ (β ⊕ γ) ⪯ (α ⊕ β) ⊕ γ.
    Proof.
      rewrite natural_addition_comm [β ⊕ γ]natural_addition_comm.
      rewrite [α ⊕ β]natural_addition_comm [_ ⊕ γ]natural_addition_comm.
      eapply natural_addition_assoc_1.
    Qed.

    Lemma natural_addition_assoc α β γ: (α ⊕ β) ⊕ γ = α ⊕ (β ⊕ γ).
    Proof.
      eapply ord_leq_eq; split; eauto using natural_addition_assoc_1, natural_addition_assoc_2.
    Qed.

  End natural_addition.

  Section ordinal_multiplication.
    (* multiplication by some natural number *)
    Fixpoint natmul (n: nat) α :=
      match n with
      | 0%nat => zero
      | S n => α ⊕ natmul n α
      end.

    Definition omul α := limit (λ n: nat, natmul n α).
    Lemma natmul_omul n α: natmul n α ⪯ omul α.
    Proof.
      apply (limit_upper_bound (λ n, natmul n α)).
    Qed.

    Lemma natmul_zero n: natmul n zero = zero.
    Proof.
      induction n as [|n IH]; simpl; auto.
      rewrite IH natural_addition_zero_left_id //=.
    Qed.

    Lemma omul_zero: zero = omul zero.
    Proof.
      apply ord_leq_eq; split.
      - eapply ord_leq_ords. intros ? [] % zero_least.
      - apply limit_least_upper_bound; intros n.
        by rewrite natmul_zero.
    Qed.
  End ordinal_multiplication.

End ordinals.
