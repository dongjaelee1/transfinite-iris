From iris.algebra Require Export ofe.
From iris.prelude Require Import options.
From transfinite.stepindex Require Import ofe.
Require Coq.Logic.ProofIrrelevance.
Set Primitive Projections.


(** different notions of limit uniqueness *)
Class BcomplUniqueLim `{SI : indexT} (A : ofe) `{!Cofe A} :=
  cofe_unique_lim (α : index) Hα (c d : bchain A α) :
    (∀ β (Hβ : β ≺ α), c β Hβ ≡{β}≡ d β Hβ) → lbcompl Hα c ≡{α}≡ lbcompl Hα d.
Global Hint Mode BcomplUniqueLim - ! ! : typeclass_instances.

Section pi.
  Import ProofIrrelevance.
  Lemma index_dec_limit_pi `{SI : indexT} (α : index) :
    ∀ (Hlim : index_is_limit α), index_dec_limit α = inr Hlim.
  Proof.
    intros Hlim. destruct index_dec_limit as [[β ->] | H].
    - exfalso. eapply index_limit_not_succ in Hlim. by apply Hlim.
    - by rewrite (proof_irrelevance _ H Hlim).
  Qed.

  Lemma cofe_unique_bcompl `{SI : indexT} (A : ofe) `{Hc: !Cofe A} {Hunique: BcomplUniqueLim A}:
    ∀ α Hα (c d : bchain A α), index_is_limit α →
      (∀ β (Hβ : β ≺ α), c β Hβ ≡{β}≡ d β Hβ) → bcompl Hα c ≡{α}≡ bcompl Hα d.
  Proof.
    intros ???? Hlim Hl.
    rewrite /bcompl. rewrite (index_dec_limit_pi _ Hlim).
    apply Hunique, Hl.
  Qed.
End pi.

(** OFEs truncated at a stepindex α*)
(* Equality at ordinals above α is fully determined by equality at α *)
Class Truncated `{SI : indexT} {A : ofe} (α : index) (x : A) := truncated y β: α ⪯ β → x ≡{α}≡ y ↔ x ≡{β}≡ y.
Global Arguments truncated {_ _} _ _ {_ } _ _ _.
Global Hint Mode Truncated - + ! ! : typeclass_instances.
Global Instance : Params (@Truncated) 2 := {}.

Class OfeTruncated `{SI : indexT} (A : ofe) (α : index) := ofe_truncated_truncated (x : A) :> Truncated α x.
Global Hint Mode OfeTruncated - + - : typeclass_instances.
Global Arguments OfeTruncated {_} _ _.

Lemma ofe_truncated_equiv `{SI : indexT} (A : ofe) (α : index) {H : OfeTruncated A α} :
  ∀ (x y : A), x ≡ y ↔ x ≡{α}≡ y.
Proof.
  intros x y. rewrite equiv_dist. split.
  - intros Hall. by apply Hall.
  - intros Hα β. destruct (index_le_total α β) as [He | He].
    + by apply ofe_truncated_truncated.
    + by eapply dist_mono'.
Qed.

Lemma ofe_truncated_dist `{SI : indexT} (A : ofe) (α : index) `{H : !OfeTruncated A α}:
  ∀ (x y : A) β, x ≡{β}≡ y ↔ x ≡{index_min β α}≡ y.
Proof.
  intros x y β. split; intros Heq.
  - eapply dist_mono'; [apply Heq | eapply index_min_le_l].
  - unfold index_min in Heq. destruct (index_le_total β α) as [H1 | H1]. 1: apply Heq.
    by eapply H.
Qed.

Global Instance discrete_is_truncated `{SI : indexT} (A : ofe) (α : index) `(H: !OfeDiscrete A) : OfeTruncated A α.
Proof.
  intros x y β Hα. split; intros H0.
  all: apply equiv_dist, ofe_discrete_discrete; (eapply dist_mono'; [apply H0 | apply index_zero_minimum]).
Qed.

Global Instance ofe_mor_truncated `{SI: indexT} {A B : ofe} α `{H : !OfeTruncated B α} : OfeTruncated (A -n> B) α.
Proof.
  intros f g β Hβ. split; intros Heq x.
  - apply ofe_truncated_truncated; auto.
  - rewrite ofe_truncated_truncated; eauto.
Qed.

(** Truncatable OFEs -- an OFE A is truncatable if, for every ordinal α, it admits a truncation [A]_{α} (again an OFE)
  and a bounded isomorphism (equality up to α) between A and [A]_{α}
*)
Definition boundedInverse `{SI: indexT} {X1 X2: ofe} (f : X2 -n> X1) (g : X1 -n> X2) (α : index) :=
  f ◎ g ≡{α}≡ cid ∧ g ◎ f ≡{α}≡ cid.
Lemma boundedInverse_antimono `{SI : indexT} {X1 X2 : ofe} (f : X2 -n> X1) (g : X1 -n> X2) (α β : index) :
  α ⪯ β → boundedInverse f g β → boundedInverse f g α.
Proof. intros Hle [H1 H2]. split; eapply dist_mono'; eauto. Qed.

Class Truncatable `{SI : indexT} (A : ofe):=
  {
    ofe_trunc_car (α : index) : ofe;
    ofe_trunc_truncated (α : index) : OfeTruncated (ofe_trunc_car α) α;
    ofe_trunc_truncate (α : index) : A -n> ofe_trunc_car α;
    ofe_trunc_expand (α : index) : ofe_trunc_car α -n> A;
    ofe_trunc_inverse (α : index) : boundedInverse (ofe_trunc_truncate α) (ofe_trunc_expand α) α;
  }.
Global Hint Mode Truncatable - - : typeclass_instances.
Global Arguments ofe_trunc_car {_ _ _} _.

(* FIXME: when printing, usually A is implicit (inferred from the Truncatable instance) and an underscore is printed.
  can we force Coq to infer & print the implicit argument ?*)
Notation "'[' A ']_{' α '}'" := (@ofe_trunc_car _ A  _ α) (only parsing).
Notation "'⌊' a '⌋_{' α '}'" := (ofe_trunc_truncate α a) (format "'⌊' a '⌋_{' α '}'").
Notation "'⌈' a '⌉_{' α '}'" := (ofe_trunc_expand α a) (format "'⌈' a '⌉_{' α '}'").

Section truncatable_props.
  Context `{SI : indexT} {A : ofe} `{Htrunc : !Truncatable A}.
  Lemma ofe_trunc_truncate_expand_id {α} :
    ofe_trunc_truncate α ◎ ofe_trunc_expand α ≡ cid.
  Proof. intros x. cbn. eapply ofe_truncated_equiv; first apply Htrunc. apply ofe_trunc_inverse. Qed.

  Lemma ofe_trunc_expand_truncate_id {α} : ofe_trunc_expand α ◎ ofe_trunc_truncate α ≡{α}≡ cid.
  Proof. apply ofe_trunc_inverse. Qed.

  Global Instance Truncatable_truncated (α : index) : OfeTruncated (ofe_trunc_car (A := A) α) α
    := (@ofe_trunc_truncated _ A _  α).

  Section truncatable_cofe.
    Context (γ: index) {Ha : Cofe A}.

    Program Definition trunc_chain (c : chain ([A]_{γ})) : chain A :=
      mkchain _ A (λ α, ofe_trunc_expand γ (c α)) _.
    Next Obligation. intros c α' β Hle. cbn. by rewrite (chain_cauchy c α' β Hle). Qed.
    Program Definition trunc_bchain β (c : bchain ([A]_{γ}) β) : bchain A β :=
      mkbchain _ A β (λ γ' Hγ', ofe_trunc_expand γ (c γ' Hγ')) _.
    Next Obligation. intros β c β' γ' Hle Hβ Hγ'. cbn. f_equiv. by apply bchain_cauchy. Qed.

    Global Program Instance Truncatable_cofe : Cofe ([A]_{γ}) :=
      {
        compl c := ⌊compl (trunc_chain c)⌋_{γ};
        lbcompl β Hβ c := ⌊lbcompl Hβ (trunc_bchain β c)⌋_{γ};
       }.
    Next Obligation.
      intros α' c. cbn.
      rewrite ofe_truncated_dist.
      setoid_rewrite (dist_mono' _ _ _ _ (conv_compl α' _)). 2: apply index_min_le_l.
      cbn. eapply dist_mono'.
      - apply equiv_dist, ofe_trunc_truncate_expand_id.
      - apply index_min_le_r.
    Qed.
    Next Obligation.
      intros α' Hα' c β Hβ. cbn. rewrite ofe_truncated_dist.
      unshelve setoid_rewrite (dist_mono' _ _ _ _ (conv_lbcompl _ _ _ β Hβ)); last by apply index_min_le_l.
      cbn. eapply dist_mono'.
      - apply equiv_dist, ofe_trunc_truncate_expand_id.
      - apply index_min_le_r.
    Qed.
    Next Obligation.
      intros α' Hα' c d β Heq. cbn. f_equiv.
      apply lbcompl_ne. intros γ' Hγ'. cbn. by f_equiv.
    Qed.

    Global Instance Truncatable_unique_lim {H : BcomplUniqueLim A}: BcomplUniqueLim ([A]_{γ}).
    Proof.
      intros β Hβ c d Heq. unfold lbcompl, Truncatable_cofe.
      f_equiv. apply H. intros β' Hβ'. cbn. by f_equiv.
    Qed.
  End truncatable_cofe.
End truncatable_props.

Section truncatable.
  Context `{SI : indexT} .

  Program Definition trunc_map  {A : ofe} {HtruncA : Truncatable A} {B : ofe} {HtruncB : Truncatable B}
  (α β : index) : (A -n> B) -n> ([A]_{α} -n> [B]_{β}) := λne f, ofe_trunc_truncate β ◎ f ◎ ofe_trunc_expand α.
  Next Obligation.
    intros A HtrucA B HtruncB α β γ f g Heq.
    apply ccompose_ne; [ |  reflexivity ]. apply ccompose_ne; auto.
  Qed.

  Context {A : ofe} {HtruncA : Truncatable A}.
  Context {B : ofe} {HtruncB : Truncatable B}.
  Lemma trunc_map_inv (f : A -n> B) (g : B -n> A) α β:
    α ⪯ β → boundedInverse f g α → boundedInverse (trunc_map α β f) (trunc_map β α g) α.
  Proof.
    intros Hle [H1 H2]. split; intros x.
    - unfold trunc_map. cbn.
      rewrite ofe_truncated_dist.
      rewrite ofe_mor_ne. 2: { eapply dist_mono'. 2: apply index_min_le_l.
        setoid_rewrite (ofe_trunc_expand_truncate_id _). apply H1.
      }
      cbn. apply equiv_dist, ofe_trunc_truncate_expand_id.
    - cbn. rewrite ofe_mor_ne.
      2: { rewrite ofe_mor_ne. 2: { eapply dist_mono'; first setoid_rewrite (ofe_trunc_expand_truncate_id _); cbn. all: eauto. }
        apply H2.
      }
      apply equiv_dist, ofe_trunc_truncate_expand_id.
  Qed.

  Context {C : ofe} {HtruncC : Truncatable C}.
  Lemma trunc_map_compose (f : A -n> B) (g : B -n> C) α β γ :
    trunc_map α β (g ◎ f) ≡{γ}≡ trunc_map γ β g ◎ trunc_map α γ f.
  Proof.
    cbn. setoid_rewrite ccompose_assoc at 2. setoid_rewrite (proj1 (equiv_dist _ _) (ccompose_assoc _ _ _)) at 3.
    setoid_rewrite <- (proj1 (equiv_dist _ _) (ccompose_assoc _ _ _)) at 3.
    setoid_rewrite (dist_mono' _ _ _ _ (ofe_trunc_expand_truncate_id)); [ | auto].
    by intros x.
  Qed.
End truncatable.


(** a more elementary property than Truncatable. Essentially, proto_trunc α chooses a unique representative of each equivalence class of ≡{α}≡ *)
Class ProtoTruncatable `{SI : indexT} (A : ofe) :=
  {
    proto_trunc α : A -n> A;
    proto_compat α (x y : A) : x ≡{α}≡ y → proto_trunc α x ≡ proto_trunc α y;
    proto_ne α x : proto_trunc α x ≡{α}≡ x;
  }.
Global Hint Mode ProtoTruncatable - + : typeclass_instances.

Section proto.
  Context `{SI : indexT} (A : ofe) `{Hcofe : !Cofe A} {Htrunc : ProtoTruncatable A}.

  (** basic facts about proto truncatability *)
  Fact proto_trunc_idempotent (a : A) α: proto_trunc α (proto_trunc α a) ≡ proto_trunc α a.
  Proof. apply proto_compat. apply proto_ne. Qed.

  Lemma proto_trunc_dist_min (a b : A) α γ : a ≡{index_min α γ}≡ b → proto_trunc α a ≡{γ}≡ proto_trunc α b.
  Proof.
    intros H. unfold index_min in H. destruct (index_le_total α γ) as [Hle | Hgt].
    - eapply equiv_dist, proto_compat, H.
    - apply ofe_mor_ne, H.
  Qed.
End proto.

(** We show that ProtoTruncatable implies Truncatable *)
(* For defining the truncated types, we wrap the OFE A in an inductive in order to not confuse typeclass inference when defining a different equivalence on it. *)
Inductive trunc_truncation `{SI : indexT} (A : ofe) (β : index) := trunc_truncationC (a : A).
Section proto_truncatable.
  Context `{SI : indexT} (A : ofe) (Htrunc : ProtoTruncatable A).

  Section trunc_def.
    Context (α : index).
    Local Definition truncembed (a : trunc_truncation A α): A := match a with trunc_truncationC _ _ a => a end.

    Instance trunc_truncation_equiv : Equiv (trunc_truncation A α) := λ a b, proto_trunc α (truncembed a) ≡ proto_trunc α (truncembed b).
    Lemma trunc_truncation_equiv_unfold a b : a ≡ b ↔ proto_trunc α (truncembed a) ≡ proto_trunc α (truncembed b).
    Proof. tauto. Qed.

    Instance trunc_truncation_dist : Dist (trunc_truncation A α) :=
      λ n a b, proto_trunc α (truncembed a) ≡{n}≡ proto_trunc α (truncembed b).

    Lemma trunc_truncation_dist_unfold a b n : a ≡{n}≡ b ↔ proto_trunc α (truncembed a) ≡{n}≡ proto_trunc α (truncembed b).
    Proof. tauto. Qed.

    Definition trunc_truncation_ofe_mixin : OfeMixin (trunc_truncation A α).
    Proof.
      split.
      - setoid_rewrite trunc_truncation_dist_unfold. setoid_rewrite trunc_truncation_equiv_unfold.
        intros x y. split; intros H.
        + intros β. by apply equiv_dist.
        + apply equiv_dist. intros γ. apply (H γ).
      - intros α'. unfold dist, trunc_truncation_dist. split; auto.
        intros a b c -> ->. auto.
      - setoid_rewrite trunc_truncation_dist_unfold. intros α' β x y Heq Hlt. eauto using dist_mono.
    Qed.
    Canonical Structure tcar_truncO : ofe := Ofe (trunc_truncation A α) trunc_truncation_ofe_mixin.

    Program Definition tcar_trunc : A -n> tcar_truncO := λne a, trunc_truncationC A α a.
    Next Obligation.
      intros β x y. rewrite trunc_truncation_dist_unfold; cbn. intros Heq.
      by apply ofe_mor_ne.
    Qed.

    Program Definition tcar_embed : tcar_truncO -n> A := λne a, proto_trunc α (truncembed a).
    Next Obligation.
      intros β [x] [y]. rewrite trunc_truncation_dist_unfold; cbn. auto.
    Qed.

    Lemma tcar_trunc_embed_inv : boundedInverse tcar_trunc tcar_embed α.
    Proof.
      split.
      - intros x. rewrite trunc_truncation_dist_unfold. cbn. destruct x. cbn.
        apply equiv_dist. apply proto_trunc_idempotent.
      - intros x. cbn. apply proto_ne.
    Qed.
  End trunc_def.

  Global Program Instance ProtoTruncatable_is_Truncatable : Truncatable A :=
    {
    ofe_trunc_car α := tcar_truncO α;
    ofe_trunc_expand α := tcar_embed α;
    ofe_trunc_truncate α := tcar_trunc α;
    }.
  Next Obligation.
    intros α x y β Hle. split.
    - rewrite !trunc_truncation_dist_unfold. destruct x, y. cbn. intros H. apply equiv_dist. apply proto_compat.
      rewrite <- proto_ne. setoid_rewrite <- proto_ne at 3. apply H.
    - intros H. eapply dist_mono'; first apply H. apply Hle.
  Qed.
  Next Obligation.
    intros α. apply tcar_trunc_embed_inv.
  Qed.
  Global Opaque ProtoTruncatable_is_Truncatable.
End proto_truncatable.

(** We can show that every OFE is truncatable and every COFE can be equipped with strongly unique limits, using classical logic with choice. *)
Require Coq.Logic.Epsilon.
Require Coq.Logic.Classical.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Logic.PropExtensionality.
Section classical_truncation.
  Context `{SI : indexT}.
  Context (A : ofe).

  (** First we show that we can get a "truncation" operation for arbitrary decidable equivalence relations.
    We later instantiate this with dist and dist_later *)
  Section fix_alpha.
    Context (P : A → A → Prop).
    Import Epsilon.
    Lemma binary_choice (X : Prop) : (X ∨ ~X) → {X} + {~ X}.
    Proof.
      intros H.
      assert (H0: exists (b : bool), if b then X else ¬ X).
      { destruct H as [H | H]; first by exists true. by exists false. }
      apply constructive_indefinite_description in H0 as [[] H0]; auto.
    Qed.

    Context (Pdec : ∀ a b, {P a b} + {¬ P a b}).
    Context {P_equiv : Equivalence P}.
    Existing Instance P_equiv.

    Definition choice_fun (a : A) := λ (b : A), if Pdec a b then true else false.

    Import FunctionalExtensionality.
    Lemma choice_fun_ext (a b : A) : P a b → choice_fun a = choice_fun b.
    Proof using P_equiv.
      intros H. apply functional_extensionality.
      intros x. unfold choice_fun.
      destruct (Pdec a x) as [H1 | H1], (Pdec b x) as [H2 | H2]; try reflexivity; exfalso.
      - apply H2. etransitivity; first (symmetry; exact H). exact H1.
      - apply H1. etransitivity; eauto.
    Qed.

    Lemma choice_fun_exists (a : A) : ∃ b, choice_fun a b = true.
    Proof using P_equiv.
      exists a. unfold choice_fun. destruct Pdec as [ | H1]; [reflexivity | exfalso; apply H1; reflexivity].
    Qed.

    Definition choose_witness (a : A) := proj1_sig (constructive_indefinite_description _ (choice_fun_exists a)).
    Lemma witness_P (a : A) : P a (choose_witness a).
    Proof.
      assert (choice_fun a (choose_witness a) = true).
      { apply (proj2_sig (constructive_indefinite_description _ (choice_fun_exists a))). }
      unfold choice_fun in H.
      destruct Pdec as [H1 | H1]; first assumption. congruence.
    Qed.

    Import PropExtensionality.
    Lemma witness_unique (R Q : A → Prop) (H0 : ∃ a, R a) (H1 : ∃ b, Q b) :
      (∀ a, R a ↔ Q a)
      → proj1_sig (constructive_indefinite_description R H0) = proj1_sig (constructive_indefinite_description Q H1).
    Proof.
      intros H.
      assert (H2 : R = Q).
      { apply functional_extensionality. intros x. apply propositional_extensionality, H. }
      subst.
      rewrite (proof_irrelevance _ H0 H1). reflexivity.
    Qed.

    Lemma choose_witness_choice (a b : A) : P a b → choose_witness a = choose_witness b.
    Proof.
      intros H. unfold choose_witness.
      apply witness_unique. intros x.
      apply choice_fun_ext in H. by rewrite H.
    Qed.
  End fix_alpha.

  Import Classical.
  Lemma dec_dist α (x y : A) : { x ≡{α}≡ y} + {~ x ≡{α}≡ y}.
  Proof. apply binary_choice. apply classic. Qed.

  Program Definition trunc (α : index) := λne a, choose_witness (dist α) (dec_dist α) a.
  Next Obligation.
    intros α β a b Heq.
    destruct (index_le_lt_dec α β) as [H1 | H1].
    - unshelve erewrite (choose_witness_choice _ _ a b _). { eapply dist_mono'; eassumption. }
      reflexivity.
    - rewrite <- (dist_mono _ _ _ _ (witness_P _ _  a)). 2 : assumption.
      rewrite <- (dist_mono _ _ _ _ (witness_P _ _ b)). 2: assumption.
      apply Heq.
  Qed.

  (* classical ProtoTruncatable instance for arbitrary OFEs *)
  Instance classical_proto_trunc : ProtoTruncatable A.
  Proof.
    exists trunc.
    - intros. unfold trunc. cbn. by rewrite (choose_witness_choice _ _  x y H).
    - intros. symmetry. unfold trunc. cbn. apply witness_P.
  Qed.

  (* Now we can use a similar technique to show that any COFE is StronglyUnique *)
  Lemma dec_dist_later α (x y : A) : { dist_later α x y} + {¬ dist_later α x y}.
  Proof. apply binary_choice. apply classic. Qed.

  Program Definition trunc_dist_later (α : index) := λne a, choose_witness (dist_later α) (dec_dist_later α) a.
  Next Obligation.
    intros α β a b Heq.
    destruct (index_le_lt_dec α β) as [H1 | H1].
    - unshelve erewrite (choose_witness_choice _ _ a b _).
      { split. intros γ H. eapply dist_mono; first apply Heq. eapply index_lt_le_trans; eauto. }
      reflexivity.
    - specialize (@witness_P (dist_later α) (dec_dist_later α) _ a) as [Ha].
      rewrite -(Ha β H1).
      specialize (@witness_P (dist_later α) (dec_dist_later α) _ b) as [Hb].
      rewrite -(Hb β H1).
      assumption.
  Qed.

  Lemma trunc_dist_later_eq α a: dist_later α a (trunc_dist_later α a).
  Proof. unfold trunc_dist_later. cbn. apply witness_P. Qed.
  Lemma trunc_dist_later_pre α a b : dist_later α a b → trunc_dist_later α a ≡ trunc_dist_later α b.
  Proof. intros H. unfold trunc_dist_later. cbn. by rewrite (choose_witness_choice _ _ a b H). Qed.

  Context {Hcofe : Cofe A}.

  (* we can prove, under these classical assumptions, that we can always make limits unique *)
  Program Definition classical_strict_lbcompl α (Hα : index_is_proper_limit α) (c : bchain A α) :=
    trunc_dist_later α (lbcompl Hα c).

  Program Instance classical_strict_cofe : Cofe A :=
  { compl := @compl SI A _;
    lbcompl := classical_strict_lbcompl;
  }.
  Next Obligation. apply conv_compl. Qed.
  Next Obligation.
    intros α Hα c β Hβ. unfold classical_strict_lbcompl.
    rewrite ofe_mor_ne.
    2: { rewrite conv_lbcompl. cbn. reflexivity. }
    specialize (trunc_dist_later_eq α (c β Hβ)) as [Hc].
    rewrite Hc //.
  Qed.
  Next Obligation.
    intros. unfold classical_strict_lbcompl.
    destruct (index_le_lt_dec n m) as [H1 | H1].
    - apply ofe_mor_ne. apply lbcompl_ne, H.
    - specialize (trunc_dist_later_eq n (lbcompl Hn c)) as [Hc].
      rewrite -Hc //.
      specialize (trunc_dist_later_eq n (lbcompl Hn d)) as [Hd].
      rewrite -Hd //.
      apply lbcompl_ne, H.
  Qed.

  Instance classical_LimUnique : @BcomplUniqueLim _ A classical_strict_cofe.
  Proof.
    intros α Hα c d H1. unfold classical_strict_cofe, lbcompl, classical_strict_lbcompl.
    apply equiv_dist. apply trunc_dist_later_pre. split. intros β Hβ.
    unshelve rewrite !conv_lbcompl; last apply H1. apply Hβ.
  Qed.
End classical_truncation.
