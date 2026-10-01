From stdpp Require Import finite.
From iris.algebra Require Export cmra updates.
From iris.bi Require Import notation.
From iris.si_logic Require Import siprop.
From iris.prelude Require Import options.
From transfinite.stepindex Require Export existential_properties ofe functors.
From transfinite.algebra Require Import truncation.

Local Open Scope sidx_scope.

(* Set Primitive Projections. *)

Local Hint Extern 1 (_ ≼ _) => etrans; [eassumption|] : core.
Local Hint Extern 1 (_ ≼ _) => etrans; [|eassumption] : core.
Local Hint Extern 10 (_ ≤ _)%nat => lia : core.

(** The basic definition of the uPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

(** A good way of understanding this definition of the uPred OFE is to
   consider the OFE uPred0 of monotonous SProp predicates. That is,
   uPred0 is the OFE of non-expansive functions from M to SProp that
   are monotonous with respect to CMRA inclusion. This notion of
   monotonicity has to be stated in the SProp logic. Together with the
   usual closedness property of SProp, this gives exactly uPred_mono.

   Then, we quotient uPred0 *in the siProp logic* with respect to
   equivalence on valid elements of M. That is, we quotient with
   respect to the following *siProp* equivalence relation:
     P1 ≡ P2 := ∀ x, ✓ x → (P1(x) ↔ P2(x))       (1)
   When seen from the ambiant logic, obtaining this quotient requires
   definig both a custom Equiv and Dist.


   It is worth noting that this equivalence relation admits canonical
   representatives. More precisely, one can show that every
   equivalence class contains exactly one element P0 such that:
     ∀ x, (✓ x → P0(x)) → P0(x)                 (2)
   (Again, this assertion has to be understood in siProp). Intuitively,
   this says that P0 trivially holds whenever the resource is invalid.
   Starting from any element P, one can find this canonical
   representative by choosing:
     P0(x) := ✓ x → P(x)                        (3)

   Hence, as an alternative definition of uPred, we could use the set
   of canonical representatives (i.e., the subtype of monotonous
   siProp predicates that verify (2)). This alternative definition would
   save us from using a quotient. However, the definitions of the various
   connectives would get more complicated, because we have to make sure
   they all verify (2), which sometimes requires some adjustments. We
   would moreover need to prove one more property for every logical
   connective.
 *)

(** Note that, somewhat curiously, [uPred M] is *not* in general a Camera,
   at least not if all propositions are considered "valid" Camera elements.
   It fails to satisfy the extension axiom. Here is the counterexample:

We use [M := (option Ex {A,B})^2] -- so we have pairs
whose components are ε, A or B.

Let
[[
  P r n := (ownM (A,A) ∧ ▷ False) ∨ ownM (A,B) ∨ ownM (B,A) ∨ ownM (B,B)
         ↔ r = (A,A) ∧ n = 0 ∨
           r = (A,B) ∨
           r = (B,A) ∨
           r = (B,B)
 Q1 r n := ownM (A, ε) ∨ ownM (B, ε)
         ↔ (A, ε) ≼ r ∨ (B, ε) ≼ r
           ("Left component is not ε")
 Q2 r n := ownM (ε, A) ∨ ownM (ε, B)
         ↔ (ε, A) ≼ r ∨ (ε, B) ≼ r
           ("Right component is not ε")
]]
These are all sufficiently closed and non-expansive and whatnot.
We have [P ≡{0}≡ Q1 * Q2]. So assume extension holds, then we get Q1', Q2'
such that
[[
  P ≡ Q1' ∗ Q2'
 Q1 ≡{0}≡ Q1'
 Q2 ≡{0}≡ Q2'
]]
Now comes the contradiction:
We know that [P (A,A) 1] does *not* hold, but I am going to show that
[(Q1' ∗ Q2') (A,A) 1] holds, which would be a contraction.
To this end, I will show (a) [Q1' (A,ε) 1] and (b) [Q2' (ε,A) 1].
The result [(Q1' ∗ Q2') (A,A)] follows from [(A,ε) ⋅ (ε,A) = (A,A)].

(a) Proof of [Q1' (A,ε) 1].
    We have [P (A,B) 1], and thus [Q1' r1 1] and [Q2' r2 1] for some
    [r1 ⋅ r2 = (A,B)]. There are four possible decompositions [r1 ⋅ r2]:
    - [(ε,ε) ⋅ (A,B)]: This would give us [Q1' (ε,ε) 1], from which we
      obtain (through down-closure and the equality [Q1 ≡{0}≡ Q1'] above) that
      [Q1 (ε,ε) 0]. However, we know that's false.
    - [(A,B) ⋅ (ε,ε)]: Can be excluded for similar reasons
      (the second resource must not be ε in the 2nd component).
    - [(ε,B) ⋅ (A,ε)]: Can be excluded for similar reasons
      (the first resource must not be ε in the 1st component).
    - [(A,ε) ⋅ (ε,B)]: This gives us the desired [Q1' (A,ε) 1].

(b) Proof of [Q2' (ε,A) 1].
    We have [P (B,A) 1], and thus [Q1' r1 1] and [Q2' r2 1] for some
    [r1 ⋅ r2 = (B,A)]. There are again four possible decompositions,
    and like above we can exclude three of them. This leaves us with
    [(B,ε) ⋅ (ε,A)] and thus [Q2' (ε,A) 1].

This completes the proof.

*)

Record uPred {SI : sidx} (M : ucmra) : Type := UPred {
  uPred_holds : SI → M → Prop;

  uPred_mono n1 n2 x1 x2 :
    uPred_holds n1 x1 → x1 ≼{n2} x2 → n2 ≤ n1 → uPred_holds n2 x2
}.
(** When working in the model, it is convenient to be able to treat [uPred] as
[SI → M → Prop].  But we only want to locally break the [uPred] abstraction
this way. *)
Local Coercion uPred_holds : uPred >-> Funclass.
Bind Scope bi_scope with uPred.
Global Arguments uPred_holds {_ _} _ _ _ : simpl never.
Add Printing Constructor uPred.
Global Instance: Params (@uPred_holds) 4 := {}.

Section cofe.
  Context {SI : sidx} {M : ucmra}.

  Inductive uPred_equiv' (P Q : uPred M) : Prop :=
    { uPred_in_equiv : ∀ n x, ✓{n} x → P n x ↔ Q n x }.
  Local Instance uPred_equiv : Equiv (uPred M) := uPred_equiv'.
  Inductive uPred_dist' (n : SI) (P Q : uPred M) : Prop :=
    { uPred_in_dist : ∀ n' x, n' ≤ n → ✓{n'} x → P n' x ↔ Q n' x }.
  Local Instance uPred_dist : Dist (uPred M) := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin (uPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; eauto with si_solver.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q i x);[apply HP|apply HQ].
    - intros α β P Q HPQ Hpre; split=> i x ??; apply HPQ; last by eauto.
      etrans; eauto with si_solver.
  Qed.
  Canonical Structure uPredO : ofe := Ofe (uPred M) uPred_ofe_mixin.

  Program Definition uPred_compl : chain uPredO → uPredO := λ c,
    {| uPred_holds n x := ∀ n', n' ≤ n → ✓{n'} x → c n' n' x |}.
  Next Obligation.
    move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply uPred_mono.
    - eapply HP, cmra_validN_includedN, cmra_includedN_le=>//. etransitivity; eauto.
    - eapply cmra_includedN_le=>//; eauto with index.
    - done.
  Qed.

  Program Definition uPred_bcompl' α : bchain uPredO α → uPredO := λ c,
    {| uPred_holds n x := ∀ n' (Hn': n' < α), n' ≤ n →  ✓{n'}x → c n' Hn' n' x |}.
  Next Obligation.
    move=> /= α c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn3 Hn23 Hv. eapply uPred_mono.
    - eapply HP, cmra_validN_includedN, cmra_includedN_le=>//; etransitivity; eauto with index.
    - eapply cmra_includedN_le=>//; eauto with index.
    - done.
  Qed.
  Lemma uPred_bcompl'_ne α (c d : bchain uPredO α) (β : SI):
    (∀ (γ : SI) (Hγ : γ < α), c γ Hγ ≡{β}≡ d γ Hγ) →
    uPred_bcompl' α c ≡{β}≡ uPred_bcompl' α d.
  Proof.
    intros Hne; split=> i x Hiβ Hv; split.
    all: intros H' j Hjα Hji Hvj; specialize (H' j Hjα Hji Hvj); eapply Hne; [by etrans | by eauto | by eauto].
  Qed.

  Definition uPred_lbcompl α (Hα : SIdx.limit α) := uPred_bcompl' α.

  Global Program Instance uPred_cofe : Cofe uPredO :=
    {| compl := uPred_compl; lbcompl := uPred_lbcompl |}.
  Next Obligation.
    intros α c; split=>i x Hiα Hv.
    etrans; [|by symmetry; apply (chain_cauchy c)]. split=>H'; [by apply H'|].
    intros n' Hin' H. eapply (chain_cauchy c n' i); eauto with si_solver.
    by eapply uPred_mono.
  Qed.
  Next Obligation.
    intros α Hα c; split=>i x Hiα Hv.
    etrans; [|unshelve by symmetry; apply (bchain_cauchy α c)]; last by eapply SIdx.le_lt_trans; eauto.
    split=>H'; [by apply H'|]. intros n' Hn' Hin' H.
    unshelve eapply (bchain_cauchy α c n' i); [by eauto using SIdx.le_lt_trans | by eauto | by eauto | by eauto | ].
    by eapply uPred_mono.
  Qed.
  Next Obligation.
    intros. by apply uPred_bcompl'_ne.
  Qed.

  Lemma lbcompl_unfold α Hα (C: bchain uPredO α) n x: lbcompl Hα C n x ↔ ∀ n' (Hn': n' < α), n' ≤ n →  ✓{n'}x → C n' Hn' n' x.
  Proof. reflexivity. Qed.

  Lemma compl_unfold  (C: chain uPredO) n x: compl C n x ↔ ∀ n', n' ≤ n →  ✓{n'}x → C n' n' x.
  Proof. reflexivity. Qed.

  Global Program Instance truncatable : ProtoTruncatable uPredO :=
  {
    proto_trunc α := λne a, uPred_bcompl' (Sᵢ α) (bchain_const a (Sᵢ α)  );
  }.
  Next Obligation.
    intros α α' x y Heq. by apply uPred_bcompl'_ne.
  Qed.
  Next Obligation.
    intros α x y H. cbn. constructor => n x' Hvn; split.
    all: intros H' j Hjα Hjn Hvj; cbn; apply H, H'; auto.
    all: apply index_succ_iff in Hjα; auto.
  Qed.
  Next Obligation.
    intros α x. cbn. constructor => n x' Hnα Hvn. split.
    - intros H'. apply H'; auto with si_solver.
    - intros H'. intros j Hjα Hjn Hvj. cbn. eapply uPred_mono; eauto.
  Qed.

  Global Instance bcompl_unique : BcomplUniqueLim uPredO.
  Proof.
    intros α Hα c d Heq. constructor => n x Hna Hvn.
    rewrite !lbcompl_unfold. split; intros H n' Hn' Hle Hvn'; apply Heq; eauto with si_solver.
  Qed.

End cofe.
Global Arguments uPredO {_} _.

Global Instance uPred_ne {SI : sidx} {M} (P : uPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply uPred_mono; eauto with si_solver; by rewrite Hx.
Qed.
Global Instance uPred_proper {SI : sidx} {M} (P : uPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply uPred_ne, equiv_dist. Qed.

Lemma uPred_holds_ne {SI : sidx} {M} (P Q : uPred M) n1 n2 x :
  P ≡{n2}≡ Q → n2 ≤ n1 → ✓{n2} x → Q n1 x → P n2 x.
Proof.
  intros [Hne] ???. eapply Hne; try done. eauto using uPred_mono, cmra_validN_le.
Qed.

(* Equivalence to the definition of uPred in the appendix. *)
Lemma uPred_alt {SI : sidx} {M : ucmra} (P: SI → M → Prop) :
  (∀ n1 n2 x1 x2, P n1 x1 → x1 ≼{n1} x2 → n2 ≤ n1 → P n2 x2) ↔
  ( (∀ x n1 n2, n2 ≤ n1 → P n1 x → P n2 x) (* Pointwise down-closed *)
  ∧ (∀ n x1 x2, x1 ≡{n}≡ x2 → ∀ m, m ≤ n → P m x1 ↔ P m x2) (* Non-expansive *)
  ∧ (∀ n x1 x2, x1 ≼{n} x2 → ∀ m, m ≤ n → P m x1 → P m x2) (* Monotonicity *)
  ).
Proof.
  (* Provide this lemma to eauto. *)
  assert (∀ n1 n2 (x1 x2 : M), n2 ≤ n1 → x1 ≡{n1}≡ x2 → x1 ≼{n2} x2).
  { intros ????? H. eapply cmra_includedN_le; last done. by rewrite H. }
  (* Now go ahead. *)
  split.
  - intros Hupred. repeat split; eauto using cmra_includedN_le with si_solver.
  - intros (Hdown & _ & Hmono) **. eapply Hmono; [done..|]. eapply Hdown; done.
Qed.

(** functor *)
Program Definition uPred_map {SI : sidx} {M1 M2 : ucmra} (f : M2 -n> M1)
  `{!CmraMorphism f} (P : uPred M1) :
  uPred M2 := {| uPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using uPred_mono, cmra_morphism_monoN. Qed.

Global Instance uPred_map_ne {SI : sidx} {M1 M2 : ucmra} (f : M2 -n> M1)
  `{!CmraMorphism f} n : Proper (dist n ==> dist n) (uPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using cmra_morphism_validN.
Qed.
Lemma uPred_map_id {SI : sidx} {M : ucmra} (P : uPred M): uPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed.
Lemma uPred_map_compose {SI : sidx} {M1 M2 M3 : ucmra} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!CmraMorphism f, !CmraMorphism g} (P : uPred M3):
  uPred_map (g ◎ f) P ≡ uPred_map f (uPred_map g P).
Proof. by split=> n x Hx. Qed.
Lemma uPred_map_ext {SI : sidx} {M1 M2 : ucmra} (f g : M1 -n> M2)
      `{!CmraMorphism f} `{!CmraMorphism g}:
  (∀ x, f x ≡ g x) → ∀ x, uPred_map f x ≡ uPred_map g x.
Proof.
  intros Hf P; split=> n x Hx /=. rewrite /uPred_map.
  unfold uPred_holds; rewrite /= Hf //.
Qed.
Definition uPredO_map {SI : sidx} {M1 M2 : ucmra} (f : M2 -n> M1) `{!CmraMorphism f} :
  uPredO M1 -n> uPredO M2 := OfeMor (uPred_map f : uPredO M1 → uPredO M2).
Lemma uPredO_map_ne {SI : sidx} {M1 M2 : ucmra} (f g : M2 -n> M1)
    `{!CmraMorphism f, !CmraMorphism g} n :
  f ≡{n}≡ g → uPredO_map f ≡{n}≡ uPredO_map g.
Proof.
  intros Hfg P; split=> n' y ??. unfold uPredO_map, uPred_holds.
  by rewrite /= (dist_le _ _ _ _(Hfg y)).
Qed.

Program Definition uPredOF {SI : sidx} (F : turFunctor) : tFunctor := {|
  tFunctor_car A B := uPredO (turFunctor_car F B A);
  tFunctor_map A1 A2 B1 B2 fg := uPredO_map (turFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros SI F A1 A2 B1 B2 n P Q HPQ.
  apply uPredO_map_ne, turFunctor_map_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros SI F A B P; simpl. rewrite -{2}(uPred_map_id P).
  apply uPred_map_ext=>y. by rewrite turFunctor_map_id.
Qed.
Next Obligation.
  intros SI F A1 A2 A3 B1 B2 B3 f g f' g' P; simpl. rewrite -uPred_map_compose.
  apply uPred_map_ext=>y; apply turFunctor_map_compose.
Qed.

Global Instance uPredOF_contractive {SI : sidx} F :
  turFunctorContractive F → tFunctorContractive (uPredOF F).
Proof.
  intros ? A1 A2 B1 B2 n P Q HPQ.
  apply uPredO_map_ne, turFunctor_map_contractive.
  destruct HPQ as [HPQ]. constructor. intros ??.
  split; by eapply HPQ.
Qed.

(** logical entailement *)
Inductive uPred_entails {SI : sidx} {M} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
Global Hint Resolve uPred_mono : uPred_def.


(** logical connectives *)
(** Following upstream Iris, the pure embedding, internal equality, internal
validity and the plainly modality are no longer primitive connectives of
[uPred]. They are derived from the embedding [uPred_si_pure] of [siProp] and
from [uPred_si_emp_valid] via the [Sbi] interface (see [base_logic/bi.v]). *)
Local Program Definition uPred_si_pure_def {SI : sidx} {M}
    (Pi : siProp) : uPred M :=
  {| uPred_holds n x := siProp_holds Pi n |}.
Solve Obligations with naive_solver eauto using siProp_closed.
Local Definition uPred_si_pure_aux : seal (@uPred_si_pure_def).
Proof. by eexists. Qed.
Definition uPred_si_pure := uPred_si_pure_aux.(unseal).
Global Arguments uPred_si_pure {SI M}.
Local Definition uPred_si_pure_unseal :
  @uPred_si_pure = @uPred_si_pure_def := uPred_si_pure_aux.(seal_eq).

Local Program Definition uPred_si_emp_valid_def {SI : sidx} {M}
    (P : uPred M) : siProp :=
  {| siProp_holds n := P n ε |}.
Solve Obligations with naive_solver eauto with uPred_def.
Local Definition uPred_si_emp_valid_aux : seal (@uPred_si_emp_valid_def).
Proof. by eexists. Qed.
Definition uPred_si_emp_valid := uPred_si_emp_valid_aux.(unseal).
Global Arguments uPred_si_emp_valid {SI M}.
Local Definition uPred_si_emp_valid_unseal :
  @uPred_si_emp_valid = @uPred_si_emp_valid_def := uPred_si_emp_valid_aux.(seal_eq).

Local Program Definition uPred_and_def {SI : sidx} {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_and_aux : seal (@uPred_and_def). Proof. by eexists. Qed.
Definition uPred_and := uPred_and_aux.(unseal).
Global Arguments uPred_and {SI M}.
Local Definition uPred_and_unseal :
  @uPred_and = @uPred_and_def := uPred_and_aux.(seal_eq).

Local Program Definition uPred_or_def {SI : sidx} {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_or_aux : seal (@uPred_or_def). Proof. by eexists. Qed.
Definition uPred_or := uPred_or_aux.(unseal).
Global Arguments uPred_or {SI M}.
Local Definition uPred_or_unseal :
  @uPred_or = @uPred_or_def := uPred_or_aux.(seal_eq).

Local Program Definition uPred_impl_def {SI : sidx} {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       x ≼ x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros SI M P Q n1 n1' x1 x1' HPQ [x2 Hx1'] Hn1 n2 x3 [x4 Hx3] ?; simpl in *.
  rewrite Hx3 (dist_le _ _ _ _ Hx1'); auto. intros ??.
  eapply HPQ; [ | by etrans | auto | auto]. exists (x2 ⋅ x4). by rewrite assoc.
Qed.
Local Definition uPred_impl_aux : seal (@uPred_impl_def). Proof. by eexists. Qed.
Definition uPred_impl := uPred_impl_aux.(unseal).
Global Arguments uPred_impl {SI M}.
Local Definition uPred_impl_unseal :
  @uPred_impl = @uPred_impl_def := uPred_impl_aux.(seal_eq).

Local Program Definition uPred_forall_def {SI : sidx} {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_forall_aux : seal (@uPred_forall_def). Proof. by eexists. Qed.
Definition uPred_forall := uPred_forall_aux.(unseal).
Global Arguments uPred_forall {SI M A}.
Local Definition uPred_forall_unseal :
  @uPred_forall = @uPred_forall_def := uPred_forall_aux.(seal_eq).

Local Program Definition uPred_exist_def {SI : sidx} {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_exist_aux : seal (@uPred_exist_def). Proof. by eexists. Qed.
Definition uPred_exist := uPred_exist_aux.(unseal).
Global Arguments uPred_exist {SI M A}.
Local Definition uPred_exist_unseal :
  @uPred_exist = @uPred_exist_def := uPred_exist_aux.(seal_eq).

Local Program Definition uPred_sep_def {SI : sidx} {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  intros SI M P Q n1 n2 x y (x1&x2&Hx&?&?) [z Hy] Hn.
  exists x1, (x2 ⋅ z); split_and?; eauto using uPred_mono, cmra_includedN_l.
  rewrite Hy. eapply dist_le, Hn. by rewrite Hx assoc.
Qed.
Local Definition uPred_sep_aux : seal (@uPred_sep_def). Proof. by eexists. Qed.
Definition uPred_sep := uPred_sep_aux.(unseal).
Global Arguments uPred_sep {SI M}.
Local Definition uPred_sep_unseal :
  @uPred_sep = @uPred_sep_def := uPred_sep_aux.(seal_eq).

Local Program Definition uPred_wand_def {SI : sidx} {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros SI M P Q n1 n1' x1 x1' HPQ ? Hn n3 x3 ???; simpl in *.
  eapply uPred_mono with n3 (x1 ⋅ x3); last reflexivity; first eapply HPQ; first by etrans.
  all: eauto using cmra_validN_includedN, cmra_monoN_r, cmra_includedN_le.
Qed.
Local Definition uPred_wand_aux : seal (@uPred_wand_def). Proof. by eexists. Qed.
Definition uPred_wand := uPred_wand_aux.(unseal).
Global Arguments uPred_wand {SI M}.
Local Definition uPred_wand_unseal :
  @uPred_wand = @uPred_wand_def := uPred_wand_aux.(seal_eq).

Local Program Definition uPred_persistently_def {SI : sidx} {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (core x) |}.
Solve Obligations with naive_solver eauto using uPred_mono, cmra_core_monoN.
Local Definition uPred_persistently_aux : seal (@uPred_persistently_def).
Proof. by eexists. Qed.
Definition uPred_persistently := uPred_persistently_aux.(unseal).
Global Arguments uPred_persistently {SI M}.
Local Definition uPred_persistently_unseal :
  @uPred_persistently = @uPred_persistently_def := uPred_persistently_aux.(seal_eq).

Local Program Definition uPred_later_def {SI : sidx} {M: ucmra} (P : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n', n' < n → P n' x |}.
Next Obligation.
  intros SI M P n1 n2 x1 x2 H1 H2 Hle n' Hlt; simpl in *.
  eapply uPred_mono; first eapply H1.
  - eauto using SIdx.lt_le_trans.
  - eauto using cmra_includedN_le with si_solver.
  - reflexivity.
Qed.
Local Definition uPred_later_aux : seal (@uPred_later_def). Proof. by eexists. Qed.
Definition uPred_later := uPred_later_aux.(unseal).
Global Arguments uPred_later {SI M}.
Local Definition uPred_later_unseal :
  @uPred_later = @uPred_later_def := uPred_later_aux.(seal_eq).

Local Program Definition uPred_ownM_def {SI : sidx} {M : ucmra} (a : M) : uPred M :=
  {| uPred_holds n x := a ≼{n} x |}.
Next Obligation.
  intros SI M a n1 n2 x1 x [a' Hx1] [x2 Hx] Hn.
  exists (a' ⋅ x2). rewrite Hx. eapply dist_le, Hn. rewrite (assoc op) -Hx1 //.
Qed.
Local Definition uPred_ownM_aux : seal (@uPred_ownM_def). Proof. by eexists. Qed.
Definition uPred_ownM := uPred_ownM_aux.(unseal).
Global Arguments uPred_ownM {SI M}.
Local Definition uPred_ownM_unseal :
  @uPred_ownM = @uPred_ownM_def := uPred_ownM_aux.(seal_eq).

Local Program Definition uPred_bupd_def {SI : sidx} {M} (Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ k yf,
      k ≤ n → ✓{k} (x ⋅ yf) → ∃ x', ✓{k} (x' ⋅ yf) ∧ Q k x' |}.
Next Obligation.
  intros SI M Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk.
  rewrite (dist_le _ _ _ _ Hx); last by etrans. intros Hxy.
  destruct (HQ k (x3 ⋅ yf)) as (x'&?&?); [by etrans|by rewrite assoc|].
  exists (x' ⋅ x3); split; first by rewrite -assoc.
  eauto using uPred_mono, cmra_includedN_l with si_solver.
Qed.
Local Definition uPred_bupd_aux : seal (@uPred_bupd_def). Proof. by eexists. Qed.
Definition uPred_bupd := uPred_bupd_aux.(unseal).
Global Arguments uPred_bupd {SI M}.
Local Definition uPred_bupd_unseal :
  @uPred_bupd = @uPred_bupd_def := uPred_bupd_aux.(seal_eq).

(** Primitive logical rules.
    These are not directly usable later because they do not refer to the BI
    connectives. *)
Module uPred_primitive.
Local Definition uPred_unseal :=
  (uPred_si_pure_unseal, uPred_si_emp_valid_unseal,
  uPred_and_unseal, uPred_or_unseal, uPred_impl_unseal,
  uPred_forall_unseal, uPred_exist_unseal,
  uPred_sep_unseal, uPred_wand_unseal,
  uPred_persistently_unseal, uPred_later_unseal, uPred_ownM_unseal,
  @uPred_bupd_unseal).
Ltac unseal :=
  rewrite !uPred_unseal /=.

Section primitive.
  Context {SI : sidx} {M : ucmra}.
  Implicit Types φ : Prop.
  Implicit Types P Q : uPred M.
  Implicit Types A : Type.
  Local Arguments uPred_holds {_ _} !_ _ _ /.
  Local Arguments siProp_holds _ !_ _ /.
  Local Hint Immediate uPred_in_entails : core.

  (** The notations below are implicitly local due to the section, so we do not
  mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (@uPred_entails SI M P%I Q%I) : stdpp_scope.
  Notation "(⊢)" := (@uPred_entails SI M) (only parsing) : stdpp_scope.
  Notation "P ⊣⊢ Q" := (@uPred_equiv SI M P%I Q%I) : stdpp_scope.
  Notation "(⊣⊢)" := (@uPred_equiv SI M) (only parsing) : stdpp_scope.

  Notation "<si_pure> Pi" := (uPred_si_pure Pi) : bi_scope.
  Notation "<si_emp_valid> P" := (uPred_si_emp_valid P).
  Notation "'⌜' φ '⌝'" := (<si_pure> siProp_pure φ%type%stdpp)%I : bi_scope.
  Notation "'True'" := ⌜ True ⌝%I : bi_scope.
  Notation "'False'" := ⌜ False ⌝%I : bi_scope.
  Infix "∧" := uPred_and : bi_scope.
  Infix "∨" := uPred_or : bi_scope.
  Infix "→" := uPred_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (uPred_forall (λ x, .. (uPred_forall (λ y, P)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (uPred_exist (λ x, .. (uPred_exist (λ y, P)) ..)) : bi_scope.
  Infix "∗" := uPred_sep : bi_scope.
  Infix "-∗" := uPred_wand : bi_scope.
  Notation "□ P" := (uPred_persistently P) : bi_scope.
  Notation "▷ P" := (uPred_later P) : bi_scope.
  Notation "|==> P" := (uPred_bupd P) : bi_scope.

  (** Entailment *)
  Lemma entails_po : PreOrder (⊢).
  Proof.
    split.
    - by intros P; split=> x i.
    - by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
  Qed.
  Lemma entails_anti_sym : AntiSymm (⊣⊢) (⊢).
  Proof. intros P Q HPQ HQP; split=> x n; by split; [apply HPQ|apply HQP]. Qed.
  Lemma equiv_entails P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof.
    split.
    - intros HPQ; split; split=> x i; apply HPQ.
    - intros [??]. exact: entails_anti_sym.
  Qed.
  Lemma entails_lim (cP cQ : chain (uPredO M)) :
    (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
  Proof.
    intros Hlim; split=> n m ? HP.
    eapply uPred_holds_ne, Hlim, HP; rewrite ?conv_compl; eauto using chain_cauchy with si_solver.
  Qed.

  Lemma entails_blim α (cP cQ: bchain (uPredO M) α) Hα:
    (∀ β Hβ, cP β Hβ ⊢ cQ β Hβ) → lbcompl Hα cP ⊢ lbcompl Hα cQ.
  Proof.
    intros Hlim; split=> β m Hv HP δ Hδ Hδβ Hv'.
    eapply Hlim, HP; eauto.
  Qed.

  (** Non-expansiveness and setoid morphisms *)
  Lemma si_pure_ne : NonExpansive (@uPred_si_pure SI M).
  Proof. intros n Pi Pi' HPi. unseal; split; intros. by apply HPi. Qed.

  Lemma si_emp_valid_ne : NonExpansive (@uPred_si_emp_valid SI M).
  Proof.
    intros n P P' HP. unseal; split=> n'.
    intros. apply HP; auto using ucmra_unit_validN.
  Qed.

  Lemma and_ne : NonExpansive2 (@uPred_and SI M).
  Proof.
    intros n P P' HP Q Q' HQ; unseal; split=> x n' ??.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  Qed.

  Lemma or_ne : NonExpansive2 (@uPred_or SI M).
  Proof.
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  Qed.

  Lemma impl_ne :
    NonExpansive2 (@uPred_impl SI M).
  Proof.
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    unseal; split; intros HPQ x' n'' ????; apply HQ, HPQ, HP;
      match goal with |- _ ≤ _ => first [reflexivity| by etrans]  | _ => by auto end.
  Qed.

  Lemma sep_ne : NonExpansive2 (@uPred_sep SI M).
  Proof.
    intros n P P' HP Q Q' HQ; split=> n' x ??.
    unseal; split; intros (x1&x2&?&?&?); ofe_subst x;
      exists x1, x2; split_and!; try (apply HP || apply HQ);
      eauto using cmra_validN_op_l, cmra_validN_op_r.
  Qed.

  Lemma wand_ne :
    NonExpansive2 (@uPred_wand SI M).
  Proof.
    intros n P P' HP Q Q' HQ; split=> n' x ??; unseal; split; intros HPQ x' n'' ???;
      apply HQ, HPQ, HP;
      match goal with |- _ ≤ _ => try reflexivity; by etrans  | _ => by eauto using cmra_validN_op_r end.
  Qed.

  Lemma forall_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_forall SI M A).
  Proof.
    by intros Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
  Qed.

  Lemma exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_exist SI M A).
  Proof.
    intros Ψ1 Ψ2 HΨ.
    unseal; split=> n' x ??; split; intros [a ?]; exists a; by apply HΨ.
  Qed.

  Lemma later_contractive : Contractive (@uPred_later SI M).
  Proof.
    unseal; intros n P Q HPQ; split=> -n' x H ? //=; split=> Hl m Hm; eapply HPQ.
    all: eauto using SIdx.lt_le_trans, cmra_validN_le with si_solver.
  Qed.

  Lemma later_ne : NonExpansive (@uPred_later SI M).
  Proof. apply contractive_ne, later_contractive. Qed.

  Lemma persistently_ne : NonExpansive (@uPred_persistently SI M).
  Proof.
    intros n P1 P2 HP.
    unseal; split=> n' x; split; apply HP; eauto using cmra_core_validN.
  Qed.

  Lemma ownM_ne : NonExpansive (@uPred_ownM SI M).
  Proof.
    intros n a b Ha.
    unseal; split=> n' x ? /=. by rewrite (dist_le _ _ _ _ Ha).
  Qed.

  Lemma bupd_ne : NonExpansive (@uPred_bupd SI M).
  Proof.
    intros n P Q HPQ.
    unseal; split=> n' x; split; intros HP k yf ??;
      destruct (HP k yf) as (x'&?&?); match goal with |- ∃ _ , _ => idtac | _ => by auto end.
    all: exists x'; split; auto; apply HPQ; eauto using cmra_validN_op_l.
           all: by etrans.
  Qed.

  (** Rules for the [siProp] embedding *)
  Lemma si_pure_mono Pi Qi : siProp_entails Pi Qi → <si_pure> Pi ⊢ <si_pure> Qi.
  Proof. intros HPQi. unseal; split=> n ??. apply HPQi. Qed.
  Lemma si_emp_valid_mono P Q :
    (P ⊢ Q) → siProp_entails (<si_emp_valid> P) (<si_emp_valid> Q).
  Proof. intros HPQ. unseal; split=> n. apply HPQ, ucmra_unit_validN. Qed.

  Lemma si_pure_impl_2 Pi Qi :
    (<si_pure> Pi → <si_pure> Qi) ⊢ <si_pure> siProp_impl Pi Qi.
  Proof.
    unseal; siProp_primitive.unseal. split; simpl; eauto using cmra_validN_le.
  Qed.
  Lemma si_pure_forall_2 {A} (Φi : A → siProp) :
   (∀ x, <si_pure> Φi x) ⊢ <si_pure> siProp_forall Φi.
  Proof. by unseal; siProp_primitive.unseal. Qed.
  Lemma si_pure_later Pi : <si_pure> siProp_later Pi ⊣⊢ ▷ <si_pure> Pi.
  Proof. by unseal; siProp_primitive.unseal. Qed.

  Lemma si_emp_valid_later_1 P :
    siProp_entails (<si_emp_valid> ▷ P) (siProp_later (<si_emp_valid> P)).
  Proof. by unseal; siProp_primitive.unseal. Qed.
  Lemma si_emp_valid_exist_1 {A} (Φ : A → uPred M) :
    siProp_entails (<si_emp_valid> ∃ x, Φ x)
                   (siProp_exist (λ x, <si_emp_valid> Φ x)).
  Proof. by unseal; siProp_primitive.unseal. Qed.

  Lemma si_emp_valid_si_pure Pi :
    <si_emp_valid> (<si_pure> Pi : uPred M)%I ≡ Pi.
  Proof. by unseal. Qed.
  Lemma si_pure_si_emp_valid P :
    <si_pure> <si_emp_valid> P ⊢ □ P.
  Proof.
    unseal. split=> /= n x _ ?.
    eapply uPred_mono with n ε; eauto using ucmra_unit_leastN.
  Qed.

  (* The following law is very similar to [persistently_impl_plainly] of the
  (old) parametric-index fork; it holds for any modality defined as
  `M P n x := ∀ y, R x y → P n y`. *)
  Lemma persistently_impl_si_pure Pi Q :
    (<si_pure> Pi → □ Q) ⊢ □ (<si_pure> Pi → Q).
  Proof.
    unseal; split=> /= n x ? HPQ n' x' ????.
    eapply uPred_mono with n' (core x)=>//; [|by apply cmra_included_includedN].
    apply (HPQ n' x); eauto using cmra_validN_le.
  Qed.

  Lemma prop_ext_2 P Q :
    siProp_entails (<si_emp_valid> ((P -∗ Q) ∧ (Q -∗ P)))
                   (siProp_internal_eq P Q).
  Proof.
    unseal; siProp_primitive.unseal. split=> n /=.
    setoid_rewrite (left_id ε op). split; naive_solver.
  Qed.

  (** Introduction and elimination rules *)
  Lemma and_elim_l P Q : P ∧ Q ⊢ P.
  Proof. by unseal; split=> n x ? [??]. Qed.
  Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
  Proof. by unseal; split=> n x ? [??]. Qed.
  Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
  Proof. intros HQ HR; unseal; split=> n x ??; by split; [apply HQ|apply HR]. Qed.

  Lemma or_intro_l P Q : P ⊢ P ∨ Q.
  Proof. unseal; split=> n x ??; left; auto. Qed.
  Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
  Proof. unseal; split=> n x ??; right; auto. Qed.
  Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
  Proof.
    intros HP HQ; unseal; split=> n x ? [?|?].
    - by apply HP.
    - by apply HQ.
  Qed.

  Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
  Proof.
    unseal; intros HQ; split=> n x ?? n' x' ????. apply HQ;
      naive_solver eauto using uPred_mono, cmra_included_includedN.
  Qed.
  Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
  Proof. unseal; intros HP ; split=> n x ? [??]; apply HP with n x; auto with si_solver. Qed.

  Lemma forall_intro {A} P (Ψ : A → uPred M): (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
  Proof. unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ. Qed.
  Lemma forall_elim {A} {Ψ : A → uPred M} a : (∀ a, Ψ a) ⊢ Ψ a.
  Proof. unseal; split=> n x ? HP; apply HP. Qed.

  Lemma exist_intro {A} {Ψ : A → uPred M} a : Ψ a ⊢ ∃ a, Ψ a.
  Proof. unseal; split=> n x ??; by exists a. Qed.
  Lemma exist_elim {A} (Φ : A → uPred M) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
  Proof. unseal; intros HΦΨ; split=> n x ? [a ?]; by apply HΦΨ with a. Qed.

  (** BI connectives *)
  Lemma sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
  Proof.
    intros HQ HQ'; unseal.
    split; intros n' x ? (x1&x2&?&?&?); exists x1,x2; ofe_subst x;
      eauto 7 using cmra_validN_op_l, cmra_validN_op_r, uPred_in_entails.
  Qed.
  Lemma True_sep_1 P : P ⊢ True ∗ P.
  Proof.
    unseal; siProp_primitive.unseal; split; intros n x ??.
    exists (core x), x. by rewrite cmra_core_l.
  Qed.
  Lemma True_sep_2 P : True ∗ P ⊢ P.
  Proof.
    unseal; split; intros n x ? (x1&x2&?&_&?); ofe_subst;
      eauto using uPred_mono, cmra_includedN_r with si_solver.
  Qed.
  Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
  Proof.
    unseal; split; intros n x ? (x1&x2&?&?&?); exists x2, x1; by rewrite (comm op).
  Qed.
  Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof.
    unseal; split; intros n x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
    exists y1, (y2 ⋅ x2); split_and?; auto.
    + by rewrite (assoc op) -Hy -Hx.
    + by exists y2, x2.
  Qed.
  Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
  Proof.
    unseal=> HPQR; split=> n x ?? n' x' ???; apply HPQR; auto.
    exists x, x'; split_and?; auto.
    eapply uPred_mono with n x; eauto using cmra_validN_op_l.
  Qed.
  Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
  Proof.
    unseal =>HPQR. split; intros n x ? (?&?&?&?&?). ofe_subst.
    eapply HPQR; eauto using cmra_validN_op_l with si_solver.
  Qed.

  (** Persistently *)
  Lemma persistently_mono P Q : (P ⊢ Q) → □ P ⊢ □ Q.
  Proof. intros HP; unseal; split=> n x ? /=. by apply HP, cmra_core_validN. Qed.
  Lemma persistently_elim P : □ P ⊢ P.
  Proof.
    unseal; split=> n x ? /=.
    eauto using uPred_mono, cmra_included_core, cmra_included_includedN with si_solver.
  Qed.
  Lemma persistently_idemp_2 P : □ P ⊢ □ □ P.
  Proof. unseal; split=> n x ?? /=. by rewrite cmra_core_idemp. Qed.

  Lemma persistently_forall_2 {A} (Ψ : A → uPred M) : (∀ a, □ Ψ a) ⊢ (□ ∀ a, Ψ a).
  Proof. by unseal. Qed.
  Lemma persistently_exist_1 {A} (Ψ : A → uPred M) : (□ ∃ a, Ψ a) ⊢ (∃ a, □ Ψ a).
  Proof. by unseal. Qed.

  Lemma persistently_and_sep_l_1 P Q : □ P ∧ Q ⊢ P ∗ Q.
  Proof.
    unseal; split=> n x ? [??]; exists (core x), x; simpl in *.
    by rewrite cmra_core_l.
  Qed.

  (** Later *)
  Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
  Proof.
    unseal=> HP; split=> -n x ?? n' ?. apply HP; eauto using cmra_validN_le with si_solver.
  Qed.
  Lemma later_intro P : P ⊢ ▷ P.
  Proof.
    unseal; split=> n /= x ? HP n' Hn'.
    apply uPred_mono with n x; eauto using cmra_validN_le with si_solver.
  Qed.
  Lemma later_forall_2 {A} (Φ : A → uPred M) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
  Proof. unseal; split=> n x Hv H n' Hn' a. by eapply H. Qed.

  (** The law [later_false_exist] (field [bi_mixin_later_false_impl_exist] of
  upstream's [BiLaterMixin]) holds for any step-index type. Proof following
  upstream Iris's port of [uPred] to Transfinite step-indexing. *)
  Lemma later_false_exist {A} (Φ : A → uPred M) :
    (▷ False → ∃ a, Φ a) ⊢ ∃ a, ▷ False → Φ a.
  Proof.
    unseal; siProp_primitive.unseal; split=> -n x Hx HΦ /=.
    destruct (HΦ 0ᵢ x) as [a HΦa]; [by eauto using cmra_validN_le, SIdx.le_0_l..| |].
    { intros n' []%SIdx.nlt_0_r. }
    exists a. intros n' x' ??? Hn'.
    destruct (decide (n' = 0ᵢ)) as [->|[]%SIdx.neq_0_lt_0%Hn'].
    eapply uPred_mono; [by apply HΦa|..]; eauto using cmra_included_includedN.
  Qed.

  (* the finite rules *)
  Lemma later_exist_false `{FI: !SIdxFinite SI} {A} (Φ : A → uPred M) :
    (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
  Proof.
    unseal; split=> -n x Hv /= H; eauto.
    destruct (finite_index n) as [->|[m ->]].
    - left; siProp_primitive.unseal; eapply SIdx.nlt_0_r.
    - right. edestruct H as [y]; eauto with si_solver. exists y.
      intros; eauto using uPred_mono with si_solver.
  Qed.

  (** The law [later_false_sep] (field [bi_mixin_later_false_impl_sep] of
  upstream's [BiLaterMixin]) holds for any step-index type. Proof following
  upstream Iris's port of [uPred] to Transfinite step-indexing. *)
  Lemma later_false_sep P Q :
    (▷ False → P ∗ Q) ⊢ (▷ False → P) ∗ (▷ False → Q).
  Proof.
    unseal; siProp_primitive.unseal; split=> -n x Hx HΦ /=.
    destruct (HΦ 0ᵢ x) as (x1 & x2 & ? & HP & HQ);
      [by eauto using cmra_validN_le, SIdx.le_0_l..| |].
    { intros n' []%SIdx.nlt_0_r. }
    destruct (cmra_extend 0ᵢ x x1 x2) as (y1&y2&Hx'&Hy1&Hy2); [|done|].
    { by eapply cmra_validN_le, SIdx.le_0_l. }
    exists y1, y2.
    split_and!; [by eapply equiv_dist|intros n' x' ??? Hn'..].
    - destruct (decide (n' = 0ᵢ)) as [->|[]%SIdx.neq_0_lt_0%Hn'].
      eapply uPred_mono; [by apply HP| |done].
      rewrite -Hy1. by apply cmra_included_includedN.
    - destruct (decide (n' = 0ᵢ)) as [->|[]%SIdx.neq_0_lt_0%Hn'].
      eapply uPred_mono; [by apply HQ| |done].
      rewrite -Hy2. by apply cmra_included_includedN.
  Qed.

  Lemma later_sep_1 `{FI: !SIdxFinite SI} P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q.
  Proof.
    unseal; split=> n x ? //= H.
    destruct (finite_index n) as [->|[m ->]]; eauto.
    { exists x, (core x); rewrite cmra_core_r; (repeat split; eauto); intros ? [] % SIdx.nlt_0_r. }
    destruct (H m) as (x1&x2&Hx&?&?); first auto with si_solver. destruct (cmra_extend m x x1 x2) as (y1&y2&Hx'&Hy1&Hy2); eauto using cmra_validN_le with si_solver; simpl in *.
    exists y1, y2; split; [by rewrite Hx'|]; split=> n' Hn'; eapply uPred_mono; eauto with si_solver.
    - eapply cmra_includedN_le; first by rewrite Hy1. by apply index_succ_iff.
    - eapply cmra_includedN_le; first by rewrite Hy2. by apply index_succ_iff.
  Qed.

  Lemma later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q).
  Proof.
    unseal; split=> n x ? //=. intros (x1&x2&Hx&Hx1&Hx2) n' Hn'.
    exists x1, x2; repeat split; eauto using dist_le with si_solver.
  Qed.

  Lemma later_sep_pure φ P: ▷ (⌜φ⌝ ∗ P) ⊢ ▷ ⌜φ⌝ ∗ ▷ P.
  Proof.
    unseal; split=> n x ? //=. intros Hlt.
    exists ε, x. rewrite left_id. split; first done.
    split; intros n' Hn; destruct (Hlt _ Hn) as (x1 & x2 & Heq & Hφ & HP).
    - done.
    - eapply uPred_mono; eauto with si_solver.
      rewrite Heq. eapply cmra_includedN_r.
  Qed.

  Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
  Proof.
    unseal; siProp_primitive.unseal; split=> -n x ? /= HP.
    destruct (index_lt_dec_minimum n) as [|[n']]; eauto.
    right. intros m x' ? ? ? Hmin. eapply uPred_mono.
    - eapply HP; eauto.
    - eauto using cmra_included_includedN.
    - (* [m] is the least index, i.e. [0ᵢ]: say which index, instead of
         [erewrite index_zero_is_unique at 1] *)
      rewrite (index_zero_is_unique m Hmin). apply SIdx.le_0_l.
  Qed.

  Lemma later_persistently_1 P : ▷ □ P ⊢ □ ▷ P.
  Proof. by unseal. Qed.
  Lemma later_persistently_2 P : □ ▷ P ⊢ ▷ □ P.
  Proof. by unseal. Qed.

  (** Basic update modality *)
  Lemma bupd_intro P : P ⊢ |==> P.
  Proof.
    unseal. split=> n x ? HP k yf ?; exists x; split; first done.
    apply uPred_mono with n x; eauto using cmra_validN_op_l.
  Qed.
  Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ⊢ |==> Q.
  Proof.
    unseal. intros HPQ; split=> n x ? HP k yf ??.
    destruct (HP k yf) as (x'&?&?); eauto.
    exists x'; split; eauto using uPred_in_entails, cmra_validN_op_l.
  Qed.
  Lemma bupd_trans P : (|==> |==> P) ⊢ |==> P.
  Proof. unseal; split; naive_solver. Qed.
  Lemma bupd_frame_r P R : (|==> P) ∗ R ⊢ |==> P ∗ R.
  Proof.
    unseal; split; intros n x ? (x1&x2&Hx&HP&?) k yf ??.
    destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto.
    { by rewrite assoc -(dist_le _ _ _ _ Hx); last auto. }
    exists (x' ⋅ x2); split; first by rewrite -assoc.
    exists x', x2. eauto using uPred_mono, cmra_validN_op_l, cmra_validN_op_r.
  Qed.
  (* This replaces [bupd_plainly] of the (old) parametric-index fork. *)
  Lemma bupd_si_pure Pi : (|==> <si_pure> Pi) ⊢ <si_pure> Pi.
  Proof.
    unseal; split => n x Hnx /= Hng.
    destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
  Qed.

  (** Own *)
  Lemma ownM_op (a1 a2 : M) :
    uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
  Proof.
    unseal; split=> n x ?; split.
    - intros [z ?]; exists a1, (a2 ⋅ z); split; [by rewrite (assoc op)|].
      split.
      + by exists (core a1); rewrite cmra_core_r.
      + by exists z.
    - intros (y1&y2&Hx&[z1 Hy1]&[z2 Hy2]); exists (z1 ⋅ z2).
      by rewrite (assoc op _ z1) -(comm op z1) (assoc op z1)
        -(assoc op _ a2) (comm op z1) -Hy1 -Hy2.
  Qed.
  Lemma persistently_ownM_core (a : M) : uPred_ownM a ⊢ □ uPred_ownM (core a).
  Proof.
    split=> n x /=; unseal; intros Hx. simpl. by apply cmra_core_monoN.
  Qed.
  Lemma ownM_unit P : P ⊢ (uPred_ownM ε).
  Proof. unseal; split=> n x ??; by  exists x; rewrite left_id. Qed.

  (** The step-index-0 counterpart of [later_ownM], which holds for any
  step-index type. Proof following upstream Iris's port of [uPred] to
  Transfinite step-indexing. *)
  Lemma later_false_ownM a :
    (▷ False → uPred_ownM a) ⊢ ∃ b,
     uPred_ownM b ∧ (▷ False → <si_pure> siProp_internal_eq a b).
  Proof.
    unseal; siProp_primitive.unseal. split=> n x /= ? Hax.
    destruct (Hax 0ᵢ x) as [y Hx]; [by eauto using cmra_validN_le, SIdx.le_0_l..| |].
    { intros n' []%SIdx.nlt_0_r. }
    destruct (cmra_extend 0ᵢ x a y) as (a'&y'&Hx'&Ha&Hy); [|done|].
    { by eapply cmra_validN_le, SIdx.le_0_l. }
    exists a'. split; [rewrite Hx'; by apply cmra_includedN_l|].
    intros n' x' ??? Hn'.
    destruct (decide (n' = 0ᵢ)) as [->|[]%SIdx.neq_0_lt_0%Hn']; done.
  Qed.

  Lemma later_ownM `{FI: !SIdxFinite SI} a :
    ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ <si_pure> siProp_internal_eq a b.
  Proof.
    unseal; siProp_primitive.unseal; split=> -n x /= ? Hax.
    destruct (finite_index n) as [->|[m ->]].
    { exists x. split; eauto. intros ? [] % SIdx.nlt_0_r. }
    edestruct Hax as [y ?]; eauto with si_solver.
    destruct (cmra_extend m x a y) as (a'&y'&Hx&H2&?); eauto using cmra_validN_le with si_solver.
    exists a'. rewrite Hx. split; eauto using cmra_includedN_l.
    intros; eapply dist_le.
    - symmetry; eapply H2.
    - eauto with si_solver.
  Qed.

  Lemma bupd_ownM_updateP x (Φ : M → Prop) :
    x ~~>: Φ → uPred_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ uPred_ownM y.
  Proof.
    unseal; siProp_primitive.unseal=> Hup; split=> n x2 ? [x3 Hx] k yf ??.
    destruct (Hup k (Some (x3 ⋅ yf))) as (y&?&?); simpl in *.
    { rewrite /= assoc -(dist_le _ _ _ _ Hx); auto. }
    exists (y ⋅ x3); split; first by rewrite -assoc.
    exists y; eauto using cmra_includedN_l.
  Qed.

  (** This law is part of upstream Iris's [uPred] interface (used, e.g., by
  [own_forall]); its model proof is the one of upstream Iris. *)
  Lemma ownM_forall {A} (f : A → M) :
    (∀ a, uPred_ownM (f a)) ⊢ ∃ z, uPred_ownM z ∧
      (∀ a, ∃ xf, <si_pure> siProp_internal_eq z (f a ⋅ xf)).
  Proof.
    unseal; siProp_primitive.unseal.
    split=> n y /= Hval Hf. exists y. split; [done|]. intros a.
    destruct (Hf a) as [xf ?]; eauto.
  Qed.

  (** Valid *)
  Lemma ownM_valid (a : M) : uPred_ownM a ⊢ <si_pure> siProp_cmra_valid a.
  Proof.
    unseal; siProp_primitive.unseal. split=> n x Hv [a' ?].
    ofe_subst. eauto using cmra_validN_op_l.
  Qed.

  (* satisfiabiity for uPred *)
  Definition uPred_sat (P: uPred M) :=
    ∀ n: SI, ∃ x: M, ✓{n} x ∧ P n x.

  Lemma uPred_sat_intro: uPred_sat True.
  Proof.
    rewrite /uPred_sat; unseal; siProp_primitive.unseal=> n //=. exists ε.
    simpl in *; split; eauto using ucmra_unit_validN.
  Qed.

  Lemma uPred_sat_mono P Q: (P ⊢ Q) → uPred_sat P → uPred_sat Q.
  Proof.
    unfold uPred_sat. intros [PQ] HP n.
    destruct (HP n) as (x & Hv & HP'). exists x. split; eauto.
  Qed.

  Lemma uPred_sat_elim φ: uPred_sat (⌜φ⌝)%I → φ.
  Proof.
    unfold uPred_sat; unseal; siProp_primitive.unseal=> Hφ.
    destruct (Hφ 0ᵢ) as [x [_ Hφ']]; apply Hφ'.
  Qed.

  Lemma uPred_sat_later P: uPred_sat (▷ P) → uPred_sat P.
  Proof.
    intros H n. destruct (H (Sᵢ n)) as (x & Hv & HP).
    exists x. split.
    - eapply cmra_validN_le; eauto with si_solver.
    - revert HP. unseal. intros HP. apply HP. eauto with si_solver.
  Qed.

  Lemma uPred_sat_bupd P: uPred_sat (|==> P) → uPred_sat P.
  Proof.
    unfold uPred_sat. unseal. intros H.
    intros n. destruct (H n) as (y & Hv & Hupd).
    destruct (Hupd n ε) as (z & Hv' & HP); eauto with si_solver; first by rewrite right_id.
    exists z; split; eauto. revert Hv'. by rewrite right_id.
  Qed.

  Lemma uPred_sat_exists A `{!TypeExistentialProperty A SI} (P: A → uPred M): uPred_sat (∃ a, P a) → ∃ a, uPred_sat (P a).
  Proof.
    unfold uPred_sat.
    specialize (can_commute_exists (λ a n, ∃ x: M, ✓{n} x ∧ P a n x)) as Hcomm.
    intros Hexist. edestruct Hcomm as (a & HP).
    - intros a m n Hmn (x & Hv & HP). exists x. split.
      + eapply cmra_validN_le; eauto with si_solver.
      + eapply uPred_mono; eauto  with si_solver.
    - intros n. destruct (Hexist n) as (x & Hv & HP); eauto.
      revert HP. unseal. intros [? ?]; eauto.
    - exists a. intros n. apply HP.
  Qed.

  (* the later or rule (it holds for any step-index type, using that every
  step-index type classically has the finite bounded existential property) *)
  Lemma later_or_2 `{FBE: !FiniteBoundedExistential SI} (P Q: uPred M):
    ▷ (P ∨ Q) ⊢ ▷ P ∨ ▷ Q.
  Proof.
    unseal; split=> -n x Hv /= H; eauto.
    edestruct (can_commute_fin_bounded_exists (λ b n, if b then P n x else Q n x) n) as [b Hb].
    - intros [] a b Hlt Hpred; eapply uPred_mono; eauto with si_solver.
    - intros n' Hlt; destruct (H n' Hlt) as [|]; by [exists true|exists false].
    - destruct b; eauto.
  Qed.

  (* persistency is bounded limit preserving *)
  Lemma bounded_limit_preserving_persistency:
    BoundedLimitPreserving (λ P, P ⊢ □ P).
  Proof.
    intros n Hn ch. unseal. intros Hbound; split=>m x Hv HP. rewrite /uPred_persistently_def /=.
    eapply lbcompl_unfold; auto. intros k Hk Hle Hv'.
    destruct (Hbound k Hk) as [Hm]. eapply Hm; first by eapply cmra_validN_le.
    rewrite lbcompl_unfold in HP. eapply HP; eauto using cmra_validN_le.
  Qed.

End primitive.
End uPred_primitive.
