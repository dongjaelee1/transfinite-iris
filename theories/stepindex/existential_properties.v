From iris.algebra Require Export stepindex.
Require Import Stdlib.Logic.Classical_Prop.


Polymorphic Class TypeExistentialProperty@{i} (X: Type@{i}) (SI: indexT) : Type :=
  can_commute_exists (P : X → index → Prop) :
  (∀ x a b, a ≺ᵢ b → P x b → P x a)
  → (∀ a, ∃ x, P x a)
  → ∃ x, ∀ a, P x a.

Polymorphic Class ExistentialProperty@{i} (SI: indexT) : Type :=
  #[global] existential_properties (X : Type@{i}) :: TypeExistentialProperty X SI.


Notation FiniteExistential := (TypeExistentialProperty bool).
Notation CountableExistential := (TypeExistentialProperty nat).

Class FiniteBoundedExistential (SI: indexT) :=
    can_commute_fin_bounded_exists (P: bool → index → Prop) c:
    (∀ x a b, a ≺ᵢ b → P x b → P x a) →
    (∀ a, a ≺ᵢ c → ∃ x, P x a) → (∃ x, ∀ a, a ≺ᵢ c → P x a).


(* existential property preserved over surjections *)
Lemma type_surj_existential@{i j} (X: Type@{i}) (Y: Type@{j}) (SI: indexT) (f: X → Y):
  TypeExistentialProperty X SI →
  Surj eq f →
  TypeExistentialProperty Y SI.
Proof.
  intros Hex Hsur P Hdown Hwit.
  edestruct (Hex (λ x, P (f x))) as [x Hx]; last by eauto.
  - eauto.
  - intros a. destruct (Hwit a) as [y Py].
    destruct (surj f y) as [x <-]. eauto.
Qed.

(* classically any step-index type has the finite existential property *)
Lemma classic_finite_existential (SI: indexT):
  (∀ P: Prop, P ∨ ¬ P) → FiniteExistential SI.
Proof.
  intros xm P Hdown Hsome. destruct (xm (∃ a, ¬ P true a)) as [[a HP]|HP]; last first.
  - exists true. intros a. destruct (xm (P true a)); auto. exfalso. apply HP. by exists a.
  - assert (P false a) by (destruct (Hsome a) as [[] ?]; naive_solver).
    exists false. intros b. destruct (index_lt_eq_lt_dec a b) as [[|<-]|]; eauto.
    destruct (Hsome b) as [[] ?]; auto. exfalso. apply HP; eauto.
Qed.

Lemma classic_finite_bounded_existential {SI: indexT}:
  (∀ P: Prop, P ∨ ¬ P) → FiniteBoundedExistential SI.
Proof.
  intros xm P c Hdown Hsome. destruct (xm (∃ a, ¬ P true a ∧ a ≺ᵢ c)) as [[a [HP Ha]]|HP]; last first.
  - exists true. intros a Ha. destruct (xm (P true a)); auto. exfalso. apply HP. by exists a.
  - assert (P false a) by (destruct (Hsome a) as [[] ?]; naive_solver).
    exists false. intros b Hb. destruct (index_lt_eq_lt_dec a b) as [[|<-]|]; eauto.
    destruct (Hsome b) as [[] ?]; auto. exfalso. apply HP; eauto.
Qed.

Global Instance finite_bounded_existential SI: FiniteBoundedExistential SI.
Proof.
  eapply classic_finite_bounded_existential, classic.
Qed.
