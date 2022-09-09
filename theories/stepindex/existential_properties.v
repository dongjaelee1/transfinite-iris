From iris.stepindex Require Export stepindex.


Polymorphic Class TypeExistentialProperty@{i} (X: Type@{i}) (SI: indexT) : Type :=
  can_commute_exists (P : X → SI → Prop) :
  (∀ x a b, a ≺ b → P x b → P x a)
  → (∀ a, ∃ x, P x a)
  → ∃ x, ∀ a, P x a.

Polymorphic Class ExistentialProperty@{i} (SI: indexT) : Type :=
  existential_properties (X : Type@{i}) :> TypeExistentialProperty X SI.


Notation FiniteExistential := (TypeExistentialProperty bool).
Notation CountableExistential := (TypeExistentialProperty nat).

Class FiniteBoundedExistential (SI: indexT) :=
    can_commute_fin_bounded_exists (P: bool → SI → Prop) c:
    (∀ x a b, a ≺ b → P x b → P x a) →
    (∀ a, a ≺ c → ∃ x, P x a) → (∃ x, ∀ a, a ≺ c → P x a).


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
  intros xm P c Hdown Hsome. destruct (xm (∃ a, ¬ P true a ∧ a ≺ c)) as [[a [HP Ha]]|HP]; last first.
  - exists true. intros a Ha. destruct (xm (P true a)); auto. exfalso. apply HP. by exists a.
  - assert (P false a) by (destruct (Hsome a) as [[] ?]; naive_solver).
    exists false. intros b Hb. destruct (index_lt_eq_lt_dec a b) as [[|<-]|]; eauto.
    destruct (Hsome b) as [[] ?]; auto. exfalso. apply HP; eauto.
Qed.

Global Instance fininte_bounded_existential_nat: FiniteBoundedExistential natI.
Proof.
  intros P [|n] Hdown Hex.
  - exists true. simpl. intros ?; lia.
  - destruct (Hex n) as [x HP]; first done.
    exists x. simpl; intros m Hm.
    assert (m = n ∨ m < n) as [->|] by lia; eauto.
Qed.












