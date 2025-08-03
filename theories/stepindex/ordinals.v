(**
  This formalization is a modification of:
  "Large Model Constructions for Second-Order ZF in Dependent Type Theory"
    by Dominik Kirst and Gert Smolka, CPP 2018

    See https://www.ps.uni-saarland.de/Publications/details/KirstSmolka:2017:Large-Model.html.

  replacing the definition of ordinals with the inductive characterization from:
  - "Lecture Notes in Computational Logic II" by Gert Smolka, 2016, https://courses.ps.uni- saarland.de/cl2_16/.
  - "Set theory and the continuum problem" by Smullyan, R. M. and Fitting, M, Dover Publications 2010
*)

From iris.prelude Require Import options.
From iris.algebra Require Import stepindex.
From transfinite.prelude Require Import prelude.
From transfinite.stepindex Require Import existential_properties utils.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.Classical_Prop.
Require Import Stdlib.Logic.Epsilon.


(* Universe polymorphism settings *)
Unset Universe Minimization ToSet.

(** Aczel's Intensional Model Construction + Extensionalisation using a choice operator*)
(**  Well-Founded Trees *)
Section aczel_trees.
  Set Universe Polymorphism. (* all definitions in this section will be universe polymorphic *)
  Polymorphic Inductive Acz@{i} : Type :=
  | Asup : ∀ A : Type@{i}, (A → Acz) → Acz.

Definition atypeof '(Asup A f) := A.
Definition aelements s : (atypeof s) → Acz := match s with Asup A f => f end.

Fixpoint aeq@{i} (s t: Acz@{i}) :=
  match s, t with
  | Asup A f, Asup B g =>
  (∀ a, ∃ b, aeq (f a) (g b)) ∧ (∀ b, ∃ a, aeq (f a) (g b))
  end.

Definition ain s '(Asup A f) := ∃ a, aeq s (f a).
Definition asubs s t := ∀ u, ain u s → ain u t.

Definition aempty : Acz := Asup False (λ f, match f with end).


(* properties about the Aczel trees *)
Lemma aeq_refl s : aeq s s.
Proof.
  induction s as [A f IH]; simpl; split; eauto 10.
Qed.

Lemma aeq_sym s t : aeq s t → aeq t s.
Proof.
  revert t; induction s as [A f IH].
  intros [B g]; simpl; intros [H1 H2]; split.
  - intros b. destruct (H2 b) as [a H3]. exists a. by apply IH.
  - intros a. destruct (H1 a) as [b H3]. exists b. by apply IH.
Qed.

Lemma aeq_trans s t u :
  aeq s t → aeq t u → aeq s u.
Proof.
  revert t u. induction s as [A f IH].
  intros [B g] [C h]. simpl. intros [H1 H2] [H3 H4]. split.
  - intros a. destruct (H1 a) as [b H5]. destruct (H3 b) as [c H6].
    exists c. by apply IH with (t := (g b)).
  - intros c. destruct (H4 c) as [b H5]. destruct (H2 b) as [a H6].
    exists a. by apply IH with (t := (g b)).
Qed.

Hint Resolve aeq_refl aeq_sym aeq_trans : core.

Global Instance aeq_equiv : Equivalence aeq.
Proof.
  constructor; eauto.
Qed.

Lemma ain_Asup A f a : ain (f a) (Asup A f).
Proof.
  simpl. exists a. by apply aeq_refl.
Qed.

Lemma Ain_Alements s t : ain s t → ∃ a : (atypeof t), aeq s (aelements t a).
Proof.
  destruct t as [A f]. intros [a H]. by exists a.
Qed.

Lemma aelements_ain (s : Acz) (a : atypeof s) : ain (aelements s a) s.
Proof.
  destruct s as [A f]; simpl in *. by exists a.
Qed.

Lemma ain_morph s s' t t' :
  aeq s s' → aeq t t' → ain s t → ain s' t'.
Proof.
  intros H1 H2 H3.
  destruct t as [B1 g1]. simpl in H3. destruct H3 as [b1 H3].
  destruct t' as [B2 g2]. simpl. simpl in H2. destruct H2 as [H2 _].
  destruct (H2 b1) as [b2 H4]. exists b2.
  rewrite <- H4. by rewrite <- H1.
Qed.

(* Extensionality *)
Lemma aeq_ext s t :
  asubs s t → asubs t s → aeq s t.
Proof.
  destruct s as [A f], t as [B g].
  intros Hfg Hgf; simpl; split.
  - intros a. destruct (Hfg (f a) (ain_Asup _ f a)) as [b ?]; eauto.
  - intros b. destruct (Hgf (g b) (ain_Asup _ g b)) as [a ?]; eauto.
Qed.

Global Instance ain_proper :
  Proper (aeq ==> aeq ==> iff) ain.
Proof.
  intros s s' H1 t t' H2. split; intros H.
  - by eapply ain_morph.
  - apply aeq_sym in H1. apply aeq_sym in H2.
    by eapply ain_morph.
Qed.

Global Instance asubs_proper :
  Proper (aeq ==> aeq ==> iff) asubs.
Proof.
intros s s' H1 t t' H2. split; intros H.
- intros u. rewrite <- H1, <- H2. apply H.
- intros u. rewrite H1 H2. apply H.
Qed.


Lemma aeq_subs s t :
  aeq s t → asubs s t.
Proof.
  intros ->; by intros ?.
Qed.

Lemma aeq_acc_morph s t:
  aeq s t → Acc ain s → Acc ain t.
Proof.
  revert t. induction s as [A f IH].
  intros [B g] H1 H2. constructor.
  intros u [b H3]. destruct H1 as [_ H1].
  destruct (H1 b) as [a H4]. apply (IH a).
  - by rewrite H4.
  - apply H2. apply ain_Asup.
Qed.

Lemma ain_wf: well_founded ain.
Proof.
  intros s; induction s as [A f IH].
  constructor. intros t [a H].
  symmetry in H. by eapply aeq_acc_morph, IH.
Qed.

End aczel_trees.

Section set_theory.

  (* sigma type for sets based on aczel trees *)
  Polymorphic Record set@{i} := mkset {
    set_tree :> Acz@{i};
    set_tree_is_normal: norm aeq set_tree = set_tree
  }.

  Definition aset s: set := mkset (norm aeq s) (norm_idem aeq s).
  Definition el (x y: set) := ain x y.

  Global Instance in_elem_of: ElemOf set set := el.
  Lemma el_unfold (X Y: set): X ∈ Y = el X Y.
  Proof. reflexivity. Qed.

  Definition subs (X Y : set) := ∀ Z, Z ∈ X → Z ∈ Y.
  Global Instance subs_subseteq: SubsetEq set := subs.
  Lemma subs_unfold (X Y: set): X ⊆ Y = subs X Y.
  Proof. reflexivity. Qed.


  Section set_lemmas.
    Implicit Types s t u : Acz.
    Implicit Types X Y Z: set.

    (* equality *)
    Lemma mkset_pi s t (H1 : norm aeq s = s) (H2 : norm aeq t = t) :
      s = t → mkset s H1 = mkset t H2.
    Proof.
      intros XY. subst t. f_equal. apply norm_pi.
    Qed.

    Lemma aset_idem (X : set): aset (set_tree X) = X.
    Proof.
      destruct X. simpl. by apply mkset_pi.
    Qed.

    Lemma aeq_aset s: aeq (aset s) s.
    Proof. symmetry; simpl. eapply (rel_norm_intro aeq). Qed.

    Lemma aeq_aset_eq s t :
      aeq s t → aset s = aset t.
    Proof.
      intros H % (rel_norm aeq). by apply mkset_pi.
    Qed.

    Lemma aeq_eq X Y:
      aeq X Y → X = Y.
    Proof.
      intros Heq % aeq_aset_eq; revert Heq; by rewrite !aset_idem.
    Qed.

    (* elements *)
    Lemma ain_aset s t : ain s t ↔ aset s ∈ aset t.
    Proof.
      by rewrite el_unfold /el !aeq_aset.
    Qed.

    Lemma asubs_subseteq (x y: set): asubs x y ↔ x ⊆ y.
    Proof.
      rewrite subs_unfold /subs /asubs; split.
      - intros Hacz z; rewrite !el_unfold /el; eauto.
      - intros Hset u; specialize (Hset (aset u)); revert Hset.
        by rewrite !el_unfold /el aeq_aset.
    Qed.

    Lemma eq_ext (x y: set): x ⊆ y → y ⊆ x → x = y.
    Proof.
      intros Hsub Hsub'; eapply aeq_eq, aeq_ext; by eapply asubs_subseteq.
    Qed.

    Lemma el_wf: well_founded el.
    Proof.
      intros x. destruct x as [s NX].
      induction (ain_wf s) as [s _ IH].
      constructor. intros [t NY] YX.
      by apply IH.
    Qed.

  End set_lemmas.
End set_theory.

(* shorthands hiding the normalizer and the aczel trees *)
Definition setof {X: Type} (f: X → set): set := aset (Asup X (λ x, set_tree (f x))).
Notation "{{ f | x : X } }" := (@setof X (λ x, f)) (x pattern, at level 60).

Definition typeof (s: set) : Type := atypeof s.
Definition elements (s: set): typeof s → set := λ x, aset (aelements s x).

Lemma in_inv {Y} x (f: Y → set): x ∈ setof f → ∃ y, x = f y.
Proof.
  rewrite el_unfold /el aeq_aset.
  intros [y Hy]. exists y. by apply aeq_eq.
Qed.

Lemma in_intro {Y} x y (f: Y → set): x = f y → x ∈ setof f.
Proof.
  intros ->. rewrite el_unfold /el aeq_aset. by exists y.
Qed.

Lemma setof_ext {Y} (f g: Y → set): (∀ y, f y = g y) → setof f = setof g.
Proof.
  intros Heq. unfold setof. eapply aeq_aset_eq; simpl.
  split; intros a; exists a; rewrite Heq; reflexivity.
Qed.

Lemma setof_eta (s: set): {{ elements s x | x: typeof s }} = s.
Proof.
  apply aeq_eq; rewrite aeq_aset; destruct s as [[X f]]; simpl.
  split; intros a; exists a; symmetry; by rewrite -(rel_norm_intro aeq).
Qed.

Lemma elements_in s x: elements s x ∈ s.
Proof.
  replace s with ({{ elements s x | x: typeof s }}) at 2 by apply setof_eta.
  by eapply in_intro.
Qed.

Lemma in_inv_elements s t: s ∈ t → ∃ x: typeof t, s = elements t x.
Proof.
  replace t with ({{ elements t x | x: typeof t }}) at 1 by apply setof_eta.
  intros [x ->] % in_inv. by exists x.
Qed.

(* we define some useful set operations *)
Definition empty_set : set := {{ match f with end | f : False }}.
Global Instance empty_set_empty : Empty set := empty_set.
Definition pair_set s t : set := {{ if b then s else t | b : bool }}.
Definition union_set s : set :=
  {{ elements (elements s a) b | (existT a b) : { a: typeof s & typeof (elements s a) } }}.
Definition singleton_set s : set := pair_set s s.

Lemma empty_set_characteristic (x : set): ¬ x ∈ (∅: set).
Proof.
  by intros [f H] % in_inv.
Qed.

(* Unordered Pairs *)
Lemma pair_set_characteristic (x y z: set):
  x ∈ (pair_set y z) ↔ x = y ∨ x = z.
Proof.
  split.
  - intros [[] H] % in_inv; auto.
  - intros [|]; by [eapply (in_intro _ true)|eapply (in_intro _ false)].
Qed.

Lemma singleton_set_characteristic (x y: set):
  x ∈ (singleton_set y) ↔ x = y.
Proof.
  rewrite /singleton_set pair_set_characteristic; tauto.
Qed.

Lemma union_set_characteristic (x z: set) :
  x ∈ union_set z ↔ ∃ y: set, x ∈ y ∧ y ∈ z.
Proof.
  split.
  - intros [[a f] ->] % in_inv. exists (elements z a); eauto using elements_in.
  - intros (y & [a ->] % in_inv_elements & [b ->] % in_inv_elements).
    by eapply (in_intro _ (existT b a)).
Qed.


Definition filter_set (P: set → Prop) s : set :=
  {{ elements s a | (exist _ a _) : ({a: typeof s | P (elements s a)}) }}.

Lemma filter_set_characteristic P s x:
  x ∈ filter_set P s ↔ x ∈ s ∧ P x.
Proof.
  split.
  - intros [[a HP] ->] % in_inv; eauto using elements_in.
  - intros [[a ->] % in_inv_elements HP]; by apply (in_intro _ (exist _ a HP)).
Qed.

Definition inter_set s : set :=
  filter_set (λ t, ∀ u, u ∈ s → t ∈ u) (union_set s).

Lemma inter_set_characteristic s u :
  u ∈ inter_set s ↔ (∃ y: set, u ∈ y ∧ y ∈ s) ∧ (∀ t, t ∈ s → u ∈ t).
Proof.
  by rewrite /inter_set filter_set_characteristic union_set_characteristic.
Qed.

Definition bunion_set s t : set :=
  union_set (pair_set s t).

Definition binter_set s t : set :=
  inter_set (pair_set s t).

Lemma bunion_set_characteristic s t u :
  u ∈ bunion_set s t ↔ u ∈ s ∨ u ∈ t.
Proof.
  rewrite /bunion_set union_set_characteristic; split.
  - intros (y & Hin & [|] % pair_set_characteristic); subst; eauto.
  - intros [|]; eexists; rewrite pair_set_characteristic; eauto.
Qed.

Lemma binter_set_characteristic s t u :
  u ∈ binter_set s t ↔ u ∈ s ∧ u ∈ t.
Proof.
  rewrite /binter_set inter_set_characteristic; split.
  - intros [_ Hin]; split; eapply Hin, pair_set_characteristic; eauto.
  - intros [Hs Ht]; split.
    + exists s; rewrite pair_set_characteristic; eauto.
    + intros v [|] % pair_set_characteristic; subst; auto.
Qed.

Lemma binter_set_subs_1 s t :
  binter_set s t ⊆ s.
Proof.
  intros x; rewrite binter_set_characteristic; tauto.
Qed.

Lemma binter_set_subs_2 s t :
  binter_set s t ⊆ t.
Proof.
    intros x; rewrite binter_set_characteristic; tauto.
Qed.

Lemma not_subs (x y: set):
  x ⊈ y → ∃ z: set, z ∈ x ∧ ¬ z ∈ y.
Proof.
  rewrite subs_unfold /subs classic_not_forall ex_impl; intros z; rewrite classic_not_impl; eauto.
Qed.

Lemma in_irrefl (x: set): x ∉ x.
Proof.
  rewrite el_unfold; induction (el_wf x) as [x _ IH]; intros Hel; by eapply IH.
Qed.

(* ordinals *)
Inductive ordinal (x: set) : Prop :=
  is_ordinal:
    (∀ y: set, y ∈ x → ordinal y) → (* all elements are ordinals *)
    (∀ y: set, y ∈ x → y ⊆ x) →     (* x is transitive *)
    ordinal x.

Lemma ordinal_el x y: x ∈ y → ordinal y → ordinal x.
Proof. destruct 2; auto. Qed.

Lemma ordinal_trans (x y z: set): x ∈ y → y ∈ z → ordinal z → x ∈ z.
Proof. destruct 3 as [_ Htrans]; by eapply Htrans. Qed.

Lemma ordinal_linear (x y: set):
  ordinal x →
  ordinal y →
  x ∈ y ∨ x = y ∨ y ∈ x.
Proof.
  intros Hox; revert y; induction Hox as [x Hord IHx Hsub].
  intros y Hoy; induction Hoy as [y Hord' IHy Hsub'].
  destruct (classic (x ⊆ binter_set x y)) as [H|H].
  - destruct (classic (y ⊆ binter_set x y)) as [|(z & Hy & Hzxy) % not_subs].
    + right; left.
      transitivity (binter_set x y); apply eq_ext; eauto using binter_set_subs_1, binter_set_subs_2.
    + destruct (IHy z Hy) as [|[|]].
      * left. eapply Hsub'; eauto.
      * left; subst z; eauto.
      * exfalso. apply Hzxy, binter_set_characteristic; done.
  - eapply not_subs in H as (z & Hx & Hxyz).
    destruct (IHx z Hx y) as [|[|]]; first by constructor.
    + exfalso. apply Hxyz, binter_set_characteristic; done.
    + subst. eauto.
    + right. right. eapply Hsub; done.
Qed.


Lemma ordinal_subs (x y: set):
  ordinal x → ordinal y → x ≠ y → x ⊆ y → x ∈ y.
Proof.
  intros Hox Hoy Hneq Hsub. destruct (ordinal_linear x y) as [|[|H]]; [done.. | |].
  - tauto.
  - eapply Hsub in H as [] % in_irrefl.
Qed.

Definition succ_set x := bunion_set x (singleton_set x).

Lemma succ_set_ordinal x: ordinal x → ordinal (succ_set x).
Proof.
  intros Hord; split; intros y;
    rewrite bunion_set_characteristic singleton_set_characteristic.
  - intros [| ->]; eauto using ordinal_el.
  - intros [| ->]; intros z Hz; rewrite bunion_set_characteristic singleton_set_characteristic; eauto using ordinal_trans.
Qed.

Lemma succ_set_iff (x y: set): x ∈ succ_set y ↔ x ∈ y ∨ x = y.
Proof.
  by rewrite bunion_set_characteristic singleton_set_characteristic.
Qed.


Lemma ordinal_case_succ_set x: ordinal x → (∃ y, x = succ_set y) ∨ (∀ y, y ∈ x → succ_set y ∈ x).
Proof.
  intros Hord; destruct (classic (∃ y, x = succ_set y)) as [|Hset]; [by eauto|].
  revert Hset; rewrite classic_not_exists; intros Hset; right.
  intros y Hin. destruct (ordinal_linear (succ_set y) x) as [|[|Hsucc]]; [eauto using succ_set_ordinal, ordinal_el|done|done| |].
  + subst x. exfalso; by eapply Hset.
  + revert Hsucc. rewrite succ_set_iff; intros Hsucc; exfalso.
    destruct Hsucc as [|]; subst; eapply in_irrefl; last by eauto.
    eapply ordinal_trans; eauto.
Qed.

Declare Scope ordinals.
Delimit Scope ordinals with O.
Local Open Scope ordinals.

Record ord@{i}:= Ord {
  ord_set :> set@{i};
  ord_set_is_ordinal : ordinal ord_set
}.
Implicit Types α β γ δ : ord.
Global Hint Immediate ord_set_is_ordinal : core.

(* NOTE: This proof uses proof_irrelevance.  *)
Lemma ord_extensional α β: ord_set α = ord_set β → α = β.
Proof.
  intros Heq. destruct α as [s Hs], β as [t Ht]; simpl in *.
  subst s. f_equal. apply proof_irrelevance.
Qed.

Lemma ord_trans α (x y: set): x ∈ (α: set) → y ∈ x → y ∈ (α: set).
Proof.
  intros H1 H2; eapply ordinal_trans; eauto.
Qed.

Lemma ord_in_ordinal α (x: set): x ∈ (α: set) → ordinal x.
Proof.
  intros H; eapply ordinal_el; eauto.
Qed.

Program Definition zero_def : ord := {| ord_set := ∅ |}.
Next Obligation.
  split; intros ? [] % empty_set_characteristic.
Qed.


Program Definition succ_def α : ord := {| ord_set := bunion_set α (singleton_set α); ord_set_is_ordinal := succ_set_ordinal α (ord_set_is_ordinal α) |}.

Program Definition limit {X} (f: X → ord) := {| ord_set := union_set ({{ f x | x : X}}) |}.
Next Obligation.
  intros X f. split; intros x [y [Hxy [a ->] % in_inv]] % union_set_characteristic.
  - eapply ord_in_ordinal, Hxy.
  - intros z Hzx; rewrite union_set_characteristic.
    exists (f a); split; [|by eapply in_intro].
    eapply ord_trans; eauto.
Qed.

Definition one_def : ord := succ_def (zero_def).


(* We make this notion only available in the ordinal scope.
   This way it does not override the step-index notation. *)
Notation "'zero'" := (zero_def) : ordinals.
Notation "'succ' x" := (succ_def x) (at level 20, no associativity): ordinals.
Notation "'one'" := (one_def) : ordinals.

Definition ord_lt (α β : ord) := (α: set) ∈ (β: set).
Infix "≺" := ord_lt (at level 80) : ordinals.
Infix "⪯" := (rc ord_lt) (at level 80) : ordinals.



Lemma ord_lt_unfold α β: α ≺ β ↔ (α: set) ∈ (β: set).
Proof. reflexivity. Qed.

Lemma ord_leq_unfold α β: α ⪯ β ↔ (α: set) ⊆ (β: set).
Proof.
  split.
  - intros [->|H]; first by intros ?.
    intros x Hxα. eapply ord_trans; eauto.
  - destruct (ordinal_linear α β) as [H|[H % ord_extensional|Hβα]]; auto.
    intros Hαβ. exfalso. eapply in_irrefl, Hαβ, Hβα.
Qed.


Program Definition ordinals (α: ord) (x: typeof α): ord :=
  {| ord_set := elements α x |}.
Next Obligation.
  intros α x. eapply ordinal_el; eauto using elements_in.
Qed.

Lemma ordinals_lt α x: ordinals α x ≺ α.
Proof.
  apply ord_lt_unfold, elements_in.
Qed.
Global Hint Immediate ordinals_lt : core.

Lemma ord_leq_ords α β: α ⪯ β ↔ ∀ γ: ord, γ ≺ α → γ ≺ β.
Proof.
  rewrite ord_leq_unfold; split.
  - intros H γ; eapply H.
  - intros Hsub x Hin. by apply (Hsub (Ord x (ord_in_ordinal _ _ Hin))).
Qed.

(** Step-Index Instance *)
(* Transitivity *)
Global Instance ord_lt_trans : Transitive ord_lt.
Proof.
  intros α β γ Hαβ Hβγ; eapply ord_trans; eauto.
Qed.

(* ordinal induction and well-foundedness *)
Lemma ord_ind (P: ord → Prop): (∀ α, (∀ β, β ≺ α → P β) → P α) → ∀ α, P α.
Proof.
  intros Hind [x Hord]. revert Hord.
  induction (el_wf x) as [x _ IH].
  intros Hord; eapply Hind; intros [y Hord'] Hlt.
  eapply IH, Hlt.
Qed.

Lemma wf_ord_lt: well_founded ord_lt.
Proof.
  intros α. induction α using ord_ind.
  by constructor.
Qed.

Lemma ord_linear α β: α ≺ β ∨ α = β ∨ β ≺ α.
Proof.
  destruct (ordinal_linear α β) as [|[|]]; eauto using ord_extensional.
Qed.

(* strong linearity *)
Lemma ord_linear_strong α β: (α ≺ β) + (α = β) + (β ≺ α).
Proof.
  destruct (classic_or_to_sum _ _ (ord_linear α β)) as [H|[H|H] % classic_or_to_sum]; eauto.
Qed.

(* zero *)
Lemma zero_least α: α ≺ zero → False.
Proof.
    apply empty_set_characteristic.
Qed.

Corollary no_smaller_than_zero: ¬ (∃ α, α ≺ zero).
Proof. by intros [α H % zero_least]. Qed.

(* successor *)
Lemma succ_leq_iff (α β: ord): (α ≺ succ β) ↔ α ⪯ β.
Proof.
  rewrite rc_iff /ord_lt succ_set_iff //=.
  split; intros [|]; [by eauto| |by eauto|subst α; eauto].
  right; by eapply ord_extensional.
Qed.

Lemma succ_greater (α: ord): α ≺ succ α.
Proof.
  rewrite succ_leq_iff; eauto.
Qed.

Lemma succ_least_greater α β: α ≺ β → succ α ⪯ β.
Proof.
  intros H. apply ord_leq_ords. intros γ; rewrite succ_leq_iff.
  intros [|]; subst; eauto using ord_lt_trans.
Qed.

Lemma ord_case_succ α: (∃ β: ord, α = succ β) ∨ (∀ β: ord, β ≺ α → succ β ≺ α).
Proof.
  destruct (ordinal_case_succ_set α) as [[x Heq]|Hlim]; first by eauto.
  - left. enough (ordinal x) as Hx by (exists (Ord x Hx); eauto using ord_extensional).
    eapply ordinal_el; first by (apply succ_set_iff; eauto).
    rewrite -Heq; eauto.
  - right. intros β; eapply Hlim.
Qed.

Lemma ord_case_succ_strong α: {β : ord | α = succ β} + (∀ β : ord, β ≺ α → succ β ≺ α).
Proof.
  destruct (classic_or_to_sum _ _ (ord_case_succ α)) as [He|Hlim].
  - left. by eapply constructive_indefinite_description in He.
  - right. done.
Qed.


Section set_ordinal_lemmas.


  Lemma ord_lt_inv_ordinals β α: β ≺ α → ∃ x: typeof α, β = ordinals α x.
  Proof.
    intros [x Hx] % in_inv_elements. exists x. apply ord_extensional, Hx.
  Qed.

  (* limit operation *)
  Lemma limit_upper_bound_strong (X : Type) (f : X → ord) (α: ord):
    (∀ β, β ≺ α → ∃ x, β ≺ f x) → α ⪯ limit f.
  Proof.
    intros H. apply ord_leq_ords. intros s [a ->] % ord_lt_inv_ordinals.
    destruct (H (ordinals α a) (ordinals_lt α a)) as [x Hleq].
    apply union_set_characteristic. exists (f x); eauto using in_intro.
  Qed.

  Lemma limit_upper_bound {X} (f: X → ord) x: f x ⪯ limit f.
  Proof.
    eapply limit_upper_bound_strong; eauto.
  Qed.

  Lemma limit_least_upper_bound {X} (f: X → ord) y: (∀ x, f x ⪯ y) → limit f ⪯ y.
  Proof.
    intros Hle. apply ord_leq_unfold.
    intros s [t [Hst Hf]] % union_set_characteristic. apply in_inv in Hf as [x ->].
    eapply ord_leq_unfold; [ | apply Hst]. apply Hle.
  Qed.

  Lemma limit_ext {Y} (f g: Y → ord):
    (∀ x, f x = g x) → limit f = limit g.
  Proof.
    intros Heq. apply ord_extensional; simpl.
    f_equal. apply setof_ext. intros x. by destruct (Heq x).
  Qed.

  Lemma limit_mono_strong {A B} (F: A → ord) (G: B → ord): (∀ a, ∃ b, F a ⪯ G b) → limit F ⪯ limit G.
  Proof.
    intros H.
    apply limit_least_upper_bound. intros x. destruct (H x) as [b Hle].
    transitivity (G b); eauto using limit_upper_bound.
  Qed.

  Lemma limit_mono {A} (F: A → ord) (G: A → ord): (∀ a, F a ⪯ G a) → limit F ⪯ limit G.
  Proof.
    intros H; eapply limit_mono_strong; intros a; by exists a.
  Qed.

  (* derived limit constructor for limits of ordinals *)
  Definition limitO α (f: ∀ β, β ≺ α → ord) := limit (λ x : typeof α, f (ordinals α x) (ordinals_lt α x)).

  Lemma limitO_ext α (f g: ∀ β, β ≺ α → ord): (∀ β Hβ, f β Hβ = g β Hβ) → limitO α f = limitO α g.
  Proof.
    intros H; apply limit_ext; auto.
  Qed.
End set_ordinal_lemmas.




Section existential_property.

  (** proof that once can "pull out" existentials when using ordinals as the stepindex type *)
  Lemma constructive_upper_bound_ordinal A (φ: A → ord → Prop):
    (∀ a α β, α ⪯ β → φ a α → φ a β) →
    (∀ a : A, { α : ord | φ a α }) →
    ({ α: ord | ∀ a: A, φ a α}).
  Proof.
    intros Hge X. exists (limit (λ a : A, proj1_sig (X a))).
    intros a. destruct (X a) as [α Hφ] eqn: H.
    eapply Hge, Hφ. transitivity (proj1_sig (X a)); last apply (limit_upper_bound (λ a : A, proj1_sig (X a))).
    by rewrite H.
  Qed.

  Lemma upper_bound_ordinal (A: Type) (φ: A → ord → Prop):
    (∀ a α β, α ⪯ β → φ a α → φ a β) →
    (∀ a : A, ∃ α : ord, φ a α) →
    (∃ α: ord, ∀ a: A, φ a α).
  Proof.
  intros Hge Ha. edestruct (constructive_upper_bound_ordinal _ _ Hge) as [α Hα].
  - intros a. by apply constructive_indefinite_description.
  - by exists α.
  Qed.

  (* classical proof of the existential property *)
  Lemma commute_exists (J : Type) (P : J → ord → Prop) :
    (∀ j α β, α ≺ β → P j β → P j α)
    → (∀ α, ∃ j, P j α)
    → ∃ j, ∀ α, P j α.
  Proof.
    intros Hdown H. destruct (classic (∃ j : J, ∀ α : ord, P j α)) as [|H1]; auto.
    destruct (upper_bound_ordinal _ (λ j α, ¬ P j α)) as [α Hbound].
    - intros a α β Hle Hα Hβ. apply Hα. destruct Hle; subst; eauto.
    - intros a. revert H1. rewrite classic_not_exists -classic_not_forall; eauto.
    - exfalso. destruct (H α); by eapply Hbound.
  Qed.
End existential_property.


Section ordinal_instance.

  Universe iris.

  (* an ordinal index instance *)
  Lemma ord_index_mixin : IndexMixin ord@{iris} ord_lt (rc ord_lt) ordinals.zero_def ordinals.succ_def.
  Proof.
    constructor.
    - apply _.
    - apply wf_ord_lt.
    - apply ord_linear_strong.
    - intros n m; rewrite rc_iff; naive_solver.
    - intros n Hn. eapply no_smaller_than_zero. by eexists _.
    - apply succ_greater.
    - apply succ_least_greater.
    - apply ord_case_succ_strong.
  Qed.
  Canonical Structure ordI : indexT := IndexT (ord@{iris}) ord_lt (rc ord_lt) zero_def succ_def ord_index_mixin.

  Global Instance ordinals_large_index: ExistentialProperty@{iris} ordI.
  Proof.
    intros X P H He. eapply commute_exists; eauto.
  Qed.

End ordinal_instance.



(*
(* universe polymorphism test --  we can create a set of sets (not really, since the sets contained in the set live in a different universe, so a better description might be that this is the class of sets?) *)
Definition set_of_sets: set := {{ (∅: set) | s : set (* <- set in a smaller universe *) }}.
Definition set_of_all_sets: set := {{ s | s : set <- set in a smaller universe }}. *)
