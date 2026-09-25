From iris.prelude Require Export options prelude.
From iris.algebra Require Export ofe cmra.
From transfinite.stepindex Require Export utils.

Local Open Scope sidx_scope.

Section ofe_lemmas.
  Context {SI : sidx} {A: ofe}.

  Lemma dist_mono' (α β: SI) (x y : A) : x ≡{α}≡ y → β ≤ α → x ≡{β}≡ y.
  Proof. intros H [Hβ | ->]%SIdx.le_lteq; [by eapply dist_lt|auto]. Qed.

End ofe_lemmas.

(** Bounded completion for any non-zero index (the fork's [bcompl]).
Upstream Iris defines [bcompl : ∀ n, bchain A n → A] for inhabited [A] (returning
[inhabitant] at index [0ᵢ]); Transfinite Iris uses the variant below, which does
not require [A] to be inhabited but asks for a proof that the bound is
non-zero. *)
Section bcompl_pos.
  Context {SI : sidx} `{!Cofe A}.
  Local Unset Program Cases.
  Program Definition bcompl_pos {α} (Hz : 0ᵢ < α) (b : bchain A α) : A :=
    match SIdx.weak_case α with
    | inl Hsucc => _
    | inr Hlim => _
    end.
  Next Obligation. intros ? Hz b [β ->]. apply (b β). stepindex. Defined.
  Next Obligation.
    intros α Hz b Hlim.
    exact (lbcompl (SIdx.Limit α Hlim (proj2 (SIdx.neq_0_lt_0 α) Hz)) b).
  Defined.

  Lemma conv_bcompl_pos α Hα (c : bchain A α) β Hβ : bcompl_pos Hα c ≡{β}≡ c β Hβ.
  Proof.
    rewrite /bcompl_pos. destruct SIdx.weak_case as [[γ ->] | Hlim]; cbn.
    - apply bchain_cauchy. stepindex.
    - apply conv_lbcompl.
  Qed.

  Lemma bcompl_pos_ne {α Hα} (c d : bchain A α) β :
    (∀ γ (Hγ: γ < α), c γ Hγ ≡{β}≡ d γ Hγ) →
    bcompl_pos Hα c ≡{β}≡ bcompl_pos Hα d.
  Proof.
    intros Hdist. rewrite /bcompl_pos. destruct SIdx.weak_case as [[γ ->] | Hlim]; cbn.
    - apply Hdist.
    - by apply lbcompl_ne.
  Qed.
End bcompl_pos.

Lemma bcompl_pos_bchain_const {SI : sidx} {A : ofe} `{!Cofe A} (a : A) (n : SI) Hn:
  ∀ p, p < n → bcompl_pos Hn (bchain_const a n) ≡{p}≡ a.
Proof.
  intros p Hp. by unshelve rewrite conv_bcompl_pos //.
Qed.

Lemma cofe_bcompl_weakly_unique {SI : sidx} (A : ofe) (HA : Cofe A) (n: SI) Hn (c d : bchain A n):
  (∀ p (Hp : p < n), c p Hp ≡{p}≡ d p Hp) → dist_later n (bcompl_pos Hn c) (bcompl_pos Hn d).
Proof.
  intros H; split; intros p Hp. unshelve rewrite !conv_bcompl_pos; [assumption | assumption | apply H].
Qed.


Lemma ccompose_assoc {SI : sidx} {A B C D : ofe} (f : C -n> D) (g : B -n> C) (h : A -n> B) :
  (f ◎ g) ◎ h ≡ f ◎ (g ◎ h).
Proof. intros x. by cbn. Qed.

Lemma ccompose_cid_l {SI : sidx} {A B : ofe} (f : A -n> B ) : cid ◎ f ≡ f.
Proof. intros x. by cbn. Qed.

Lemma ccompose_cid_r {SI : sidx} {A B : ofe} (f : A -n> B ) :  f ◎ cid ≡ f.
Proof. intros x. by cbn. Qed.


(** Bounded limit preserving predicates (the fork's [BoundedLimitPreserving]).
Upstream Iris merged this into [LimitPreserving] (field
[limit_preserving_lbcompl]); Transfinite Iris also uses it on its own. *)
Class BoundedLimitPreserving {SI : sidx} `{!Cofe A} (P : A → Prop) : Prop :=
  bounded_limit_preserving n Hn (c : bchain A n) : (∀ m Hm, P (c m Hm)) → P (lbcompl Hn c).
Global Hint Mode BoundedLimitPreserving - + + ! : typeclass_instances.

Section bounded_limit_preservation.
  Context {SI : sidx}.

  Lemma bounded_limit_preserving_fun_app {A: ofe} `{!Cofe A} (P: A → Prop) X (x: X) :
    BoundedLimitPreserving P → BoundedLimitPreserving (λ f: X -d> A, P (f x)).
  Proof.
    rewrite /BoundedLimitPreserving. intros Hbound n Hn Hval Hent.
    eapply Hbound; eauto.
  Qed.

End bounded_limit_preservation.
