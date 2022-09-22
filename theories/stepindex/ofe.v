From iris.prelude Require Export options prelude.
From iris.algebra Require Export ofe cmra.



Section ofe_lemmas.
  Context `{SI: indexT} {A: ofe}.

  Lemma dist_mono' (α β: index) (x y : A) : x ≡{α}≡ y → β ⪯ α → x ≡{β}≡ y.
  Proof. intros H [-> | Hβ]; [auto | by eapply dist_mono]. Qed.

End ofe_lemmas.

Lemma cofe_bcompl_weakly_unique `{SI : indexT} (A : ofe) (HA : Cofe A) (n: index) Hn (c d : bchain A n):
  (∀ p (Hp : p ≺ n), c p Hp ≡{p}≡ d p Hp) → dist_later n (bcompl Hn c) (bcompl Hn d).
Proof.
  intros H; split; intros p Hp. unshelve rewrite !conv_bcompl; [assumption | assumption | apply H].
Qed.


Lemma ccompose_assoc `{SI : indexT} {A B C D : ofe} (f : C -n> D) (g : B -n> C) (h : A -n> B) :
  (f ◎ g) ◎ h ≡ f ◎ (g ◎ h).
Proof. intros x. by cbn. Qed.

Lemma ccompose_cid_l `{SI : indexT} {A B : ofe} (f : A -n> B ) : cid ◎ f ≡ f.
Proof. intros x. by cbn. Qed.

Lemma ccompose_cid_r `{SI : indexT} {A B : ofe} (f : A -n> B ) :  f ◎ cid ≡ f.
Proof. intros x. by cbn. Qed.
