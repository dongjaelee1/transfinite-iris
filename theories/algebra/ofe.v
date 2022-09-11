From iris.prelude Require Export prelude.
From iris.prelude Require Import options.
From iris.stepindex Require Export stepindex.
Set Primitive Projections.
(** This files defines (a shallow embedding of) the category of OFEs:
    Ordered families of equivalences. This is a cartesian closed
    category, and mathematically speaking, the entire development lives
    in this category. However, we will generally prefer to work with raw
    Coq functions plus some registered Proper instances for non-expansiveness.
    This makes writing such functions much easier. It turns out that it many
    cases, we do not even need non-expansiveness.
*)

(** Unbundeled version *)
Class Dist `{SI: indexT} A := dist : index → relation A.

Global Instance: Params (@dist) 4 := {}.
Notation "x ≡{ n }≡ y" := (dist n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Notation "x ≡{ n }@{ A }≡ y" := (dist (A:=A) n x y)
  (at level 70, n at next level, only parsing).

Global Hint Extern 0 (_ ≡{_}≡ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡{_}≡ _) => symmetry; assumption : core.
Notation NonExpansive f := (∀ n, Proper (dist n ==> dist n) f).
Notation NonExpansive2 f := (∀ n, Proper (dist n ==> dist n ==> dist n) f).

Tactic Notation "ofe_subst" ident(x) :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?SI ?A ?d ?n x _ |- _ => setoid_subst_aux (@dist SI A d n) x
  | H:@dist ?SI ?A ?d ?n _ x |- _ => symmetry in H; setoid_subst_aux (@dist SI A d n) x
  end.
Tactic Notation "ofe_subst" :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?SI ?A ?d ?n ?x _ |- _ => setoid_subst_aux (@dist SI A d n) x
  | H:@dist ?SI ?A ?d ?n _ ?x |- _ => symmetry in H;setoid_subst_aux (@dist SI A d n) x
  end.

Record OfeMixin `{SI: indexT} A `{Equiv A, Dist A} := {
  mixin_equiv_dist (x y : A) : x ≡ y ↔ ∀ (n: index), x ≡{n}≡ y;
  mixin_dist_equivalence (n : index): Equivalence (dist n);
  mixin_dist_mono (n m: index) (x y : A) : x ≡{n}≡ y → m ≺ n → x ≡{m}≡ y
}.

(** Bundled version *)
Structure ofe `{SI: indexT} := Ofe {
  ofe_car :> Type;
  ofe_equiv : Equiv ofe_car;
  ofe_dist : Dist ofe_car;
  ofe_mixin : OfeMixin ofe_car
}.
Global Arguments Ofe {_} _ {_ _} _.
Add Printing Constructor ofe.
Global Hint Extern 0 (Equiv _) => eapply (ofe_equiv _) : typeclass_instances.
Global Hint Extern 0 (Dist _) => eapply (ofe_dist _) : typeclass_instances.
Global Arguments ofe_car : simpl never.
Global Arguments ofe_equiv : simpl never.
Global Arguments ofe_dist : simpl never.
Global Arguments ofe_mixin : simpl never.

(** When declaring instances of subclasses of OFE (like CMRAs and unital CMRAs)
we need Coq to *infer* the canonical OFE instance of a given type and take the
mixin out of it. This makes sure we do not use two different OFE instances in
different places (see for example the constructors [Cmra] and [Ucmra] in the
file [cmra.v].)

In order to infer the OFE instance, we use the definition [ofe_mixin_of'] which
is inspired by the [clone] trick in ssreflect. It works as follows, when type
checking [@ofe_mixin_of' A ?Ac id] Coq faces a unification problem:

  ofe_car ?Ac  ~  A

which will resolve [?Ac] to the canonical OFE instance corresponding to [A]. The
definition [@ofe_mixin_of' A ?Ac id] will then provide the corresponding mixin.
Note that type checking of [ofe_mixin_of' A id] will fail when [A] does not have
a canonical OFE instance.

The notation [ofe_mixin_of A] that we define on top of [ofe_mixin_of' A id]
hides the [id] and normalizes the mixin to head normal form. The latter is to
ensure that we do not end up with redundant canonical projections to the mixin,
i.e. them all being of the shape [ofe_mixin_of' A id]. *)
Definition ofe_mixin_of' `{SI: indexT} A {Ac : ofe} (f : Ac → A) : OfeMixin Ac := ofe_mixin Ac.
Notation ofe_mixin_of A :=
  ltac:(let H := eval hnf in (ofe_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section ofe_mixin.
  Context `{SI: indexT} {A : ofe}.
  Implicit Types x y : A.

  Lemma equiv_dist x y : x ≡ y ↔ ∀ (n: index), x ≡{n}≡ y.
  Proof. apply (mixin_equiv_dist _ (ofe_mixin A)). Qed.
  Global Instance dist_equivalence n : Equivalence (@dist SI A _ n).
  Proof. apply (mixin_dist_equivalence _ (ofe_mixin A)). Qed.
  Lemma dist_mono (n m: index) x y : x ≡{n}≡ y → m ≺ n → x ≡{m}≡ y.
  Proof. apply (mixin_dist_mono _ (ofe_mixin A)). Qed.
  Lemma dist_mono' (n m: index) x y : x ≡{n}≡ y → m ⪯ n → x ≡{m}≡ y.
  Proof. intros H [-> | Hm]; [auto | by eapply dist_mono]. Qed.
End ofe_mixin.

Global Hint Extern 1 (_ ≡{_}≡ _) => apply equiv_dist; assumption : core.

(** Discrete OFEs and discrete OFE elements *)
Class Discrete `{SI: indexT} {A : ofe} (x : A) := discrete y : x ≡{zero}≡ y → x ≡ y.
Global Arguments discrete {_ _} _ {_} _ _.
Global Hint Mode Discrete - + ! : typeclass_instances.
Global Instance: Params (@Discrete) 2 := {}.

Class OfeDiscrete `{SI: indexT} (A : ofe) := ofe_discrete_discrete (x : A) :> Discrete x.
Global Hint Mode OfeDiscrete - ! : typeclass_instances.

(** OFEs with a completion *)
Record chain `{SI: indexT} (A : ofe) := mkchain {
  chain_car :> index → A;
  chain_cauchy n m: n ⪯ m → chain_car m ≡{n}≡ chain_car n
}.
Global Arguments chain_car {_ _} _ _.
Global Arguments chain_cauchy {_ _} _ _ _ _.


Record bchain `{SI: indexT} (A : ofe) (n: index) := mkbchain {
  bchain_car :>  ∀ m, m ≺ n → A;
  bchain_cauchy m p Hm Hp: m ⪯ p → bchain_car p Hp ≡{m}≡ bchain_car m Hm
}.
Global Arguments bchain_car {_ _} _ _ _.
Global Arguments bchain_cauchy {_ _} _ _ _ _ _.


Program Definition chain_map `{SI: indexT} {A B : ofe} (f : A → B) `{NonExpansive f} (c : chain A) : chain B :=
  {| chain_car n := f (c n) |}.
Next Obligation. by intros SI A B f Hf c n i ?; apply Hf, chain_cauchy. Qed.

Program Definition bchain_map `{SI: indexT} {A B : ofe} (f : A → B) `{NonExpansive f} {n} (c: bchain A n) : bchain B n :=
  {| bchain_car m Hm := f (c m Hm) |}.
Next Obligation. by intros SI A B f Hf n c m p ? Hm Hp; apply Hf, bchain_cauchy. Qed.

Class Cofe `{SI: indexT} (A : ofe) :=
  {
    compl : chain A → A;
    (** We only require a bounded limit operation for proper limit indices *)
    lbcompl {n} : index_is_proper_limit n → bchain A n → A;
    conv_compl n c : compl c ≡{n}≡ c n;
    conv_lbcompl n Hn (c: bchain A n) m Hm: lbcompl Hn c ≡{m}≡ c m Hm;
    lbcompl_ne {n Hn} (c d: bchain A n) m: (∀ p (Hp: p ≺ n), c p Hp ≡{m}≡ d p Hp) → lbcompl Hn c ≡{m}≡ lbcompl Hn d
  }.
Global Arguments compl : simpl never.
Global Arguments lbcompl : simpl never.
Global Hint Mode Cofe - ! : typeclass_instances.

(** But we can derive bounded limits for all non-zero indices. *)
Section bcompl.
  Context `{SI : indexT} `{!Cofe A}.
  Local Unset Program Cases.
  Program Definition bcompl {α} (Hz : zero ≺ α) (b : bchain A α) : A :=
    match index_dec_limit α with
    | inl Hsucc => _
    | inr Hlim => _
    end.
  Next Obligation. intros ? Hz b [β ->]. apply (b β). eauto. Defined.
  Next Obligation. intros α Hz b Hlim. by unshelve eapply (lbcompl _ b). Defined.

  Lemma conv_bcompl α Hα (c : bchain A α) β Hβ : bcompl Hα c ≡{β}≡ c β Hβ.
  Proof.
    rewrite /bcompl. destruct index_dec_limit as [[γ ->] | Hlim]; cbn.
    - apply bchain_cauchy. eauto.
    - apply conv_lbcompl.
  Qed.

  Lemma bcompl_ne {α Hα} (c d : bchain A α) β :
    (∀ γ (Hγ: γ ≺ α), c γ Hγ ≡{β}≡ d γ Hγ) →
    bcompl Hα c ≡{β}≡ bcompl Hα d.
  Proof.
    intros Hdist. rewrite /bcompl. destruct index_dec_limit as [[γ ->] | Hlim]; cbn.
    - apply Hdist.
    - by apply lbcompl_ne.
  Qed.
End bcompl.


(* TODO: remove these lemmas *)
Lemma chain_conv_compl `{SI: indexT} `{!Cofe A} (c: chain A) n : compl c ≡{n}≡ c n.
Proof. rewrite conv_compl; eauto using chain_cauchy. Qed.

Lemma bchain_conv_bcompl `{SI: indexT} `{!Cofe A} n Hn (c: bchain A n) m Hm: bcompl Hn c ≡{m}≡ c m Hm.
Proof. rewrite conv_bcompl; eauto using bchain_cauchy. Qed.

Lemma compl_chain_map `{SI: indexT} `{!Cofe A, !Cofe B} (f : A → B) (c: chain A) `(NonExpansive f) :
  compl (chain_map f c) ≡ f (compl c).
Proof. apply equiv_dist=>n. by rewrite !chain_conv_compl. Qed.

Program Definition chain_const `{SI: indexT} {A : ofe} (a : A) : chain A :=
  {| chain_car n := a |}.
Next Obligation. by intros ??????. Qed.

Lemma compl_chain_const `{SI: indexT} {A : ofe} `{!Cofe A} (a : A) :
  compl (chain_const a) ≡ a.
Proof. apply equiv_dist=>n. by rewrite chain_conv_compl. Qed.

Program Definition bchain_const `{SI : indexT} {A : ofe} (a : A) n : bchain A n :=
  {| bchain_car m _ := a |}.
Next Obligation.
  by intros ????????.
Qed.

Lemma bcompl_bchain_const `{SI: indexT} {A : ofe} `{!Cofe A} (a : A) (n : index) Hn:
  ∀ p, p ≺ n → bcompl Hn (bchain_const a n) ≡{p}≡ a.
Proof.
  intros p Hp. by unshelve rewrite bchain_conv_bcompl.
Qed.

(** General properties *)
Section ofe.
  Context `{SI: indexT} {A : ofe}.
  Implicit Types x y : A.
  Global Instance ofe_equivalence : Equivalence ((≡) : relation A).
  Proof.
    split.
    - by intros x; rewrite equiv_dist.
    - by intros x y; rewrite !equiv_dist.
    - by intros x y z; rewrite !equiv_dist; intros; trans y.
  Qed.
  Global Instance dist_ne n : Proper (dist n ==> dist n ==> iff) (@dist SI A _ n).
  Proof.
    intros x1 x2 ? y1 y2 ?; split; intros.
    - by trans x1; [|trans y1].
    - by trans x2; [|trans y2].
  Qed.
  Global Instance dist_proper n : Proper ((≡) ==> (≡) ==> iff) (@dist SI A _ n).
  Proof.
    by move => x1 x2 /equiv_dist Hx y1 y2 /equiv_dist Hy; rewrite (Hx n) (Hy n).
  Qed.
  Global Instance dist_proper_2 n x : Proper ((≡) ==> iff) (dist n x).
  Proof. by apply dist_proper. Qed.
  Global Instance Discrete_proper : Proper ((≡) ==> iff) (@Discrete SI A).
  Proof. intros x y Hxy. rewrite /Discrete. by setoid_rewrite Hxy. Qed.

  Lemma dist_le n n' x y : x ≡{n}≡ y → n' ⪯ n → x ≡{n'}≡ y.
  Proof. destruct 2; eauto using dist_mono; congruence. Qed.
  Lemma dist_le' n n' x y : n' ⪯ n → x ≡{n}≡ y → x ≡{n'}≡ y.
  Proof. intros; eauto using dist_le. Qed.
  (** [ne_proper] and [ne_proper_2] are not instances to improve efficiency of
  type class search during setoid rewriting.
  Local Instances of [NonExpansive{,2}] are hence accompanied by instances of
  [Proper] built using these lemmas. *)
  Lemma ne_proper {B : ofe} (f : A → B) `{!NonExpansive f} :
    Proper ((≡) ==> (≡)) f.
  Proof. by intros x1 x2; rewrite !equiv_dist; intros Hx n; rewrite (Hx n). Qed.
  Lemma ne_proper_2 {B C : ofe} (f : A → B → C) `{!NonExpansive2 f} :
    Proper ((≡) ==> (≡) ==> (≡)) f.
  Proof.
     unfold Proper, respectful; setoid_rewrite equiv_dist.
     by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
  Qed.

  Lemma conv_compl' `{!Cofe A} (n m: index) (c: chain A) : n ⪯ m → compl c ≡{n}≡ c m.
  Proof.
    transitivity (c n); first by apply chain_conv_compl. symmetry. by rewrite chain_cauchy.
  Qed.

  Lemma discrete_iff n (x : A) `{!Discrete x} y : x ≡ y ↔ x ≡{n}≡ y.
  Proof.
    split; intros; auto. apply (discrete _), dist_le with n; auto.
  Qed.
  Lemma discrete_iff_0 n (x : A) `{!Discrete x} y : x ≡{zero}≡ y ↔ x ≡{n}≡ y.
  Proof. by rewrite -!discrete_iff. Qed.
End ofe.

(** Contractive functions *)
Definition dist_later {SI: indexT} `{!Dist A} (n : index) (x y : A) : Prop :=
  ∀ m, m ≺ n → x ≡{m}≡ y.

Global Arguments dist_later _ _ _ !_ _ _ /.

Global Instance dist_later_equivalence `{SI: indexT} (A : ofe) n : Equivalence (@dist_later SI A _ n).
Proof.
  split.
  - now intros ???.
  - unfold dist_later; intros ?? H ??; now rewrite H.
  - unfold dist_later; intros ??? H1 H2 ??; now rewrite H1 ?H2.
Qed.

Lemma dist_dist_later `{SI: indexT} {A : ofe} n (x y : A) : dist n x y → dist_later n x y.
Proof. intros Heq ??; eapply dist_mono; eauto. Qed.

Lemma dist_later_dist `{SI: indexT} {A : ofe} n m (x y : A) : m ≺ n → dist_later n x y → dist m x y.
Proof. intros ? H; by apply H. Qed.
(* We don't actually need this lemma (as our tactics deal with this through
   other means), but technically speaking, this is the reason why
   pre-composing a non-expansive function to a contractive function
   preserves contractivity. *)
Lemma ne_dist_later `{SI: indexT} {A B : ofe} (f : A → B) :
  NonExpansive f → ∀ n, Proper (dist_later n ==> dist_later n) f.
Proof. intros Hf ??????; by eapply Hf, H. Qed.

Lemma dist_later_zero `{SI: indexT} {A : ofe} (x y : A): dist_later zero x y.
Proof. intros ? [] % index_lt_zero_is_normal. Qed.

Global Instance ne2_dist_later_l `{SI: indexT} {A B C: ofe} (f : A → B → C) :
  NonExpansive2 f → ∀ n, Proper (dist_later n ==> dist n ==> dist_later n) f.
Proof. intros H n a b H1 c d H2 m Hm. apply H; by eauto using dist_mono. Qed.
Global Instance ne2_dist_later_r `{SI: indexT} {A B C: ofe} (f : A → B → C) :
  NonExpansive2 f → ∀ n, Proper (dist n ==> dist_later n ==> dist_later n) f.
Proof. intros H n a b H1 c d H2 m Hm. apply H; by eauto using dist_mono. Qed.


Notation Contractive f := (∀ n, Proper (dist_later n ==> dist n) f).

Global Instance const_contractive `{SI: indexT} {A B : ofe} (x : A) : Contractive (@const A B x).
Proof. by intros n y1 y2. Qed.

Section contractive.
  Local Set Default Proof Using "Type*".
  Context `{SI: indexT} {A B : ofe} (f : A → B) `{!Contractive f}.
  Implicit Types x y : A.

  Lemma contractive_0 x y : f x ≡{zero}≡ f y.
  Proof. by apply (_ : Contractive f), dist_later_zero. Qed.
  Lemma contractive_mono n x y : dist_later n x y → f x ≡{n}≡ f y.
  Proof. by apply (_ : Contractive f). Qed.

  Global Instance contractive_ne : NonExpansive f | 100.
  Proof.
    intros n x y ?; eapply (dist_mono (succ n)), index_succ_greater.
    eapply contractive_mono.
    intros ??. eapply dist_le; eauto.
  Qed.

  Global Instance contractive_proper : Proper ((≡) ==> (≡)) f | 100.
  Proof. apply (ne_proper _). Qed.
End contractive.

(* TODO: fix f_contractive *)
Ltac f_contractive :=
  match goal with
  | |- ?f _ ≡{_}≡ ?f _ => simple apply (_ : Proper (dist_later _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (dist_later _ ==> _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (_ ==> dist_later _ ==> _) f)
  | |- dist_later _ (?f _) (?f _) => simple apply (_ : Proper (dist_later _ ==> dist_later _) f)
  | |- dist_later _ (?f _ _) (?f _ _) => simple apply (_ : Proper (dist_later _ ==> _ ==> dist_later _) f)
  | |- dist_later _ (?f _ _) (?f _ _) => simple apply (_ : Proper (_ ==> dist_later _ ==> dist_later _) f)
  end;
  try simple apply reflexivity.

(* FIXME: the last clause is a hacky addition since the approach for dealing this from finite Iris (destructing the index) cannot be directly translated.
  we might want to look for a smarter solution. *)
Ltac solve_contractive :=
  solve_proper_core ltac:(fun _ => first [f_contractive | f_equiv |
      try match goal with
        | H : @dist_later _ ?A _ _ ?x ?y |- ?x ≡{_}≡ ?y =>
            by (apply H; eauto 3 with index)
      end]).

(* without smoothness, we only get uniqueness at ≺ n *)
Lemma cofe_bcompl_weakly_unique `{SI : indexT} (A : ofe) (HA : Cofe A) (n: index) Hn (c d : bchain A n):
 (∀ p (Hp : p ≺ n), c p Hp ≡{p}≡ d p Hp) → dist_later n (bcompl Hn c) (bcompl Hn d).
Proof.
  intros H p Hp. unshelve rewrite !conv_bcompl; [assumption | assumption | apply H].
Qed.

(** Limit preserving predicates *)
Class LimitPreserving `{SI: indexT} {A: ofe} `{!Cofe A} (P : A → Prop) : Prop :=
  limit_preserving (c : chain A) : (∀ n, P (c n)) → P (compl c).
Global Hint Mode LimitPreserving - + + ! : typeclass_instances.

Section limit_preserving.
  Context {SI: indexT} {A: ofe}`{!Cofe A}.
  (* These are not instances as they will never fire automatically...
     but they can still be helpful in proving things to be limit preserving. *)

  Lemma limit_preserving_ext (P Q : A → Prop) :
    (∀ x, P x ↔ Q x) → LimitPreserving P → LimitPreserving Q.
  Proof. intros HP Hlimit c ?. apply HP, Hlimit; eauto=> n. by apply HP. Qed.

  Global Instance limit_preserving_const (P : Prop) : LimitPreserving (λ _ : A, P).
  Proof. intros c HP. apply (HP zero). Qed.

  Lemma limit_preserving_discrete (P : A → Prop) :
    Proper (dist zero ==> impl) P → LimitPreserving P.
  Proof. intros PH c HP. by rewrite (conv_compl zero c). Qed.

  Lemma limit_preserving_and (P1 P2 : A → Prop) :
    LimitPreserving P1 → LimitPreserving P2 →
    LimitPreserving (λ x, P1 x ∧ P2 x).
  Proof. intros Hlim1 Hlim2 c HC. split; [apply Hlim1|apply Hlim2]; apply HC. Qed.

  Lemma limit_preserving_impl (P1 P2 : A → Prop) :
    Proper (dist zero ==> impl) P1 → LimitPreserving P2 →
    LimitPreserving (λ x, P1 x → P2 x).
  Proof.
    intros Hlim1 Hlim2 c HP HP1. apply Hlim2; eauto; intros n; apply HP.
    eapply Hlim1, HP1. apply dist_le with n; last eapply index_zero_minimum.
    apply (conv_compl n c); eauto.
  Qed.

  Lemma limit_preserving_forall {B} (P : B → A → Prop) :
    (∀ y, LimitPreserving (P y)) →
    LimitPreserving (λ x, ∀ y, P y x).
  Proof. intros Hlim c Hc y. by apply Hlim. Qed.

  Lemma limit_preserving_equiv `{!Cofe B} (f g : A → B) :
    NonExpansive f → NonExpansive g → LimitPreserving (λ x, f x ≡ g x).
  Proof.
    intros Hf Hg c Hc. apply equiv_dist=> n.
    by rewrite -!compl_chain_map !conv_compl /= Hc.
  Qed.
End limit_preserving.


(** Bounded limit preserving predicates *)
Class BoundedLimitPreserving {SI: indexT} `{!Cofe A} (P : A → Prop) : Prop :=
  bounded_limit_preserving n Hn (c: bchain A n) : (∀ m Hm, P (c m Hm)) → P (lbcompl Hn c).
Global Hint Mode BoundedLimitPreserving - + + ! : typeclass_instances.

Section bounded_limit_preserving.
  Context {SI: indexT} `{!Cofe A}.
  (* These are not instances as they will never fire automatically...
     but they can still be helpful in proving things to be limit preserving. *)

  Lemma bounded_limit_preserving_ext (P Q : A → Prop) :
    (∀ x, P x ↔ Q x) → BoundedLimitPreserving P → BoundedLimitPreserving Q.
  Proof. intros HP Hlimit n Hn c HC. apply HP, Hlimit; eauto=> m Hm. by apply HP. Qed.

  Global Instance bounded_limit_preserving_const (P : Prop) : P → BoundedLimitPreserving (λ _: A, P).
  Proof. intros c HP ?; eauto. Qed.

  Lemma bounded_limit_preserving_bcompl α Hα (c : bchain A α) P:
    BoundedLimitPreserving P →
    (∀ β Hβ, P (c β Hβ)) → P (bcompl Hα c).
  Proof.
    intros Hpres HP. rewrite /bcompl. destruct index_dec_limit as [[β ->] | Hlim]; cbn.
    - apply HP.
    - by apply Hpres.
  Qed.

  Lemma bounded_limit_preserving_and (P1 P2 : A → Prop) :
    BoundedLimitPreserving P1 → BoundedLimitPreserving P2 →
    BoundedLimitPreserving (λ x, P1 x ∧ P2 x).
  Proof. intros Hlim1 Hlim2 n c Hn HC. split; [apply Hlim1 | apply Hlim2]; apply HC. Qed.


  Lemma bounded_limit_preserving_forall {B} (P : B → A → Prop) :
    (∀ y, BoundedLimitPreserving (P y)) →
    BoundedLimitPreserving (λ x, ∀ y, P y x).
  Proof. intros Hlim c ? ? ? y. by apply Hlim. Qed.

  (* TODO: equiv does not seem to be bounded limit preserving*)
End bounded_limit_preserving.


(** Fixpoint *)
Section fixpoint.

  Context {SI: indexT} `{!Cofe A} (f: A → A) `{C: Contractive f} `{In: Inhabited A}.

  Record is_bounded_fixpoint_chain n (ch : ∀ m, m ≺ n → A) := mk_is_bounded_fixpoint_chain
    {
      ch_cauchy  m p (Hm : m ≺ n) (Hp : p ≺ n): m ⪯ p → ch p Hp ≡{m}≡ ch m Hm;
      is_fp : forall Hn, dist_later n (f (bcompl Hn (mkbchain SI A n ch ch_cauchy))) (bcompl Hn (mkbchain SI A n ch ch_cauchy));
    }.

  Definition bounded_fixpoint_chain n := {ch : ∀ m, m ≺ n → A & is_bounded_fixpoint_chain n ch}.
  Program Definition mk_bounded_fixpoint_chain n (ch : bchain A n) (fp : ∀ Hn, dist_later n (f (bcompl Hn ch)) (bcompl Hn ch)) :=
    existT (bchain_car n ch) (mk_is_bounded_fixpoint_chain n (bchain_car n ch) _ _).
  Next Obligation. intros n ch _. apply ch. Defined.
  Next Obligation. intros n ch fp Hn. cbn. apply fp. Defined.

  Definition get_chain n (bfc : bounded_fixpoint_chain n) := mkbchain SI A n (projT1 bfc) (@ch_cauchy n (projT1 bfc) (projT2 bfc)).
  Coercion get_chain : bounded_fixpoint_chain >-> bchain.

  Program Definition cast {n} (c: bounded_fixpoint_chain n) m (Hm: m ⪯ n): bounded_fixpoint_chain m :=
    mk_bounded_fixpoint_chain m (mkbchain SI A m (λ p Hp, projT1 c p _) _) _.
  Next Obligation. intros ??????; eauto using index_lt_le_trans. Qed.
  Next Obligation.
    intros n c m Hm p1 p2 Hp Hp1 Hp2; simpl.
    specialize (bchain_cauchy n c); eauto.
  Qed.
  Next Obligation.
    intros n c m Hm Hn p Hp; simpl. unshelve rewrite !bchain_conv_bcompl; simpl; eauto.
    specialize (@bchain_conv_bcompl SI A _ n ltac:(eauto using index_lt_le_trans) c) as Hx. cbn in Hx. rewrite -Hx.
    eapply is_fp. eauto using index_lt_le_trans.
  Qed.

  Lemma cast_chain n (Hn: zero ≺ n) m (Hm: zero ≺ m) (Hmn: m ⪯ n) (c: bounded_fixpoint_chain n):
      dist_later m (bcompl Hm (cast c m Hmn)) (bcompl Hn c).
  Proof.
    intros p Hp. unshelve rewrite !bchain_conv_bcompl; eauto using index_lt_le_trans.
    simpl. specialize (bchain_cauchy n c); eauto.
  Qed.

  Lemma fp_chain_is_fp n (ch : bounded_fixpoint_chain n) (Hn : zero ≺ n): dist_later n (f (bcompl Hn ch)) (bcompl Hn ch).
  Proof.
    destruct ch as (ch & (cauchy & fp)). apply fp.
  Qed.

  Lemma bounded_fixpoint_chain_unique n (Hn: zero ≺ n) (c: bounded_fixpoint_chain n) m (Hm: zero ≺ m) (Hmn: m ⪯ n) (d: bounded_fixpoint_chain m) :
    dist_later m (bcompl Hn c) (bcompl Hm d).
  Proof using A C SI f.
  revert Hmn d. induction (index_lt_wf m) as [m _ IH]. intros Hmn d p Hp.
  rewrite -(fp_chain_is_fp _ d Hm p Hp). rewrite -(fp_chain_is_fp _ c Hn p _); eauto using index_lt_le_trans.
  destruct (index_is_zero p) as [->|NT].
  - by apply contractive_0.
  - eapply contractive_mono; eauto.
    assert (p ⪯ m) as Hpm by eauto.
    pose (e := cast d p Hpm).
    transitivity (bcompl NT e).
    + eapply IH; eauto using index_lt_le_trans.
    + apply cast_chain.
  Qed.


  Section inductive_step.


    Local Definition patch_base_case {n: index} (g: zero ≺ n → A) : A :=
      match index_is_zero n with
      | left H => inhabitant
      | right NT => g NT
      end.

    Program Definition bfpc : ∀ (n: index), bounded_fixpoint_chain n :=
      index_cumulative_rec (fun _ => A) is_bounded_fixpoint_chain
        (fun n IH => f (patch_base_case (fun NT => bcompl NT (get_chain n IH)))) _.
    Next Obligation.
      intros n G. cbn in *. unshelve econstructor; first last.
      - intros Hn m Hm; simpl. unshelve rewrite bchain_conv_bcompl; simpl; eauto.
        unfold patch_base_case. destruct index_is_zero; subst.
        + by eapply contractive_0.
        + apply contractive_mono; eauto. by eapply is_fp.
      - intros m p Hm Hp Hle. unfold patch_base_case.
        repeat destruct index_is_zero; eauto; subst.
        + destruct Hle; subst; by exfalso; eapply index_lt_zero_is_normal.
        + by eapply contractive_0.
        + apply contractive_mono; eauto. apply bounded_fixpoint_chain_unique, Hle.
    Qed.
  End inductive_step.

  Program Definition fixpoint_chain: chain A := mkchain _ _  (λ n, f (patch_base_case (λ Hn, bcompl Hn (get_chain n (bfpc n))))) _.
  Next Obligation.
    intros m n Hnm; simpl. unfold patch_base_case. repeat destruct index_is_zero; eauto; subst.
    - destruct Hnm; subst; by exfalso; eapply index_lt_zero_is_normal.
    - subst. by eapply contractive_0.
    - apply contractive_mono; eauto. apply bounded_fixpoint_chain_unique; eauto using is_fp.
  Qed.

  Program Definition fixpoint_def  : A := compl fixpoint_chain.
  Definition fixpoint_aux : seal (@fixpoint_def). Proof using Type. by eexists. Qed.
  Definition fixpoint := fixpoint_aux.(unseal).
  Definition fixpoint_eq : @fixpoint = @fixpoint_def := fixpoint_aux.(seal_eq).

  Lemma fixpoint_unfold :
    fixpoint ≡ f (fixpoint).
  Proof.
    apply equiv_dist=>n.
    rewrite fixpoint_eq /fixpoint_def; cbn.
    erewrite !conv_compl. unfold fixpoint_chain; simpl.
    unfold patch_base_case; destruct index_is_zero; subst.
    - by apply contractive_0.
    - eapply contractive_mono; eauto. symmetry. eapply is_fp.
  Qed.

End fixpoint.

Section fixpoint.
  Context {SI: indexT} `{!Cofe A} (f : A → A) `{!Contractive f} `{Inhabited A}.

  Lemma fixpoint_unique (x : A) : x ≡ f x → x ≡ fixpoint f.
  Proof.
    rewrite !equiv_dist=> Hx n. induction (index_lt_wf n) as [n _ IH].
    rewrite Hx fixpoint_unfold. eapply contractive_mono; eauto.
  Qed.

  Lemma fixpoint_ne (g : A → A) `{!Contractive g} n :
    (∀ z, f z ≡{n}≡ g z) → fixpoint f ≡{n}≡ fixpoint g.
  Proof.
    intros Hfg. induction (index_lt_wf n) as [n _ IH].
    do 2 (rewrite fixpoint_unfold; symmetry). etransitivity; last by eapply Hfg.
    eapply contractive_mono; eauto.
    intros ??; eapply IH; eauto.
    intros; eapply dist_le', Hfg; eauto.
  Qed.
  Lemma fixpoint_proper (g : A → A) `{!Contractive g} :
    (∀ x, f x ≡ g x) → fixpoint f ≡ fixpoint g.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_ne. Qed.

  Lemma fixpoint_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) →
    (∀ x, P x → P (f x)) →
    LimitPreserving P →
    BoundedLimitPreserving P →
    P (fixpoint f).
  Proof.
    intros Pr [x Hx] Hincr Hlim Hblim.
    eapply Pr.
    { eapply fixpoint_unique, (@fixpoint_unfold SI A _ f _ {| inhabitant := x |}). }
    rewrite fixpoint_eq /fixpoint_def.
    eapply Hlim. intros m; simpl.
    apply Hincr.
    rewrite /bfpc. apply index_cumulative_rec_unfold.
    intros p succs H1.
    unfold patch_base_case at 1. destruct index_is_zero; subst.
    - apply Hx.
    - apply bounded_limit_preserving_bcompl; first by eapply Hblim.
      intros. rewrite index_cumulative_rec_dep_step; cbn. apply Hincr, H1.
  Qed.
End fixpoint.
Global Arguments fixpoint {_ A _} f {_ _}.


(** Fixpoint of f when f^k is contractive. **)
Definition fixpointK `{SI: indexT} {A: ofe} `{!Cofe A, Inhabited A} k (f : A → A)
  `{!Contractive (Nat.iter k f)} := fixpoint (Nat.iter k f).

Section fixpointK.
  Local Set Default Proof Using "Type*".
  Context `{SI: indexT} {A: ofe} `{!Cofe A, Inhabited A} (f : A → A) (k : nat).
  Context {f_contractive : Contractive (Nat.iter k f)} {f_ne : NonExpansive f}.
  (* Note than f_ne is crucial here:  there are functions f such that f^2 is contractive,
     but f is not non-expansive.
     Consider for example f: SPred → SPred (where SPred is "downclosed sets of natural numbers").
     Define f (using informative excluded middle) as follows:
     f(N) = N  (where N is the set of all natural numbers)
     f({0, ..., n}) = {0, ... n-1}  if n is even (so n-1 is at least -1, in which case we return the empty set)
     f({0, ..., n}) = {0, ..., n+2} if n is odd
     In other words, if we consider elements of SPred as ordinals, then we decreaste odd finite
     ordinals by 1 and increase even finite ordinals by 2.
     f is not non-expansive:  Consider f({0}) = ∅ and f({0,1}) = f({0,1,2,3}).
     The arguments are clearly 0-equal, but the results are not.

     Now consider g := f^2. We have
     g(N) = N
     g({0, ..., n}) = {0, ... n+1}  if n is even
     g({0, ..., n}) = {0, ..., n+4} if n is odd
     g is contractive.  All outputs contain 0, so they are all 0-equal.
     Now consider two n-equal inputs. We have to show that the outputs are n+1-equal.
     Either they both do not contain n in which case they have to be fully equal and
     hence so are the results.  Or else they both contain n, so the results will
     both contain n+1, so the results are n+1-equal.
   *)

  Let f_proper : Proper ((≡) ==> (≡)) f := ne_proper f.
  Local Existing Instance f_proper.

  Lemma fixpointK_unfold : fixpointK k f ≡ f (fixpointK k f).
  Proof.
    symmetry. rewrite /fixpointK. apply fixpoint_unique.
    by rewrite -Nat.iter_succ_r Nat.iter_succ -fixpoint_unfold.
  Qed.

  Lemma fixpointK_unique (x : A) : x ≡ f x → x ≡ fixpointK k f.
  Proof.
    intros Hf. apply fixpoint_unique. clear f_contractive.
    induction k as [|k' IH]=> //=. by rewrite -IH.
  Qed.

  Section fixpointK_ne.
    Context (g : A → A) `{g_contractive : !Contractive (Nat.iter k g)}.
    Context {g_ne : NonExpansive g}.

    Lemma fixpointK_ne n : (∀ z, f z ≡{n}≡ g z) → fixpointK k f ≡{n}≡ fixpointK k g.
    Proof.
      rewrite /fixpointK=> Hfg /=. apply fixpoint_ne=> z.
      clear f_contractive g_contractive.
      induction k as [|k' IH]=> //=. by rewrite IH Hfg.
    Qed.

    Lemma fixpointK_proper : (∀ z, f z ≡ g z) → fixpointK k f ≡ fixpointK k g.
    Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpointK_ne. Qed.
  End fixpointK_ne.

  Lemma fixpointK_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) → (∀ x, P x → P (f x)) →
    LimitPreserving P →
    BoundedLimitPreserving P →
    P (fixpointK k f).
  Proof.
    intros. rewrite /fixpointK. apply fixpoint_ind; eauto.
    intros; apply Nat.iter_ind; auto.
  Qed.
End fixpointK.

(** Mutual fixpoints *)
Section fixpointAB.
  Context `{SI: indexT} {A B: ofe}`{!Cofe A, !Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA : A → B → A).
  Context (fB : A → B → B).
  Context {fA_contractive : ∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context {fB_contractive : ∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.

  Local Definition fixpoint_AB (x : A) : B := fixpoint (fB x).
  Local Instance fixpoint_AB_contractive : Contractive fixpoint_AB.
  Proof.
    intros n x x' Hx; rewrite /fixpoint_AB.
    apply fixpoint_ne=> y. solve_contractive.
  Qed.

  Local Definition fixpoint_AA (x : A) : A := fA x (fixpoint_AB x).
  Local Instance fixpoint_AA_contractive : Contractive fixpoint_AA.
  Proof using fA_contractive. solve_contractive. Qed.

  Definition fixpoint_A : A := fixpoint fixpoint_AA.
  Definition fixpoint_B : B := fixpoint_AB fixpoint_A.

  Lemma fixpoint_A_unfold : fA fixpoint_A fixpoint_B ≡ fixpoint_A.
  Proof. by rewrite {2}/fixpoint_A (fixpoint_unfold _). Qed.
  Lemma fixpoint_B_unfold : fB fixpoint_A fixpoint_B ≡ fixpoint_B.
  Proof. by rewrite {2}/fixpoint_B /fixpoint_AB (fixpoint_unfold _). Qed.

  Local Instance: Proper ((≡) ==> (≡) ==> (≡)) fA.
  Proof using fA_contractive.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; eauto using dist_dist_later.
  Qed.
  Local Instance: Proper ((≡) ==> (≡) ==> (≡)) fB.
  Proof using fB_contractive.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; auto using dist_dist_later.
  Qed.

  Lemma fixpoint_A_unique p q : fA p q ≡ p → fB p q ≡ q → p ≡ fixpoint_A.
  Proof.
    intros HfA HfB. rewrite -HfA. apply fixpoint_unique. rewrite /fixpoint_AA.
    f_equiv=> //. apply fixpoint_unique. by rewrite HfA HfB.
  Qed.
  Lemma fixpoint_B_unique p q : fA p q ≡ p → fB p q ≡ q → q ≡ fixpoint_B.
  Proof. intros. apply fixpoint_unique. by rewrite -fixpoint_A_unique. Qed.
End fixpointAB.

Section fixpointAB_ne.
  Context `{SI: indexT} {A B: ofe} `{!Cofe A, !Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA fA' : A → B → A).
  Context (fB fB' : A → B → B).
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA'}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB'}.

  Lemma fixpoint_A_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_A fA fB ≡{n}≡ fixpoint_A fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z.
    rewrite /fixpoint_AA /fixpoint_AB HfA. f_equiv. by apply fixpoint_ne.
  Qed.
  Lemma fixpoint_B_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_B fA fB ≡{n}≡ fixpoint_B fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z. rewrite HfB. f_contractive.
    eapply dist_dist_later, fixpoint_A_ne; auto.
  Qed.

  Lemma fixpoint_A_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_A fA fB ≡ fixpoint_A fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_A_ne. Qed.
  Lemma fixpoint_B_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_B fA fB ≡ fixpoint_B fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_B_ne. Qed.
End fixpointAB_ne.

(** Non-expansive function space *)
Record ofe_mor `{SI: indexT} (A B : ofe) : Type := OfeMor {
  ofe_mor_car :> A → B;
  ofe_mor_ne : NonExpansive ofe_mor_car
}.
Global Arguments OfeMor {_ _ _} _ {_}.
Add Printing Constructor ofe_mor.
Global Existing Instance ofe_mor_ne.

Notation "'λne' x .. y , t" :=
  (@OfeMor _ _ _ (λ x, .. (@OfeMor _ _ _ (λ y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).

Section ofe_mor.
  Context `{SI: indexT} {A B : ofe}.
  Global Instance ofe_mor_proper (f : ofe_mor A B) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper, ofe_mor_ne. Qed.
  Local Instance ofe_mor_equiv : Equiv (ofe_mor A B) := λ f g, ∀ x, f x ≡ g x.
  Local Instance ofe_mor_dist : Dist (ofe_mor A B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition ofe_mor_ofe_mixin : OfeMixin (ofe_mor A B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - intros n m f g ? x ?; by eapply dist_mono.
  Qed.
  Canonical Structure ofe_morO := Ofe (ofe_mor A B) ofe_mor_ofe_mixin.

  Program Definition ofe_mor_chain (c : chain ofe_morO)
    (x : A) : chain B := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Definition ofe_mor_compl `{!Cofe B} : chain ofe_morO → ofe_morO := λ c,
    {| ofe_mor_car x := compl (ofe_mor_chain c x) |}.
  Next Obligation.
    intros ? c n x y Hx. by rewrite (conv_compl n (ofe_mor_chain c x))
      (conv_compl n (ofe_mor_chain c y)) /= Hx.
  Qed.

  Program Definition ofe_mor_bchain {n} (c : bchain ofe_morO n) (x : A) : bchain B n :=
    {| bchain_car n Hn := c n Hn x |}.
  Next Obligation. intros n c x m Hm i ??. by apply (bchain_cauchy n c). Qed.
  Program Definition ofe_mor_lbcompl `{!Cofe B} n : index_is_proper_limit n → bchain ofe_morO n → ofe_morO := λ Hn c,
    {| ofe_mor_car x := lbcompl Hn (ofe_mor_bchain c x) |}.
  Next Obligation.
    intros ? n Hn c m x y Hx. eapply lbcompl_ne.
    by intros; unfold ofe_mor_bchain; simpl; rewrite Hx.
  Qed.


  Global Program Instance ofe_mor_cofe `{!Cofe B} : Cofe  ofe_morO :=
    {| compl := ofe_mor_compl; lbcompl := ofe_mor_lbcompl |}.
  Next Obligation.
    intros ? n c x; cbn. rewrite conv_compl //=.
  Qed.
  Next Obligation.
    intros ? n c m Hm H x; cbn. rewrite (conv_lbcompl n) //=.
  Qed.
  Next Obligation.
    move=> ? n Hn c d m Heq x //=. eapply lbcompl_ne.
    intros p Hp; eapply Heq.
  Qed.

  Global Instance ofe_mor_car_ne :
    NonExpansive2 (@ofe_mor_car SI A B).
  Proof. intros n f g Hfg x y Hx; rewrite Hx; apply Hfg. Qed.
  Global Instance ofe_mor_car_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@ofe_mor_car SI A B) := ne_proper_2 _.
  Lemma ofe_mor_ext (f g : ofe_mor A B) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.
End ofe_mor.

Global Arguments ofe_morO {_} _ _.
Notation "A -n> B" :=
  (ofe_morO A B) (at level 99, B at level 200, right associativity).
Global Instance ofe_mor_inhabited `{SI: indexT} {A B : ofe} `{Inhabited B} :
  Inhabited (A -n> B) := populate (λne _, inhabitant).

(** Identity and composition and constant function *)
Definition cid `{SI: indexT} {A: ofe} : A -n> A := OfeMor id.
Global Instance: Params (@cid) 2 := {}.
Definition cconst `{SI: indexT} {A B : ofe} (x : B) : A -n> B := OfeMor (const x).
Global Instance: Params (@cconst) 3 := {}.

Definition ccompose `{SI: indexT} {A B C: ofe}
  (f : B -n> C) (g : A -n> B) : A -n> C := OfeMor (f ∘ g).
Global Instance: Params (@ccompose) 4 := {}.

Infix "◎" := ccompose (at level 40, left associativity).
Global Instance ccompose_ne `{SI: indexT} {A B C: ofe} :
  NonExpansive2 (@ccompose SI A B C).
Proof. intros n ?? Hf g1 g2 Hg x. rewrite /= (Hg x) (Hf (g2 x)) //. Qed.

Lemma ccompose_assoc `{SI : indexT} {A B C D : ofe} (f : C -n> D) (g : B -n> C) (h : A -n> B) :
  (f ◎ g) ◎ h ≡ f ◎ (g ◎ h).
Proof. intros x. by cbn. Qed.

Lemma ccompose_cid_l `{SI : indexT} {A B : ofe} (f : A -n> B ) : cid ◎ f ≡ f.
Proof. intros x. by cbn. Qed.

Lemma ccompose_cid_r `{SI : indexT} {A B : ofe} (f : A -n> B ) :  f ◎ cid ≡ f.
Proof. intros x. by cbn. Qed.

(* Function space maps *)
Definition ofe_mor_map `{SI: indexT} {A A' B B': ofe} (f : A' -n> A) (g : B -n> B')
  (h : A -n> B) : A' -n> B' := g ◎ h ◎ f.
Global Instance ofe_mor_map_ne SI {A A' B B': ofe} n :
  Proper (dist n ==> dist n ==> dist n ==> dist n) (@ofe_mor_map SI A A' B B').
Proof. intros ??? ??? ???. by repeat apply ccompose_ne. Qed.

Definition ofe_morO_map `{SI: indexT} {A A' B B': ofe} (f : A' -n> A) (g : B -n> B') :
  (A -n> B) -n> (A' -n>  B') := OfeMor (ofe_mor_map f g).
Global Instance ofe_morO_map_ne `{SI: indexT} {A A' B B': ofe} :
  NonExpansive2 (@ofe_morO_map SI A A' B B').
Proof.
  intros n f f' Hf g g' Hg ?. rewrite /= /ofe_mor_map.
  by repeat apply ccompose_ne.
Qed.

(** * Unit type *)
Section unit.
  Context `{SI: indexT}.
  Local Instance unit_dist : Dist unit := λ _ _ _, True.
  Definition unit_ofe_mixin : OfeMixin unit.
  Proof. by repeat split. Qed.
  Canonical Structure unitO : ofe := Ofe unit unit_ofe_mixin.

  Global Program Instance unit_cofe : Cofe unitO := { compl x := () }.
  Solve All Obligations with by repeat split.

  Global Instance unit_ofe_discrete : OfeDiscrete unitO.
  Proof. done. Qed.
End unit.

(** * Empty type *)
Section empty.
  Context `{SI: indexT}.
  Local Instance Empty_set_dist : Dist Empty_set := λ _ _ _, True.
  Definition Empty_set_ofe_mixin : OfeMixin Empty_set.
  Proof. by repeat split; try exists zero. Qed.
  Canonical Structure Empty_setO : ofe := Ofe Empty_set Empty_set_ofe_mixin.

  Global Program Instance Empty_set_cofe : Cofe Empty_setO :=
    { compl x := x zero; lbcompl n Hn c := c zero (proper_limit_not_zero Hn) }.
  Solve All Obligations with by repeat split.

  Global Instance Empty_set_ofe_discrete : OfeDiscrete Empty_setO.
  Proof. done. Qed.
End empty.

(** * Product type *)
Section product.
  Context `{SI: indexT} {A B : ofe}.

  Local Instance prod_dist : Dist (A * B) := λ n, prod_relation (dist n) (dist n).
  Global Instance pair_ne :
    NonExpansive2 (@pair A B) := _.
  Global Instance fst_ne : NonExpansive (@fst A B) := _.
  Global Instance snd_ne : NonExpansive (@snd A B) := _.
  Definition prod_ofe_mixin : OfeMixin (A * B).
  Proof.
    split.
    - intros x y; unfold dist, prod_dist, equiv, prod_equiv, prod_relation.
      rewrite !equiv_dist; naive_solver.
    - apply _.
    - by intros n m [x1 y1] [x2 y2] [??]; split; eapply dist_mono.
  Qed.
  Canonical Structure prodO : ofe := Ofe (A * B) prod_ofe_mixin.

  Global Program Instance prod_cofe `{!Cofe A, !Cofe B} : Cofe prodO :=
    { compl c := (compl (chain_map fst c), compl (chain_map snd c));
      lbcompl n Hn c := (lbcompl Hn (bchain_map fst c), lbcompl Hn (bchain_map snd c)) }.
  Next Obligation.
    repeat split; cbn; by rewrite conv_compl.
  Qed.
  Next Obligation.
    repeat split; cbn; by rewrite conv_lbcompl; simpl.
  Qed.
  Next Obligation.
    intros; cbn; split; cbn; eapply lbcompl_ne; intros; simpl; f_equiv; eauto.
  Qed.

  Global Instance prod_discrete (x : A * B) :
    Discrete (x.1) → Discrete (x.2) → Discrete x.
  Proof. by intros ???[??]; split; apply (discrete _). Qed.
  Global Instance prod_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete prodO.
  Proof. intros ?? [??]; apply _. Qed.
End product.

Global Arguments prodO {_} _ _.
Global Typeclasses Opaque prod_dist.

Global Instance prod_map_ne `{SI: indexT} {A A' B B' : ofe} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@prod_map A A' B B').
Proof. by intros f f' Hf g g' Hg ?? [??]; split; [apply Hf|apply Hg]. Qed.
Definition prodO_map `{SI: indexT} {A A' B B': ofe} (f : A -n> A') (g : B -n> B') :
  prodO A B -n> prodO A' B' := OfeMor (prod_map f g).
Global Instance prodO_map_ne `{SI: indexT} {A A' B B': ofe} :
  NonExpansive2 (@prodO_map SI A A' B B').
Proof. intros n f f' Hf g g' Hg [??]; split; [apply Hf|apply Hg]. Qed.

(** * OFE → OFE Functors *)
Record oFunctor `{SI: indexT} := OFunctor {
  oFunctor_car : ∀ A B, ofe;
  oFunctor_map  {A1 A2 B1 B2}:
    ((A2 -n> A1) * (B1 -n> B2)) → oFunctor_car A1 B1 -n> oFunctor_car A2 B2;
  oFunctor_map_ne {A1 A2 B1 B2}:
    NonExpansive (@oFunctor_map A1 A2 B1 B2);
  oFunctor_map_id {A B} (x : oFunctor_car A B) :
    oFunctor_map (cid,cid) x ≡ x;
  oFunctor_map_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    oFunctor_map (f◎g, g'◎f') x ≡ oFunctor_map (g,g') (oFunctor_map (f,f') x)
}.
Global Existing Instance oFunctor_map_ne.
Global Instance: Params (@oFunctor_map) 6 := {}.

Declare Scope oFunctor_scope.
Delimit Scope oFunctor_scope with OF.
Bind Scope oFunctor_scope with oFunctor.

Class oFunctorContractive `{SI: indexT} (F : oFunctor) :=
  oFunctor_map_contractive `{A1 : ofe} `{A2 : ofe} `{B1 : ofe} `{B2 : ofe} :>
    Contractive  (@oFunctor_map SI F A1 A2 B1 B2).
Global Hint Mode oFunctorContractive - ! : typeclass_instances.

(** We add the coercion because there is no more Cofe argument *)
Definition oFunctor_apply `{SI: indexT} (F: oFunctor) (A: ofe) : ofe := oFunctor_car F A A.
Coercion oFunctor_apply : oFunctor >-> Funclass.

Program Definition constOF `{SI: indexT} (B : ofe) : oFunctor :=
  {| oFunctor_car A1 A2 := B; oFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion constOF : ofe >-> oFunctor.

Global Instance constOF_contractive `{SI: indexT} B : oFunctorContractive (constOF B).
Proof. rewrite /oFunctorContractive; apply _. Qed.

Program Definition idOF `{SI: indexT} : oFunctor :=
  {| oFunctor_car A1 A2 := A2; oFunctor_map A1 A2 B1 B2 f := f.2 |}.
Solve Obligations with done.
Notation "∙" := idOF : oFunctor_scope.

Program Definition prodOF `{SI: indexT} (F1 F2 : oFunctor) : oFunctor := {|
  oFunctor_car A B := prodO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map A1 A2 B1 B2 fg :=
    prodO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros SI ?? A1 A2 B1 B2 n ???; by apply prodO_map_ne; apply oFunctor_map_ne.
Qed.
Next Obligation. by intros SI F1 F2 A B [??]; rewrite /= !oFunctor_map_id. Qed.
Next Obligation.
  intros SI F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !oFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodOF F1%OF F2%OF) : oFunctor_scope.

Global Instance prodOF_contractive `{SI: indexT} {F1 F2 : ofe}:
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (prodOF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply prodO_map_ne; apply oFunctor_map_contractive.
Qed.

Program Definition ofe_morOF `{SI: indexT} (F1 F2 : oFunctor) : oFunctor := {|
  oFunctor_car A B := oFunctor_car F1 B A -n> oFunctor_car F2 A B;
  oFunctor_map A1 A2 B1 B2 fg :=
    ofe_morO_map (oFunctor_map F1 (fg.2, fg.1)) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros SI F1 F2 A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply oFunctor_map_ne; split; by apply Hfg.
Qed.
Next Obligation.
  intros SI F1 F2 A B [f ?] ?; simpl. rewrite /= !oFunctor_map_id.
  apply (ne_proper f). apply oFunctor_map_id.
Qed.
Next Obligation.
  intros SI F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [h ?] ?; simpl in *.
  rewrite -!oFunctor_map_compose. do 2 apply (ne_proper _). apply oFunctor_map_compose.
Qed.
Notation "F1 -n> F2" := (ofe_morOF F1%OF F2%OF) : oFunctor_scope.

Global Instance ofe_morOF_Contractive `{SI: indexT}  (F1 F2 : oFunctor):
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (ofe_morOF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply oFunctor_map_contractive; unfold dist_later; intros; split; cbn; eauto.
  all: destruct (Hfg m); auto.
Qed.

(** * Sum type *)
Section sum.
  Context `{SI: indexT} {A B : ofe}.

  Local Instance sum_dist : Dist (A + B) := λ n, sum_relation (dist n) (dist n).
  Global Instance inl_ne : NonExpansive (@inl A B) := _.
  Global Instance inr_ne : NonExpansive (@inr A B) := _.
  Global Instance inl_ne_inj n : Inj (dist n) (dist n) (@inl A B) := _.
  Global Instance inr_ne_inj n : Inj (dist n) (dist n) (@inr A B) := _.

  Definition sum_ofe_mixin : OfeMixin (A + B).
  Proof.
    split.
    - intros x y; split=> Hx.
      + destruct Hx=> n; constructor; by apply equiv_dist.
      + destruct (Hx zero); constructor; apply equiv_dist=> n; by apply (inj _).
    - apply _.
    - destruct 1; constructor; eapply dist_mono; eauto.
  Qed.

  Canonical Structure sumO : ofe := Ofe (A + B) sum_ofe_mixin.

  Program Definition inl_chain (c : chain sumO) (a : A) : chain A :=
    {| chain_car n := match c n return _ with inl a' => a' | _ => a end |}.
  Next Obligation. intros c a n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Program Definition inr_chain (c : chain sumO) (b : B) : chain B :=
    {| chain_car n := match c n return _ with inr b' => b' | _ => b end |}.
  Next Obligation. intros c b n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Definition sum_compl `{!Cofe A, !Cofe B} : chain sumO → sumO := λ c,
    match c zero with
    | inl a => inl (compl (inl_chain c a))
    | inr b => inr (compl (inr_chain c b))
    end.

  Program Definition inl_bchain {n} (c : bchain sumO n) (a : A) : bchain A n :=
    {| bchain_car n Hn := match c n Hn return _ with inl a' => a' | _ => a end |}.
  Next Obligation. intros n c a m p Hm Hp Hmp; simpl. by destruct (bchain_cauchy n c m p Hm Hp Hmp). Qed.
  Program Definition inr_bchain {n} (c : bchain sumO n) (b : B) : bchain B n :=
    {| bchain_car n Hn := match c n Hn return _ with inr b' => b' | _ => b end |}.
  Next Obligation. intros n c b m p Hm Hp Hmp; simpl. by destruct (bchain_cauchy n c m p Hm Hp Hmp). Qed.
  Definition sum_lbcompl `{!Cofe A, !Cofe B} n : index_is_proper_limit n → bchain sumO n → sumO :=
    λ Hn c,
    match c zero (proper_limit_not_zero Hn) with
    | inl a => inl (lbcompl Hn (inl_bchain c a))
    | inr b => inr (lbcompl Hn (inr_bchain c b))
    end.

  Global Program Instance sum_cofe `{!Cofe A, !Cofe B} : Cofe  sumO :=
    { compl := sum_compl; lbcompl := sum_lbcompl }.
  Next Obligation.
    intros ?? n c; rewrite /compl /sum_compl.
    feed inversion (chain_cauchy c zero n).
    - apply index_zero_minimum.
    - rewrite (conv_compl n (inl_chain c _)) /=. destruct (c n); naive_solver.
    - rewrite (conv_compl n (inr_chain c _)) /=. destruct (c n); naive_solver.
  Qed.
  Next Obligation.
    intros ?? n Hn c m Hm. rewrite /sum_lbcompl.
    feed inversion (bchain_cauchy n c zero m (proper_limit_not_zero Hn) Hm).
    - apply index_zero_minimum.
    - rewrite (conv_lbcompl n _ _ _ Hm) /=. destruct (c m _); naive_solver.
    - rewrite (conv_lbcompl n _ _ _ Hm) /=. destruct (c m _); naive_solver.
  Qed.
  Next Obligation.
    intros ?????? m H1. unfold sum_lbcompl.
    destruct (H1 zero (proper_limit_not_zero Hn)); simpl; rewrite lbcompl_ne; eauto.
    all: intros p Hp; simpl; destruct (H1 p Hp); eauto.
  Qed.

  Global Instance inl_discrete (x : A) : Discrete x → Discrete (inl x).
  Proof. inversion_clear 2; constructor; by apply (discrete _). Qed.
  Global Instance inr_discrete (y : B) : Discrete y → Discrete (inr y).
  Proof. inversion_clear 2; constructor; by apply (discrete _). Qed.
  Global Instance sum_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete sumO.
  Proof. intros ?? [?|?]; apply _. Qed.
End sum.

Global Arguments sumO {_} _ _.
Global Typeclasses Opaque sum_dist.

Global Instance sum_map_ne `{SI: indexT} {A A' B B' : ofe} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@sum_map A A' B B').
Proof.
  intros f f' Hf g g' Hg ??; destruct 1; constructor; [by apply Hf|by apply Hg].
Qed.
Definition sumO_map `{SI: indexT} {A A' B B': ofe} (f : A -n> A') (g : B -n> B') :
  sumO A B -n> sumO A' B' := OfeMor (sum_map f g).
Global Instance sumO_map_ne `{SI: indexT} {A A' B B'} :
  NonExpansive2 (@sumO_map SI A A' B B').
Proof. intros n f f' Hf g g' Hg [?|?]; constructor; [apply Hf|apply Hg]. Qed.

Program Definition sumOF `{SI: indexT} (F1 F2 : oFunctor) : oFunctor := {|
  oFunctor_car A B := sumO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map A1 A2 B1 B2 fg :=
    sumO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros ??? A1 A2 B1 B2 n ???; by apply sumO_map_ne; apply oFunctor_map_ne.
Qed.
Next Obligation. by intros ? F1 F2 A B [?|?]; rewrite /= !oFunctor_map_id. Qed.
Next Obligation.
  intros ? F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [?|?]; simpl;
    by rewrite !oFunctor_map_compose.
Qed.
Notation "F1 + F2" := (sumOF F1%OF F2%OF) : oFunctor_scope.

Global Instance sumOF_contractive `{SI: indexT} (F1 F2 : oFunctor):
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (sumOF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply sumO_map_ne; apply oFunctor_map_contractive.
Qed.

(** * Discrete OFEs *)
Section discrete_ofe.
  Context `{SI: indexT} {A: Type} `{Equiv A} (Heq : @Equivalence A (≡)).

  Local Instance discrete_dist : Dist A := λ n x y, x ≡ y.
  Definition discrete_ofe_mixin : OfeMixin A.
  Proof using Type*.
    split.
    - intros x y; split; [done|intros Hn; apply (Hn zero)].
    - done.
    - done.
  Qed.

  Global Instance discrete_ofe_discrete : OfeDiscrete (Ofe A discrete_ofe_mixin).
  Proof. by intros x y. Qed.

  Global Program Instance discrete_cofe : Cofe (Ofe A discrete_ofe_mixin) :=
    { compl c := c zero;
      lbcompl n Hn c := c zero (proper_limit_not_zero Hn)
    }.
  Next Obligation.
    intros n c; simpl.
    symmetry; apply (chain_cauchy c zero n).
    eapply index_zero_minimum.
  Qed.
  Next Obligation.
    intros n Hn c; simpl.
    symmetry; apply (bchain_cauchy n c zero m).
    eapply index_zero_minimum.
  Qed.
  Next Obligation.
    intros; simpl; eauto.
  Qed.

End discrete_ofe.

Notation discreteO A := (Ofe A (discrete_ofe_mixin _)).
(** Force the [Equivalence] proof to be [eq_equivalence] so that it does not
find another one, like [ofe_equivalence], in the case of aliases. See also
https://gitlab.mpi-sws.org/iris/iris/issues/299 *)
Notation leibnizO A := (Ofe A (@discrete_ofe_mixin _ _ equivL eq_equivalence)).

(** In order to define a discrete CMRA with carrier [A] (in the file [cmra.v])
we need to determine the [Equivalence A] proof that was used to construct the
OFE instance of [A] (note that this proof is not the same as the one we obtain
via [ofe_equivalence]).

We obtain the proof of [Equivalence A] by inferring the canonical OFE mixin
using [ofe_mixin_of A], and then check whether it is indeed a discrete OFE. This
will fail if no OFE, or an OFE other than the discrete OFE, was registered. *)
Notation discrete_ofe_equivalence_of A := ltac:(
  match constr:(ofe_mixin_of A) with
  | discrete_ofe_mixin ?H => exact H
  end) (only parsing).

Global Instance leibnizO_leibniz A `{SI: indexT} : LeibnizEquiv (leibnizO A).
Proof. by intros x y. Qed.

(** * Basic Coq types *)
Canonical Structure boolO `{SI: indexT} : ofe := leibnizO bool.
Canonical Structure natO `{SI: indexT} : ofe := leibnizO nat.
Canonical Structure positiveO `{SI: indexT} : ofe := leibnizO positive.
Canonical Structure NO `{SI: indexT} : ofe := leibnizO N.
Canonical Structure ZO `{SI: indexT} : ofe := leibnizO Z.

Section prop.
  Context `{SI: indexT}.

  Local Instance Prop_equiv : Equiv Prop := iff.
  Local Instance Prop_equivalence : Equivalence (≡@{Prop}) := _.
  Canonical Structure PropO := discreteO Prop.
End prop.

(** * Option type *)
Section option.
  Context `{SI: indexT} {A : ofe}.

  Local Instance option_dist : Dist (option A) := λ n, option_Forall2 (dist n).
  Lemma dist_option_Forall2 n mx my : mx ≡{n}≡ my ↔ option_Forall2 (dist n) mx my.
  Proof. done. Qed.

  Definition option_ofe_mixin : OfeMixin (option A).
  Proof.
    split.
    - intros mx my; split; [by destruct 1; constructor; apply equiv_dist|].
      intros Hxy; destruct (Hxy zero); constructor; apply equiv_dist.
      by intros n; feed inversion (Hxy n).
    - apply _.
    - destruct 1; constructor; eapply dist_le; eauto.
  Qed.
  Canonical Structure optionO := Ofe (option A) option_ofe_mixin.


  Global Instance Some_ne : NonExpansive (@Some A).
  Proof. intros ????. by econstructor. Qed.
  Global Instance Some_dist_inj n : Inj (dist n) (dist n) (@Some A).
  Proof. by inversion_clear 1. Qed.

  Program Definition option_chain (c : chain optionO) (x : A) : chain A :=
    {| chain_car n := default x (c n) |}.
  Next Obligation. intros c x n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Definition option_compl `{!Cofe A} : (chain optionO) → optionO := λ c,
    match c zero with Some x => Some (compl (option_chain c x)) | None => None end.

  Program Definition option_bchain n (c : bchain optionO n) (x : A) : bchain A n :=
    {| bchain_car n Hn := default x (c n Hn) |}.
  Next Obligation. intros n c x m p Hm Hp Hmp; simpl. by destruct (bchain_cauchy n c m p Hm Hp Hmp). Qed.
  Definition option_lbcompl `{!Cofe A} n (Hn: index_is_proper_limit n): (bchain optionO n) → optionO := λ c,
    match c zero (proper_limit_not_zero Hn) with
    | Some x => Some (lbcompl Hn (option_bchain n c x))
    | None => None
    end.

  Global Program Instance option_cofe `{!Cofe A} : Cofe optionO :=
    { compl := option_compl; lbcompl := option_lbcompl }.
  Next Obligation.
    intros ? n c; rewrite /compl /option_compl.
    feed inversion (chain_cauchy c zero n); auto using index_zero_minimum.
    constructor. rewrite (conv_compl n (option_chain c _)) /=.
    destruct (c n); naive_solver.
  Qed.
  Next Obligation.
    intros ? n Hn c m Hm; rewrite /lbcompl /option_lbcompl.
    feed inversion (bchain_cauchy n c zero m (proper_limit_not_zero Hn) Hm); auto using index_zero_minimum.
    constructor. unshelve rewrite conv_lbcompl; eauto; simpl.
    destruct (c m Hm); naive_solver.
  Qed.
  Next Obligation.
    intros ? n Hn c d m Hc; rewrite /lbcompl /option_lbcompl.
    destruct (Hc zero (proper_limit_not_zero Hn)); auto. rewrite lbcompl_ne; eauto.
    intros p Hp; simpl. destruct (Hc p Hp); eauto.
  Qed.

  Global Instance option_ofe_discrete : OfeDiscrete A → OfeDiscrete optionO.
  Proof. destruct 2; constructor; by apply (discrete _). Qed.

  Global Instance is_Some_ne n : Proper (dist n ==> iff) (@is_Some A).
  Proof. destruct 1; split; eauto. Qed.
  Global Instance from_option_ne {B} (R : relation B) n :
    Proper ((dist (A:=A) n ==> R) ==> R ==> dist n ==> R) from_option.
  Proof. destruct 3; simpl; auto. Qed.

  Global Instance None_discrete : Discrete (@None A).
  Proof. inversion_clear 1; constructor. Qed.
  Global Instance Some_discrete x : Discrete x → Discrete (Some x).
  Proof. by intros ?; inversion_clear 1; constructor; apply discrete. Qed.

  Lemma dist_None n mx : mx ≡{n}≡ None ↔ mx = None.
  Proof. split; [by inversion_clear 1|by intros ->]. Qed.
  Lemma dist_Some n x y : Some x ≡{n}≡ Some y ↔ x ≡{n}≡ y.
  Proof. split; [by inversion_clear 1 | by intros ->]. Qed.
  Lemma dist_Some_inv_l n mx my x :
    mx ≡{n}≡ my → mx = Some x → ∃ y, my = Some y ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_r n mx my y :
    mx ≡{n}≡ my → my = Some y → ∃ x, mx = Some x ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_l' n my x : Some x ≡{n}≡ my → ∃ x', Some x' = my ∧ x ≡{n}≡ x'.
  Proof. intros ?%(dist_Some_inv_l _ _ _ x); naive_solver. Qed.
  Lemma dist_Some_inv_r' n mx y : mx ≡{n}≡ Some y → ∃ y', mx = Some y' ∧ y ≡{n}≡ y'.
  Proof. intros ?%(dist_Some_inv_r _ _ _ y); naive_solver. Qed.
End option.

Global Typeclasses Opaque option_dist.
Global Arguments optionO {_} _.

Global Instance option_fmap_ne `{SI: indexT} {A B : ofe} n:
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@fmap option _ A B).
Proof. intros f f' Hf ?? []; constructor; auto. Qed.
Global Instance option_mbind_ne `{SI: indexT} {A B : ofe} n:
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@mbind option _ A B).
Proof. destruct 2; simpl; auto. Qed.
Global Instance option_mjoin_ne `{SI: indexT} {A : ofe} n:
  Proper (dist n ==> dist n) (@mjoin option _ A).
Proof. destruct 1 as [?? []|]; simpl; by constructor. Qed.

(* TODO: why is this here *)
Lemma fmap_Some_dist `{SI: indexT} {A B : ofe} (f : A → B) (mx : option A) (y : B) n :
  f <$> mx ≡{n}≡ Some y ↔ ∃ x : A, mx = Some x ∧ y ≡{n}≡ f x.
Proof.
  split; [|by intros (x&->&->)].
  intros (?&?%fmap_Some&?)%dist_Some_inv_r'; naive_solver.
Qed.

Definition optionO_map `{SI: indexT} {A B: ofe} (f : A -n> B) : optionO A -n> optionO B :=
  OfeMor (fmap f : optionO A → optionO B).
Global Instance optionO_map_ne `{SI: indexT} (A B: ofe) : NonExpansive (@optionO_map _ A B).
Proof. by intros n f f' Hf []; constructor; apply Hf. Qed.

Program Definition optionOF `{SI: indexT} (F : oFunctor) : oFunctor := {|
  oFunctor_car A B := optionO (oFunctor_car F A B);
  oFunctor_map A1 A2 B1 B2 fg := optionO_map (oFunctor_map F fg)
|}.
Next Obligation.
  by intros SI F A1 A2 B1 B2 n f g Hfg; apply optionO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros SI F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply oFunctor_map_id.
Qed.
Next Obligation.
  intros SI F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply oFunctor_map_compose.
Qed.

Global Instance optionOF_contractive `{SI: indexT} (F : oFunctor):
  oFunctorContractive F → oFunctorContractive (optionOF F).
Proof.
  by intros ? ? A1 A2 B1 B2 n f g Hfg; apply optionO_map_ne, oFunctor_map_contractive.
Qed.

(** * Later type *)
(** Note that the projection [later_car] is not non-expansive (see also the
lemma [later_car_anti_contractive] below), so it cannot be used in the logic.
If you need to get a witness out, you should use the lemma [Next_uninj]
instead. *)
Record later (A : Type) : Type := Next { later_car : A }.
Add Printing Constructor later.
Global Arguments Next {_} _.
Global Arguments later_car {_} _.
Global Instance: Params (@Next) 1 := {}.

Section later.
  Context `{SI: indexT} {A : ofe}.
  Local Instance later_equiv : Equiv (later A) := λ x y, later_car x ≡ later_car y.
  Local Instance later_dist : Dist (later A) := λ n x y,
    dist_later n (later_car x) (later_car y).
  Definition later_ofe_mixin : OfeMixin (later A).
  Proof.
    split.
    - intros x y; unfold equiv, later_equiv; rewrite !equiv_dist.
      split; first by intros Hxy n m Hm.
      intros H n; eapply (H (succ n)). by eapply index_succ_iff.
    - split; rewrite /dist /later_dist.
      + by intros [x].
      + by intros [x] [y].
      + by intros [x] [y] [z] ??; trans y.
    - intros n m [x] [y] H ? p Hp. eapply H; by transitivity m.
  Qed.
  Canonical Structure laterO : ofe := Ofe (later A) later_ofe_mixin.

  Lemma later_car_bounded_expansive (a b : laterO) n: a ≡{succ n}≡ b → later_car a ≡{n}≡ later_car b.
  Proof.
    intros H. destruct a as [a], b as [b]; cbn in *. apply (H n (index_succ_greater _)).
  Qed.

  Lemma later_dist_unfold (a b : laterO) n : a ≡{n}≡ b ↔ dist_later n (later_car a) (later_car b).
  Proof. tauto. Qed.

  Program Definition later_chain (c : chain laterO) : chain A :=
    {| chain_car n := later_car (c (succ n)) |}.
  Next Obligation.
    intros c n i ?; apply (chain_cauchy c (succ n)); eauto with index.
  Qed.

  Program Definition later_limit_bchain {n} (c : bchain laterO n) (islim: ∀ m, m ≺ n → succ m ≺ n) : bchain A n :=
    {| bchain_car m Hm := later_car (c (succ m) (islim m Hm)) |}.
  Next Obligation.
    intros n c islim m p ? Hm Hp; apply (bchain_cauchy n c (succ m) (succ p)); eauto with index.
  Qed.


  Global Instance Next_contractive : Contractive  (@Next A).
  Proof. by intros n x y. Qed.

  Global Program Instance later_cofe `{!Cofe A} : Cofe laterO :=
    { compl c := Next (compl (later_chain c));
      lbcompl n Hn c := Next (lbcompl Hn (later_limit_bchain c (proper_limit_is_limit Hn)))
    }.
  Next Obligation.
    intros ? n c m Hm; simpl. rewrite conv_compl /=.
    symmetry; apply (chain_cauchy c (succ m) n); eauto with index.
  Qed.
  Next Obligation.
    intros ? n Hn c m Hm; simpl. intros p Hp; simpl.
    unshelve rewrite conv_lbcompl; simpl; first by eauto using index_lt_le_trans.
    symmetry; eapply (bchain_cauchy n c (succ p)); eauto with index.
  Qed.
  Next Obligation.
    intros ? n Hn c d m H; simpl.
    intros p Hp; simpl; eapply lbcompl_ne; intros q Hq; simpl; by eapply H.
  Qed.

  Global Instance Later_inj n : Inj (dist_later n) (dist n) (@Next A).
  Proof. by intros x y H. Qed.

  Lemma Next_uninj x : ∃ a, x ≡ Next a.
  Proof. by exists (later_car x). Qed.
  Local Instance later_car_anti_contractive n :
    Proper (dist n ==> dist_later n) later_car.
  Proof. move=> [x] [y] /= Hxy. done. Qed.

  (** [f] is contractive iff it can factored into [Next] and a non-expansive
  function. *)
  Lemma contractive_alt {B : ofe} (f : A → B) :
    Contractive f ↔ ∃ g : later A → B, NonExpansive g ∧ ∀ x, f x ≡ g (Next x).
  Proof.
    split.
    - intros Hf. exists (f ∘ later_car); split=> // n x y ?; simpl. by f_contractive.
    - intros (g&Hg&Hf) n x y Hxy. rewrite !Hf. by apply Hg.
  Qed.
End later.

Arguments laterO {_} _.

Definition later_map {A B} (f : A → B) (x : later A) : later B :=
  Next (f (later_car x)).
Global Instance later_map_ne {SI: indexT} {A B : ofe} (f : A → B) n :
  Proper (dist_later n ==> dist_later n) f →
  Proper (dist n ==> dist n) (later_map f) | 0.
Proof. intros P [x] [y] H; rewrite /later_map //=.
       intros m Hm; apply P, Hm. apply H.
Qed.

Global Instance later_map_ne' `{SI: indexT} {A B : ofe} (f : A → B) `{NonExpansive  f} : NonExpansive  (later_map f).
Proof. intros ?[x][y]H. unfold later_map; simpl.
       intros ??; cbn. f_equiv. by eapply H.
Qed.

Lemma later_map_id {A} (x : later A) : later_map id x = x.
Proof. by destruct x. Qed.
Lemma later_map_compose {A B C} (f : A → B) (g : B → C) (x : later A) :
  later_map (g ∘ f) x = later_map g (later_map f x).
Proof. by destruct x. Qed.
Lemma later_map_ext `{SI: indexT} {A B : ofe} (f g : A → B) x :
  (∀ x, f x ≡ g x) → later_map f x ≡ later_map g x.
Proof. destruct x; intros Hf; apply Hf. Qed.
Definition laterO_map `{SI: indexT} {A B: ofe} (f : A -n> B) : laterO A -n> laterO B :=
  OfeMor (later_map f).
Global Instance laterO_map_contractive {SI: indexT} (A B : ofe) : Contractive  (@laterO_map SI A B).
Proof. intros n f g ? [x] ??; simpl. by apply H. Qed.

Program Definition laterOF `{SI: indexT} (F : oFunctor) : oFunctor := {|
  oFunctor_car A B := laterO (oFunctor_car F A B);
  oFunctor_map A1 A2 B1 B2 fg := laterO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros k F A1 A2 B1 B2 n fg fg' ?.
  by apply (contractive_ne laterO_map), oFunctor_map_ne.
Qed.
Next Obligation.
  intros k F A B x; simpl. rewrite -{2}(later_map_id x).
  apply later_map_ext=>y. by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros k F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -later_map_compose.
  apply later_map_ext=>y; apply oFunctor_map_compose.
Qed.
Notation "▶ F"  := (laterOF F%OF) (at level 20, right associativity) : oFunctor_scope.

Global Instance laterOF_contractive `{SI: indexT} {F :oFunctor} : oFunctorContractive (laterOF F).
Proof.
  intros A1 A2 B1 B2 n fg fg' Hfg. apply laterO_map_contractive.
  intros ???; simpl.  by eapply oFunctor_map_ne, Hfg.
Qed.

(** * Dependently-typed functions over a discrete domain *)
(** This separate notion is useful whenever we need dependent functions, and
whenever we want to avoid the hassle of the bundled non-expansive function type.

Note that non-dependent functions over a discrete domain, [A -d> B] (following
the notation we introduce below) are non-expansive if they are
[Proper ((≡) ==> (≡))]. In other words, since the domain is discrete,
non-expansiveness and respecting [(≡)] are the same. If the domain is moreover
Leibniz ([LeibnizEquiv A]), we get both for free.

We make [discrete_fun] a definition so that we can register it as a canonical
structure.  We do not bundle the [Proper] proof to keep [discrete_fun] easier to
use. It turns out all the desired OFE and functorial properties do not rely on
this [Proper] instance. *)
Definition discrete_fun `{SI: indexT} {A} (B : A → ofe) := ∀ x : A, B x.

Section discrete_fun.
  Context `{SI: indexT} {A : Type} {B : A → ofe}.
  Implicit Types f g : discrete_fun B.

  Instance discrete_fun_equiv : Equiv (discrete_fun B) := λ f g, ∀ x, f x ≡ g x.
  Instance discrete_fun_dist : Dist (discrete_fun B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition discrete_fun_ofe_mixin : OfeMixin (discrete_fun B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - intros n m f g ? H x. eauto using dist_le.
  Qed.
  Canonical Structure discrete_funO := Ofe (discrete_fun B) discrete_fun_ofe_mixin.

  Program Definition discrete_fun_chain `(c : chain discrete_funO) (x : A) : chain (B x) :=
    {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Definition discrete_fun_bchain {n} `(c : bchain discrete_funO n) (x : A) : bchain (B x) n :=
    {| bchain_car n Hn := c n Hn x |}.
  Next Obligation. intros n c x m p Hm Hp Hmp. by apply (bchain_cauchy n c _ _  Hm Hp Hmp). Qed.


  Global Program Instance discrete_fun_cofe `{!∀ x, Cofe (B x)} : Cofe discrete_funO :=
    { compl c x := compl (discrete_fun_chain c x); lbcompl n Hn c x := lbcompl Hn (discrete_fun_bchain c x) }.
  Next Obligation.
    intros ? n c x. by apply conv_compl.
  Qed.
  Next Obligation.
    intros ? n Hn c m Hm x. unshelve rewrite conv_lbcompl; eauto.
  Qed.
  Next Obligation.
    intros ? n Hn c d m H x. eapply lbcompl_ne; intros; simpl; by eapply H.
  Qed.

  Global Instance discrete_fun_inhabited `{∀ x, Inhabited (B x)} : Inhabited discrete_funO :=
    populate (λ _, inhabitant).
  Global Instance discrete_fun_lookup_discrete `{EqDecision A} f x :
    Discrete f → Discrete (f x).
  Proof.
    intros Hf y ?.
    set (g x' := if decide (x = x') is left H then eq_rect _ B y _ H else f x').
    trans (g x).
    { apply Hf=> x'. unfold g. by destruct (decide _) as [[]|]. }
    unfold g. destruct (decide _) as [Hx|]; last done.
    by rewrite (proof_irrel Hx eq_refl).
  Qed.
End discrete_fun.

Global Arguments discrete_funO {_ _} _.
Notation "A -d> B" :=
  (@discrete_funO _ A (λ _, B)) (at level 99, B at level 200, right associativity).

Definition discrete_fun_map `{SI: indexT} {A} {B1 B2 : A → ofe} (f : ∀ x, B1 x → B2 x)
  (g : discrete_fun B1) : discrete_fun B2 := λ x, f _ (g x).

Lemma discrete_fun_map_ext `{SI: indexT} {A} {B1 B2 : A → ofe} (f1 f2 : ∀ x, B1 x → B2 x)
  (g : discrete_fun B1) :
  (∀ x, f1 x (g x) ≡ f2 x (g x)) → discrete_fun_map f1 g ≡ discrete_fun_map f2 g.
Proof. done. Qed.
Lemma discrete_fun_map_id `{SI: indexT} {A} {B : A → ofe} (g : discrete_fun B) :
  discrete_fun_map (λ _, id) g = g.
Proof. done. Qed.
Lemma discrete_fun_map_compose `{SI: indexT} {A} {B1 B2 B3 : A → ofe}
    (f1 : ∀ x, B1 x → B2 x) (f2 : ∀ x, B2 x → B3 x) (g : discrete_fun B1) :
  discrete_fun_map (λ x, f2 x ∘ f1 x) g = discrete_fun_map f2 (discrete_fun_map f1 g).
Proof. done. Qed.

Global Instance discrete_fun_map_ne `{SI: indexT} {A} {B1 B2 : A → ofe} (f : ∀ x, B1 x → B2 x) n :
  (∀ x, Proper (dist n ==> dist n) (f x)) →
  Proper (dist n ==> dist n) (discrete_fun_map f).
Proof. by intros ? y1 y2 Hy x; rewrite /discrete_fun_map (Hy x). Qed.

Definition discrete_funO_map `{SI: indexT} {A} {B1 B2 : A → ofe} (f : discrete_fun (λ x, B1 x -n> B2 x)) :
  discrete_funO B1 -n> discrete_funO B2 := OfeMor (discrete_fun_map f).
Global Instance discrete_funO_map_ne `{SI: indexT} {A} {B1 B2 : A → ofe} :
  NonExpansive (@discrete_funO_map SI A B1 B2).
Proof. intros n f1 f2 Hf g x; apply Hf. Qed.

Program Definition discrete_funOF `{SI: indexT} {C} (F : C → oFunctor) : oFunctor := {|
  oFunctor_car A B := discrete_funO (λ c, oFunctor_car (F c) A B);
  oFunctor_map A1 A2 B1 B2 fg := discrete_funO_map (λ c, oFunctor_map (F c) fg)
|}.
Next Obligation.
  intros SI C F A1 A2 B1 B2 n ?? g. by apply discrete_funO_map_ne=>?; apply oFunctor_map_ne.
Qed.
Next Obligation.
  intros SI C F A B g; simpl. rewrite -{2}(discrete_fun_map_id g).
  apply discrete_fun_map_ext=> y; apply oFunctor_map_id.
Qed.
Next Obligation.
  intros SI C F A1 A2 A3 B1 B2 B3 f1 f2 f1' f2' g.
  rewrite /= -discrete_fun_map_compose.
  apply discrete_fun_map_ext=>y; apply oFunctor_map_compose.
Qed.

Notation "T -d> F" := (@discrete_funOF _ T%type (λ _, F%OF)) : oFunctor_scope.

Global Instance discrete_funOF_contractive {SI: indexT} {C} (F : C → oFunctor) :
  (∀ c, oFunctorContractive (F c)) → oFunctorContractive (discrete_funOF F).
Proof.
  intros ? A1 A2 B1 B2 n ?? g.
  by apply discrete_funO_map_ne=>c; apply oFunctor_map_contractive.
Qed.

(** * Constructing isomorphic OFEs *)
Lemma iso_ofe_mixin `{SI: indexT} {A : ofe} {B: Type} `{!Equiv B, !Dist B} (g : B → A)
  (g_equiv : ∀ y1 y2, y1 ≡ y2 ↔ g y1 ≡ g y2)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2) : OfeMixin B.
Proof.
  split.
  - intros y1 y2. rewrite g_equiv. setoid_rewrite g_dist. apply equiv_dist.
  - split.
    + intros y. by apply g_dist.
    + intros y1 y2. by rewrite !g_dist.
    + intros y1 y2 y3. rewrite !g_dist. intros ??; etrans; eauto.
  - intros n m y1 y2. rewrite !g_dist. intros; eapply dist_le; eauto.
Qed.

Section iso_cofe_subtype.
  Context `{SI: indexT} {A B : ofe} `{!Cofe A} (P : A → Prop) (f : ∀ x, P x → B) (g : B → A).
  Context (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2).
  Let Hgne : NonExpansive g.
  Proof. intros n y1 y2. apply g_dist. Qed.
  Existing Instance Hgne.
  Context (gf : ∀ x Hx, g (f x Hx) ≡ x).
  Context (Hlimit : ∀ c : chain B, P (compl (chain_map g c))).
  Context (Hblimit : ∀ n (Hn : index_is_proper_limit n) c, P (lbcompl Hn (bchain_map g c))).
  Program Definition iso_cofe_subtype : Cofe B :=
    {| compl c := f (compl (chain_map g c)) _; lbcompl n Hn c := f (lbcompl Hn (bchain_map g c)) _ |}.
  Next Obligation. apply Hlimit. Qed.
  Next Obligation. apply Hblimit. Qed.
  Next Obligation. intros n c; simpl. apply g_dist. by rewrite gf conv_compl. Qed.
  Next Obligation. intros n Hn c m Hm; simpl. apply g_dist. by unshelve rewrite gf conv_lbcompl. Qed.
  Next Obligation.
    intros n Hn c d m Heq; simpl. apply g_dist. rewrite !gf.
    apply lbcompl_ne. intros ??; simpl; by rewrite Heq.
  Qed.

End iso_cofe_subtype.

Lemma iso_cofe_subtype' `{SI: indexT} {A B : ofe} `{!Cofe A}
  (P : A → Prop) (f : ∀ x, P x → B) (g : B → A)
  (Pg : ∀ y, P (g y))
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x Hx, g (f x Hx) ≡ x)
  (Hlimit : LimitPreserving P)
  (Hblimit : BoundedLimitPreserving P) : Cofe B.
Proof. apply: (iso_cofe_subtype P f g)=> //; eauto. Qed.

Definition iso_cofe `{SI: indexT} {A B : ofe} `{!Cofe A} (f : A → B) (g : B → A)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x, g (f x) ≡ x) : Cofe B.
Proof. by apply (iso_cofe_subtype (λ _, True) (λ x _, f x) g). Qed.

(** * Sigma type *)
Section sigma.
  Context `{SI: indexT} {A : ofe} {P : A → Prop}.
  Implicit Types x : sig P.

  (* TODO: Find a better place for this Equiv instance. It also
     should not depend on A being an OFE. *)
  Local Instance sig_equiv : Equiv (sig P) := λ x1 x2, `x1 ≡ `x2.
  Local Instance sig_dist : Dist (sig P) := λ n x1 x2, `x1 ≡{n}≡ `x2.

  Definition sig_equiv_alt x y : x ≡ y ↔ `x ≡ `y := reflexivity _.
  Definition sig_dist_alt n x y : x ≡{n}≡ y ↔ `x ≡{n}≡ `y := reflexivity _.

  Lemma exist_ne n a1 a2 (H1 : P a1) (H2 : P a2) :
    a1 ≡{n}≡ a2 → a1 ↾ H1 ≡{n}≡ a2 ↾ H2.
  Proof. done. Qed.

  Global Instance proj1_sig_ne : NonExpansive (@proj1_sig _ P).
  Proof. by intros n [a Ha] [b Hb] ?. Qed.
  Definition sig_ofe_mixin : OfeMixin (sig P).
  Proof. by apply (iso_ofe_mixin proj1_sig). Qed.
  Canonical Structure sigO : ofe := Ofe (sig P) sig_ofe_mixin.

  Global Instance sig_cofe `{!Cofe A, !LimitPreserving P, !BoundedLimitPreserving P} : Cofe sigO.
  Proof. apply (iso_cofe_subtype' P (exist P) proj1_sig)=> //. by intros []. Qed.

  Global Instance sig_discrete (x : sig P) :  Discrete (`x) → Discrete x.
  Proof. intros ? y. rewrite sig_dist_alt sig_equiv_alt. apply (discrete _). Qed.
  Global Instance sig_ofe_discrete : OfeDiscrete A → OfeDiscrete sigO.
  Proof. intros ??. apply _. Qed.
End sigma.

Global Arguments sigO {_ _} _.

(** * SigmaT type *)
(** Ofe for [sigT]. The first component must be discrete and use Leibniz
equality, while the second component might be any OFE. *)
Section sigT.
  Import EqNotations.

  Context `{SI: indexT} {A : Type} {P : A → ofe}.
  Implicit Types x : sigT P.

  (**
    The distance for [{ a : A & P }] uses Leibniz equality on [A] to
    transport the second components to the same type,
    and then step-indexed distance on the second component.
    Unlike in the topos of trees, with (C)OFEs we cannot use step-indexed equality
    on the first component.
  *)
  Local Instance sigT_dist : Dist (sigT P) := λ n x1 x2,
    ∃ Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 ≡{n}≡ projT2 x2.

  (**
    Usually we'd give a direct definition, and show it equivalent to
    [∀ n, x1 ≡{n}≡ x2] when proving the [equiv_dist] OFE axiom.
    But here the equivalence requires UIP — see [sigT_equiv_eq_alt].
    By defining [equiv] in terms of [dist], we can define an OFE
    without assuming UIP, at the cost of complex reasoning on [equiv].
  *)
  Local Instance sigT_equiv : Equiv (sigT P) := λ x1 x2,
    ∀ n, x1 ≡{n}≡ x2.

  (** Unfolding lemmas.
      Written with [↔] not [=] to avoid https://github.com/coq/coq/issues/3814. *)
  Definition sigT_equiv_eq x1 x2 : (x1 ≡ x2) ↔ ∀ n, x1 ≡{n}≡ x2 :=
      reflexivity _.

  Definition sigT_dist_eq x1 x2 n : (x1 ≡{n}≡ x2) ↔
    ∃ Heq : projT1 x1 = projT1 x2, (rew Heq in projT2 x1) ≡{n}≡ projT2 x2 :=
      reflexivity _.

  Definition sigT_dist_proj1 n {x y} : x ≡{n}≡ y → projT1 x = projT1 y := proj1_ex.
  Definition sigT_equiv_proj1 {x y} : x ≡ y → projT1 x = projT1 y := λ H, proj1_ex (H zero).

  Definition sigT_ofe_mixin : OfeMixin (sigT P).
  Proof.
    split => // n.
    - split; hnf; setoid_rewrite sigT_dist_eq.
      + intros. by exists eq_refl.
      + move => [xa x] [ya y] /=. destruct 1 as [-> Heq].
        by exists eq_refl.
      + move => [xa x] [ya y] [za z] /=.
        destruct 1 as [-> Heq1].
        destruct 1 as [-> Heq2]. exists eq_refl => /=. by trans y.
    - setoid_rewrite sigT_dist_eq.
      move => m [xa x] [ya y] /=. destruct 1 as [-> Heq].
      exists eq_refl. by eapply dist_dist_later.
  Qed.

  Canonical Structure sigTO : ofe := Ofe (sigT P) sigT_ofe_mixin.

  Lemma sigT_equiv_eq_alt `{!∀ a b : A, ProofIrrel (a = b)} x1 x2 :
    x1 ≡ x2 ↔
    ∃ Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 ≡ projT2 x2.
  Proof.
    setoid_rewrite equiv_dist. setoid_rewrite sigT_dist_eq. split => Heq.
    - move: (Heq zero) => [H0eq1 _].
      exists H0eq1 => n. move: (Heq n) => [] Hneq1.
      by rewrite (proof_irrel H0eq1 Hneq1).
    - move: Heq => [Heq1 Heqn2] n. by exists Heq1.
  Qed.

  (** [projT1] is non-expansive and proper. *)
  Global Instance projT1_ne : NonExpansive (projT1 : sigTO → leibnizO A).
  Proof. solve_proper. Qed.

  Global Instance projT1_proper : Proper ((≡) ==> (≡)) (projT1 : sigTO → leibnizO A).
  Proof. apply ne_proper, projT1_ne. Qed.

  (** [projT2] is "non-expansive"; the properness lemma [projT2_ne] requires UIP. *)
  Lemma projT2_ne n (x1 x2 : sigTO) (Heq : x1 ≡{n}≡ x2) :
    rew (sigT_dist_proj1 n Heq) in projT2 x1 ≡{n}≡ projT2 x2.
  Proof. by destruct Heq. Qed.

  Lemma projT2_proper `{!∀ a b : A, ProofIrrel (a = b)} (x1 x2 : sigTO) (Heqs : x1 ≡ x2):
    rew (sigT_equiv_proj1 Heqs) in projT2 x1 ≡ projT2 x2.
  Proof.
    move: x1 x2 Heqs => [a1 x1] [a2 x2] Heqs.
    case: (proj1 (sigT_equiv_eq_alt _ _) Heqs) => /=. intros ->.
    rewrite (proof_irrel (sigT_equiv_proj1 Heqs) eq_refl) /=. done.
  Qed.

  (** [existT] is "non-expansive" — general, dependently-typed statement. *)
  Lemma existT_ne n {i1 i2} {v1 : P i1} {v2 : P i2} :
    ∀ (Heq : i1 = i2), (rew f_equal P Heq in v1 ≡{n}≡ v2) →
      existT i1 v1 ≡{n}≡ existT i2 v2.
  Proof. intros ->; simpl. exists eq_refl => /=. done. Qed.

  Lemma existT_proper {i1 i2} {v1 : P i1} {v2 : P i2} :
    ∀ (Heq : i1 = i2), (rew f_equal P Heq in v1 ≡ v2) →
      existT i1 v1 ≡ existT i2 v2.
  Proof. intros Heq Heqv n. apply (existT_ne n Heq), equiv_dist, Heqv. Qed.

  (** [existT] is "non-expansive" — non-dependently-typed version. *)
  Global Instance existT_ne_2 a : NonExpansive (@existT A P a).
  Proof. move => ??? Heq. apply (existT_ne _ eq_refl Heq). Qed.

  Global Instance existT_proper_2 a : Proper ((≡) ==> (≡)) (@existT A P a).
  Proof. apply ne_proper, _. Qed.

  Implicit Types (c : chain sigTO).

  Global Instance sigT_discrete x : Discrete (projT2 x) → Discrete x.
  Proof.
    move: x => [xa x] ? [ya y] [] /=; intros -> => /= Hxy n.
    exists eq_refl => /=. apply equiv_dist, (discrete _), Hxy.
  Qed.

  Global Instance sigT_ofe_discrete : (∀ a, OfeDiscrete (P a)) → OfeDiscrete sigTO.
  Proof. intros ??. apply _. Qed.

  Lemma sigT_chain_const_proj1 c n : projT1 (c n) = projT1 (c zero).
  Proof. refine (sigT_dist_proj1 _ (chain_cauchy c zero n _)). apply index_zero_minimum. Qed.

  Lemma sigT_bchain_const_proj1 n Hn (c: bchain sigTO n) m Hm: projT1 (c m Hm) = projT1 (c zero Hn).
  Proof. refine (sigT_dist_proj1 _ (bchain_cauchy n c zero m _ _ _)). apply index_zero_minimum. Qed.

  (* For this COFE construction we need UIP (Uniqueness of Identity Proofs)
    on [A] (i.e. [∀ x y : A, ProofIrrel (x = y)]. UIP is most commonly obtained
    from decidable equality (by Hedberg’s theorem, see
    [stdpp.proof_irrel.eq_pi]). *)
  Section cofe.
    Context `{!∀ a b : A, ProofIrrel (a = b)} `{!∀ a, Cofe (P a)}.

    Program Definition chain_map_snd c : chain (P (projT1 (c zero))) :=
      {| chain_car n := rew (sigT_chain_const_proj1 c n) in projT2 (c n) |}.
    Next Obligation.
      move => c n i Hle /=.
      (* [Hgoal] is our thesis, up to casts: *)
      case: (chain_cauchy c n i Hle) => [Heqin Hgoal] /=.
      (* Pretty delicate. We have two casts to [projT1 (c zero)].
        We replace those by one cast. *)
      move: (sigT_chain_const_proj1 c i) (sigT_chain_const_proj1 c n)
        => Heqi0 Heqn0.
      (* Rewrite [projT1 (c zero)] to [projT1 (c n)] in goal and [Heqi0]: *)
      destruct Heqn0.
      by rewrite /= (proof_irrel Heqi0 Heqin).
    Qed.

    Definition sigT_compl : chain sigTO → sigTO :=
      λ c, existT (projT1 (c zero)) (compl (chain_map_snd c)).

    Program Definition bchain_map_snd n Hn (c: bchain sigTO n): bchain (P (projT1 (c zero Hn))) n :=
      {| bchain_car m Hm := rew (sigT_bchain_const_proj1 n Hn c m Hm) in projT2 (c m Hm) |}.
    Next Obligation.
      move => n Hn c m p Hm Hp Hle /=.
      (* [Hgoal] is our thesis, up to casts: *)
      case: (bchain_cauchy n c m p Hm Hp Hle) => [Heqin Hgoal] /=.
      (* Pretty delicate. We have two casts to [projT1 (c zero)].
        We replace those by one cast. *)
      move: (sigT_bchain_const_proj1 n Hn c m Hm ) (sigT_bchain_const_proj1 n Hn c p Hp)
        => Heqm0 Heqp0.
      (* Rewrite [projT1 (c zero)] to [projT1 (c n)] in goal and [Heqi0]: *)
      destruct Heqm0.
      by rewrite /= (proof_irrel Heqp0 Heqin).
    Qed.

    Definition sigT_lbcompl n (Hn: index_is_proper_limit n) (c: bchain sigTO n): sigTO :=
      existT (projT1 (c zero (proper_limit_not_zero Hn))) (lbcompl Hn (bchain_map_snd n (proper_limit_not_zero Hn) c)).


    Global Program Instance sigT_cofe : Cofe sigTO := { compl := sigT_compl; lbcompl := sigT_lbcompl }.
    Next Obligation.
      intros n c. rewrite /sigT_compl sigT_dist_eq /=.
      exists (symmetry (sigT_chain_const_proj1 c n)).
      (* Our thesis, up to casts: *)
      pose proof (conv_compl n (chain_map_snd c)) as Hgoal.
      move: (compl (chain_map_snd c)) Hgoal => pc0 /=.
      destruct (sigT_chain_const_proj1 c n); simpl. done.
    Qed.
    Next Obligation.
      intros n Hn c m Hm. rewrite /sigT_lbcompl sigT_dist_eq /=.
      exists (symmetry (sigT_bchain_const_proj1 n (proper_limit_not_zero Hn) c m Hm)).
      (* Our thesis, up to casts: *)
      pose proof (conv_lbcompl n Hn (bchain_map_snd n (proper_limit_not_zero Hn) c) m Hm) as Hgoal.
      move: (lbcompl Hn (bchain_map_snd n (proper_limit_not_zero Hn) c)) Hgoal => pc0 /=.
      destruct (sigT_bchain_const_proj1 n (proper_limit_not_zero Hn) c m Hm); simpl. done.
    Qed.
    Next Obligation.
      intros n Hn c d m Heq; rewrite /sigT_lbcompl sigT_dist_eq /=.
      destruct (Heq zero (proper_limit_not_zero Hn)) as [eq Ht]. exists eq; simpl.
      enough (lbcompl Hn (rew [λ x : A, bchain (P x) n] eq in bchain_map_snd n (proper_limit_not_zero Hn) c) ≡{m}≡ lbcompl Hn (bchain_map_snd n (proper_limit_not_zero Hn) d)) as Hlbcompl.
      { rewrite <-Hlbcompl. clear Ht Hlbcompl. by destruct eq. }
      apply lbcompl_ne; simpl. intros p Hp. destruct (Heq p Hp) as [eq' H'].
      rewrite <-(@map_subst _ (λ y, bchain (P y) n) P (λ y d, d p Hp) _ _ eq); simpl.
      rewrite rew_compose. revert H'.
      move: (sigT_bchain_const_proj1 n (proper_limit_not_zero Hn) d p Hp) (eq_trans (sigT_bchain_const_proj1 n (proper_limit_not_zero Hn) c p Hp) eq) => e1 e2.
      destruct e1; simpl. intros <-.
      by rewrite /= (proof_irrel e2 eq').
    Qed.
  End cofe.
End sigT.

Global Arguments sigTO {_ _} _.

Section sigTOF.
  Context `{SI: indexT} {A : Type}.

  Program Definition sigT_map {P1 P2 : A → ofe} :
    discrete_funO (λ a, P1 a -n> P2 a) -n>
    sigTO P1 -n> sigTO P2 :=
    λne f xpx, existT _ (f _ (projT2 xpx)).
  Next Obligation.
    move => ?? f n [x px] [y py] [/= Heq]. destruct Heq; simpl.
    exists eq_refl => /=. by f_equiv.
  Qed.
  Next Obligation.
    move => ?? n f g Heq [x px] /=. exists eq_refl => /=. apply Heq.
  Qed.

  Program Definition sigTOF (F : A → oFunctor) : oFunctor := {|
    oFunctor_car A B := sigTO (λ a, oFunctor_car (F a) A B);
    oFunctor_map A1 A2 B1 B2 fg := sigT_map (λ a, oFunctor_map (F a) fg)
  |}.
  Next Obligation.
    repeat intro. exists eq_refl => /=. solve_proper.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), oFunctor_map_id.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), oFunctor_map_compose.
  Qed.

  Global Instance sigTOF_contractive {F} :
    (∀ a, oFunctorContractive (F a)) → oFunctorContractive (sigTOF F).
  Proof.
    repeat intro. apply sigT_map => a. exact: oFunctor_map_contractive.
  Qed.
End sigTOF.
Global Arguments sigTOF {_ _} _%OF.

Notation "{ x  &  P }" := (sigTOF (λ x, P%OF)) : oFunctor_scope.
Notation "{ x : A &  P }" := (@sigTOF _ A%type (λ x, P%OF)) : oFunctor_scope.


(** * Finite COFEs *)
(** In the special case of natural numbers as step-index type, there are no bounded limits. *)
(** This case enables us to get additional COFE instances. *)
(** This is not a class since it should only be used as an easy way of constructing Cofes. *)
Record FiniteCofe {SI: indexT} `{!FiniteIndex SI} (A : ofe) :=
  {
    fin_compl : chain A → A;
    conv_fin_compl n c : fin_compl c ≡{n}≡ c n;
  }.
Global Arguments fin_compl : simpl never.

Lemma FiniteIndex_no_limit {SI: indexT} `{Hfin: !FiniteIndex SI} (n : index): ¬ index_is_proper_limit n.
Proof.
  intros Hlim.
  destruct Hlim as [Hlim Hnz]. destruct (Hfin n) as [-> | [β ->]]; first by index_contra_solve.
  by apply index_succ_not_limit in Hlim.
Qed.

Program Definition FiniteCofe_lbcompl `{SI: indexT} `{!FiniteIndex SI} (A : ofe) {Hfin : FiniteCofe A}
  (n : index) (Hn : index_is_proper_limit n) (c : bchain A n) : A := _.
Next Obligation. intros ?? A Hfin n Hlim. exfalso. by eapply FiniteIndex_no_limit. Qed.

Program Definition FiniteCofe_is_Cofe `{SI: indexT} `{!FiniteIndex SI} {A : ofe} (Hfin : FiniteCofe A) : Cofe A :=
  {| compl := fin_compl A Hfin; lbcompl := @FiniteCofe_lbcompl _ _ A Hfin |}.
Next Obligation. intros. apply conv_fin_compl. Qed.
Next Obligation. intros. exfalso. by eapply FiniteIndex_no_limit. Qed.
Next Obligation. intros. exfalso. by eapply FiniteIndex_no_limit. Qed.

Program Definition Cofe_is_FiniteCofe `{SI: indexT} `{!FiniteIndex SI} `{!Cofe A} : FiniteCofe A := {| fin_compl := compl |}.
Next Obligation. intros; apply conv_compl. Qed.

Section iso_fin_cofe_subtype.
  Context `{SI: indexT} `{!FiniteIndex SI} {A B : ofe} `{!Cofe A} (P : A → Prop) (f : ∀ x, P x → B) (g : B → A).
  Context (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2).
  Let Hgne : NonExpansive g.
  Proof. intros n y1 y2. apply g_dist. Qed.
  Existing Instance Hgne.
  Context (gf : ∀ x Hx, g (f x Hx) ≡ x).
  Context (Hlimit : ∀ c : chain B, P (compl (chain_map g c))).
  Program Definition iso_finite_cofe_subtype : FiniteCofe B :=
    {| fin_compl c := f (compl (chain_map g c)) _ |}.
  Next Obligation. apply Hlimit. Qed.
  Next Obligation. intros n c; simpl. apply g_dist. by rewrite gf conv_compl. Qed.
End iso_fin_cofe_subtype.

Lemma iso_finite_cofe_subtype' `{SI: indexT} `{!FiniteIndex SI} {A B : ofe} `{!Cofe A}
  (P : A → Prop) (f : ∀ x, P x → B) (g : B → A)
  (Pg : ∀ y, P (g y))
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x Hx, g (f x Hx) ≡ x)
  (Hlimit : LimitPreserving P) : Cofe B.
Proof. refine (FiniteCofe_is_Cofe _). apply: (iso_finite_cofe_subtype P f g)=> //; eauto. Qed.

Definition iso_finite_cofe `{SI: indexT} `{!FiniteIndex SI} {A B : ofe} `{!Cofe A} (f : A → B) (g : B → A)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x, g (f x) ≡ x) : Cofe B.
Proof. refine (FiniteCofe_is_Cofe _). by apply (iso_finite_cofe_subtype (λ _, True) (λ x _, f x) g). Qed.

(** * Isomorphisms between OFEs *)
Record ofe_iso `{SI: indexT} (A B : ofe) := OfeIso {
  ofe_iso_1 : A -n> B;
  ofe_iso_2 : B -n> A;
  ofe_iso_12 y : ofe_iso_1 (ofe_iso_2 y) ≡ y;
  ofe_iso_21 x : ofe_iso_2 (ofe_iso_1 x) ≡ x;
}.
Global Arguments OfeIso {_ _ _} _ _ _ _.
Global Arguments ofe_iso_1 {_ _ _} _.
Global Arguments ofe_iso_2 {_ _ _} _.
Global Arguments ofe_iso_12 {_ _ _} _ _.
Global Arguments ofe_iso_21 {_ _ _} _ _.

Section ofe_iso.
  Context `{SI: indexT} {A B : ofe}.

  Local Instance ofe_iso_equiv : Equiv (ofe_iso A B) := λ I1 I2,
    ofe_iso_1 I1 ≡ ofe_iso_1 I2 ∧ ofe_iso_2 I1 ≡ ofe_iso_2 I2.

  Local Instance ofe_iso_dist : Dist (ofe_iso A B) := λ n I1 I2,
    ofe_iso_1 I1 ≡{n}≡ ofe_iso_1 I2 ∧ ofe_iso_2 I1 ≡{n}≡ ofe_iso_2 I2.

  Global Instance ofe_iso_1_ne : NonExpansive (ofe_iso_1 (A:=A) (B:=B)).
  Proof. by destruct 1. Qed.
  Global Instance ofe_iso_2_ne : NonExpansive (ofe_iso_2 (A:=A) (B:=B)).
  Proof. by destruct 1. Qed.

  Lemma ofe_iso_ofe_mixin : OfeMixin (ofe_iso A B).
  Proof. by apply (iso_ofe_mixin (λ I, (ofe_iso_1 I, ofe_iso_2 I))). Qed.
  Canonical Structure ofe_isoO : ofe := Ofe (ofe_iso A B) ofe_iso_ofe_mixin.

  (* ≡ is not BoundedLimitPreserving, so we do not get this Cofe instance in the general case.
    However, for finite Cofes this works. *)
  Global Instance ofe_iso_cofe {Hfin: FiniteIndex SI} {HA: Cofe A} {HB : Cofe B} : Cofe ofe_isoO.
  Proof.
    unshelve refine (iso_finite_cofe_subtype'
      (λ I : prodO (A -n> B) (B -n> A),
        (∀ y, I.1 (I.2 y) ≡ y) ∧ (∀ x, I.2 (I.1 x) ≡ x))
      (λ I HI, OfeIso (I.1) (I.2) (proj1 HI) (proj2 HI))
      (λ I, (ofe_iso_1 I, ofe_iso_2 I)) _ _ _ _).
    - simpl. split; first apply ofe_iso_12. apply ofe_iso_21.
    - by intros ?.
    - done.
    - apply limit_preserving_and; apply limit_preserving_forall=> ?;
    apply limit_preserving_equiv; first [intros ???; done|solve_proper].
  Qed.
End ofe_iso.

Global Arguments ofe_isoO {_} _ _.

Program Definition iso_ofe_refl `{SI: indexT} {A: ofe} : ofe_iso A A := OfeIso cid cid _ _.
Solve Obligations with done.

Definition iso_ofe_sym `{SI: indexT} {A B : ofe} (I : ofe_iso A B) : ofe_iso B A :=
  OfeIso (ofe_iso_2 I) (ofe_iso_1 I) (ofe_iso_21 I) (ofe_iso_12 I).
Global Instance iso_ofe_sym_ne {SI: indexT}  {A B : ofe} : NonExpansive (iso_ofe_sym (A:=A) (B:=B)).
Proof. intros n I1 I2 []; split; simpl; by f_equiv. Qed.

Program Definition iso_ofe_trans `{SI: indexT} {A B C : ofe}
    (I : ofe_iso A B) (J : ofe_iso B C) : ofe_iso A C :=
  OfeIso (ofe_iso_1 J ◎ ofe_iso_1 I) (ofe_iso_2 I ◎ ofe_iso_2 J) _ _.
Next Obligation. intros SI A B C I J z; simpl. by rewrite !ofe_iso_12. Qed.
Next Obligation. intros SI A B C I J z; simpl. by rewrite !ofe_iso_21. Qed.
Global Instance iso_ofe_trans_ne `{SI : indexT} {A B C : ofe} : NonExpansive2 (iso_ofe_trans (A:=A) (B:=B) (C:=C)).
Proof. intros n I1 I2 [] J1 J2 []; split; simpl; by f_equiv. Qed.

Program Definition iso_ofe_cong `{SI : indexT} (F : oFunctor) `{!Cofe A, !Cofe B}
    (I : ofe_iso A B) : ofe_iso (oFunctor_apply F A) (oFunctor_apply F B) :=
  OfeIso (oFunctor_map F (ofe_iso_2 I, ofe_iso_1 I))
    (oFunctor_map F (ofe_iso_1 I, ofe_iso_2 I)) _ _.
Next Obligation.
  intros SI F A ? B ? I x. rewrite -oFunctor_map_compose -{2}(oFunctor_map_id F x).
  apply equiv_dist=> n.
  apply oFunctor_map_ne; split=> ? /=; by rewrite ?ofe_iso_12 ?ofe_iso_21.
Qed.
Next Obligation.
  intros SI F A ? B ? I y. rewrite -oFunctor_map_compose -{2}(oFunctor_map_id F y).
  apply equiv_dist=> n.
  apply oFunctor_map_ne; split=> ? /=; by rewrite ?ofe_iso_12 ?ofe_iso_21.
Qed.
Global Instance iso_ofe_cong_ne `{SI : indexT} (F : oFunctor) `{!Cofe A, !Cofe B} :
  NonExpansive (iso_ofe_cong F (A:=A) (B:=B)).
Proof. intros n I1 I2 []; split; simpl; by f_equiv. Qed.
Global Instance iso_ofe_cong_contractive `{SI : indexT} (F : oFunctor) `{!Cofe A, !Cofe B} :
  oFunctorContractive F → Contractive (iso_ofe_cong F (A:=A) (B:=B)).
Proof.
  intros ? n I1 I2 HI; split; simpl.
  (* FIXME: simplify when f_contractive is fixed *)
  (*f_contractive; by destruct HI. *)
  all: f_contractive; intros m Hm; specialize (HI m Hm); split.
  1,4: by apply ofe_iso_2_ne. all: by apply ofe_iso_1_ne.
Qed.
