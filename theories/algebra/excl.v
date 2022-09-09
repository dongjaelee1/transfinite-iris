From iris.algebra Require Export cmra.
From iris.prelude Require Import options.

Local Arguments validN _ _ _ _ !_ /.
Local Arguments valid _ _  !_ /.

Inductive excl (A : Type) :=
  | Excl : A → excl A
  | ExclBot : excl A.
Global Arguments Excl {_} _.
Global Arguments ExclBot {_}.

Global Instance: Params (@Excl) 1 := {}.
Global Instance: Params (@ExclBot) 1 := {}.

Notation excl' A := (option (excl A)).
Notation Excl' x := (Some (Excl x)).
Notation ExclBot' := (Some ExclBot).

Global Instance maybe_Excl {A} : Maybe (@Excl A) := λ x,
  match x with Excl a => Some a | _ => None end.

Section excl.
Context {SI} {A : ofe SI}.
Implicit Types a b : A.
Implicit Types x y : excl A.

(* Cofe *)
Inductive excl_equiv : Equiv (excl A) :=
  | Excl_equiv a b : a ≡ b → Excl a ≡ Excl b
  | ExclBot_equiv : ExclBot ≡ ExclBot.
Existing Instance excl_equiv.
Inductive excl_dist : Dist SI (excl A) :=
  | Excl_dist a b n : a ≡{n}≡ b → Excl a ≡{n}≡ Excl b
  | ExclBot_dist n : ExclBot ≡{n}≡ ExclBot.
Existing Instance excl_dist.

Global Instance Excl_ne : NonExpansive (@Excl A).
Proof. by constructor. Qed.
Global Instance Excl_proper : Proper ((≡) ==> (≡)) (@Excl A).
Proof. by constructor. Qed.
Global Instance Excl_inj : Inj (≡) (≡) (@Excl A).
Proof. by inversion_clear 1. Qed.
Global Instance Excl_dist_inj n : Inj (dist n) (dist n) (@Excl A).
Proof. by inversion_clear 1. Qed.

Definition excl_ofe_mixin : OfeMixin SI (excl A).
Proof.
  apply (iso_ofe_mixin (maybe Excl)).
  - by intros [a|] [b|]; split; inversion_clear 1; constructor.
  - by intros n [a|] [b|]; split; inversion_clear 1; constructor.
Qed.
Canonical Structure exclO : ofe SI := Ofe (excl A) excl_ofe_mixin.

Global Instance excl_cofe `{!Cofe A} : Cofe exclO.
Proof.
  apply (iso_cofe (from_option Excl ExclBot) (maybe Excl)).
  - by intros n [a|] [b|]; split; inversion_clear 1; constructor.
  - by intros []; constructor.
Qed.

Global Instance excl_ofe_discrete : OfeDiscrete A → OfeDiscrete exclO.
Proof. by inversion_clear 2; constructor; apply (discrete _). Qed.
Global Instance excl_leibniz : LeibnizEquiv A → LeibnizEquiv (excl A).
Proof. by destruct 2; f_equal; apply leibniz_equiv. Qed.

Global Instance Excl_discrete a : Discrete a → Discrete (Excl a).
Proof. by inversion_clear 2; constructor; apply (discrete _). Qed.
Global Instance ExclBot_discrete : Discrete (@ExclBot A).
Proof. by inversion_clear 1; constructor. Qed.

(* CMRA *)
Local Instance excl_valid_instance : Valid (excl A) := λ x,
  match x with Excl _ => True | ExclBot => False end.
Local Instance excl_validN_instance : ValidN SI (excl A) := λ n x,
  match x with Excl _ => True | ExclBot => False end.
Local Instance excl_pcore_instance : PCore (excl A) := λ _, None.
Local Instance excl_op_instance : Op (excl A) := λ x y, ExclBot.

Lemma excl_cmra_mixin : CmraMixin SI (excl A).
Proof.
  split; try discriminate.
  - by intros [] n; destruct 1; constructor.
  - by destruct 1; intros ?.
  - intros x; split; [done|]. by move=> /(_ zero).
  - intros n m [?|]; simpl; auto.
  - by intros [?|] [?|] [?|]; constructor.
  - by intros [?|] [?|]; constructor.
  - by intros n [?|] [?|].
  - intros n x [?|] [?|] ? Hx; eexists _, _; inversion_clear Hx; eauto.
Qed.
Canonical Structure exclR := Cmra SI (excl A) excl_cmra_mixin.

Global Instance excl_cmra_discrete : OfeDiscrete A → CmraDiscrete exclR.
Proof. split; first apply _. by intros []. Qed.

(** Exclusive *)
Global Instance excl_exclusive x : Exclusive x.
Proof. by destruct x; intros n []. Qed.

(** Option excl *)
Lemma excl_validN_inv_l n mx a : ✓{n} (Excl' a ⋅ mx) → mx = None.
Proof. by destruct mx. Qed.
Lemma excl_validN_inv_r n mx a : ✓{n} (mx ⋅ Excl' a) → mx = None.
Proof. by destruct mx. Qed.

Lemma Excl_includedN n a b  : Excl' a ≼{n} Excl' b ↔ a ≡{n}≡ b.
Proof.
  split; [|by intros ->]. by intros [[c|] Hb%(inj Some)]; inversion_clear Hb.
Qed.
Lemma Excl_included a b : Excl' a ≼ Excl' b ↔ a ≡ b.
Proof.
  split; [|by intros ->]. by intros [[c|] Hb%(inj Some)]; inversion_clear Hb.
Qed.
End excl.

Global Arguments exclO {_} _.
Global Arguments exclR {_} _.

(* Functor *)
Definition excl_map {A B} (f : A → B) (x : excl A) : excl B :=
  match x with Excl a => Excl (f a) | ExclBot => ExclBot end.
Lemma excl_map_id {A} (x : excl A) : excl_map id x = x.
Proof. by destruct x. Qed.
Lemma excl_map_compose {A B C} (f : A → B) (g : B → C) (x : excl A) :
  excl_map (g ∘ f) x = excl_map g (excl_map f x).
Proof. by destruct x. Qed.
Lemma excl_map_ext {SI} {A B : ofe SI} (f g : A → B) x :
  (∀ x, f x ≡ g x) → excl_map f x ≡ excl_map g x.
Proof. by destruct x; constructor. Qed.
Global Instance excl_map_ne {SI} {A B : ofe SI} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@excl_map A B).
Proof. by intros f f' Hf; destruct 1; constructor; apply Hf. Qed.
Global Instance excl_map_cmra_morphism {SI} {A B : ofe SI} (f : A → B) :
  NonExpansive f → CmraMorphism (excl_map f).
Proof. split; try done; try apply _. by intros n [a|]. Qed.
Definition exclO_map {SI} {A B: ofe SI} (f : A -n> B) : exclO A -n> exclO B :=
  OfeMor (excl_map f).
Global Instance exclO_map_ne {SI} (A B: ofe SI) : NonExpansive (@exclO_map SI A B).
Proof. by intros n f f' Hf []; constructor; apply Hf. Qed.

Program Definition exclRF {SI} (F : oFunctor SI) : rFunctor SI := {|
  rFunctor_car A B := (exclR (oFunctor_car F A B));
  rFunctor_map A1 A2 B1 B2 fg := exclO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros SI F A1 A2 B1 B2 n x1 x2 ??. by apply exclO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros SI F A B x; simpl. rewrite -{2}(excl_map_id x).
  apply excl_map_ext=>y. by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros SI F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -excl_map_compose.
  apply excl_map_ext=>y; apply oFunctor_map_compose.
Qed.

Global Instance exclRF_contractive {SI} (F: oFunctor SI) :
  oFunctorContractive F → rFunctorContractive (exclRF F).
Proof.
  intros A1 A2 B1 B2 n x1 x2 ??. by apply exclO_map_ne, oFunctor_map_contractive.
Qed.
