From stdpp Require Import gmap.
From iris.algebra Require Import agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export own.
From iris.prelude Require Import options.
Import uPred.

(* "Saved anything" -- this can give you saved propositions, saved predicates,
   saved whatever-you-like. *)

Class savedAnythingG `{SI : indexT} (Σ : gFunctors) (F : oFunctor) := SavedAnythingG {
  saved_anything_inG :> inG Σ (agreeR (oFunctor_apply F (iPropO Σ)));
  saved_anything_contractive : oFunctorContractive F (* NOT an instance to avoid cycles with [subG_savedAnythingΣ]. *)
}.
Definition savedAnythingΣ `{SI : indexT} (F : oFunctor) `{!oFunctorContractive F} : gFunctors :=
  #[ GFunctor (agreeRF F) ].

Global Instance subG_savedAnythingΣ `{SI : indexT} {Σ} {F : oFunctor} `{!oFunctorContractive F} :
  subG (savedAnythingΣ F) Σ → savedAnythingG Σ F.
Proof. solve_inG. Qed.

Definition saved_anything_own `{SI : indexT} {Σ: gFunctors} {F} `{!savedAnythingG Σ F}
    (γ : gname) (x : oFunctor_apply F (iPropO Σ)) : iProp Σ :=
  own γ (to_agree x).
Global Typeclasses Opaque saved_anything_own.
Global Instance: Params (@saved_anything_own) 5 := {}.

Section saved_anything.
  Context `{SI : indexT} {Σ: gFunctors} {F} `{!savedAnythingG Σ F}.
  Implicit Types x y : oFunctor_apply F (iPropO Σ).
  Implicit Types γ : gname.

  Global Instance saved_anything_persistent γ x :
    Persistent (saved_anything_own γ x).
  Proof. rewrite /saved_anything_own; apply _. Qed.

  Global Instance saved_anything_ne γ : NonExpansive (saved_anything_own γ).
  Proof. solve_proper. Qed.
  Global Instance saved_anything_proper γ : Proper ((≡) ==> (≡)) (saved_anything_own γ).
  Proof. solve_proper. Qed.

  Lemma saved_anything_alloc_strong x (I : gname → Prop) :
    pred_infinite I →
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_anything_own γ x.
  Proof. intros ?. by apply own_alloc_strong. Qed.

  Lemma saved_anything_alloc_cofinite x (G : gset gname) :
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_anything_own γ x.
  Proof. by apply own_alloc_cofinite. Qed.

  Lemma saved_anything_alloc x : ⊢ |==> ∃ γ, saved_anything_own γ x.
  Proof. by apply own_alloc. Qed.

  Lemma saved_anything_agree γ x y :
    saved_anything_own γ x -∗ saved_anything_own γ y -∗ x ≡ y.
  Proof.
    iIntros "Hx Hy". rewrite /saved_anything_own.
    iDestruct (own_valid_2 with "Hx Hy") as "Hv".
    by rewrite agree_validI agree_equivI.
  Qed.
End saved_anything.

(** Provide specialized versions of this for convenience. **)

(* Saved propositions. *)
Notation savedPropG Σ := (savedAnythingG Σ (▶ (∙ _))).
Notation savedPropΣ := (savedAnythingΣ (▶ (∙ _))).

Definition saved_prop_own `{SI : indexT} {Σ : gFunctors} `{!savedPropG Σ} (γ : gname) (P: iProp Σ) :=
  saved_anything_own (F := ▶ (∙ _)) γ (Next P).

Global Instance saved_prop_own_contractive `{SI : indexT} {Σ : gFunctors} `{!savedPropG Σ} γ :
  Contractive (saved_prop_own γ).
Proof. solve_contractive. Qed.

Lemma saved_prop_alloc_strong `{SI : indexT} {Σ : gFunctors} `{!savedPropG Σ} (I : gname → Prop) (P: iProp Σ) :
  pred_infinite I →
  ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_prop_own γ P.
Proof. iIntros (?). by iApply saved_anything_alloc_strong. Qed.

Lemma saved_prop_alloc_cofinite `{SI : indexT} {Σ : gFunctors} `{!savedPropG Σ} (G : gset gname) (P: iProp Σ) :
  ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_prop_own γ P.
Proof. iApply saved_anything_alloc_cofinite. Qed.

Lemma saved_prop_alloc `{SI : indexT} {Σ : gFunctors} `{!savedPropG Σ} (P: iProp Σ) :
  ⊢ |==> ∃ γ, saved_prop_own γ P.
Proof. iApply saved_anything_alloc. Qed.

Lemma saved_prop_agree `{SI : indexT} {Σ : gFunctors} `{!savedPropG Σ} γ P Q :
  saved_prop_own γ P -∗ saved_prop_own γ Q -∗ ▷ (P ≡ Q).
Proof.
  iIntros "HP HQ". iApply later_equivI.
  iApply (saved_anything_agree (F := ▶ (∙ _)) with "HP HQ").
Qed.

(* Saved predicates. *)
Notation savedPredG Σ A := (savedAnythingG Σ (A -d> ▶ (∙ _))).
Notation savedPredΣ A := (savedAnythingΣ (A -d> ▶ (∙ _))).

Definition saved_pred_own `{SI : indexT} {Σ : gFunctors} `{!savedPredG Σ A} (γ : gname) (Φ : A → iProp Σ) :=
  saved_anything_own (F := A -d> ▶ (∙ _)) γ (OfeMor Next ∘ Φ).

Global Instance saved_pred_own_contractive `{SI : indexT} {Σ : gFunctors} `{!savedPredG Σ A} γ :
  Contractive (saved_pred_own γ : (A -d> iPropO Σ) → iProp Σ).
Proof.
  (* TODO: fix this once f_contractive is fixed *)
  solve_proper_prepare.
  f_equiv. intros a; simpl. f_contractive.
  intros ??. by apply H.
Qed.

Lemma saved_pred_alloc_strong `{SI : indexT} {Σ : gFunctors} `{!savedPredG Σ A} (I : gname → Prop) (Φ : A → iProp Σ) :
  pred_infinite I →
  ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_pred_own γ Φ.
Proof. iIntros (?). by iApply saved_anything_alloc_strong. Qed.

Lemma saved_pred_alloc_cofinite `{SI : indexT} {Σ : gFunctors} `{!savedPredG Σ A} (G : gset gname) (Φ : A → iProp Σ) :
  ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_pred_own γ Φ.
Proof. iApply saved_anything_alloc_cofinite. Qed.

Lemma saved_pred_alloc `{SI : indexT} {Σ : gFunctors} `{!savedPredG Σ A} (Φ : A → iProp Σ) :
  ⊢ |==> ∃ γ, saved_pred_own γ Φ.
Proof. iApply saved_anything_alloc. Qed.

(* We put the `x` on the outside to make this lemma easier to apply. *)
Lemma saved_pred_agree `{SI : indexT} {Σ : gFunctors} `{!savedPredG Σ A} γ Φ Ψ x :
  saved_pred_own γ Φ -∗ saved_pred_own γ Ψ -∗ ▷ (Φ x ≡ Ψ x).
Proof.
  unfold saved_pred_own. iIntros "#HΦ #HΨ /=". iApply later_equivI.
  iDestruct (saved_anything_agree (F := A -d> ▶ (∙ _)) with "HΦ HΨ") as "Heq".
  by iDestruct (discrete_fun_equivI with "Heq") as "?".
Qed.
