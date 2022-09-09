From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap_view list.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.
Import uPred.

Local Notation proph_map P V := (gmap P (list V)).
Definition proph_val_list (P V : Type) := list (P * V).

(** The CMRA we need. *)
Class proph_mapPreG {SI} (P V : Type) (Σ : gFunctors SI) `{Countable P} := {
  proph_map_preG_inG :> inG Σ (gmap_viewR P (listO $ leibnizO SI V))
}.

Class proph_mapG {SI} (P V : Type) (Σ : gFunctors SI) `{Countable P} := ProphMapG {
  proph_map_inG :> proph_mapPreG P V Σ;
  proph_map_name : gname
}.
Global Arguments proph_map_name {_ _ _ _ _ _} _ : assert.

Definition proph_mapΣ {SI} (P V : Type) `{Countable P} : gFunctors SI :=
  #[GFunctor (gmap_viewR P (listO $ leibnizO SI V))].

Global Instance subG_proph_mapPreG {SI} {Σ: gFunctors SI} {P V} `{Countable P} :
  subG (proph_mapΣ P V) Σ → proph_mapPreG P V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context {SI} {Σ: gFunctors SI} `{pG : proph_mapG SI P V Σ}.
  Implicit Types pvs : proph_val_list P V.
  Implicit Types R : proph_map P V.
  Implicit Types p : P.

  (** The list of resolves for [p] in [pvs]. *)
  Fixpoint proph_list_resolves pvs p : list V :=
    match pvs with
    | []         => []
    | (q,v)::pvs => if decide (p = q) then v :: proph_list_resolves pvs p
                    else proph_list_resolves pvs p
    end.

  Definition proph_resolves_in_list R pvs :=
    map_Forall (λ p vs, vs = proph_list_resolves pvs p) R.

  Definition proph_map_interp pvs (ps : gset P) : iProp Σ :=
    (∃ R, ⌜proph_resolves_in_list R pvs ∧
          dom (gset _) R ⊆ ps⌝ ∗
          own (proph_map_name pG) (gmap_view_auth (V:=listO $ leibnizO SI V) 1 R))%I.

  Definition proph_def (p : P) (vs : list V) : iProp Σ :=
    own (proph_map_name pG) (gmap_view_frag (V:=listO $ leibnizO SI V) p (DfracOwn 1) vs).

  Definition proph_aux : seal (@proph_def). Proof. by eexists. Qed.
  Definition proph := proph_aux.(unseal).
  Definition proph_eq : @proph = @proph_def := proph_aux.(seal_eq).
End definitions.

Section list_resolves.
  Context {P V : Type} `{Countable P}.
  Implicit Type pvs : proph_val_list P V.
  Implicit Type p : P.
  Implicit Type R : proph_map P V.

  Lemma resolves_insert pvs p R :
    proph_resolves_in_list R pvs →
    p ∉ dom (gset _) R →
    proph_resolves_in_list (<[p := proph_list_resolves pvs p]> R) pvs.
  Proof.
    intros Hinlist Hp q vs HEq.
    destruct (decide (p = q)) as [->|NEq].
    - rewrite lookup_insert in HEq. by inversion HEq.
    - rewrite lookup_insert_ne in HEq; last done. by apply Hinlist.
  Qed.
End list_resolves.

(** This variant of [proph_map_init] should only be used when absolutely needed.
The key difference to [proph_map_init] is that the [inG] instances in the new
[proph_mapPreG] instance are related to the original [proph_mapPreG] instance,
whereas [proph_map_init] forgets about that relation. *)
Lemma proph_map_init_names {SI: indexT} {Σ: gFunctors SI} `{Countable P, !proph_mapPreG P V Σ} pvs ps :
  ⊢ |==> ∃ γ, let H := ProphMapG SI P V Σ _ _ _ γ in proph_map_interp pvs ps.
Proof.
  iMod (own_alloc (gmap_view_auth 1 ∅)) as (γ) "Hh".
  { apply gmap_view_auth_valid. }
  iModIntro. iExists γ, ∅. iSplit; last by iFrame.
  iPureIntro. done.
Qed.

Lemma proph_map_init {SI: indexT} {Σ: gFunctors SI} `{Countable P, !proph_mapPreG P V Σ} pvs ps :
  ⊢ |==> ∃ _ : proph_mapG P V Σ, proph_map_interp pvs ps.
Proof.
  iMod (proph_map_init_names pvs ps) as (γ) "H". iModIntro.
  by iExists (ProphMapG SI P V Σ _ _ _ γ).
Qed.

Section proph_map.
  Context {SI} {Σ: gFunctors SI} `{proph_mapG SI P V Σ}.
  Implicit Types p : P.
  Implicit Types v : V.
  Implicit Types vs : list V.
  Implicit Types R : proph_map P V.
  Implicit Types ps : gset P.

  (** General properties of mapsto *)
  Global Instance proph_timeless p vs : Timeless (proph p vs).
  Proof. rewrite proph_eq /proph_def. apply _. Qed.

  Lemma proph_exclusive p vs1 vs2 :
    proph p vs1 -∗ proph p vs2 -∗ False.
  Proof.
    rewrite proph_eq /proph_def. iIntros "Hp1 Hp2".
    iCombine "Hp1 Hp2" as "Hp".
    iDestruct (own_valid with "Hp") as %[Hp _]%gmap_view_frag_op_valid_L.
    done.
  Qed.

  Lemma proph_map_new_proph p ps pvs :
    p ∉ ps →
    proph_map_interp pvs ps ==∗
    proph_map_interp pvs ({[p]} ∪ ps) ∗ proph p (proph_list_resolves pvs p).
  Proof.
    iIntros (Hp) "HR". iDestruct "HR" as (R) "[[% %] H●]".
    rewrite proph_eq /proph_def.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply (gmap_view_alloc _ p (DfracOwn 1)); last done.
      apply (not_elem_of_dom (D:=gset P)). set_solver. }
    iModIntro. iFrame.
    iExists (<[p := proph_list_resolves pvs p]> R).
    iFrame. iPureIntro. split.
    - apply resolves_insert; first done. set_solver.
    - rewrite dom_insert. set_solver.
  Qed.

  Lemma proph_map_resolve_proph p v pvs ps vs :
    proph_map_interp ((p,v) :: pvs) ps ∗ proph p vs ==∗
    ∃vs', ⌜vs = v::vs'⌝ ∗ proph_map_interp pvs ps ∗ proph p vs'.
  Proof.
    iIntros "[HR Hp]". iDestruct "HR" as (R) "[HP H●]". iDestruct "HP" as %[Hres Hdom].
    rewrite /proph_map_interp proph_eq /proph_def.
    iDestruct (own_valid_2 with "H● Hp") as %[_ HR]%gmap_view_both_valid_L.
    assert (vs = v :: proph_list_resolves pvs p) as ->.
    { rewrite (Hres p vs HR). simpl. by rewrite decide_True. }
    iMod (own_update_2 with "H● Hp") as "[H● H◯]".
    { eapply gmap_view_update. }
    iModIntro. iExists (proph_list_resolves pvs p). iFrame. iSplitR.
    - iPureIntro. done.
    - iExists _. iFrame. iPureIntro. split.
      + intros q ws HEq. destruct (decide (p = q)) as [<-|NEq].
        * rewrite lookup_insert in HEq. by inversion HEq.
        * rewrite lookup_insert_ne in HEq; last done.
          rewrite (Hres q ws HEq).
          simpl. rewrite decide_False; done.
      + assert (p ∈ dom (gset P) R) by exact: elem_of_dom_2.
        rewrite dom_insert. set_solver.
  Qed.
End proph_map.
