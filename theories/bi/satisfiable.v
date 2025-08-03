From iris.bi Require Import
  derived_connectives derived_laws
  derived_laws_later notation interface
  plainly updates big_op.
From iris.prelude Require Import options.

Import interface.bi.
Import derived_laws.bi.
Import derived_laws_later.bi.

Section satisfiable.
  Context `{SI: indexT} {PROP: bi}.

  Class Satisfiable (sat: PROP → Prop) := {
    sat_mono P Q: (P ⊢ Q) → sat P →  sat Q;
    sat_elim φ: sat (⌜φ⌝)%I → φ;
  }.

  Class SatisfiableBUpd `{!BiBUpd PROP} (sat: PROP → Prop) := {
    sat_bupd P: sat (|==> P)%I → sat P;
  }.

  Class SatisfiableLater (sat: PROP → Prop) := {
    sat_later P: sat (▷ P)%I → sat P;
  }.

  Class SatisfiableExists (X: Type) (sat: PROP → Prop) := {
    sat_exists Φ: sat (∃ x: X, Φ x)%I → ∃ x: X, sat (Φ x);
  }.

  Notation SatisfiableFiniteExists := (SatisfiableExists bool).

  Section satisfiable.
    Context {sat: PROP → Prop} `{Sat: Satisfiable sat}.

    Global Instance sat_equiv: Proper (equiv ==> iff) sat.
    Proof using Sat.
      intros P Q HPQ. split; intros H'; eapply sat_mono, H'; by rewrite HPQ.
    Qed.

    Lemma sat_or `{SatisfiableFiniteExists sat} P Q:
      sat (P ∨ Q)%I → sat P ∨ sat Q.
    Proof using Sat.
      rewrite bi.or_alt; intros [[] ?] % sat_exists; eauto.
    Qed.

    Lemma sat_big_or `{SatisfiableFiniteExists sat} {X} P A:
      sat ([∨ list] x ∈ A, P x)%I → ∃ x: X, x ∈ A ∧ sat (P x).
    Proof using Sat.
      induction A as [|a A IH]; simpl.
      - intros [] % sat_elim.
      - intros [HP|HP] % sat_or; first by eauto using list_elem_of_here.
        destruct IH as [? []]; eauto using list_elem_of_further.
    Qed.

    Lemma sat_sep `{!BiAffine PROP} P Q:
      sat (P ∗ Q)%I → sat P ∧ sat Q.
    Proof using Sat.
      intros Hsat; split; eapply sat_mono, Hsat.
      - eapply bi.sep_elim_l, _.
      - eapply bi.sep_elim_r, _.
    Qed.

    Lemma sat_forall {X} (x: X) P: sat (∀ x, P x)%I → sat (P x).
    Proof using Sat. intros Hs; eapply sat_mono, Hs. apply forall_elim. Qed.

    Lemma sat_impl P Q: sat (P → Q)%I → (True ⊢ P) → sat Q.
    Proof using Sat.
      intros Hs Hent; eapply sat_mono, Hs.
      etrans; last apply impl_elim_r.
      apply bi.and_intro; last reflexivity.
      etrans; last apply Hent. by eapply pure_intro.
    Qed.

    Lemma sat_wand P Q: sat (P -∗ Q)%I → (True ⊢ P) → sat Q.
    Proof using Sat.
      intros Hs Hent; eapply sat_mono, Hs.
      erewrite True_sep_2.
      rewrite Hent. apply wand_elim_r.
    Qed.

    Lemma sat_pers `{!BiAffine PROP} P: sat (<pers> P)%I → sat P.
    Proof using Sat.
      intros Hs; eapply sat_mono, Hs.
      apply persistently_elim. apply _.
    Qed.

    Lemma sat_intuitionistically P: sat (□ P)%I → sat P.
    Proof using Sat.
      intros Hs; eapply sat_mono, Hs.
      apply intuitionistically_elim.
    Qed.

  End satisfiable.


  Section satisfiable_frame.
    Context {sat: PROP → Prop} `{Sat: Satisfiable sat}.

    Definition sat_frame (F P: PROP) := sat (F ∗ P)%I.

    Global Instance sat_frame_satisifable `{Aff: !BiAffine PROP} F: Satisfiable (sat_frame F).
    Proof using Sat.
      split.
      - intros P Q HPQ; rewrite /sat_frame; eapply sat_mono.
        by rewrite HPQ.
      - by intros φ [_ Hφ % sat_elim] % sat_sep.
    Qed.

    Global Instance sat_frame_satisfiable_bupd `{!BiBUpd PROP} `{!SatisfiableBUpd sat} F:
      SatisfiableBUpd (sat_frame F).
    Proof using Sat.
      split. intros P Hsat; rewrite /sat_frame; eapply sat_bupd, sat_mono, Hsat.
      apply bupd_frame_l.
    Qed.

    Global Instance sat_frame_satisfiable_later `{!SatisfiableLater sat} F:
      SatisfiableLater (sat_frame F).
    Proof using Sat.
      split. intros P Hsat; rewrite /sat_frame; eapply sat_later, sat_mono, Hsat.
      by rewrite -bi.later_sep_2 -(bi.later_intro F).
    Qed.

    Global Instance sat_frame_satisfiable_exists X `{!SatisfiableExists X sat} F:
    SatisfiableExists X (sat_frame F).
    Proof using Sat.
      split. intros P Hsat; rewrite /sat_frame; eapply sat_exists, sat_mono, Hsat.
      by rewrite bi.sep_exist_l.
    Qed.

    Lemma sat_frame_move F P:
      sat_frame F P ↔ sat_frame emp%I (F ∗ P)%I.
    Proof using Sat.
      by rewrite /sat_frame bi.emp_sep.
    Qed.

    Lemma sat_sat_frame P:
      sat_frame emp%I P ↔ sat P.
    Proof using Sat.
      by rewrite /sat_frame bi.emp_sep.
    Qed.

    End satisfiable_frame.
End satisfiable.

