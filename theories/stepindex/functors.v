From iris.prelude Require Import options.
From iris.algebra Require Export ofe cmra.
From iris.algebra Require Import
  gmap gmap_view agree excl list vector auth
  max_prefix_list mono_list excl_auth dfrac_agree.
From transfinite.stepindex Require Import ofe.


(** * OFE → OFE Functors *)
Record tFunctor {SI : sidx} := TFunctor {
  tFunctor_car : ∀ A B, ofe;
  tFunctor_map  {A1 A2 B1 B2}:
    ((A2 -n> A1) * (B1 -n> B2)) → tFunctor_car A1 B1 -n> tFunctor_car A2 B2;
  tFunctor_map_ne {A1 A2 B1 B2}:
    NonExpansive (@tFunctor_map A1 A2 B1 B2);
  tFunctor_map_id {A B} (x : tFunctor_car A B) :
    tFunctor_map (cid,cid) x ≡ x;
  tFunctor_map_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    tFunctor_map (f◎g, g'◎f') x ≡ tFunctor_map (g,g') (tFunctor_map (f,f') x)
}.
Global Existing Instance tFunctor_map_ne.
Global Instance: Params (@tFunctor_map) 6 := {}.

Declare Scope tFunctor_scope.
Delimit Scope tFunctor_scope with TF.
Bind Scope tFunctor_scope with tFunctor.

Class tFunctorContractive {SI : sidx} (F : tFunctor) :=
  #[export] tFunctor_map_contractive `{A1 : ofe} `{A2 : ofe} `{B1 : ofe} `{B2 : ofe} ::
    Contractive  (@tFunctor_map SI F A1 A2 B1 B2).
Global Hint Mode tFunctorContractive - ! : typeclass_instances.

(** We add the coercion because there is no more Cofe argument *)
Definition tFunctor_apply {SI : sidx} (F: tFunctor) (A: ofe) : ofe := tFunctor_car F A A.
Coercion tFunctor_apply : tFunctor >-> Funclass.

Program Definition constTF {SI : sidx} (B : ofe) : tFunctor :=
  {| tFunctor_car A1 A2 := B; tFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion constTF : ofe >-> tFunctor.

Global Instance constTF_contractive {SI : sidx} B : tFunctorContractive (constTF B).
Proof. rewrite /tFunctorContractive; apply _. Qed.

(** OFE → CMRA Functors *)
Record trFunctor {SI : sidx} := TRFunctor {
  trFunctor_car : ∀ (A: ofe) (B: ofe), cmra;
  trFunctor_map {A1 A2 B1 B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → trFunctor_car A1 B1 -n> trFunctor_car A2 B2;
  trFunctor_map_ne A1 A2 B1 B2:
    NonExpansive (@trFunctor_map A1 A2 B1 B2);
  trFunctor_map_id {A B} (x : trFunctor_car A B) :
    trFunctor_map (cid,cid) x ≡ x;
  trFunctor_map_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    trFunctor_map (f◎g, g'◎f') x ≡ trFunctor_map (g,g') (trFunctor_map (f,f') x);
  trFunctor_mor {A1 A2 B1 B2}
      (fg : (A2 -n> A1) * (B1 -n> B2)) :
    CmraMorphism (trFunctor_map fg)
}.
Global Existing Instances trFunctor_map_ne trFunctor_mor.
Global Instance: Params (@trFunctor_map) 6 := {}.

Declare Scope trFunctor_scope.
Delimit Scope trFunctor_scope with TRF.
Bind Scope trFunctor_scope with trFunctor.

Class trFunctorContractive {SI : sidx} (F : trFunctor) :=
  #[export] trFunctor_map_contractive A1 A2 B1 B2 ::
    Contractive (@trFunctor_map SI F A1 A2 B1 B2).

Definition trFunctor_apply {SI : sidx} (F: trFunctor) (A: ofe) `{!Cofe A} : cmra :=
  trFunctor_car F A A.

Program Definition trFunctor_to_tFunctor {SI : sidx} (F: trFunctor) : tFunctor := {|
  tFunctor_car A B := trFunctor_car F A B;
  tFunctor_map A1 A2 B1 B2 fg := trFunctor_map F fg
|}.
Next Obligation.
  intros F A B x. simpl in *. apply trFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. simpl in *.
  apply trFunctor_map_compose.
Qed.

Global Instance trFunctor_to_tFunctor_contractive {SI : sidx} (F: trFunctor) :
  trFunctorContractive F → tFunctorContractive (trFunctor_to_tFunctor F).
Proof.
  intros A1 A2 B1 B2 n f g Hfg. apply trFunctor_map_contractive.
Qed.

Program Definition trFunctor_tFunctor_compose {SI : sidx} (F1 : trFunctor) (F2 : tFunctor) : trFunctor := {|
  trFunctor_car A B := trFunctor_car F1 (tFunctor_car F2 B A) (tFunctor_car F2 A B);
  trFunctor_map A1 A2 B1 B2 'fg :=
    trFunctor_map F1 (tFunctor_map F2 (fg.2,fg.1),tFunctor_map F2 fg)
|}.
Next Obligation.
  intros SI F1 F2 A1 A2 B1 B2 n [f1 g1] [f2 g2] [??]; simpl in *.
  apply trFunctor_map_ne; split; apply tFunctor_map_ne; by split.
Qed.
Next Obligation.
  intros SI F1 F2 A B x; simpl in *. rewrite -{2}(trFunctor_map_id F1 x).
  apply equiv_dist=> n. apply trFunctor_map_ne.
  split=> y /=; by rewrite !tFunctor_map_id.
Qed.
Next Obligation.
  intros SI F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' x; simpl in *.
  rewrite -trFunctor_map_compose. apply equiv_dist=> n. apply trFunctor_map_ne.
  split=> y /=; by rewrite !tFunctor_map_compose.
Qed.
Global Instance trFunctor_tFunctor_compose_contractive_1 {SI : sidx} (F1 : trFunctor) (F2 : tFunctor) :
  trFunctorContractive F1 → trFunctorContractive (trFunctor_tFunctor_compose F1 F2).
Proof.
  intros ? A1 A2 B1 B2 n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_contractive. destruct Hfg; split; simpl in *; apply tFunctor_map_ne; by split.
Qed.
Global Instance trFunctor_tFunctor_compose_contractive_2 {SI : sidx} (F1 : trFunctor) (F2 : tFunctor):
  tFunctorContractive F2 → trFunctorContractive (trFunctor_tFunctor_compose F1 F2).
Proof.
  intros ? A1 A2 B1 B2 n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_equiv; split; simpl in *; f_contractive; destruct Hfg; by split.
Qed.

Program Definition constTRF {SI : sidx} (B : cmra) : trFunctor :=
  {| trFunctor_car A1 A2 := B; trFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion constTRF : cmra >-> trFunctor.

Global Instance constTRF_contractive {SI : sidx} (B : cmra): trFunctorContractive (constTRF B).
Proof. rewrite /trFunctorContractive; apply _. Qed.


(** OFE → UCMRA Functors *)
Record turFunctor {SI : sidx} := TURFunctor {
  turFunctor_car : ∀ A B, ucmra;
  turFunctor_map {A1 A2 B1 B2}:
    ((A2 -n> A1) * (B1 -n> B2)) → turFunctor_car A1 B1 -n> turFunctor_car A2 B2;
  turFunctor_map_ne {A1 A2 B1 B2 : ofe}:
    NonExpansive (@turFunctor_map A1 A2 B1 B2);
  turFunctor_map_id {A B : ofe} (x : turFunctor_car A B) :
    turFunctor_map (cid,cid) x ≡ x;
  turFunctor_map_compose {A1 A2 A3 B1 B2 B3 : ofe}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    turFunctor_map (f◎g, g'◎f') x ≡ turFunctor_map (g,g') (turFunctor_map (f,f') x);
  turFunctor_mor {A1 A2 B1 B2 : ofe}
      (fg : (A2 -n> A1) * (B1 -n> B2)) :
    CmraMorphism (turFunctor_map fg)
}.
Global Existing Instances turFunctor_map_ne turFunctor_mor.
Global Instance: Params (@turFunctor_map) 6 := {}.

Declare Scope turFunctor_scope.
Delimit Scope turFunctor_scope with TURF.
Bind Scope turFunctor_scope with turFunctor.

Class turFunctorContractive {SI : sidx} (F : turFunctor) :=
  #[export] turFunctor_map_contractive A1 A2 B1 B2 ::
    Contractive (@turFunctor_map SI F A1 A2 B1 B2).

Definition turFunctor_apply {SI : sidx} (F: turFunctor) (A: ofe) `{!Cofe A} : ucmra :=
  turFunctor_car F A A.

Program Definition turFunctor_to_trFunctor {SI : sidx} (F: turFunctor) : trFunctor := {|
  trFunctor_car A B := turFunctor_car F A B;
  trFunctor_map A1 A2 B1 B2 fg := turFunctor_map F fg
|}.
Next Obligation.
  intros F A B x. simpl in *. apply turFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. simpl in *.
  apply turFunctor_map_compose.
Qed.

Global Instance turFunctor_to_trFunctor_contractive {SI : sidx} (F: turFunctor) :
  turFunctorContractive F → trFunctorContractive (turFunctor_to_trFunctor F).
Proof.
  intros ? A1 A2 B1 B2 n f g Hfg. apply turFunctor_map_contractive. done.
Qed.

Program Definition turFunctor_tFunctor_compose {SI : sidx} (F1 : turFunctor) (F2 : tFunctor) : turFunctor := {|
  turFunctor_car A B := turFunctor_car F1 (tFunctor_car F2 B A) (tFunctor_car F2 A B);
  turFunctor_map A1 A2 B1 B2 'fg :=
    turFunctor_map F1 (tFunctor_map F2 (fg.2,fg.1),tFunctor_map F2 fg)
|}.
Next Obligation.
  intros SI F1 F2 A1 A2 B1 B2 n [f1 g1] [f2 g2] [??]; simpl in *.
  apply turFunctor_map_ne; split; apply tFunctor_map_ne; by split.
Qed.
Next Obligation.
  intros SI F1 F2 A B x; simpl in *. rewrite -{2}(turFunctor_map_id F1 x).
  apply equiv_dist=> n. apply turFunctor_map_ne.
  split=> y /=; by rewrite !tFunctor_map_id.
Qed.
Next Obligation.
  intros SI F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' x; simpl in *.
  rewrite -turFunctor_map_compose. apply equiv_dist=> n. apply turFunctor_map_ne.
  split=> y /=; by rewrite !tFunctor_map_compose.
Qed.
Global Instance turFunctor_tFunctor_compose_contractive_1 {SI : sidx} (F1 : turFunctor) (F2 : tFunctor):
  turFunctorContractive F1 → turFunctorContractive (turFunctor_tFunctor_compose F1 F2).
Proof.
  intros ? A1 A2 B1 B2 n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_contractive; destruct Hfg; split; simpl in *; apply tFunctor_map_ne; by split.
Qed.
Global Instance turFunctor_tFunctor_compose_contractive_2 {SI : sidx} (F1 : turFunctor) (F2 : tFunctor):
  tFunctorContractive F2 → turFunctorContractive (turFunctor_tFunctor_compose F1 F2).
Proof.
  intros ? A1 A2 B1 B2 n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_equiv; split; simpl in *; f_contractive; destruct Hfg; by split.
Qed.

Program Definition constTURF {SI : sidx} (B : ucmra) : turFunctor :=
  {| turFunctor_car A1 A2 := B; turFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion constTURF : ucmra >-> turFunctor.

Global Instance constTURF_contractive {SI : sidx} (B: ucmra) : turFunctorContractive (constTURF B).
Proof. rewrite /turFunctorContractive; apply _. Qed.



(* OFE -> OFE functor instances *)
Program Definition idTF {SI : sidx} : tFunctor :=
  {| tFunctor_car A1 A2 := A2; tFunctor_map A1 A2 B1 B2 f := f.2 |}.
Solve Obligations with done.
Notation "∙" := idTF : tFunctor_scope.

Program Definition prodTF {SI : sidx} (F1 F2 : tFunctor) : tFunctor := {|
  tFunctor_car A B := prodO (tFunctor_car F1 A B) (tFunctor_car F2 A B);
  tFunctor_map A1 A2 B1 B2 fg :=
    prodO_map (tFunctor_map F1 fg) (tFunctor_map F2 fg)
|}.
Next Obligation.
  intros SI ?? A1 A2 B1 B2 n ???; by apply prodO_map_ne; apply tFunctor_map_ne.
Qed.
Next Obligation. by intros SI F1 F2 A B [??]; rewrite /= !tFunctor_map_id. Qed.
Next Obligation.
  intros SI F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !tFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodTF F1%TF F2%TF) : tFunctor_scope.

Global Instance prodTF_contractive {SI : sidx} {F1 F2 : ofe}:
  tFunctorContractive F1 → tFunctorContractive F2 →
  tFunctorContractive (prodTF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply prodO_map_ne; apply tFunctor_map_contractive.
Qed.

Program Definition ofe_morTF {SI : sidx} (F1 F2 : tFunctor) : tFunctor := {|
  tFunctor_car A B := tFunctor_car F1 B A -n> tFunctor_car F2 A B;
  tFunctor_map A1 A2 B1 B2 fg :=
    ofe_morO_map (tFunctor_map F1 (fg.2, fg.1)) (tFunctor_map F2 fg)
|}.
Next Obligation.
  intros SI F1 F2 A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply tFunctor_map_ne; split; by apply Hfg.
Qed.
Next Obligation.
  intros SI F1 F2 A B [f ?] ?; simpl. rewrite /= !tFunctor_map_id.
  apply (ne_proper f). apply tFunctor_map_id.
Qed.
Next Obligation.
  intros SI F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [h ?] ?; simpl in *.
  rewrite -!tFunctor_map_compose. do 2 apply (ne_proper _). apply tFunctor_map_compose.
Qed.
Notation "F1 -n> F2" := (ofe_morTF F1%TF F2%TF) : tFunctor_scope.

Global Instance ofe_morTF_Contractive {SI : sidx}  (F1 F2 : tFunctor):
  tFunctorContractive F1 → tFunctorContractive F2 →
  tFunctorContractive (ofe_morTF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply tFunctor_map_contractive;
    split; intros m Hlt; split; simpl.
  all: destruct Hfg as [Hfg]; destruct (Hfg m); auto.
Qed.


Program Definition sumTF {SI : sidx} (F1 F2 : tFunctor) : tFunctor := {|
  tFunctor_car A B := sumO (tFunctor_car F1 A B) (tFunctor_car F2 A B);
  tFunctor_map A1 A2 B1 B2 fg :=
    sumO_map (tFunctor_map F1 fg) (tFunctor_map F2 fg)
|}.
Next Obligation.
  intros ??? A1 A2 B1 B2 n ???; by apply sumO_map_ne; apply tFunctor_map_ne.
Qed.
Next Obligation. by intros ? F1 F2 A B [?|?]; rewrite /= !tFunctor_map_id. Qed.
Next Obligation.
  intros ? F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [?|?]; simpl;
    by rewrite !tFunctor_map_compose.
Qed.
Notation "F1 + F2" := (sumTF F1%TF F2%TF) : tFunctor_scope.

Global Instance sumTF_contractive {SI : sidx} (F1 F2 : tFunctor):
  tFunctorContractive F1 → tFunctorContractive F2 →
  tFunctorContractive (sumTF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply sumO_map_ne; apply tFunctor_map_contractive.
Qed.

Program Definition optionTF {SI : sidx} (F : tFunctor) : tFunctor := {|
  tFunctor_car A B := optionO (tFunctor_car F A B);
  tFunctor_map A1 A2 B1 B2 fg := optionO_map (tFunctor_map F fg)
|}.
Next Obligation.
  by intros SI F A1 A2 B1 B2 n f g Hfg; apply optionO_map_ne, tFunctor_map_ne.
Qed.
Next Obligation.
  intros SI F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply tFunctor_map_id.
Qed.
Next Obligation.
  intros SI F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply tFunctor_map_compose.
Qed.

Global Instance optionTF_contractive {SI : sidx} (F : tFunctor):
  tFunctorContractive F → tFunctorContractive (optionTF F).
Proof.
  by intros ? ? A1 A2 B1 B2 n f g Hfg; apply optionO_map_ne, tFunctor_map_contractive.
Qed.

Program Definition laterTF {SI : sidx} (F : tFunctor) : tFunctor := {|
  tFunctor_car A B := laterO (tFunctor_car F A B);
  tFunctor_map A1 A2 B1 B2 fg := laterO_map (tFunctor_map F fg)
|}.
Next Obligation.
  intros k F A1 A2 B1 B2 n fg fg' ?.
  by apply (contractive_ne laterO_map), tFunctor_map_ne.
Qed.
Next Obligation.
  intros k F A B x; simpl. rewrite -{2}(later_map_id x).
  apply later_map_ext=>y. by rewrite tFunctor_map_id.
Qed.
Next Obligation.
  intros k F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -later_map_compose.
  apply later_map_ext=>y; apply tFunctor_map_compose.
Qed.
Notation "▶ F"  := (laterTF F%TF) (at level 20, right associativity) : tFunctor_scope.

Global Instance laterTF_contractive {SI : sidx} {F :tFunctor} : tFunctorContractive (laterTF F).
Proof.
  intros A1 A2 B1 B2 n fg fg' Hfg. apply laterO_map_contractive.
  split; intros ???; simpl.  by eapply tFunctor_map_ne, Hfg.
Qed.

Program Definition discrete_funTF {SI : sidx} {C} (F : C → tFunctor) : tFunctor := {|
  tFunctor_car A B := discrete_funO (λ c, tFunctor_car (F c) A B);
  tFunctor_map A1 A2 B1 B2 fg := discrete_funO_map (λ c, tFunctor_map (F c) fg)
|}.
Next Obligation.
  intros SI C F A1 A2 B1 B2 n ?? g. by apply discrete_funO_map_ne=>?; apply tFunctor_map_ne.
Qed.
Next Obligation.
  intros SI C F A B g; simpl. rewrite -{2}(discrete_fun_map_id g).
  apply discrete_fun_map_ext=> y; apply tFunctor_map_id.
Qed.
Next Obligation.
  intros SI C F A1 A2 A3 B1 B2 B3 f1 f2 f1' f2' g.
  rewrite /= -discrete_fun_map_compose.
  apply discrete_fun_map_ext=>y; apply tFunctor_map_compose.
Qed.

Notation "T -d> F" := (@discrete_funTF _ T%type (λ _, F%TF)) : tFunctor_scope.

Global Instance discrete_funTF_contractive {SI : sidx} {C} (F : C → tFunctor) :
  (∀ c, tFunctorContractive (F c)) → tFunctorContractive (discrete_funTF F).
Proof.
  intros ? A1 A2 B1 B2 n ?? g.
  by apply discrete_funO_map_ne=>c; apply tFunctor_map_contractive.
Qed.

Section sigTTF.
  Context {SI : sidx} {A : Type}.

Program Definition sigTTF (F : A → tFunctor) : tFunctor := {|
    tFunctor_car A B := sigTO (λ a, tFunctor_car (F a) A B);
    tFunctor_map A1 A2 B1 B2 fg := sigT_map (λ a, tFunctor_map (F a) fg)
|}.
  Next Obligation.
    repeat intro. exists eq_refl => /=. solve_proper.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), tFunctor_map_id.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), tFunctor_map_compose.
  Qed.

  Global Instance sigTTF_contractive {F} :
    (∀ a, tFunctorContractive (F a)) → tFunctorContractive (sigTTF F).
  Proof.
    repeat intro. apply sigT_map => a. exact: tFunctor_map_contractive.
  Qed.
End sigTTF.
Global Arguments sigTTF {_ _} _%_TF.

Notation "{ x  &  P }" := (sigTTF (λ x, P%TF)) : tFunctor_scope.
Notation "{ x : A &  P }" := (@sigTTF _ A%type (λ x, P%TF)) : tFunctor_scope.



(* OFE -> CMRA and OFE -> UCMRA functors *)
Program Definition prodTRF {SI : sidx} (F1 F2 : trFunctor) : trFunctor := {|
  trFunctor_car A B := prodR (trFunctor_car F1 A B) (trFunctor_car F2 A B);
  trFunctor_map A1 A2 B1 B2 fg :=
    prodO_map (trFunctor_map F1 fg) (trFunctor_map F2 fg)
|}.
Next Obligation.
  intros SI F1 F2 A1 A2 B1 B2 α ???. by apply prodO_map_ne; apply trFunctor_map_ne.
Qed.
Next Obligation. by intros SI F1 F2 A B [??]; rewrite /= !trFunctor_map_id. Qed.
Next Obligation.
  intros SI F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !trFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodTRF F1%TRF F2%TRF) : trFunctor_scope.

Global Instance prodTRF_contractive {SI : sidx} (F1 F2 : trFunctor):
  trFunctorContractive F1 → trFunctorContractive F2 →
  trFunctorContractive (prodTRF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 α ???;
    by apply prodO_map_ne; apply trFunctor_map_contractive.
Qed.

Program Definition prodTURF {SI : sidx} (F1 F2 : turFunctor) : turFunctor := {|
  turFunctor_car A B := prodUR (turFunctor_car F1 A B) (turFunctor_car F2 A B);
  turFunctor_map A1 A2 B1 B2 fg :=
    prodO_map (turFunctor_map F1 fg) (turFunctor_map F2 fg)
|}.
Next Obligation.
  intros SI F1 F2 A1 A2 B1 B2 α ???. by apply prodO_map_ne; apply turFunctor_map_ne.
Qed.
Next Obligation. by intros SI F1 F2 A B [??]; rewrite /= !turFunctor_map_id. Qed.
Next Obligation.
  intros SI F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !turFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodTURF F1%TURF F2%TURF) : turFunctor_scope.

Global Instance prodTURF_contractive {SI : sidx} (F1 F2 : turFunctor):
  turFunctorContractive F1 → turFunctorContractive F2 →
  turFunctorContractive (prodTURF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 α ???;
    by apply prodO_map_ne; apply turFunctor_map_contractive.
Qed.

Program Definition optionTURF {SI : sidx} (F : trFunctor) : turFunctor := {|
  turFunctor_car A B := optionUR (trFunctor_car F A B);
  turFunctor_map A1 A2 B1 B2 fg := optionO_map (trFunctor_map F fg)
|}.
Next Obligation.
  by intros SI F A1 A2 B1 B2 α f g Hfg; apply optionO_map_ne, trFunctor_map_ne.
Qed.
Next Obligation.
  intros SI F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply trFunctor_map_id.
Qed.
Next Obligation.
  intros SI F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply trFunctor_map_compose.
Qed.

Global Instance optionTURF_contractive {SI : sidx} (F : trFunctor):
  trFunctorContractive F → turFunctorContractive (optionTURF F).
Proof.
  by intros ? A1 A2 B1 B2 α f g Hfg; apply optionO_map_ne, trFunctor_map_contractive.
Qed.

Program Definition optionTRF {SI : sidx} (F : trFunctor) : trFunctor := {|
  trFunctor_car A B := optionR (trFunctor_car F A B);
  trFunctor_map A1 A2 B1 B2 fg := optionO_map (trFunctor_map F fg)
|}.
Solve Obligations with apply @optionTURF.

Global Instance optionTRF_contractive {SI : sidx} (F: trFunctor) :
  trFunctorContractive F → trFunctorContractive (optionTRF F).
Proof. apply optionTURF_contractive. Qed.


Program Definition discrete_funTURF {SI : sidx} {C} (F : C → turFunctor) : turFunctor := {|
  turFunctor_car A B := discrete_funUR (λ c, turFunctor_car (F c) A B);
  turFunctor_map A1 A2 B1 B2 fg := discrete_funO_map (λ c, turFunctor_map (F c) fg)
|}.
Next Obligation.
  intros SI C F A1 A2 B1 B2 α ?? g. by apply discrete_funO_map_ne=>?; apply turFunctor_map_ne.
Qed.
Next Obligation.
  intros SI C F A B g; simpl. rewrite -{2}(discrete_fun_map_id g).
  apply discrete_fun_map_ext=> y; apply turFunctor_map_id.
Qed.
Next Obligation.
  intros SI C F A1 A2 A3 B1 B2 B3 f1 f2 f1' f2' g. rewrite /=-discrete_fun_map_compose.
  apply discrete_fun_map_ext=>y; apply turFunctor_map_compose.
Qed.
Global Instance discrete_funTURF_contractive {SI : sidx} {C} (F : C → turFunctor) :
  (∀ c, turFunctorContractive (F c)) → turFunctorContractive (discrete_funTURF F).
Proof.
  intros ? A1 A2 B1 B2 α ?? g.
  by apply discrete_funO_map_ne=>c; apply turFunctor_map_contractive.
Qed.


Program Definition agreeTRF {SI : sidx} (F : tFunctor) : trFunctor := {|
  trFunctor_car A B := agreeR (tFunctor_car F A B);
  trFunctor_map A1 A2 B1 B2 fg := agreeO_map (tFunctor_map F fg)
|}.
Next Obligation.
  intros ?? A1 A2 B1 B2 n ???; simpl. by apply agreeO_map_ne, tFunctor_map_ne.
Qed.
Next Obligation.
  intros ? F A B x; simpl. rewrite -{2}(agree_map_id x).
  apply (agree_map_ext _)=>y. by rewrite tFunctor_map_id.
Qed.
Next Obligation.
  intros ? F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -agree_map_compose.
  apply (agree_map_ext _)=>y; apply tFunctor_map_compose.
Qed.

Global Instance agreeTRF_contractive {SI : sidx} (F : tFunctor):
  tFunctorContractive F → trFunctorContractive (agreeTRF F).
Proof.
  intros ? A1 A2 B1 B2 n ???; simpl.
  by apply agreeO_map_ne, tFunctor_map_contractive.
Qed.


Program Definition exclTRF {SI : sidx} (F : tFunctor) : trFunctor := {|
  trFunctor_car A B := (exclR (tFunctor_car F A B));
  trFunctor_map A1 A2 B1 B2 fg := exclO_map (tFunctor_map F fg)
|}.
Next Obligation.
  intros SI F A1 A2 B1 B2 n x1 x2 ??. by apply exclO_map_ne, tFunctor_map_ne.
Qed.
Next Obligation.
  intros SI F A B x; simpl. rewrite -{2}(excl_map_id x).
  apply excl_map_ext=>y. by rewrite tFunctor_map_id.
Qed.
Next Obligation.
  intros SI F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -excl_map_compose.
  apply excl_map_ext=>y; apply tFunctor_map_compose.
Qed.

Global Instance exclTRF_contractive {SI : sidx} (F: tFunctor) :
  tFunctorContractive F → trFunctorContractive (exclTRF F).
Proof.
  intros A1 A2 B1 B2 n x1 x2 ??. by apply exclO_map_ne, tFunctor_map_contractive.
Qed.


Program Definition gmapOF {SI : sidx} K `{Countable K} (F : tFunctor) : tFunctor := {|
  tFunctor_car A B := gmapO K (tFunctor_car F A B);
  tFunctor_map A1 A2 B1 B2 fg := gmapO_map (tFunctor_map F fg)
|}.
Next Obligation.
  by intros K SI ?? F A1 A2 B1 B2 n f g Hfg; apply gmapO_map_ne, tFunctor_map_ne.
Qed.
Next Obligation.
  intros K SI ?? F A B x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply tFunctor_map_id.
Qed.
Next Obligation.
  intros K SI ?? F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply tFunctor_map_compose.
Qed.
Global Instance gmapOF_contractive {SI : sidx} K `{Countable K} (F: tFunctor) :
  tFunctorContractive F → tFunctorContractive (gmapOF K F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply gmapO_map_ne, tFunctor_map_contractive.
Qed.


Program Definition gmapTURF {SI : sidx} K `{Countable K} (F : trFunctor) : turFunctor := {|
  turFunctor_car A B := gmapUR K (trFunctor_car F A B);
  turFunctor_map A1 A2 B1 B2 fg := gmapO_map (trFunctor_map F fg)
|}.
Next Obligation.
  by intros K ? ? SI F A1 A2 B1 B2 n f g Hfg; apply gmapO_map_ne, trFunctor_map_ne.
Qed.
Next Obligation.
  intros K SI ?? F A B x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply trFunctor_map_id.
Qed.
Next Obligation.
  intros K SI ?? F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply trFunctor_map_compose.
Qed.
Global Instance gmapTURF_contractive {SI : sidx} K `{Countable K} (F: trFunctor) :
  trFunctorContractive F → turFunctorContractive (gmapTURF K F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply gmapO_map_ne, trFunctor_map_contractive.
Qed.

Program Definition gmapTRF {SI : sidx} K `{Countable K} (F : trFunctor) : trFunctor := {|
  trFunctor_car A B := gmapR K (trFunctor_car F A B);
  trFunctor_map A1 A2 B1 B2 fg := gmapO_map (trFunctor_map F fg)
|}.
Solve Obligations with (intros SI; intros; apply (@gmapTURF SI)).


Global Instance gmapTRF_contractive {SI : sidx} K `{Countable K} (F : trFunctor) :
  trFunctorContractive F → trFunctorContractive (gmapTRF K F).
Proof. apply gmapTURF_contractive. Qed.


Program Definition listTF {SI : sidx} (F : tFunctor) : tFunctor := {|
  tFunctor_car A B := listO (tFunctor_car F A B);
  tFunctor_map A1 A2 B1 B2 fg := listO_map (tFunctor_map F fg)
|}.
Next Obligation.
  by intros ? F A1 A2 B1 B2 n f g Hfg; apply listO_map_ne, tFunctor_map_ne.
Qed.
Next Obligation.
  intros ? F A B x. rewrite /= -{2}(list_fmap_id x).
  apply list_fmap_equiv_ext=>???. apply tFunctor_map_id.
Qed.
Next Obligation.
  intros ? F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -list_fmap_compose.
  apply list_fmap_equiv_ext=>???; apply tFunctor_map_compose.
Qed.

Global Instance listTF_contractive {SI : sidx} F :
  tFunctorContractive F → tFunctorContractive (listTF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply listO_map_ne, tFunctor_map_contractive.
Qed.


Program Definition vecOF {SI : sidx} (F : tFunctor) m : tFunctor := {|
  tFunctor_car A B := vecO (tFunctor_car F A B) m;
  tFunctor_map A1 A2 B1 B2 fg := vecO_map m (tFunctor_map F fg)
|}.
Next Obligation.
  intros SI F A1 A2 B1 B2 n m f g Hfg. by apply vecO_map_ne, tFunctor_map_ne.
Qed.
Next Obligation.
  intros SI F m A B l.
  change (vec_to_list (vec_map m (tFunctor_map F (cid, cid)) l) ≡ l).
  rewrite vec_to_list_map. apply listTF.
Qed.
Next Obligation.
  intros SI F m A1 A2 A3 B1 B2 B3 f g f' g' l.
  change (vec_to_list (vec_map m (tFunctor_map F (f ◎ g, g' ◎ f')) l)
    ≡ vec_map m (tFunctor_map F (g, g')) (vec_map m (tFunctor_map F (f, f')) l)).
  rewrite !vec_to_list_map. by apply: (tFunctor_map_compose (listTF F) f g f' g').
Qed.

Global Instance vecOF_contractive {SI : sidx} (F : tFunctor) m :
  tFunctorContractive F → tFunctorContractive (vecOF F m).
Proof.
  by intros ?? A1 A2 B1 B2 n ???; apply vecO_map_ne; first apply tFunctor_map_contractive.
Qed.

(* Definition of gmap_viewUR changed to cmra -> ucmra (was ofe -> ucmra) *)
Program Definition gmap_viewTURF {SI : sidx} (K : Type) `{Countable K} (F : trFunctor) : turFunctor := {|
  turFunctor_car A B := gmap_viewUR K (trFunctor_car F A B);
  turFunctor_map A1 A2 B1 B2 fg :=
    viewO_map (rel:=gmap_view.gmap_view_rel K (trFunctor_car F A1 B1))
              (rel':=gmap_view.gmap_view_rel K (trFunctor_car F A2 B2))
              (gmapO_map (K:=K) (trFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (trFunctor_map F fg)))
|}.
Next Obligation.
  intros ? K ?? F A1 A2 B1 B2 n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne, trFunctor_map_ne. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply trFunctor_map_ne. done.
Qed.
Next Obligation.
  intros ? K ?? F A B x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -{2}(map_fmap_id y).
    apply: map_fmap_equiv_ext=>k ??.
    apply trFunctor_map_id.
  - rewrite /= -{2}(map_fmap_id y).
    apply: map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    apply trFunctor_map_id.
Qed.
Next Obligation.
  intros ? K ?? F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -map_fmap_compose.
    apply: map_fmap_equiv_ext=>k ??.
    apply trFunctor_map_compose.
  - rewrite /= -map_fmap_compose.
    apply: map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    apply trFunctor_map_compose.
Qed.
Next Obligation.
  intros ? K ?? F A1 A2 B1 B2 fg; simpl.
  (* [apply] does not work, probably the usual unification probem (Coq #6294) *)
  apply @view_map_cmra_morphism; [apply _..|]=> n m f.
  intros Hrel k [df va] Hf. move: Hf.
  rewrite !lookup_fmap.
  destruct (f !! k) as [[df' va']|] eqn:Hfk; rewrite Hfk; last done.
  simpl=>[= <- <-].
  specialize (Hrel _ _ Hfk). simpl in Hrel.
  destruct Hrel as (v & dq & Hlookup & Hval & Hincl).
  eexists (trFunctor_map F fg v), dq.
  rewrite Hlookup. split; first done. split.
  - split; first by apply Hval. simpl. apply: cmra_morphism_validN. apply Hval.
  - destruct Hincl as [[[fdq fv]|] Hincl].
    + apply: Some_includedN_mono. rewrite -Some_op in Hincl.
      apply (inj _) in Hincl. rewrite -pair_op in Hincl.
      exists (fdq, trFunctor_map F fg fv). rewrite -pair_op.
      split; first apply Hincl. rewrite -cmra_morphism_op.
      simpl. f_equiv. apply Hincl.
    + exists None. rewrite right_id in Hincl. apply (inj _) in Hincl.
      rewrite right_id. f_equiv. split; first apply Hincl.
      simpl. f_equiv. apply Hincl.
Qed.

Global Instance gmap_viewTURF_contractive {SI : sidx} (K : Type) `{Countable K} (F: trFunctor) :
  trFunctorContractive F → turFunctorContractive (gmap_viewTURF K F).
Proof.
  intros ? A1 A2 B1 B2 n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne. apply trFunctor_map_contractive. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply trFunctor_map_contractive. done.
Qed.

Program Definition gmap_viewTRF {SI : sidx} (K : Type) `{Countable K} (F : trFunctor) : trFunctor := {|
  trFunctor_car A B := gmap_viewR K (trFunctor_car F A B);
  trFunctor_map A1 A2 B1 B2 fg :=
    viewO_map (rel:=gmap_view.gmap_view_rel K (trFunctor_car F A1 B1))
              (rel':=gmap_view.gmap_view_rel K (trFunctor_car F A2 B2))
              (gmapO_map (K:=K) (trFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (trFunctor_map F fg)))
|}.
Solve Obligations with apply @gmap_viewTURF.


Global Instance gmap_viewTRF_contractive {SI : sidx} (K : Type) `{Countable K} (F: trFunctor) :
  trFunctorContractive F → trFunctorContractive (gmap_viewTRF K F).
Proof. apply gmap_viewTURF_contractive. Qed.



Program Definition authTURF {SI : sidx} (F : turFunctor) : turFunctor := {|
  turFunctor_car A B := authUR (turFunctor_car F A B);
  turFunctor_map A1 A2 B1 B2 fg :=
    viewO_map (turFunctor_map F fg) (turFunctor_map F fg)
|}.
Next Obligation.
  intros SI F A1 A2 B1 B2 n f g Hfg.
  apply viewO_map_ne; by apply turFunctor_map_ne.
Qed.
Next Obligation.
  intros SI F A B x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y; apply turFunctor_map_id.
Qed.
Next Obligation.
  intros SI F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y; apply turFunctor_map_compose.
Qed.
Next Obligation.
  intros SI F A1 A2 B1 B2 fg; simpl.
  apply view_map_cmra_morphism; [apply _..|]=> n a b [??]; split.
  - by apply (cmra_morphism_monoN _).
  - by apply (cmra_morphism_validN _).
Qed.

Global Instance authTURF_contractive {SI : sidx} (F : turFunctor):
  turFunctorContractive F → turFunctorContractive (authTURF F).
Proof.
  intros ? A1 A2 B1 B2 n f g Hfg.
  apply viewO_map_ne; by apply turFunctor_map_contractive.
Qed.

Program Definition authTRF {SI : sidx} (F : turFunctor) : trFunctor := {|
  trFunctor_car A B := authR (turFunctor_car F A B);
  trFunctor_map A1 A2 B1 B2 fg :=
    viewO_map (turFunctor_map F fg) (turFunctor_map F fg)
|}.
Solve Obligations with apply @authTURF.

Global Instance authTRF_contractive {SI : sidx} (F : turFunctor):
  turFunctorContractive F → trFunctorContractive (authTRF F).
Proof. apply authTURF_contractive. Qed.




(* derived instances *)
Definition max_prefix_listTURF {SI : sidx} (F : tFunctor) : turFunctor :=
  gmapTURF nat (agreeTRF F).

Global Instance max_prefix_listTURF_contractive {SI : sidx} F :
  tFunctorContractive F → turFunctorContractive (max_prefix_listTURF F).
Proof. apply _. Qed.

Definition max_prefix_listTRF {SI : sidx} (F : tFunctor) : trFunctor :=
  gmapTRF nat (agreeTRF F).

Global Instance max_prefix_listTRF_contractive {SI : sidx} F :
  tFunctorContractive F → trFunctorContractive (max_prefix_listTRF F).
Proof. apply _. Qed.


Definition dfrac_agreeTRF {SI : sidx} (F : tFunctor) : trFunctor :=
  prodTRF (constTRF dfracR) (agreeTRF F).

Global Instance dfrac_agreeTRF_contractive {SI : sidx} F :
  tFunctorContractive F → trFunctorContractive (dfrac_agreeTRF F).
Proof. apply _. Qed.


Definition excl_authTURF {SI : sidx} (F : tFunctor) : turFunctor :=
  authTURF (optionTURF (exclTRF F)).

Global Instance excl_authTURF_contractive {SI : sidx} F :
  tFunctorContractive F → turFunctorContractive (excl_authTURF F).
Proof. apply _. Qed.

Definition excl_authTRF {SI : sidx} (F : tFunctor) : trFunctor :=
  authTRF (optionTURF (exclTRF F)).

Global Instance excl_authTRF_contractive {SI : sidx} F :
  tFunctorContractive F → trFunctorContractive (excl_authTRF F).
Proof. apply _. Qed.


Definition mono_listTURF {SI : sidx} (F : tFunctor) : turFunctor :=
  authTURF (max_prefix_listTURF F).

Global Instance mono_listTURF_contractive {SI : sidx} F :
  tFunctorContractive F → turFunctorContractive (mono_listTURF F).
Proof. apply _. Qed.

Definition mono_listTRF {SI : sidx} (F : tFunctor) : trFunctor :=
  authTRF (max_prefix_listTURF F).

Global Instance mono_listTRF_contractive {SI : sidx} F :
  tFunctorContractive F → trFunctorContractive (mono_listTRF F).
Proof. apply _. Qed.
