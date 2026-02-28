(* begin hide *)
From Stdlib Require Import
  ZArith
  List
  Strings.Byte.
From Stdlib Require Uint63 Sint63 SpecFloat PrimFloat FloatOps FloatAxioms.
From MetaRocq.Utils Require Import bytestring.
From CeresBS Require Import
  CeresUtils
  CeresS
  CeresString
  CeresSerialize
  CeresDeserialize.

Import ListNotations.
(* end hide *)


(** Completeness: all values can be serialized without loss of information. *)
Definition Complete {A : Type} (ser : A -> sexp) (de : sexp -> error + A) : Prop :=
  forall (a : A), de (ser a) = inr a.

(** Soundness: deserialization succeeds only for well-formed expressions. *)
Definition Sound {A : Type} (ser : A -> sexp) (de : sexp -> error + A) : Prop :=
  forall (e : sexp) (a : A),
    de e = inr a ->
    ser a = e.

Class CompleteClass (A : Type) `{Serialize A} `{Deserialize A} : Prop :=
  complete_class : forall l, @Complete A to_sexp (_from_sexp l).

Class SoundClass (A : Type) `{Serialize A} `{Deserialize A} : Prop :=
  sound_class : forall l, @Sound A to_sexp (_from_sexp l).

(**)

Class CompleteIntegral (A : Type) `{Integral A} `{SemiIntegral A} : Prop :=
  complete_integral : forall (a : A), from_Z (to_Z a) = Some a.

Class SoundIntegral (A : Type) `{Integral A} `{SemiIntegral A} : Prop :=
  sound_integral : forall z a, from_Z z = Some a -> to_Z a = z.

Global
Instance CompleteClass_Integral {A} `{CompleteIntegral A} : CompleteClass A.
Proof.
  intros l a; cbn; rewrite complete_integral; reflexivity.
Qed.

Global
Instance SoundClass_Integral {A} `{SoundIntegral A} : SoundClass A.
Proof.
  intros l [ [] | ] a; cbn; try discriminate.
  destruct from_Z eqn:Ez; try discriminate.
  intros E; injection E; intros [].
  apply (f_equal Atom), (f_equal Num). apply sound_integral; assumption.
Qed.

Global
Instance Complete_Z : CompleteIntegral Z.
Proof.
  intros a. reflexivity.
Qed.

Global
Instance Complete_N : CompleteIntegral N.
Proof.
  intros a. unfold from_Z, SemiIntegral_N.
  replace (Z.ltb _ _) with false.
  - rewrite N2Z.id; reflexivity.
  - symmetry; apply Z.ltb_ge.
    apply N2Z.is_nonneg.
Qed.

Global
Instance Complete_nat : CompleteIntegral nat.
Proof.
  intros a. unfold from_Z, SemiIntegral_nat.
  replace (Z.ltb _ _) with false.
  - rewrite Nat2Z.id; reflexivity.
  - symmetry; apply Z.ltb_ge.
    apply Nat2Z.is_nonneg.
Qed.

Global
Instance Sound_Z : SoundIntegral Z.
Proof.
  intros a b H; injection H; intros []; reflexivity.
Qed.

Global
Instance Sound_N : SoundIntegral N.
Proof.
  intros z n. unfold from_Z, SemiIntegral_N.
  destruct (Z.ltb_spec z 0); try discriminate.
  intros E; injection E; clear E.
  intros []; rewrite Z2N.id; auto.
Qed.

Global
Instance Sound_nat : SoundIntegral nat.
Proof.
  intros z n.  unfold from_Z, SemiIntegral_nat.
  destruct (Z.ltb_spec z 0); try discriminate.
  intros E; injection E; clear E.
  intros []; rewrite Z2Nat.id; auto.
Qed.

(**)

Lemma sound__con {A} (tyname : string)
    (g : string -> loc -> error + A) (f : string -> FromSexpList A)
    l (e : sexp) (a : A)
  : Deser._con tyname g f l e = inr a ->
    (exists c, e = Atom (Raw c) /\ g c l = inr a) \/
    (exists c es, e = List (Atom (Raw c) :: es) /\ f c l (type_error tyname) es = inr a).
Proof.
  destruct e as [ [] | [ | [ [] | ] ] ]; cbn; try discriminate; eauto.
Qed.

Lemma _find_or_spec {A B C}
    (eqb : A -> A -> bool) (a : A) (xs : list (A * B)) (f : B -> C) (b : C)
    (P : C -> Prop)
  : P (_find_or eqb a xs f b) ->
    (List.Exists (fun p => eqb a (fst p) = true /\ P (f (snd p))) xs) \/
    (List.Forall (fun p => eqb a (fst p) = false) xs /\ P b).
Proof.
  induction xs as [ | xy xs IH ].
  - auto.
  - cbn. destruct xy as [x y].
    destruct (eqb a x) eqn:Eeqb.
    + left; left; auto.
    + intros H; specialize (IH H).
      destruct IH as [ | [] ].
      * left; right; assumption.
      * right; constructor; [ constructor; auto | auto ].
Qed.

(* For backwards compatibility. [List.Exists_impl] which was added on 8.10. *)
Lemma List_Exists_impl {A} (P Q : A -> Prop) (xs : list A)
  : (forall x, P x -> Q x) -> List.Exists P xs -> List.Exists Q xs.
Proof.
  induction 2; intros; auto.
Qed.

Theorem sound_match_con {A} (tyname : string)
    (c0 : list (string * A)) (c1 : list (string * FromSexpList A))
    l (e : sexp) (a : A)
  : Deser.match_con tyname c0 c1 l e = inr a ->
    List.Exists (fun p => e = Atom (Raw (fst p)) /\ a = snd p) c0
      \/ List.Exists (fun p => exists es,
           List (Atom (Raw (fst p)) :: es) = e /\
           inr a = snd p l (type_error tyname) es) c1.
Proof.
  unfold Deser.match_con.
  intros DESER. apply sound__con in DESER. destruct DESER as [ (c & Ee & Ea ) | (c & es & Ee & Ea) ].
  - apply _find_or_spec in Ea. destruct Ea as [ Ea | [] ]; [ | discriminate ].
    left. revert Ea; apply List_Exists_impl.
    intros [] [Es Ea]; cbn in *.
    apply CeresString.eqb_eq_string in Es.
    injection Ea; intros.
    subst. auto.
  - apply _find_or_spec in Ea. destruct Ea as [ Ea | [] ]; [ | discriminate ].
    right. revert Ea; apply List_Exists_impl.
    intros [] [Es Ea]; cbn in *.
    apply CeresString.eqb_eq_string in Es.
    exists es.
    subst; auto.
Qed.

Ltac elim_Exists H :=
  match type of H with
  | (List.Exists _ nil) => apply List.Exists_nil in H; destruct H
  | (List.Exists _ (cons _ _)) => apply List.Exists_cons in H;
    destruct H as [ H | H ]; [ | elim_Exists H ]
  end.

Global
Instance CompleteClass_bool : CompleteClass bool.
Proof.
  unfold CompleteClass, Complete.
  intros l []; reflexivity.
Qed.

Global
Instance SoundClass_bool : SoundClass bool.
Proof.
  intros l e a Ee; apply sound_match_con in Ee.
  destruct Ee as [ Ee | Ee ]; elim_Exists Ee;
    destruct Ee as [Eatom Ea]; subst; try reflexivity.
Qed.

Global
Instance CompleteClass_option {A} `{CompleteClass A} : CompleteClass (option A).
Proof.
  unfold CompleteClass, Complete.
  intros l []; cbn; [ rewrite H1 | ]; reflexivity.
Qed.

Global
Instance CompleteClass_sum {A B} `{CompleteClass A} `{CompleteClass B} : CompleteClass (A + B).
Proof.
  intros l []; cbn; rewrite complete_class; reflexivity.
Qed.

Global
Instance CompleteClass_prod {A B} `{CompleteClass A} `{CompleteClass B} : CompleteClass (A * B).
Proof.
  intros l []; cbn; rewrite 2 complete_class; reflexivity.
Qed.

Section DeRetField.

Context {R} (r : R) {n : nat}.

Inductive UnnilFields : R -> list sexp -> Prop :=
| MkUnnilFields : UnnilFields r nil.

Lemma sound_ret_field {a} l err es
  : inr a = _fields (@Deser.ret R r n) l err es ->
    UnnilFields a es.
Proof.
  destruct es; cbn.
  - intros H; injection H; intros J; rewrite J; constructor.
  - discriminate.
Qed.

End DeRetField.

Section DeBindField.

Context {A B} (pa : FromSexp A)
    {n m : nat} (f : A -> FromSexpListN (S n) m B).

Context (a : B) (es : list sexp) {l : loc} {err : message -> message}.

Inductive UnconsFields : list sexp -> Prop :=
| MkUnconsFields a' e' es'
  : pa (n :: l) e' = inr a' ->
    inr a = _fields (f a') l err es' ->
    UnconsFields (e' :: es').

Lemma sound_bind_field
  : inr a = _fields (Deser.bind_field pa f) l err es ->
    UnconsFields es.
Proof.
  destruct es; cbn; try discriminate.
  destruct pa eqn:E1; cbn; try discriminate.
  apply MkUnconsFields. assumption.
Qed.

End DeBindField.

Ltac sound_field Ea :=
  (apply sound_ret_field in Ea; destruct Ea) +
  (let a1 := fresh "a" in
   let e1 := fresh "e" in
   let es := fresh "es" in
   let Ea1 := fresh "Ea1" in
   apply sound_bind_field in Ea;
   destruct Ea as [a1 e1 es Ea1 Ea];
   sound_field Ea).

Global
Instance SoundClass_option {A} `{SoundClass A} : SoundClass (option A).
Proof.
  intros l e a Ee; apply sound_match_con in Ee.
  destruct Ee as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
  - destruct Ee as [E1 E2]; subst; reflexivity.
  - destruct Ee as [es [Ee Ea]].
    sound_field Ea. cbn.
    apply H1 in Ea1.
    rewrite Ea1; assumption.
Qed.

Global
Instance SoundClass_sum {A B} `{SoundClass A} `{SoundClass B} : SoundClass (A + B).
Proof.
  intros l e a Ee; apply sound_match_con in Ee.
  destruct Ee as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
  - destruct Ee as [es [Ee Ea]].
    sound_field Ea. cbn.
    apply sound_class in Ea1.
    rewrite Ea1; assumption.
  - destruct Ee as [es [Ee Ea]].
    sound_field Ea. cbn.
    apply sound_class in Ea1.
    rewrite Ea1; assumption.
Qed.

Global
Instance SoundClass_prod {A B} `{SoundClass A} `{SoundClass B} : SoundClass (A * B).
Proof.
  intros l [ ea | [ | ea [ | eb [ | ] ] ] ] a; cbn; try discriminate.
  destruct (_from_sexp _ ea) eqn:Ea; cbn; try discriminate.
  destruct (_from_sexp _ eb) eqn:Eb; cbn; try discriminate.
  intros Eab; injection Eab; intros [].
  unfold to_sexp, Serialize_product; cbn.
  repeat f_equal; [ revert Ea | revert Eb ]; eapply sound_class.
Qed.

Lemma sound_class_list {A} `{SoundClass A} (es : list sexp)
  : forall fs xs n l a,
      map to_sexp (rev xs) = fs ->
      _sexp_to_list _from_sexp xs n l es = inr a -> to_sexp a = List (fs ++ es).
Proof.
  induction es as [ | e es ]; cbn; intros fs xs n l a E1 E2.
  - apply (f_equal List).
    injection E2; intros [].
    rewrite rev_alt in E1. rewrite app_nil_r. assumption.
  - destruct _from_sexp as [ | a'] eqn:E3 in E2; try discriminate.
    apply IHes with (fs := fs ++ [e]) in E2; cbn.
    + rewrite app_cons_assoc; assumption.
    + rewrite map_app; cbn.
      f_equal; [ assumption | f_equal ].
      eapply sound_class. eassumption.
Qed.

Global
Instance SoundClass_list {A} `{SoundClass A} : SoundClass (list A).
Proof.
  intros l [e | es] a; cbn; try discriminate.
  apply sound_class_list with (fs := []).
  reflexivity.
Qed.

Lemma complete_class_list {A} `{CompleteClass A} (a : list A)
  : forall (xs : list A) (n : nat) (l : loc),
      _sexp_to_list _from_sexp xs n l (map to_sexp a) = inr (rev xs ++ a).
Proof.
  induction a as [ | y ys ]; intros; cbn.
  - rewrite rev_alt, app_nil_r; reflexivity.
  - rewrite complete_class. rewrite app_cons_assoc.
    apply IHys.
Qed.

Global
Instance CompleteClass_list {A} `{CompleteClass A} : CompleteClass (list A).
Proof.
  intros l a. apply complete_class_list.
Qed.

Global
Instance CompleteClass_string : CompleteClass string.
Proof.
  intros l a. reflexivity.
Qed.

Global
Instance SoundClass_string : SoundClass string.
Proof.
  intros l [ [] | ]; cbn; try discriminate.
  intros ? E; injection E; intros []; reflexivity.
Qed.


Lemma bytestring_of_to : forall s,
  bytestring.String.of_string (bytestring.String.to_string s) = s.
Proof.
  induction s.
  - reflexivity.
  - cbn.
    rewrite IHs.
    rewrite Ascii.byte_of_ascii_of_byte.
    reflexivity.
Qed.

Lemma bytestring_to_of : forall s,
  bytestring.String.to_string (bytestring.String.of_string s) = s.
Proof.
  induction s.
  - reflexivity.
  - cbn.
    rewrite IHs.
    rewrite Ascii.ascii_of_byte_of_ascii.
    reflexivity.
Qed.

Global
Instance CompleteClass_coq_string : CompleteClass String.string.
Proof.
  intros l a.
  cbn.
  rewrite bytestring_to_of.
  reflexivity.
Qed.

Global
Instance SoundClass_coq_string : SoundClass String.string.
Proof.
  intros l [ [] | ]; cbn; try discriminate.
  intros ? E; injection E; intros [].
  unfold to_sexp, Serialize_coq_string.
  rewrite bytestring_of_to.
  reflexivity.
Qed.

Global
Instance CompleteClass_byte : CompleteClass byte.
Proof.
  intros l a. reflexivity.
Qed.

Global
Instance SoundClass_byte : SoundClass byte.
Proof.
  intros l [ [ | s | ] | ]; cbn; try discriminate.
  destruct s as [ | ? [] ]; cbn; try discriminate.
  intros ? E; injection E; intros []; reflexivity.
Qed.

Global
Instance Complete_unit : @CompleteClass unit Serialize_unit Deserialize_unit.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn.
  destruct o.
  reflexivity.
Qed.

Global
Instance Sound_unit : @SoundClass unit Serialize_unit Deserialize_unit.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  unfold to_sexp, Serialize_unit.
  unfold _from_sexp, Deserialize_unit in He.
  destruct e; try discriminate.
  destruct a0; try discriminate.
  destruct s; try discriminate.
  destruct b; try discriminate.
  destruct s; try discriminate.
  destruct b; try discriminate.
  destruct s; try discriminate.
  reflexivity.
Qed.

Global
Instance CompleteClass_ascii : CompleteClass Ascii.ascii.
Proof.
  intros l a.
  cbn.
  rewrite Ascii.ascii_of_byte_of_ascii.
  reflexivity.
Qed.

Global
Instance SoundClass_ascii : SoundClass Ascii.ascii.
Proof.
  intros l [ [ | s | ] | ]; cbn; try discriminate.
  destruct s as [ | ? [] ]; cbn; try discriminate.
  intros ? E; injection E; intros [].
  unfold to_sexp, Serialize_ascii.
  rewrite Ascii.byte_of_ascii_of_byte.
  reflexivity.
Qed.

Global
Instance CompleteClass_Empty_set : CompleteClass Empty_set.
Proof.
  intros l v.
  destruct v.
Qed.

Global
Instance SoundClass_Empty_set : SoundClass Empty_set.
Proof.
  intros l s v.
  destruct v.
Qed.

Global
Instance CompleteClass_comparison : CompleteClass comparison.
Proof.
  unfold CompleteClass, Complete.
  intros l []; reflexivity.
Qed.

Global
Instance SoundClass_comparison : SoundClass comparison.
Proof.
  intros l e a Ee; apply sound_match_con in Ee.
  destruct Ee as [ Ee | Ee ]; elim_Exists Ee;
    destruct Ee as [Eatom Ea]; subst; try reflexivity.
Qed.

Global
Instance Complete_sint : @CompleteIntegral PrimInt63.int Integral_sint SemiIntegral_sint.
Proof.
  intros a. unfold from_Z, SemiIntegral_sint.
  unfold to_Z, Integral_sint.
  destruct andb eqn:H.
  - apply Bool.andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1.
    apply Z.leb_le in H2.
    rewrite Sint63.of_to_Z.
    reflexivity.
  - apply Bool.andb_false_iff in H as [H | H].
    + apply Z.leb_nle in H.
      specialize (Sint63.to_Z_bounded a) as H1.
      destruct H1 as [H1 _].
      contradiction.
    + apply Z.leb_nle in H.
      specialize (Sint63.to_Z_bounded a) as H1.
      destruct H1 as [_ H1].
      contradiction.
Qed.

Global
Instance Complete_uint : @CompleteIntegral PrimInt63.int Integral_uint SemiIntegral_uint.
Proof.
  intros a. unfold from_Z, SemiIntegral_uint.
  unfold to_Z, Integral_uint.
  destruct andb eqn:H.
  - apply Bool.andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1.
    apply Z.ltb_lt in H2.
    rewrite Uint63.of_to_Z.
    reflexivity.
  - apply Bool.andb_false_iff in H as [H | H].
    + apply Z.leb_nle in H.
      specialize (Uint63.to_Z_rec_bounded Uint63.size a) as H1.
      destruct H1 as [H1 _].
      contradiction.
    + apply Z.ltb_nlt in H.
      specialize (Uint63.to_Z_rec_bounded Uint63.size a) as H1.
      destruct H1 as [_ H1].
      assert (H0 : Uint63Axioms.to_Z Uint63Axioms.digits = Z.of_nat Uint63Axioms.size).
      { reflexivity. }
      rewrite H0 in *; clear H0.
      contradiction.
Qed.

Global
Instance Sound_sint : @SoundIntegral PrimInt63.int Integral_sint SemiIntegral_sint.
Proof.
  intros z n. unfold from_Z, SemiIntegral_sint.
  destruct andb eqn:H.
  - intros E; injection E as <-.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1.
    apply Z.leb_le in H2.
    rewrite <- Sint63.is_int.
    reflexivity.
    split; assumption.
  - intros. discriminate.
Qed.

Global
Instance Sound_uint : @SoundIntegral PrimInt63.int Integral_uint SemiIntegral_uint.
Proof.
  intros z n. unfold from_Z, SemiIntegral_uint.
  destruct andb eqn:H.
  - intros E; injection E as <-.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1.
    apply Z.ltb_lt in H2.
    rewrite <- Uint63.is_int.
    reflexivity.
    split; assumption.
  - intros. discriminate.
Qed.

Global
Instance Complete_positive : CompleteIntegral positive.
Proof.
  intros a. unfold from_Z, SemiIntegral_positive.
  unfold to_Z, Integral_positive.
  replace (Z.leb _ _) with false.
  - cbn. reflexivity.
  - symmetry.
    exact Zone_pos.
Qed.

Global
Instance Sound_positive : SoundIntegral positive.
Proof.
  intros z n. unfold from_Z, SemiIntegral_positive.
  destruct (Z.leb_spec z 0); try discriminate.
  intros E; injection E as <-.
  unfold to_Z, Integral_positive.
  rewrite Z2Pos.id by assumption.
  reflexivity.
Qed.

Ltac simpl_byte :=
  match goal with
  | [ |- context E [ CeresString.eqb_byte ?x ?x ] ] => rewrite eqb_byte_refl
  | [ |- context E [ CeresString.eqb_byte ?x ?y ] ] => rewrite neqb_byte_neq by congruence
  end.

Ltac simpl_bytes :=
  repeat simpl_byte.


Global
Instance CompleteClass_spec_float : CompleteClass SpecFloat.spec_float.
Proof.
  unfold CompleteClass, Complete.
  intros l [];
    unfold _from_sexp; cbn -[_from_sexp].
  - simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn.
    simpl_bytes.
    reflexivity.
  - simpl_bytes.
    rewrite !complete_class.
    reflexivity.
Qed.

Global
Instance SoundClass_spec_float : SoundClass SpecFloat.spec_float.
Proof.
  intros l e a Ee; apply sound_match_con in Ee.
  destruct Ee as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
  - destruct Ee as [E1 E2]; subst; reflexivity.
  - destruct Ee as [es [<- Ea]].
    sound_field Ea.
    apply sound_class in Ea1.
    cbn.
    rewrite Ea1.
    reflexivity.
  - destruct Ee as [es [<- Ea]].
    sound_field Ea.
    apply sound_class in Ea1.
    cbn.
    rewrite Ea1.
    reflexivity.
  - destruct Ee as [es [<- Ea]].
    sound_field Ea.
    apply sound_class in Ea0.
    apply sound_class in Ea1.
    apply sound_class in Ea2.
    cbn.
    rewrite Ea0.
    rewrite Ea1.
    rewrite Ea2.
    reflexivity.
Qed.

Global
Instance CompleteClass_prim_float : CompleteClass PrimFloat.float.
Proof.
  unfold CompleteClass, Complete.
  intros.
  unfold _from_sexp, Deserialize_prim_float.
  specialize CompleteClass_spec_float as H.
  unfold CompleteClass, Complete, _from_sexp in H.
  unfold to_sexp, Serialize_prim_float.
  rewrite H.
  rewrite FloatAxioms.Prim2SF_valid.
  rewrite FloatAxioms.SF2Prim_Prim2SF.
  reflexivity.
Qed.

Global
Instance SoundClass_prim_float : SoundClass PrimFloat.float.
Proof.
  intros l e a Ee.
  unfold _from_sexp, Deserialize_prim_float in Ee.
  destruct Deserialize_spec_float eqn:H in Ee; try discriminate.
  apply sound_class in H.
  destruct SpecFloat.valid_binary eqn:Hvalid in Ee; try discriminate.
  injection Ee as <-.
  unfold to_sexp, Serialize_prim_float.
  rewrite FloatAxioms.Prim2SF_SF2Prim; auto.
Qed.

Module StrongSound.

  (* Strong soundness *)

  Inductive SoundClassStrong (P : sexp -> Prop) : sexp -> Prop :=
  | SoundAtom : forall a,
      P (Atom a) ->
      SoundClassStrong P (Atom a)
  | SoundList : forall es,
      P (List es) ->
      Forall (SoundClassStrong P) es ->
      SoundClassStrong P (List es).

  Lemma SoundClassStrong_implies_P {P : sexp -> Prop} :
    forall e,
      SoundClassStrong P e -> P e.
  Proof.
    intros e Hss.
    inversion Hss; auto.
  Qed.

  Lemma SoundClassStrong_List_inv {P : sexp -> Prop} :
    forall es,
      SoundClassStrong P (List es) ->
        Forall (SoundClassStrong P) es.
  Proof.
    intros es Hss.
    inversion Hss; auto.
  Qed.

  Lemma Forall_SoundClassStrong_Forall_P {P : sexp -> Prop} :
    forall es,
      Forall (SoundClassStrong P) es ->
        Forall P es.
  Proof.
    intros es Hss.
    induction Hss as [| e es' Hss_e Hss_es' IH]; constructor.
    - apply SoundClassStrong_implies_P.
      assumption.
    - assumption.
  Qed.



  (* Soundness helper lemmas *)

  Local Lemma sound_class_list_forall_aux {A : Type}
                                   `{Serialize A}
                                   `{Deserialize A}
                                    (es : list sexp) :
    forall xs n l a,
      Forall (fun e => forall l' t, _from_sexp l' e = inr t -> to_sexp t = e) es ->
      _sexp_to_list _from_sexp xs n l es = inr a ->
      map to_sexp a = (map to_sexp (rev xs) ++ es).
  Proof.
    induction es as [| e es IH].
    - (* nil *)
      intros xs n l ts Hall Hdes.
      cbn in Hdes.
      injection Hdes as <-.
      rewrite rev_alt.
      rewrite app_nil_r.
      reflexivity.
    - (* cons *)
      intros xs n l ts Hall Hdes.
      cbn in Hdes.
      destruct (_from_sexp _ e) as [? | t] eqn:Hdes_e; try discriminate.
      inversion Hall as [|e' es' He Hes' Heq1]; subst.
      apply IH in Hdes; auto.
      rewrite Hdes; cbn.
      rewrite map_app; cbn.
      erewrite He; eauto.
      rewrite <- app_assoc; cbn.
      reflexivity.
  Qed.

  Lemma sound_class_list_forall {A : Type}
                               `{Serialize A}
                               `{Deserialize A}
                                (es : list sexp) :
    forall l xs,
      Forall (fun e => forall l' t, _from_sexp l' e = inr t -> to_sexp t = e) es ->
      _sexp_to_list _from_sexp nil 0 l es = inr xs ->
      map to_sexp xs = es.
  Proof.
    intros.
    erewrite sound_class_list_forall_aux; eauto.
    cbn.
    reflexivity.
  Qed.

  Lemma sound_class_list_strong {A : Type}
       `{Serialize A}
       `{Deserialize A}
        (P : sexp -> Prop)
        (HP : forall e, P e -> forall l' t, _from_sexp l' e = inr t -> to_sexp t = e) :
    forall es,
    Forall (SoundClassStrong P) es ->
    forall l xs,
      _sexp_to_list _from_sexp nil 0 l es = inr xs ->
      map to_sexp xs = es.
  Proof.
    intros.
    erewrite sound_class_list_forall; eauto.
    apply Forall_SoundClassStrong_Forall_P in H1.
    eapply Forall_impl; [| exact H1].
    exact HP.
  Qed.

  Lemma sound_class_list_prod_strong {A B : Type}
       `{Serialize B} `{Deserialize B}
       `{SoundClass A}
        (P : sexp -> Prop)
        (HP : forall e, P e -> forall l' (t : B), _from_sexp l' e = inr t -> to_sexp t = e) :
    forall es l (xs : list (A * B)),
      Forall (SoundClassStrong P) es ->
      _sexp_to_list _from_sexp nil 0 l es = inr xs ->
      map (fun p => List [to_sexp (fst p); to_sexp (snd p)]) xs = es.
  Proof.
    intros.
    eapply sound_class_list_forall; eauto.
    eapply Forall_impl; [| exact H4].
    intros e HPe l' t Hdes.
    destruct t as [a b].
    unfold _from_sexp, Deserialize_prod in Hdes.
    destruct e; try discriminate.
    destruct xs0; try discriminate.
    destruct xs0; try discriminate.
    destruct xs0; try discriminate.
    destruct (_from_sexp _ s) eqn:Hdesa in Hdes; try discriminate.
    destruct (_from_sexp _ s0) eqn:Hdesb in Hdes; try discriminate.
    injection Hdes as <- <-.
    apply sound_class in Hdesa as <-.
    inversion HPe as [|? HP_list Hss_inner]; subst.
    apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
    apply List.Forall_cons_iff in Hss_inner as [Hss_b _].
    apply SoundClassStrong_implies_P in Hss_b.
    eapply HP in Hss_b as <-; eauto.
    cbn. reflexivity.
  Qed.

  Lemma sound_class_list_sum_strong {A B : Type}
       `{Serialize B} `{Deserialize B}
       `{SoundClass A}
        (P : sexp -> Prop)
        (HP : forall e, P e -> forall l' (t : B), _from_sexp l' e = inr t -> to_sexp t = e) :
    forall es l (xs : list (A + B)),
      Forall (SoundClassStrong P) es ->
      _sexp_to_list _from_sexp nil 0 l es = inr xs ->
      map to_sexp xs = es.
  Proof.
    intros.
    eapply sound_class_list_forall; eauto.
    eapply Forall_impl; [| exact H4].
    intros e HPe l' t Hdes.
    unfold _from_sexp, Deserialize_sum in Hdes.
    apply sound_match_con in Hdes.
    destruct Hdes as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
    - destruct Ee as [es' [<- Ea]].
      sound_field Ea.
      apply sound_class in Ea1 as <-.
      cbn. reflexivity.
    - destruct Ee as [es' [<- Ea]].
      sound_field Ea.
      inversion HPe as [|? HP_list Hss_inner]; subst.
      apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
      apply List.Forall_cons_iff in Hss_inner as [Hss_e _].
      apply SoundClassStrong_implies_P in Hss_e.
      eapply HP in Hss_e as <-; eauto.
      cbn. reflexivity.
  Qed.

  Lemma sound_class_list_option_strong {A : Type}
       `{Serialize A} `{Deserialize A}
        (P : sexp -> Prop)
        (HP : forall e, P e -> forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) :
    forall es l (xs : list (option A)),
      Forall (SoundClassStrong P) es ->
      _sexp_to_list _from_sexp nil 0 l es = inr xs ->
      map to_sexp xs = es.
  Proof.
    intros.
    eapply sound_class_list_forall; eauto.
    eapply Forall_impl; [| exact H1].
    intros e HPe l' t Hdes.
    unfold _from_sexp, Deserialize_option in Hdes.
    apply sound_match_con in Hdes.
    destruct Hdes as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
    - destruct Ee as [E1 E2]; subst; reflexivity.
    - destruct Ee as [es' [<- Ea]].
      sound_field Ea.
      inversion HPe as [|? HP_list Hss_inner]; subst.
      apply List.Forall_cons_iff in Hss_inner as [_ Hss_inner].
      apply List.Forall_cons_iff in Hss_inner as [Hss_e _].
      apply SoundClassStrong_implies_P in Hss_e.
      eapply HP in Hss_e as <-; eauto.
      cbn. reflexivity.
  Qed.

  Lemma sound_class_list_list_strong {A : Type}
       `{Serialize A} `{Deserialize A}
        (P : sexp -> Prop)
        (HP : forall e, P e -> forall l' (t : A), _from_sexp l' e = inr t -> to_sexp t = e) :
    forall es l (xs : list (list A)),
      Forall (SoundClassStrong P) es ->
      _sexp_to_list _from_sexp nil 0 l es = inr xs ->
      map to_sexp xs = es.
  Proof.
    intros.
    eapply sound_class_list_forall; eauto.
    eapply Forall_impl; [| exact H1].
    intros e HPe l' t Hdes.
    unfold _from_sexp, Deserialize_list in Hdes.
    destruct e; try discriminate.
    unfold to_sexp, Serialize_list.
    erewrite sound_class_list_forall; eauto.
    apply SoundClassStrong_List_inv in HPe.
    eapply Forall_impl; [| exact HPe].
    intros e HPe' ? t' Hdes'.
    apply SoundClassStrong_implies_P in HPe'.
    eapply HP in HPe' as <-; eauto.
  Qed.

End StrongSound.
