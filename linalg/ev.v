Require Import
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.vectorspace
  MathClasses.theory.groups.

Module Exercise1.
  Lemma f_equiv' `{Equiv A} `{f : A -> A} :
    f = f -> forall x y, x = y -> f x = f y.
  Proof.
    intros.
    f_equiv.
    assumption.
  Qed.

  Lemma one : forall `{HVS : VectorSpace K V}, forall (u : V), 0 · u = mon_unit.
  Proof.
    intros.
    setoid_rewrite <- left_identity.
    setoid_rewrite <- left_inverse with (x := 1 · u).
    setoid_rewrite <- associativity.
    apply f_equiv'.
    { cbv; intros ?? Hxy; now rewrite Hxy. }
    setoid_rewrite <- distribute_r.
    cbv; now group.
  Qed.

  Lemma two : forall `{HVS : VectorSpace K V}, forall (α : K), α · mon_unit = mon_unit.
  Proof.
    intros.
    rewrite <- right_identity.
    rewrite <- (right_inverse (α · mon_unit)) at 2 3.
    rewrite associativity.
    apply (f_equiv' (f := fun v => v & - (α · mon_unit)));
      [ cbv; intros ?? Hxy; now rewrite Hxy |].
    rewrite <- distribute_l.
    pose scalar_mult_proper.
    rewrite left_identity.
    reflexivity.
  Qed.

  Lemma three : forall `{HVS : VectorSpace K V}, forall (u : V), -1 · u = -u.
  Proof.
    intros.
    setoid_rewrite <- right_identity.
    setoid_rewrite <- (right_inverse u).
    setoid_rewrite associativity.
    apply (f_equiv' (f := fun v => v & - u));
      [ cbv; intros ?? Hxy; now rewrite Hxy |].
    rewrite left_inverse.
    rewrite <- (left_identity u (op := (·))) at 2.
    rewrite <- distribute_r.
    pose scalar_mult_proper.
    rewrite left_inverse.
    apply one.
  Qed.

End Exercise1.

Module Exercise2.
  Module i.
    Require Import
      Coq.Vectors.Vector
      MathClasses.theory.dec_fields
      Field.
    Import VectorNotations.

    Open Scope vector_scope.

    Context F `{DecField F}.
    Add Field F: (stdlib_field_theory F).

    Definition vec := Vector.t F.

    Definition vec_constant {n : nat} (c : F) : vec n := Vector.const c n.

    Instance vec_zero {n : nat} : Zero (vec n) := Vector.const 0 n.

    Instance vec_eq {n : nat} : Equiv (vec n) :=
      fold_right2 (fun α β S => α = β /\ S) True n.

    Instance: forall {n : nat}, Reflexive (vec_eq (n := n)).
    Proof.
      intros n x.
      induction x.
      - simpl. apply I.
      - split; [reflexivity | assumption].
    Qed.

    (* If you're reading this on HEAD, please help me replace this [≡] into a [=] *)
    Lemma vec_n0_eq_empty : forall (v : vec 0), v ≡ [].
    Proof.
      apply case0.
      reflexivity.
    Qed.

    Lemma vec_cons_eq : forall {n : nat} (u v : vec n) (α β : F), (α::u = β::v) <-> α = β /\ u = v.
    Proof.
      easy.
    Qed.

    (* If you're reading this on HEAD, please help me replace this [≡] into a [=] *)
    Lemma vec_exists_head : forall {n : nat} (v : vec (S n)), exists (hd : F) (tl : vec n), hd::tl ≡ v.
    Proof.
    Admitted.

    Instance: forall {n : nat}, Symmetric (vec_eq (n := n)).
    Proof.
      intros n x y Heq.
      induction n.
      - rewrite (vec_n0_eq_empty x), (vec_n0_eq_empty y).
        reflexivity.
      - specialize (vec_exists_head x) as [x0 [xt Heq_xht]].
        specialize (vec_exists_head y) as [y0 [yt Heq_yht]].
        rewrite <- Heq_xht in *.
        rewrite <- Heq_yht in *.
        (* You know when you have this feeling that you're doing something wrong,
           but you have no clue what this is ? *)
        apply vec_cons_eq.
        split.
        all:destruct (vec_cons_eq xt yt x0 y0) as [H0 Hosef].
        -- pose proof (H0 Heq) as [Hs _].
           symmetry in Hs.
           assumption.
        -- pose proof (H0 Heq) as [_ Hs].
           specialize (IHn xt yt Hs).
           assumption.
    Qed.
  End i.

End Exercise2.
