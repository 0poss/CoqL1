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

    Lemma vec_cons_eq : forall {n : nat} (u v : vec n) (α β : F), (α::u = β::v) <-> α = β /\ u = v.
    Proof.
      split; intros; assumption.
    Qed.

    Lemma vec0_eq_proper : Proper (equiv ==> equiv ==> flip impl) (vec_eq (n := 0)).
    Proof.
      repeat intro.
      assert (nil F ≡ nil F) by reflexivity.
      rewrite (case0 (fun v : vec 0 => v ≡ nil F) H3 x).
      rewrite (case0 (fun v : vec 0 => v ≡ nil F) H3 x0).
      reflexivity.
    Qed.

    Instance: forall {n : nat}, Symmetric (vec_eq (n := n)).
    Proof.
      intros n u v Heq.
      induction n.
      - pose vec0_eq_proper.
        rewrite (case0 (fun v => v = []) I v), (case0 (fun v => v = []) I u).
        reflexivity.
      - rewrite (eta u), (eta v) in *.
        apply vec_cons_eq.
        destruct (vec_cons_eq (tl u) (tl v) (hd u) (hd v)) as [Hi _].
        pose proof (Hi Heq) as [Hs_hd Hs_tl].
        split.
        + symmetry.
          exact Hs_hd.
        + apply IHn.
          exact Hs_tl.
    Qed.

    Instance: forall {n : nat}, Transitive (vec_eq (n := n)).
    Proof.
      intros n u v z Heq_uv Heq_vz.
      (* Maybe I'll avoid writing a [vec_eq_ind] function eternally *)
      induction n.
      - pose vec0_eq_proper as Hp.
        rewrite (case0 (fun v => v = []) I u), (case0 (fun v => v = []) I v) in *.
        exact Heq_vz.
      - rewrite (eta u), (eta v), (eta z) in *.
        destruct (vec_cons_eq (tl u) (tl v) (hd u) (hd v)) as [Hi_uv _].
        destruct (vec_cons_eq (tl v) (tl z) (hd v) (hd z)) as [Hi_vz _].
        pose proof (Hi_uv Heq_uv) as [Hs_hd_uv Hs_tl_uv].
        pose proof (Hi_vz Heq_vz) as [Hs_hd_vz Hs_tl_vz].
        split.
        + transitivity (hd v).
          * exact Hs_hd_uv.
          * exact Hs_hd_vz.
        + apply IHn with (v := (tl v)).
          * exact Hs_tl_uv.
          * exact Hs_tl_vz.
    Qed.
  End i.

End Exercise2.
