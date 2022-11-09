Module Exercise1.

(* This exercise was done using MathClasses. I'll stick to mathcomp in the future. *)

Require Import
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.vectorspace
  MathClasses.theory.groups.

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
    (** The exercice statement is simply (translated) :
     Prove that the set K^n with the following operations :
            (x_1, ..., x_n) + (y_1, ..., y_n) = (x_1 + y_1, ..., x_n + y_n)
         and
            λ·(x_1, ..., x_n) = (λ × x_1, ..., λ × x_n)
     is a vector space.

     So I figured that would be the occasion the learn how to properly define Mathclasses structures.
     That's why this Module is so long, apologies. *)
    
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

    Instance vec_add {n : nat} : Plus (vec n) :=
      map2 (fun α β => α + β).

    Instance vec_neg {n : nat} : Negate (vec n) :=
      map (fun α => - α).

    Instance vec_scal {n : nat} : ScalarMult F (vec n) :=
      fun α => map (fun β => α * β).

    Instance: forall {n : nat}, Reflexive (vec_eq (n := n)).
    Proof.
      intros n x.
      induction x.
      - simpl. apply I.
      - split; [reflexivity | assumption].
    Qed.

    Lemma vec0_eq_nil : forall v : vec 0, v ≡ [].
    Proof with reflexivity. apply case0... Qed.

    Lemma vec_cons_eq : forall {n : nat} (u v : vec n) (α β : F), (α::u = β::v) <-> α = β /\ u = v.
    Proof. split; intros; assumption. Qed.

    Lemma vec0_eq_proper : Proper (equiv ==> equiv ==> flip impl) (vec_eq (n := 0)).
    Proof.
      repeat intro.
      assert (nil F ≡ nil F) by reflexivity.
      rewrite (vec0_eq_nil x), (vec0_eq_nil x0).
      reflexivity.
    Qed.

    Instance: forall {n : nat}, Symmetric (vec_eq (n := n)).
    Proof.
      intros n u v Heq.
      induction n.
      - pose vec0_eq_proper.
        rewrite (vec0_eq_nil v), (vec0_eq_nil u).
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
        rewrite (vec0_eq_nil u), (vec0_eq_nil v) in *.
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

    Instance: forall {n : nat}, Setoid (vec n).
    Proof. split; apply _. Qed.

    Lemma vec0_add_proper : Proper (equiv ==> equiv ==> equiv) (vec_add (n := 0)).
    Proof.
      repeat intro.
      assert (nil F ≡ nil F) by reflexivity.
      rewrite (vec0_eq_nil x),
        (vec0_eq_nil x0),
        (vec0_eq_nil y),
        (vec0_eq_nil y0).
      reflexivity.
    Qed.

    Instance vec_add_commutative {n : nat} : Commutative (vec_add (n := n)).
    Proof.
      intros u v.
      induction n.
      - pose vec0_add_proper as Hp.
        rewrite (case0 (fun v => v = []) I v), (vec0_eq_nil u).
        reflexivity.
      - rewrite (eta u), (eta v) in *.
        split.
        + apply commutativity.
        + apply IHn.
    Qed.

    Instance vec_add_associative {n : nat} : Associative (vec_add (n := n)).
    Proof.
      intros u v z.
      induction n.
      - pose vec0_add_proper as Hp.
        rewrite (vec0_eq_nil v), (vec0_eq_nil u), (vec0_eq_nil z).
        reflexivity.
      - rewrite (eta u), (eta v), (eta z) in *.
        split.
        + apply associativity.
        + apply IHn.
    Qed.

    Lemma vec_add_proper {n : nat} : Proper (equiv ==> equiv ==> equiv) (vec_add (n := n)).
    Proof.
      induction n.
      - apply vec0_add_proper; assumption.
      - intros u v Heq_uv x y Heq_xy.
        rewrite (eta u), (eta v), (eta x), (eta y) in *.
        split; [apply sg_op_proper | apply IHn];
          try apply Heq_uv; try apply Heq_xy.
    Qed.
    
    Instance: forall {n : nat}, SemiGroup (vec n).
    Proof.
      split.
      apply _.
      apply _.
      apply vec_add_proper.
    Qed.

    Instance: forall {n : nat}, LeftIdentity (vec_add (n := n)) vec_zero.
    Proof.
      intros n v.
      induction n.
      - rewrite (vec0_eq_nil v).
        reflexivity.
      - rewrite (eta v), (eta vec_zero).
        split.
        + group.
        + apply IHn.
    Qed.

    Instance: forall {n : nat}, RightIdentity (vec_add (n := n)) vec_zero.
    Proof.
      intros n v.
      rewrite commutativity.
      apply left_identity.
    Qed.
    
    Instance: forall {n : nat}, Monoid (vec n).
    Proof. split; apply _. Qed.

    Instance: forall {n : nat}, Proper (equiv ==> equiv) (vec_neg (n := n)).
    Proof.
      intros n u v Heq.
      induction n.
      - rewrite (vec0_eq_nil u), (vec0_eq_nil v).
        reflexivity.
      - rewrite (eta u), (eta v) in *.
        split.
        + apply (negate_proper F).(sm_proper).
          apply Heq.
        + apply IHn.
          apply Heq.
    Qed.  

    Instance: forall {n : nat}, Setoid_Morphism (vec_neg (n := n)).
    Proof. split; apply _. Qed.

    Instance: forall {n : nat}, LeftInverse (vec_add (n := n)) (vec_neg (n := n)) vec_zero.
    Proof.
      intros n v.
      induction n.
      - rewrite (vec0_eq_nil v).
        reflexivity.
      - rewrite (eta v) in *.
        split.
        + apply left_inverse.
        + apply IHn.
    Qed.

    Instance: forall {n : nat}, RightInverse (vec_add (n := n)) (vec_neg (n := n)) vec_zero.
    Proof.
      intros n v.
      rewrite commutativity.
      apply left_inverse.
    Qed.

    Instance: forall {n : nat}, Group (vec n).
    Proof. split; apply _. Qed.
    
    Instance: forall {n : nat}, AbGroup (vec n).
    Proof. split; apply _. Qed.

    Instance: forall {n : nat}, LeftHeteroDistribute (vec_scal (n := n)) (vec_add (n := n)) (vec_add (n := n)).
    Proof.
      intros n α u v.
      induction n.
      - rewrite (vec0_eq_nil u), (vec0_eq_nil v).
        reflexivity.
      - rewrite (eta u), (eta v).
        split.
        + apply distribute_l.
        + apply IHn.
    Qed.

    (* Is there a Lemma I can prove to "automate" this ? Besides using Ltac. *)
    Instance: forall {n : nat}, RightHeteroDistribute (vec_scal (n := n)) (+) (vec_add (n := n)).
    Proof.
      intros n α β v.
      induction n.
      - rewrite (vec0_eq_nil v).
        reflexivity.
      - rewrite (eta v).
        split.
        + apply distribute_r.
        + apply IHn.
    Qed.

    Instance: forall {n : nat}, HeteroAssociative (vec_scal (n := n)) (vec_scal (n := n)) (vec_scal (n := n)) mult.
    Proof.
      intros n α β v.
      induction n.
      - rewrite (vec0_eq_nil v).
        reflexivity.
      - rewrite (eta v).
        split.
        + apply associativity.
        + apply IHn.
    Qed.

    Instance: forall {n : nat}, LeftIdentity (vec_scal (n := n)) 1.
    Proof.
      intros n v.
      induction n.
      - rewrite (vec0_eq_nil v).
        reflexivity.
      - rewrite (eta v).
        split.
        + apply left_identity.
        + apply IHn.
    Qed.

    Instance: forall {n : nat}, Proper (equiv ==> equiv ==> equiv) (vec_scal (n := n)).
    Proof.
      intros n α β Heq_αβ u v Heq_uv.
      induction n.
      - rewrite (vec0_eq_nil u), (vec0_eq_nil v).
        reflexivity.
      - rewrite (eta u), (eta v) in *.
        split.
        + apply sg_op_proper.
          * exact Heq_αβ.
          * apply Heq_uv.
        + apply IHn.
          apply Heq_uv.
    Qed.

    Instance: forall {n : nat}, Module F (vec n).
    Proof. split; apply _. Qed.

    Instance: forall {n : nat}, VectorSpace F (vec n).
    Proof. split; apply _. Qed.
  End i.

End Exercise2.

