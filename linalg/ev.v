Require Import
  Coq.Classes.Morphisms
  MathClasses.interfaces.abstract_algebra
  MathClasses.interfaces.vectorspace
  MathClasses.misc.workaround_tactics
  MathClasses.theory.setoids
  MathClasses.theory.groups.

Lemma f_equiv' `{Equiv A} `{f : A -> A} :
  f = f -> forall x y, x = y -> f x = f y.
Proof.
  intros.
  f_equiv.
  assumption.
Qed.

Goal forall `{HVS : VectorSpace K V}, forall u : V, 0 · u = mon_unit.
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
