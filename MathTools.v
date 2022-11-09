From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory.
Open Scope ring_scope.

Goal forall (K : fieldType) (E : vectType K) (x y : E), x + y = y + x.
Proof.
  move=> K E x y.
