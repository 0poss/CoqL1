From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory.

Open Scope ring_scope.

Definition Sequence (K : fieldType) := nat -> K.
Definition SequenceSum {K : fieldType} (s : Sequence K) (n : nat) := \sum_(0 <= i < n.+1) s i.

Inductive GeometricSequence {K : fieldType} : Sequence K -> K -> Prop :=
| geo_seq (s : Sequence K) (q : K) (H : forall (n : nat), s n * q = s n.+1) : GeometricSequence s q.

Lemma sum_distrr {K : fieldType} (m n : nat) (s : Sequence K) (q : K) :
    q * (\sum_(m <= i < n) s i) = \sum_(m <= i < n) q * s i.
Proof.
  by rewrite big_distrr.
Qed.

Lemma sum_extract_fst {K : fieldType} (s : Sequence K) (m n : nat) :
  (m <= n)%N -> \sum_(m <= i < n.+1) s i = s m + \sum_(m <= i < n) s i.+1.
Proof.
  move => le_mn.
  by rewrite big_nat_recl.
Qed.

Lemma sum_extract_lst {K : fieldType} (s : Sequence K) (m n : nat) :
  (m <= n)%N -> \sum_(m <= i < n.+1) s i = \sum_(m <= i < n) s i + s n.
Proof.
  move => le_mn.
  by rewrite big_nat_recr/=.
Qed.

Lemma geo_seq_n_term {K : fieldType} (s : Sequence K) (q : K) :
  GeometricSequence s q -> forall (n : nat), s n = s O * q ^+ n.
Proof.
  move => geo_s.
  inversion geo_s.
  clear s0 q0 H0 H1.
  elim => [|n IHn].
    by rewrite mulrC mul1r.
  rewrite -H IHn.
  by rewrite -mulrA -exprSr.
Qed.

Lemma one_minus_q_product_development {K : fieldType} (q : K) (n : nat) :
  (1-q) * SequenceSum (fun (i:nat) => q ^+ i) n = 1 - q ^+ n.+1.
Proof.
  rewrite /SequenceSum mulrBl.
  rewrite {1}sum_extract_fst//.
  rewrite sum_distrr.
  rewrite sum_extract_lst//.
  under (eq_bigr (F1 := fun i => q * q ^+ i)) do rewrite -exprS.
  rewrite -exprS.
  rewrite mul1r.
  by rewrite addrKA.
Qed.

Lemma GeometricSequence_Sum {K : fieldType} (s : Sequence K) (q : K) :
  q <> 1 -> GeometricSequence s q -> forall n : nat, SequenceSum s n = s O * (1 - q ^+ n.+1) / (1 - q).
Proof.
  move => neq_q1 geo_s n.
  inversion geo_s.
  clear s0 q0 H0 H1.
  rewrite /SequenceSum.
  under eq_bigr => i*.
    by rewrite (geo_seq_n_term s q)// over.
  rewrite -sum_distrr.
  rewrite -(mul1r (\sum_(_ <= i < _.+1) _)).
  have: 1 - q <> 0.
  rewrite -(mulKf (F := K) (x := 1 - q)).
