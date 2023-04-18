Require Import Coq.Arith.PeanoNat.
Require Import Arith.
From Coq Require Export String.
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  -reflexivity.
  -simpl. rewrite IHn'. reflexivity.
Qed.
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros. induction n.
  -simpl. reflexivity.
  -simpl. rewrite -> IHn. reflexivity.
Qed.
Theorem add_zero : forall n : nat,
  n = n + 0.
Proof.
  intros. induction n.
  -reflexivity.
  -simpl. rewrite <- IHn. reflexivity.
Qed.
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros. induction n.
  -simpl. rewrite <- add_zero. reflexivity.
  -simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
Qed. 
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [|n' IHn'].
  +simpl. reflexivity.
  +simpl. rewrite <- IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n.
  *simpl. reflexivity.
  *simpl. rewrite -> IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros. induction n as [| k IHk].
  -simpl. reflexivity.
  -simpl. rewrite IHk. reflexivity.  
Qed.
Fixpoint even (n:nat) : bool  := 
  match n with
  |O => true
  |S O => false
  |S (S n') => even n'
  end.
(*O Lemma a seguir sera usado para provar o Teorema even_S*)
Lemma double_negb: forall b : bool,
  b = negb(negb b).
Proof.
  intros [].
  -simpl. reflexivity. 
  -simpl. reflexivity.
Qed.
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros. induction n as [|k IHk].
  +simpl. reflexivity.
  +rewrite -> IHk. 
  simpl. 
  rewrite <- double_negb. 
  reflexivity.
Qed.