From Coq Require Export String.
Require Import Coq.Init.Nat.

(* Teoremas do Induction.v e Basics.v*)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl.
    rewrite add_0_r.
    reflexivity.
  - simpl.
    rewrite <- plus_n_Sm.
    rewrite IHn.
    reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  assert(H: n + m = m + n). 
    {rewrite add_comm. reflexivity. }
  rewrite H.
  rewrite add_assoc.
  reflexivity.
Qed.

Lemma mult_n_Sm:
  forall m n: nat,
  n * S m = n + (n * m).
Proof.
  intros m n.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    rewrite add_shuffle3.
    reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [ | n' IHn].
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity. 
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m.
  - rewrite mul_0_r.
    reflexivity.
  - simpl.
    rewrite mult_n_Sm.
    rewrite IHm.
    reflexivity.
Qed.

(*Fim dos Teoremas*)

Fixpoint div2 (n:nat) : nat :=
  match n with
  | O => O
  | S O => O 
  | S (S n') => S (div2 n')  
end.  

Fixpoint sum (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n + sum n'
  end.

Theorem plus_n_1 : forall (n : nat),
  n + 1 = S (n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall (n m:nat),
  n + S m = S (n + m).
Proof. 
  intros n m.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.  
Qed.

Theorem mult_2_n_plus : forall (n : nat),
  n + n = 2 * n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite add_0_r.
    reflexivity.
Qed.

Theorem mul2_div2 : forall n : nat,
  n = div2 (2 * n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - rewrite mult_n_Sm.
    simpl.
    rewrite add_0_r.
    rewrite mult_2_n_plus.
    rewrite <- IHn.
    reflexivity.
Qed.

Theorem div2_mult2_plus: forall (n m : nat),
  n + div2 m = div2 (2 * n + m).
Proof.
  intros n m.
  induction n.
  - reflexivity.
  - rewrite mult_n_Sm.
    simpl.
    rewrite add_0_r.
    rewrite mult_2_n_plus.
    rewrite <- IHn.
    reflexivity.
Qed.

Theorem mult_Sn_m : forall (n m : nat),
  S n * m = m + n * m.
Proof.
  intros n m.
  rewrite mul_comm.
  rewrite mult_n_Sm.
  rewrite <- mul_comm.
  reflexivity.
Qed.

Theorem sum_Sn : forall n : nat,
  sum (S n) = S n + sum n.
Proof.
  reflexivity.
Qed.
Theorem mult_dist: forall a b, a*(b+1) = a*b + a.
Proof.
  intros. induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- add_assoc. rewrite IHa. simpl.
  rewrite plus_n_Sm. rewrite add_assoc. rewrite <- plus_n_Sm.
  reflexivity.
Qed.

Theorem gaussSum : forall n, (sum n) = div2 (n*(n+1)).
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - rewrite mult_dist. rewrite -> sum_Sn. rewrite <- plus_n_1.
    rewrite IHn.
    rewrite div2_mult2_plus. simpl. rewrite add_0_r.
    rewrite mult_dist. rewrite  mult_dist.
    rewrite  <- mult_dist. rewrite add_comm. rewrite -> mul_comm.
    rewrite -> add_assoc. reflexivity.
Qed.


Definition even (n:nat):bool :=
  match n with
  |O => true
  |S O => false
  |S (S n') => even n'
  end.
Definition odd (n:nat):bool := 
  negb(even n).



