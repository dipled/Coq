Require Import Coq.Arith.PeanoNat.
Require Import Arith.
From Coq Require Export String.
Inductive bool :Type :=
  |true
  |false.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  |true, true => true
  |_, _ => false
  end.
Definition neg (b:bool) : bool :=
  match b with
  |false => true
  |true => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  |false => b2
  |true => true
  end.

Fixpoint somatorio (n:nat) : nat :=
  match n with 
  |O => O 
  |S n' => n + (somatorio n')
  end.

Fixpoint div2 (n:nat) : nat := 
  match n with
  |O => O
  |S O => O
  |S (S n') => 1 + (div2 n')
  end.

Theorem dem_1: forall a b: bool, (neg (orb a  b)) = andb (neg a) (neg b).
Proof.
intros [] [].
-simpl. reflexivity.
-simpl. reflexivity.
-simpl. reflexivity.
-simpl. reflexivity.
Qed.

Theorem dem_2: forall a b: bool, (neg (andb a b)) = orb (neg a) (neg b).
Proof.
  intros a b.
  destruct a as [].
  -destruct b as [].
    +simpl. reflexivity.
    +simpl. reflexivity.
  -destruct b.
    +simpl. reflexivity.
    +simpl. reflexivity.
Qed.
Theorem succ_n_plus_0: forall n, S n = S (n+0).
Proof. induction n as [|n' IHn'].
  -reflexivity.
  -simpl. rewrite IHn'. reflexivity.
Qed.

Theorem n_plus_0: forall n, n = (n+0).
Proof. induction n as [|n' IHn'].
  -reflexivity.
  -simpl. rewrite succ_n_plus_0. rewrite IHn'. reflexivity.
Qed.

Theorem plus_succ: forall a b, S(a+b) = a + S(b).
Proof. intros a b. induction a.
- simpl. reflexivity.
- simpl. rewrite <- IHa. reflexivity.
Qed.

Theorem pluscom: forall a b, a + b = b + a.
Proof.
intros a b.
induction a as [|a' IHa']. 
- simpl. rewrite <- n_plus_0. reflexivity.
- simpl. rewrite IHa'. rewrite plus_succ. reflexivity.
Qed.

Theorem n_times_0: forall n, n * 0 = 0.
Proof.
intros n. induction n. 
-reflexivity.
-simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem n_times_1: forall n, n * 1 = n.
Proof.
  intros b.
  induction b.
  - simpl. reflexivity.
  - simpl. rewrite IHb. reflexivity.
Qed.

Theorem plus_n_1_succ_n: forall n, n + 1 = S n.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_1_n_succ_n: forall n, 1 + n = S n.
  Proof.
    intros n.
    induction n.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  Theorem plus_one_ass: forall a b, 1 + (a + b) = (a + 1 + b).
Proof.
  intros a b.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_1_succ_n. 
  rewrite <- plus_n_1_succ_n. 
  rewrite -> plus_n_1_succ_n.
  rewrite <- pluscom. rewrite IHa. reflexivity.
Qed.

Theorem plus_1_n_n_1: forall n, 1 + n = n + 1.
Proof.
  intros n. induction n.
  - reflexivity.
  - rewrite plus_n_1_succ_n. rewrite <- plus_n_1_succ_n. rewrite -> plus_n_1_succ_n. reflexivity.
Qed.

Theorem one_plus_sum: forall a b, 1 + (a+b) = (1 + a + b).
Proof.
  intros a c.
  induction a.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem plusass: forall a b c, a + (b + c) = b + (a + c).
Proof.
  intros a b c. induction a.
  -simpl. reflexivity.
  -simpl. rewrite IHa. rewrite plus_succ. reflexivity. 
Qed.

Theorem multdist: forall a b : nat,  b + b * a = b * S a.
Proof.
  intros a b. induction b.
  - simpl. reflexivity.
  - simpl. rewrite <- IHb. rewrite plusass. reflexivity.
Qed.

Theorem multcom: forall a b, a * b = b * a.
Proof.
  intros a b. 
  induction a.
  -simpl. rewrite n_times_0. reflexivity.
  -simpl. rewrite <- multdist. rewrite <- IHa. reflexivity. 
Qed.

Lemma somatorio_destruir: forall n : nat,
  somatorio (S n) = (S n) + somatorio n.
Proof.
  intros. induction n.
  -simpl. reflexivity.
  -simpl. reflexivity.
Qed.

Theorem somatorio_formula: forall n:nat,
  somatorio n = div2(n*(S(n))).
Proof.
  intros. induction n as [| k IHk].
  -simpl. reflexivity.
  -rewrite somatorio_destruir. rewrite IHk. simpl.
Qed.