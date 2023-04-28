
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
Theorem plus_n_Sm2 : forall n m : nat,
  S (n + m) = S n + m.
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
Theorem n_times_0: forall n, n * 0 = 0.
Proof.
intros n. induction n. 
-reflexivity.
-simpl. rewrite -> IHn. reflexivity.
Qed.
Lemma add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [|n' IHn'].
  +simpl. reflexivity.
  +simpl. rewrite <- IHn'. reflexivity.
Qed.
Lemma add_assoc2: forall a b c,
  a + (b + c) = b + (a + c).
Proof.
  intros. induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa. rewrite plus_n_Sm. reflexivity.
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

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros.
  assert (H: n + 0 + 0 = n).
  - rewrite add_zero. rewrite add_zero. reflexivity.
  - rewrite H. reflexivity.
Qed.

Theorem plus_assoc: forall a b, a + b = b + a.
Proof.
  intros. induction a as [|k IHk].
  - rewrite <- add_zero. simpl. reflexivity.
  - simpl. rewrite IHk. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem succ_n_plus_1: forall n, n + 1 = S n.
Proof.
  induction n.
  -reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem mult_dist: forall a b, a*(b+1) = a*b + a.
Proof.
  intros. induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- add_assoc. rewrite IHa. simpl.
  rewrite plus_n_Sm. rewrite add_assoc.
  reflexivity.
Qed.

Lemma aux': forall a b, b + b * a = b * S a.
Proof.
  intros; induction a.
  - rewrite n_times_0. replace (b*1) with (b).
    rewrite <- add_zero. reflexivity.
    induction b.
    + reflexivity.
    + simpl. rewrite <- IHb. reflexivity.
  - rewrite <- succ_n_plus_1. 
  rewrite -> mult_dist. rewrite add_assoc. rewrite IHa.
  rewrite plus_n_Sm2. rewrite mult_dist. reflexivity.
Qed.
  
Theorem mult_com: forall a b, a * b = b * a.
Proof.
  intros. induction a.
  - simpl; rewrite mul_0_r. reflexivity.
  - simpl.
    rewrite plus_assoc. rewrite <- aux'.
    rewrite add_comm. rewrite IHa. reflexivity.
Qed.
  
(*Exercicios feitos por conta (Que nao estao do livro)*)

Fixpoint sum (x : nat) : nat :=
  match x with
  |O => O
  |S (x') => x + (sum x')
  end.
Fixpoint div2 (n : nat) : nat :=
  match n with 
  |O => O
  |S O => O
  |S(S n') => 1 + (div2 n')
  end.

Theorem gaussSum : forall n, (sum n) = div2 (n*(n+1)).
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - rewrite mult_dist. rewrite <- succ_n_plus_1.
    replace (sum (n+1)) with (sum(n) +(n + 1)).
    + rewrite IHn. rewrite mult_com.