From Coq Require Export String.
From Coq Require Import Unicode.Utf8_core.
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

Fixpoint even (n:nat):Prop :=
  match n with
  |O => True
  |S O => False
  |S (S n') => even n'
  end.

Definition odd (n: nat): Prop :=  ~(even n).

Fixpoint eqNat (n m : nat) : bool :=
  match n,m with
  |O, O => true
  |O, _ => false
  |_, O => false
  |S n', S m' => eqNat n' m'
  end.

Theorem contras: forall A B : Prop,
  (A -> B) -> (~B -> ~A).
Proof.
  intros A B. intro. intro. intro. apply H in H1. 
    apply H0 in H1. destruct H1.
Qed.


Definition eqBool (a b: bool): bool :=
  match a,b with
  |true, true => true
  |false, false => true
  |_,_ => false
  end.

Lemma not_equals_eq: forall a: bool,
  a = false <-> a <> true.
Proof.
  intros. destruct a.
  - split.
    + intro. discriminate.
    + intro. destruct H. reflexivity.
  - split.
    + intro. discriminate.
    + intro. reflexivity. 
Qed.

Theorem even_n_SSn: forall n : nat,
  even(n) = even(S (S n)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem even_n_odd: ∀n: nat,
  even n -> ~(odd n).
Proof.
  intros.
  induction n.
  - change (odd 0) with (~(even 0)).
    intro. apply H0 in H. destruct H.
  - change (odd (S n)) with (~(even (S n))).
    intro. apply H0 in H. destruct H.
Qed.

Theorem odd_n_even: ∀n: nat,
~(odd n) -> even n.
Proof.
  intros. induction n.
  - simpl. apply I.
  - apply even_n_odd.

Theorem even_n_Sn: forall n: nat,
even(S n) ->  ~(even n).
Proof.
  intros. induction n.
  - intro. simpl in H. destruct H.
  - intro.
    rewrite <- even_n_SSn in H. 
    apply IHn in H0. apply H0 in H; destruct H.
Qed.

(* Theorem even_lem: ∀n: nat,
  even(n) \/ ~even n.
Proof.
  intros. induction n.
  - left. 
  (*Aparentemente a lib de logica do Coq tem um axioma
  que diz que True é sempre uma proposicao verdadeira*)
  apply I.
  - destruct IHn.
    + right. apply even_n_Sn. rewrite <- even_n_SSn.
      apply H.
    + left.  *)


Lemma negb_eq: forall a: bool,
  (negb a = true) -> a = false.
Proof.
  intros.
  destruct a.
  - simpl in H. symmetry in H. apply H.
  - reflexivity. 
Qed.

(* Theorem mdi_example: ∀n: nat, 
  even(n) = true -> even(7*n) = true.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - rewrite even_n_SSn in H. rewrite even_n_SSn in H.
    rewrite even_n_SSn in H.
    simpl (7*S n). rewrite plus_n_Sm.
Qed. *)
