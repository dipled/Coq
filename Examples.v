Require Import Coq.Arith.PeanoNat.
Require Import Arith.
From Coq Require Export String.
Theorem mult_n_zero: forall n: nat, n * 0 = 0.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem ponens: forall A B : Prop,
  ((A -> B) /\ A) -> B.
Proof.
  intros.
  destruct H.
  apply H in H0.
  assumption.
Qed.
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros. destruct H as (A & B). assumption.
Qed.
Lemma tol: forall A B: Prop,
  ((A -> B) /\ ~B) -> ~A.
Proof.
  intros. destruct H as [H1 H2]. unfold not.
  intro. apply H1 in H. contradiction.
Qed.

Lemma dem1: forall A B: Prop,
  ~A \/ ~B -> ~(A /\ B).
Proof.
  intros.
  unfold not.
  intro.
  destruct H0.
  destruct H. - contradiction. - contradiction.
Qed.
  
Lemma dem2: forall A B: Prop,
  ~(A \/ B) -> ~A /\ ~B.
Proof.
  intros.
  split. 
  intro. apply H. left. assumption. 
  intro. apply H. right. assumption.
Qed.

Lemma dem3: forall A B: Prop,
  ~A /\ ~B -> ~(A \/ B).
Proof.
  intros.
  destruct H.
  intro. destruct H1 as [H2 | H3].
  - contradiction.
  - contradiction.
Qed.
   
Example Lista2K: forall A B  : Prop, (A \/ B) /\ ~A -> B .
Proof.
  intros.
  destruct H. destruct H. contradiction. assumption.
Qed.

Example Teste: forall A B C : Prop, (A \/ B) -> (~A -> (B \/ C)).
Proof.
  intros.
  left.
  destruct H. contradiction. assumption.
Qed.
