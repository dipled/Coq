Require Import Coq.Arith.PeanoNat.
Require Import Arith.
From Coq Require Export String.]
Inductive bool :Type :=
  |true
  |false.
Notation "⊥" := false.
Notation "⊤" := true.
Definition and (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  |⊤, ⊤ => ⊤
  |_, _ => ⊥
  end.
Notation "p ∧ q" := (and p q) (at level 40, left associativity).
Definition notb (b:bool) : bool :=
  match b with
  |false => true
  |true => false
  end.
Definition or (b1:bool) (b2:bool) : bool :=
  match b1 with
  |false => b2
  |true => true
  end.
Infix "∨" := or (at level 20, left associativity).
Notation "¬" := notb (at level 10).

Theorem dem_1: forall a b: bool, (notb (a ∨ b)) = (¬a ∧ ¬b).
Proof.
intros [] [].
-simpl. reflexivity.
-simpl. reflexivity.
-simpl. reflexivity.
-simpl. reflexivity.
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
