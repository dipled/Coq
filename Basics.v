Require Import Coq.Arith.PeanoNat.
Require Import Arith.
From Coq Require Export String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b: bool) : bool := 
  match b with
  |false => true
  |true => false
  end.

Definition orb (a: bool) (b: bool) : bool := 
  match a with
  |true => true
  |false => b
  end.

Definition andb (a: bool) (b: bool) : bool :=
  match a with
  |true => b
  |false => false
  end.

Definition nandb (a : bool) (b : bool) : bool :=
  match a with
  |false => negb b
  |true => false
  end.
  Compute negb(nandb(orb true false) false).
(*
Example test_nandb1: (nandb true true) = false.
Proof.
  simpl.
  reflexivity.
Qed. 

Example test_nandb2: (nandb false false) = true.
Proof.
  simpl.
  reflexivity.
Qed.
(*Temos expressoes condicionais!!!!!*)
Definition andb' (a : bool) (b : bool) : bool :=
  if a then b
  else false.
Compute andb' true true.

(*O coq permite voce fazer notacoes proprias 
como as definidas abaixo*)
Notation "a && b" := (andb a b).
Notation "a || b" := (orb a b).
(*Modulos sao usados para separar funcoes com mesmo nome*)
Module Pedro.
  Definition exemplo1 : bool := true.
End Pedro.
Definition exemplo1 : nat := S 0.

Check exemplo1.
Check Pedro.exemplo1.

(*Tuplas podem ser criadas baseadas em tipos existentes*)
Inductive bit : Type :=
  |B0
  |B1.
Inductive nybble : Type :=
  |bits (b0 b1 b2 b3 : bit).

Definition allzeros (n :nybble) : bool :=
  match n with
  |(bits B0 B0 B0 B0) => true
  |(bits _ _ _ _) => false
  end.
Compute allzeros (bits B0 B0 B0 B0).
*)
(*Botando essas definicoes no modulo para nao interferir
com a biblioteca padrao*)
Module Naturais.

  Inductive nat : Type := 
  |O
  |S (n : nat).

End Naturais.



Fixpoint sum' (n : nat) : nat :=
  match n with
  |O => O
  |S n' =>  sum' n' + n
  end.


Fixpoint div2 (n : nat) : nat :=
    match n with
    |O => O
    |S O => O
    |S (S x) => 1 + (div2 x)
    end.
Fixpoint leb' (a: nat) (b: nat) : bool := 
  match a,b with 
  |O, O => true
  |O, _ => false
  |S a', O => true
  |(S a'), (S b') => leb' a' b'
  end.
Fixpoint subt (n:nat) (m:nat) : nat :=
  match m with
  |O => n  
  |S m' => match n with 
           |O => n
           |S n' => subt n' m'
           end
  end.

Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    |O => m 
    |S n' => S (plus n' m)
    end.


Fixpoint mult (n : nat) (m : nat) : nat := 
  match n with
  |O => O
  |S n' => plus m (mult n' m)
  end.


Theorem plus_0_n : forall n: nat, O + n = n.
Proof.
    intros n.
    simpl. 
    reflexivity.
Qed.


Fixpoint fatorial (n : nat) : nat := 
  match n with
  |O => S O
  |S O => S O
  |S n' => mult (S n') (fatorial n')
  end.
Compute fatorial 5.
