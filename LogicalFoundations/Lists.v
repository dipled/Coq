Require Import Coq.Unicode.Utf8.
Inductive natprod : Type :=
  |pair (n1 n2 :nat).

Definition fst (p : natprod) : nat :=
  match p with
  |pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  |pair x y => y
  end.

Notation "( x , y )" := (pair x y).
Definition swap_pair (p : natprod) : natprod :=
  match p with
  |(x,y) => (y,x)
  end.
(*Simple facts about pairs*)
Theorem surjective_pairing:forall a b,
  (a,b) = (fst(a,b),snd(a,b)).
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem surjective_pairing': forall p,
  p = (fst p, snd p).
Proof.
  intros. destruct p. simpl.
  reflexivity.
Qed.
Theorem snd_fst_is_swap : ∀ (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  destruct p. simpl. reflexivity.
Qed.

(*Lists*)

Inductive natlist : Type :=
  |nil
  |cons (n:nat) (l:natlist).


Notation "x :: l" := (cons x l)
(at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  |S count' => n :: (repeat n count')
  |O => []
  end.
Compute repeat 3 9.