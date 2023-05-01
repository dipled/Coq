Require Import Coq.Unicode.Utf8.
From LF Require Import Induction.

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

Fixpoint length (l : natlist) : nat :=
  match l with
  |[] => O
  |(h::t) => S (length t)
  end.

Fixpoint append (l1 l2 : natlist) : natlist :=
  match l1 with
  |[] => l2
  |(h::t) => h :: (append t l2)
  end.

Notation " x ++ y " := (append x y)
  (right associativity, at level 60).


Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  |[] => []
  |(h::t) => if(eqNat h O) then nonzeros t
             else h :: (nonzeros t)
  end.
Compute nonzeros [1;2;3;4;5;0;0;0;7].
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  |[] => []
  |(h::t) => if(odd h) then h :: (oddmembers t)
             else oddmembers t
  end.
Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1,l2 with
  |[], _ => l2
  |_, [] => l1
  |(h1::t1), (h2::t2) => h1 :: h2 :: (alternate t1 t2)
  end.
(*Bags sao sets com repeticao*)
Definition bag := natlist.
(*Definindo algumas funcoes para os bags*)

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  |[] => O
  |(h::t) => if (eqNat v h) then S (count v t)
             else (count v t)
  end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
  reflexivity.
Qed.
Definition sum : bag -> bag -> bag :=
  append.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
  reflexivity.
Qed.
Definition add (v : nat) (s : bag) : bag :=
  sum s [v].
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof.
  reflexivity.
Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof.
  reflexivity.
Qed.

Definition member (v : nat) (s : bag) : bool :=
  if (eqNat (count v s) O) then false
  else true.
Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  |[] => []
  |(h::t) => if (eqNat v h) then t
             else h :: (remove_one v t)
  end.
Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  |[] => []
  |(h::t) => if (eqNat v h) then remove_all v t
             else h :: (remove_one v t)
  end.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1,s2 with
  |_,[] => false
  |[], _ => true
  |(h1::t1),(h2::t2) => if(eqNat(count h1 s2) 0) then false
                        else included t1 (remove_one h1 s2)
  end.
 Example test_included1: included [1;2] [2;1;4;1] = true.
Proof.
  simpl. reflexivity.
Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof.
  reflexivity.
Qed.
