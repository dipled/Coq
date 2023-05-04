Require Import Coq.Unicode.Utf8.
Require Import Arith.
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
  append s [v].
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
  simpl. reflexivity.
Qed.

(*Logica com listas*)
Definition tail (l:natlist) : natlist :=
  match l with
  |[] => []
  |(h::t) => t
  end.
	
Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tail l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. 
Qed.
(*Inducao com listas: Seja l uma lista,
1) Mostrar que vale para [].
2) Supor que vale para uma l' e mostrar que vale para uma (cons n l').*)
Theorem app_assoc : ∀ l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros.
  induction l1 as [| n l1' IHl1'].
  -(*l1 is nil*)
    simpl. reflexivity.
  -(*l1 is cons n l1'*)
    simpl. rewrite IHl1'. reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  |[] => []
  |(h::t) =>  (rev t) ++ [h]
  end.
Lemma app_length: forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros. induction l1.
  * simpl. reflexivity.
  * simpl. rewrite <- IHl1. reflexivity.
Qed.
Lemma add_length: forall l : natlist, forall n : nat,
  length(add n l) = S(length(l)).
Proof.
  intros. induction l.
  + simpl. reflexivity.
  + simpl. rewrite app_length.
    simpl. rewrite plus_n_1. reflexivity.
Qed.

Theorem rev_length : ∀ l : natlist,
  length (rev l) = length l.
Proof.
  intros. induction l.
  + reflexivity.
  + simpl. rewrite app_length.
    simpl. rewrite IHl. rewrite plus_n_1. reflexivity.
Qed.
(*Podemos pesquisar por teoremas sobre funcoes que esquecemos o nome utilizando Search
Search rev.
Search (_ + _ = _ + _).
*)
Lemma app_nil_r : ∀ l : natlist,
  l ++ [] = l.
Proof.
  intros. induction l.
  -reflexivity.
  -simpl. rewrite IHl. reflexivity.
Qed. 

Lemma rev_app_distr: ∀ l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  -simpl. rewrite app_nil_r. reflexivity.
  -simpl. rewrite -> IHl1.
   rewrite app_assoc. reflexivity.
Qed.
Theorem rev_involutive : ∀ l : natlist,
  rev (rev l) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr.
    rewrite IHl. simpl. reflexivity.
Qed.

Theorem app_assoc4 : ∀ l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros. rewrite app_assoc. rewrite app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : ∀ l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
 intros. induction l1.
 - reflexivity.
 - destruct n.
   +simpl. rewrite IHl1. reflexivity.
   +simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1,l2 with
  |[],[] => true
  |_,[] => false
  |[],_ => false
  |(h1::t1),(h2::t2) => if(eqNat h1 h2) 
                        then (eqblist t1 t2)
                        else false
  end.
Lemma eqNat_refl: forall n : nat,
  true = eqNat n n.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
Theorem eqblist_refl : ∀ l:natlist,
  true = eqblist l l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite <- eqNat_refl.
    rewrite IHl. reflexivity.
Qed.

Theorem count_member_nonzero : ∀ (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros. reflexivity.
Qed.

Theorem leb_n_Sn : ∀ n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_does_not_increase_count: ∀ (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros. induction s.
  - simpl. reflexivity.
  - induction n.
    + simpl. rewrite leb_n_Sn. reflexivity.
    + simpl. rewrite IHs. reflexivity.
Qed.

Theorem involution_injective : ∀ (f : nat → nat),
  (∀ n : nat, n = f (f n)) -> (∀ n1 n2 : nat, f n1 = f n2 ->n1 = n2).
Proof.
  intros. rewrite H.
  rewrite <- H0.
  rewrite <- H.
  reflexivity.
Qed.

Theorem rev_injective : ∀ (l1 l2 : natlist),
  rev l1 = rev l2 → l1 = l2.
Proof.
  intros. rewrite <- rev_involutive. 
  rewrite <- H. rewrite rev_involutive.
  reflexivity.
Qed.
(*Vamos supor que queremos escrever uma funcao que retorna o n-esimo elemento de uma lista. Caso a lista não tenha um elemento, teriamos que retornar um valor natural para servir de erro, mas isso nao eh uma solucao otima.
  Podemos, entao, criar um novo tipo, que ira funcionar como um tipo Maybe em Haskell*)
Inductive natoption : Type :=
  |Some (c : nat)
  |None.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l, n with
  |[], _ => None
  |(h::t), O => Some h
  |(h::t), S n' => nth_error t n'
  end.
Compute nth_error [1;2;3;4;5;6;7;8;100;5] 100.

Definition head (l : natlist) : natoption :=
  match l with
  |[] => None
  |(h::t) => Some h
  end.

