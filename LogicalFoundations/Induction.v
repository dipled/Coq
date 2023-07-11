From Coq Require Export String.
From Coq Require Import Unicode.Utf8_core.
(* Teoremas do Induction.v e Basics.v*)

Lemma succ_def: ∀ a : nat,
  S a = (a + 1).
Proof.
  intros.
  induction a.
  - reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed. 

Lemma succ_def2: ∀ a : nat,
  S a = (1 + a).
Proof.
  intros.
  induction a.
  - reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed. 

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem sub_0_r : forall n:nat, n - 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. reflexivity.
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

Fixpoint mod2 (n: nat): nat :=
  match n with
  |O => O
  |S O => S O
  |S(S n') => mod2 n'
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

Fixpoint even (n:nat):bool :=
  match n with
  |O => true
  |S O => false
  |S (S n') => even n'
  end.

Definition odd (n: nat): bool :=  negb (even n).

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

Lemma false_equals_false:
  false = false.
Proof.
  reflexivity.
Qed.

Lemma bool_diff_eq_false: forall a: bool,
  (a <> false) -> (a = true).
Proof.
  intros. destruct a.
  - reflexivity.
  - pose proof false_equals_false as H'.
    apply H in H'.
    destruct H'. 
Qed.

Theorem even_n_SSn: forall n : nat,
  even(n) = even(S (S n)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma negb_eq: forall a: bool,
  (negb a = true) -> a = false.
Proof.
  intros.
  destruct a.
  - simpl in H. symmetry in H. apply H.
  - reflexivity. 
Qed.
Theorem bool_dne: ∀ a: bool,
  a = negb(negb a).
Proof.
  destruct a; reflexivity.
Qed.


Lemma bool_diff_eq_true: ∀ a: bool,
  a <> true <-> a = false.
Proof.
  intros.
  split.
  - intro. destruct a.
    + destruct H. reflexivity.
    + reflexivity.
  - intro. destruct a.
    + discriminate H.
    + intro. discriminate H0.
Qed.



Theorem even_n_odd: ∀ n: nat,
  even n = negb(odd n).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - change(odd(S n)) with (negb(even(S n))).
    rewrite <- bool_dne. reflexivity.
Qed.

Theorem even_n_lem: ∀ n: nat,
  (orb (even n) (negb (even n))) = true.
Proof.
  intros. destruct (even n).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem orb_prop_eq: ∀  α β a: bool,
((orb α β) = a) -> (α = a) \/ (β = a).
Proof.
  intros.
  destruct a.
  - destruct α; destruct β; simpl in H.
     * left; reflexivity.
     * left; reflexivity.
     * right; reflexivity.
     * right; apply H.
  - destruct α; destruct β.
     * simpl in H. left; apply H.
     * simpl in H. left; apply H.
     * simpl in H. right; apply H.
     * simpl in H. right; reflexivity.
Qed.
Theorem bool_neg_both_sides: ∀ a b: bool,
  (a = b) <-> ((negb a) = (negb b)).
Proof.
  destruct a; destruct b; split; intro.
  - simpl. reflexivity.
  - reflexivity.
  - simpl. symmetry; apply H.
  - simpl in H. symmetry in H. apply H.
  - simpl; symmetry in H; apply H.
  - simpl in H; symmetry in H; apply H.
  - reflexivity.
  - reflexivity.
Qed.

Theorem even_n_Sn: ∀ n: nat,
  (even n) = (negb (even (S n))).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - rewrite <- even_n_SSn. symmetry. apply bool_neg_both_sides in IHn.
    rewrite <- bool_dne in IHn. apply IHn.
Qed.

Theorem even_n_Sn_Prop: ∀ n: nat,
  (even n = true) <-> (even (S n) = false).
Proof.
  intros. split.
  - intro.
    rewrite bool_neg_both_sides in H.
    rewrite even_n_Sn in H. 
    rewrite <- bool_dne in H.
    simpl (negb true) in H.
    apply H.
  - intro.
    rewrite bool_neg_both_sides in H.
    rewrite even_n_Sn in H. 
    rewrite <- bool_dne in H.
    rewrite even_n_SSn. simpl (negb false) in H.
    apply H.
Qed.

Theorem iff_neg: ∀ A B: Prop,
  (A <-> B) -> (~A <-> ~B).
Proof.
  intros. destruct H.
  split.
  - intro.  intro. apply H0 in H2. apply H1 in H2. destruct H2.
  - intro. intro. apply H in H2. apply H1 in H2. destruct H2.
Qed.



Lemma even_n_diff_true_even_Sn: ∀ n: nat,
  even n <> true <-> even (S n) = true. 
Proof.
  intros. split.
  - intro. apply bool_diff_eq_true in H.
    rewrite even_n_Sn in H. apply bool_neg_both_sides in H.
    rewrite <- bool_dne in H. simpl(negb false) in H.
    apply H.
  - intro. rewrite bool_diff_eq_true. rewrite even_n_Sn in H.
    rewrite <- even_n_SSn in H. apply bool_neg_both_sides in H.
    rewrite <- bool_dne in H. simpl (negb true) in H. apply H.
Qed. 


Lemma add_one_to_both_sides: ∀ a b : nat,
  (a=b) -> (a+1 = b+1).
Proof.
  intros.
  induction a; induction b.
    + reflexivity.
    + rewrite H. reflexivity.
    + rewrite H. reflexivity.
    + rewrite H. reflexivity.
Qed.

Theorem nat_2m: ∀ n : nat,
 ((∃ m : nat, n = 2*m) \/ (∃ m : nat, n = 2*m+1)).
Proof.
  intros.
  induction n.
  - left. exists 0. reflexivity.
  - destruct IHn. 
    + right. destruct H. exists x. apply add_one_to_both_sides in H.
      rewrite plus_n_1 in H. apply H.
    + left. destruct H. exists (x+1). apply add_one_to_both_sides in H.
      rewrite plus_n_1 in H. rewrite mult_dist.
      rewrite <- add_assoc in H. simpl(1+1) in H. apply H.
Qed.



Theorem not_n_2m_then_n_2mplus1: ∀ n: nat,
  ¬(∃ m : nat, n = 2*m) -> (∃ m : nat, n = 2*m + 1).
Proof.
  intros. induction n as [| k].
  - destruct H. exists 0. reflexivity.
  - pose proof nat_2m as X. destruct X with (S k).
    + apply H in H0. destruct H0.
    + apply H0.
Qed.  


Lemma sub_one_both_sides: ∀ a b: nat,
  (a = b -> (a-1 = b-1)).
Proof.
  intros.
  induction a; induction b.
  - simpl. reflexivity.
  - rewrite H. simpl. reflexivity.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
Qed. 

Lemma div2_both_sides: ∀ a b : nat,
  (a = b) -> ((div2 a) = (div2 b)).
Proof.
  intros.
  induction a; induction b.
  - reflexivity.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
Qed.

Lemma add_sub_assoc: ∀ n : nat,
  n + 1 - 1 = n + (1 - 1).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.  rewrite plus_n_Sm. change (S(n+0)-0) with (S(n+0)).
    reflexivity.
Qed.

Lemma one_2_x: ∀ x: nat,
   ~(1 = 2*x).
Proof.
  intros. intro. pose proof H as H'.
  apply div2_both_sides in H.
  rewrite <- mul2_div2 in H. simpl in H.
  symmetry in H.
  rewrite H in H'. simpl in H'. discriminate H'.
Qed.
 
Lemma mult_dist_sub: ∀ n : nat,
  2*(n - 1) = 2*n - 2.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite add_0_r. rewrite <- plus_n_Sm.
    rewrite add_assoc. rewrite sub_0_r. rewrite add_sub_assoc. simpl(1-1).
    rewrite add_0_r. reflexivity.
Qed.

Lemma minus_two_minus1_minus1: ∀ n : nat,
  n - 2 = n - 1 - 1.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite sub_0_r. reflexivity.
Qed.

Theorem n_2m_then_Sn_2m: ∀ n: nat,
(∃ m : nat, S n = 2*m) -> ~(∃ m : nat, n = 2*m).
Proof.
  intros. induction n.
  - destruct H. pose proof one_2_x as H'. intro.
    destruct H' with x. apply H.
  - intro. apply IHn in H0.
    destruct H0.
    destruct H.
    exists (x-1). rewrite mult_dist_sub.
    apply sub_one_both_sides in H.
    apply sub_one_both_sides in H.
    simpl in H. rewrite sub_0_r in H.
    rewrite add_0_r in H.
    simpl. rewrite add_0_r. rewrite minus_two_minus1_minus1. apply H.
Qed.

Lemma muda_nada:  ∀ a b c : nat,
  (a = b) -> (a-c = b-c).
Proof.
  intros.
  induction a; induction b.
  - reflexivity.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
Qed.

Theorem n_diff_Sn: ∀ n : nat,
  n <> S n.
Proof.
  intro.
  induction n.
  - intro. discriminate H.
  - intro. apply sub_one_both_sides in H.
    simpl in H. rewrite sub_0_r in H. apply IHn in H.
    destruct H.
Qed.

Theorem not_and_2m_2mplus1: ∀ n : nat,
  (∃ m : nat, n = 2*m + 1) -> ~(∃ m : nat, n = 2*m).
Proof.
  intros.
  intro.
  destruct H. destruct H0.
  pose proof H0 as H1.
  rewrite H in H0.
  apply div2_both_sides in H0.
  rewrite <- mul2_div2 in H0.
  rewrite <- div2_mult2_plus in H0.
  simpl (div2 1) in H0.
  rewrite add_0_r in H0.
  rewrite H0 in H.
  symmetry in H1.
  rewrite H1 in H. rewrite <- succ_def in H.
  apply n_diff_Sn in H. destruct H.
Qed.



Theorem even_classic_def: ∀ n: nat, 
  (even n = true) <-> (∃ m: nat, n = 2*m).
Proof.
  intros.
  induction n as [|k].
    + split.
      - intro. exists 0. reflexivity.
      - intro. reflexivity.
    + apply iff_neg in IHk as H'. split.
      - intro. rewrite even_n_diff_true_even_Sn in H'. apply H' in H as H''.
        apply not_n_2m_then_n_2mplus1 in H''. 
        destruct H''. apply add_one_to_both_sides in H0.
        rewrite plus_n_1 in H0. rewrite <- add_assoc in H0.
        exists (x+1). rewrite mult_dist. simpl(1+1) in H0.
        apply H0.
      - intro. destruct H'.
        pose proof nat_2m as H2.
        destruct H2 with k.
        * apply  n_2m_then_Sn_2m in H. apply H in H3. destruct H3.
        * apply  not_and_2m_2mplus1 in H3. apply H1 in H3.
          rewrite even_n_Sn in H3. rewrite bool_neg_both_sides in H3.
          rewrite <- bool_dne in H3. simpl (negb true) in H3.
          apply bool_diff_eq_false in H3. apply H3.
Qed.


Theorem odd_classic_def: ∀ n: nat, 
  (odd n = true) <-> (∃ m: nat, n = 2*m + 1).
Proof.
  intros. induction n.
  - split.
    + intro. rewrite bool_neg_both_sides in H. rewrite <- even_n_odd in H.
      simpl in H. discriminate H.
    + intro. apply not_and_2m_2mplus1 in H. destruct H.
      exists 0; reflexivity.
  -
    rewrite bool_neg_both_sides.
    rewrite <- even_n_odd.
    simpl(negb true).
    destruct IHn.
    split.
    + intro. pose proof even_classic_def as H2.
      destruct H2 with (S n).
      apply contras in H4.
      * apply not_n_2m_then_n_2mplus1 in H4.
        apply H4.
      * intro. rewrite H5 in H1. discriminate H1.
    + intro. rewrite bool_neg_both_sides. rewrite <- even_n_Sn.
      simpl (negb false). pose proof nat_2m as H2.
      * destruct H2 with n.
        ** apply even_classic_def in H3.
           apply H3.
        ** apply H0 in H3. apply H in H3. destruct H3. destruct H1.
           pose proof H1 as H1'.
           rewrite succ_def in H1'.
           apply sub_one_both_sides in H1'.
           rewrite add_sub_assoc in H1'.
           simpl (1-1) in H1'. rewrite add_0_r in H1'.
           pose proof H3 as H3'.
           rewrite H1' in H3'.
           rewrite add_sub_assoc in H3'.
           simpl(1-1) in H3'. rewrite add_0_r in H3'.
           apply div2_both_sides in H3'.
           rewrite <- mul2_div2 in H3'. rewrite <- div2_mult2_plus in H3'.
           simpl in H3'. rewrite add_0_r in H3'.
           symmetry in H3. rewrite H3' in H1. rewrite H3 in H1.
           pose proof n_diff_Sn as HMatadora.
           destruct HMatadora with n. symmetry. apply H1.
 Qed.