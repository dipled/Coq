Require Export Coq.Lists.List.
Import ListNotations.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Lemma eq_cons : forall (X:Type) (l1 l2: list X) (x: X),
  l1 = l2 -> x :: l1 = x :: l2.
  intros X l1 l2 x.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [|h l IH].
  - intros l1 l2 H. unfold split in H. injection H as H.
    rewrite <- H. reflexivity.
  - intros l1 l2 H. 
    induction l1 as [|h1 l1], l2 as [|h2 l2].
    + simpl in H. destruct (split l),h. injection H as H H1.
      discriminate H.

    + simpl in H. destruct (split l), h in H. injection H as H.
      discriminate H.

    + simpl in H. destruct (split l), h in H. injection H as H.
      discriminate H1.
    
    + simpl in H. destruct h. destruct (split l). injection H as H. 
      replace l with (combine l1 l2).
      rewrite H, H1.
        reflexivity.
      apply IH.
      rewrite H0, H2. reflexivity.
Qed.


Theorem split_combine : forall X Y (l1 : list X) (l2 : list Y) (l : list (X*Y)),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof.
  intros X Y l1 l2 l. generalize dependent l1.
  generalize dependent l2. induction l as [| h t IHl].
  - intros. destruct l1.
    + destruct l2.
      * reflexivity.
      * simpl in H. discriminate H.
    + destruct l2.
      * simpl in H. discriminate H.
      * simpl in H0. discriminate H0.
  - intros.
    destruct l1 eqn: El1; destruct l2 eqn: El2.
    + discriminate H0.
    + discriminate H0.
    + discriminate H0.
    + destruct h. simpl in H. injection H as H. injection H0 as H0. apply IHl in H.
      simpl. rewrite H. rewrite H0,H1. reflexivity. apply H2.
Qed. 
      
      