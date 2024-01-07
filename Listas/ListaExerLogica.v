Require Export Coq.Lists.List.
Import ListNotations.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P. intro H. intro H0. destruct H0 as [a H1]. apply H1 in H as contra. apply contra.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intro. destruct H as [a H1]. destruct H1 as [Pa | Qa].
    + left. exists a. apply Pa.
    + right. exists a. apply Qa.
  - intro. destruct H.
    + destruct H. exists x. left. apply H.
    + destruct H. exists x. right. apply H.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros. split.
   - destruct H. exists x. destruct H. apply H.
   - destruct H. destruct H. exists x. apply H0.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros. induction l.
  - simpl in H. exfalso. apply H.
  - simpl. simpl in H. destruct H.
    + left. f_equal. apply H.
    + right. apply IHl. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros. split.
  - intro. induction l.
    + simpl in H. exfalso. apply H.
    + simpl in H. destruct H.
      * exists a. split.
        -- apply H.
        -- simpl. left. reflexivity.
      * apply IHl in H as H0. destruct H0. exists x.
        destruct H0. split.
        -- apply H0.
        -- simpl. right. apply H1.
   - intro. induction l.
     -- simpl in H. destruct H. destruct H. exfalso. apply H0.
     -- simpl. destruct H. destruct H. simpl in H0. destruct H0.
        --- left. rewrite H0. apply H.
        --- right. apply IHl. exists x. split. apply H. apply H0. 
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. generalize dependent l'.
  induction l.
  - intro. split.
    + intro. simpl in H. right. apply H.
    + intro. destruct H. simpl in H. exfalso. apply H.
      simpl. apply H.
  - intro. split.
    + intro. simpl in H. destruct H.
      * simpl. left. left. apply H.
      * apply IHl in H as H0. destruct H0.
        -- simpl. left. right. apply H0.
        -- right. apply H0.
    + intro. simpl in H. destruct H. destruct H.
      -- simpl. left. apply H.
      -- simpl. right. apply IHl. left. apply H.
      -- simpl. right. apply IHl. right. apply H.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros. intro. apply H. right. intro. apply H. left. apply H0.
Qed.

Theorem disj_impl : forall (P Q: Prop),
 (~P \/ Q) -> P -> Q.
Proof.
  intros. destruct H. apply H in H0. destruct H0. apply H.
Qed.


Theorem Peirce_double_negation: forall (P:Prop), (forall P Q: Prop,
  (((P->Q)->P)->P)) -> (~~ P -> P).
Proof.
  intros. apply H with (Q := False). intro. unfold not in H0.
  apply H0 in H1 as contra. exfalso. apply contra.
Qed.

Theorem double_negation_excluded_middle : forall (P:Prop),
  (forall (P : Prop), (~~ P -> P)) -> (P \/ ~P). 
Proof.
  intros. apply H. intro. apply H0. right. intro. apply H0. left. apply H1.
Qed.

Theorem lem_demorgan : (forall P : Prop, (P \/ ~P)) -> (forall Q R: Prop, (~(~R /\ ~ Q) -> R \/ Q)).
Proof.
  intros LEM Q R. intro. specialize LEM with (P := R) as I.
  specialize LEM with (P := Q) as J. destruct I. 
  - left. apply H0.
  - right. destruct J.
    -- apply H1.
    -- exfalso. apply H. split. apply H0. apply H1.
Qed.

Theorem demorgan_imp_or : (forall Q R: Prop, (~(~R /\ ~ Q) -> R \/ Q)) 
                         -> (forall P Q : Prop, (P -> Q) -> ~P \/ Q).
Proof.
  intros. apply H. intro. destruct H1.
  apply H1. intro. apply H2. apply H0. apply H3. Qed.

Lemma p_imp_p: forall P : Prop, P -> P.
Proof.
  intros. apply H.
Qed.

Theorem imp_or_pierce: (forall P Q : Prop, (P -> Q) -> ~P \/ Q) -> (forall P Q: Prop,
  (((P->Q)->P)->P)).
Proof.
  intros. specialize H with (P := P) (Q := P) as H2.
  apply H in H0 as H3. destruct H3.
  - pose proof p_imp_p as pimpp. apply H2 in pimpp as H3.
    destruct H3.
    -- apply H0. intro. apply H3 in H4. destruct H4.
    -- apply H3.
  - apply H1.
Qed.
