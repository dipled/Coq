Theorem dem1: forall (A B: Prop),
    (~A \/ ~B) -> ~(A /\ B).
Proof.
    intros. intro.
    (*Split /\ and \/*)
    destruct H0. destruct H. 
    (*Case 1: A Holds*)
    - apply H in H0; destruct H0.
    (*Case 2: B Holds*) 
    - apply H in H1; destruct H1.
Qed.

Theorem dem2: forall (A B: Prop),
    ~(A \/ B) <-> (~A /\ ~B).
Proof.
    intros. split.
    - intro. split.
      * intro. destruct H.
        left. apply H0.
      * intro. destruct H.
        right. apply H0.
    - intro. destruct H. intro. destruct H1.
      * apply H in H1; destruct H1.
      * apply H0 in H1; destruct H1.
Qed.
      