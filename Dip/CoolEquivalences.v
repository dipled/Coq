Definition Pierce := forall A B : Prop, ((A -> B) -> A) -> A.

Definition DNe := forall A : Prop, ~~A -> A.

Definition LEM := forall A : Prop, A \/ ~A.

Theorem pierce_lem_eq: Pierce <-> LEM.
Proof.
  unfold Pierce, LEM. split.
  - intro pierce. intro A.
    apply pierce with (B := False). intro. 
    right. intro. apply H. left. apply H0.  
  - intro lem. intros A B. intro H.
    specialize lem with (A := A).
    destruct lem.
    + apply H0.
    + apply H. intro H1. apply H0 in H1 as contra.
      destruct contra.
Qed.

Theorem pierce_dne_eq: Pierce <-> DNe.
Proof.
  unfold Pierce, DNe. split.
  - intro pierce. intro A. intro H. apply pierce with (B := False).
    intro H0. apply H in H0 as contra. destruct contra.
  - intro dne. intros A B. intro H. apply dne. intro. apply H0.
    apply H. intro. apply H0 in H1 as contra. destruct contra.
Qed.

Theorem lem_dne_qq: DNe <-> LEM.
Proof.
  unfold DNe, LEM. split.
  - intro dne. intro A. apply dne. intro.
    apply H. left. apply dne. intro. apply H.
    right. intro. apply H0 in H1 as contra. destruct contra. 
  - intro lem. intro A. intro H. specialize lem with (A := A).
    destruct lem. 
    { apply H0. } 
    { apply H in H0 as contra. destruct contra. }
Qed.
    

