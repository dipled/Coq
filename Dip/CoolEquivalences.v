Definition Pierce := forall A B : Prop, ((A -> B) -> A) -> A.

Definition DNe := forall A : Prop, ~~A -> A.

Definition LEM := forall A : Prop, A \/ ~A.

Definition IP := forall A : Prop, (~A -> False) -> A.

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

Theorem pierce_ip_eq: Pierce <-> IP.
Proof.
  unfold Pierce, IP. split.
  - intro pierce. intro A. intro H.
    apply pierce with (B := False). intro. unfold not in H.
    apply H in H0 as contra. destruct contra.
  - intro IP. intros A B. intro H.
    apply IP. intro. apply H0. apply H. intro. apply H0 in H1 as contra.
    destruct contra.
Qed.
    
Theorem lem_ip_eq: LEM <-> IP.
Proof.
  unfold LEM, IP. split.
  {
    intros lem. intro A. intro H. specialize lem with (A := A) as lem_spec.
    destruct lem_spec.
    - apply H0.
    - apply H in H0 as contra. destruct contra.
  }
  {
    intro ip. intro A. apply ip. intro. apply H. left. apply ip. intro. apply H.
    right. apply H0.
  }
Qed.

Theorem dne_ip_eq: DNe <-> IP.
Proof.
  unfold DNe, IP. split.
  - intro dne. intro A. intro H.
    apply dne. intro H0. apply H. apply H0.
  - intro ip. intro A. intro H.
    apply ip. intro H0. apply H. apply H0.
Qed.

