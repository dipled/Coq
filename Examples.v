Example Teste: forall A B C : Prop, (A \/ B) -> (~A -> (B \/ C)).
Proof.
  intros.
  destruct H.
  - apply H0 in H; destruct H.
  - left; apply H.
Qed.
