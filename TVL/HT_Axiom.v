From Coq Require Export String.

Axiom HereAndThere : forall A B : Prop,
    A \/ (~B) \/ (A -> B).


