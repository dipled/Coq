From Coq Require Export String.


Inductive HTProp : Type :=
    |T
    |F
    |NF.


Definition notht (p : HTProp) : HTProp :=
    match p with
    |T => F
    |F => T
    |NF => F
    end.


Definition andht (p q : HTProp) : HTProp :=
    match p, q with
    |F,_ => F
    |_, F => F
    |T, T => T
    |_, _ => NF
    end.


Definition orht (p q : HTProp) : HTProp :=
    match p, q with
    |T, _ => T
    |_, T => T
    |NF, _ => NF
    |_, NF => NF
    |_, _ => F
    end.



Definition impht (p q : HTProp) : HTProp :=
    match p, q with
    |F,_ => T
    |_, T => T
    |NF, F => F
    |NF, _ => T
    |T, F => F
    |T, NF => NF
    end.

Theorem HT_axiom_holds: forall a b : HTProp,
    orht (orht a (notht b)) (impht a b) = T.
Proof.
    intros a b.
    destruct a; destruct b; reflexivity.
Qed.

