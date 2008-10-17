Section ocase.
  Variables A B : Type.

  Variable disc : option A.

  Variable NoneCase : disc = None -> B.
  Variable SomeCase : forall v, disc = Some v -> B.

  Definition ocase :=
    match disc as disc' return (disc = disc' -> B) with
      | None => NoneCase
      | Some v => SomeCase _
    end (refl_equal _).
End ocase.

Implicit Arguments ocase [A B].

Notation "'IfNull' x 'Then' e1 'Else' e2" :=
  (ocase x (fun _ => e1) (fun x _ => e2))
  (no associativity, at level 70).
Notation "'IfNull' e 'As' x 'Then' e1 'Else' e2" :=
  (ocase e (fun _ => e1) (fun x _ => e2))
  (no associativity, at level 70).
