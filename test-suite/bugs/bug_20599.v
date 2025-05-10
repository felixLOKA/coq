Variant T : nat -> Set :=
| T1 : forall {n}, T (S n).

Definition TS {n : nat} (t : T n) : (T (S n)) := T1.

Declare Scope t_scope.

Number Notation T Nat.of_num_uint Nat.to_num_uint
    (via nat
        mapping [[T1] => O, [TS] => S]) : t_scope.

Open Scope t_scope.

Fail Definition test := 0. (** Error: Anomaly "Uncaught exception Option.IsNone." **)
