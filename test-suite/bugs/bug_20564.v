Require Import Ltac2.Ltac2.

Fail Ltac2 rec compile1 (cenv : constr list) : constr :=
  (*                ^^^^                               *)
  (* Error: This expression has type constr but an expression was expected of type
constr list *)
  x.

Fail Ltac2 compile2 (cenv : constr list) : constr :=
  x. (* Error: Unbound value x *)

Fail Ltac2 rec compile3 (cenv : constr) : constr :=
  x. (* Compiles "correctly" *)

Fail Ltac2 compile3 (cenv : constr) : constr :=
  x. (* Error: Unbound value x *)
