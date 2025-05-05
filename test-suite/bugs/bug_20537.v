Module M.
  Tactic Notation (at level 5) "foo" int(x) := do x apply S; exact 0.
End M.

Import M.
(* Anomaly
"Uncaught exception Failure("Grammar.extend: No level labelled \"5\" in entry \"ltac_expr\"")."
 *)

Check eq_refl : ltac:(foo 4) = 4.
