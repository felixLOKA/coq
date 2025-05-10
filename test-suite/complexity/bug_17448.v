(* Expected time < 1.00s *)
Require Import Extraction.

Definition test (f : nat -> nat) (n : nat) : bool.
Proof.
refine (let n := _ in match n with 0 => true | S n => false end).
do 40 refine (let n := _ in f n).
exact n.
Defined.

Time Recursive Extraction test.
