Require Import PrimInt63.

Open Scope uint63_scope.

Primitive array := #array_type.

Primitive make : forall A, int -> A -> array A := #array_make.
Arguments make {_} _ _.

Primitive get : forall A, array A -> int -> A := #array_get.
Arguments get {_} _ _.

Primitive set : forall A, array A -> int -> A -> array A := #array_set.
Arguments set {_} _ _ _.

Module Inconsistent.

  Inductive CMP (x:array (unit -> nat)) := C.

  Definition F (x:nat) := fun _:unit => x.

  Polymorphic Definition TARGET@{u} := let m := [| F 0; F 0 | F 0 |] in
                       let m := set m 0 (fun _ => get (set m 1 (F 1)) 0 tt) in
                       CMP m.

  Polymorphic Cumulative Inductive foo@{u} : Type@{u} := CC (_ : TARGET@{u} = TARGET@{u}).
End Inconsistent.
