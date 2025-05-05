Set Definitional UIP.

Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.
Arguments srefl {_ _}.

Module WithProp.

(* Axiom implied by propext (so consistent) *)
Axiom all_eq : forall (P Q:Prop), P -> Q -> seq P Q.

Definition transport (P Q:Prop) (x:P) (y:Q) : Q
  := match all_eq P Q x y with srefl => x end.

Definition top : Prop := forall P : Prop, P -> P.

Definition c : top :=
  fun P p =>
    transport
      (top -> top)
      P
      (fun x : top => x (top -> top) (fun x => x) x)
      p.

(* Fail Timeout 1 Eval lazy in c (top -> top) (fun x => x) c. *)
(* loops *)

End WithProp.

Module WithoutProp.

(* Axiom implied by propext (so consistent) *)
Axiom all_eq : forall (P Q:SProp), P -> Q -> seq P Q.

(* go through Set because match from SProp to SProp doesn't have the
   special reduction *)
Record Box (A:SProp) : Set := box { unbox : A }.
Arguments box {_}. Arguments unbox {_}.

Definition transport (P Q:SProp) (x:P) (y:Q) : Q
  := unbox match all_eq P Q x y with srefl => box x end.

Definition top : SProp := forall P : SProp, P -> P.

Definition c : top :=
  fun P p =>
    transport
      (top -> top)
      P
      (fun x : top => x (top -> top) (fun x => x) x)
      p.

(* Fail Timeout 1 Eval lazy in c (top -> top) (fun x => x) c. *)
(* loops *)

End WithoutProp.
