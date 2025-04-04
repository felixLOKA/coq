(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ind_tables

(** Induction/recursion schemes *)

val elim_scheme : dep:bool -> to_kind:Sorts.family -> individual scheme_kind

val mutual_rect_dep : mutual scheme_kind
val mutual_rec_dep : mutual scheme_kind
val mutual_ind_dep : mutual scheme_kind
val mutual_sind_dep : mutual scheme_kind
val mutual_rect_nodep : mutual scheme_kind
val mutual_rec_nodep : mutual scheme_kind
val mutual_ind_nodep : mutual scheme_kind
val mutual_sind_nodep : mutual scheme_kind

(** Case analysis schemes *)

val case_dep : individual scheme_kind
val case_nodep : individual scheme_kind
val casep_dep : individual scheme_kind
val casep_nodep : individual scheme_kind
    
(* val mutual_case_dep : mutual scheme_kind *)
(* val mutual_casep_dep : mutual scheme_kind *)
(* val mutual_cases_dep : mutual scheme_kind *)
(* val mutual_casep_dep_set : mutual scheme_kind *)
(* val mutual_case_nodep : mutual scheme_kind *)
(* val mutual_casep_nodep : mutual scheme_kind *)
(* val mutual_cases_nodep : mutual scheme_kind *)
(* val mutual_case_nodep_set : mutual scheme_kind *)
    
val cases_dep : individual scheme_kind
val cases_nodep : individual scheme_kind
val casep_dep_set : individual scheme_kind
val case_nodep_set : individual scheme_kind
