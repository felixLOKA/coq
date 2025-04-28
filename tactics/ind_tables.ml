(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* File created by Vincent Siles, Oct 2007, extended into a generic
   support for generation of inductive schemes by Hugo Herbelin, Nov 2009 *)

(* This file provides support for registering inductive scheme builders,
   declaring schemes and generating schemes on demand *)

open Names
open Nameops
open Declarations
open Constr
open Util


(**********************************************************************)
(* Registering schemes in the environment *)

type handle = Evd.side_effects

type mutual_scheme_object_function =
  Environ.env -> handle -> inductive list -> bool -> constr array Evd.in_ustate option (* None = silent error *)
type individual_scheme_object_function =
  Environ.env -> handle -> inductive -> bool -> constr Evd.in_ustate option (* None = silent error *)

(* scheme_name * sort * dep *)
type 'a scheme_kind = (string list * Sorts.family option * bool)

let pr_scheme_kind (kind : string list * Sorts.family option * bool) = 
  let (str_list, opt_str,b) = kind in
  let pr_list = Pp.prlist Pp.str str_list in
  let pr_option = match opt_str with
    | Some s -> Pp.str (" (" ^ (Sorts.family_to_str s) ^ ")")
    | None -> Pp.str " (None)"
  in
  Pp.(pr_list ++ pr_option)

(**********************************************************************)
(* The table of scheme building functions *)

type individual
type mutual


type scheme_dependency =
| SchemeMutualDep of Names.MutInd.t * mutual scheme_kind * bool (* true = internal *)
| SchemeIndividualDep of inductive * individual scheme_kind * bool (* true = internal *)

type scheme_object_function =
  | MutualSchemeFunction of mutual_scheme_object_function * (Environ.env -> Names.MutInd.t -> bool -> scheme_dependency list) option
  | IndividualSchemeFunction of individual_scheme_object_function * (Environ.env -> inductive -> bool -> scheme_dependency list) option

(* Stores only the schemes initialized at the launch of coqtop (or similar tools).
   User-defined inductive types and their associated schemes are not added to this table. *)
let scheme_object_table =
  (Hashtbl.create 17 :
     ((string list * Sorts.family option * bool), (one_inductive_body option -> string) * scheme_object_function)
  Hashtbl.t)

let key_str key =
  let (str_list, opt_str,b) = key in
  let str_list = String.concat " " str_list in
  let str_option = match opt_str with
    | Some s -> " (" ^ (Sorts.family_to_str s) ^ ")"
    | None -> " (None)"
  in
  str_list ^ str_option

    
(* let make_suff_fun f ind = *)
(*   let sort =  *)
(*      match ind.mind_arity with *)
(*      | RegularArity a -> a.mind_sort *)
(*      | TemplateArity b -> b.template_level *)
(*   in *)
  

  
(*   match sort with *)
  
(*   (match name with *)
(*      | None -> (key_str key) *)
(*      | Some id -> (Id.to_string id) ^ "_" ^ (key_str key)) *)

let declare_scheme_object key suff f =
  let () =
    if not (Id.is_valid ("ind_" ^ suff None)) then
      CErrors.user_err Pp.(str ("Illegal induction scheme suffix: " ^ suff None))
  in
  if Hashtbl.mem scheme_object_table key then
    CErrors.user_err
      Pp.(str "Scheme object " ++ str (key_str key) ++ str " already declared.")
  else begin
    Hashtbl.add scheme_object_table key (suff,f);
    key
  end

let declare_mutual_scheme_object key suff ?deps f =
  let (strl,sortf) = key in
  let key = (strl,sortf,true) in
  declare_scheme_object key suff (MutualSchemeFunction (f, deps))

let declare_individual_scheme_object key suff ?deps f =
  let (strl,sortf) = key in
  let key = (strl,sortf,false) in
  declare_scheme_object key suff (IndividualSchemeFunction (f, deps))

let is_declared_scheme_object key =
  (* let tmp = String.split_on_char '_' key in *)
  Hashtbl.mem scheme_object_table key

let scheme_kind_name (key : _ scheme_kind) : string list * Sorts.family option * bool = key

let scheme_key (key : string list * Sorts.family option * bool) : _ scheme_kind  = key

let get_suff sch_type sch_sort =
  try
    fst (
      match sch_sort with
      | Some st -> Hashtbl.find scheme_object_table (sch_type,sch_sort,true)
      | None -> Hashtbl.find scheme_object_table (sch_type,Some InType,true)
      )
  with Not_found ->
  (try
    fst (match sch_sort with
      | Some st -> Hashtbl.find scheme_object_table (sch_type,sch_sort,false)
      | None -> Hashtbl.find scheme_object_table (sch_type,Some InType,false)
       )
   with Not_found -> assert false) 
  
(**********************************************************************)
(* Defining/retrieving schemes *)

let is_visible_name id =
  try ignore (Nametab.locate (Libnames.qualid_of_ident id)); true
  with Not_found -> false

let compute_name internal id =
  if internal then
    Namegen.next_ident_away_from (add_prefix "internal_" id) is_visible_name
  else id

let declare_definition_scheme = ref (fun ~internal ~univs ~role ~name ?loc c ->
    CErrors.anomaly (Pp.str "scheme declaration not registered"))

let lookup_scheme kind ind =
  try Some (DeclareScheme.lookup_scheme kind ind) with Not_found -> None

let redeclare_schemes eff =
  let fold c role accu = match role with
  | Evd.Schema (ind, kind) ->
    try
      let _ = DeclareScheme.lookup_scheme kind ind in
      accu
    with Not_found ->
      let old = try Sorts.Map.find kind accu with Not_found -> [] in
      Sorts.Map.add kind ((ind, c) :: old) accu
  in
  let schemes = Cmap.fold fold eff.Evd.seff_roles Sorts.Map.empty in
  let iter kind defs = List.iter (DeclareScheme.declare_scheme SuperGlobal kind) defs in
  Sorts.Map.iter iter schemes

let local_lookup_scheme eff kind ind = match lookup_scheme kind ind with
| Some _ as ans -> ans
| None ->
  let exception Found of Constant.t in
  let iter c role = match role with
    | Evd.Schema (i, k) ->
      let tmp = if (Sorts.compareT k kind == 0) then true else false in
      if tmp && Ind.UserOrd.equal i ind then raise (Found c)
  in
  (* Inefficient O(n), but the number of locally declared schemes is small and
     this is very rarely called *)
  try let _ = Cmap.iter iter eff.Evd.seff_roles in None with Found c -> Some c

let local_check_scheme kind ind eff =
  Option.has_some (local_lookup_scheme eff kind ind)

let define ?loc internal role id c poly uctx =
  let id = compute_name internal id in
  let uctx = UState.collapse_above_prop_sort_variables ~to_prop:true uctx in
  let uctx = UState.minimize uctx in
  let c = UState.nf_universes uctx c in
  let uctx = UState.restrict uctx (Vars.universes_of_constr c) in
  let univs = UState.univ_entry ~poly uctx in
  (* ici on appelle vernac/declare.ml declare_definition_scheme *)
  !declare_definition_scheme ~internal ~univs ~role ~name:id ?loc c

  module Locmap : sig

    type t

    val default : Loc.t option -> t
    val make : ?default:Loc.t -> MutInd.t -> Loc.t option list -> t
    val lookup : locmap:t -> Names.inductive -> Loc.t option

end = struct

    type t = {
      default : Loc.t option;
      ind_to_loc : Loc.t Names.Indmap.t;
    }
    let lookup ~locmap:{ ind_to_loc; default } x =
      Names.Indmap.find_opt x ind_to_loc |> fun loc ->
      Option.append loc default

    let default default = { default; ind_to_loc = Names.Indmap.empty }

    let make ?default mind locs =
      let default, ind_to_loc =
        CList.fold_left_i (fun i (default,m) loc ->
          let m = match loc with
            | None -> m
            | Some loc -> Indmap.add (mind, i) loc m
          in
          let default = if Option.has_some default then default else loc in
          default, m)
          0 (default,Names.Indmap.empty) locs in
      { default; ind_to_loc }

  end

(* Assumes that dependencies are already defined *)
let rec define_individual_scheme_base ?loc kind suff f ~internal idopt (mind,i as ind) eff =
  (* FIXME: do not rely on the imperative modification of the global environment *)
  match f (Global.env ()) eff ind internal with
    | None -> None
    | Some (c, ctx) -> 
      let mib = Global.lookup_mind mind in
      let id = match idopt with
        | Some id -> id
        | None -> Id.of_string (suff (Some mib.mind_packets.(i))) in
      let role = Evd.Schema (ind, kind) in
      let const, neff = define ?loc internal role id c (Declareops.inductive_is_polymorphic mib) ctx in
      let eff = Evd.concat_side_effects neff eff in
      Some (const, eff)

and define_individual_scheme ?loc kind ~internal names (mind,i as ind) eff =
  match Hashtbl.find scheme_object_table kind with
  | _,MutualSchemeFunction _ -> assert false
  | s,IndividualSchemeFunction (f, deps) ->
    let deps = match deps with None -> [] | Some deps -> deps (Global.env ()) ind internal in
    match Option.List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) eff deps with
    | None -> CErrors.user_err Pp.(str "Problems were found during definition of scheme dependences.")
    | Some eff -> define_individual_scheme_base ?loc kind s f ~internal names ind eff

(* Assumes that dependencies are already defined *)
and define_mutual_scheme_base ?(locmap=Locmap.default None) kind suff f ~internal names inds eff =
  (* FIXME: do not rely on the imperative modification of the global environment *)
  let mind = (fst (List.hd inds)) in
  match f (Global.env ()) eff inds internal with
    | None -> None
    | Some (cl, ctx) -> 
      let mib = Global.lookup_mind mind in
      let ids =
        if Array.length cl <> List.length names then
          Array.init (Array.length mib.mind_packets) (fun i ->
              try (i,Int.List.assoc i names)
              with Not_found -> (i,Id.of_string (suff (Some mib.mind_packets.(i)))))
        else
          Array.of_list names
      in
      let fold effs idd cl =
        let (i,id) = idd in
        let role = Evd.Schema ((mind, i), kind)in
        let loc = Locmap.lookup ~locmap (mind,i) in
        let cst, neff = define ?loc internal role id cl (Declareops.inductive_is_polymorphic mib) ctx in
        (Evd.concat_side_effects neff effs, cst)
      in
      let (eff, consts) = Array.fold_left2_map fold eff ids cl in
      Some (consts, eff)
    
and define_mutual_scheme ?locmap kind ~internal names inds eff =
  let (strl,sortf,mutual) = kind in
  let kind = match sortf with Some k -> (strl,sortf,true) | None -> (strl,Some Sorts.InType,true) in 
  match Hashtbl.find scheme_object_table kind with
  | _,IndividualSchemeFunction _ -> assert false
  | s,MutualSchemeFunction (f, deps) ->
    let mind = (fst (List.hd inds)) in
    let deps = match deps with None -> [] | Some deps -> deps (Global.env ()) mind internal in
    match Option.List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) eff deps with
    | None -> CErrors.user_err Pp.(str "Problems were found during definition of scheme dependences.")
    | Some eff -> define_mutual_scheme_base ?locmap kind s f ~internal names inds eff

and declare_scheme_dependence eff sd =
match sd with
| SchemeIndividualDep (ind, kind, intern) ->
  if local_check_scheme kind ind eff then Some eff
  else
    begin match define_individual_scheme kind ~internal:intern None ind eff with
      | None -> None
      | Some (_, eff') -> Some (Evd.concat_side_effects eff' eff)
    end
| SchemeMutualDep (ind, kind, intern) ->
  if local_check_scheme kind (ind,0) eff then Some eff
  else
    begin match define_mutual_scheme kind ~internal:intern [] [(ind,0)] eff with
      | None -> None
      | Some (_, eff') -> Some (Evd.concat_side_effects eff' eff)
    end

let find_scheme kind (mind,i as ind) =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= fun sigma ->
  match local_lookup_scheme (Evd.eval_side_effects sigma) kind ind with
  | Some s ->
    Proofview.tclUNIT s
  | None ->
    try
      match Hashtbl.find scheme_object_table kind with
      | s,IndividualSchemeFunction (f, deps) ->
        let deps = match deps with None -> [] | Some deps -> deps (Global.env ()) ind true in (* /!\ *)
        begin match Option.List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) Evd.empty_side_effects deps with
          | None -> assert false
          | Some eff -> 
            begin match define_individual_scheme_base kind s f ~internal:true None ind eff with
              | None -> assert false
              | Some (c, eff) -> 
                Proofview.tclEFFECTS eff <*> Proofview.tclUNIT c
            end
        end
      | s,MutualSchemeFunction (f, deps) ->
        let deps = match deps with None -> [] | Some deps -> deps (Global.env ()) mind true in (* /!\ *)
        begin match Option.List.fold_left (fun eff dep -> declare_scheme_dependence eff dep) Evd.empty_side_effects deps with
          | None -> assert false
          | Some eff -> 
            begin match define_mutual_scheme_base kind s f ~internal:true [] [mind,i] eff with
              | None -> assert false
              | Some (ca, eff) -> 
                Proofview.tclEFFECTS eff <*> Proofview.tclUNIT ca.(i)
            end
        end
    with Rocqlib.NotFoundRef _ as e ->
      let e, info = Exninfo.capture e in
      Proofview.tclZERO ~info e

let define_individual_scheme ?loc ?(intern=false) kind names ind =
  match define_individual_scheme ?loc kind ~internal:intern names ind Evd.empty_side_effects with
    | None -> ()
    | Some (_ , eff) -> redeclare_schemes eff

let define_mutual_scheme ?locmap ?(intern=false) kind names inds =
  match define_mutual_scheme ?locmap kind ~internal:intern names inds Evd.empty_side_effects with
    | None -> ()
    | Some (_ , eff) -> redeclare_schemes eff
