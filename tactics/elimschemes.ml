(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to inductive schemes
   initially developed by Christine Paulin (induction schemes), Vincent
   Siles (decidable equality and boolean equality) and Matthieu Sozeau
   (combined scheme) in file command.ml, Sep 2009 *)

(* This file builds schemes related to case analysis and recursion schemes *)

open Constr
open Indrec
open Declarations
open Ind_tables
open UnivGen

(* Induction/recursion schemes *)

let build_induction_scheme_in_type env dep sort ind =
  let sigma = Evd.from_env env in
  let sigma, pind = Evd.fresh_inductive_instance ~rigid:UState.univ_rigid env sigma ind in
  let pind = Util.on_snd EConstr.EInstance.make pind in
  let sigma, sort = Evd.fresh_sort_quality ~rigid:UnivRigid sigma sort in
  let sigma, c = build_induction_scheme env sigma pind dep sort in
  Some (EConstr.to_constr sigma c, Evd.ustate sigma)

let build_mutual_induction_scheme_in_type env dep sort isrec l =
  let ind,_ = match l with | x::_ -> x | [] -> assert false in
  let sigma, inst =
    let _, ctx = Typeops.type_of_global_in_context env (Names.GlobRef.IndRef (ind,0)) in
    let u, ctx = UnivGen.fresh_instance_from ctx None in
    let u = EConstr.EInstance.make u in
    let sigma = Evd.from_ctx (UState.of_context_set ctx) in
    sigma, u
  in
  let n = List.length l in
  let sigma, lrecspec =
    let rec loop i n sigma ll =
      if i>=n then (sigma,ll)
      else
        let new_sigma, new_sort = Evd.fresh_sort_quality ~rigid:UnivRigid sigma sort in
        let (indd,ii) = List.nth l i in
        let new_l = List.append ll [(((indd,ii),inst),dep,new_sort)] in
        loop (i + 1) n new_sigma new_l
    in
    loop 0 n sigma []
  in
  let sigma, listdecl =
    if isrec then Indrec.build_mutual_induction_scheme env sigma ~force_mutual:false lrecspec
    else
      List.fold_left_map (fun sigma (ind,dep,sort) ->
          let sigma, c = Indrec.build_case_analysis_scheme env sigma ind dep sort in
          let c, _ = Indrec.eval_case_analysis c in
          sigma, c)
        sigma lrecspec
  in
  let array = Array.of_list listdecl in
  let l = Array.map (fun x -> EConstr.to_constr sigma x) array in
  Some (l, Evd.ustate sigma)

(**********************************************************************)
(* [modify_sort_scheme s rec] replaces the sort of the scheme
   [rec] by [s] *)

let change_sort_arity sort =
  let rec drec a = match kind a with
    | Cast (c,_,_) -> drec c
    | Prod (n,t,c) -> let s, c' = drec c in s, mkProd (n, t, c')
    | LetIn (n,b,t,c) -> let s, c' = drec c in s, mkLetIn (n,b,t,c')
    | Sort s -> s, mkSort sort
    | _ -> assert false
  in
    drec


(** [weaken_sort_scheme env sigma s n c t] derives by subtyping from [c:t]
   whose conclusion is quantified on [Type i] at position [n] of [t] a
   scheme quantified on sort [s]. [s] is declared less or equal to [i]. *)
let weaken_sort_scheme env evd sort npars term ty =
  let open Context.Rel.Declaration in
  let evdref = ref evd in
  let rec drec ctx np elim =
    match kind elim with
      | Prod (n,t,c) ->
          let ctx = LocalAssum (n, t) :: ctx in
          if Int.equal np 0 then
            let osort, t' = change_sort_arity (EConstr.ESorts.kind !evdref sort) t in
              evdref := Evd.set_leq_sort !evdref sort (EConstr.ESorts.make osort);
              mkProd (n, t', c),
              mkLambda (n, t', mkApp(term, Context.Rel.instance mkRel 0 ctx))
          else
            let c',term' = drec ctx (np-1) c in
            mkProd (n, t, c'), mkLambda (n, t, term')
      | LetIn (n,b,t,c) ->
        let ctx = LocalDef (n, b, t) :: ctx in
        let c',term' = drec ctx np c in
        mkLetIn (n,b,t,c'), mkLetIn (n,b,t,term')
      | _ -> CErrors.anomaly ~label:"weaken_sort_scheme" (Pp.str "wrong elimination type.")
  in
  let ty, term = drec [] npars ty in
    !evdref, ty, term

let optimize_non_type_induction_scheme kind dep sort env _handle ind _ =
  (* This non-local call to [lookup_scheme] is fine since we do not use it on a
     dependency generated on the fly. *)
  match lookup_scheme kind ind with
  | Some cte ->
    let sigma = Evd.from_env env in
    (* in case the inductive has a type elimination, generates only one
       induction scheme, the other ones share the same code with the
       appropriate type *)
    let sigma, cte = Evd.fresh_constant_instance env sigma cte in
    let c = mkConstU cte in
    let t = Typeops.type_of_constant_in env cte in
    let (mib,mip) = Inductive.lookup_mind_specif env ind in
    let npars =
      (* if a constructor of [ind] contains a recursive call, the scheme
         is generalized only wrt recursively uniform parameters *)
      if (Inductiveops.mis_is_recursive_subset env [ind] (Rtree.Kind.make mip.mind_recargs))
      then
        mib.mind_nparams_rec
      else
        mib.mind_nparams in
    (* here, if [sort] is [Type] then it means that it's actually a [Set]:
       we optimise non-[Type] schemes *)
    let sigma, sort = Evd.fresh_sort_quality sigma sort in
    let sigma, t', c' = weaken_sort_scheme env sigma sort npars c t in
    let sigma = Evd.minimize_universes sigma in
    Some (Evarutil.nf_evars_universes sigma c', Evd.ustate sigma)
  | None ->
    build_induction_scheme_in_type env dep sort ind

let make_suff_sort one_ind suff dep =
  match one_ind with
  | None -> suff
  | Some i ->
    let sort = i.mind_sort
    in
    match sort with
    | Prop -> if dep then (Names.Id.to_string i.mind_typename) ^ "_" ^ suff ^ "_dep"
      else (Names.Id.to_string i.mind_typename) ^ "_" ^ suff
    | Type _ | SProp | Set -> if dep then (Names.Id.to_string i.mind_typename) ^ "_" ^ suff
      else (Names.Id.to_string i.mind_typename) ^ "_" ^ suff ^ "_nodep"
    | QSort _ -> (Names.Id.to_string i.mind_typename) ^ "_" ^ suff

let inType = (UnivGen.QualityOrSet.Qual (Sorts.Quality.QConstant QType))
let inSet = (UnivGen.QualityOrSet.Set)
let inProp = (UnivGen.QualityOrSet.Qual (Sorts.Quality.QConstant QProp))
let inSProp = (UnivGen.QualityOrSet.Qual (Sorts.Quality.QConstant QSProp))
  
let rect_dep =
  declare_individual_scheme_object (["Induction"], Some (inType))
    (fun id -> make_suff_sort id "rect" true)
    (fun env _ x _ -> build_induction_scheme_in_type env true inType x)

let mutual_rect_dep =
  declare_mutual_scheme_object (["Induction"], Some inType)
    (fun id -> make_suff_sort id "rect" true)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env true QualityOrSet.qtype true x)

let rec_dep =
  declare_individual_scheme_object (["Induction"], Some inSet)
    (fun id -> make_suff_sort id "rec" true)
    (optimize_non_type_induction_scheme rect_dep true QualityOrSet.set)

let mutual_rec_dep =
  declare_mutual_scheme_object (["Induction"], Some inSet)
    (fun id -> make_suff_sort id "rec" true)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env true QualityOrSet.set true x)

let ind_dep =
  declare_individual_scheme_object (["Induction"], Some inProp)
    (fun id -> make_suff_sort id "ind" true)
    (optimize_non_type_induction_scheme rec_dep true QualityOrSet.prop)

let mutual_ind_dep =
  declare_mutual_scheme_object (["Induction"], Some inProp)
    (fun id -> make_suff_sort id "ind" true)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env true QualityOrSet.prop true x)

let sind_dep =
  declare_individual_scheme_object (["Induction"], Some inSProp)
    (fun id -> make_suff_sort id "inds" true)
    (fun env _ x _ -> build_induction_scheme_in_type env true QualityOrSet.sprop x)

let mutual_sind_dep =
  declare_mutual_scheme_object (["Induction"], Some inSProp)
    (fun id -> make_suff_sort id "inds" true)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env true QualityOrSet.sprop true x)

let rect_nodep =
  declare_individual_scheme_object (["Minimality"], Some inType)
    (fun id -> make_suff_sort id "rect" false)
    (fun env _ x _ -> build_induction_scheme_in_type env false QualityOrSet.qtype x)

let mutual_rect_nodep =
  declare_mutual_scheme_object (["Minimality"], Some inType)
    (fun id -> make_suff_sort id "rect" false)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env false QualityOrSet.qtype true x)

let rec_nodep =
  declare_individual_scheme_object (["Minimality"], Some inSet)
    (fun id -> make_suff_sort id "rec" false)
    (optimize_non_type_induction_scheme rect_nodep false QualityOrSet.set)

let mutual_rec_nodep =
  declare_mutual_scheme_object (["Minimality"], Some inSet)
    (fun id -> make_suff_sort id "rec" false)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env false QualityOrSet.set true x)

let ind_nodep =
  declare_individual_scheme_object (["Minimality"], Some inProp)
    (fun id -> make_suff_sort id "ind" false)
    (optimize_non_type_induction_scheme rec_nodep false QualityOrSet.prop)

let mutual_ind_nodep =
  declare_mutual_scheme_object (["Minimality"], Some inProp)
    (fun id -> make_suff_sort id "ind" false)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env false inProp true x)

let sind_nodep =
  declare_individual_scheme_object (["Minimality"], Some inSProp)
    (fun id -> make_suff_sort id "inds" false)
    (fun env _ x _ -> build_induction_scheme_in_type env false QualityOrSet.sprop x)

let mutual_sind_nodep =
  declare_mutual_scheme_object (["Minimality"], Some inSProp)
    (fun id -> make_suff_sort id "inds" false)
    (fun env _ x _ -> build_mutual_induction_scheme_in_type env false QualityOrSet.sprop true x)

let elim_scheme ~dep ~to_kind =
  let open QualityOrSet in
  match to_kind with
  | Qual q ->
     begin
       match q with
       | QConstant QSProp when dep -> sind_dep
       | QConstant QProp when dep -> ind_dep
       | (QConstant QType | QVar _) when dep -> rect_dep
       | QConstant QSProp -> sind_nodep
       | QConstant QProp -> ind_nodep
       | QConstant QType | QVar _ -> rect_nodep
     end
  | Set -> if dep then rec_dep else rec_nodep

(* Case analysis *)

let build_case_analysis_scheme_in_type env dep sort ind =
  let sigma = Evd.from_env env in
  let (sigma, indu) = Evd.fresh_inductive_instance env sigma ind in
  let indu = Util.on_snd EConstr.EInstance.make indu in
  let sigma, sort = Evd.fresh_sort_quality ~rigid:UnivRigid sigma sort in
  let (sigma, c) = build_case_analysis_scheme env sigma indu dep sort in
  let (c, _) = Indrec.eval_case_analysis c in
  Some (EConstr.Unsafe.to_constr c, Evd.ustate sigma)

let case_dep =
    declare_individual_scheme_object (["Elimination"], Some inType)
      (fun id -> make_suff_sort id "caset" true)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env true QualityOrSet.qtype x)

let casep_dep =
    declare_individual_scheme_object (["Elimination"], Some inProp)
      (fun id -> make_suff_sort id "case" true)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env true QualityOrSet.prop x)

let cases_dep =
    declare_individual_scheme_object (["Elimination"], Some inSProp)
      (fun id -> make_suff_sort id "cases" true)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env true QualityOrSet.sprop x)

let casep_dep_set =
    declare_individual_scheme_object (["Elimination"], Some inSet)
      (fun id -> make_suff_sort id "case" true)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env true QualityOrSet.set x)

let case_nodep =
    declare_individual_scheme_object (["Case"], Some inType)
      (fun id -> make_suff_sort id "caset" false)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env false QualityOrSet.qtype x)

let casep_nodep =
    declare_individual_scheme_object (["Case"], Some inProp)
      (fun id -> make_suff_sort id "case" false)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env false QualityOrSet.prop x)

let cases_nodep =
    declare_individual_scheme_object (["Case"], Some inSProp)
      (fun id -> make_suff_sort id "cases" false)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env false QualityOrSet.sprop x)

let case_nodep_set =
    declare_individual_scheme_object (["Case"], Some inSet)
      (fun id -> make_suff_sort id "case" false)
      (fun env _ x _ -> build_case_analysis_scheme_in_type env false QualityOrSet.set x)      
