(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Reduction
open Declarations
open Constr
open Univ
open Util

let rec break_app c =
  match Constr.kind c with
  | App (c, args) ->
    let hd, args0 = break_app c in
    hd, Array.append args0 args
  | Cast (c, _, _) -> break_app c
  | _ -> c, [||]

let infer_level_eq u variances =
  if LMap.mem u variances
  then LMap.set u Variance.Invariant variances
  else variances

let infer_level_leq u variances =
  match LMap.find u variances with
  | exception Not_found -> variances
  | varu -> LMap.set u (Variance.sup varu Variance.Covariant) variances

let infer_generic_instance_eq variances u =
  Array.fold_left (fun variances u -> infer_level_eq u variances)
    variances (Instance.to_array u)

let variance_pb cv_pb var =
  let open Variance in
  match cv_pb, var with
  | _, Irrelevant -> Irrelevant
  | _, Invariant -> Invariant
  | CONV, Covariant -> Invariant
  | CUMUL, Covariant -> Covariant

let infer_cumulative_ind_instance cv_pb cumi variances u =
  Array.fold_left2 (fun variances varu u ->
      match LMap.find u variances with
      | exception Not_found -> variances
      | varu' ->
        LMap.set u (Variance.sup varu' (variance_pb cv_pb varu)) variances)
    variances (ACumulativityInfo.variance cumi) (Instance.to_array u)

let infer_inductive_instance cv_pb env variances ind nargs u =
  let mind = Environ.lookup_mind (fst ind) env in
  match mind.mind_universes with
  | Monomorphic_ind _ -> assert (Instance.is_empty u); variances
  | Polymorphic_ind _ -> infer_generic_instance_eq variances u
  | Cumulative_ind cumi ->
    if not (Int.equal (inductive_cumulativity_arguments (mind,snd ind)) nargs)
    then infer_generic_instance_eq variances u
    else infer_cumulative_ind_instance cv_pb cumi variances u

let infer_constructor_instance_eq env variances ((mi,ind),ctor) nargs u =
  let mind = Environ.lookup_mind mi env in
  match mind.mind_universes with
  | Monomorphic_ind _ -> assert (Instance.is_empty u); variances
  | Polymorphic_ind _ -> infer_generic_instance_eq variances u
  | Cumulative_ind cumi ->
    if not (Int.equal (constructor_cumulativity_arguments (mind,ind,ctor)) nargs)
    then infer_generic_instance_eq variances u
    else infer_cumulative_ind_instance CONV cumi variances u

let infer_sort cv_pb variances s =
  match cv_pb with
  | CONV ->
    LSet.fold infer_level_eq (Universe.levels (Sorts.univ_of_sort s)) variances
  | CUMUL ->
    LSet.fold infer_level_leq (Universe.levels (Sorts.univ_of_sort s)) variances

exception TryReduce

let check_reduce reduce env c =
  if not reduce then
    let cb = Environ.lookup_constant c env in
    match cb.const_body with
    | Def _ -> raise TryReduce
    | OpaqueDef _ | Undef _ -> ()

(* env is for looking up globrefs, binders are irrelevant *)
let rec infer_term ~reduce cv_pb env variances c =
  let c = if reduce then Reduction.whd_all env c else c in
  let hd, args = break_app c in
  let nargs = Array.length args in
  let variances = match Constr.kind hd with
    | App _ | Cast _ -> assert false
    | Sort s -> infer_sort cv_pb variances s
    | Const (c,u) ->
      check_reduce reduce env c;
      infer_generic_instance_eq variances u
    | Ind (ind,u) -> infer_inductive_instance cv_pb env variances ind nargs u
    | Construct (ctor,u) ->
      (* NB: no constructor_instance_leq *)
      infer_constructor_instance_eq env variances ctor nargs u
    | Prod (_,t,b) ->
      let variances = infer_term ~reduce CONV env variances t in
      infer_term ~reduce cv_pb env variances b
    | LetIn (_,b,t,c) ->
      let variances = infer_term ~reduce CONV env variances b in
      let variances = infer_term ~reduce CONV env variances t in
      infer_term ~reduce cv_pb env variances c
    | Rel _ | Var _ | Meta _ | Evar _
    | Lambda _
    | Proj _ | Case _ | Fix _ | CoFix _ ->
      fold (infer_term ~reduce CONV env) variances hd
  in
  Array.fold_left (infer_term ~reduce CONV env) variances args

let infer_term cv_pb env variances c =
  try infer_term ~reduce:false cv_pb env variances c
  with TryReduce -> infer_term ~reduce:true cv_pb env variances c

let infer_arity_constructor env variances arcn is_arity params =
  let numchecked = ref 0 in
  let numparams = Context.Rel.nhyps params in
  let basic_check variances tp =
    let variances =
      if !numchecked >= numparams then
        infer_term CUMUL env variances tp
      else
        variances
    in
    numchecked := !numchecked + 1; variances
  in
  let infer_typ typ variances =
    match typ with
    | Context.Rel.Declaration.LocalAssum (_, typ') ->
      basic_check variances typ'
    | Context.Rel.Declaration.LocalDef _ -> assert false
  in
  let arcn' = Term.it_mkProd_or_LetIn arcn params in
  let typs, codom = Reduction.dest_prod env arcn' in
  let variances = Context.Rel.fold_outside infer_typ typs ~init:variances in
  if not is_arity then basic_check variances codom else variances

let infer_inductive env mie =
  let open Entries in
  let { mind_entry_params = params;
        mind_entry_inds = entries; } = mie
  in
  let univs =
    match mie.mind_entry_universes with
    | Monomorphic_ind_entry _
    | Polymorphic_ind_entry _ as univs -> univs
    | Cumulative_ind_entry cumi ->
      let uctx = CumulativityInfo.univ_context cumi in
      let uarray = Instance.to_array @@ UContext.instance uctx in
      let env = Environ.push_context uctx env in
      let variances =
        Array.fold_left (fun variances u -> LMap.add u Variance.Irrelevant variances)
          LMap.empty uarray
      in
      let variances = List.fold_left (fun variances entry ->
          let _, params = Typeops.infer_local_decls env params in
          let variances = infer_arity_constructor
              env variances entry.mind_entry_arity true params
          in
          List.fold_left
            (fun variances cons ->
               infer_arity_constructor
                 env variances cons false params)
            variances entry.mind_entry_lc)
          variances
          entries
      in
      let variances = Array.init (Array.length uarray)
          (fun i -> LMap.find uarray.(i) variances)
      in
      Cumulative_ind_entry (CumulativityInfo.make (uctx, variances))
  in
  { mie with mind_entry_universes = univs }
