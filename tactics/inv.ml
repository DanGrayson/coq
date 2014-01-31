(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Vars
open Context
open Termops
open Namegen
open Environ
open Inductiveops
open Printer
open Retyping
open Tacmach
open Clenv
open Tacticals
open Tactics
open Elim
open Equality
open Misctypes
open Tacexpr
open Proofview.Notations

let collect_meta_variables c =
  let rec collrec acc c = match kind_of_term c with
    | Meta mv -> mv::acc
    | _ -> fold_constr collrec acc c
  in
  collrec [] c

let check_no_metas clenv ccl =
  if occur_meta ccl then
    let metas = List.filter (fun m -> not (Evd.meta_defined clenv.evd m))
      (collect_meta_variables ccl) in
    let metas = List.map (Evd.meta_name clenv.evd) metas in
    let opts = match metas with [_] -> " " | _ -> "s " in
    errorlabstrm "inversion"
      (str ("Cannot find an instantiation for variable"^opts) ++
	 prlist_with_sep pr_comma pr_name metas
	 (* ajouter "in " ++ pr_lconstr ccl mais il faut le bon contexte *))

let var_occurs_in_pf gl id =
  let env = pf_env gl in
  occur_var env id (pf_concl gl) ||
  List.exists (occur_var_in_decl env id) (pf_hyps gl)

(* [make_inv_predicate (ity,args) C]

   is given the inductive type, its arguments, both the global
   parameters and its local arguments, and is expected to produce a
   predicate P such that if largs is the "local" part of the
   arguments, then (P largs) will be convertible with a conclusion of
   the form:

   <A1>a1=a1-><A2>a2=a2 ... -> C

   Algorithm: suppose length(largs)=n

   (1) Push the entire arity, [xbar:Abar], carrying along largs and
   the conclusion

   (2) Pair up each ai with its respective Rel version: a1==(Rel n),
   a2==(Rel n-1), etc.

   (3) For each pair, ai,Rel j, if the Ai is dependent - that is, the
   type of [Rel j] is an open term, then we construct the iterated
   tuple, [make_iterated_tuple] does it, and use that for our equation

   Otherwise, we just use <Ai>ai=Rel j

 *)

type inversion_status = Dep of constr option | NoDep

let compute_eqn env sigma n i ai =
  (ai, (mkRel (n-i),get_type_of env sigma (mkRel (n-i))))

let make_inv_predicate env sigma indf realargs id status concl =
  let nrealargs = List.length realargs in
  let (hyps,concl) =
    match status with
      | NoDep ->
	  (* We push the arity and leave concl unchanged *)
	  let hyps_arity,_ = get_arity env indf in
	  (hyps_arity,concl)
      | Dep dflt_concl ->
	  if not (occur_var env id concl) then
	    errorlabstrm "make_inv_predicate"
              (str "Current goal does not depend on " ++ pr_id id ++ str".");
          (* We abstract the conclusion of goal with respect to
             realargs and c to * be concl in order to rewrite and have
             c also rewritten when the case * will be done *)
	  let pred =
            match dflt_concl with
              | Some concl -> concl (*assumed it's some [x1..xn,H:I(x1..xn)]C*)
              | None ->
		let sort = get_sort_family_of env sigma concl in
		let p = make_arity env true indf (new_sort_in_family sort) in
		fst (Unification.abstract_list_all env
                       (Evd.create_evar_defs sigma)
		       p concl (realargs@[mkVar id])) in
	  let hyps,bodypred = decompose_lam_n_assum (nrealargs+1) pred in
	  (* We lift to make room for the equations *)
	  (hyps,lift nrealargs bodypred)
  in
  let nhyps = rel_context_length hyps in
  let env' = push_rel_context hyps env in
  let realargs' = List.map (lift nhyps) realargs in
  let pairs = List.map_i (compute_eqn env' sigma nhyps) 0 realargs' in
  (* Now the arity is pushed, and we need to construct the pairs
   * ai,mkRel(n-i+1) *)
  (* Now, we can recurse down this list, for each ai,(mkRel k) whether to
     push <Ai>(mkRel k)=ai (when   Ai is closed).
   In any case, we carry along the rest of pairs *)
  let rec build_concl eqns n = function
    | [] -> (it_mkProd concl eqns,n)
    | (ai,(xi,ti))::restlist ->
        let (lhs,eqnty,rhs) =
          if closed0 ti then
	    (xi,ti,ai)
          else
	    make_iterated_tuple env' sigma ai (xi,ti)
	in
        let eq_term = Coqlib.build_coq_eq () in
        let eqn = applist (eq_term ,[eqnty;lhs;rhs]) in
	build_concl ((Anonymous,lift n eqn)::eqns) (n+1) restlist
  in
  let (newconcl,neqns) = build_concl [] 0 pairs in
  let predicate = it_mkLambda_or_LetIn_name env newconcl hyps in
  (* OK - this predicate should now be usable by res_elimination_then to
     do elimination on the conclusion. *)
  (predicate,neqns)

(* The result of the elimination is a bunch of goals like:

           |- (cibar:Cibar)Equands->C

   where the cibar are either dependent or not.  We are fed a
   signature, with "true" for every recursive argument, and false for
   every non-recursive one.  So we need to do the
   sign_branch_len(sign) intros, thinning out all recursive
   assumptions.  This leaves us with exactly length(sign) assumptions.

   We save their names, and then do introductions for all the equands
   (there are some number of them, which is the other argument of the
   tactic)

   This gives us the #neqns equations, whose names we get also, and
   the #length(sign) arguments.

   Suppose that #nodep of these arguments are non-dependent.
   Generalize and thin them.

   This gives us #dep = #length(sign)-#nodep arguments which are
   dependent.

   Now, we want to take each of the equations, and do all possible
   injections to get the left-hand-side to be a variable.  At the same
   time, if we find a lhs/rhs pair which are different, we can
   discriminate them to prove false and finish the branch.

   Then, we thin away the equations, and do the introductions for the
   #nodep arguments which we generalized before.
 *)

(* Called after the case-assumptions have been killed off, and all the
   intros have been done.  Given that the clause in question is an
   equality (if it isn't we fail), we are responsible for projecting
   the equality, using Injection and Discriminate, and applying it to
   the concusion *)

(* Computes the subset of hypothesis in the local context whose
   type depends on t (should be of the form (mkVar id)), then
   it generalizes them, applies tac to rewrite all occurrencies of t,
   and introduces generalized hypotheis.
   Precondition: t=(mkVar id) *)

let dependent_hyps id idlist gl =
  let rec dep_rec =function
    | [] -> []
    | (id1,_,_)::l ->
	(* Update the type of id1: it may have been subject to rewriting *)
	let d = pf_get_hyp gl id1 in
	if occur_var_in_decl (Global.env()) id d
        then d :: dep_rec l
        else dep_rec l
  in
  dep_rec idlist

let split_dep_and_nodep hyps gl =
  List.fold_right
    (fun (id,_,_ as d) (l1,l2) ->
       if var_occurs_in_pf gl id then (d::l1,l2) else (l1,d::l2))
    hyps ([],[])

(* Computation of dids is late; must have been done in rewrite_equations*)
(* Will keep generalizing and introducing back and forth... *)
(* Moreover, others hyps depending of dids should have been *)
(* generalized; in such a way that [dids] can endly be cleared *)
(* Consider for instance this case extracted from Well_Ordering.v

  A : Set
  B : A ->Set
  a0 : A
  f : (B a0) ->WO
  y : WO
  H0 : (le_WO y (sup a0 f))
  ============================
   (Acc WO le_WO y)

  Inversion H0 gives

  A : Set
  B : A ->Set
  a0 : A
  f : (B a0) ->WO
  y : WO
  H0 : (le_WO y (sup a0 f))
  a1 : A
  f0 : (B a1) ->WO
  v : (B a1)
  H1 : (f0 v)=y
  H3 : a1=a0
  f1 : (B a0) ->WO
  v0 : (B a0)
  H4 : (existS A [a:A](B a) ->WO a0 f1)=(existS A [a:A](B a) ->WO a0 f)
  ============================
   (Acc WO le_WO (f1 v0))

while, ideally, we would have expected

  A : Set
  B : A ->Set
  a0 : A
  f0 : (B a0)->WO
  v : (B a0)
  ============================
   (Acc WO le_WO (f0 v))

obtained from destruction with equalities

  A : Set
  B : A ->Set
  a0 : A
  f : (B a0) ->WO
  y : WO
  H0 : (le_WO y (sup a0 f))
  a1 : A
  f0 : (B a1)->WO
  v : (B a1)
  H1 : (f0 v)=y
  H2 : (sup a1 f0)=(sup a0 f)
  ============================
   (Acc WO le_WO (f0 v))

by clearing initial hypothesis H0 and its dependency y, clearing H1
(in fact H1 can be avoided using the same trick as for newdestruct),
decomposing H2 to get a1=a0 and (a1,f0)=(a0,f), replacing a1 by a0
everywhere and removing a1 and a1=a0 (in fact it would have been more
regular to replace a0 by a1, avoiding f1 and v0 cannot replace f0 and v),
finally removing H4 (here because f is not used, more generally after using
eq_dep and replacing f by f0) [and finally rename a0, f0 into a,f].
Summary: nine useless hypotheses!
Nota: with Inversion_clear, only four useless hypotheses
*)

let generalizeRewriteIntros tac depids id =
  Proofview.Goal.enter begin fun gl ->
  let dids = Tacmach.New.of_old (dependent_hyps id depids) gl in
  (Tacticals.New.tclTHENLIST
    [Proofview.V82.tactic (bring_hyps dids); tac;
     (* may actually fail to replace if dependent in a previous eq *)
     intros_replacing (ids_of_named_context dids)])
  end

let rec tclMAP_i n tacfun = function
  | [] -> Tacticals.New.tclDO n (tacfun None)
  | a::l ->
      if Int.equal n 0 then Proofview.tclZERO (Errors.UserError ("", Pp.str"Too many names."))
      else Tacticals.New.tclTHEN (tacfun (Some a)) (tclMAP_i (n-1) tacfun l)

let remember_first_eq id x = if !x == MoveLast then x := MoveAfter id

(* invariant: ProjectAndApply is responsible for erasing the clause
   which it is given as input
   It simplifies the clause (an equality) to use it as a rewrite rule and then
   erases the result of the simplification. *)
(* invariant: ProjectAndApplyNoThining simplifies the clause (an equality) .
   If it can discriminate then the goal is proved, if not tries to use it as
   a rewrite rule. It erases the clause which is given as input *)

let projectAndApply thin id eqname names depids =
  let subst_hyp l2r id =
    tclTHEN (tclTRY(rewriteInConcl l2r (mkVar id)))
      (if thin then clear [id] else (remember_first_eq id eqname; tclIDTAC))
  in
  let substHypIfVariable tac id =
    Proofview.Goal.enter begin fun gl ->
    let (t,t1,t2) =
      Tacmach.New.of_old (fun gls -> Hipattern.dest_nf_eq gls (pf_get_hyp_typ gls id)) gl
    in
    match (kind_of_term t1, kind_of_term t2) with
    | Var id1, _ -> generalizeRewriteIntros (Proofview.V82.tactic (subst_hyp true id)) depids id1
    | _, Var id2 -> generalizeRewriteIntros (Proofview.V82.tactic (subst_hyp false id)) depids id2
    | _ -> tac id
    end
  in
  let deq_trailer id _ neqns =
    Tacticals.New.tclTHENLIST
      [Proofview.V82.tactic (if not (List.is_empty names) then clear [id] else tclIDTAC);
       (tclMAP_i neqns (fun idopt ->
	 Tacticals.New.tclTRY (Tacticals.New.tclTHEN
	   (intro_move idopt MoveLast)
	   (* try again to substitute and if still not a variable after *)
	   (* decomposition, arbitrarily try to rewrite RL !? *)
	   (Tacticals.New.tclTRY (Tacticals.New.onLastHypId (substHypIfVariable (fun id -> Proofview.V82.tactic (subst_hyp false id)))))))
	 names);
       Proofview.V82.tactic (if List.is_empty names then clear [id] else tclIDTAC)]
  in
  substHypIfVariable
    (* If no immediate variable in the equation, try to decompose it *)
    (* and apply a trailer which again try to substitute *)
    (fun id ->
      dEqThen false (deq_trailer id)
	(Some (ElimOnConstr (mkVar id,NoBindings))))
    id

(* Inversion qui n'introduit pas les hypotheses, afin de pouvoir les nommer
   soi-meme (proposition de Valerie). *)
let rewrite_equations_gene othin neqns ba =
  Proofview.Goal.enter begin fun gl ->
  let (depids,nodepids) =
    Tacmach.New.of_old (fun gl -> split_dep_and_nodep ba.assums gl) gl
  in
  let rewrite_eqns =
    match othin with
      | Some thin ->
          Tacticals.New.onLastHypId
            (fun last ->
              Tacticals.New.tclTHENLIST
                [Tacticals.New.tclDO neqns
                     (Tacticals.New.tclTHEN intro
                        (Tacticals.New.onLastHypId
                           (fun id ->
                              Tacticals.New.tclTRY
			        (projectAndApply thin id (ref MoveLast)
				  [] depids))));
                 Proofview.V82.tactic (onHyps (compose List.rev (afterHyp last)) bring_hyps);
                 Proofview.V82.tactic (onHyps (afterHyp last)
                   (compose clear ids_of_named_context))])
      | None -> Proofview.tclUNIT ()
  in
  (Tacticals.New.tclTHENLIST
    [Tacticals.New.tclDO neqns intro;
     Proofview.V82.tactic (bring_hyps nodepids);
     Proofview.V82.tactic (clear (ids_of_named_context nodepids));
     Proofview.V82.tactic (onHyps (compose List.rev (nLastDecls neqns)) bring_hyps);
     Proofview.V82.tactic (onHyps (nLastDecls neqns) (compose clear ids_of_named_context));
     rewrite_eqns;
     Proofview.V82.tactic (tclMAP (fun (id,_,_ as d) ->
               (tclORELSE (clear [id])
                 (tclTHEN (bring_hyps [d]) (clear [id]))))
       depids)])
  end

(* Introduction of the equations on arguments
   othin: discriminates Simple Inversion, Inversion and Inversion_clear
     None: the equations are introduced, but not rewritten
     Some thin: the equations are rewritten, and cleared if thin is true *)

let rec get_names allow_conj (loc,pat) = match pat with
  | IntroWildcard ->
      error "Discarding pattern not allowed for inversion equations."
  | IntroAnonymous | IntroForthcoming _ ->
      error "Anonymous pattern not allowed for inversion equations."
  | IntroFresh _ ->
      error "Fresh pattern not allowed for inversion equations."
  | IntroRewrite _->
      error "Rewriting pattern not allowed for inversion equations."
  | IntroOrAndPattern [l] ->
      let get_name id = Option.get (fst (get_names false id)) in
      if allow_conj then begin match l with
      | [] -> (None, [])
      | id :: l ->
        let n = get_name id in
        (Some n, n :: List.map get_name l)
      end else
	error"Nested conjunctive patterns not allowed for inversion equations."
  | IntroInjection l ->
      error "Injection patterns not allowed for inversion equations."
  | IntroOrAndPattern l ->
      error "Disjunctive patterns not allowed for inversion equations."
  | IntroIdentifier id ->
      (Some id,[id])

let extract_eqn_names = function
  | None -> None,[]
  | Some x -> x

let rewrite_equations othin neqns names ba =
  Proofview.Goal.enter begin fun gl ->
  let names = List.map (get_names true) names in
  let (depids,nodepids) =
    Tacmach.New.of_old (fun gl -> split_dep_and_nodep ba.assums gl) gl
  in
  let rewrite_eqns =
    let first_eq = ref MoveLast in
    match othin with
      | Some thin ->
          Tacticals.New.tclTHENLIST
            [Proofview.V82.tactic (onHyps (compose List.rev (nLastDecls neqns)) bring_hyps);
             Proofview.V82.tactic (onHyps (nLastDecls neqns) (compose clear ids_of_named_context));
	     tclMAP_i neqns (fun o ->
	       let idopt,names = extract_eqn_names o in
               (Tacticals.New.tclTHEN
		 (intro_move idopt MoveLast)
		 (Tacticals.New.onLastHypId (fun id ->
		   Tacticals.New.tclTRY (projectAndApply thin id first_eq names depids)))))
	       names;
	     Tacticals.New.tclMAP (fun (id,_,_) -> Proofview.tclUNIT () >= fun () -> (* delay for [first_eq]. *)
	       intro_move None (if thin then MoveLast else !first_eq))
	       nodepids;
	     Proofview.V82.tactic (tclMAP (fun (id,_,_) -> tclTRY (clear [id])) depids)]
      | None -> Proofview.tclUNIT ()
  in
  (Tacticals.New.tclTHENLIST
    [Tacticals.New.tclDO neqns intro;
     Proofview.V82.tactic (bring_hyps nodepids);
     Proofview.V82.tactic (clear (ids_of_named_context nodepids));
     rewrite_eqns])
  end

let interp_inversion_kind = function
  | SimpleInversion -> None
  | FullInversion -> Some false
  | FullInversionClear -> Some true

let rewrite_equations_tac (gene, othin) id neqns names ba =
  let othin = interp_inversion_kind othin in
  let tac =
    if gene then rewrite_equations_gene othin neqns ba
    else rewrite_equations othin neqns names ba in
  match othin with
  | Some true (* if Inversion_clear, clear the hypothesis *) ->
    Tacticals.New.tclTHEN tac (Proofview.V82.tactic (tclTRY (clear [id])))
  | _ ->
    tac


let raw_inversion inv_kind id status names =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let c = mkVar id in
    let reduce_to_atomic_ind = Tacmach.New.pf_apply Tacred.reduce_to_atomic_ind gl in
    let type_of = Tacmach.New.pf_type_of gl in
    begin
      try
        Proofview.tclUNIT (reduce_to_atomic_ind (type_of c))
      with UserError _ ->
        Proofview.tclZERO (Errors.UserError ("raw_inversion" ,
	                                     str ("The type of "^(Id.to_string id)^" is not inductive.")))
    end >= fun (ind,t) ->
    try
      let indclause = Tacmach.New.of_old (fun gl -> mk_clenv_from gl (c,t)) gl in
      let ccl = clenv_type indclause in
      check_no_metas indclause ccl;
      let IndType (indf,realargs) = find_rectype env sigma ccl in
      let (elim_predicate,neqns) =
        make_inv_predicate env sigma indf realargs id status concl in
      let (cut_concl,case_tac) =
        if status != NoDep && (dependent c concl) then
          Reduction.beta_appvect elim_predicate (Array.of_list (realargs@[c])),
          Tacticals.New.case_then_using
        else
          Reduction.beta_appvect elim_predicate (Array.of_list realargs),
          Tacticals.New.case_nodep_then_using
      in
      (Tacticals.New.tclTHENS
         (assert_tac Anonymous cut_concl)
         [case_tac names
             (introCaseAssumsThen (rewrite_equations_tac inv_kind id neqns))
             (Some elim_predicate) ([],[]) ind indclause;
          Tacticals.New.onLastHypId
            (fun id ->
              (Tacticals.New.tclTHEN
                 (Proofview.V82.tactic (apply_term (mkVar id)
                                          (List.init neqns (fun _ -> Evarutil.mk_new_meta()))))
                 reflexivity))])
    with e when Errors.noncritical e ->
      let e = Errors.push e in
      Proofview.tclZERO e
  end

(* Error messages of the inversion tactics *)
let wrap_inv_error id = function
  | Indrec.RecursionSchemeError
      (Indrec.NotAllowedCaseAnalysis (_,(Type _ | Prop Pos as k),i)) ->
      Proofview.tclZERO (Errors.UserError ("",
	(strbrk "Inversion would require case analysis on sort " ++
	pr_sort k ++
	strbrk " which is not allowed for inductive definition " ++
	pr_inductive (Global.env()) i ++ str ".")))
  | e -> Proofview.tclZERO e

(* The most general inversion tactic *)
let inversion inv_kind status names id =
  Proofview.tclORELSE
    (raw_inversion inv_kind id status names)
    (wrap_inv_error id)

(* Specializing it... *)

let inv_gen gene thin status names =
  try_intros_until (inversion (gene,thin) status names)

open Tacexpr

let inv k = inv_gen false k NoDep

let half_inv_tac id  = inv SimpleInversion None (NamedHyp id)
let inv_tac id       = inv FullInversion None (NamedHyp id)
let inv_clear_tac id = inv FullInversionClear None (NamedHyp id)

let dinv k c = inv_gen false k (Dep c)

let half_dinv_tac id  = dinv SimpleInversion None None (NamedHyp id)
let dinv_tac id       = dinv FullInversion None None (NamedHyp id)
let dinv_clear_tac id = dinv FullInversionClear None None (NamedHyp id)

(* InvIn will bring the specified clauses into the conclusion, and then
 * perform inversion on the named hypothesis.  After, it will intro them
 * back to their places in the hyp-list. *)

let invIn k names ids id =
  Proofview.Goal.enter begin fun gl ->
    let hyps = List.map (fun id -> Tacmach.New.pf_get_hyp id gl) ids in
    let concl = Proofview.Goal.concl gl in
    let nb_prod_init = nb_prod concl in
    let intros_replace_ids =
      Proofview.Goal.enter begin fun gl ->
        let concl = Proofview.Goal.concl gl in
        let nb_of_new_hyp =
          nb_prod concl - (List.length hyps + nb_prod_init)
        in
        if nb_of_new_hyp < 1 then
          intros_replacing ids
        else
          Tacticals.New.tclTHEN (Tacticals.New.tclDO nb_of_new_hyp intro) (intros_replacing ids)
      end
    in
    Proofview.tclORELSE
      (Tacticals.New.tclTHENLIST
         [Proofview.V82.tactic (bring_hyps hyps);
          inversion (false,k) NoDep names id;
          intros_replace_ids])
      (wrap_inv_error id)
  end

let invIn_gen k names idl = try_intros_until (invIn k names idl)

let inv_clause k names = function
  | [] -> inv k names
  | idl -> invIn_gen k names idl
