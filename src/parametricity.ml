(**************************************************************************)
(*                                                                        *)
(*     CoqParam                                                           *)
(*     Copyright (C) 2012                                                 *)
(*                                                                        *)
(*     Chantal Keller                                                     *)
(*     Marc Lasson                                                        *)
(*                                                                        *)
(*     INRIA - École Polytechnique - ÉNS de Lyon                          *)
(*                                                                        *)
(*   This file is distributed under the terms of the GNU Lesser General   *)
(*   Public License                                                       *)
(*                                                                        *)
(**************************************************************************)

open Term
open Names
open Vars
open Constr
open Environ
open Util
open Context
open Environ
open Debug

let error msg = 
  raise (Errors.UserError ("Parametricity plugin", msg))

module CoqConstants = struct
  let msg = "parametricity: unable to fetch constants"

  let add_constraints evdref univ =
    let env = Global.env () in 
    let extract_type_sort poly_ref = 
      let poly_ref = Evarutil.e_new_global evdref (delayed_force poly_ref) in 
      let ref_type = Retyping.get_type_of env !evdref poly_ref in 
      let ref_sort = 
        let _, a, _ = destProd ref_type in 
        a
      in 
      ignore (Evarconv.e_cumul env evdref univ ref_sort)
    in 
    let extract_pred_sort poly_ref = 
      let poly_ref = Evarutil.e_new_global evdref (delayed_force poly_ref) in 
      let ref_type = Retyping.get_type_of env !evdref poly_ref in 
      let ref_sort = 
        let _, _, typ = destProd ref_type in 
        let _, _, typ = destProd typ in 
        let _, a, _ = destProd typ in 
        snd (decompose_prod a) 
      in 
      ignore (Evarconv.e_cumul env evdref univ ref_sort)
    in  
    List.iter extract_type_sort [Program.coq_eq_ind; Program.coq_eq_refl; Program.coq_eq_rect];
    extract_pred_sort Program.coq_eq_rect

  let eq evdref args = 
    Program.papp evdref Program.coq_eq_ind args 
  
  let eq_refl evdref args = 
    Program.papp evdref Program.coq_eq_refl args 

  let transport evdref args = 
    Program.papp evdref Program.coq_eq_rect args 

  let proof_irrelevance evdref args = 
    Program.papp evdref (fun () -> Coqlib.coq_reference msg ["Logic"; "ProofIrrelevance"] "proof_irrelevance") args 
end

let program_mode = ref false
let set_program_mode = 
   Goptions.declare_bool_option 
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "Parametricity Program";
      Goptions.optkey   = ["Parametricity"; "Program"];
      Goptions.optread  = (fun () -> !program_mode);
      Goptions.optwrite = (:=) program_mode }

let default_arity = 2

let hyps_from_rel_context env = 
  let rctx = Environ.rel_context env in 
  let rec aux acc depth = function 
      [] -> acc
    | (_, None, _) :: tl -> aux (depth :: acc) (depth + 1) tl
    | _ :: tl -> aux acc (depth + 1) tl 
  in 
  aux [] 1 rctx 

let compose_prod_assum rel_context init = 
 fold_rel_context_reverse (fun (acc : constr) ->
  function (x, None, typ) -> mkProd (x, typ, acc) 
         | (x, Some def, typ) -> mkLetIn (x, def, typ, acc)) ~init rel_context

let compose_lam_assum rel_context init = 
 fold_rel_context_reverse (fun (acc : constr) ->
  function (x, None, typ) -> mkLambda (x, typ, acc) 
         | (x, Some def, typ) -> mkLetIn (x, def, typ, acc)) ~init rel_context

let decompose_prod_n_assum_by_prod n =
  if n < 0 then
    failwith "decompose_prod_n_assum_by_prod: integer parameter must be positive";
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else match kind_of_term c with
    | Prod (x,t,c)    -> prodec_rec (add_rel_decl (x,None,t) l) (n-1) c
    | LetIn (x,b,t,c) -> prodec_rec (add_rel_decl (x,Some b,t) l) n c
    | Cast (c,_,_)      -> prodec_rec l n c
    | c -> failwith "decompose_prod_n_assum_by_prod: not enough assumptions"
  in
  prodec_rec empty_rel_context n

let decompose_prod =
  let rec prodec_rec l c = match kind_of_term c with
    | Prod (x,t,c) -> prodec_rec ((x,t)::l) c
    | _              -> l,c
  in
  prodec_rec []

let decompose_lam =
  let rec lamdec_rec l c = match kind_of_term c with
    | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | _                -> l,c
  in
  lamdec_rec []


let rec has_cast t = 
 let t = snd (decompose_lam t) in 
 let t = snd (decompose_prod t) in 
 isCast t || Constr.fold (fun acc t -> acc || has_cast t) false t
  


let prop_or_type env evdr s = s

(* [prime order index c] replace all the free variable in c by its [index]-projection where 0 <= index < order. 
 * Exemple, if c is a well-defined term in context x, y, z |- c, then [prime order index c] is 
 * c[x_index/x,y_index/y, z_index/z] and is well-defined in:
 *    x_1, x_2, ...,x_order, x_R, y_1, y_2, ..., y_order, y_R, z1, z_2, ..., z_order, z_R
 * *)
let rec prime order index c = 
  let rec aux depth c = match Constr.kind c with
    | Constr.Rel i -> 
        if i <= depth then c else Constr.mkRel (depth + (order + 1) * (i - depth)  - index) 
    | _ -> Constr.map_with_binders ((+) 1) aux depth c
  in aux 0 c

(* [translate_string] provides a generic name for the translation of identifiers. *)
let translate_string order x =
 match order with 
   | 0 -> x
   | 1 -> x^"_P"
   | 2 -> x^"_R"
   | 3 -> x^"_T"
   | n -> x^"_R_"^(string_of_int n)
 
(* [prime_string] provides a generic name for the projections of indentifiers. *)
let prime_string order value x = 
  if value >= order then 
    translate_string order x
  else if order = 1 then x else 
    match value with 
     | 0 -> x^"₁"
     | 1 -> x^"₂"
     | 2 -> x^"₃"
     | n -> Printf.sprintf "%s_%d" x (n-1)

(* The translation of identifiers. *)
let translate_id order y = (id_of_string @@ translate_string order @@ string_of_id @@ y)
(* The prime of identifiers. *)
let prime_id order value y = (id_of_string @@ prime_string order value @@ string_of_id @@ y)
(* The prime of names. *)
let prime_name order value = function
  | Name y -> Name  (prime_id order value y)
  | Anonymous -> Anonymous
(* The translation of names. *)
let translate_name order = function
  | Name y -> Name  (translate_id order y)
  | Anonymous -> Anonymous

(*
(* l \in ⟦s⟧_3 = l₁ → l₂ → l₃ → t, 
 * where t is Prop if s ∈ {Set, Prop} or s otherwise. *)
let translate_sort l s = 
  let rec aux k acc = function 
  | [] -> acc
  | hd::tl ->
      let k = k - 1 in 
      aux k (mkArrow (mkRel k) acc) tl
  in
  aux (List.length l) (prop_or_type s) l *)

(* [range f n] computes [f n-1; f n-2; ...; f 0] *)
let range f order =
  let rec aux k acc = 
    if k < order then 
      aux (k + 1) ((f k)::acc)
    else 
      acc
  in 
  aux 0 []

(* [rev_range f n] computes [f 0; f 1; ...; f n-1] *)
let rev_range f order = 
  List.rev (range f order)

(* the iterator for natural numbers. *)
let fold_nat f x = 
  let rec aux acc n =
    if n = 0 then acc else
      let n = n - 1 in 
      aux (f n acc) n
  in aux x 

(* [first n l] returns the first [n] elements of [l]. *)
let firsts n l = fst (List.chop n l)

(* If [t] is well-defined in G, x1, ..., xn, [apply_head_variables t n] returns 
 * (t x1 ... xn) *)
let apply_head_variables t n = 
  let l = fold_nat (fun k l -> (mkRel (k + 1))::l) [] n in 
  mkApp (t, Array.of_list (List.rev l)) 

let apply_head_variables_ctxt t ctxt = 
  mkApp (t, Termops.extended_rel_vect 0 ctxt) 

(* Substitution in a signature. *)
let substnl_rel_context subst n sign =
  let rec aux n = function
  | d::sign -> substnl_decl subst n d :: aux (n+1) sign
  | [] -> []
  in List.rev (aux n (List.rev sign))

let substl_rel_context subst = substnl_rel_context subst 0


(* A variant of mkApp that reduces redexes. *)
let mkBetaApp (f, v) = Reduction.beta_appvect f v

(* If [c] is well-formed type in env [G], then [generalize G c] returns [forall G.c]. *)
let generalize_env (env : Environ.env) (init : types) = 
  let l = Environ.rel_context env in 
  Context.fold_rel_context_reverse (fun x y -> mkProd_or_LetIn y x) l ~init 

(* If [c] is well-formed term in env [G], then [generalize G c] returns [fun G.c]. *)
let abstract_env (env : Environ.env) (init : constr) = 
  let l = Environ.rel_context env in 
  Context.fold_rel_context_reverse (fun x y -> mkLambda_or_LetIn y x) l ~init 

let mkFreshInd env evd c = 
  let evd', res = Evd.fresh_inductive_instance env !evd c in 
  evd := evd'; mkIndU res

let mkFreshConstruct env evd c = 
  let evd', res = Evd.fresh_constructor_instance env !evd c in 
  evd := evd'; mkConstructU res

(* G |- t ---> |G|, x1, x2 |- [x1,x2] in |t| *)
let rec relation order evd env (t : constr) : constr = 
  debug_string [`Relation] (Printf.sprintf "relation %d evd env t" order);
  debug_evar_map [`Relation]  "evd =" !evd; 
  debug [`Relation] "input =" env !evd t;
  let res = match kind t with 
    | Sort s -> fold_nat (fun _ -> mkArrow (mkRel order)) (prop_or_type env evd t) order
    | Prod (x, a, b) ->
        let a_R = relation order evd env a in 
        (* |G|, x1, x2 |- [x1,x2] in |a| *)
        let a_R = liftn order (order + 1) a_R in 
        (*|G|, f1, f2, x1, x2 |- [x1,x2] in |a| *)
        let env = push_rel (x, None, a) env in 
        let b_R = relation order evd env b in 
        debug_string [`Relation] (Printf.sprintf "b has cast : %b" (has_cast b));
        debug_string [`Relation] (Printf.sprintf "b_R has cast : %b" (has_cast b_R));
        (* |G|, x1, x2, x_R, y1, y2 |- [y1,y2] in |b| *)
        let b_R = liftn order (2 * order + 2) b_R in 
        debug_string [`Relation] (Printf.sprintf "b_R lifted has cast : %b" (has_cast b_R));
        (* |G|, f1, f2, x1, x2, x_R, y1, y2 |- [y1,y2] in |b| *)
        let fxs = 
          fold_nat (fun k l -> 
            (mkApp (mkRel (order + k + 2), [| mkRel (k + 2) |]))::l) [] order 
        in (* |G|, f1, f2, x1, x2, x_R |- [f1 x1, f2 x2] *)
        let b_R = Vars.substl fxs b_R in 
        debug_string [`Relation] (Printf.sprintf "b_R subste has cast : %b" (has_cast b_R));
        (* |G|, f1, f2, x_1, x_2, x_R |- [f1 x1, f2 x2] in |b| *) 
        let x_R = translate_name order x in 
        let prods = range (fun k -> 
          (prime_name order k x, 
           lift (order + k) (prime order k a))) order in
        compose_prod prods (mkProd (x_R, a_R, b_R)) 
        (* |G|, f1, f2 |- forall x_1, x_2, x_R, [f1 x1, f2 x2] in |b| *)
    | _ ->
        let t_R = translate order evd env t in 
        debug_string [`Relation] (Printf.sprintf "t_R has cast : %b" (has_cast t_R));
        let t_R = lift order t_R in 
        debug_string [`Relation] (Printf.sprintf "t_R lifted has cast : %b" (has_cast t_R));
        apply_head_variables t_R order
  in 
 if !debug_mode && List.exists (fun x -> List.mem x [`Relation]) debug_flag then begin
    debug_string [`Relation] (Printf.sprintf "exit relation %d evd env t" order);
    debug_evar_map [`Relation]  "evd =" !evd; 
    debug [`Relation] "input =" env !evd t;
    debug_string [`Relation] (Printf.sprintf "input has cast : %b" (has_cast t));
    debug_mode := false;
    let env_R = translate_env order evd env in 
    let lams = range (fun k -> (Anonymous, None, lift k (prime order k t))) order in
    let env_R = Environ.push_rel_context lams env_R in
    debug_mode := true;
    debug [`Relation] "output =" env_R !evd res;
    debug_string [`Relation] (Printf.sprintf "output has cast : %b" (has_cast res))
  end;
  res


(* G |- t ---> |G| |- |t| *)
and translate order evd env (t : constr) : constr = 
  debug_string [`Translate] (Printf.sprintf "translate %d evd env t" order);
  debug_evar_map [`Translate]  "evd =" !evd; 
  debug [`Translate] "input =" env !evd t;
  let res = match kind t with
    | Rel n -> mkRel ( (n - 1) * (order + 1) + 1)
    
    | Sort _ | Prod (_,_,_) -> 
        (* [..., _ : t'', _ : t', _ : t] *)
        let lams = range (fun k -> (Anonymous, lift k (prime order k t))) order in
        compose_lam lams (relation order evd env t) 
    
    | App (c,l) -> 
        let l = List.rev (Array.to_list l) in
        let l_R = List.flatten (List.map (fun x -> 
           (translate order evd env x)::
           (range (fun k -> prime order k x) order)) l) in
        applist (translate order evd env c, List.rev l_R)

    | Var i -> translate_variable order evd env i
    | Meta n -> not_implemented ~reason:"meta" env !evd t
    | Cast (c, k, t) ->
        let c_R = translate order evd env c in 
        let t_R = relation order evd env t in
        let sub = range (fun k -> prime order k c) order in 
        let t_R = substl sub t_R in
        mkCast (c_R, k, t_R)
 
    | Lambda (x, a, m) -> 
        let lams = range (fun k -> 
          (prime_name order k x, lift k (prime order k a))) order 
        in
        let x_R = translate_name order x in 
        let a_R = relation order evd env a in
        let env = push_rel (x, None, a) env in
        compose_lam lams (mkLambda (x_R, a_R, translate order evd env m))
 
    | LetIn (x, b, t, c) -> 
        fold_nat (fun k acc ->
           mkLetIn (prime_name order k x, lift k (prime order k b), lift k (prime order k t), acc))
           (mkLetIn (translate_name order x, lift order (translate order evd env b), relation order evd env t, 
            let env = push_rel (x, Some b, t) env in
            translate order evd env c)) order       

    | Const c -> 
        translate_constant order evd env c
 
    | Fix _ ->  
        translate_fix order evd env t
 
    | Ind indu -> translate_inductive order env evd indu
 
    | Construct cstru -> translate_constructor order env evd cstru
 
    | Case (ci , p, c, bl) -> 
        let nargs, nparams = Inductiveops.inductive_nrealargs ci.ci_ind, Inductiveops.inductive_nparams ci.ci_ind in
        let theta = mkCase (ci, lift (nargs + 1) p, mkRel 1, Array.map (lift (nargs + 1)) bl) in
        debug_case_info [`Case] ci;
        debug [`Case] "theta (in translated env) = " Environ.empty_env !evd theta;
        debug_string [`Case] (Printf.sprintf "nargs = %d, params = %d" nargs nparams); 
        let ci_R = translate_case_info order env ci in
        debug_case_info [`Case] ci_R;
        debug [`Case] "p:" env !evd p;
        let lams, t = decompose_lam_n_assum (nargs + 1) p in 
        let env_lams = Environ.push_rel_context lams env in 
        debug [`Case] "t:" env_lams !evd t;
        let t_R = relation order evd env_lams t in
        debug [`Case] "t_R:" Environ.empty_env !evd t_R;
        let sub = range (fun k -> prime order k theta) order in 
        debug_string [`Case] "substitution :"; List.iter (debug [`Case] "" Environ.empty_env !evd) sub;
        let t_R = substl sub t_R in 
        debug [`Case] "t_R" Environ.empty_env !evd t_R;
        let lams_R =  translate_rel_context order evd env lams in
        let p_R = compose_lam_assum lams_R t_R in
        let c_R = translate order evd env c in 
        let bl_R = Array.map (translate order evd env) bl in 
        let tuple = (ci_R, p_R, c_R, bl_R) in 
        mkCase tuple
   
    | CoFix _ -> 
        translate_cofix order evd env t
   
    | _ -> not_implemented ~reason:"trapfall" env !evd t
 in  
  if !debug_mode && List.exists (fun x -> List.mem x [`Translate]) debug_flag then begin
    debug_string [`Translate] (Printf.sprintf "exit translate %d evd env t" order);
    debug_evar_map [`Translate]  "evd =" !evd; 
    debug [`Translate] "input =" env !evd t;
    debug_string [`Translate] (Printf.sprintf "input has cast : %b" (has_cast t));
    debug_mode := false;
    let env_R = translate_env order evd env in 
    debug_mode := true;
    debug [`Translate] "output =" env_R !evd res;
    debug_string [`Translate] (Printf.sprintf "output has cast : %b" (has_cast res))
  end;
  res

and translate_constant order (evd : Evd.evar_map ref) env cst : constr =
  try 
   let cst, names = cst in 
   let evd', constr = Evd.fresh_global ~rigid:Evd.univ_rigid ~names env !evd (Relations.get_constant order cst) in 
   evd := evd';
   constr
  with Not_found -> 
      let (kn, u) = cst in 
      let cb = lookup_constant kn env in 
      Declarations.(match cb.const_body with 
        | Def _ -> 
            let (value, constraints) = Environ.constant_value env cst in 
            let evd' = Evd.add_constraints !evd constraints in
            evd := evd';
            translate order evd env value
        | OpaqueDef op -> 
            let table = Environ.opaque_tables env in 
            let typ = Typeops.type_of_constant_in env cst in
            let cte_constraints = Declareops.constraints_of_constant table cb in
            let cte_constraints = Univ.subst_instance_constraints u cte_constraints in
            let evd' = Evd.add_constraints !evd cte_constraints in
            evd := evd';
            let fold = mkConstU cst in 
            let def = Opaqueproof.force_proof table op in
            let _ = Opaqueproof.force_constraints table op in 
            let u = snd cst in 
            let def = subst_instance_constr u def in
            let pred = mkLambda (Anonymous, typ, substl (range (fun _ -> mkRel 1) order) (relation order evd env typ)) in
            let res = translate order evd env def in
            let uf_opaque_stmt = CoqConstants.eq evd [| typ; def; fold|] in 
            let sort = Typing.sort_of env evd typ in
            let proof_opaque = 
              try 
                if is_prop_sort sort then 
                  (debug [`ProofIrrelevance] "def =" env !evd def;
                  debug [`ProofIrrelevance] "fold =" env !evd fold;
                  CoqConstants.proof_irrelevance evd [| typ; def; fold |])
                else 
                  raise Not_found
              with e -> 
                debug_string [`ProofIrrelevance] (Printexc.to_string e);
                let evd_, hole = Evarutil.new_evar Environ.empty_env !evd uf_opaque_stmt in evd := evd_; 
                CoqConstants.add_constraints evd (mkSort sort);
                 hole
            in 
            CoqConstants.transport evd [| typ; def; pred; res; fold; proof_opaque |]
        | _ -> 
            error 
              (Pp.str (Printf.sprintf "The constant '%s' has no registered translation." 
    (KerName.to_string (Constant.user (fst cst))))))

and translate_rel_context order evd env rc =
  let _, (ll : rel_context list) = Context.fold_rel_context (fun decl (env, acc) -> 
     let (x, def, typ) = decl in 
     let x_R = translate_name order x in 
     let def_R = Option.map (translate order evd env) def in 
     let typ_R = relation order evd env typ in 
     let l : rel_context = range (fun k -> 
       (prime_name order k x, 
        Option.map (fun x -> lift k (prime order k x)) def, 
        lift k (prime order k typ))) order
     in
     let env = push_rel decl env in 
     env, (((x_R, Option.map (lift order) def_R, typ_R)::l))::acc) ~init:(env, []) rc
  in 
  List.flatten ll


and translate_variable order evd env v : constr =
  try 
    Constr.mkConst (Relations.get_variable order v)
  with Not_found -> 
    error 
      (Pp.str (Printf.sprintf "The variable '%s' has no registered translation, provide one with the Realizer command." (Names.Id.to_string v)))
and translate_inductive order env evdr (ind, names) =
  try 
   let evd, constr = Evd.fresh_global ~rigid:Evd.univ_rigid ~names env !evdr (Relations.get_inductive order ind) in 
   evdr := evd;
   constr
  with Not_found -> error (Pp.str (Printf.sprintf "The inductive '%s' has no registered translation." 
    (KerName.to_string (MutInd.user (fst ind)))))

and translate_constructor order env evdr ((ind, i), u) = 
  let (ind, u) = destInd (translate_inductive order env evdr (ind,u)) in 
  mkConstructU ((ind, i), u)

and translate_case_info order env ci = 
  { 
    ci_ind = Globnames.destIndRef (Relations.get_inductive order ci.ci_ind);
    ci_npar = (order + 1) * ci.ci_npar;
    ci_cstr_ndecls = Array.map (fun x -> (order + 1) * x) ci.ci_cstr_ndecls;
    ci_cstr_nargs = Array.map (fun x -> (order + 1) * x) ci.ci_cstr_nargs;
    ci_pp_info = translate_case_printing order env ci.ci_pp_info;
  }

and translate_case_printing order env cp = 
  let translate_bool_list l =  
    List.flatten (List.map (fun x -> range (fun _ -> x) (order + 1)) l) 
  in
  { 
    ind_tags = (range (fun _ -> false) order) @ translate_bool_list cp.ind_tags;
    cstr_tags = Array.map translate_bool_list cp.cstr_tags;
    style = translate_style cp.style }

and translate_style x = x

and translate_cofix order evd env t = 
  let (index, (lna, tl, bl)) as fix = destCoFix t in
  let nfun = Array.length lna in
  let rec letfix name fix typ n k acc =
    if k = 0 then acc 
    else 
      let k = k-1 in 
      let fix_k = lift (n*order + k) (prime order k fix) in 
      let typ_k = lift (n*order + k) (prime order k typ) in 
      let acc = mkLetIn (Name (id_of_string (Printf.sprintf "fix_%s_%d" name (k+1))),
                           fix_k, typ_k, acc) in  
      letfix name fix typ n k acc 
  in 
  let rec letfixs n acc = 
    if n = 0 then acc
    else 
      let n = n - 1 in 
      let name = 
        match lna.(n) with 
        | Name id ->  Names.Id.to_string id
        | _ -> string_of_int n
      in
      let fix = mkCoFix (index, (lna, tl, bl)) in 
      let typ = tl.(n) in 
      let acc = letfix name fix typ n order acc in 
      letfixs n acc
  in
  let nrealargs = Array.map (fun x -> rel_context_nhyps (fst (decompose_lam_assum x))) bl in     
  (* [lna_R] is the translation of names of each fixpoints. *)
  let lna_R = Array.map (translate_name order) lna in
  let ftbk_R = Array.mapi (fun i x -> 
    let narg = nrealargs.(i) in 
    let ft, bk = decompose_prod_n_assum_by_prod narg x in 
    let ft_R = translate_rel_context order evd env ft in
    let env_ft = push_rel_context ft env in 
    let bk_R = relation order evd env_ft bk in
     (ft, ft_R, bk, bk_R)) tl
  in
  let tl_R = Array.mapi (fun n (ft, ft_R, bk, bk_R) -> 
     (* bk_R is well-typed in | G, ft|, x_1 : bk_1, x_2 : bk_R *)
     (* we lift it to insert the [nfun * order] letins. *)
     let ft_R_len = rel_context_length ft_R in 
     let bk_R = liftn (nfun * order) (ft_R_len + order + 1) bk_R in 
     let sub = range (fun k -> 
                  mkApp (mkRel (ft_R_len + (nfun - n)*order - k ),
                     Array.map (prime order k) (Termops.extended_rel_vect 0 ft)))
               order 
     in 
     compose_prod_assum (Termops.lift_rel_context (nfun * order) ft_R) (substl sub bk_R)) ftbk_R
  in

  (* env_rec is the environement under fipoints. *)
  let env_rec = push_rec_types (lna, tl, bl) env in 
  (* n : fix index *)
  let process_body n = 
    let lams, body = decompose_lam_assum bl.(n) in 
    let env_lams = push_rel_context lams env_rec in
    let narg = rel_context_length lams in 
    let body_R = translate order evd env_lams body in 
    let (ft, ft_R, bk, bk_R) = ftbk_R.(n) in 
    let theta = mkApp (mkRel (nfun - n + narg), Termops.extended_rel_vect 0 lams) in
    (* lift to insert fixpoints variables before arguments 
     * plus possible letins that were not in the type.
     * *)
    let nfun_letins = nfun + narg - nrealargs.(n) in 
    let bk = liftn nfun_letins (narg + 1) bk in 
    let bk_R = liftn (nfun_letins * (order + 1)) ((order + 1) * narg + order + 1) bk_R in 
    (* narg is the position of fixpoints in env *)
    let body_R = rewrite_cofixpoints order evd env_lams narg fix body theta bk bk_R body_R in
    let lams_R = translate_rel_context order evd env_rec lams in 
    let res = compose_lam_assum lams_R body_R in 
    if List.exists (fun x -> List.mem x [`Fix]) debug_flag then begin
      let env_R = translate_env order evd env_rec in 
      debug [`Fix] "res = " env_R !evd res;
    end;
    res 
  in
  let bl_R = Array.init nfun process_body in 
  let bl_R = 
    (* example: if order = 2 and nfun = 3, then permut_sub is : [1;2;7;3;4;8;5;6;9] *)
    let suc_order = order + 1 in 
    let size_of_sub = suc_order * nfun in 
    let permut_sub = 
     let l = List.init size_of_sub (fun x -> if x mod suc_order <> 0 then nfun + x - x / suc_order else  1 + x / suc_order) in
     List.map mkRel l
    in 
    Array.map (fun x -> 
          let x = liftn size_of_sub (size_of_sub + 1) x in 
          substl permut_sub x) bl_R
  in 
  let res = mkCoFix (index, (lna_R, tl_R, bl_R)) in 
  let res = letfixs nfun res in
  if List.exists (fun x -> List.mem x [`Fix]) debug_flag then begin
    let env_R = translate_env order evd env in 
    debug [`Fix] "cofix res = " env_R !evd res;
  end;
  res



and translate_fix order evd env t = 
  let ((ri, i) as ln, (lna, tl, bl)) as fix = destFix t in
  let nfun = Array.length lna in
  let rec letfix name fix typ n k acc =
    if k = 0 then acc 
    else 
      let k = k-1 in 
      let fix_k = lift (n*order + k) (prime order k fix) in 
      let typ_k = lift (n*order + k) (prime order k typ) in 
      let acc = mkLetIn (Name (id_of_string (Printf.sprintf "fix_%s_%d" name (k+1))),
                           fix_k, typ_k, acc) in  
      letfix name fix typ n k acc 
  in 
  let rec letfixs n acc = 
    if n = 0 then acc
    else 
      let n = n - 1 in 
      let name = 
        match lna.(n) with 
        | Name id ->  Names.Id.to_string id
        | _ -> string_of_int n
      in
      let fix = mkFix ((ri, n), (lna, tl, bl)) in 
      let typ = tl.(n) in 
      let acc = letfix name fix typ n order acc in 
      letfixs n acc
  in
  let nrealargs = Array.map (fun x -> rel_context_nhyps (fst (decompose_lam_assum x))) bl in     
  (* [ln_R] is the translation of ln, the array of arguments for each fixpoints. *) 
  let ln_R = (Array.map (fun x -> x*(order + 1) + order) ri, i) in
  (* [lna_R] is the translation of names of each fixpoints. *)
  let lna_R = Array.map (translate_name order) lna in
  let ftbk_R = Array.mapi (fun i x -> 
    let narg = nrealargs.(i) in 
    let ft, bk = decompose_prod_n_assum_by_prod narg x in 
    let ft_R = translate_rel_context order evd env ft in
    let env_ft = push_rel_context ft env in 
    let bk_R = relation order evd env_ft bk in
     (ft, ft_R, bk, bk_R)) tl
  in
  let tl_R = Array.mapi (fun n (ft, ft_R, bk, bk_R) -> 
     (* bk_R is well-typed in | G, ft|, x_1 : bk_1, x_2 : bk_R *)
     (* we lift it to insert the [nfun * order] letins. *)
     let ft_R_len = rel_context_length ft_R in 
     let bk_R = liftn (nfun * order) (ft_R_len + order + 1) bk_R in 
     let sub = range (fun k -> 
                  mkApp (mkRel (ft_R_len + (nfun - n)*order - k ),
                     Array.map (prime order k) (Termops.extended_rel_vect 0 ft)))
               order 
     in 
     compose_prod_assum (Termops.lift_rel_context (nfun * order) ft_R) (substl sub bk_R)) ftbk_R
  in
  (* env_rec is the environement under fipoints. *)
  let env_rec = push_rec_types (lna, tl, bl) env in 
  (* n : fix index *)
  let process_body n = 
    let lams, body = decompose_lam_assum bl.(n) in 
    let narg = rel_context_length lams in 
    (* rec_arg gives the position of the recursive argument *)
    let rec_arg = narg - (fst ln).(n) in 
    let args = Termops.extended_rel_list 0 lams in
    let lams_R = translate_rel_context order evd env_rec lams in 
    let env_lams = push_rel_context lams env_rec in 

    let inst_args depth args = 
      mkApp (mkRel (depth + nfun - n + narg), Array.of_list args)
    in  
    (* we use this complicated function to translate the 
     * shallow cases just after a lambda (the goal is to 
     * avoid as much as possible rewriting). 
     * *)
    let rec traverse_cases env depth (args : constr list) typ typ_R term = 
      match kind term with 
        | Case (ci , p, c, branches) when test_admissible env c args p branches ->
            process_case env depth args term 
        | _ -> 
            (* otherwise we have to perform some rewriting. *)
            debug [`Fix] "c = " env !evd term;
            debug [`Fix] "typ = " env !evd typ;
            let term_R  = translate order evd env term in 
            let theta = inst_args depth args in 
            (* depth + narg is the position of fixpoints in env *)
            rewrite_fixpoints order evd env (depth + narg) fix term theta typ typ_R term_R

    and test_admissible env c args predicate branches = 
       isRel c && List.mem c args && Array.for_all (Vars.noccurn (destRel c)) branches && 
       let typ = Retyping.get_type_of env !evd c in 
       debug [`Fix] "typ = " env !evd typ;
       List.iteri (fun i x -> 
          debug [`Fix] (Printf.sprintf "args.(%d) = " i) env !evd x) args;
       let (ind, u), ind_args = Inductiveops.find_inductive env !evd typ in 
       let nparams = Inductiveops.inductive_nparams ind in 
       let _, realargs = List.chop nparams ind_args in 
       List.iteri (fun i x -> 
          debug [`Fix] (Printf.sprintf "realargs.(%d) = " i) env !evd x) realargs;
       List.for_all (fun x -> List.mem x args) realargs

    and process_case env depth (fun_args : constr list) case = 
        
        debug [`Fix] "case = " env !evd case;
        let (ci, p, c, bl) = destCase case in 
        debug [`Fix] "predicate = " env !evd p;
        let c_R = translate order evd env c in
        let ci_R = translate_case_info order env ci in 
        let c_typ = Retyping.get_type_of env !evd c in 
        debug [`Fix] "c_typ = " env !evd c_typ;
        let ((ind, u) as pind, params_args)  = 
          Inductiveops.find_inductive env !evd c_typ 
        in 
       let i_nargs, i_nparams = 
          Inductiveops.inductive_nrealargs ind, 
          Inductiveops.inductive_nparams ind 
        in
        let i_params, i_realargs = List.chop i_nparams params_args in 
        debug_string [`Fix] "make inductive family ...";
        let ind_fam = Inductiveops.make_ind_family (pind, i_params) in
        debug_string [`Fix] "get_constructors";
        let constructors = Inductiveops.get_constructors env ind_fam in 
        debug_string [`Fix] "done";
 
        assert (List.length i_realargs = i_nargs);
        let fun_args_i = 
          List.map (fun x -> if x = c then mkRel 1
                             else if List.mem x i_realargs then mkRel (2 + i_nargs - (List.index (=) x i_realargs))
                             else lift (i_nargs + 1) x) fun_args 
        in
        let theta = inst_args (depth + i_nargs + 1) fun_args_i in 
        let sub = range (fun k -> prime order k theta) order in 
        let lams, typ = decompose_lam_n_assum (i_nargs + 1) p in 
        debug [`Fix] "theta = " (push_rel_context lams env) !evd theta;
        debug [`Fix] "theta = " Environ.empty_env !evd theta;
        let lams_R = translate_rel_context order evd env lams in 
        let env_lams = Environ.push_rel_context lams env in 
        let typ_R = relation order evd env_lams typ in
        let p_R = substl sub typ_R in 
        let p_R = compose_lam_assum lams_R p_R in 
        debug [`Fix] "predicate_R = " Environ.empty_env !evd p_R;
        let bl_R = 
          debug_string [`Fix] (Printf.sprintf "dest_rel = %d" (destRel c));
          debug_string [`Fix] (Printf.sprintf "depth = %d" depth);
          debug_string [`Fix] (Printf.sprintf "barg = %d" narg);
          debug_string [`Fix] (Printf.sprintf "fst ln = %d" (fst ln).(n));
          debug_string [`Fix] (Printf.sprintf "rec_arg = %d" rec_arg);
          if (destRel c) = depth + rec_arg then 
            Array.map (translate order evd env) bl 
          else begin
            Array.mapi (fun i b ->
               let (cstr, u) as cstru = constructors.(i).Inductiveops.cs_cstr in 
               let pcstr = mkConstructU cstru in 
               let nrealdecls = Inductiveops.constructor_nrealdecls cstr in
               let realdecls, b = decompose_lam_n_assum nrealdecls b in
               let lifted_i_params = List.map (lift nrealdecls) i_params in 
               let instr_cstr = 
                 mkApp (pcstr, 
                        Array.of_list 
                         (List.append lifted_i_params 
                           (Termops.extended_rel_list 0 realdecls))) 
               in
               let concls = constructors.(i).Inductiveops.cs_concl_realargs in  
               assert (Array.length concls = i_nargs);
               let fun_args = 
                List.map (fun x -> if x = c then instr_cstr
                             else if List.mem x i_realargs then concls.(i_nargs - (List.index (=) x i_realargs))
                             else lift nrealdecls x) fun_args 
               in
               let realdecls_R = translate_rel_context order evd env realdecls in 
               let sub = instr_cstr::(List.rev (Array.to_list concls)) in 
               let typ = substl sub typ in 
               (* FIXME : translate twice here :*)
               let typ_R = relation order evd env_lams typ in
               let env = push_rel_context realdecls env in 
               let b_R = traverse_cases env (depth + nrealdecls) fun_args typ typ_R b in 
               compose_lam_assum realdecls_R b_R
            ) bl 
          end
        in 
        mkCase (ci_R, p_R, c_R, bl_R)
    in 
    let (_, ft_R, bk, bk_R) = ftbk_R.(n) in 
    let nfun_letins = nfun + narg - nrealargs.(n) in 
    (* lift to insert fixpoints variables before arguments 
     * plus possible letins that were not in the type.
     * *)
    let bk = liftn nfun_letins (narg + 1) bk in 
    let bk_R = liftn (nfun_letins * (order + 1)) ((order + 1) * narg + order + 1) bk_R in 
    let body_R = traverse_cases env_lams 0 args bk bk_R body in 
    let res = compose_lam_assum lams_R body_R in 
    if List.exists (fun x -> List.mem x [`Fix]) debug_flag then begin
      let env_R = translate_env order evd env_rec in 
      debug [`Fix] "res = " env_R !evd res;
    end;
    res 
  in
  let bl_R = Array.init nfun process_body in 
  let bl_R = 
    (* example: if order = 2 and nfun = 3, then permut_sub is : [1;2;7;3;4;8;5;6;9] *)
    let suc_order = order + 1 in 
    let size_of_sub = suc_order * nfun in 
    let permut_sub = 
     let l = List.init size_of_sub (fun x -> if x mod suc_order <> 0 then nfun + x - x / suc_order else  1 + x / suc_order) in
     List.map mkRel l
    in 
    Array.map (fun x -> 
          let x = liftn size_of_sub (size_of_sub + 1) x in 
          substl permut_sub x) bl_R
  in 
  let res = mkFix (ln_R, (lna_R, tl_R, bl_R)) in 
  letfixs nfun res 

(* for debugging only  *)
and translate_env order evdr env = 
  let init_env = Environ.reset_context env in 
  let rc = translate_rel_context order evdr init_env (Environ.rel_context env) in
  push_rel_context rc init_env

(* Γ ⊢ source : typ
 * Γ ⊢ target : typ
 * ⟦Γ⟧, typ₁, typ₂ ⊢ typ_R : Type 
 *
 * builds : 
 * 
 *
 * *)
and rewrite_fixpoints order evdr env (depth : int) (fix : fixpoint) source target typ typ_R acc =
  debug [`Fix] "source =" env !evdr source;
  debug [`Fix] "target =" env !evdr target;
  debug [`Fix] "typ =" env !evdr typ;
  if List.exists (fun x -> List.mem x [`Fix]) debug_flag then begin
    let env_R = translate_env order evdr env in 
    let rc_order = rev_range (fun k -> (Name (id_of_string (Printf.sprintf "rel_%d" k))), None, 
                         lift k (prime order k typ)) order in 
    let env_R = push_rel_context rc_order env_R in
    debug [`Fix] "typ_R =" env_R !evdr typ_R
  end;
  let instantiate_fixpoint_in_rel_context rc = 
    let (ri, k), stuff = fix in 
    let pos = depth in 
    let nfun = Array.length ri in 
    let front, back = List.chop pos rc in
    let funs, back = List.chop nfun back in 
    let fixs = List.mapi (fun i -> function (name, None, typ) -> 
      (name, Some (mkFix ((ri, nfun - 1 - i), stuff)), typ) | _ -> assert false) funs in 
    front @ fixs @ back
  in
  let env_rc = Environ.rel_context env in 
  let env_rc = instantiate_fixpoint_in_rel_context env_rc in 
  let path = CoqConstants.eq evdr [| typ; source; target|] in
  let gen_rc, new_vec, path = weaken_unused_free_rels env_rc path in  
  let gen_path = it_mkProd_or_LetIn path  gen_rc in 
  debug [`Fix] "gen_path_type" Environ.empty_env !evdr gen_path;
  let evd, hole = Evarutil.new_evar Environ.empty_env !evdr gen_path in 
  evdr := evd; 
  let let_gen acc = mkLetIn (Name (id_of_string "gen_path"), hole, gen_path, acc) in 
  let_gen @@ (fold_nat (fun k acc ->
    let pred_sub = 
      (range (fun x -> lift 1 (prime order (k+1+x) target)) (order-1 - k))
      @ [ mkRel 1 ] 
      @ (range (fun x -> lift 1 (prime order x source)) k)
    in
    let sort = Retyping.get_type_of env !evdr typ in
    CoqConstants.add_constraints evdr sort;
    let index = lift 1 (prime order k typ) in 
    let pred = mkLambda (Name (id_of_string "x"), index, liftn 1 2 (substl pred_sub (liftn 1 (order + 1) typ_R))) in 
    let base = lift 1 (prime order k source) in 
    let endpoint = lift 1 (prime order k target) in 
    let path = mkApp (mkRel 1, 
       Array.map (fun x -> lift 1 (prime order k x)) new_vec)
    in 
    CoqConstants.transport evdr
          [| index; 
             base; 
             pred; acc; endpoint; path |]) (lift 1 acc) order)

and weaken_unused_free_rels env_rc term = 
  (* Collect the dependencies with [vars] in a rel_context. *)
   let rec collect_free_vars k vars = function 
     | [] -> vars
     | decl::tl when Int.Set.mem k vars -> 
       let fv = 
          match decl with 
             (_, None, typ) -> 
               Termops.free_rels typ
           | (_, Some def, typ) -> 
               Int.Set.union (Termops.free_rels def) (Termops.free_rels typ)
       in
       let vars = Int.Set.fold (fun x -> Int.Set.add (x + k)) fv vars in
       collect_free_vars (k + 1) vars tl
    | _::tl ->  
       collect_free_vars (k + 1) vars tl
   in
   let rec apply_substitution_rel_context k sub acc = 
     function [] -> List.rev acc | decl :: tl when destRel (List.hd sub) > 0 -> 
       let sub = List.tl sub in 
       let decl = substl_decl (List.map (lift (-k)) sub) decl in 
       apply_substitution_rel_context (k + 1) sub (decl::acc) tl
     | _ :: tl -> 
       apply_substitution_rel_context k (List.tl sub) acc tl
   in 

   debug_rel_context [`Fix] "env_rv = " Environ.empty_env env_rc;
   let set = collect_free_vars 1 (Termops.free_rels term) env_rc in 
   let lst = Int.Set.fold (fun x acc -> x::acc) set [] in 
   let lst = List.sort Pervasives.compare lst in
   debug_string [`Fix] (Printf.sprintf "[%s]" (String.concat ";" (List.map string_of_int lst)));
   let rec dup n x acc = if n <= 0 then acc else dup (n-1) x (x::acc) in 
   let rec gen_sub min pos len acc = function
            [] -> dup (len - min) 0 acc 
    | hd :: tl -> 
        let n = hd - min - 1 in 
        let acc = pos::(dup n 0 acc) in 
        gen_sub hd (pos + 1) len acc tl
   in
   let sub_lst = List.rev (gen_sub 0 1 (List.length env_rc) [] lst) in
   debug_string [`Fix] (Printf.sprintf "[%s]" (String.concat ";" (List.map string_of_int sub_lst)));
   let sub = List.map mkRel sub_lst in
   let new_env_rc = apply_substitution_rel_context 1 sub [] env_rc in 
   let new_vec = Termops.extended_rel_list 0 env_rc in
   let new_vec = List.filter (fun x -> let v = destRel x in Int.Set.mem v set) new_vec in 
   let new_vec = Array.of_list new_vec in
   assert (Array.length new_vec == Context.rel_context_nhyps new_env_rc);
   new_env_rc, new_vec, substl sub term
   
and rewrite_cofixpoints order evdr env (depth : int) (fix : cofixpoint) source target typ typ_R acc =
  debug [`Fix] "source =" env !evdr source;
  debug [`Fix] "target =" env !evdr target;
  debug [`Fix] "typ =" env !evdr typ;
  if List.exists (fun x -> List.mem x [`Fix]) debug_flag then begin
    let env_R = translate_env order evdr env in 
    let rc_order = rev_range (fun k -> (Name (id_of_string (Printf.sprintf "rel_%d" k))), None, 
                         lift k (prime order k typ)) order in 
    let env_R = push_rel_context rc_order env_R in
    debug [`Fix] "typ_R =" env_R !evdr typ_R
  end;
  let instantiate_fixpoint_in_rel_context rc = 
    let index, ((lna, _, _) as stuff) = fix in 
    let pos = depth in 
    let nfun = Array.length lna in 
    let front, back = List.chop pos rc in
    let funs, back = List.chop nfun back in 
    let fixs = List.mapi (fun i -> function (name, None, typ) -> 
      (name, Some (mkCoFix ((nfun - 1 - index), stuff)), typ) | _ -> assert false) funs in 
    front @ fixs @ back
  in
  let env_rc = Environ.rel_context env in 
  let env_rc = instantiate_fixpoint_in_rel_context env_rc in 
  let gen_path = it_mkProd_or_LetIn (CoqConstants.eq evdr [| typ; source; target|]) env_rc in 
  debug [`Fix] "gen_path_type" env !evdr gen_path;
  let evd, hole = Evarutil.new_evar Environ.empty_env !evdr gen_path in 
  evdr := evd; 
  let let_gen acc = mkLetIn (Name (id_of_string "gen_path"), hole, gen_path, acc) in 
  let_gen @@ (fold_nat (fun k acc ->
    let pred_sub = 
      (range (fun x -> lift 1 (prime order (k+1+x) target)) (order-1 - k))
      @ [ mkRel 1 ] 
      @ (range (fun x -> lift 1 (prime order x source)) k)
    in
    let index = lift 1 (prime order k typ) in 
    let pred = mkLambda (Name (id_of_string "x"), index, liftn 1 2 (substl pred_sub (liftn 1 (order + 1) typ_R))) in 
    let base = lift 1 (prime order k source) in 
    let endpoint = lift 1 (prime order k target) in 
    let path = mkApp (mkRel 1, 
       Array.map (fun x -> lift 1 (prime order k x))
        (Termops.extended_rel_vect 0 env_rc)) 
    in 
    let sort = Retyping.get_type_of env !evdr typ in
    CoqConstants.add_constraints evdr sort;
    CoqConstants.transport evdr
          [| index; 
             base; 
             pred; acc; endpoint; path |]) (lift 1 acc) order)




open Entries
open Declarations

let map_local_entry f = function 
  | LocalDef c -> LocalDef (f c)
  | LocalAssum c -> LocalAssum (f c)

let constr_of_local_entry = function LocalDef c | LocalAssum c -> c 

(* Translation of inductives. *)

let rec translate_mind_body order evdr env kn b inst = 
  let env = push_context b.mind_universes env in

  debug_string [`Inductive] "computing envs ...";
  debug_evar_map [`Inductive] "translate_mind, evd = \n" !evdr;
  let envs = 
    let params = subst_instance_context inst b.mind_params_ctxt in
    let env_params = push_rel_context params env in
    let env_arities = 
      List.fold_left (fun env ind -> 
        let typename = ind.mind_typename in
        debug_string [`Inductive] (Printf.sprintf "Adding '%s' to the environement." (Names.Id.to_string typename));
        let full_arity, cst = 
           Inductive.constrained_type_of_inductive env ((b, ind), inst) 
        in 
        let env = Environ.push_rel (Names.Name typename, None, full_arity) env in 
        let env = Environ.add_constraints cst env in
        env
      ) env (Array.to_list b.mind_packets)
    in 
    let env_arities_params = push_rel_context params env_arities in
    (env_params, params, env_arities, env_arities_params)
  in 

  debug_string [`Inductive] "translatation of params ...";
  let mind_entry_params_R =
    translate_mind_param order evdr env (subst_instance_context inst b.mind_params_ctxt)
  in 
  debug_string [`Inductive] "translatation of inductive ...";
  let mind_entry_inds_R = 
    List.mapi 
      (fun i x -> translate_mind_inductive order evdr env (kn,i) b inst envs x) 
      (Array.to_list b.mind_packets)
  in
  debug_evar_map [`Inductive] "translate_mind, evd = \n" !evdr;
  let ctx = Evd.universe_context !evdr in
  let res = { 
    mind_entry_record = None;
    mind_entry_finite = b.mind_finite;
    mind_entry_params = mind_entry_params_R;
    mind_entry_inds = mind_entry_inds_R;
    mind_entry_polymorphic = b.mind_polymorphic;
    mind_entry_universes = ctx;
    mind_entry_private = b.mind_private
  } in
  Debug.debug_mutual_inductive_entry !evdr res; 
  res


and translate_mind_param order evd env (l : rel_context) = 
  let rec aux env acc = function 
     | [] -> acc
     | (x, (Some def as op), hd)::tl -> 
       let x_R = (translate_name order x, LocalDef (translate order evd env def)) in  
       let env = push_rel (x, op, hd) env in
       let x_i = range (fun k -> 
                 (prime_name order k x, LocalDef (lift k (prime order k def)))) order in 
       let acc = (x_R::x_i):: acc in
       aux env acc tl  
     | (x,None,hd)::tl -> 
           let x_R = (translate_name order x, LocalAssum (relation order evd env hd)) in  
           let env = push_rel (x, None, hd) env in
           let x_i = range (fun k -> 
                     (prime_name order k x, LocalAssum (lift k (prime order k hd)))) order in 
           let acc = (x_R::x_i):: acc in
           aux env acc tl  
  in 
  let l = List.rev l in
  List.map (function (Name x,c) -> (x, c) | _ -> failwith "anonymous param") (List.flatten (aux env [] l))

and translate_mind_inductive order evdr env ikn mut_entry inst (env_params, params, env_arities, env_arities_params) e = 
  let typename = e.mind_typename in
  let p = List.length mut_entry.mind_params_ctxt in
  Debug.debug_string [`Inductive] (Printf.sprintf "mind_nparams = %d" mut_entry.mind_nparams); 
  Debug.debug_string [`Inductive] (Printf.sprintf "mind_nparams_rec = %d" p); 
  Debug.debug_string [`Inductive] (Printf.sprintf "mind_nparams_ctxt = %d" (List.length mut_entry.mind_params_ctxt)); 
  let _, arity = 
     decompose_prod_n_assum p (Inductive.type_of_inductive env ((mut_entry, e), inst))
  in
  debug [`Inductive] "Arity:" env_params !evdr arity;
  let arity_R = 
      debug_string [`Inductive] "Computing arity";
      let arity_R = relation order evdr env_params arity in
      let inds = List.rev (fold_nat 
         (fun k acc -> 
           prime order k 
            (apply_head_variables_ctxt (mkIndU (ikn, inst)) params)::acc) [] order) in 
      debug_string [`Inductive] "Substitution:";
      List.iter (debug [`Inductive] "" Environ.empty_env Evd.empty) inds;
      let result = substl inds arity_R in 
      if List.exists (fun x -> List.mem x [`Inductive]) debug_flag then begin
        let env_params_R = translate_env order evdr env_params in      
        debug [`Inductive] "Arity_R after substitution:" env_params_R !evdr result;
      end;
      result
  in
  { 
    mind_entry_typename = translate_id order typename;
    mind_entry_arity = arity_R;
    mind_entry_template = (match e.mind_arity with TemplateArity _ -> true | _ -> false);
    mind_entry_consnames = List.map (translate_id order) (Array.to_list e.mind_consnames);
    mind_entry_lc = 
      begin
        debug_string [`Inductive] "Computing constructors";
        let l = Array.to_list e.mind_user_lc in
        let l = List.map (subst_instance_constr inst) l in
        debug_string [`Inductive] "before translation :";
        List.iter (debug [`Inductive] "" env_arities !evdr) l;
        let l =  List.map (fun x -> snd (decompose_prod_n_assum p x)) l in
        debug_string [`Inductive] "remove uniform parameters :";
        List.iter (debug [`Inductive] "" env_arities_params !evdr) l;
        (*
        let sub = range (fun k -> mkRel (mut_entry.mind_nparams_rec + k + 1)) mut_entry.mind_nparams_rec in
        let l = List.map (substl sub) l in 
        debug_string "reverse parameters and inductive variables :"; 
        List.map (debug Environ.empty_env) l;*)
        let l = List.map (relation order evdr env_arities_params) l in
        let for_each_constructor k =
          (* Elements Ti of l are defined in the translation of the context : 
            *   [A'1;...;A'n;x1:X1;...;xn:Xp] 
            * augmented with 
            *   y_1 : Ti_1, y_2 : Ti_2
            * which is 
            *   [A'1_1; A'1_2; A'1_R;...;A'n_1;A'n_2;A'n_R;x1_1:X1_1; x1_2:X1_2, x1_R : ...] 
            *
            * We then replace the variables A'i_j by the original inductive and we let the
            * A'1_R and the xi_j untouched. Finally we subtitue all the y_i by constructors.
            *
            *
            * Therefore the substitution is the reverse list of : 
            *  [I1, I1, Rel , 
            *   ..., 
            *   Ip, Ip, Rel, 
            *   Rel , Rel , Rel ,
            *   ... 
            *   Rel , Rel , Rel , 
            *   mkConstruct Cil, mkConstruct Cil ]
            * *) 
          let n = Array.length mut_entry.mind_packets in 
          let (kn, i) = ikn in 
          let first_part = List.flatten (range (fun k -> 
            let k' = n-1-k in 
            (mkRel ((order + 1)*p + k'+1))::(range (fun _ -> mkIndU ((kn, k), inst)) order)) n)
          in
          let second_part = List.flatten @@ List.rev @@ (List.map List.rev) (range (fun k -> 
            (mkRel ((order + 1)*(k+1)))::(range (fun i -> mkRel ((order + 1)*k + i + 1)) order)) p)
          in
          debug_string [`Inductive] (Printf.sprintf "constructor n°%d" k);
          let third_part = range (fun m -> prime order m (apply_head_variables_ctxt (mkConstructU  ((ikn, k + 1), inst)) params)) order in 
          let final_substitution = third_part @ second_part @ (first_part) in
          debug_string [`Inductive] "substitution :";
          List.iter (debug [`Inductive] "" Environ.empty_env Evd.empty) final_substitution;
          substl final_substitution 
        in
        debug_string [`Inductive] "before substitution:";
        List.iter (debug [`Inductive] "" Environ.empty_env Evd.empty) l;
        let result = List.mapi for_each_constructor l in 
        debug_string [`Inductive] "after substitution:";
        List.iter (debug [`Inductive] "" Environ.empty_env Evd.empty) result;
        result
      end
  }


