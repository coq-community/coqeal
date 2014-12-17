open Term
open Names
open Vars
open Constr
open Environ
open Util
open Context
open Environ

let error msg = 
  raise (Errors.UserError ("Parametricity plugin", msg))

module CoqConstants = struct
  let msg = "parametricity: unable to fetch constants"
  
  let eq evdref args = 
    Program.papp evdref (fun () -> Coqlib.coq_reference msg ["Init"; "Logic"] "eq") args 
  
  let eq_refl evdref args = 
    Program.papp evdref (fun () -> Coqlib.coq_reference msg ["Init"; "Logic"] "eq_refl") args 

  let transport evdref args = 
    Program.papp evdref (fun () -> Coqlib.coq_reference msg ["Init"; "Logic"] "eq_rect") args 

  let proof_irrelevance evdref args = 
    Program.papp evdref (fun () -> Coqlib.coq_reference msg ["Logic"; "ProofIrrelevance"] "proof_irrelevance") args 
end


let all = [`ProofIrrelevance; 
           `Abstraction; 
           `Relation; 
           `Translate; 
           `Fix; 
           `Case; 
           `GenericUnfolding; 
           `Unfolding; 
           `Inductive; 
           `Module; 
           `Realizer]
let debug_flag = []

let default_arity = 2

let debug_message flags s e = 
  if List.exists (fun x -> List.mem x flags) debug_flag then
    Pp.msg_notice Pp.(str s ++ e)

let debug_env flags (s : string) env evd = 
  if List.exists (fun x -> List.mem x flags) debug_flag then
    Pp.(msg_notice (str s ++ Printer.pr_context_of env evd)) 

let debug flags (s : string) env evd c = 
  if List.exists (fun x -> List.mem x flags) debug_flag then 
    try 
      Pp.(msg_notice (str s
       ++ Printer.pr_context_of env evd));
      Pp.(msg_notice (str "" 
         ++ str "\n |-"
         ++ Printer.safe_pr_constr_env env evd c)) 
    with e -> Pp.(msg_notice (str (Printf.sprintf "Caught exception while debugging '%s'" (Printexc.to_string e))))

let debug_evar_map flags s evd = 
  if List.exists (fun x -> List.mem x flags) debug_flag then (
    Pp.msg_info Pp.(str s ++ Evd.pr_evar_universe_context (Evd.evar_universe_context evd)))

let debug_string flags s =
  if List.exists (fun x -> List.mem x flags) debug_flag then
    Pp.msg_notice (Pp.str ("--->\t"^s))

let debug_case_info flags ci = 
  if List.exists (fun x -> List.mem x flags) debug_flag then
    let (ind, k) = ci.ci_ind in 
    let ind_string = Printf.sprintf "%s[%d]" (MutInd.to_string ind) k in 
    let param = ci.ci_npar in 
    let ndecls = String.concat ";" (List.map string_of_int (Array.to_list ci.ci_cstr_ndecls)) in 
    let nargs = String.concat ";" (List.map string_of_int (Array.to_list ci.ci_cstr_nargs)) in 
    let pp_info x =
      let ind_tags = String.concat ";" (List.map string_of_bool x.ind_tags) in  
      let cstr_tags = 
        String.concat "," (List.map (fun tags -> String.concat ";" (List.map string_of_bool tags)) 
        (Array.to_list x.cstr_tags))
      in  
      let string_of_style = match x.style with 
        LetStyle -> "LetStyle" | IfStyle -> "IfStyle" | LetPatternStyle -> "LetPatternStyle" | MatchStyle -> "MatchStyle" | RegularStyle -> "RegularStyle" 
      in
      Printf.sprintf "ind_tags = %s, cstr_tags = %s, style = %s" ind_tags cstr_tags string_of_style
    in 
    debug_string flags
  (Printf.sprintf "CASEINFO:inductive = %s.\nparam = %d.\nndecls = %s.\nnargs = %s.\npp_info = %s\n.EOFCASEINFO"
      ind_string
      param
      ndecls
      nargs 
      (pp_info ci.ci_pp_info))

let debug_rel_context flags s env l = 
  if List.exists (fun x -> List.mem x flags) debug_flag then
    Pp.msg_notice Pp.(str s ++ (Termops.print_rel_context (push_rel_context l env)))

let not_implemented ?(reason = "no reason") env evd t = 
  debug [`Not_implemented] (Printf.sprintf "not implemented (%s):" reason) env evd t;
  failwith "not_implemented"

let hyps_from_rel_context env = 
  let rctx = Environ.rel_context env in 
  let rec aux acc depth = function 
      [] -> acc
    | (_, None, _) :: tl -> aux (depth :: acc) (depth + 1) tl
    | _ :: tl -> aux acc (depth + 1) tl 
  in 
  aux [] 1 rctx 

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

(* the iterator for natural numbers. *)
let fold_nat f x = 
  let rec aux acc n =
    if n = 0 then acc else
      let n = n - 1 in 
      aux (f n acc) n
  in aux x 

(* [first n l] returns the first [n] elements of [l]. *)
let firsts n l = 
  let rec aux n acc l = 
    if n > 0 then 
      match l with 
       | [] -> failwith "firsts"
       | hd::tl -> aux (n - 1) (hd :: acc) tl
    else 
      List.rev acc
  in aux n [] l

(* If [t] is well-defined in G, x1, ..., xn, [apply_head_variables t n] returns 
 * (t x1 ... xn) *)
let apply_head_variables t n = 
  let l = fold_nat (fun k l -> (mkRel (k + 1))::l) [] n in 
  mkApp (t, Array.of_list (List.rev l))

(* Substitution in a signature. *)
let substnl_rel_context subst n sign =
  let rec aux n = function
  | d::sign -> substnl_decl subst n d :: aux (n+1) sign
  | [] -> []
  in List.rev (aux n (List.rev sign))

let substl_rel_context subst = substnl_rel_context subst 0


(* unfold the given fixpoint. *)
let unfold_fixpoint env (t : constr) : constr = 
  match kind t with 
    | Fix ((ri, i),(lna, tl, bl)) -> 
        let nfun = Array.length lna in 
        let friends k = mkFix ((ri, k), (lna, tl, bl)) in 
        let sub = range friends nfun in 
        substl sub bl.(i)
    | _ -> failwith "unfold_fixpoint: expects a fixpoint"

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

(* Returns the statement : 
  *  forall x1 ... xn x, (fix f x1 ... xn x := F) x1 ... xn x = F[f/fix f x1 ... xn x := F] 
  * *)
let rec unfold_fixpoint_statement evdref (env : Environ.env) (t : constr) : types =
  match kind t with 
    | Fix ((ri, i), (lna, tl, bl)) -> 
        let narg = ri.(i) + 1 in 
        let cty = tl.(i) in
        debug [`Unfolding] (Printf.sprintf "narg = %d\n" narg) env !evdref cty;
        let front, typ = decompose_prod_n narg cty in 
        let appvars = Array.of_list (range (fun n -> mkRel (n+1)) narg) in 
        let unfolded = unfold_fixpoint env t in 
        let concl = 
          CoqConstants.eq evdref [| typ; mkBetaApp (lift narg unfolded, appvars); mkApp (lift narg t, appvars) |] 
        in
        let res = compose_prod front concl in 
        debug [`Unfolding] "concl + front" env !evdref res;
        let res = generalize_env env res in 
        debug [`Unfolding] "generalize" Environ.empty_env !evdref res;
        res
    | _ -> failwith "unfold_fixpoint_statement: expects a fixpoint"

(* Tries to find a proof of the previous "unfolding statement". 
 * Should work if (and only if ?) the fixpoint as the following 
 * form: 
 * fix f x1 ... xn a1 ... an (x : I P1 ... Pp a1 ... an). F 
 * where I is an inductive with p parameters and n arguments. 
 * The arguments of I are instantiated with unconstrained free variables. 
 * This is enough to translate all induction schemes, which are always
 * of this form. 
 * 
 * Note: that there are fixpoints that may not be proved to be 
 * extensionally equal to their unfolding. For instance, the 
 * following constant fixpoint structurally recursive on a 
 * non-contractible path: 
 * phi := fix A (f : A -> A) (x : A) (p : f x = x) := 0
 *
 * There is no (axiom free) proof that : 
 *   forall A f x p, phi A f x p = 0. 
 * *)
let rec unfold_fixpoint_proof (env : Environ.env) t : constr = 
  match kind t with 
    | Fix ((ri, i), (lna, tl, bl)) -> 
        let evdref = ref Evd.empty in 
        let narg = ri.(i) + 1 in 
        let cty = tl.(i) in
        let front, typ = decompose_prod_n_assum narg cty in
        let env' = Environ.push_rel_context front env in  
        let (_, _, struct_arg), front' = List.hd front, List.tl front in 
        let appvars = Array.of_list (range (fun n -> mkRel (n+1)) narg) in 
        let unfolded = unfold_fixpoint env t in 
        let base_point = mkBetaApp (lift narg unfolded, appvars) in 
        let end_point =  mkApp (lift narg t, appvars) in 
        let concl = CoqConstants.eq evdref [| typ; base_point; end_point |] in 
        let (ind, _) as pind, args = Inductive.find_inductive env' struct_arg in
        let param = firsts (Inductiveops.inductive_nparams ind) args in
        let ind_fam = Inductiveops.make_ind_family (pind, param) in 
        let ci = Inductiveops.make_case_info env' ind RegularStyle in 

        let constructors = Inductiveops.get_constructors env' ind_fam in 
        let realargs_and_struct = Inductiveops.inductive_nrealargs ind + 1 in 
        let return_type = 
          lift realargs_and_struct (it_mkLambda_or_LetIn concl (firsts realargs_and_struct front)) 
        in
        let build_branch env evdr k = 
          let summary = constructors.(k) in 
          List.iter (debug [`GenericUnfolding] "params" Environ.empty_env Evd.empty) summary.Inductiveops.cs_params;
          let constructor_args = Termops.lift_rel_context 1 Inductiveops.(summary.cs_args) in 
          debug_rel_context [`GenericUnfolding] "arguments of contructors:" env constructor_args;
          let env' = Environ.push_rel_context constructor_args env in 
          let evd = !evdr in
          let hole1, hole2, evd = 
            let evd, sort = Evarutil.new_Type env' evd in 
            let evd, type_hole = Evarutil.new_evar env' evd sort in 
            let evd, term_hole = Evarutil.new_evar env' evd type_hole in 
            type_hole, term_hole, evd
          in
          evdr := evd;
          let refl = 
              CoqConstants.eq_refl evdr [| hole1; hole2 |]
          in
          let res = it_mkLambda_or_LetIn refl constructor_args in
          debug [`GenericUnfolding] (Printf.sprintf "branch %d" k) env !evdr res; res
        in  
        let branches = Array.init (Array.length constructors) (build_branch env' evdref) in 
        let res = mkCase (ci, return_type,  mkRel 1, branches) in
        let res = it_mkLambda_or_LetIn res front in
        let evd = !evdref in 
        debug  [`GenericUnfolding] "proof of unfolding:" env evd res;
        debug_evar_map [`GenericUnfolding] "evar before typing" evd;
        let evd, _ = try
            Typing.e_type_of env evd res 
          with Type_errors.TypeError (env, err) ->
            let msg = Himsg.explain_type_error env evd err in 
            debug_message [`GenericUnfolding] "exception caught : " msg;
            raise Not_found
        in 
        debug_evar_map [`GenericUnfolding] "evar after typing" evd;
        let evd = Pretyping.solve_remaining_evars Pretyping.all_and_fail_flags env evd (Evd.empty, evd) in 
        let res = Evarutil.flush_and_check_evars evd res in 
        let evd = Evd.empty in 
        debug  [`GenericUnfolding] "proof of unfolding in env:" env !evdref res;
        let res = abstract_env env res in
        let env = Environ.empty_env in
        debug [`GenericUnfolding] "result after normalization" env evd res;
        res

    | Lambda (x, a, m) -> 
        let env = push_rel (x, None, a) env in 
        unfold_fixpoint_proof env m
   
    | Const cst ->  
        let cval = Environ.constant_value_in env cst in 
        unfold_fixpoint_proof env cval
   
    | _ -> failwith "unfold_fixpoint_proof: expects a fixpoint"


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
  match kind t with 
    | Sort s -> fold_nat (fun _ -> mkArrow (mkRel order)) (prop_or_type env evd t) order
    | Prod (x, a, b) ->
        let a_R = relation order evd env a in 
        (* |G|, x1, x2 |- [x1,x2] in |a| *)
        let a_R = liftn order (order + 1) a_R in 
        (*|G|, f1, f2, x1, x2 |- [x1,x2] in |a| *)
        let env = push_rel (x, None, a) env in 
        let b_R = relation order evd env b in 
        (* |G|, x1, x2, x_R, y1, y2 |- [y1,y2] in |b| *)
        let b_R = liftn order (2 * order + 2) b_R in 
        (* |G|, f1, f2, x1, x2, x_R, y1, y2 |- [y1,y2] in |b| *)
        let fxs = 
          fold_nat (fun k l -> 
            (mkApp (mkRel (order + k + 2), [| mkRel (k + 2) |]))::l) [] order 
        in (* |G|, f1, f2, x1, x2, x_R |- [f1 x1, f2 x2] *)
        let b_R = Vars.substl fxs b_R in 
        (* |G|, f1, f2, x_1, x_2, x_R |- [f1 x1, f2 x2] in |b| *) 
        let x_R = translate_name order x in 
        let prods = range (fun k -> 
          (prime_name order k x, 
           lift (order + k) (prime order k a))) order in
        compose_prod prods (mkProd (x_R, a_R, b_R)) 
        (* |G|, f1, f2 |- forall x_1, x_2, x_R, [f1 x1, f2 x2] in |b| *)
    | _ ->
        apply_head_variables (lift order (translate order evd env t)) order

(* G |- t ---> |G| |- |t| *)
and translate order evd env (t : constr) : constr = 
  debug_string [`Translate] (Printf.sprintf "translate %d evd env t" order);
  debug_evar_map [`Translate]  "evd =" !evd; 
  debug [`Translate] "input =" env !evd t;
  match kind t with
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
 
    | Ind (ind, u) -> mkFreshInd env evd (translate_inductive order env ind)
    | Construct (cstr, u) -> mkFreshConstruct env evd (translate_constructor order env cstr)
 
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
        let lams_R = List.flatten (List.map 
         (function (x, None, c) -> 
            (translate_name order x, relation order evd env c)::
              (range (fun k -> (prime_name order k x, lift k (prime order k c))) order)
          | _ -> failwith "parametricity: definition in pattern matching.") lams) 
        in
        debug_string [`Case] "lams_R :";
        List.iter (fun (x, c) -> debug [`Case] "" Environ.empty_env Evd.empty c) lams_R;
        let p_R = compose_lam lams_R t_R in
        let c_R = translate order evd env c in 
        let bl_R = Array.map (translate order evd env) bl in 
        let tuple = (ci_R, p_R, c_R, bl_R) in 
        mkCase tuple
   
    | Fix ((ri, i) as ln ,(lna, tl, bl)) -> 
        let print_fix (ri, i) lna tl bl =
          debug_string [`Fix] (Printf.sprintf "index = %d" i);
          debug_string [`Fix] (Printf.sprintf "recindxs = %s"
            (String.concat ";" (List.map string_of_int (Array.to_list ri))));
          debug_string [`Fix] "typearray =";
          Array.iter (debug [`Fix] "" Environ.empty_env Evd.empty) tl;
          debug_string [`Fix] "body =";
          Array.iter (debug [`Fix] "" Environ.empty_env Evd.empty) bl
        in
        print_fix ln lna tl bl;
        (* [nfun] is the number of function defined in the fixpoint. *)
        let nfun = Array.length lna in
        (* [ln_R] is the translation of ln, the array of arguments for each fixpoints. *) 
        let ln_R = (Array.map (fun x -> x*(order + 1) + order) ri, i) in
        (* [lna_R] is the translation of names of each fixpoints. *)
        let lna_R = Array.map (translate_name order) lna in
        (* [friends k] returns the k-th original fixpoint. *)
        let friends k = mkFix ((ri, k), (lna, tl, bl)) in 
        (* TODO : explain that *)
        let tl_relation = Array.mapi (fun i x -> 
           let narg = (fst ln).(i) + 1 in 
           let narg_R = (fst ln_R).(i) + 1 in 
           let _, bk = decompose_prod_n narg x in 
           let bk_R = relation order evd env bk in (* TODO: WRONG ! Some things are translated twice here. *)
           let x_R = relation order evd env x in 
           let ft_R, _ = decompose_prod_n_assum narg_R x_R in   
           ((ft_R, bk_R), x_R)) tl 
        in 
        (* tl_R is the array of translated types of fixpoints under the translation of env. *)
        let tl_R = Array.mapi (fun i (_, x) -> 
            let sub = range (fun k -> prime order k (friends i)) order in 
            lift nfun (substl sub x)) tl_relation
        in
        (* env_rec is the environement under fipoints. *)
        let env_rec = push_rec_types (lna, tl, bl) env in 
        (* [bl_R] is the array of translated bodies. *)
        let bl_R = Array.mapi (fun l x -> 
          (* narg is the number of arguments + 1 for the recursive argument. *)
          let narg = (fst ln).(l) + 1 in 
          debug_string [`Fix] (Printf.sprintf "narg = %d\n" narg);
          (* narg_R is the number of translated arguments + 1 for the structural argument. *)
          let narg_R = (fst ln_R).(l) + 1 in 
          debug_string [`Fix] (Printf.sprintf "narg_R = %d\n" narg_R);
          (* let [x^1 ... x^narg] be the argument of the fixpoint (x^narg is the structural argument). *)
          (* appvars is [[| x^1, ..., x^narg |] *)
          let appvars = Array.of_list (range (fun n -> mkRel (n+1)) narg) in 
          (* appvars is [[| x^1_1, x^2_2, x^3_R,  ..., x^narg_1, x^narg_2, x^narg_R|] *)
          let appvars_R = Array.of_list (range (fun n -> mkRel (n+1)) narg_R) in 
          (* [fix] is the l-th fixpoint, under the context extented with x^1, ..., x^narg. *)
          let fix = lift narg (friends l) in 
          (* [appfix] is the l-th fixpoint applied to x^1, ..., x^narg, under the context env extented with x^1, ..., x^narg. *)
          let appfix = mkApp (fix, appvars) in 
          (* [unfolded] is the l-th fixpoint unfolded and applied to x^1, ..., x^narg, under the context extented with x^1, ..., x^narg. *)
          let unfolded = mkBetaApp (unfold_fixpoint env fix, appvars) in 
          let name = lna.(l) in 
          debug [`Fix] "type of fp :" env Evd.empty tl.(l);
          let _, typ = decompose_prod_n narg tl.(l) in 
          let pred_sub k =
              (range (fun x -> lift 1 (prime order (k+1+x) appfix)) (order-1 - k))
            @ [ mkRel 1 ] 
            @ (range (fun x -> lift 1 (prime order x unfolded)) k)
          in
          for k = 0 to order-1 do  
            debug_string [`Fix] (Printf.sprintf "pred %d subst :" k);
            List.iter (debug [`Fix] "" Environ.empty_env Evd.empty) (pred_sub k)
          done;
          debug_string [`Fix] "--> Translating body:";
          (* we substitute the "primes" of fixpoint name by the prime of friends. *)
          let sub = List.flatten 
           (range (fun i ->
            (mkRel (nfun - i))::(range (fun k -> lift nfun (prime order k (friends i))) order))
            nfun) 
          in
          debug_string [`Fix] "fix subst :";
          List.iter (debug [`Fix] "" Environ.empty_env Evd.empty) sub;
          (*
          let bdy_R = liftn nfun (narg_R + 1) 
             (mkApp (lift narg_R (substl sub (liftn nfun (List.length sub + 1) (translate order evd env_rec x))), appvars_R)) 
          in
          *)
          (* Defined in Gamma_R, f1_1, f1_2, f1_R,  .., fn_1, fn_2, fn_R *)
          let bdy_R = translate order evd env_rec x in 
          debug [`Fix] "bdy_R = " Environ.empty_env Evd.empty bdy_R;
          (* Defined in Gamma_R, f1_R,  .., fn_R *)
          let bdy_R = substl sub (liftn nfun ((List.length sub) + 1) bdy_R) in 
          debug [`Fix] "bdy_R = " Environ.empty_env Evd.empty bdy_R;
          (* Defined in Gamma_R, uf1, ..., ufn, f1_R,  .., fn_R *)
          let bdy_R = liftn nfun (nfun + 1) bdy_R in
          debug [`Fix] "bdy_R = " Environ.empty_env Evd.empty bdy_R;
          let bdy_R = mkApp (lift narg_R bdy_R, appvars_R) in
          debug [`Fix] "bdy_R = " Environ.empty_env Evd.empty bdy_R;
          let prods, typ_relation = fst tl_relation.(l) in 
          (* [lift_two] insert the LetIn "unfold_fp" and the recursive argument. Example: [prime order k (lift_two appfix)] is the l-th fixpoint
           * indexed by k, under the context "env_R, f_R, unfold_fp, appvars_R". *)
          let lift_two x = liftn (2*nfun) (narg_R + 1) x  in 
          let res = 
            fold_nat (fun k acc ->
              let index = prime order k typ in
              let base = prime order k unfolded in
              let pred = mkLambda (name, index, substl (pred_sub k) (liftn 1 (order+1) typ_relation)) in 
              debug [`Fix] (Printf.sprintf "pred(%d) = " k) Environ.empty_env Evd.empty pred;
              let endpoint = prime order k appfix in 
              let path = 
                mkApp (mkApp (mkRel (narg_R + l + nfun + 1), 
                Array.of_list (List.map 
                  (fun x -> lift (2*nfun + narg_R) (prime order k (mkRel x))) (hyps_from_rel_context env))),
                Array.map (prime order k) appvars) in (* TODO : mkApp (..., env) *)
              CoqConstants.transport evd 
              [| lift_two index; 
                 lift_two base; 
                 lift_two pred; acc; lift_two endpoint; path |])
              bdy_R order
          in 
          let res = it_mkLambda_or_LetIn res prods in 
          res) bl 
        in
        let rec build_uf_stmt k res =
            let fp = friends k in 
            if k < nfun then
              let name = 
                match lna.(k) with 
                | Name id ->  Names.Id.to_string id
                | _ -> string_of_int k
              in 
              let uf_stmt = unfold_fixpoint_statement evd env fp in 
              let hole =
                 try unfold_fixpoint_proof env fp with Not_found ->
                   let evd_, hole = Evarutil.new_evar Environ.empty_env !evd uf_stmt in 
                   evd := evd_; hole
              in
              debug [`Fix] "uf statement:" Environ.empty_env Evd.empty uf_stmt;
              let res = 
                mkLetIn (Name (id_of_string (Printf.sprintf "unfold_fp_%s" name)), hole, uf_stmt, res) 
              in
              build_uf_stmt (k+1) res
            else res
        in
        debug_evar_map [`Fix] "evd (endoffix) =" !evd;
        print_fix ln_R lna_R tl_R bl_R;
        let res = mkFix (ln_R, (lna_R, tl_R, bl_R)) in 
        let res = build_uf_stmt 0 res in 
        debug [`Fix] "result of fix :" Environ.empty_env Evd.empty res;
        res
    | CoFix(ln, (_, tl, bl)) -> not_implemented ~reason:"cofix" env !evd t
   
    | _ -> not_implemented ~reason:"trapfall" env !evd t

and translate_constant order (evd : Evd.evar_map ref) env cst : constr =
  try 
    Evarutil.e_new_global evd (Relations.get_constant order (Univ.out_punivs cst)) 
  with Not_found -> 
      let (kn, u) = cst in 
      let cb = lookup_constant kn env in 
      Declarations.(match cb.const_body with 
        | Def _ -> 
            let value, _ = Environ.constant_value env cst in 
            translate order evd env value
        | OpaqueDef op -> 
            let table = Environ.opaque_tables env in 
            let fold = mkConstU cst in 
            let evd', typ = Typing.e_type_of ~refresh:true env !evd fold in
            evd := evd';
            let def = Opaqueproof.force_proof table op in
            let _ = Opaqueproof.force_constraints table op in 
            let u = snd cst in 
            let def = subst_instance_constr u def in
            let def = mkCast (def, DEFAULTcast, typ) in
            let pred = mkLambda (Anonymous, typ, substl (range (fun _ -> mkRel 1) order) (relation order evd env typ)) in
            let res = translate order evd env def in
            let uf_opaque_stmt = CoqConstants.eq evd [| typ; def; fold|] in 
            let proof_opaque = 
              try 
                let sort = Typing.sort_of env evd typ in
                if is_prop_sort sort then 
                  (debug [`ProofIrrelevance] "def =" env !evd def;
                  debug [`ProofIrrelevance] "fold =" env !evd fold;
                  CoqConstants.proof_irrelevance evd [| typ; def; fold |])
                else 
                  raise Not_found
              with e -> 
                debug_string [`ProofIrrelevance] (Printexc.to_string e);
                let evd_, hole = Evarutil.new_evar Environ.empty_env !evd uf_opaque_stmt in evd := evd_; hole
            in 
            CoqConstants.transport evd [| typ; def; pred; res; fold; proof_opaque |]
        | _ -> 
            error 
              (Pp.str (Printf.sprintf "The constant '%s' has no registered translation." 
    (KerName.to_string (Constant.user (fst cst))))))
            

and translate_variable order evd env v : constr =
  Constr.mkConst (Relations.get_variable order v)

and translate_inductive order env (ind_name : inductive) =
  try 
    Relations.get_inductive order ind_name
  with Not_found -> error (Pp.str (Printf.sprintf "The inductive '%s' has no registered translation." 
    (KerName.to_string (MutInd.user (fst ind_name)))))

and translate_constructor order env (ind, i) : constructor = 
  (translate_inductive order env ind, i)

and translate_case_info order env ci = 
  { 
    ci_ind = translate_inductive order env ci.ci_ind;
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

open Entries
open Declarations

let map_local_entry f = function 
  | LocalDef c -> LocalDef (f c)
  | LocalAssum c -> LocalAssum (f c)

let constr_of_local_entry = function LocalDef c | LocalAssum c -> c 


let check_params env evdr ctx l = 
  let env = push_context ctx env in
  let env, params = List.fold_left
     (fun (env, params) -> function (x, LocalAssum c) | (x, LocalDef c) -> 
        debug [`Inductive] "c = " env !evdr c;
        evdr := fst (Typing.e_type_of env !evdr c);
        let env = push_rel (Names.Name x, None, c) env in 
        let params = (Names.Name x, None, c)::params in
        env, params) (env, []) (List.rev l)
  in 
  env, params


(* Translation of inductives. *)

let rec translate_mind_body order evdr env kn b inst = 
  let env = push_context b.mind_universes env in

  debug_string [`Inductive] "computing envs ...";
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
  (*
  List.iter (function (id, LocalDef c ) ->
    Pp.(msg_notice (Nameops.pr_id id));
       debug [`Inductive] "local_def" empty_env !evdr c |
                      (id, LocalAssum c) -> 
    Pp.(msg_notice (Nameops.pr_id id));
                        debug [`Inductive] "local_assum"  empty_env !evdr c) mind_entry_params_R; *)


  debug_string [`Inductive] "translatation of inductive ...";
  let mind_entry_inds_R = 
    List.mapi 
      (fun i x -> translate_mind_inductive order evdr env (kn,i) b inst envs x) 
      (Array.to_list b.mind_packets)
  in
  let ctx = Univ.instantiate_univ_context b.mind_universes in
  { 
    mind_entry_record = None;
    mind_entry_finite = b.mind_finite;
    mind_entry_params = mind_entry_params_R;
    mind_entry_inds = mind_entry_inds_R;
    mind_entry_polymorphic = b.mind_polymorphic;
    mind_entry_universes = ctx;
    mind_entry_private = b.mind_private
  }


and translate_mind_param order evd env (l : rel_context) = 
  let rec aux env acc = function 
     | [] -> acc
     | (x,op,hd)::tl -> 
           (* TODO : This is not the right thing. *)
           let x_R = (translate_name order x, LocalAssum (relation order evd env hd)) in  
           let env = push_rel (x, op, hd) env in
           let x_i = range (fun k -> 
                     (prime_name order k x, LocalAssum (lift k (prime order k hd)))) order in 
           let acc = (x_R::x_i):: acc in
           aux env acc tl  
  in 
  let l = List.rev l in
  List.map (function (Name x,c) -> (x, c) | _ -> failwith "anonymous param") (List.flatten (aux env [] l))

and translate_mind_inductive order evdr env ikn mut_entry inst (env_params, params, env_arities, env_arities_params) e = 
  let typename = e.mind_typename in
  let p = mut_entry.mind_nparams in 
  let _, arity = 
     decompose_prod_n p (Inductive.type_of_inductive env ((mut_entry, e), inst))
  in
  debug [`Inductive] "Arity:" env_params !evdr arity;
  let arity_R = 
      debug_string [`Inductive] "Computing arity";
      let arity_R = relation order evdr env_params arity in
      debug [`Inductive] "Arity_R before substitution:" Environ.empty_env Evd.empty arity_R;
      let inds = List.rev (fold_nat 
         (fun k acc -> 
           prime order k 
            (apply_head_variables (mkIndU (ikn, inst)) p)::acc) [] order) in 
      debug_string [`Inductive] "Substitution:";
      List.iter (debug [`Inductive] "" Environ.empty_env Evd.empty) inds;
      let result = substl inds arity_R in 
      debug [`Inductive] "Arity_R after substitution:" Environ.empty_env Evd.empty result;
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
        let l =  List.map (fun x -> snd (decompose_prod_n p x)) l in
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
          let third_part = range (fun m -> prime order m (apply_head_variables (mkConstructU  ((ikn, k + 1), inst)) p)) order in 
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



let rec retype_mind_entry env evdr mie = 
  debug_evar_map [`Inductive] "before retyping, evar = " !evdr;
  let params = relcontext_of_local_entry env evdr mie.mind_entry_params in
  debug_evar_map [`Inductive] "after retyping params, evar = " !evdr;
  let env_params = push_rel_context params env in 
  let arities = List.map (fun ind -> 
          let arity = ind.mind_entry_arity in 
          let ctx, sort = Reduction.dest_arity env_params arity in
          (* let new_sort = Evarutil.e_new_Type env_params evdr in *)
          let arity = mkArity(ctx, sort) in 
          (* debug [`Inductive] "refreshing : " env !evdr ind.mind_entry_arity;
          let evd, arity = Evarsolve.refresh_universes (Some false) env !evdr ind.mind_entry_arity in 
          debug [`Inductive] " refreshed : " env !evdr arity; 
          evdr := evd; *)
          ind.mind_entry_typename, arity
      ) mie.mind_entry_inds
  in 
  debug_evar_map [`Inductive] "after refreshing universes, evar = " !evdr;
  let full_arities = List.map (fun (n, x) -> (n, it_mkProd_or_LetIn x params)) arities in 
  let env_arities = 
    List.fold_left (fun env (typename, full_arity) -> 
      debug_string [`Inductive] (Printf.sprintf "Adding '%s' to the environement." (Names.Id.to_string typename));
      let env = Environ.push_rel (Names.Name typename, None, full_arity) env in 
      env
    ) env full_arities
  in 
  let env_arities_params = push_rel_context params env_arities in
  List.iteri (fun k ind -> 
    let _, arity_sort = Reduction.dest_arity env_params (snd (List.nth arities k)) in
    debug_string [`Inductive] (Printf.sprintf "Inductive '%s'" (Names.Id.to_string ind.mind_entry_typename));
    debug [`Inductive] "sort =" Environ.empty_env !evdr (mkSort arity_sort);
    List.iteri (fun i cstr ->
       debug_string [`Inductive] (Printf.sprintf "checking constructor %d:" i);
       debug_evar_map [`Inductive] "evar = " !evdr;
       debug [`Inductive] "cstr = " env_arities_params !evdr cstr;
       let evd, typ = Typing.e_type_of env_arities_params !evdr cstr in 
       debug [`Inductive] "typ = " env_arities_params !evdr typ;
       let constructor_sort = destSort typ in 
       evdr := Evd.set_leq_sort env_arities_params evd constructor_sort arity_sort;
   ) ind.mind_entry_lc) mie.mind_entry_inds;
   debug_evar_map [`Inductive] "evar = " !evdr;
   
   { mie with 
     mind_entry_inds = List.mapi
       (fun i mei -> { mei with mind_entry_arity = snd (List.nth arities i)}) mie.mind_entry_inds;
     mind_entry_universes = Evd.universe_context !evdr }
   
and relcontext_of_local_entry env evdr local_entry = 
  let env, params = List.fold_left
     (fun (env, params) -> function (x, LocalAssum c)  -> 
        debug [`Inductive] "c = " env !evdr c;
        evdr := fst (Typing.e_type_of env !evdr c);
        let env = push_rel (Names.Name x, None, c) env in 
        let params = (Names.Name x, None, c)::params in
        env, params     
     | (x, LocalDef c) -> assert false (* TODO *)
     ) (env, []) (List.rev local_entry)
  in 
  params 
