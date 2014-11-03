open Term
open Names
open Vars
open Constr
open Environ
open Util
open Context
open Environ

module CoqConstants = struct
  let msg = "parametricity: unable to fetch constants"
  
  let eq evdref args = 
    Program.papp evdref (fun () -> Coqlib.coq_reference msg ["Init"; "Logic"] "eq") args 

  let transport evdref args = 
    Program.papp evdref (fun () -> Coqlib.coq_reference msg ["Init"; "Logic"] "eq_rect") args 
end

let test = ref (mkRel 0)

let debug_flag = true

let default_arity = 2

let debug env c = 
  if debug_flag then
    Pp.(msg_notice (
       Printer.pr_context_of env ++ str "\n|-"
       ++ Printer.safe_pr_constr_env env c))

let print_string s =
  if debug_flag then  
    Pp.msg_notice (Pp.str ("--->\t"^s))

let print_caseinfo ci =
  if debug_flag then 
    let ndecls = Array.to_list ci.ci_cstr_ndecls in
    let nargs = Array.to_list ci.ci_cstr_nargs in 
    let to_string x = 
      String.concat ";" (List.map string_of_int x)
    in 
    let string_of_style = function 
      LetStyle -> "LetStyle" | IfStyle -> "IfStyle" | LetPatternStyle -> "LetPatternStyle" | MatchStyle -> "MatchStyle" | RegularStyle -> "RegularStyle" 
    in
    let s = Printf.sprintf "style = %s, ind_nargs = %d, pars = %d, decls = %s, nargs = %s"
      (string_of_style ci.ci_pp_info.style)
      (ci.ci_pp_info.ind_nargs)
      ci.ci_npar
      (to_string ndecls)
      (to_string nargs)
    in 
    print_string s

let not_implemented ?(reason = "no reason") env t = 
  Pp.msg_notice (Pp.str (Printf.sprintf "not implemented (%s):" reason));
  debug env t;
  Pp.msg_notice (Pp.str "now raising exception");
  failwith "not implemented"

let hyps_from_rel_context env = 
  let rctx = Environ.rel_context env in 
  let rec aux acc depth = function 
      [] -> acc
    | (_, None, _) :: tl -> aux (depth :: acc) (depth + 1) tl
    | _ :: tl -> aux acc (depth + 1) tl 
  in 
  aux [] 1 rctx 

let prop_or_type s = s (*
   if is_Set s || is_Prop sthen mkProp else s *)

let rec affine_lift order index depth c = match Constr.kind c with
  | Constr.Rel i -> if i <= depth then c else Constr.mkRel (order * i + index)
  | _ -> Constr.map_with_binders ((+) 1) (affine_lift order index) depth c

let rec prime order index c = 
  let rec aux depth c = match Constr.kind c with
    | Constr.Rel i -> 
        if i <= depth then c else Constr.mkRel (depth + (order + 1) * (i - depth)  - index) 
    | _ -> Constr.map_with_binders ((+) 1) aux depth c
  in aux 0 c

let translate_string order x =
 match order with 
   | 0 -> x
   | 1 -> x^"_P"
   | 2 -> x^"_R"
   | 3 -> x^"_T"
   | n -> x^"_R_"^(string_of_int n)
 
let prime_string order value x = 
  if value >= order then 
    translate_string order x
  else if order = 1 then x else 
    match value with 
     | 0 -> x^"₁"
     | 1 -> x^"₂"
     | 2 -> x^"₃"
     | n -> Printf.sprintf "%s_%d" x (n-1)

let translate_id order y = (id_of_string @@ translate_string order @@ string_of_id @@ y)
let prime_id order value y = (id_of_string @@ prime_string order value @@ string_of_id @@ y)


let prime_name order value = function
  | Name y -> Name  (prime_id order value y)
  | Anonymous -> Anonymous

let translate_name order = function
  | Name y -> Name  (translate_id order y)
  | Anonymous -> Anonymous

(* l \in ⟦s⟧_3 = l₁ → l₂ → l₃ → t, 
 * where t is Prop if s ∈ {Set, Prop} or s otherwise. *)
let translate_sort l s = 
  let rec aux k acc = function 
  | [] -> acc
  | hd::tl ->
      let k = k - 1 in 
      aux k (mkArrow (mkRel k) acc) tl
  in
  aux (List.length l) (prop_or_type s) l

let range f order =
  let rec aux k acc = 
    if k < order then 
      aux (k + 1) ((f k)::acc)
    else 
      acc
  in 
  aux 0 []

let fold_nat f x = 
  let rec aux acc n =
    if n = 0 then acc else
      let n = n - 1 in 
      aux (f n acc) n
  in aux x 

let apply_head_variables t n = 
  let l = fold_nat (fun k l -> (mkRel (k + 1))::l) [] n in 
  mkApp (t, Array.of_list (List.rev l))


let unfold_fixpoint env (t : constr) : constr = 
  match kind t with 
    | Fix ((ri, i),(lna, tl, bl)) -> 
        let nfun = Array.length lna in 
        let friends k = mkFix ((ri, k), (lna, tl, bl)) in 
        let sub = range friends nfun in 
        substl sub bl.(i)
    | _ -> failwith "unfold_fixpoint: expects a fixpoint"

let mkBetaApp (f, v) = Reduction.beta_appvect f v

let rec unfold_fixpoint_statement evdref (env : Environ.env) (t : constr) : constr =
  match kind t with 
    | Fix ((ri, i), (lna, tl, bl)) -> 
        let narg = ri.(i) + 1 in 
        let cty = tl.(i) in
        print_string (Printf.sprintf "narg = %d\n" narg);
        debug env cty;
        let front, typ = decompose_prod_n narg cty in 
        let appvars = Array.of_list (range (fun n -> mkRel (n+1)) narg) in 
        let unfolded = unfold_fixpoint env t in 
        let concl = CoqConstants.eq evdref [| typ; mkBetaApp (lift narg unfolded, appvars); mkApp (lift narg t, appvars) |] in 
        print_string (Printf.sprintf "??? %d \n" (Environ.nb_rel env));
        Environ.fold_rel_context (fun _ -> mkProd_or_LetIn) env ~init:(compose_prod front concl)
    | Lambda (x, a, m) -> 
        let env = push_rel (x, None, a) env in 
        unfold_fixpoint_statement evdref env m
    | Const cst ->  
        let cval = Environ.constant_value_in env cst in 
        unfold_fixpoint_statement evdref env cval
    | _ -> failwith "unfold_fixpoint_statement: expects a fixpoint"

(* G |- t ---> |G|, x1, x2 |- [x1,x2] in |t| *)
(* TODO : CHECK env *)

let rec relation order evd env (t : constr) : constr = 
  print_string (Printf.sprintf "relation %d evd env t" order);
  print_string "evd ="; Pp.msg_info (Evd.pr_evar_map None !evd); Pp.msg_info (Evd.pr_evar_universe_context (Evd.evar_universe_context !evd));
  print_string "t ="; debug env t;
  match kind t with 
    | Sort s -> fold_nat (fun _ -> mkArrow (mkRel order)) (prop_or_type t) order
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

and translate order evd env (t : constr) : constr = 
  print_string (Printf.sprintf "translate %d evd env t" order);
  print_string "evd ="; Pp.msg_info (Evd.pr_evar_map None !evd);
  print_string "t ="; debug env t;
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
    | Meta n -> not_implemented ~reason:"meta" env t
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


    | Const c -> translate_constant order evd env c
    | Ind (ind, u) -> mkInd (translate_inductive order env ind)
    | Construct (cstr, u) -> translate_constructor order env cstr
    | Case (ci , p, c, bl) -> 
        print_string "input :";
        print_case (ci, p, c, bl);
        let nargs = ci.ci_pp_info.ind_nargs in
        let theta = mkCase (ci, lift (nargs + 1) p, mkRel 1, Array.map (lift (nargs + 1)) bl) in
        print_string "theta:";
        debug Environ.empty_env theta;
        print_string (Printf.sprintf "nargs = %d" nargs); 
        let ci_R = translate_case_info order env ci in
        print_string "p:";
        debug Environ.empty_env p;
        let lams, t = decompose_lam_n (nargs + 1) p in 
        print_string "t:";
        debug Environ.empty_env t;
        let t_R = relation order evd env t in
        print_string "t_R:";
        debug Environ.empty_env t_R;
        let sub = range (fun k -> prime order k theta) order in 
        print_string "substitution :";
        List.iter (debug Environ.empty_env) sub;
        let t_R = substl sub t_R in 
        print_string "t_R[...]:";
        debug Environ.empty_env t_R;
        print_string "lams :";
        List.iter (fun (x, c) -> debug Environ.empty_env c) lams;
        let lams_R = List.flatten (List.map (fun (x, c) -> 
            (translate_name order x, relation order evd env c)::
              (range (fun k -> (prime_name order k x, lift k (prime order k c))) order)) lams) 
        in
        print_string "lams_R :";
        List.iter (fun (x, c) -> debug Environ.empty_env c) lams_R;
        let p_R = compose_lam lams_R t_R in
        let c_R = translate order evd env c in 
        let bl_R = Array.map (translate order evd env) bl in 
        let tuple = (ci_R, p_R, c_R, bl_R) in 
        print_case tuple;
        mkCase tuple
    | Fix ((ri, i) as ln ,(lna, tl, bl)) -> 
        let print_fix (ri, i) lna tl bl =
          print_string (Printf.sprintf "index = %d" i);
          print_string (Printf.sprintf "recindxs = %s"
            (String.concat ";" (List.map string_of_int (Array.to_list ri))));
          print_string "typearray =";
          Array.iter (debug Environ.empty_env) tl;
          print_string "body =";
          Array.iter (debug Environ.empty_env) bl
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
           let bk_R = relation order evd env bk in (* TODO: WRONG ! *)
           let x_R = relation order evd env x in 
           let ft_R, _ = decompose_prod_n_assum narg_R x_R in   
           ((ft_R, bk_R), x_R)) tl 
        in 
        (* tl_R is the array of translated types of fixpoints under the translation of env. *)
        let tl_R = Array.mapi (fun i (_, x) -> 
            let sub = range (fun k -> prime order k (friends i)) order in 
            substl sub x) tl_relation
        in
        (* env_rec is the environement under fipoints. *)
        let env_rec = push_rec_types (lna, tl, bl) env in 
        (* [bl_R] is the array of translated bodies. *)
        let bl_R = Array.mapi (fun l x -> 
          (* narg is the number of arguments + 1 for the recursive argument. *)
          let narg = (fst ln).(l) + 1 in 
          print_string (Printf.sprintf "narg = %d\n" narg);
          (* narg is the number of translated arguments + 1 for the structural argument. *)
          let narg_R = (fst ln_R).(l) + 1 in 
          print_string (Printf.sprintf "narg_R = %d\n" narg_R);
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
          print_string "type of fp :";
          debug env tl.(l);
          let _, typ = decompose_prod_n narg tl.(l) in 
          let pred_sub k =
              (range (fun x -> lift 1 (prime order (k+1+x) appfix)) (order-1 - k))
            @ [ mkRel 1 ] 
            @ (range (fun x -> lift 1 (prime order x unfolded)) k)
          in
          for k = 0 to order-1 do  
            print_string (Printf.sprintf "pred %d subst :" k);
            List.iter (debug Environ.empty_env) (pred_sub k)
          done;
          print_string "--> Translating body:";
          (* we substitute the "primes" of fixpoint name by the prime of friends. *)
          let sub = List.flatten 
           (range (fun i ->
            (mkRel (i+1))::(range (fun k -> lift 1 (prime order k (friends i))) order))
            nfun) 
          in
          print_string "fix subst :";
          List.iter (debug Environ.empty_env) sub;
          let bdy_R = liftn 1 (narg_R + 1) (mkApp (lift narg_R (substl sub (liftn nfun (List.length sub + 1) (translate order evd env_rec x))), appvars_R)) in
          let prods, typ_relation = fst tl_relation.(l) in 
          (* [lift_two] insert the LetIn "unfold_fp" and the recursive argument. Example: [prime order k (lift_two appfix)] is the l-th fixpoint
           * indexed by k, under the context "env_R, f_R, unfold_fp, appvars_R". *)
          let lift_two = liftn 2 (narg_R + 1) in 
          let res = 
            fold_nat (fun k acc ->
              let index = prime order k typ in
              let base = prime order k unfolded in
              let pred = mkLambda (name, index, substl (pred_sub k) (liftn 1 (order+1) typ_relation)) in 
              print_string (Printf.sprintf "pred(%d) = " k);
              debug Environ.empty_env pred;
              let endpoint = prime order k appfix in 
              let path = 
                mkApp (mkApp (mkRel (narg_R + 1), 
                Array.of_list (List.map 
                  (fun x -> lift (narg_R + 2) (prime order k (mkRel x))) (hyps_from_rel_context env))),
                Array.map (prime order k) appvars) in (* TODO : mkApp (..., env) *)
              CoqConstants.transport evd [| lift_two index; lift_two base; lift_two pred; acc; lift_two endpoint; path |])
              bdy_R order
          in 
          let uf_stmt = unfold_fixpoint_statement evd env t in 
          let evd_, hole = Evarutil.new_evar !evd Environ.empty_env uf_stmt in evd := evd_;
          let res = it_mkLambda_or_LetIn res prods in 
          let res = 
            mkLetIn (Name (id_of_string "unfold_fp"), hole, uf_stmt, res) 
          in
          res) bl 
        in
        print_string "evd (endoffix) ="; Pp.msg_info (Evd.pr_evar_map None !evd);
        print_fix ln_R lna_R tl_R bl_R;
        mkFix (ln_R, (lna_R, tl_R, bl_R))
    | CoFix(ln, (_, tl, bl)) -> not_implemented ~reason:"cofix" env t
    | _ -> not_implemented ~reason:"trapfall" env t

and translate_constant order evd env cst : constr =
  try 
    Constr.mkConst (Relations.get_constant order (Univ.out_punivs cst))
  with Not_found -> 
    let cval = Environ.constant_value_in env cst in 
    translate order evd env cval

and translate_variable order evd env v : constr =
  Constr.mkConst (Relations.get_variable order v)

and translate_mutual_inductive order env (ind_name : mutual_inductive) =
  Relations.get_inductive order ind_name

and translate_inductive order env (mut_ind, i) = 
  (translate_mutual_inductive order env mut_ind, i)

and translate_constructor order env ((mut_ind, k), i) : constr = 
  mkConstruct ((translate_mutual_inductive order env mut_ind, k), i)

and translate_case_info order env ci = 
  { 
    ci_ind = translate_inductive order env ci.ci_ind;
    ci_npar = (order + 1) * ci.ci_npar;
    ci_cstr_ndecls = Array.map (fun x -> (order + 1) * x) ci.ci_cstr_ndecls;
    ci_cstr_nargs = Array.map (fun x -> (order + 1) * x) ci.ci_cstr_nargs;
    ci_pp_info = translate_case_printing order env ci.ci_pp_info;
  }

and translate_case_printing order env cp = 
  { 
    ind_nargs = (order + 1) * cp.ind_nargs + order;
    style = translate_style cp.style }

and translate_style x = x

and print_case (ci, p, c, bl) =
  print_string "ci :";
  print_caseinfo ci;
  print_string "p:";
  debug Environ.empty_env c;
  Array.iteri (fun n x -> 
    print_string (Printf.sprintf "bl_%d:" n);
    debug Environ.empty_env x) bl

open Entries
open Declarations

let map_local_entry f = function 
  | LocalDef c -> LocalDef (f c)
  | LocalAssum c -> LocalAssum (f c)

let constr_of_local_entry = function LocalDef c | LocalAssum c -> c 


let rec translate_mind_body order evd env kn b = 
  { 
    mind_entry_record = (match b.mind_record with Some _ -> Some true | _ -> None);
    mind_entry_finite = b.mind_finite;
    mind_entry_params = translate_mind_param order evd env b.mind_params_ctxt;
    mind_entry_inds = List.mapi 
      (fun i -> translate_mind_inductive order evd env (kn,i) b) 
      (Array.to_list b.mind_packets);
    mind_entry_polymorphic = b.mind_polymorphic;
    mind_entry_universes = b.mind_universes;
    mind_entry_private = b.mind_private
  }


and translate_mind_param order evd env (l : rel_context) = 
  let rec aux env acc = function 
     | [] -> acc
     | (x,op,hd)::tl -> 
           let env = push_rel (x, op, hd) env in
           let x_R = (translate_name order x, LocalAssum (relation order evd env hd)) in  
           let x_i = range (fun k -> 
                     (prime_name order k x, LocalAssum (lift k (prime order k hd)))) order in 
           let acc = (x_R::x_i):: acc in
           aux env acc tl  
  in 
  let l = List.rev l in
  print_string "params :";
  if debug_flag then 
    Pp.msg_notice (Termops.print_rel_context (push_rel_context l Environ.empty_env));
  let result = 
    List.map (function (Name x,c) -> (x, c) | _ -> failwith "anonymous param") (List.flatten (aux env [] l))
  in 
  print_string "translated params:";
  if debug_flag then 
    List.iter (fun (x, c) -> Pp.msg_notice (Pp.str (string_of_id x)); debug Environ.empty_env (constr_of_local_entry c)) result;
  result

and translate_mind_inductive order evd env ikn mut_entry e = 
  let p = mut_entry.mind_nparams_rec in 
  { 
    mind_entry_typename = translate_id order e.mind_typename;
    mind_entry_arity =
    begin
      let arity = Inductive.type_of_inductive env (Univ.in_punivs (mut_entry, e)) in
      print_string "Arity:";
      debug Environ.empty_env arity;
      let _, arity = decompose_prod_n p arity in
      print_string "Arity after removing params:";
      debug Environ.empty_env arity;
      let arity_R = 
         relation order evd env arity
      in
      print_string "Arity_R before substitution:";
      debug Environ.empty_env arity_R;
      let inds = List.rev (fold_nat 
         (fun k acc -> prime order k 
            (apply_head_variables (mkInd ikn) p)::acc) [] order) in 
      print_string "Substitution:";
      List.iter (debug Environ.empty_env) inds;
      let result = substl inds arity_R in 
      print_string "Arity_R after substitution:";
      debug Environ.empty_env result;
      result
    end;
    mind_entry_consnames = List.map (translate_id order) (Array.to_list e.mind_consnames);
    mind_entry_lc = 
      begin
        let l = Array.to_list e.mind_user_lc in
        print_string "before translation :";
        List.iter (debug Environ.empty_env) l;
        let l = List.map (compose snd (decompose_prod_n p)) l in
        print_string "remove uniform parameters :";
        List.iter (debug Environ.empty_env) l;
        (*
        let sub = range (fun k -> mkRel (mut_entry.mind_nparams_rec + k + 1)) mut_entry.mind_nparams_rec in
        let l = List.map (substl sub) l in 
        print_string "reverse parameters and inductive variables :"; 
        List.map (debug Environ.empty_env) l;*)
        let l = List.map (relation order evd env) l in
        let for_each_constructor k =
          (* Elements Ti of l are defined in the translation of the context : 
            *   [A'1;...;A'p;x1:X1;...;xn:Xn] 
            * augmented with 
            *   y_1 : Ti_1, y_2 : Ti_2
            * which is 
            *   [A'1_1; A'1_2; A'1_R;...;A'p_1;A'p_2;A'p_R;x1_1:X1_1; x1_2:X1_2, x1_R : ...] 
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
            (mkRel ((order + 1)*p + k+1))::(range (fun _ -> mkInd (kn, k)) order)) n)
          in
          let second_part = List.flatten @@ List.rev @@ (List.map List.rev) (range (fun k -> 
            (mkRel ((order + 1)*(k+1)))::(range (fun i -> mkRel ((order + 1)*k + i + 1)) order)) p)
          in
          print_string (Printf.sprintf "constructor n°%d" k);
          let third_part = range (fun m -> prime order m (apply_head_variables (mkConstruct (ikn, k + 1)) p)) order in 
          let final_substitution = third_part @ second_part @ first_part in
          print_string "substitution :";
          List.iter (debug Environ.empty_env) final_substitution;
          substl final_substitution 
        in
        print_string "before substitution:";
        List.iter (debug Environ.empty_env) l;
        let result = List.mapi for_each_constructor l in 
        print_string "after substitution:";
        List.iter (debug Environ.empty_env) result;
        result
      end
  }

(** Adds the definition name := ⟦a⟧ : ⟦b⟧ a a. *)
let declare_abstraction order evd env a b name =
  let sigma = ref evd in 
  Obligations.check_evars env evd;
  print_string "translate term ...";
  let a_R = translate order sigma env a  in
  print_string "translate type ...";
  let b_R = relation order sigma env b in 
  let sub = range (fun k -> prime order k a) order in 
  let b_R = substl sub b_R in
  let evd, _ = Typing.e_type_of env !sigma a_R in
  let evd, _ = Typing.e_type_of env evd b_R in
  print_string "eterm_obligations:";
  let obls, _, a_R, b_R = Obligations.eterm_obligations env name evd 0 a_R b_R in 
  let ctx = Evd.evar_universe_context evd in
  let hook = 
    match kind_of_term a with 
      | Const cte -> Some 
         (Lemmas.mk_hook (fun _ dcl -> 
            Relations.add_global order (Globnames.ConstRef (Univ.out_punivs cte)) dcl))
      | _ -> None
  in
  print_string "add_definition:";
  ignore (Obligations.add_definition name ?hook ~term:a_R b_R ctx obls);
  print_string "evar_map ="; Pp.msg_info (Evd.pr_evar_map None evd)

