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

open Debug
open Term
open Names
open Vars
open Constr
open Environ
open Util
open Context
open Environ
open Rel.Declaration
open Sigma.Notations

let unsafe_e_ (f : Evd.evar_map ref -> 'a)
  (evd : 'r Sigma.t) : ('a, 'r) sigma_ =
  let evdref = ref (Sigma.to_evar_map evd) in
  let a = f evdref in
  Sigma.Unsafe.of_pair (a, !evdref)

let unsafe_ (f : Evd.evar_map -> 'a * Evd.evar_map)
                  (evd : 'r Sigma.t) : ('a, 'r) sigma_ =
  Sigma.(Unsafe.of_pair (f (to_evar_map evd)))

let unsafe0_ (f : Evd.evar_map ->  Evd.evar_map) =
  unsafe_ (fun x -> ((), f x))

let unsafe_swap_ (f : Evd.evar_map -> Evd.evar_map * 'a)
   (evd : 'r Sigma.t) : ('a, 'r) sigma_ =
  unsafe_ (fun x -> let (evd, a) = f x in (a, evd)) evd

let sigma_sort_of env (c : types) =
  unsafe_e_ (fun evdref -> Typing.e_sort_of env evdref c)

let sigma_conv env ?ts t1 t2 =
  unsafe_e_ (fun evdr -> Evarconv.e_conv env evdr ?ts t1 t2)

let sigma_cumul env ?ts t1 t2 =
  unsafe_e_ (fun evdr -> Evarconv.e_cumul env evdr ?ts t1 t2)

let rec sigma_list_iter :
  'r. ('a -> unit run_) -> 'a list -> 'r Sigma.t -> (unit, 'r) sigma_ =
  fun f l evd ->
  match l with [] -> Sigma ((), evd, Sigma.refl)
             | a :: l -> let Sigma (_, evd, p) = (f a).run evd in
                         let Sigma (_, evd, q) = sigma_list_iter f l evd in
                         Sigma ((), evd, p +> q)


let sigma_list_mapi (f : int -> 'a -> 'b run_) l
  (evd : 'r Sigma.t) : (_, 'r) sigma_ =
  let rec aux i l = {run = fun evd ->
    match l with [] -> Sigma ([], evd, Sigma.refl)
               | a :: l -> let Sigma (a', evd, p) = (f i a).run evd in
                           let Sigma (l', evd, q) = (aux (i + 1) l).run evd in
                           Sigma (a' :: l', evd, p +> q)}
  in (aux 0 l).run evd

let sigma_list_map f = sigma_list_mapi (fun _ -> f)

let sigma_fold_right f l ~init evd =
  let rec aux : type r. 'a list -> 'b -> r Sigma.t -> ('b, r) sigma_ =
  fun l init evd ->
  match l with
    [] -> Sigma (init, evd, Sigma.refl)
  | a::l -> let Sigma (f_l_accu, evd, p) = aux l init evd in
            let Sigma (f_a_flaccu, evd, q) = (f a f_l_accu).run evd in
            Sigma (f_a_flaccu, evd, p +> q) in
  aux l init evd

let sigma_fold_nat
      (f : int -> 'a -> 'a run_) x n (evd : 'r Sigma.t) : ('a, 'r) sigma_ =
  let rec aux acc n : 'a run_ =
    {run = fun evd ->
           if n = 0 then Sigma (acc, evd, Sigma.refl) else
             let n = n - 1 in
             let Sigma (f_n_acc, evd, p) = (f n acc).run evd in
             let Sigma (aux_fnacc_n , evd, q) = (aux f_n_acc n).run evd in
             Sigma (aux_fnacc_n, evd, p +> q)} in
  (aux x n).run evd

let sigma_array_mapi (f : int -> 'a -> 'b run_) a (evd : 'r Sigma.t) =
  let open Array in
  let l = length a in
  if l = 0 then Sigma ([||], evd, Sigma.refl) else begin
      let Sigma (fa0, evd, p) = (f 0 (unsafe_get a 0)).run evd in
      let r = make l fa0 in
      let sevdr : (unit, 'r) sigma_ ref = ref (Sigma ((), evd, p)) in
      for i = 1 to l - 1 do
        let Sigma ((), evd, p) = !sevdr in
        let Sigma (fai, evd, q) = (f i (unsafe_get a i)).run evd in
        unsafe_set r i fai;
        sevdr := Sigma ((), evd, p +> q)
      done;
      let Sigma (_, evd, p) = !sevdr in Sigma (r, evd, p)
    end

let sigma_array_map (f : 'a -> 'b run_) = sigma_array_mapi (fun _ -> f)

let sigma_array_init l (f : int -> 'a run_)
                     (evd : 'r Sigma.t) : ('a array, 'r) sigma_ =
  let open Array in
  if l = 0 then Sigma ([||], evd, Sigma.refl) else
  if l < 0 then invalid_arg "Array.init"
  (* See #6575. We could also check for maximum array size, but this depends
     on whether we create a float array or a regular one... *)
  else
    let Sigma (f0, evd, p) = (f 0).run evd in
    let res = make l f0 in
    let sevdr : (unit, 'r) sigma_ ref = ref (Sigma ((), evd, p)) in
    for i = 1 to pred l do
      let Sigma ((), evd, p) = !sevdr in
      let Sigma (fi, evd, q) = (f i).run evd in
      unsafe_set res i fi;
      sevdr := Sigma ((), evd, p +> q)
    done;
    let Sigma (_, evd, p) = !sevdr in Sigma (res, evd, p)


let error msg =
  raise (CErrors.UserError ("Parametricity plugin", msg))

module CoqConstants = struct
  let msg = "parametricity: unable to fetch constants"

  let add_constraints =
    fun univ evd ->
    let env = Global.env () in
    let extract_type_sort poly_ref evd =
      let Sigma (poly_ref, evd, p) =
        Evarutil.new_global evd (delayed_force poly_ref) in
      let ref_type = Retyping.get_type_of env
        (Sigma.to_evar_map evd) poly_ref in
      let ref_sort = let _, a, _ = destProd ref_type in a in
      let Sigma (_, evd, q) = sigma_cumul env univ ref_sort evd in
      Sigma ((), evd, p +> q)
    in
    let extract_pred_sort poly_ref evd =
      let Sigma (poly_ref, evd, p) =
        Evarutil.new_global evd (delayed_force poly_ref) in
      let ref_type = Retyping.get_type_of env
          (Sigma.to_evar_map evd) poly_ref in
      let ref_sort = let _, _, typ = destProd ref_type in
                     let _, _, typ = destProd typ in
                     let _, a, _ = destProd typ in
                     snd (decompose_prod a) in
      let Sigma (_, evd, q) = sigma_cumul env univ ref_sort evd in
      Sigma ((), evd, p +> q)
    in
    let Sigma (_, evd, p) =
      sigma_list_iter (fun poly_ref -> {run =
        fun evd -> extract_type_sort poly_ref evd
                      })
      [Program.coq_eq_ind; Program.coq_eq_refl; Program.coq_eq_rect]
      evd in
    let Sigma (_, evd, q) = extract_pred_sort Program.coq_eq_rect evd in
    Sigma ((), evd, p +> q)

  let eq args = unsafe_e_ (fun evdr ->
                    Program.papp evdr Program.coq_eq_ind args)

  let eq_refl args = unsafe_e_ (fun evdr ->
                         Program.papp evdr Program.coq_eq_refl args)

  let transport args = unsafe_e_ (fun evdr ->
                           Program.papp evdr Program.coq_eq_rect args)

  let proof_irrelevance args = unsafe_e_ (fun evdr ->
    Program.papp evdr (fun () ->
      Coqlib.coq_reference msg ["Logic"; "ProofIrrelevance"] "proof_irrelevance") args)
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

let decompose_prod_n_assum_by_prod n =
  if n < 0 then
    failwith "decompose_prod_n_assum_by_prod: integer parameter must be positive";
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else match kind_of_term c with
    | Prod (x,t,c)    -> prodec_rec (Rel.add (LocalAssum (x,t)) l) (n-1) c
    | LetIn (x,b,t,c) -> prodec_rec (Rel.add (LocalDef (x,b,t)) l) n c
    | Cast (c,_,_)      -> prodec_rec l n c
    | c -> failwith "decompose_prod_n_assum_by_prod: not enough assumptions"
  in
  prodec_rec Rel.empty n

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
  mkApp (t, Rel.to_extended_vect 0 ctxt)

(* Substitution in a signature. *)
let substnl_rel_context (subst : Vars.substl) n sign =
  let rec aux n = function
  | d::sign -> substnl_decl subst n d :: aux (n+1) sign
  | [] -> []
  in List.rev (aux n (List.rev sign))

let substl_rel_context subst = substnl_rel_context subst 0


(* A variant of mkApp that reduces redexes. *)
let mkBetaApp (f, v) = Reduction.beta_appvect f v

(* If [c] is well-formed type in env [G], then [generalize G c] returns [forall G.c]. *)
let generalize_env (env : Environ.env) (init : types) =
  it_mkProd_or_LetIn init (Environ.rel_context env)

(* If [c] is well-formed term in env [G], then [generalize G c] returns [fun G.c]. *)
let abstract_env (env : Environ.env) (init : constr) =
  it_mkLambda_or_LetIn init (Environ.rel_context env)

let mkFreshInd env evd c =
  mkIndU Sigma.(apply evd {run = fun evd ->
    fresh_inductive_instance env evd c})

let mkFreshConstruct env evd c =
  mkConstructU Sigma.(apply evd {run = fun evd ->
    fresh_constructor_instance env evd c})

(* G |- t ---> |G|, x1, x2 |- [x1,x2] in |t| *)
let rec relation :
  type r. _ -> _ -> constr -> r Sigma.t -> (constr, r) sigma_ =
  fun order env t evd ->
  debug_string [`Relation] (Printf.sprintf "relation %d env t evd" order);
  debug_evar_map [`Relation]  "evd =" (Sigma.to_evar_map evd);
  debug [`Relation] "input =" env (Sigma.to_evar_map evd) t;
  let Sigma (res, evd, p) = match kind t with
    | Sort s -> let res = fold_nat (fun _ -> mkArrow (mkRel order)
                                   ) (prop_or_type env evd t) order
                in Sigma (res, evd, Sigma.refl)
    | Prod (x, a, b) ->
        let Sigma (a_R, evd, p) = relation order env a evd in
        (* |G|, x1, x2 |- [x1,x2] in |a| *)
        let a_R = liftn order (order + 1) a_R in
        (*|G|, f1, f2, x1, x2 |- [x1,x2] in |a| *)
        let env = push_rel (LocalAssum (x, a)) env in
        let Sigma (b_R, evd, q) = relation order env b evd in
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
        Sigma (compose_prod prods (mkProd (x_R, a_R, b_R)), evd, p +> q)
        (* |G|, f1, f2 |- forall x_1, x_2, x_R, [f1 x1, f2 x2] in |b| *)
    | _ ->
        let Sigma (t_R, evd, p) = translate order env t evd in
        debug_string [`Relation] (Printf.sprintf "t_R has cast : %b" (has_cast t_R));
        let t_R = lift order t_R in
        debug_string [`Relation] (Printf.sprintf "t_R lifted has cast : %b" (has_cast t_R));
        Sigma (apply_head_variables t_R order, evd, p)
  in
  if !debug_mode && List.exists (fun x -> List.mem x [`Relation]) debug_flag then begin
      debug_string [`Relation] (Printf.sprintf "exit relation %d env t evd" order);
      debug_evar_map [`Relation]  "evd =" (Sigma.to_evar_map evd);
      debug [`Relation] "input =" env (Sigma.to_evar_map evd) t;
      debug_string [`Relation] (Printf.sprintf "input has cast : %b" (has_cast t));
      debug_mode := false;
      let Sigma (env_R, _, _) = translate_env order env evd in
      let lams = range (fun k -> LocalAssum (Anonymous, lift k (prime order k t))) order in
      let env_R = Environ.push_rel_context lams env_R in
      debug_mode := true;
      debug [`Relation] "output =" env_R (Sigma.to_evar_map evd) res;
      debug_string [`Relation] (Printf.sprintf "output has cast : %b" (has_cast res))
    end;
  Sigma (res, evd, p)

(* G |- t ---> |G| |- |t| *)
and translate : type r. _ -> _ -> _ -> r Sigma.t -> (constr, r) sigma_ =
  fun order env t evd ->
  let Sigma (res, evd, p) = match kind t with
    | Rel n -> Sigma (mkRel ( (n - 1) * (order + 1) + 1), evd, Sigma.refl)

    | Sort _ | Prod (_,_,_) ->
        (* [..., _ : t'', _ : t', _ : t] *)
        let lams = range (fun k -> (Anonymous, lift k (prime order k t
                         ))) order in
        let Sigma (rt, evd, p) = relation order env t evd in
        Sigma (compose_lam lams rt, evd, p)

    | App (c,l) ->
        let l = List.rev (Array.to_list l) in
        let Sigma (ll_R, evd, p) = sigma_list_map (fun x -> {run = fun evd ->
           let Sigma (tx, evd, p) = translate order env x evd in
           Sigma (tx :: range (fun k -> prime order k x) order,
                  evd, p)}) l evd in
        let l_R = List.flatten ll_R in
        let Sigma (tc, evd, q) = translate order env c evd in
        Sigma (applist (tc, List.rev l_R), evd, p +> q)

    | Var i -> translate_variable order env i evd
    | Meta n -> not_implemented ~reason:"meta" env (Sigma.to_evar_map evd) t
    | Cast (c, k, t) ->
        let Sigma (c_R, evd, p) = translate order env c evd in
        let Sigma (t_R, evd, q) = relation order env t evd in
        let sub = range (fun k -> prime order k c) order in
        let t_R = substl sub t_R in
        Sigma (mkCast (c_R, k, t_R), evd, p +> q)

    | Lambda (x, a, m) ->
        let lams = range (fun k ->
          (prime_name order k x, lift k (prime order k a))) order
        in
        let x_R = translate_name order x in
        let Sigma (a_R, evd, p1) = relation order env a evd in
        let env = push_rel (LocalAssum (x, a)) env in
        let Sigma (tm, evd, p2) = translate order env m evd in
        Sigma (compose_lam lams (mkLambda (x_R, a_R, tm)), evd,
               p1 +> p2)

    | LetIn (x, b, t, c) ->
       let Sigma (tb, evd, p1) = translate order env b evd in
       let Sigma (rt, evd, p2) = relation order env t evd in
       let env = push_rel (LocalDef (x, b, t)) env in
       let Sigma (tc, evd, p3) = translate order env c evd in
       let res = fold_nat (fun k acc -> mkLetIn (prime_name order k x,
                                                 lift k (prime order k b),
                                                 lift k (prime order k t), acc))
                          (mkLetIn (translate_name order x,
                                    lift order tb, rt, tc))
                          order in
       Sigma (res, evd, p1 +> p2 +> p3)

    | Const c -> translate_constant order env c evd

    | Fix _ -> translate_fix order env t evd

    | Ind indu -> translate_inductive order env indu evd

    | Construct cstru -> translate_constructor order env cstru evd

    | Case (ci , p, c, bl) ->
        let nargs, nparams = Inductiveops.inductive_nrealargs ci.ci_ind, Inductiveops.inductive_nparams ci.ci_ind in
        let theta = mkCase (ci, lift (nargs + 1) p, mkRel 1, Array.map (lift (nargs + 1)) bl) in
        debug_case_info [`Case] ci;
        debug [`Case] "theta (in translated env) = " Environ.empty_env (Sigma.to_evar_map evd) theta;
        debug_string [`Case] (Printf.sprintf "nargs = %d, params = %d" nargs nparams);
        let ci_R = translate_case_info order env ci in
        debug_case_info [`Case] ci_R;
        debug [`Case] "p:" env (Sigma.to_evar_map evd) p;
        let lams, t = decompose_lam_n_assum (nargs + 1) p in
        let env_lams = Environ.push_rel_context lams env in
        debug [`Case] "t:" env_lams (Sigma.to_evar_map evd) t;
        let Sigma (t_R, evd, p1) = relation order env_lams t evd in
        debug [`Case] "t_R:" Environ.empty_env (Sigma.to_evar_map evd) t_R;
        let sub = range (fun k -> prime order k theta) order in
        debug_string [`Case] "substitution :"; List.iter (debug [`Case] "" Environ.empty_env (Sigma.to_evar_map evd)) sub;
        let t_R = substl sub t_R in
        debug [`Case] "t_R" Environ.empty_env (Sigma.to_evar_map evd) t_R;
        let Sigma (lams_R, evd, p2) =
          translate_rel_context order env lams evd in
        let p_R = it_mkLambda_or_LetIn t_R lams_R in
        let Sigma (c_R, evd, p3) = translate order env c evd in
        let Sigma (bl_R, evd, p4) =
          sigma_array_map
            (fun t -> {run = fun evd -> translate order env t evd}) bl
            evd in
        let tuple = (ci_R, p_R, c_R, bl_R) in
        Sigma (mkCase tuple, evd, p1 +> p2 +> p3 +> p4)

    | CoFix _ -> translate_cofix order env t evd

    | Proj (p, c) ->
       let Sigma (tc, evd, q) = translate order env c evd in
       let proj = mkProj (Projection.map (fun cte ->
                              Globnames.destConstRef
                                (Relations.get_constant order cte)) p,
                          tc) in
       Sigma (proj, evd, q)
    | _ -> not_implemented ~reason:"trapfall" env (Sigma.to_evar_map evd) t
 in
  if !debug_mode && List.exists (fun x -> List.mem x [`Translate]) debug_flag then begin
    debug_string [`Translate] (Printf.sprintf "exit translate %d env t evd" order);
    debug_evar_map [`Translate]  "evd =" (Sigma.to_evar_map evd);
    debug [`Translate] "input =" env (Sigma.to_evar_map evd) t;
    debug_string [`Translate] (Printf.sprintf "input has cast : %b" (has_cast t));
    debug_mode := false;
    let Sigma (env_R, _, _) = translate_env order env evd in
    debug_mode := true;
    debug [`Translate] "output =" env_R (Sigma.to_evar_map evd) res;
    debug_string [`Translate] (Printf.sprintf "output has cast : %b" (has_cast res))
  end;
  Sigma (res, evd, p)

and translate_constant :
  type r. _ -> _ -> _ -> r Sigma.t -> (constr, r) sigma_ =
  fun order env ucst evd ->
  let cst, names = ucst in
  try
    Sigma.fresh_global ~rigid:Evd.univ_rigid ~names env evd
                         (Relations.get_constant order cst)
  with Not_found ->
      let cb = lookup_constant cst env in
      Declarations.(match cb.const_body with
        | Def _ ->
            let (value, constraints) = Environ.constant_value env ucst in
            let Sigma (_, evd, p) =
              unsafe0_ (fun evd -> Evd.add_constraints evd constraints) evd in
            let Sigma (tvalue, evd, q) = translate order env value evd in
            Sigma (tvalue, evd, p +> q)
        | OpaqueDef op ->
            let table = Environ.opaque_tables env in
            let typ = Typeops.type_of_constant_in env ucst in
            let cte_constraints = Declareops.constraints_of_constant table cb in
            let cte_constraints = Univ.subst_instance_constraints names
               cte_constraints in
            let Sigma (_, evd, p1) =
              unsafe0_ (fun evd -> Evd.add_constraints evd cte_constraints) evd in
            let fold = mkConstU ucst in
            let def = Opaqueproof.force_proof table op in
            let _ = Opaqueproof.force_constraints table op in
            let def = subst_instance_constr names def in
            let Sigma (rtyp, evd, p2) = relation order env typ evd in
            let pred = mkLambda (Anonymous, typ,
                                 substl (range (fun _ -> mkRel 1) order) rtyp) in
            let Sigma (res, evd, p3) = translate order env def evd in
            let Sigma (uf_opaque_stmt, evd, p4) =
              CoqConstants.eq [| typ; def; fold|] evd in
            let Sigma (sort, evd, p5) = sigma_sort_of env typ evd in
            let Sigma (proof_opaque, evd, p6) =
              try
                if is_prop_sort sort then
                  (debug [`ProofIrrelevance] "def =" env (Sigma.to_evar_map evd) def;
                  debug [`ProofIrrelevance] "fold =" env (Sigma.to_evar_map evd) fold;
                  let Sigma (pi, evd, p6) =
                    CoqConstants.proof_irrelevance [| typ; def; fold |] evd in
                  Sigma (pi, evd, p6))
                else
                  raise Not_found
              with e ->
                debug_string [`ProofIrrelevance] (Printexc.to_string e);
                let Sigma (hole, evd, p6) =
                  Evarutil.new_evar Environ.empty_env evd uf_opaque_stmt in
                let Sigma (_, evd, p7) =
                  CoqConstants.add_constraints (mkSort sort) evd in
                Sigma (hole, evd, p6 +> p7)
            in
            let Sigma (t, evd, p7) = CoqConstants.transport
                 [| typ; def; pred; res; fold; proof_opaque |] evd in
            Sigma (t, evd, p1 +> p2 +> p3 +> p4 +> p5 +> p6 +> p7)
        | _ ->  error
           (Pp.str (Printf.sprintf
                      "The constant '%s' has no registered translation."
                      (KerName.to_string (Constant.user cst)))))

and translate_rel_context :
  type r. _ -> _ -> _ -> r Sigma.t -> (_, r) sigma_ =
  fun order env rc evd ->
  let Sigma ((_, ll), evd, p) =
    sigma_fold_right (fun decl (env, acc) -> {run = fun evd ->
        let (x, def, typ) = to_tuple decl in
        let x_R = translate_name order x in
        let Sigma (def_R, evd, p1) = match def with
            None -> Sigma (None, evd, Sigma.refl)
          | Some d -> let Sigma (td, evd, p) = translate order env d evd in
                        Sigma (Some td, evd, p) in
        let Sigma (typ_R, evd, p2) = relation order env typ evd in
        let l : Context.Rel.t = range (fun k -> of_tuple
                                                  (prime_name order k x,
                                                   Option.map (fun x -> lift k (prime order k x)) def,
                                                   lift k (prime order k typ))) order
        in
        let env = push_rel decl env in
        let pair = env, (Context.Rel.add (of_tuple (x_R,
           Option.map (lift order) def_R, typ_R)) l) :: acc in
        Sigma (pair, evd, p1 +> p2)
                     })  ~init:(env, []) rc evd
  in
  Sigma (List.flatten ll, evd, p)


and translate_variable :
  type r. _ -> _ -> _ -> r Sigma.t -> (constr, r) sigma_ =
  fun order env v evd ->
  try
    Sigma (Constr.mkConst (Relations.get_variable order v), evd, Sigma.refl)
  with Not_found ->
    error
      (Pp.str (Printf.sprintf "The variable '%s' has no registered translation, provide one with the Realizer command." (Names.Id.to_string v)))

and translate_inductive :
  type r. _ -> _ -> _ * _ -> r Sigma.t -> (_, r) sigma_ =
  fun order env (ind, names) evd ->
  try
    Sigma.fresh_global ~rigid:Evd.univ_rigid ~names
                       env evd (Relations.get_inductive order ind)
       with Not_found -> error (Pp.str (Printf.sprintf "The inductive '%s' has no registered translation."
    (KerName.to_string (MutInd.user (fst ind)))))

and translate_constructor :
  type r. _ -> _ -> ((_ * _) * _) -> r Sigma.t -> (_, r) sigma_ =
  fun order env ((ind, i), u) evd ->
  let Sigma (ti, evd, p) = translate_inductive order env (ind,u) evd in
  let (ind, u) = destInd ti in
  Sigma (mkConstructU ((ind, i), u), evd, p)

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

and translate_cofix :
  type r. _ -> _ -> _ -> r Sigma.t -> (_, r) sigma_ =
  fun order env t evd ->
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
  let nrealargs = Array.map (fun x -> Context.Rel.nhyps (fst (decompose_lam_assum x))) bl in
  (* [lna_R] is the translation of names of each fixpoints. *)
  let lna_R = Array.map (translate_name order) lna in
  let Sigma (ftbk_R, evd, p) = sigma_array_mapi (fun i x -> {run = fun evd ->
    let narg = nrealargs.(i) in
    let ft, bk = decompose_prod_n_assum_by_prod narg x in
    let Sigma (ft_R, evd, p) = translate_rel_context order env ft evd in
    let env_ft = push_rel_context ft env in
    let Sigma (bk_R, evd, q) = relation order env_ft bk evd in
     Sigma ((ft, ft_R, bk, bk_R), evd, p +> q)}) tl evd
  in
  let tl_R = Array.mapi (fun n (ft, ft_R, bk, bk_R) ->
     (* bk_R is well-typed in | G, ft|, x_1 : bk_1, x_2 : bk_R *)
     (* we lift it to insert the [nfun * order] letins. *)
     let ft_R_len = Context.Rel.length ft_R in
     let bk_R = liftn (nfun * order) (ft_R_len + order + 1) bk_R in
     let sub = range (fun k ->
                  mkApp (mkRel (ft_R_len + (nfun - n)*order - k ),
                     Array.map (prime order k) (Rel.to_extended_vect 0 ft)))
               order
     in
     it_mkProd_or_LetIn (substl sub bk_R)
       (Termops.lift_rel_context (nfun * order) ft_R)) ftbk_R
  in

  (* env_rec is the environement under fipoints. *)
  let env_rec = push_rec_types (lna, tl, bl) env in
  (* n : fix index *)
  let process_body n : constr run_ = {run = fun evd ->
    let lams, body = decompose_lam_assum bl.(n) in
    let env_lams = push_rel_context lams env_rec in
    let narg = Context.Rel.length lams in
    let Sigma (body_R, evd, p1) = translate order env_lams body evd in
    let (ft, ft_R, bk, bk_R) = ftbk_R.(n) in
    let theta = mkApp (mkRel (nfun - n + narg), Rel.to_extended_vect 0 lams) in
    (* lift to insert fixpoints variables before arguments
     * plus possible letins that were not in the type.
     * *)
    let nfun_letins = nfun + narg - nrealargs.(n) in
    let bk = liftn nfun_letins (narg + 1) bk in
    let bk_R = liftn (nfun_letins * (order + 1)) ((order + 1) * narg + order + 1) bk_R in
    (* narg is the position of fixpoints in env *)
    let Sigma (body_R, evd, p2) =
      rewrite_cofixpoints order env_lams narg fix body
                          theta bk bk_R body_R evd in
    let Sigma (lams_R, evd, p3) =
      translate_rel_context order env_rec lams evd in
    let res = it_mkLambda_or_LetIn body_R lams_R in
    if List.exists (fun x -> List.mem x [`Fix]) debug_flag then begin
      let Sigma (env_R, _, _) = translate_env order env_rec evd in
      debug [`Fix] "res = " env_R (Sigma.to_evar_map evd) res;
    end;
    Sigma (res, evd, p1 +> p2 +> p3)}
  in
  let Sigma (bl_R, evd, q) = sigma_array_init nfun process_body evd in
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
    let Sigma (env_R, _, _) = translate_env order env evd in
    debug [`Fix] "cofix res = " env_R (Sigma.to_evar_map evd) res;
  end;
  Sigma (res, evd, p +> q)

and translate_fix :
  type r. _ -> _ -> _ -> r Sigma.t -> (_, r) sigma_ =
  fun order env t evd ->
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
  let nrealargs = Array.map (fun x -> Context.Rel.nhyps (fst (decompose_lam_assum x))) bl in
  (* [ln_R] is the translation of ln, the array of arguments for each fixpoints. *)
  let ln_R = (Array.map (fun x -> x*(order + 1) + order) ri, i) in
  (* [lna_R] is the translation of names of each fixpoints. *)
  let lna_R = Array.map (translate_name order) lna in
  let Sigma (ftbk_R, evd, p1) = sigma_array_mapi (fun i x -> {run = fun evd ->
    let narg = nrealargs.(i) in
    let ft, bk = decompose_prod_n_assum_by_prod narg x in
    let Sigma (ft_R, evd, p1)  = translate_rel_context order env ft evd in
    let env_ft = push_rel_context ft env in
    let Sigma (bk_R, evd, p2) = relation order env_ft bk evd in
     Sigma ((ft, ft_R, bk, bk_R), evd, p1 +> p2)}) tl evd
  in
  let tl_R = Array.mapi (fun n (ft, ft_R, bk, bk_R) ->
     (* bk_R is well-typed in | G, ft|, x_1 : bk_1, x_2 : bk_R *)
     (* we lift it to insert the [nfun * order] letins. *)
     let ft_R_len = Context.Rel.length ft_R in
     let bk_R = liftn (nfun * order) (ft_R_len + order + 1) bk_R in
     let sub = range (fun k ->
                  mkApp (mkRel (ft_R_len + (nfun - n)*order - k ),
                     Array.map (prime order k) (Rel.to_extended_vect 0 ft)))
               order
     in
     it_mkProd_or_LetIn (substl sub bk_R)
     (Termops.lift_rel_context (nfun * order) ft_R)) ftbk_R
  in
  (* env_rec is the environement under fipoints. *)
  let env_rec = push_rec_types (lna, tl, bl) env in
  (* n : fix index *)
  let process_body n : constr run_ = {run = fun evd ->
    let lams, body = decompose_lam_assum bl.(n) in
    let narg = Context.Rel.length lams in
    (* rec_arg gives the position of the recursive argument *)
    let rec_arg = narg - (fst ln).(n) in
    let args = Context.Rel.to_extended_list 0 lams in
    let Sigma (lams_R, evd, p1) =
      translate_rel_context order env_rec lams evd in
    let env_lams = push_rel_context lams env_rec in
    let inst_args depth args =
      mkApp (mkRel (depth + nfun - n + narg), Array.of_list args)
    in
    (* we use this complicated function to translate the
     * shallow cases just after a lambda (the goal is to
     * avoid as much as possible rewriting).
     * *)
    let rec traverse_cases :
      type r. _ -> _ -> constr list -> _ -> _ -> _ ->
          r Sigma.t -> (constr, r) sigma_ =
      fun env depth args typ typ_R term evd ->
      match kind term with
        | Case (ci , p, c, branches) when
               test_admissible env c args p branches evd ->
            process_case env depth args term evd
        | _ ->
            (* otherwise we have to perform some rewriting. *)
            debug [`Fix] "c = " env (Sigma.to_evar_map evd) term;
            debug [`Fix] "typ = " env (Sigma.to_evar_map evd) typ;
            let Sigma (term_R, evd, p)  = translate order env term evd in
            let theta = inst_args depth args in
            (* depth + narg is the position of fixpoints in env *)
            let Sigma (rfix, evd, q) =
              rewrite_fixpoints order env (depth + narg) fix term theta
                                typ typ_R term_R evd in
            Sigma (rfix, evd, p +> q)

    and test_admissible :
      type r. _ -> _ -> _ -> _ -> _ -> r Sigma.t -> bool =
      fun env c args predicate branches evd ->
      isRel c && List.mem c args &&
        Array.for_all (Vars.noccurn (destRel c)) branches &&
          let typ = Retyping.get_type_of env (Sigma.to_evar_map evd) c in
          debug [`Fix] "typ = " env (Sigma.to_evar_map evd) typ;
          List.iteri (fun i x ->
              debug [`Fix] (Printf.sprintf "args.(%d) = " i) env
                    (Sigma.to_evar_map evd) x) args;
          let (ind, u), ind_args =
            Inductiveops.find_inductive env (Sigma.to_evar_map evd) typ in
          let nparams = Inductiveops.inductive_nparams ind in
          let _, realargs = List.chop nparams ind_args in
          List.iteri (fun i x ->
              debug [`Fix] (Printf.sprintf "realargs.(%d) = " i) env
                    (Sigma.to_evar_map evd) x) realargs;
          List.for_all (fun x -> List.mem x args) realargs

    and process_case :
      type r. _ -> _ -> constr list -> _ -> r Sigma.t -> (_, r) sigma_ =
        fun env depth fun_args case evd ->
        debug [`Fix] "case = " env (Sigma.to_evar_map evd) case;
        let (ci, p, c, bl) = destCase case in
        debug [`Fix] "predicate = " env (Sigma.to_evar_map evd) p;
        let Sigma (c_R, evd, p1) = translate order env c evd in
        let ci_R = translate_case_info order env ci in
        let c_typ = Retyping.get_type_of env (Sigma.to_evar_map evd) c in
        debug [`Fix] "c_typ = " env (Sigma.to_evar_map evd) c_typ;
        let ((ind, u) as pind, params_args)  =
          Inductiveops.find_inductive env (Sigma.to_evar_map evd) c_typ
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
        debug [`Fix] "theta = " (push_rel_context lams env) (Sigma.to_evar_map evd) theta;
        debug [`Fix] "theta = " Environ.empty_env (Sigma.to_evar_map evd) theta;
        let Sigma (lams_R, evd, p2) = translate_rel_context order env lams evd in
        let env_lams = Environ.push_rel_context lams env in
        let Sigma (typ_R, evd, p3) = relation order env_lams typ evd in
        let p_R = substl sub typ_R in
        let p_R = it_mkLambda_or_LetIn p_R lams_R in
        debug [`Fix] "predicate_R = " Environ.empty_env (Sigma.to_evar_map evd) p_R;
        let Sigma (bl_R, evd, p4) =
          debug_string [`Fix] (Printf.sprintf "dest_rel = %d" (destRel c));
          debug_string [`Fix] (Printf.sprintf "depth = %d" depth);
          debug_string [`Fix] (Printf.sprintf "barg = %d" narg);
          debug_string [`Fix] (Printf.sprintf "fst ln = %d" (fst ln).(n));
          debug_string [`Fix] (Printf.sprintf "rec_arg = %d" rec_arg);
          if (destRel c) = depth + rec_arg then
            sigma_array_map (fun x -> {run = fun evd ->
                                             translate order env x evd}) bl evd
          else begin
            sigma_array_mapi (fun i b -> {run = fun evd ->
               let (cstr, u) as cstru = constructors.(i).Inductiveops.cs_cstr in
               let pcstr = mkConstructU cstru in
               let nrealdecls = Inductiveops.constructor_nrealdecls cstr in
               let realdecls, b = decompose_lam_n_assum nrealdecls b in
               let lifted_i_params = List.map (lift nrealdecls) i_params in
               let instr_cstr =
                 mkApp (pcstr,
                        Array.of_list
                         (List.append lifted_i_params
                           (Context.Rel.to_extended_list 0 realdecls)))
               in
               let concls = constructors.(i).Inductiveops.cs_concl_realargs in
               assert (Array.length concls = i_nargs);
               let fun_args =
                List.map (fun x -> if x = c then instr_cstr
                             else if List.mem x i_realargs then concls.(i_nargs - (List.index (=) x i_realargs))
                             else lift nrealdecls x) fun_args
               in
               let Sigma (realdecls_R, evd, p1) =
                 translate_rel_context order env realdecls evd in
               let sub = instr_cstr::(List.rev (Array.to_list concls)) in
               let typ = substl sub typ in
               (* FIXME : translate twice here :*)
               let Sigma (typ_R, evd, p2) =
                 relation order env_lams typ evd in
               let env = push_rel_context realdecls env in
               let Sigma (b_R, evd, p3) =
                 traverse_cases env (depth + nrealdecls)
                                fun_args typ typ_R b evd in
               Sigma (it_mkLambda_or_LetIn b_R realdecls_R, evd, p1 +> p2 +> p3)
                             }) bl evd
          end
        in
        Sigma (mkCase (ci_R, p_R, c_R, bl_R), evd, p1 +> p2 +> p3 +> p4)
    in
    let (_, ft_R, bk, bk_R) = ftbk_R.(n) in
    let nfun_letins = nfun + narg - nrealargs.(n) in
    (* lift to insert fixpoints variables before arguments
     * plus possible letins that were not in the type.
     * *)
    let bk = liftn nfun_letins (narg + 1) bk in
    let bk_R = liftn (nfun_letins * (order + 1)) ((order + 1) * narg + order + 1) bk_R in
    let Sigma (body_R, evd, p2) =
      traverse_cases env_lams 0 args bk bk_R body evd in
    let res = it_mkLambda_or_LetIn body_R lams_R in
    if List.exists (fun x -> List.mem x [`Fix]) debug_flag then begin
      let Sigma (env_R, _, _) = translate_env order env_rec evd in
      debug [`Fix] "res = " env_R (Sigma.to_evar_map evd) res;
    end;
    Sigma (res, evd, p1 +> p2)}
  in
  let Sigma (bl_R, evd, p2) = sigma_array_init nfun process_body evd in
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
  Sigma (letfixs nfun res, evd, p1 +> p2)

(* for debugging only  *)
and translate_env : 'r. _ -> _ -> 'r Sigma.t -> (_, 'r) sigma_ =
  fun order env evd  ->
  let init_env = Environ.reset_context env in
  let Sigma (rc, evd, p) =
    translate_rel_context order init_env (Environ.rel_context env) evd in
  Sigma (push_rel_context rc init_env, evd, p)

(* Γ ⊢ source : typ
 * Γ ⊢ target : typ
 * ⟦Γ⟧, typ₁, typ₂ ⊢ typ_R : Type
 *
 * builds :
 *
 *
 * *)
and rewrite_fixpoints :
  type r. _ -> _ -> int -> fixpoint -> _ -> _ ->
                        _ -> _ -> _ -> r Sigma.t -> (_, r) sigma_ =
  fun order env depth fix source target typ typ_R acc evd ->
  debug [`Fix] "source =" env (Sigma.to_evar_map evd) source;
  debug [`Fix] "target =" env (Sigma.to_evar_map evd) target;
  debug [`Fix] "typ =" env (Sigma.to_evar_map evd) typ;
  if List.exists (fun x -> List.mem x [`Fix]) debug_flag then begin
    let Sigma (env_R, _, _) = translate_env order env evd in
    let rc_order = rev_range (fun k ->
                       LocalAssum ((Name (id_of_string (Printf.sprintf "rel_%d" k))),
                       lift k (prime order k typ))) order in
    let env_R = push_rel_context rc_order env_R in
    debug [`Fix] "typ_R =" env_R (Sigma.to_evar_map evd) typ_R
  end;
  let instantiate_fixpoint_in_rel_context rc =
    let (ri, k), stuff = fix in
    let pos = depth in
    let nfun = Array.length ri in
    let front, back = List.chop pos rc in
    let funs, back = List.chop nfun back in
    let fixs = List.mapi (fun i -> function LocalAssum (name, typ) ->
      LocalDef (name, (mkFix ((ri, nfun - 1 - i), stuff)), typ) | _ -> assert false) funs in
    front @ fixs @ back
  in
  let env_rc = Environ.rel_context env in
  let env_rc = instantiate_fixpoint_in_rel_context env_rc in
  let Sigma (path, evd, p1) = CoqConstants.eq [| typ; source; target|] evd in
  let gen_rc, new_vec, path = weaken_unused_free_rels env_rc path in
  let gen_path = it_mkProd_or_LetIn path  gen_rc in
  debug [`Fix] "gen_path_type" Environ.empty_env (Sigma.to_evar_map evd) gen_path;
  let Sigma (hole, evd, p2) =
    Evarutil.new_evar Environ.empty_env evd gen_path in
  let let_gen acc = mkLetIn (Name (id_of_string "gen_path"), hole, gen_path, acc) in
  let Sigma (fn, evd, p3) =
    (sigma_fold_nat (fun k acc -> {run = fun evd ->
    let pred_sub =
      (range (fun x -> lift 1 (prime order (k+1+x) target)) (order-1 - k))
      @ [ mkRel 1 ]
      @ (range (fun x -> lift 1 (prime order x source)) k)
    in
    let sort = Retyping.get_type_of env (Sigma.to_evar_map evd) typ in
    let Sigma (_, evd, p1) = CoqConstants.add_constraints sort evd in
    let index = lift 1 (prime order k typ) in
    let pred = mkLambda (Name (id_of_string "x"), index, liftn 1 2 (substl pred_sub (liftn 1 (order + 1) typ_R))) in
    let base = lift 1 (prime order k source) in
    let endpoint = lift 1 (prime order k target) in
    let path = mkApp (mkRel 1,
       Array.map (fun x -> lift 1 (prime order k x)) new_vec)
    in
    let Sigma (t, evd, p2) = CoqConstants.transport
          [| index;
             base;
             pred; acc; endpoint; path |] evd in
    Sigma (t, evd, p1 +> p2)}) (lift 1 acc) order evd) in
  Sigma (let_gen @@ fn, evd, p1 +> p2 +> p3)

and weaken_unused_free_rels env_rc term =
  (* Collect the dependencies with [vars] in a rel_context. *)
   let rec collect_free_vars k vars = function
     | [] -> vars
     | decl::tl when Int.Set.mem k vars ->
       let fv =
          match decl with
             LocalAssum (_, typ) ->
               Termops.free_rels typ
           | LocalDef (_, def, typ) ->
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
   let new_vec = Context.Rel.to_extended_list 0 env_rc in
   let new_vec = List.filter (fun x -> let v = destRel x in Int.Set.mem v set) new_vec in
   let new_vec = Array.of_list new_vec in
   assert (Array.length new_vec == Context.Rel.nhyps new_env_rc);
   new_env_rc, new_vec, substl sub term

and rewrite_cofixpoints :
  type r. _ -> _ -> int -> cofixpoint -> _ -> _ -> _ -> _ -> _ ->
  r Sigma.t -> (constr, r) sigma_ =
  fun order env depth fix source target typ typ_R acc evd ->
  debug [`Fix] "source =" env (Sigma.to_evar_map evd) source;
  debug [`Fix] "target =" env (Sigma.to_evar_map evd) target;
  debug [`Fix] "typ =" env (Sigma.to_evar_map evd) typ;
  if List.exists (fun x -> List.mem x [`Fix]) debug_flag then begin
    let Sigma (env_R, _, _) = translate_env order env evd in
    let rc_order = rev_range (fun k -> LocalAssum ((Name (id_of_string (Printf.sprintf "rel_%d" k))),
                         lift k (prime order k typ))) order in
    let env_R = push_rel_context rc_order env_R in
    debug [`Fix] "typ_R =" env_R (Sigma.to_evar_map evd) typ_R
  end;
  let instantiate_fixpoint_in_rel_context rc =
    let index, ((lna, _, _) as stuff) = fix in
    let pos = depth in
    let nfun = Array.length lna in
    let front, back = List.chop pos rc in
    let funs, back = List.chop nfun back in
    let fixs = List.mapi (fun i -> function LocalAssum (name, typ) ->
      LocalDef (name, mkCoFix ((nfun - 1 - index), stuff), typ) | _ -> assert false) funs in
    front @ fixs @ back
  in
  let env_rc = Environ.rel_context env in
  let env_rc = instantiate_fixpoint_in_rel_context env_rc in
  let Sigma (eq, evd, p1) = CoqConstants.eq [| typ; source; target|] evd in
  let gen_path = it_mkProd_or_LetIn eq env_rc in
  debug [`Fix] "gen_path_type" env (Sigma.to_evar_map evd) gen_path;
(* :TODO: Warning, this code should be ported to the new state safe sigma API *)
  let Sigma (hole, evd, p2) =
    Evarutil.new_evar Environ.empty_env evd gen_path in
  let let_gen acc = mkLetIn (Name (id_of_string "gen_path"), hole, gen_path, acc) in
  let Sigma (fn, evd, p3) = sigma_fold_nat (fun k acc -> {run = fun evd ->
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
        (Rel.to_extended_vect 0 env_rc))
    in
    let sort = Retyping.get_type_of env (Sigma.to_evar_map evd) typ in
    let Sigma (_, evd, p1) = CoqConstants.add_constraints sort evd in
    let Sigma (r, evd, p2) = CoqConstants.transport
          [| index;
             base;
             pred; acc; endpoint; path |] evd in
    Sigma (r, evd, p1 +> p2)}) (lift 1 acc) order evd in
  Sigma (let_gen @@ fn, evd, p1 +> p2 +> p3)

open Entries
open Declarations

let map_local_entry f = function
  | LocalDefEntry c -> LocalDefEntry (f c)
  | LocalAssumEntry c -> LocalAssumEntry (f c)

let constr_of_local_entry = function LocalDefEntry c | LocalAssumEntry c -> c

(* Translation of inductives. *)

let rec translate_mind_body :
  type r. _ -> _ -> _ -> _ -> _ -> _ -> r Sigma.t -> (_, r) sigma_ =
  fun name order env kn b inst evd ->
  let env = push_context b.mind_universes env in

  debug_string [`Inductive] "computing envs ...";
  debug_env [`Inductive] "translate_mind, env = \n" env (Sigma.to_evar_map evd);
  debug_evar_map [`Inductive] "translate_mind, evd = \n" (Sigma.to_evar_map evd);
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
        let env = Environ.push_rel (LocalAssum (Names.Name typename, full_arity)) env in
        let env = Environ.add_constraints cst env in
        env
      ) env (Array.to_list b.mind_packets)
    in
    let env_arities_params = push_rel_context params env_arities in
    (env_params, params, env_arities, env_arities_params)
  in

  debug_string [`Inductive] "translatation of params ...";
  let Sigma (mind_entry_params_R, evd, p1) =
    translate_mind_param order env
      (subst_instance_context inst b.mind_params_ctxt) evd
  in
  debug_string [`Inductive] "translatation of inductive ...";
  let Sigma (mind_entry_inds_R, evd, p2) =
    sigma_list_mapi
      (fun i x -> {run = fun evd ->
         translate_mind_inductive name order env (kn,i) b inst envs x evd})
      (Array.to_list b.mind_packets) evd
  in
  debug_evar_map [`Inductive] "translate_mind, evd = \n" (Sigma.to_evar_map evd);
  let ctx = Evd.universe_context (Sigma.to_evar_map evd) in
  let res = {
    mind_entry_record = None;
    mind_entry_finite = b.mind_finite;
    mind_entry_params = mind_entry_params_R;
    mind_entry_inds = mind_entry_inds_R;
    mind_entry_polymorphic = b.mind_polymorphic;
    mind_entry_universes = snd ctx;
    mind_entry_private = b.mind_private
  } in
  Debug.debug_mutual_inductive_entry (Sigma.to_evar_map evd) res;
  Sigma (res, evd, p1 +> p2)

and translate_mind_param :
  type r. _ -> _ -> _ -> r Sigma.t -> (_, r) sigma_ =
  fun order env (l : Context.Rel.t) evd ->
  let rec aux : type r. _ -> _ -> _ -> r Sigma.t -> (_, r) sigma_ =
    fun env acc l evd -> match l with
     | [] -> Sigma (acc, evd, Sigma.refl)
     | LocalDef (x, def, hd)::tl ->
        let Sigma (tdef, evd, p) = translate order env def evd in
        let x_R = (translate_name order x, LocalDefEntry tdef) in
        (* Cyril: hd is not translated, bug? *)
        let env = push_rel (LocalDef (x, def, hd)) env in
        let x_i = range (fun k ->
          (prime_name order k x,
           LocalDefEntry (lift k (prime order k def)))) order in
        let acc = (x_R::x_i):: acc in
        let Sigma (auxres, evd, q) = aux env acc tl evd in
        Sigma (auxres, evd, p +> q)
     | LocalAssum (x,hd)::tl ->
        let Sigma (thd, evd, p) = relation order env hd evd in
        let x_R = (translate_name order x, LocalAssumEntry thd) in
        let env = push_rel (LocalAssum (x, hd)) env in
        let x_i = range (fun k ->
          (prime_name order k x,
           LocalAssumEntry (lift k (prime order k hd)))) order in
        let acc = (x_R::x_i):: acc in
        let Sigma (auxres, evd, q) = aux env acc tl evd in
        Sigma (auxres, evd, p +> q)
  in
  let l = List.rev l in
  let Sigma (auxres, evd, p) = aux env [] l evd in
  Sigma(List.map (function (Name x,c) -> (x, c) |
                     _ -> failwith "anonymous param")
           (List.flatten auxres),
        evd, p)

and translate_mind_inductive :
  type r. _ -> _ -> _ -> _ -> _ -> _ ->
       (_ * _ * _ * _) -> _ -> r Sigma.t -> (_, r) sigma_ =
  fun name order env ikn mut_entry inst
      (env_params, params, env_arities, env_arities_params) e evd ->
  let p = List.length mut_entry.mind_params_ctxt in
  Debug.debug_string [`Inductive] (Printf.sprintf "mind_nparams = %d" mut_entry.mind_nparams);
  Debug.debug_string [`Inductive] (Printf.sprintf "mind_nparams_rec = %d" p);
  Debug.debug_string [`Inductive] (Printf.sprintf "mind_nparams_ctxt = %d" (List.length mut_entry.mind_params_ctxt));
  let _, arity =
     decompose_prod_n_assum p (Inductive.type_of_inductive env ((mut_entry, e), inst))
  in
  debug [`Inductive] "Arity:" env_params (Sigma.to_evar_map evd) arity;
  let Sigma (arity_R, evd, p1) =
      debug_string [`Inductive] "Computing arity";
      let Sigma (arity_R, evd, p1) = relation order env_params arity  evd in
      let inds = List.rev (fold_nat
         (fun k acc ->
           prime order k
            (apply_head_variables_ctxt (mkIndU (ikn, inst)) params)::acc) [] order) in
      debug_string [`Inductive] "Substitution:";
      List.iter (debug [`Inductive] "" Environ.empty_env Evd.empty) inds;
      let result = substl inds arity_R in
      if List.exists (fun x -> List.mem x [`Inductive]) debug_flag then begin
        let Sigma (env_params_R, _, _) = translate_env order env_params evd in
        debug [`Inductive] "Arity_R after substitution:" env_params_R (Sigma.to_evar_map evd) result;
      end;
      Sigma (result, evd, p1)
  in
  let trans_consname s = translate_id order (Id.of_string ((Id.to_string name)^"_"^(Id.to_string s))) in
  let Sigma (mind_entry, evd, p2) =       begin
        debug_string [`Inductive] "Computing constructors";
        let l = Array.to_list e.mind_user_lc in
        let l = List.map (subst_instance_constr inst) l in
        debug_string [`Inductive] "before translation :";
        List.iter (debug [`Inductive] "" env_arities (Sigma.to_evar_map evd)) l;
        let l =  List.map (fun x -> snd (decompose_prod_n_assum p x)) l in
        debug_string [`Inductive] "remove uniform parameters :";
        List.iter (debug [`Inductive] "" env_arities_params
                         (Sigma.to_evar_map evd)) l;
        (*
        let sub = range (fun k -> mkRel (mut_entry.mind_nparams_rec + k + 1)) mut_entry.mind_nparams_rec in
        let l = List.map (substl sub) l in
        debug_string "reverse parameters and inductive variables :";
        List.map (debug Environ.empty_env) l;*)
        let Sigma (l, evd, p2) =
          sigma_list_map (fun t -> {run = fun evd ->
              relation order env_arities_params t evd}) l evd in
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
        Sigma (result, evd, p2)
      end in
  Sigma ({
    mind_entry_typename = name;
    mind_entry_arity = arity_R;
    mind_entry_template = (match e.mind_arity with TemplateArity _ -> true | _ -> false);
    mind_entry_consnames = List.map trans_consname (Array.to_list e.mind_consnames);
    mind_entry_lc = mind_entry
  }, evd, p1 +> p2)
