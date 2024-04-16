(* LTS USING IMMUTABLE LIST *)

open Ast                 (* Term Abstract Syntax Tree *)
open Reductions_ast
open Reductions          (* Term Semantics Reduction Rules *)
open Z3api               (* Z3 Interface to for symbolic execution *)
open Upto_tools          (* Types and Functions for Upto Techniques *)
open Normalisation
open Generalisations
open Lts_ast             (* Data structures used by the LTS
                            NOTE: lts_ast.ml is openned last.
                                  upto_tools.ml has interfering definitions
                                  that would squash definitions needed here. *)

(** EXIT STATUS **)
let exit_eq = 43
let exit_ineq = 42
let exit_unknown = 0

(*** bound reached flag ***)
let bound_reached = ref false

(*** debug instrumentation ***)
let debug_traces = ref false
let print_debug_traces str =
  if !debug_traces  then
    Printf.printf "[traces] %s\n" str

let debug_confs = ref false
let print_debug_confs str =
  if !debug_confs  then
    Printf.printf "[configurations] %s\n" str

let debug_leaf_confs = ref false
let print_debug_leaf_confs str =
  if !debug_leaf_confs  then
    Printf.printf "[leaf configuration]\n%s\n\n" str

let debug_sigma = ref false
let print_debug_sigma str =
  if !debug_sigma  then
    Printf.printf "[symbolic-environment] %s\n" str

let debug_memo = ref false
let print_debug_memo str =
  if !debug_memo  then
    Printf.printf "[memoisation] %s\n" str

let debug_norm = ref false
let print_debug_norm str =
  if !debug_norm  then
    Printf.printf "[normalisation] %s\n" str

let debug_gc = ref false
let print_debug_gc str =
  if !debug_gc  then
    Printf.printf "[garbage-collection] %s\n" str

let debug_sep = ref false
let print_debug_sep str =
  if !debug_sep  then
    Printf.printf "[separation] %s\n" str

let debug_nr = ref false
let print_debug_nr str =
  if !debug_nr  then
    Printf.printf "[name-reuse] %s\n" str

let debug_id = ref false
let print_debug_id str =
  if !debug_id  then
    Printf.printf "[identity] %s\n" str

let debug_sigma_gc = ref false
let print_debug_sigma_gc str =
  if !debug_sigma_gc  then
    Printf.printf "[sigma-garbage-collection] %s\n" str

let debug_sigma_norm = ref false
let print_debug_sigma_norm str =
  if !debug_sigma_norm  then
    Printf.printf "[sigma-normalisation] %s\n" str

let debug_sigma_simp = ref false
let print_debug_sigma_simp str =
  if !debug_sigma_simp  then
    Printf.printf "[sigma-simplification] %s\n" str

let debug_generalise = ref false
let print_debug_generalise str =
  if !debug_generalise  then
    Printf.printf "[generalisation] %s\n" str

let debug_gamma_duplicates = ref false
let print_debug_gamma_duplicates str =
  if !debug_gamma_duplicates  then
    Printf.printf "[gamma-duplicates] %s\n" str

let debug_reachable_beta_graph = ref false
let print_debug_reachable_beta_graph str =
  if !debug_reachable_beta_graph  then
    Printf.printf "[reachable beta graph] %s\n" str

let debug_beta_graph_size = ref false
let print_debug_beta_graph_size str =
  if !debug_beta_graph_size  then
    Printf.printf "[beta graph size] %s\n" str

let lazy_print_debug f d =
  if !d  then f ()

(*****************
 * Bound Reached *
 *****************)
let do_bound_reached cfg_pair =
  print_debug_leaf_confs (string_of_cfg_pair cfg_pair);
  bound_reached := true

(*****************************************************
 * GARBAGE-COLLECTION, NORMALISATION AND MEMOISATION *
 *****************************************************)
(*** memoisation ***)
let flag_memo = ref false

type minimal_cfg = {min_g: value list;
                    min_s: string;
                    min_e: context_or_term}

type minimal_cfg_pair = {min_c1: minimal_cfg option;
                         min_c2: minimal_cfg option;
                         min_sigma: sigma;
                         min_bgraph: mini_beta_graph;
                         min_beta: int}

let init_memoisation_cache n =
  let dummy_cfg = Some {min_g = []; min_s = ""; min_e = dummy_ocontext} in
  let dummy_cfg_pair =
    {min_c1 = dummy_cfg;
     min_c2 = dummy_cfg;
     min_sigma = [];
     min_beta = mini_beta_init;           (** EXPERIMENTAL **)
     min_bgraph = mini_beta_graph_init}   (** EXPERIMENTAL **)
  in
  Memoisation.make_bounded_set n dummy_cfg_pair

(*** get names ***)
(* note: separted nxtid, so now nxtid is specifically for abs names in sigma *)
(* we need to merge abstract names because they are shared between confs *)
let merge_abs_names names1 names2 =
  match names1,names2 with
  | Some names1,Some names2 ->
     (** THIS IS INEFFICIENT. WE CAN PROBABLY FIGURE A SINGLE FOLD FOR THIS. **)
     let domain1 = List.map fst (NameMap.bindings names1.abs) in
     let domain2 = List.map fst (NameMap.bindings names2.abs) in
     let domain = List.sort_uniq compare (domain1 @ domain2) in
     let new_nxtabs,merged_abs =
       (List.fold_left
          (fun (nxtid,acc) k -> 
            let success,newmap = namemap_add_fresh k nxtid acc in
            let new_nxtid = if success then nxtid + 1 else nxtid in
            new_nxtid,newmap)
          (0,NameMap.empty) domain)
     in
     let aux names =
       {names with nxtid = {names.nxtid with nxtabs = new_nxtabs}; abs = merged_abs}
     in
     Some (aux names1) , Some (aux names2)
  | _ -> names1,names2
let get_conf_names : config option -> nxtid -> conf_names option =
  fun cfg nxtid ->
  match cfg with
  | None -> None
  | Some {g; s; e} ->
     let starting_names = {empty_conf_names with nxtid=nxtid} in
     let g_names = List.fold_left (fun ls (i,v) ->
                       names_of_value v s ls) starting_names (g_to_list g) in
     let ge_names =
       match e with
       | OContext (Cxt (ecxt,t)) -> names_of_context ecxt s g_names
       | PTerm cek -> names_of_cek_exp cek s g_names
       | _ -> g_names
     in
     Some ge_names

(** START OF BLOCK OF NAME GETTERS FOR EDGE NAME PERMUTATION **)
(* GET NAMES FOR CANONICATION OF BETAS AND PERMUTATION OF EDGES *)
(* WE ONLY WANT ABS NAMES, SO WE CAN EMPTY EVERY OTHER NAMEMAP *)
let get_beta_names : Beta.t -> conf_names -> conf_names =
  fun beta starting_names ->
  match beta with
  | BetaInit -> starting_names
  | Beta {b1;b2;sigma;l=label} ->
     (* GET LABEL NAMES *)
     (* get fresh names in the label first *)
     let label_names =
       match label with (* only abs, so no store *)
       | OpCall (prv,v) -> names_of_value v StoreMap.empty starting_names 
       | _ -> starting_names
     in

     (* GET SIGMA NAMES *)
     let sigma_names = conf_names_of_sigma sigma label_names in

     (* GET BETA PART NAMES *)
     let get_g_names g s acc =
       List.fold_left (fun ls (i,v) ->
           names_of_value v s ls) acc (g_to_list g)
     in
     begin
       match b1,b2 with
       | Some b1 , Some b2 -> 
          let g1, s1, g2, s2 = b1.g , b1.s , b2.g , b2.s in
          let b1_names = names_of_store s1 (get_g_names g1 s1 sigma_names) in
          let b2_names = names_of_store s2 (get_g_names g2 s2 b1_names) in
          b2_names
       | Some b1 , None ->
          let g1, s1 = b1.g , b1.s in
          let b1_names = names_of_store s1 (get_g_names g1 s1 sigma_names) in
           b1_names 
       | None , Some b2 -> 
          let g2, s2 = b2.g , b2.s in
          let b2_names = names_of_store s2 (get_g_names g2 s2 sigma_names) in
          b2_names
       | None , None -> starting_names
     end

let get_eebeta_names : EEBeta.t -> conf_names -> conf_names =
  fun {beta';e1;e2;beta} starting_names ->
  let get_ocxt_names e names =
    match e with
    | None | Some Diamond -> names
    | Some (Cxt (ecxt,t)) -> names_of_context ecxt StoreMap.empty names
  in
  (* need to get beta names first to avoid normalising again *)
  starting_names
  |> get_beta_names beta
  |> get_ocxt_names e1
  |> get_ocxt_names e2
  |> get_beta_names beta'
(** END OF BLOCK OF NAME GETTER FUNCTIONS FOR EDGE NAME PERMUTATION **)

(* GET EEBETA NAMES IN EE's IN GRAPH FOR REGULAR NORMALISATION *)
(** NOTE: no need to get names in beta **)
let get_graph_eebeta_names : beta_graph -> config option -> config option
                       -> conf_names option -> conf_names option 
                       -> conf_names option * conf_names option =
  fun beta_graph c1 c2 names1 names2 ->
  let f k eebeta_set acc =
    let g (acc1,acc2) ({e1;e2;beta} : EEBeta.t) =
      let aux s names = function
        | None | Some Diamond -> names
        | Some (Cxt (ecxt,t)) -> names_of_context ecxt s names
      in
      (** Monadic obfuscation. This would otherwise require 2^4 cases **)
      (** e.g. C1,acc1 and C2,acc2 could be each some or none.
       ** if Ci = None then acci = None, if Ci = Some, then acci = Some.
       ** otherwise, there's a mismatch between names and CFG.
       ** this works because previous cases would output an error. **)
      (c1 >>= fun c1 -> acc1
          >>= fun acc1 -> Some (aux c1.s acc1 e1)),
      (c2 >>= fun c2 -> acc2
          >>= fun acc2 -> Some (aux c2.s acc2 e2))
    in
    List.fold_left g acc eebeta_set
  in
  BetaMap.fold f beta_graph (names1,names2)

(*** garbage collection ***)
let flag_gc = ref false

let garbage_collect_conf : config option -> conf_names option -> config option =
  fun cfg names ->
  match cfg , names with
  | None , None -> None
  | Some cfg , Some { nxtid ; vars ; locs ; abs } ->
     let new_s = garbage_collect cfg.s locs print_debug_gc in
     print_debug_gc (Printf.sprintf "new store: %s" (string_of_s new_s));
     Some {cfg with s = new_s}
  | Some _ , None -> failwith "lts.ml garbage collection: mismatch option of cfg and names (1)"
  | None , Some _ -> failwith "lts.ml garbage collection: mismatch option of cfg and names (2)"

(*** sigma garbage collection ***)
let flag_sigma_gc = ref false

let garbage_collect_sigma : (sigma * dep_tree) -> conf_names option -> conf_names option ->
                            (sigma * dep_tree) =
  fun (sigma,dtree) names1 names2 ->
  if not !flag_sigma_gc then sigma,dtree else
    begin
      print_debug_sigma_gc "CALLING: garbage_collect_sigma";
      match names1,names2 with
      | Some names1 , Some names2 -> Upto_tools.sigma_gc sigma dtree names1 names2
      | Some names1 , None -> Upto_tools.sigma_gc sigma dtree names1 empty_conf_names
      | None , Some names2 -> Upto_tools.sigma_gc sigma dtree names2 empty_conf_names
      | None , None ->
         failwith "garbage_collect_sigma: this shouldn't be called on a None-None conf pair"
    end
(*** normalisation ***)
let flag_norm = ref false

let normalise_conf : config option -> conf_names option -> name_map -> config option =
  fun cfg names sigma_names ->
  match cfg , names with
  | None , None -> None
  | Some {g; s; e} , Some names ->
     let new_g = IntMap.map (fun v -> normalise_val v names sigma_names) g in
     let new_s = mk_normalised_store names sigma_names s in
     print_debug_gc (Printf.sprintf "NEW S: %s" (string_of_s new_s));
     let new_e =
       match e with
       | OContext (Cxt (ecxt,t)) -> OContext (Cxt(normalise_cxt ecxt names sigma_names , t))
       | PTerm e -> PTerm (normalise_cek_exp e names sigma_names)
       | _ -> e
     in
     Some {g = new_g; s = new_s; e = new_e}
  | Some _ , None -> failwith "lts.ml garbage collection: mismatch option of cfg and names (1)"
  | None , Some _ -> failwith "lts.ml garbage collection: mismatch option of cfg and names (2)"

(* normalisation for regular memoisation that skips normalising betas *)
let normalise_eebeta_ee : EEBeta.t -> conf_names option -> conf_names option -> name_map -> EEBeta.t =
  fun {beta';e1;e2;beta} names1 names2 sigma_names ->
  let aux names = function
    | None -> None
    | Some e ->
       (match e with
        | Diamond -> Some Diamond
        | Cxt (ecxt,t) ->
           names >>= fun names -> Some (Cxt(normalise_cxt ecxt names sigma_names , t)))
  in
  (** beta doesn't need to be normalised **)
  {beta'; e1=aux names1 e1; e2=aux names2 e2; beta}

let normalise_beta_graph : beta_graph -> conf_names option -> conf_names option
                           -> name_map -> beta_graph =
  fun beta_graph names1 names2 sigma_names ->
  let f beta_key eebeta_set acc_beta_graph =
    let g eebeta = normalise_eebeta_ee eebeta names1 names2 sigma_names in
    let new_beta_key = beta_key in (** no need to modify it, we normalise when creating them **)
    let new_eebeta_set = List.map g eebeta_set in
    BetaMap.add new_beta_key new_eebeta_set acc_beta_graph
  in
  BetaMap.fold f beta_graph BetaMap.empty

(*** sigma normalisation ***)
let flag_sigma_norm = ref false

(*** sigma simplification ***)
let flag_sigma_simp = ref false
let simplify_sigma : (sigma * dep_tree) -> conf_names option -> conf_names option ->
                            (sigma * dep_tree) =
  fun sigma names1 names2 ->
  if not !flag_sigma_simp then sigma else
    begin
      print_debug_sigma_simp "CALLING: simplify_sigma";
      match names1,names2 with
      | Some names1 , Some names2 ->
         sigma_subset_removal
           (Upto_tools.sigma_simp sigma names1 names2) names1 names2
      | Some names1 , None ->
         sigma_subset_removal
           (Upto_tools.sigma_simp sigma names1 empty_conf_names) names1 empty_conf_names
      | None , Some names2 ->
         sigma_subset_removal
           (Upto_tools.sigma_simp sigma names2 empty_conf_names) names2 empty_conf_names
      | None , None -> failwith "simplify_sigma: this shouldn't be called on a None-None conf pair"
    end

(*** gamma uniq ***)
let flag_gamma_duplicates = ref false
let gamma_uniq : config_pair -> config_pair =
  fun ({a; c1; c2} as cfg_pair) ->
  if not !flag_gamma_duplicates then cfg_pair
  else
    begin
  match c1 , c2 with
  | None , None -> cfg_pair
  | Some ({g = g1; s = s1} as c1) , Some ({g = g2; s = s2} as c2) ->
     let to_delete = gama_dup_indices (g_to_list g1) (g_to_list g2) s1 s2 in
     let new_g1 = g_filter (fun k _ -> IntSet.mem k to_delete) g1 in
     let new_g2 = g_filter (fun k _ -> IntSet.mem k to_delete) g2 in
     {cfg_pair with
                    c1 = Some {c1 with g = new_g1};
                    c2 = Some {c2 with g = new_g2}}
  | Some ({g = g1; s = s1} as c1) , None ->
     let to_delete = gama_dup_indices (g_to_list g1) (g_to_list g1) s1 s1 in
     let new_g1 = g_filter (fun k _ -> IntSet.mem k to_delete) g1 in
     {cfg_pair with
                    c1 = Some {c1 with g = new_g1};
                    c2 = None}
  | None , Some ({g = g2; s = s2} as c2) ->
     let to_delete = gama_dup_indices (g_to_list g2) (g_to_list g2) s2 s2 in
     let new_g2 = g_filter (fun k _ -> IntSet.mem k to_delete) g2 in
     {cfg_pair with
                    c1 = None;
                    c2 = Some {c2 with g = new_g2}}
    end

(********************
 * UP-TO TECHNIQUES *
 ********************)
(* up-to separation *)
let flag_sep = ref false

let upto_separation : config_pair -> config_pair =
  fun cfg_pair ->
  if not !flag_sep then cfg_pair
  else
    begin
      print_debug_sep "up-to separation called";

      let c1 , c2 = cfg_pair.c1 , cfg_pair.c2 in
      match c1,c2 with
      | None , _ -> print_debug_sep "LHS bot"; cfg_pair
      | _ , None -> print_debug_sep "RHS bot"; cfg_pair
      | Some c1, Some c2 ->
         begin
           let exp_of_option =
             function PTerm e -> e | OContext _ -> failwith "upto_separation: No Term (Op Context)" in
           let unwrap_option =
             function Some e -> e | None -> failwith "upto_separation: None" in
           let names_of_bindings s bs =
             List.map (fun (k,v) -> k , names_of_value v s empty_conf_names) bs in
           let g1_kns = names_of_bindings c1.s (IntMap.bindings c1.g) in
           let g2_kns = names_of_bindings c2.s (IntMap.bindings c2.g) in
           let graph_n1, graph_n2 =
             get_graph_eebeta_names cfg_pair.beta_graph
               (Some c1) (Some c2) (Some empty_conf_names) (Some empty_conf_names)
           in
           let e1_ns = names_of_cek_exp (exp_of_option c1.e) c1.s (unwrap_option graph_n1) in
           let e2_ns = names_of_cek_exp (exp_of_option c2.e) c2.s (unwrap_option graph_n1) in
           let keys_to_remove = find_keys_to_remove g1_kns g2_kns e1_ns e2_ns in

           print_debug_sep
             (Printf.sprintf "G1_KNS:\n%s\n"
                (let f (k,ns) = Printf.sprintf "(%d |-> %s)" k (string_of_conf_names ns) in
                 string_of_list f g1_kns));
           print_debug_sep
             (Printf.sprintf "G2_KNS:\n%s\n"
                (let f (k,ns) = Printf.sprintf "(%d |-> %s)" k (string_of_conf_names ns) in
                 string_of_list f g2_kns));
           
           print_debug_sep (Printf.sprintf "Pre G1: %s" (string_of_g c1.g));

           let remove_keys ls gmap1 gmap2 =
             List.fold_left
               (fun (map1,map2) k -> print_debug_sep (Printf.sprintf "index removed: %d" k);
                                     IntMap.remove k map1,
                                     IntMap.remove k map2) (gmap1,gmap2) ls in

           let new_g1,new_g2 = remove_keys keys_to_remove c1.g c2.g in

           print_debug_sep (Printf.sprintf "Post G1: %s" (string_of_g new_g1));

           {cfg_pair with c1 = Some {c1 with g = new_g1};
                          c2 = Some {c2 with g = new_g2}}
         end
     end


(* up-to name reuse *)
let flag_nr = ref false

let get_eframe_names : (eval_cxt * store) option -> (conf_names * store) option =
  fun es ->
  match es with
  | None -> None
  | Some (eframe,s) -> Some (names_of_context eframe s empty_conf_names , s)

let get_value_names : (value * store) option -> (conf_names * store) option =
  fun vs ->
  match vs with
  | None -> None
  | Some (v,s) -> Some (names_of_value v s empty_conf_names , s)

let skip_name_reuse : (conf_names * store) option -> (conf_names * store) option -> bool =
  fun ns1 ns2 ->
  match ns1,ns2 with
  | None,None -> failwith "skip name reuse: expected at least one config"
  | None,Some (n2,s2) -> is_ho_in_locs n2.locs s2
  | Some (n1,s1),None -> is_ho_in_locs n1.locs s1
  | Some (n1,s1),Some (n2,s2) -> is_ho_in_locs n1.locs s1 || is_ho_in_locs n2.locs s2

(* up-to identity *)
let flag_id = ref false

(* gc and normalisation refactored *)
let sprint_names names1 names2 =
  match names1, names2 with
  | Some names1, Some names2 ->
     Printf.sprintf "Names found: \n%s\n%s"
     (Printf.sprintf "C1 Names: \n%s\n" (string_of_conf_names names1))
     (Printf.sprintf "C2 Names: \n%s\n" (string_of_conf_names names2))
  | Some names1, None ->
     Printf.sprintf "Names found: \n%s\n%s"
       (Printf.sprintf "C1 Names: \n%s\n" (string_of_conf_names names1))
       (Printf.sprintf "C2 Names: \nNONE\n")
  | None, Some names2 ->
     Printf.sprintf "Names found: \n%s\n%s"
       (Printf.sprintf "C1 Names: \nNONE\n")
       (Printf.sprintf "C2 Names: \n%s\n" (string_of_conf_names names2))
  | None, None -> "No names found (both are None)"

let debug_id_prints cfg_pair =
  match cfg_pair.c1, cfg_pair.c2 with
  | Some c1, Some c2 ->
     print_debug_id (Printf.sprintf "normalised pair:\n%s" (string_of_cfg_pair cfg_pair));
     print_debug_id (Printf.sprintf "G's equal? %b" ((string_of_g c1.g) = (string_of_g c2.g)));
     print_debug_id (Printf.sprintf "S's equal? %b" (c1.s = c2.s));
     print_debug_id (Printf.sprintf "E's equal? %b" (c1.e = c2.e))
  | _ -> print_debug_id "id not applicable"

let get_conf_pair_names cfg_pair0 nxtid =
    let nxtid  = {nxtvar = 0; nxtloc = 0; nxtabs = nxtid} in
    let names1 = get_conf_names cfg_pair0.c1 nxtid in
    let names2 = get_conf_names cfg_pair0.c2 nxtid in (** TODO: THREAD THE NAMES. THEY HAVE SHARED ALPHAS. **)
    let names1,names2 =
      get_graph_eebeta_names cfg_pair0.beta_graph cfg_pair0.c1 cfg_pair0.c2 names1 names2
    in
    (names1,names2)

let get_sigma_names cfg_pair0 =
  let nxtid,names_sigma = names_of_sigma (fst cfg_pair0.sigma) (1,NameMap.empty) in
  (nxtid,names_sigma)

let normalise_label l names sigma_names =
  let rec normalise_prv = function
    | PrIndex i -> PrIndex i
    | PrConst v -> PrConst (normalise_val v names sigma_names)
    | PrTuple vs -> PrTuple (List.map normalise_prv vs)
    | PrList (ls,t) -> PrList (Ast.SymList.map2 normalise_prv ls, t) (** TODO: check map2 **)
  in
  match l with
  | Tau -> Tau
  | OpCall (prv,v) ->
     let prv' = normalise_prv prv in
     let v'   = normalise_val v names sigma_names in
     OpCall (prv',v')
  | PrCall (v,prv) ->
     let prv' = normalise_prv prv in
     let v'   = normalise_val v names sigma_names in
     PrCall (v',prv')
  | OpRet  v   -> OpRet (normalise_val v names sigma_names)
  | PrRet  prv -> PrRet (normalise_prv prv)
  | Markup s -> Markup s
let normalise_trace tr names1 names2 sigma_names =
  match names1,names2 with
  | Some names , _ -> List.map (fun l -> normalise_label l names sigma_names) tr
  | None , Some names -> List.map (fun l -> normalise_label l names sigma_names) tr
  | None , None -> tr

(** START OF BLOCK OF NORMALISATION FUNCTIONS FOR EDGE NAME PERMUTATION **)
let normalise_beta : Beta.t -> conf_names -> Beta.t =
  fun beta names ->
  match beta with
  | BetaInit -> BetaInit
  | Beta {b1;b2;sigma;l} ->
     let normalised_label = normalise_label l names NameMap.empty in (* empty sigma names *)
     let normalised_sigma = normalise_sigma sigma names.abs in
     let normalise_g g = IntMap.map (fun v ->
                             let res = normalise_val v names NameMap.empty in res) g in
     let normalise_s s = mk_normalised_store names NameMap.empty s in
     let normalised_b1 =
       b1 >>= ((fun b1 -> Some {g = normalise_g b1.g; s = normalise_s b1.s})
                         : BetaPart.t -> BetaPart.t option) in
     let normalised_b2 =
       b2 >>= ((fun b2 -> Some {g = normalise_g b2.g; s = normalise_s b2.s})
                         : BetaPart.t -> BetaPart.t option) in
     Beta {b1 = normalised_b1;
           b2 = normalised_b2;
           sigma = normalised_sigma;
           l = normalised_label}

let normalise_eebeta : EEBeta.t -> conf_names -> EEBeta.t =
  fun {beta';e1;e2;beta} names ->
  let normalise_e e = match e with
    | None | Some Diamond -> e
    | Some (Cxt (ecxt,t)) -> Some (Cxt (normalise_cxt ecxt names NameMap.empty,t))
  in
  {beta' = normalise_beta beta' names;
   e1 = normalise_e e1 ;
   e2 = normalise_e e2 ;
   beta = normalise_beta beta names}

let set_loc_var_identity starting_names =
  let loc_names = starting_names.locs in
  let var_names = starting_names.vars in
  let loc_identity = NameMap.mapi (fun {id;str} _ -> set_var_loc_ignore ()) loc_names in
  let var_identity = NameMap.mapi (fun {id;str} _ -> set_var_loc_ignore ()) var_names in
  let alpha_names = {starting_names with vars = var_identity; locs = loc_identity} in
  alpha_names

(*
let normalise_beta_edge : EEBeta.t -> conf_names -> EEBeta.t =
  fun eebeta starting_names ->
  (* get eebeta names first because that way we don't normalise eebeta.beta for reachability *)
  let edge_names = starting_names |> get_eebeta_names eebeta in
  normalise_eebeta eebeta edge_names 
 *)
(* alpha normalisation : see comment on add function *)
let normalise_beta_alphas : Beta.t -> conf_names -> Beta.t =
  fun beta starting_names ->
  (* get all names first *)
  let beta_names = starting_names |> get_beta_names beta in

  (* update map so everything points back at itself *)
  let alpha_names = set_loc_var_identity beta_names in
  
  (* now normalise *)
  normalise_beta beta alpha_names

let normalise_eebeta_alphas : EEBeta.t -> conf_names -> EEBeta.t =
  fun eebeta starting_names ->
  (* get all names first *)
  let edge_names = starting_names |> get_eebeta_names eebeta in
  
  (* update map so everything points back at itself *)
  let alpha_names = set_loc_var_identity edge_names in

  (* now normalise *)
  normalise_eebeta eebeta alpha_names

(** END OF EDGE PERMUTATION BLOCK **)

(* REGULAR NORMALISATION *)
let gc_locations_and_sigma cfg_pair0 =
    (*** REMOVE GAMMA DUPLICATES FIRST ***)
    let cfg_pair0 = gamma_uniq cfg_pair0 in

    (*** FIND ALL NAMES FOR GC ***)
    let nxtid,names_sigma = get_sigma_names cfg_pair0 in
    let names1,names2 = get_conf_pair_names cfg_pair0 nxtid in
    (* PRINT *)
    print_debug_norm "===START OF NORMALISATION CYCLE===";
    print_debug_norm (Printf.sprintf "SIGMA names:\n%s\n" (string_of_names_map names_sigma));
    print_debug_norm (sprint_names names1 names2);
    print_debug_norm (Printf.sprintf "configuration before:\n%s\n" (string_of_cfg_pair cfg_pair0));

    (*** GARBAGE COLLECT LOCATIONS ***)
    let cfg_pair1 =
      if not !flag_gc then cfg_pair0 else
        {cfg_pair0 with c1 = garbage_collect_conf cfg_pair0.c1 names1;
                        c2 = garbage_collect_conf cfg_pair0.c2 names2;}
    in

    print_debug_sigma_gc "==START OF SIGMA GC CYCLE==";
    print_debug_sigma_gc (Printf.sprintf "OLD SIGMA:\n%s" (string_of_sigma (fst cfg_pair0.sigma)));
    let garbage_collected_sigma = garbage_collect_sigma cfg_pair0.sigma names1 names2 in
    print_debug_sigma_gc (Printf.sprintf "NEW SIGMA:\n%s"
                            (string_of_sigma (fst garbage_collected_sigma)));

    print_debug_sigma_simp "==START OF SIGMA SIMP CYCLE==";
    print_debug_sigma_simp (Printf.sprintf "OLD SIGMA:\n%s"
                              (string_of_sigma (fst garbage_collected_sigma)));
    let simplified_sigma = simplify_sigma garbage_collected_sigma names1 names2 in
    print_debug_sigma_simp (Printf.sprintf "NEW SIGMA:\n%s"
                              (string_of_sigma (fst simplified_sigma)));
    
    let cfg_pair2 = {cfg_pair1 with sigma = simplified_sigma} in
    cfg_pair2 , cfg_pair1 , garbage_collected_sigma

(** HAD TO MOVE CFG MINIMISATION HERE **)

let minimal_of_cfg_opt cfg_opt =
  match cfg_opt with
  | None -> None
  | Some {g; s; e} ->
     Some {min_g = g_to_val_list g; min_s = string_of_s s; min_e = e}

let minimal_of_cfg_pair {a; c1; c2; tr; bound = (bound1,bound2); sigma=(sigma,dtree);beta;beta_graph} =
  (** EXPERIMENTAL **)
  let beta = normalise_beta_alphas beta empty_conf_names in
  let (_,id_map),reachable_graph =
    mini_reachable_beta_graph beta
      beta_graph empty_beta_id_map beta_graph_init
  in
  {min_c1 = minimal_of_cfg_opt c1; min_c2 = minimal_of_cfg_opt c2; min_sigma = sigma;
   min_beta =
     (match BetaMap.find_opt beta id_map with
      |None ->
        failwith
          (Printf.sprintf "minimise_beta_graph: beta not found: %s"
             (Beta.to_string beta))
      | Some x -> x)  ; 
   min_bgraph = (minimise_beta_graph reachable_graph id_map)}

(** END OF MINIMISATION **)

let gc_normalisation cfg_pair0 =
    (* GARBAGE COLLECT *)
    let cfg_pair2 , cfg_pair1 , garbage_collected_sigma = gc_locations_and_sigma cfg_pair0 in
    
    (* FIND ALL NAMES AGAIN FOR NORMALISATION NOW *)
    let nxtid,names_sigma = get_sigma_names cfg_pair2 in
    let names1,names2 = get_conf_pair_names cfg_pair2 nxtid in

    (** MERGE NAMES BECAUSE ABS IS UNSOUND **)
    let names1,names2 = merge_abs_names names1 names2 in

    (*** NORMALISING CONFIG FOR MEMOISATION ***)
    print_debug_sigma_norm "==START OF SIGMA NORM CYCLE==";
    print_debug_sigma_norm (Printf.sprintf "SIGMA FLAG: %b" !flag_sigma_norm);
    print_debug_sigma_norm (Printf.sprintf "OLD SIGMA:\n%s" (string_of_sigma (fst cfg_pair2.sigma)));
    let normalised_sigma =
      if not !flag_sigma_norm then cfg_pair2.sigma else
        normalise_sigma (fst cfg_pair2.sigma) names_sigma , (snd cfg_pair2.sigma)
    in
    print_debug_sigma_norm (Printf.sprintf "NEW SIGMA:\n%s"
                              (string_of_sigma (fst normalised_sigma)));
    
    let normalised_cfg_pair =
      if not !flag_norm then cfg_pair2 else
        {cfg_pair2 with c1 = normalise_conf cfg_pair2.c1 names1 names_sigma;
                        c2 = normalise_conf cfg_pair2.c2 names2 names_sigma;
                        (* tr = normalise_trace cfg_pair2.tr names1 names2 names_sigma; *)
                        (* should be same for both sides *)
                        sigma = normalised_sigma;
                        beta = cfg_pair2.beta;
                        beta_graph = normalise_beta_graph
                                       cfg_pair2.beta_graph names1 names2 names_sigma}
    in
    (** PRINT **)
    let names_to_print () =
      let nxtid',names_sigma' = get_sigma_names normalised_cfg_pair in
      let names1',names2' = get_conf_pair_names normalised_cfg_pair nxtid' in
      print_debug_sigma_norm (Printf.sprintf "SIGMA names:\n%s\n"
                                (string_of_names_map names_sigma'));
      print_debug_norm (sprint_names names1' names2')
    in
    lazy_print_debug names_to_print debug_norm;
    print_debug_norm (Printf.sprintf "configuration after:\n%s\n"
                        (string_of_cfg_pair normalised_cfg_pair));
    normalised_cfg_pair , cfg_pair1 , garbage_collected_sigma

(* up-to generalisation *)
let flag_generalise = ref false
let flag_gen_succeeded = ref false
let set_gen_success () = flag_gen_succeeded := true
let retry_fun = ref (fun () -> ())
let twice_twice = ref false

let apply_generalisation_gen gen10 gen20 s1 s2 sigma =
  let sigma1 , countersigma1 , abs1 , newls1 , pos1 , gen1 =
    match gen10 with
    | Some gen ->
       generalise_conditions gen sigma (fst sigma , fst sigma)
         s1 None !flag_generalise print_debug_generalise
    | _ -> sigma , (fst sigma , fst sigma) , None , [] , None , None
  in
  let sigma2 , countersigma2 , abs2 , newls2 , pos2 , gen2 =
    match gen20 with
    | Some gen ->
       generalise_conditions gen sigma1 countersigma1
         s2 abs1 !flag_generalise print_debug_generalise
    | _ -> sigma1 , countersigma1 , None , [] , None , None
  in
  let s1 =
    match gen10 with
    | Some gen ->
       generalise gen s1 newls1 countersigma2 pos1 !flag_generalise set_gen_success
    | _ -> s1
  in
  let s2 =
    match gen20 with
    | Some gen ->
       generalise gen s2 newls2 countersigma2 pos2 !flag_generalise set_gen_success
    | _ -> s2
  in
  s1,s2,sigma2,gen1,gen2

let apply_generalisation func1 func2 s1 s2 sigma =
  let get_gen func =
    match func with
    | Some (FunVal (_ , _ , _ , _ , _ , gen)) -> Some gen
    | _ -> None
  in
  apply_generalisation_gen (get_gen func1) (get_gen func2) s1 s2 sigma

let apply_sync_generalisation label1 label2 s1 s2 sigma =
  match label1 , label2 with
  | Some (PrCall (AbsFun(_,_,_,name,gen1),_)) ,
    Some (PrCall (AbsFun(_,_,_,_,gen2),_)) ->
     if name = Ast.sync_string then apply_generalisation_gen (Some gen1) (Some gen2) s1 s2 sigma
     else s1,s2,sigma,None,None
  | _ ->
     s1,s2,sigma,None,None

let flag_reachable_beta_graph = ref false

(* up-to generalisable nested opponent call *)

(*** opponent transition functions ***
 *
 * Accepts an LTS configuration
 * Returns:
 * - A list of config_pair: this is the list of next configurations
 *
 * Invariant: all returned configurations are proponent configurations
 *
 * Top-level function:
 * - op_transitions
 *
 * *)

(* mk_op_tuple is the core of name-reuse *)
let rec mk_op_tuple_from_type : abs_set -> Type.t -> IntSet.t -> bool -> value * abs_set * IntSet.t =
  fun a in_type used_ids skip_name_reuse ->
  match in_type with
  | Type.UnitT -> ConstVal UnitConst , a , used_ids
  | BoolT | IntT ->
     let new_id , new_a = abs_next_id in_type a in
     AbsCon (new_id, in_type, Ast.default_acname, None) , new_a , IntSet.add new_id used_ids
  | Type.FunT (args,ret_type) ->
     begin
       match args with
       | arg_type::[] ->
          begin
            let make_new_abs () =
              let new_id , new_a = abs_next_id in_type a in
              AbsFun (new_id, arg_type, ret_type, Ast.default_afname, None) ,
              new_a ,
              IntSet.add new_id used_ids
            in
            if skip_name_reuse || (not !flag_nr) then make_new_abs ()
            else
              begin
                match TypeMap.find_opt in_type a.ti with
                | None -> make_new_abs ()
                | Some id_set ->
                   begin
                     match get_reusable_name id_set used_ids with
                     | None -> make_new_abs ()
                     | Some (new_id , new_used_ids) ->
                        print_debug_nr (Printf.sprintf "id reused: %d" new_id);
                        AbsFun (new_id, arg_type, ret_type, "af", None) , a , new_used_ids
                   end
              end
          end
       | _ -> failwith "get fun type: unexpected type given"
     end
  | TupleT ls ->
     let new_ls, new_a, new_used_ids =
       List.fold_right
         (fun t (vs,a,used) ->
           let new_item,new_a,new_used = mk_op_tuple_from_type a t used skip_name_reuse in
           new_item::vs,new_a,new_used) ls ([],a,used_ids)
     in
     TupleVal new_ls , new_a , new_used_ids
  | Type.ListT t ->
     let new_id , new_a = abs_next_id in_type a in
     ListVal (AbsList {idid=new_id;str=Ast.default_alname}, t) , new_a , IntSet.add new_id used_ids
  | VarT _ -> failwith "mk op tuple: only closed types at LTS, VarT shouldn't appear."

let components_from_type a k_type ns1 ns2 newtr =
  let skip = skip_name_reuse ns1 ns2 in
  let old_names =
    match ns1,ns2 with
    | None,None -> IntSet.empty
    | Some(n1,s1),None -> intset_of_namemap n1.abs
    | None,Some(n2,s2) -> intset_of_namemap n2.abs
    | Some(n1,s1), Some(n2,s2) ->
       IntSet.union (intset_of_namemap n1.abs) (intset_of_namemap n2.abs)
  in
  let new_abs , new_a , used_ids = mk_op_tuple_from_type a k_type old_names skip in
  let new_trace = newtr new_abs in
  (new_abs , new_trace , new_a)

let op_ret_trans (({a; c1; c2; tr; bound = (bound1,bound2)} as cfg_pair):config_pair) =
  let newtr new_abs = (OpRet new_abs) :: tr in
  let components_from_type_frame a k_type es1 es2 =
    let ns1 = get_eframe_names es1 in
    let ns2 = get_eframe_names es2 in
    components_from_type a k_type ns1 ns2 newtr
  in
  let bound10,bound20 = {bound1 with ret = bound1.ret - 1 }, {bound2 with ret = bound2.ret - 1 } in
  if min bound10.ret bound20.ret <= 0 then (do_bound_reached cfg_pair; []) else
    let cfg_pair = {cfg_pair with bound = (bound10,bound20)} in
    match (c1, c2) with
    | None, None -> []

    | Some ({e = OContext (Cxt(k1_nxt,k1_type))} as c01), None ->
       let (new_abs , new_trace , new_a) =
         components_from_type_frame a k1_type (Some (k1_nxt,c01.s)) None in
       {cfg_pair with
         a = new_a;
         c1 = Some {c01 with e = PTerm {ecxt = k1_nxt;e = ValExp (new_abs, None)}};
         c2 = None;
         tr = new_trace} :: []

    | None, Some ({e = OContext (Cxt(k2_nxt,k2_type))} as c02) ->
       let (new_abs , new_trace , new_a) =
         components_from_type_frame a k2_type None (Some (k2_nxt,c02.s)) in
       {cfg_pair with
         a = new_a;
         c1 = None;
         c2 = Some {c02 with e = PTerm {ecxt = k2_nxt;e = ValExp (new_abs, None)}};
         tr = new_trace} :: []

    | Some ({e = OContext (Cxt(k1_nxt,k1_type))} as c01),
      Some ({e = OContext (Cxt(k2_nxt,k2_type))} as c02) ->
       if k1_type <> k2_type then failwith "oret: evaluation context type mismatch" else

         let (new_abs , new_trace, new_a) = components_from_type_frame a k2_type
                                              (Some (k1_nxt,c01.s)) (Some (k2_nxt,c02.s)) in
         {cfg_pair with
           a = new_a;
           c1 = Some {c01 with e = PTerm {ecxt = k1_nxt; e = ValExp (new_abs, None)}};
           c2 = Some {c02 with e = PTerm {ecxt = k2_nxt; e = ValExp (new_abs, None)}};
           tr = new_trace} :: []

  (* valid opponent configurations that cannot return *)
  | Some {e = OContext Diamond}, Some {e = OContext Diamond} -> []

  (** op_coterminate checks Bottom and Diamond cases, before entering this function **)

  (* anything else is invalid here *)
  | _ -> failwith "erroneous configurations in opponent return transition"
;;

let get_fun_type = function
  | Type.FunT (argt::[],rett) -> argt , rett
  | t -> failwith ("get_fun_type: expected function, got " ^ (Type.string_of_t t))

let rec type_of_value = function
  | ConstVal c ->
     begin
       match c with
       | IntConst i -> Type.IntT
       | BoolConst b -> Type.BoolT
       | UnitConst -> Type.UnitT
     end
  | FunVal (func_name, ret_type, arg, arg_type, body, _) -> Type.FunT ([arg_type],ret_type)
  | AbsCon (id, typ, name, _) -> typ
  | AbsFun (id, t1, t2, name, gen) -> Type.FunT ([t1],t2)
  | TupleVal ls -> TupleT (List.map type_of_value ls)
  | ListVal (_,t) -> Type.ListT t

(** START OF EDGE PERMUTATION CODE **)

(* adding beta edge function:
OPCALL:
(C1,C2,b,Sigma)- opcall(i,a) 
  -> (C1',C2',b',Sigma[$b' |-> ($'b',$'C1.E,$'C2.E,$'b)])

b' = (C1.g,C1.s,C2.g,C2.s,opcall(i,a))
Names(b') = $
Names(b',C1.E,C2.E,b) = $'
$b' = ($C1.g,$C1.s,$C2.g,$C2.s,opcall(i,$a))

1. normalise b: $b
2. normalise eebeta: $'eebeta
3. update graph: Sigma[$b --> $'eebeta]

* NORMALISATION APPEARS TO BE IDEMPOTENT:
this means we can normalise beta twice and obtain the same result.
this implies that we don't have to denormalise tail betas.
however, if we collect their names before everything else,
this also means we do not even need to normalise tailing betas again. 

* Note: you get errors because names are not found.
we need to get names again in eebeta and beta and assign the same names back.
 *)
let beta_graph_add_edge beta eebeta beta_graph =
  (* the normalisation functions handle the logic for identity of locs and vars *)
  let normalised_beta = normalise_beta_alphas beta empty_conf_names in
  let normalised_eebeta = normalise_eebeta_alphas eebeta empty_conf_names in
  beta_graph_add normalised_beta normalised_eebeta beta_graph

(** END OF EDGE PERMUTATION CODE **)

let beta_mk cfg_pair label =
  let aux c = c >>= fun c :(BetaPart.t option) -> Some {g=c.g;s=c.s} in
  Beta.mk (aux cfg_pair.c1) (aux cfg_pair.c2) (fst cfg_pair.sigma) label

let op_call_trans ({a; c1; c2; tr; bound = (bound10,bound20);
                    sigma; beta_graph; beta} as cfg_pair :config_pair) =
  let last_move_is_sync =
    match tr with
    | (PrCall (AbsFun(_,_,_,name,_),v)) :: xs ->
       name = Ast.sync_string
    | _ -> false
  in
  (** TODO: temporary hack to set sync errors to false **)
  if last_move_is_sync then (flag_gen_succeeded := true; []) else

  let op_reduce_app vop varg bound =
    (* HACK: the code below assumes that the bound is decreased by 1 by reduce_app *)
    match reduce_app vop varg bound with (** REMOVED REFRESH VOP **)
    | None -> (* stuck due to application of abstract constant or bad types *)
        {ecxt = []; e = AppExp (ValExp (vop, None), ValExp (varg, None), None)}
    | Some (new_e, new_bound) ->
        {ecxt = []; e = new_e}
  in
  if min bound10.call bound20.call <= 0 then (do_bound_reached cfg_pair; [])
  else
    begin
      let newtr i new_abs = OpCall (i, new_abs) :: tr in
      let components_from_type_value a k_type vs1 vs2 i =
        let ns1 = get_value_names vs1 in
        let ns2 = get_value_names vs2 in
        components_from_type a k_type ns1 ns2 (newtr i)
      in
      match (c1, c2) with
      | (None, None) -> []

      | (Some ({g = g1_map; e = OContext e1} as c01), None) -> 
         (List.fold_left
            (fun out_lst (index,func) ->
              if not(is_ho_value func)
              then failwith "ocall: g shouldn't contain ground-type values" else

                (* generalise *)
                let s1,_,sigma2,gen1,_ =
                  apply_generalisation (Some func) None c01.s c01.s sigma in
                
                let arg_type, ret_type = get_fun_type (type_of_value func) in
                let new_abs , new_trace , new_a =
                  components_from_type_value a arg_type (Some (func,s1)) None (PrIndex index)
                in
                let new_label = List.hd new_trace in
                let new_beta =
                  beta_mk {cfg_pair with c1 = Some {c01 with s = s1}; sigma = sigma2} new_label in
                let new_beta_graph =
                  beta_graph_add_edge
                    new_beta (EEBeta.mk new_beta (Some e1) None beta) beta_graph
                in
                ({a = new_a;
                  c1 = Some {c01 with e = PTerm (op_reduce_app func new_abs bound10.internal); s = s1};
                  c2 = None;
                  tr = new_trace;
                  bound = ({bound10 with call = bound10.call-1},bound20); sigma = sigma2;
                  beta_graph = new_beta_graph;
                  beta = new_beta} :: out_lst))
            []
            (g_to_list g1_map))

      | (None, Some ({g = g2_map; e = OContext e2} as c02)) ->
         (List.fold_left
            (fun out_lst (index,func) ->

              if not(is_ho_value func)
              then failwith "ocall: g shouldn't contain ground-type values" else

                (* generalise *)
                let _,s2,sigma2,_,gen2 =
                  apply_generalisation None (Some func) c02.s c02.s sigma in

                let arg_type, ret_type = get_fun_type (type_of_value func) in
                let new_abs , new_trace , new_a =
                  components_from_type_value a arg_type None (Some (func,s2)) (PrIndex index)
                in

                let new_label = List.hd new_trace in
                let new_beta =
                  beta_mk {cfg_pair with c2 = Some {c02 with s = s2}; sigma = sigma2} new_label in
                let new_beta_graph =
                  beta_graph_add_edge
                    new_beta (EEBeta.mk new_beta None (Some e2) beta) beta_graph
                in

                ({a = new_a;
                  c1 = None;
                  c2 = Some {c02 with e = PTerm (op_reduce_app func new_abs bound20.internal); s = s2};
                  tr = new_trace;
                  bound = (bound10,{bound20 with call = bound20.call-1}); sigma = sigma2;
                  beta = new_beta;
                  beta_graph = new_beta_graph} :: out_lst))
            []
            (g_to_list g2_map))

      | (Some ({g = g1_map; e = OContext e1} as c01), Some ({g = g2_map; e = OContext e2} as c02)) ->
         let (_, out_lst) =
           (List.fold_left
              (fun (g2_lst_in, out_lst) (index1,func1) ->
                match g2_lst_in with
                | [] -> assert false
                | (index2,func2) :: g2_rest ->

                   (* generalise *)
                   let s1,s2,sigma2,gen1,gen2 =
                     apply_generalisation (Some func1) (Some func2) c01.s c02.s sigma in

                   if (type_of_value func1) <> (type_of_value func2)
                   then failwith "ocall: type mismatch" else (
                     if index1 <> index2
                     then failwith "ocall: index mismatch" else (

                       if not(is_ho_value func1)
                       then failwith "ocall: g shouldn't contain ground-type values" else (

                         let arg_type, ret_type = get_fun_type (type_of_value func1) in
                         let new_abs , new_trace , new_a =
                           components_from_type_value a arg_type
                             (Some (func1,c01.s)) (Some (func2,c02.s)) (PrIndex index1)
                         in

                         let new_label = List.hd new_trace in
                         let new_beta =
                           beta_mk {cfg_pair with c1 = Some {c01 with s = s1};
                                                  c2 = Some {c02 with s = s2};
                                                  sigma = sigma2} new_label
                         in
                         let new_beta_graph =
                           beta_graph_add_edge
                             new_beta (EEBeta.mk new_beta (Some e1) (Some e2) beta) beta_graph
                         in
                         (g2_rest,
                          {a = new_a;
                           c1 = Some {c01 with e = PTerm (op_reduce_app func1 new_abs bound10.internal);
                                               s = s1};
                           c2 = Some {c02 with e = PTerm (op_reduce_app func2 new_abs bound20.internal);
                                               s = s2};
                           tr = new_trace;
                           bound = ({bound10 with call = bound10.call-1},
                                    {bound20 with call = bound20.call-1}); sigma = sigma2;
                           beta = new_beta;
                           beta_graph = new_beta_graph} :: out_lst)))))
              (g_to_list g2_map, [])
              (g_to_list g1_map))
         in out_lst

  (** op_coterminate checks Bottom and Diamond cases, before entering this function **)
      
      (* anything else is invalid here *)
      | _ -> failwith "Internal Error! erroneous configurations in opponent call transition"
    end

let op_coterminate ({c1; c2; tr} as cfg_pair) =
  match (c1, c2) with (** Beta should necessarily be diamond too, if e1 or e2 is OContext Diamond  -- no need to check **)
  | (None, None) -> (true, [])
  (* relies on invariant that k's have same length in both configs *)
  | (Some {e = OContext _}, Some {e = OContext _}) -> (true, [])
  | (Some {e = OContext Diamond}, None) -> (false, (Markup "only LHS terminates") :: tr)
  | (None, Some {e = OContext Diamond}) -> (false, (Markup "only RHS terminates") :: tr)
  | (None, Some {e = OContext _}) -> (true, [])
  | (Some {e = OContext _}, None) -> (true, [])
  (* anything else is invalid here *)
  | _, Some {e = PTerm _}
  | Some {e = PTerm _}, _ -> ((print_endline
             "Internal Error! Proponent configurations found at opponent coterminate check.");
          print_endline ("c1,c2 = " ^ (string_of_cfg_pair cfg_pair));
          assert (false))

(* op_transitions: top-level for opponent configurations
 *
 * Accepts a double configuration
 * Produces a set of dbl_config
 * bisimulation can fail here only when checking co-termination
 * *)
let op_transitions cfg_pair =
  let (success, tr) = op_coterminate cfg_pair in
  if not success then
    if not !flag_gen_succeeded then
      begin
        Printf.printf "Bisimulation failed! Failing trace:\n %s\n\n" (string_of_trace tr);
        if not(is_sigma_empty (fst cfg_pair.sigma)) then
          begin
            Printf.printf "Symbolic Environment:\n %s\n\n"
              (string_of_sigma (fst cfg_pair.sigma));
            if (check_sat_sigma (fst cfg_pair.sigma))
            then Printf.printf "Satisfying Assignment:\n%s\n" (get_model_s ())
            else failwith "sigma should be sat but isn't"
          end;
        exit exit_ineq
      end
    else
      begin
        begin
          if !flag_generalise then
            begin
              Printf.printf "Potential failing trace found:\n %s\n\n" (string_of_trace tr);
              print_endline
                "However, state generalisations were used so inequivalences may be unsound.";
              print_endline "***Retrying with state generalisations off***\n";
              flag_generalise := false;
              twice_twice := true;
              !retry_fun ()
            end
          else
            begin
              Printf.printf "Bisimulation failed! Real failing trace found:\n %s\n\n"
                (string_of_trace tr);
              exit exit_ineq
            end
        end;
        exit exit_unknown
      end
  ;
  (op_call_trans cfg_pair) @ (op_ret_trans cfg_pair) (* explore op-call moves before op-ret *)


(*** proponent transition functions ***
 *
 * Accepts an LTS configuration and a bound
 * Returns:
 * - A list of (config_pair * bound): this is the list of next configurations
 *
 * Invariant: all returned configurations are opponent configurations
 *
 * Top-level function:
 * - pr_transitions
 *
 * *)

let ret_type_of_fun = function
  | FunVal (_, ret_type, _, _, _, _) -> ret_type
  | AbsFun (_, _, ret_type, _, _) -> ret_type
  | _ -> failwith "arg type of function: not a function"

(* this appears to be reducing a single config. *)
(* return type: (Either config * Either transition label * Bound * Sigma) *)
let config_transition cfg bound0 sigma0 lsubs0 =
  print_debug_sigma (Printf.sprintf "produced sigma: %s" (string_of_sigma (fst sigma0)));
  match cfg with
  | None -> (None, None, bound0, sigma0, lsubs0) :: []    (* this is a bottom configuration *)
  | Some {e = OContext _} -> failwith "Internal Error! opponent configuration at proponent move"
  | Some ({s = s0; e = PTerm e0} as cfg0) ->
     begin
       let next_confs = big_step {Reductions_ast.s = s0; e = e0} bound0 sigma0 lsubs0 in
       let process_conf ({Reductions_ast.s = s1; e = e1}, bound1, sigma1, lsubs1) =
         (* bound exhausted during reduction -- tau is used as a flag to the caller  *)
         if bound1 = 0 then (None, Some Tau, 0, sigma0, lsubs1) (* still need to accumulate lsubs *)
         else
           begin
             match e1 with
             | {ecxt = []; e = ValExp (v, _)} ->
                (** ---RETURN--- transition **)
                (* collect all functions in the value *)
                let new_g,new_prval = collect_funcs v cfg0.g in
                (* temporary dummy_context. replaced with OContext from beta in pr_transitions *)
                (Some (abslist_swap_cfg lsubs1 {g = new_g; s = s1; e = dummy_ocontext}),
                 Some (PrRet new_prval), bound1, sigma1, lsubs1)
             | {ecxt = AppRandECxt ((AbsFun (afid, t1, t2, str, gen) as v1), _)
                       :: ec_rest; e = ValExp (v2, _)} ->
                (** ---CALL--- transition **)
                (* collect all functions in the value *)
                let new_g,new_prval = collect_funcs v2 cfg0.g in
                (Some (abslist_swap_cfg lsubs1 {g = new_g; s = s1; e = OContext (Cxt(ec_rest , t2))}),
                 Some (PrCall (v1,new_prval)), bound1, sigma1, lsubs1)
             | _ -> (* otherwise stuck term*)
                (None, None, bound1, sigma1, lsubs1)
           end
       in List.map process_conf next_confs
     end

(** START OF EDGE PERMUTATION CODE **)

(* PROP RETURN:
(C1,C2,b,Sigma)- prret(d) -> (C1',C2',b',Sigma')

Names(b) = $
Sigma($b) = {(b1,E11,E21,b1'), ... , (bn,E1n,E2n,bn')}

#: Names(bi) -> Names(b) (* denormalise *)
#+: for each n in Names(E1i,E2i,bi') . n not in #, #+[n->fresh]

denormalise will require us to run get_conf_names
bi is normalised, b.
 *)

(* denormalisation function:
Given Sigma($b) = (bi,E1i,E2i,bi') , get name map Names(bi) -> Names(b).
Plane:
1. get names from bi and b. assert: lists are same length.
2. get list of names from each map. 
3. sort lists by range (snd)
4. 
. assert: every i in N1 and N2 match.
 *)
let get_denormalisation_map : Beta.t -> Beta.t -> int * name_map =
  fun bi b ->
  let bi_names = (get_beta_names bi empty_conf_names).abs in
  let b_names = (get_beta_names b empty_conf_names).abs in
  let bi_list = NameMap.bindings bi_names in
  let b_list = NameMap.bindings b_names in
  assert(List.length bi_list = List.length b_list);
  let bi_sorted = List.sort_uniq (fun (ki,ii) (k,i) -> compare ii i) bi_list in
  let b_sorted = List.sort_uniq (fun (ki,ii) (k,i) -> compare ii i) b_list in
  assert(List.length bi_list = List.length bi_sorted);
  assert(List.length b_list = List.length b_sorted);
  let f (maxid,acc) ((ki,ii),(k,i)) =
    assert(ii = i);
    let success,new_acc = namemap_add_fresh ki k.id acc in
    assert(success);
    max (max k.id ki.id) maxid , new_acc
  in
  List.fold_left f (0,NameMap.empty) (List.combine bi_sorted b_sorted)

let list_beta_edges beta beta_graph =
  list_adjacent_betas (normalise_beta_alphas beta empty_conf_names) beta_graph

(* denormalise eebeta function:
Given eebeta = {bi';e1i;e2i;bi}, b
1. get_denormalisation_map from bi' to b and max nxtid for abs
2. build empty_conf_names with abs nxtid to largest index in range of denormalisation map
3. get new names using map from step 2 again to get missing alphas
4. normalise eebeta using map from step 3
 *)
let denormalise_eebeta (eebeta : EEBeta.t) beta = 
  let nxtabs,denormalised_abs_map = get_denormalisation_map eebeta.beta' beta in
  let nxtabs = nxtabs + 1 in (** THIS WAS A MASSIVELY PAINFUL BUG!!! **)
  let eebeta_names = get_eebeta_names eebeta
                       {empty_conf_names with
                         nxtid = {empty_conf_names.nxtid with nxtabs = nxtabs};
                         abs = denormalised_abs_map} in
  let concrete_eebeta = normalise_eebeta_alphas eebeta eebeta_names in
  concrete_eebeta


(** END OF EDGE PERMUTATION CODE **)

(* Stackless Prop Ret: 
 * 1. get all the (E1, E2, beta') from beta_graph(beta)
 * 2. if C_i != None then E_i != None (sanity check) otherwise internal error.
 * 3. fold over the list of (E1, E2, beta'), and replace the dummy_cxt with the appropriate E_i
 * 4. and beta with beta'.
 *)
let pr_ret out_list ({c1;c2;tr;beta;beta_graph} as cfg_pair) =
  match tr with
  | PrRet _ :: _ ->
     (** current move is PrRet, create new cfg and replace dummy_cxt and beta for each eebeta**)
     let eebeta_list = list_beta_edges beta beta_graph in
     (* type signature for eebeta needed because it's ambiguous *)
     let f (acc : config_pair list) (eebeta : EEBeta.t) : (config_pair list) =
       let aux c e =
         match c,e with
         | Some _ , None -> failwith "pr_ret: E in graph is None, but expected Some"
         | None , _ -> None
         | Some c , Some e -> Some {c with e = OContext e}
       in
       let concrete_eebeta = denormalise_eebeta eebeta beta in
       if eebeta.beta <> normalise_beta_alphas concrete_eebeta.beta empty_conf_names then
         begin
           Printf.printf "b not equal $#b:\n<%s>\n<%s>"
             (Beta.to_string eebeta.beta)
             (Beta.to_string (normalise_beta_alphas concrete_eebeta.beta empty_conf_names));
           assert(false)
         end;
       let new_c1 = aux c1 concrete_eebeta.e1 in
       let new_c2 = aux c2 concrete_eebeta.e2 in
       let new_beta_graph =
         if not(!flag_reachable_beta_graph) then beta_graph
         else reachable_beta_graph eebeta.beta beta_graph beta_graph_init
       in
       {cfg_pair with c1 = new_c1;
                      c2 = new_c2;
                      beta = concrete_eebeta.beta;
                      beta_graph = new_beta_graph} :: acc
     in
     List.fold_left f out_list eebeta_list
  | _ ->
     (** current move is not PrRet, leave cfg_pair unchanged **)
     cfg_pair :: out_list

let pr_transitions ({c1; c2; tr; bound = (bound10, bound20); sigma = sigma0; beta; beta_graph}
                    as cfg_pair) =
  print_debug_sigma (Printf.sprintf "sigma0: %s" (string_of_prop (prop_of_sigma (fst sigma0))));
  print_debug_traces (string_of_trace cfg_pair.tr);
  print_debug_confs (string_of_cfg_pair cfg_pair);

  (* LHS Challenge *)
  (* first try to transition C1 with bound10 *)

  (* need to first call config_transition to produce all reachable confs *)
  (* then, for each conf, produce all reachable c2 confs that satisfy the SIGMA *)

  let c1_confs = config_transition c1 bound10.internal sigma0 [] in
  
  (* cases on c1_confs *)
  let cases_of_c1 conf rest =
    match conf with
    | (None, Some Tau, 0, sigma1, lsubs1) -> (* no challenge from LHS - exhausted bound *)
       do_bound_reached cfg_pair;
       rest

    | (None, None, bound1, sigma1, lsubs1) -> (* no challenge from LHS - bot *)
       begin
         (* subs lists from c1 subs in c2 *)
         let c2 = c2 >>= (fun c2 -> Some (abslist_swap_cfg lsubs1 c2)) in
         let c2_confs = config_transition c2 bound20.internal sigma1 [] in
         let cases_of_c2 conf rest2 =
           match conf with
           | (None, Some Tau, 0, sigma2, lsubs2) -> (* run out of bound *)
              do_bound_reached cfg_pair;
              rest2

           | (None, None, bound2, sigma2, lsubs2) -> (* both bot *)
              rest2

           (* transition of C2 with bound20 results in bound2 *)
           | (Some c21, Some label2, bound2, sigma2, lsubs2) -> (* RHS challenge matched by a move *)
              (* subs lists from c2 subs in new c2, c1 is None so nothing to subs *)
              let new_tr = label2 :: (if c1 = None then tr else (Markup "entering LHS=bot") :: tr) in
              (** TODO: maybe remove all generalisations at prop. should be innocuous **)
              let gen_s1,gen_s2,gen_sigma2 = c21.s,c21.s,sigma2 in
              let gen_s1',gen_s2',gen_sigma2',gen1',gen2' = (* generalisation: sync proponent call *)
                apply_sync_generalisation None (Some label2) gen_s1 gen_s2 gen_sigma2
              in
              let final_cfg_pair = 
                {cfg_pair with c1 = None;
                               c2 = Some {c21 with s = gen_s2'};
                               tr = new_tr;
                               bound = ({bound10 with internal = bound1},
                                        {bound20 with internal = bound2});
                               sigma = gen_sigma2'} 
              in
              (* perform PrRet if current move is PrRet *)
              pr_ret rest2 final_cfg_pair

           | (_, _, _, _, _) -> (print_endline "Internal error! unexpected value"; assert false;)
         in
         List.fold_right (fun conf rest -> cases_of_c2 conf rest) c2_confs rest
       end
    | (Some c11, Some label1, bound1, sigma1, lsubs1) -> (* LHS challenge to be matched by RHS *)
       begin
         (* since C1 with bound10 succeeded, run C2 with bound20 *)
         (* c11 needs list sub from c1, c2 needs list subs using c1 *)
         let c2 = c2 >>= (fun c2 -> Some (abslist_swap_cfg lsubs1 c2)) in
         let c2_confs = config_transition c2 bound20.internal sigma1 [] in
         let cases_of_c2 conf rest2 =
           
           let last_move_is_sync =
             match label1 with
             | (PrCall (AbsFun(_,_,_,name,_),v)) ->
                name = Ast.sync_string
             | _ -> false
           in
           (** TODO: temporary hack to set sync errors to false **)
           if last_move_is_sync then flag_gen_succeeded := true;
             
           match conf with
           | (None, Some Tau, 0, sigma2, lsubs2) -> (* RHS run out of bound *)
              do_bound_reached cfg_pair;
              rest2
         
           | (None, None, bound2, sigma2, lsubs2) -> (* RHS got stuck or became bot*)
              (* c11 needs subs from c2 *)
              let c11 = abslist_swap_cfg lsubs2 c11 in
              let new_tr = label1 :: (if c2 = None then tr else (Markup "entering RHS=bot") :: tr) in
              print_debug_traces (string_of_trace [label1]);
              print_debug_confs (string_of_cfg c11);
              (** TODO: refactor **)
              let gen_s1,_,gen_sigma2,gen1,_ = c11.s,c11.s,sigma2,None,None in
              let gen_s1',_,gen_sigma2',gen1',gen2' =
                apply_sync_generalisation (Some label1) None gen_s1 gen_s1 gen_sigma2
              in
              let final_cfg_pair =
                {cfg_pair with c1 = Some {c11 with s = gen_s1'};
                               c2 = None ;
                               tr = new_tr;
                               bound = ({bound10 with internal = bound1},
                                        {bound20 with internal = bound2});
                               sigma = gen_sigma2'}
              in
              (* perform PrRet if current move is PrRet *)
              pr_ret rest2 final_cfg_pair

           | (Some c21, Some label2, bound2, sigma2, lsubs2) ->
              (* C11 needs subs from c2, c21 needs subs from c2 *)
              let c11 = abslist_swap_cfg lsubs2 c11 in
              let label1 = abslist_swap_label (lsubs1 @ lsubs2) label1 in
              let label2 = abslist_swap_label (lsubs1 @ lsubs2) label2 in
              (** STRUCTURAL EQUALITY OF LABELS IS TOO STRONG because of symbolic names. **)
              (*Printf.printf "label1: %s\nlabel2: %s"
                (string_of_trans label1) (string_of_trans label2);*)
              (* no need to traverse label to make sure all constants are the same
                 we only have constants, tuples, or indexes. So structural eq suffices.*)
              
              let last_move_is_sync =
                match label1 with
                | (PrCall (AbsFun(_,_,_,name,_),v)) ->
                   name = Ast.sync_string
                | _ -> false
              in
              (** TODO: temporary hack to set sync errors to false **)
              if last_move_is_sync then flag_gen_succeeded := true;
              
              if label1 = label2 then
                begin
                  (** TODO: refactor **)
                  let gen_s1,gen_s2,gen_sigma2,gen1,gen2 = c11.s,c21.s,sigma2,None,None in
                  let gen_s1',gen_s2',gen_sigma2',gen1',gen2' =
                    apply_sync_generalisation (Some label1) (Some label2) gen_s1 gen_s2 gen_sigma2
                  in
                  let new_cfg_pair =
                    {cfg_pair with c1 = Some {c11 with s = gen_s1'};
                                   c2 = Some {c21 with s = gen_s2'};
                                   tr = label1 :: tr;
                                   bound = ({bound10 with internal = bound1},
                                            {bound20 with internal = bound2});
                                   sigma = gen_sigma2'}
                  in
                  (* perform PrRet if current move is PrRet *)
                  pr_ret rest2 new_cfg_pair
                end
              else
                (* labels are not equal... time to check *)
                begin
                  (* PrIndex of int | PrConst of value | PrTuple of prvalue list *)
                  let check_congruence_sat v1 v2 sigma =
                    print_debug_sigma "entered check_congruence_sat";
                    (* gets two values, returns pair A,B,C *)
                    (* A: v1 == v2? *)
                    (* B: formula c1 <> c2 *)
                    (* C: f1 == f2? *)

                    let rec get_congruence_prop v1 v2 const_eq fun_eq not_cong =
                      match v1,v2 with
                      (* Int, Bool, Unit, AbsCons or AbsFun *)
                      | PrConst (ConstVal UnitConst),PrConst (ConstVal UnitConst) ->
                         true && const_eq , fun_eq , not_cong
                      | PrConst (ConstVal (IntConst i1)),PrConst (ConstVal (IntConst i2)) ->
                         (i1=i2) && const_eq , fun_eq , (i1<>i2) || not_cong
                      | PrConst (ConstVal (BoolConst b1)),PrConst (ConstVal (BoolConst b2)) ->
                         (b1=b2) && const_eq , fun_eq , (b1<>b2) || not_cong
                      | PrConst (AbsCon (id1,typ1,name1,m1)), PrConst (AbsCon (id2,typ2,name2,m2)) ->
                         begin
                           match typ1,typ2 with
                           | Type.BoolT,Type.BoolT  ->
                              let new_sigma =
                                sigma_add_bvar_neq (id1,name1) (id2,name2) (fst sigma)
                              in
                              const_eq , fun_eq , check_sat_sigma new_sigma || not_cong
                           | Type.IntT,Type.IntT  ->
                              let new_sigma =
                                sigma_add_ivar_neq (id1,name1) (id2,name2) (fst sigma)
                              in
                              const_eq , fun_eq , check_sat_sigma new_sigma || not_cong
                           | t1,t2 ->
                              (** BUG: T1 =/= T2 SHOULD NOT HAPPEN,
                                  THIS CAN ONLY BE IF A1 =/= A2, OR TYPE CHECKING FAILED **)
                              (assert(t1=t2);
                               print_endline (string_of_trans label1);
                               print_endline (string_of_trans label2);
                               print_endline (string_of_prvalue v1);
                               print_endline (string_of_prvalue v2);
                               failwith "get_congruence_prop: only x1 = x2 of bool/int allowed")
                         end
                      | PrConst (AbsCon (id1,typ1,name1,m1)), PrConst (ConstVal v) ->
                         begin
                           match v with
                           | IntConst i ->
                              begin
                                (** BUG: T1 =/= T2 SHOULD NOT HAPPEN **)
                                assert(typ1 = Type.IntT);
                                let new_sigma =
                                  sigma_add_iconst_neq (id1,name1) i (fst sigma)
                                in
                                const_eq , fun_eq , check_sat_sigma new_sigma || not_cong
                              end
                           | BoolConst b ->
                              begin
                                (** BUG: T1 =/= T2 SHOULD NOT HAPPEN **)
                                assert(typ1 = Type.BoolT);
                                let new_sigma =
                                  sigma_add_bconst_neq (id1,name1) b (fst sigma)
                                in
                                const_eq , fun_eq , check_sat_sigma new_sigma || not_cong
                              end
                           | _ -> failwith "get_congruence_prop: only x = c of bool/int allowed"
                         end
                      | PrConst (ConstVal v), PrConst (AbsCon (id1,typ1,name1,m1)) ->
                         begin
                           match v with
                           | IntConst i ->
                              begin
                                (** BUG: T1 =/= T2 SHOULD NOT HAPPEN **)
                                assert(typ1 = Type.IntT);
                                let new_sigma =
                                  sigma_add_iconst_neq (id1,name1) i (fst sigma)
                                in
                                const_eq , fun_eq , check_sat_sigma new_sigma || not_cong
                              end
                           | BoolConst b ->
                              begin
                                (** BUG: T1 =/= T2 SHOULD NOT HAPPEN **)
                                assert(typ1 = Type.BoolT);
                                let new_sigma =
                                  sigma_add_bconst_neq (id1,name1) b (fst sigma)
                                in
                                const_eq , fun_eq , check_sat_sigma new_sigma || not_cong
                              end
                           | _ -> failwith "get_congruence_prop: only x = c of bool/int allowed"
                         end
                      | PrIndex i1, PrIndex i2 -> const_eq , i1=i2 && fun_eq , (i1<>i2) || not_cong
                      | PrTuple (x::xs), PrTuple (y::ys) ->
                         let cons1,funs1,new_not_cong =
                           get_congruence_prop x y const_eq fun_eq not_cong
                         in
                         get_congruence_prop (PrTuple xs) (PrTuple ys) cons1 funs1 new_not_cong
                      | PrTuple [], PrTuple [] -> const_eq , fun_eq , not_cong
                      | PrList (Cons(x,xs),t1) , PrList (Cons(y,ys),t2) ->
                         assert(t1 = t2);
                         let cons1,funs1,new_not_cong =
                           get_congruence_prop x y const_eq fun_eq not_cong
                         in
                         get_congruence_prop
                           (PrList (xs,t1)) (PrList (ys,t2)) cons1 funs1 new_not_cong
                      | PrList (Nil,t1) , PrList (Nil,t2) ->
                         assert(t1 = t2);
                         const_eq , fun_eq , not_cong
                      | PrList (AbsList id1,t1) , PrList (AbsList id2,t2) ->
                         assert(t1 = t2);
                         (id1 = id2) && const_eq , fun_eq , (id1<>id2) || not_cong
                      | PrList (AbsList _,_) , _ | _ , PrList (AbsList _,_)
                        | PrList (Nil,_) , _ | _ , PrList (Nil,_) ->
                         false , fun_eq , true
                      | v1 , v2 ->
                         (** BUG: T1 =/= T2 SHOULD NOT HAPPEN,
                             THIS CAN ONLY BE IF A1 =/= A2, OR TYPE CHECKING FAILED **)
                         (print_endline (string_of_trans label1);
                          print_endline (string_of_trans label2);
                          print_endline (string_of_prvalue v1);
                          print_endline (string_of_prvalue v2);
                          failwith "pr move: congruence mismatch (v1 <> v2)")
                    in
                    let cons_eq,funs_eq,no_cong = get_congruence_prop v1 v2 true true false in
                    assert(funs_eq);

                    let labels_different =
                      if v1 = v2 then false else (* concrete v1 = v2 handled, no need to set false *)
                        if cons_eq
                        then (* concrete vals in tuple equal, check symbolic vals *)
                          no_cong (* set to false tho *)
                        else (* concrete vals in tuple not equal, no need to check symbolic vals *)
                          true
                    in
                    not labels_different
                  in
                  (** TODO: refactor **)
                  let generalise_on_sigma new_sigma = c11.s,c21.s,new_sigma,None,None in

                  match label1,label2 with
                  | PrRet prv1, PrRet prv2 ->
                     let labels_equal = check_congruence_sat prv1 prv2 sigma2 in
                     let gen_s1,gen_s2,gen_sigma2,gen1,gen2 = generalise_on_sigma sigma2 in
                     let gen_s1',gen_s2',gen_sigma2',gen1',gen2' =
                       apply_sync_generalisation (Some label1) (Some label2) gen_s1 gen_s2 gen_sigma2
                     in
                     if labels_equal
                     then
                       begin
                         (* yes, they are equivalent under some assignment *)
                         let final_cfg_pair =
                           {cfg_pair with c1 = Some {c11 with s = gen_s1'};
                                          c2 = Some {c21 with s = gen_s2'};
                                          tr = label1 :: tr;
                                          bound = ({bound10 with internal = bound1},
                                                   {bound20 with internal = bound2});
                                          sigma = (gen_sigma2')}
                         in
                         (* perform PrRet if current move is PrRet *)
                         pr_ret rest2 final_cfg_pair
                       end
                     else
                       begin
                         (* no, so we enter bottom mode *)
                         let final_cfg_pair1 =
                           {cfg_pair with c1 = Some {c11 with s = gen_s1'};
                                          c2 = None;
                                          tr = label1 :: (Markup (rhs_fail label2)) :: tr;
                                          bound = ({bound10 with internal = bound1},
                                                   {bound20 with internal = bound2});
                                          sigma = (gen_sigma2')}
                         in
                         let final_cfg_pair2 =
                           {cfg_pair with c1 = None;
                                          c2 = Some {c21 with s = gen_s2'};
                                          tr = label2 :: (Markup (lhs_fail label1)) :: tr;
                                          bound = ({bound10 with internal = bound1},
                                                   {bound20 with internal = bound2});
                                          sigma = (gen_sigma2')}
                         in
                         (* perform PrRet if current move is PrRet *)
                         pr_ret (pr_ret rest2 final_cfg_pair1) final_cfg_pair2
                       end

                  | PrCall (AbsFun (a1, _, _, _, _), prv1) ,
                    PrCall (AbsFun (a2, _, _, _, _), prv2) ->
                     let labels_equal =
                       if a1 = a2
                       then check_congruence_sat prv1 prv2 sigma2
                       else false
                     in
                     let gen_s1,gen_s2,gen_sigma2,gen1,gen2 = generalise_on_sigma sigma2 in
                     let gen_s1',gen_s2',gen_sigma2',gen1',gen2' =
                       apply_sync_generalisation (Some label1) (Some label2) gen_s1 gen_s2 gen_sigma2
                     in
                     if a1 = a2 && labels_equal
                     then
                       begin
                         (* yes, they are equivalent under some assignment *)
                         let final_cfg_pair =
                           {cfg_pair with c1 = Some {c11 with s = gen_s1'};
                                          c2 = Some {c21 with s = gen_s2'};
                                          tr = label1 :: tr;
                                          bound = ({bound10 with internal = bound1},
                                                   {bound20 with internal = bound2});
                                          sigma = gen_sigma2'}
                         in
                         final_cfg_pair :: rest2
                       end
                     else
                       begin
                         (* no, so we enter bottom mode *)
                         let final_cfg_pair1 =
                           {cfg_pair with c1 = Some {c11 with s = gen_s1'};
                                          c2 = None ;
                                          tr = label1 :: (Markup (rhs_fail label2)) :: tr;
                                          bound = ({bound10 with internal = bound1},
                                                   {bound20 with internal = bound2});
                                          sigma = gen_sigma2'}
                         in
                         let final_cfg_pair2 = 
                           {cfg_pair with c1 = None;
                                          c2 = Some {c21 with s = gen_s2'};
                                          tr = label2 :: (Markup (lhs_fail label1)) :: tr;
                                          bound = ({bound10 with internal = bound1},
                                                   {bound20 with internal = bound2});
                                          sigma = gen_sigma2'}
                         in
                         final_cfg_pair1 :: final_cfg_pair2 :: rest2
                       end
                  | _ -> (** when labels don't match **)
                     let gen_s1,gen_s2,gen_sigma2,gen1,gen2 = generalise_on_sigma sigma2 in
                     let gen_s1',gen_s2',gen_sigma2',gen1',gen2' =
                       apply_sync_generalisation (Some label1) (Some label2) gen_s1 gen_s2 gen_sigma2
                     in
                     let final_cfg_pair1 =
                       {cfg_pair with c1 = Some {c11 with s = gen_s1'};
                                      c2 = None;
                                      tr = label1 :: (Markup (rhs_fail label2)) :: tr;
                                      bound = ({bound10 with internal = bound1},
                                               {bound20 with internal = bound2});
                                      sigma = gen_sigma2'}
                     in
                     let final_cfg_pair2 = 
                       {cfg_pair with c1 = None;
                                      c2 = Some {c21 with s = gen_s2'};
                                      tr = label2 :: (Markup (lhs_fail label1)) :: tr;
                                      bound = ({bound10 with internal = bound1},
                                               {bound20 with internal = bound2});
                                      sigma = gen_sigma2'}
                     in
                     pr_ret (pr_ret rest2 final_cfg_pair1) final_cfg_pair2
                end
           | (_, _, _, _, _) -> (print_endline "Internal error! unexpected value"; assert false;)
         in
         List.fold_right (fun conf rest -> cases_of_c2 conf rest) c2_confs rest
       end
    | (_, _, _, _, _) -> (print_endline "Internal error! unexpected value"; assert false;)
  in
  List.fold_right (fun conf rest -> cases_of_c1 conf rest) c1_confs []

type config_kind = Opponent | Proponent

(*** FUNCTIONS TO START THE GAME ***)
(* USING MUTABLE STACK/QUEUE *)
let print_success_message init_bound =
  Printf.printf
    "END! Nothing more to explore; no difference was found between the terms with bound = %d. "
    init_bound;
  if !bound_reached
  then
    begin
      begin
        if !twice_twice
        then print_endline "Could not prove the counterexample found through generalisation is real. Please try with a larger bound, or update the invariant."
        else print_endline "However the bound was exceeded in some plays."
      end;
      exit exit_unknown
    end
  else
    begin
      print_endline "The bound was not exceeded - the terms are indeed equivalent!";
      exit exit_eq
    end

let check_cfg_equality cfg_pair =
  (* TODO: THIS IS HACKY! I don't know why g's are not equal, but their strings are*)
  match minimal_of_cfg_opt cfg_pair.c1 , minimal_of_cfg_opt cfg_pair.c2 with
  | Some {min_g = g1; min_s = s1; min_e = e1} ,
    Some {min_g = g2; min_s = s2; min_e = e2} ->
     let g_eq = (string_of_list string_of_val g1) = (string_of_list string_of_val g2) in
     let s_eq = (s1 = s2) in
     let e_eq = (e1 = e2) in
     let beta_graph_bindings = BetaMap.bindings cfg_pair.beta_graph in
     let e1s,e2s =
       List.fold_left
         (fun (acc1,acc2) (k,eebs) ->
           List.fold_left
             (fun (acc1,acc2) (eeb:EEBeta.t) -> eeb.e1::acc1 , eeb.e2::acc2) (acc1,acc2) eebs)
         ([],[]) beta_graph_bindings
     in
     let ee_eq = e1s = e2s in

     g_eq && s_eq && e_eq && ee_eq
  | _ , _ -> false

let op_gc_normalisation_memoisation cfg_pair0 memo_cache =
  if not !flag_memo then Some cfg_pair0 else
    let normalised_cfg_pair , cfg_pair1 , garbage_collected_sigma =
      gc_normalisation cfg_pair0
    in
    (*** UP-TO IDENTITY ***)
    (*g: g_map; k: typed_eval_cxt list; s: store;*)
    debug_id_prints normalised_cfg_pair;
    if check_cfg_equality normalised_cfg_pair && !flag_id
    then
      begin
        print_debug_id "configuration pruned"; None
      end
    else
      
      (*** ATTEMPT MEMOISATION ***)
      if not (Memoisation.add memo_cache (minimal_of_cfg_pair normalised_cfg_pair))
      then (None) (* memoisation failed, i.e. config already seen *)
      else (Some {cfg_pair1 with sigma = garbage_collected_sigma})


(* PR UP-TO TECHNIQUES *)
let pr_upto_techniques cfg_pair =
  upto_separation cfg_pair

(* OP STACK CLOSURE. Performed directly after a PR RET. *)
(* OpClosure:
   1. get label of CFG_PAIR
   2. if label is Return, we proceed
   3.
   *)
(*let oclosure_of_cfg_list cfg_list =
  let oclosure_of_cfg_pair acc cfg_pair =
    let label = "" in
    let check_label = label = "ret" in
    cfg_pair::acc
  in
  List.fold_left oclosure_of_cfg_pair [] cfg_list*)

(* PR MOVES. Helper function to chain things that occur on the pr side. *)
let pr_moves cfg_pair =
  let pr_cfgs = pr_transitions (pr_upto_techniques cfg_pair) in pr_cfgs
(*(oclosure_of_cfg_list pr_cfgs)*)

(* OP MOVES. Helper function to chain memoisation and other things on the op side. *)
let op_moves cfg_pair memo_cache =
  match op_gc_normalisation_memoisation cfg_pair memo_cache with
  | None -> []
  | Some cfg_pair -> op_transitions cfg_pair

(* BISIM FUNCTIONS *)
let rec play_bisim_game_bfs cfg_pair_lst init_bound max_pending_confs memo_cache =
  print_debug_confs ("No of configs = " ^ (string_of_int (List.length cfg_pair_lst)));
  if (List.length cfg_pair_lst) > max_pending_confs  then
    (print_endline ("!No of configs = " ^ (string_of_int (List.length cfg_pair_lst))); assert false);
  let is_opponent_cfg_pair {c1; c2} =
    match c1, c2 with
    | None, None -> true
    | Some {e=OContext _}, _ -> true
    | _, Some {e=OContext _} -> true
    | _, _ -> false
  in
  let get_next next_cfg_lst cfg_pair =
    print_debug_beta_graph_size (string_of_int (BetaMap.cardinal cfg_pair.beta_graph));
    (*** this makes the tool not find inequivalences it did before; e.g., ex1v1-ineq.bils ***)
    if (min (fst cfg_pair.bound).call (snd cfg_pair.bound).call <= 0)
       || (min (fst cfg_pair.bound).ret (snd cfg_pair.bound).ret <= 0)
       || (min (fst cfg_pair.bound).internal (snd cfg_pair.bound).internal <= 0)
    then begin
        do_bound_reached cfg_pair;
        print_debug_traces
          (Printf.sprintf "Bound Reached on trace:\n%s" (string_of_trace cfg_pair.tr));
        next_cfg_lst
      end
    else
      (* for performance put the short lists first (1-4 elements);
         next_cfg_lst can be arbitrarily long (100K elemens) *)
      if is_opponent_cfg_pair cfg_pair
      then (op_moves cfg_pair memo_cache) @ next_cfg_lst
      else (pr_moves cfg_pair) @ next_cfg_lst
  in
  match cfg_pair_lst with
  | [] -> print_success_message init_bound
  | _  -> play_bisim_game_bfs
            (List.fold_left get_next [] cfg_pair_lst) init_bound max_pending_confs memo_cache

let rec play_bisim_game_dfs cfg_pair_lst init_bound max_pending_confs memo_cache =
  print_debug_confs ("No of configs = " ^ (string_of_int (List.length cfg_pair_lst)));
  if (List.length cfg_pair_lst) > max_pending_confs  then
    (print_endline ("!No of configs = " ^ (string_of_int (List.length cfg_pair_lst))); assert false);
  let is_opponent_cfg_pair {c1; c2} =
    match c1, c2 with
    | None, None -> true
    | Some {e=OContext _}, _ -> true
    | _, Some {e=OContext _} -> true
    | _, _ -> false
  in
  let get_next cfg_pair =
    print_debug_beta_graph_size (string_of_int (BetaMap.cardinal cfg_pair.beta_graph));
    (*** this makes the tool not find inequivalences it did before; e.g., ex1v1-ineq.bils ***)
    if (min (fst cfg_pair.bound).call (snd cfg_pair.bound).call <= 0)
       || (min (fst cfg_pair.bound).ret (snd cfg_pair.bound).ret <= 0)
       || (min (fst cfg_pair.bound).internal (snd cfg_pair.bound).internal <= 0)
    then begin
        do_bound_reached cfg_pair;
        print_debug_traces
          (Printf.sprintf "Bound Reached on trace:\n%s" (string_of_trace cfg_pair.tr));
        []
      end
    else
      if is_opponent_cfg_pair cfg_pair
      then (op_moves cfg_pair memo_cache)
      else (pr_moves cfg_pair)
  in
  match cfg_pair_lst with
  | [] -> print_success_message init_bound
  | cfgp :: cfgp_rest  -> play_bisim_game_dfs ((get_next cfgp) @ cfgp_rest) init_bound max_pending_confs memo_cache


(* TOP LEVEL FUNCTION *)
let start_bisim_game e1 e2 bound0
      (_,t,c,b,m,n,g,s,r,i,a,l,f,z,u,h,e,p) traversal maxpending maxcache
      (fn,fg,fs,fr,fi,fa,fl,ff,fz,fu,fh)=
  debug_traces := t;
  debug_confs := c;
  debug_leaf_confs := e;
  debug_sigma := b;
  debug_memo := m;
  debug_norm := n;
  debug_gc := g;
  debug_sep := s;
  debug_nr := r;
  debug_id := i;
  debug_sigma_gc := a;
  debug_sigma_norm := l;
  debug_sigma_simp := f;
  debug_generalise := z;
  debug_gamma_duplicates := u;
  debug_reachable_beta_graph := h;
  debug_beta_graph_size := p;

  flag_memo := (not (maxcache = 0));
  flag_norm := fn;
  flag_gc := fg;
  flag_sep := fs;
  flag_nr := fr;
  flag_id := fi;
  flag_sigma_gc := fa;
  flag_sigma_norm := fl;
  flag_sigma_simp := ff;
  flag_generalise := fz;
  flag_gamma_duplicates := fu;
  flag_reachable_beta_graph := fh;

  print_debug_traces "TRACES DEBUG: enabled";
  print_debug_confs "CONFIGS DEBUG: enabled";
  print_debug_sigma "SYMBOLIC DEBUG: enabled";
  print_debug_memo "MEMOISATION DEBUG: enabled";
  print_debug_memo (Printf.sprintf "MEMOISATION FLAG: %b" !flag_memo);
  print_debug_norm "NORMALISATION DEBUG: enabled";
  print_debug_norm (Printf.sprintf "NORMALISATION FLAG: %b" !flag_norm);
  print_debug_gc "GARBAGE-COLLECTION DEBUG: enabled";
  print_debug_gc (Printf.sprintf "GARBAGE-COLLECTION FLAG: %b" !flag_gc);
  print_debug_sep "SEPARATION DEBUG: enabled";
  print_debug_sep (Printf.sprintf "SEPARATION FLAG: %b" !flag_sep);
  print_debug_nr "NAME-REUSE DEBUG: enabled";
  print_debug_nr (Printf.sprintf "NAME-REUSE FLAG: %b" !flag_nr);
  print_debug_sigma_gc "SIGMA-GC DEBUG: enabled";
  print_debug_sigma_gc (Printf.sprintf "SIGMA-GC FLAG: %b" !flag_sigma_gc);
  print_debug_sigma_norm "SIGMA-NORM DEBUG: enabled";
  print_debug_sigma_norm (Printf.sprintf "SIGMA-NORM FLAG: %b" !flag_sigma_norm);
  print_debug_sigma_simp "SIGMA-SIMP DEBUG: enabled";
  print_debug_sigma_simp (Printf.sprintf "SIGMA-SIMP FLAG: %b" !flag_sigma_simp);
  print_debug_generalise "GENERALISATION DEBUG: enabled";
  print_debug_generalise (Printf.sprintf "GENERALISATION FLAG: %b" !flag_generalise);
  print_debug_gamma_duplicates "GAMMA-DUPLICATES DEBUG: enabled";
  print_debug_gamma_duplicates (Printf.sprintf "GAMMA-DUPLICATES FLAG: %b" !flag_gamma_duplicates);
  print_debug_reachable_beta_graph "REACHABLE BETA GRAPH DEBUG: enabled";
  print_debug_reachable_beta_graph (Printf.sprintf "REACHABLE BETA FLAG: %b" !flag_reachable_beta_graph);
  let bound00 = {call = bound0; ret = bound0; internal = bound0} in

  let start_bisim () =
    let memo_cache = init_memoisation_cache maxcache in
    let init_cfgp =
      [{a = empty_abs_set;
        c1 = Some {g = g_empty (); s = StoreMap.empty; e = PTerm {ecxt = []; e = e1}};
        c2 = Some {g = g_empty (); s = StoreMap.empty; e = PTerm {ecxt = []; e = e2}};
        tr = []; bound = (bound00,bound00); sigma = ([] , (empty_dtree,not fa));
        beta = Beta.init; beta_graph = beta_graph_init}]
    in
    if traversal = 0 then
      (play_bisim_game_bfs init_cfgp bound0 maxpending memo_cache) (* BFS *)
    else
      (play_bisim_game_dfs init_cfgp bound0 maxpending memo_cache) (* DFS *)
  in
  retry_fun := start_bisim;
  start_bisim ()
