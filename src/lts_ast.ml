open Ast                 (* Term Abstract Syntax Tree *)
open Reductions_ast
open Reductions          (* Term Semantics Reduction Rules *)
open Z3api               (* Z3 Interface to for symbolic execution *)
open Upto_tools          (* Types and Functions for Upto Techniques *)
open Normalisation
open Generalisations

(* LTS configurations
 *
 * ** config: Single configuration
 * fields:
 * - g: the knowledge environment
 * - k: the evaluation context stack
 * - s: store
 * - e: Some CEK expression (proponent config) / None (opponent config)
 *
 * ** config_pair
 * fields:
 * - a: common set of abstract names
 * - c1: Some config (regular 1st config) / None (bottom 1st config)
 * - c2: Some config (regular 2nd config) / None (bottom 2nd config)
 * - tr: the trace that led to this config pair (last transition is first in the list)
 *
 * Invariants:
 * (c1 = None) OR (c2 = None) OR all of the following hold:
 *
 * - List.length c1.g = List.length c2.g
 * - List.length c1.k = List.length c2.k
 * - c1.e = None iff c2.e = None
 *
 * How to use the g component (knowledge environment list):
 * - New values are added at the beginning of the list.
 * - The head of the list is assumed to have index (List.length g)
 * - The last element in the list is assumed to have index 1
 *
 * *)

(*** proponent values used for LTS labels ***)
type prvalue = PrIndex of int | PrConst of value
               | PrTuple of prvalue list | PrList of prvalue sym_list * Type.t

let rec string_of_prvalue v =
  match v with
  | PrIndex i -> Printf.sprintf "_idx_%d_" i
  | PrConst c -> string_of_val c
  | PrTuple vs -> 
     Printf.sprintf "(%s)" (string_of_sequence "," string_of_prvalue vs)
  | PrList (ls,t) ->
     Printf.sprintf "(%s : %s list)" (SymList.to_string string_of_prvalue ls) (Type.string_of_t t)

(*********************************)
(* GAMMA ENVIRONMENT DEFINITIONS *)
(*********************************)
(*** integer map for Gamma and functions to manipulate Gamma ***)
module StringSet = Set.Make(String)
module IntMap = Map.Make(Int)
type int_val_map = (Ast.value IntMap.t)

type g_map = int_val_map

let g_empty () = IntMap.empty

let g_filter f g = IntMap.filter f g
let g_add v g =
  let new_index =
    match IntMap.max_binding_opt g with
    | Some (max_index,_) -> max_index + 1
    | None -> 1
  in
  IntMap.add new_index v g , new_index

let g_to_list g = IntMap.bindings g
let g_to_val_list g =
  let glist = IntMap.bindings g in
  let sorted_glist = List.sort (fun (k1,_) (k2,_) -> compare k1 k2) glist in
  let vallist = List.map snd sorted_glist in
  vallist
let string_of_g g =
  string_of_sequence ","
    (fun (idx,v) -> Printf.sprintf "(%d,%s)" idx (string_of_val v)) (g_to_list g)

(*******************************)
(* 'Alpha' NAMESET DEFINITIONS *)
(*******************************)
(*** integer set and type map for A ***)
(* module IntSet = Set.Make(Int) --- int set in upto_tools.ml*)
module TypeMap = Map.Make(Type)
type abs_it_map = Type.t IntMap.t
type abs_ti_map = IntSet.t TypeMap.t
type abs_set = {next:int ; it:abs_it_map ; ti:abs_ti_map} (* next id, id -> type, type -> idset *)

let abs_next_id : Type.t -> abs_set -> (int * abs_set) =
  fun t {next;it;ti} ->
  let new_next = next + 1 in
  let next = get_fresh_id () in
  let new_it = IntMap.add next t it in
  let new_ti =
    match TypeMap.find_opt t ti with
    | None -> TypeMap.add t (IntSet.singleton next) ti
    | Some iset -> TypeMap.add t (IntSet.add next iset) ti
  in
  next , {next=new_next ; it=new_it ; ti=new_ti}

let abs_remove_id : int -> abs_set -> abs_set =
  fun id ({next;it;ti} as abs) ->
  match IntMap.find_opt id it with
  | None -> abs
  | Some t ->
     let new_it = IntMap.remove id it in
     let new_ti =
       match TypeMap.find_opt t ti with
       | None -> failwith "abs_remove_id: it and ti desync"
       | Some iset -> TypeMap.add t (IntSet.remove id iset) ti
     in
     {abs with it=new_it;ti=new_ti}

let empty_abs_set = {next=0 ; it=IntMap.empty ; ti=TypeMap.empty}

(****************************************************)
(* LTS TRANSITIONS & EVALUATION CONTEXT DEFINITIONS *)
(****************************************************)
type trans =
  | Tau
  | OpCall of prvalue * value (* gamma index * AbsCon or AbsFun or Tuple of AbsFun/AbsCon *)
  | PrCall of value * prvalue (* AbsFun * value *)
  | OpRet  of value           (* AbsCon or AbsFun or Tuple of AbsFun/AbsCon *)
  | PrRet  of prvalue         (* ConstVal or AbsCon or AbsFun *)
  | Markup of string          (* used in traces to mark certain points *)
type typed_eval_cxt = eval_cxt * Type.t

(*** helper functions ***)
let string_of_trans = function
    | Tau -> "-tau->"
    | OpCall (pri, v) ->
       Printf.sprintf "\n-op_call %s %s->" (string_of_prvalue pri) (string_of_val v)
    | PrCall (v, prv) ->
       Printf.sprintf "\n-pr_call %s %s->" (string_of_val v) (string_of_prvalue prv)
    | OpRet v -> Printf.sprintf "\n-op_ret %s->" (string_of_val v)
    | PrRet v -> Printf.sprintf "\n-pr_ret %s->" (string_of_prvalue v)
    | Markup s -> Printf.sprintf "\n-[ %s ]->" s

let string_of_trace tr =
  List.fold_left (fun rest label -> (string_of_trans label) ^ rest) "" tr

let string_of_typed_eval_cxt (cxt,t) = (Printf.sprintf "(%s : %s)"(Reductions_ast.string_of_ecxt cxt) (Type.string_of_t t))

let rec string_of_k k =
  match k with
  | [] -> "[]"
  | ecxt::xs ->
     (string_of_typed_eval_cxt ecxt)
     ^ "::" ^ (string_of_k xs)

let rhs_fail label = (Printf.sprintf "entering RHS=bot (tried: %s)" (string_of_trans label))
let lhs_fail label = (Printf.sprintf "entering LHS=bot (tried: %s)" (string_of_trans label))

let rec collect_funcs v g =
  let pridx_of_snd (a,b) = (a,PrIndex b) in
  match v with
  | ConstVal _ -> g , PrConst v
  | FunVal   _ -> pridx_of_snd (g_add v g)
  | AbsCon   _ -> g , PrConst v
  | AbsFun   _ -> pridx_of_snd (g_add v g)
  | TupleVal ls ->
     let new_g, idx_list =
       List.fold_right
         (fun v (g',idx_acc) ->
           let new_g , new_prindex = collect_funcs v g' in
           new_g , new_prindex::idx_acc) ls (g,[])
     in new_g , PrTuple idx_list
  | ListVal (ls,t) ->
     let new_g, idx_sym_list = 
       SymList.fold_right
         (fun v (g',idx_acc) ->
           let new_g , new_prindex = collect_funcs v g' in
           new_g , Cons(new_prindex,idx_acc))
         (fun (g',acc) -> function
           | None -> g',acc
           | Some id -> g',AbsList id) ls (g,Nil)
     in new_g , PrList (idx_sym_list,t)

(*************************)
(* STACKLESS DEFINITIONS *)
(*************************)
(* beta definitions: 
   betas are 2 beta parts, one for each configuration, and a symbolic environment.
   since configurations may be Bottom, beta parts are optional.
 *)
(* Beta module: to make betas comparable for sets and maps, we compare their strings. *)
module BetaPart = struct
  type t = {g: g_map ; s: store}
  let to_string {g;s} =
    Printf.sprintf "[(%s) , (%s)]" (string_of_g g) (string_of_s s)
  let compare = compare
end
module Beta = struct
  type t = BetaInit | Beta of {b1: BetaPart.t option; b2: BetaPart.t option; sigma: sigma; l: trans}
  let to_string = function
    | BetaInit -> "<>"
    | Beta {b1;b2;sigma;l} -> 
       let b1_s = string_of_option BetaPart.to_string b1 in
       let b2_s = string_of_option BetaPart.to_string b2 in
       Printf.sprintf " <beta> b1 = {%s} ; b2 = {%s} ; sigma = {%s} ; l = {%s} </beta> " b1_s b2_s (string_of_sigma sigma) (string_of_trans l)
  let stack_to_string bs = string_of_list to_string bs
  let compare = compare
  (** DUMMY INITIAL BETA **)
  let init = BetaInit
  (** CONSTRUCTOR **)
  let mk b1 b2 sigma l = Beta {b1=b1;b2=b2;sigma=sigma;l=l}
end
  
(* beta graph elements definitions:
   * eebeta: pair of optional evaluation contexts and a beta
   * EEBeta module: to make eebetas comparable to Sets, we compare strings
   * EEBetaSet module: adjacency set of every beta; contains corresponding Evaluation Contexts for each adjacent beta
   *)
type o_cxt = Diamond | Cxt of typed_eval_cxt
let string_of_o_cxt = function
  | Diamond -> "<>"
  | Cxt ecxt -> string_of_typed_eval_cxt ecxt
module EEBeta = struct
  type t = {beta': Beta.t; e1: o_cxt option; e2: o_cxt option; beta: Beta.t}
  let to_string {beta';e1;e2;beta} =
    let e1_s , e2_s =
      (string_of_option string_of_o_cxt e1) ,
      (string_of_option string_of_o_cxt e2)
    in Printf.sprintf " <eebeta> %s;%s;%s;%s </eebeta> "
         (Beta.to_string beta') e1_s e2_s (Beta.to_string beta)
  let compare = compare
  (** INIT DUMMY EEBETA **)
  let init : t = {beta'=Beta.init;e1=Some Diamond; e2=Some Diamond;beta=Beta.init}
  (** CONSTRUCTOR **)
  let mk beta' e1 e2 beta : t = {beta';e1;e2;beta}
end
(*module EEBetaSet = Set.Make(EEBeta)*)
let string_of_eebeta_set set = string_of_list EEBeta.to_string (set)


(* beta graph definitions:
   * initial beta and eebeta as dummy values to start the graph with
   * BetaMap module: a Map using Beta as its domain
   * beta_graph: BetaMap that uses EEBetaSet as the codomain (i.e. beta_graph: Beta |-> EEBetaSet)
 *)
module BetaMap = Map.Make(Beta)
type beta_graph = (EEBeta.t list) BetaMap.t
let string_of_beta_graph (graph : beta_graph) =
  let aux (beta_key,beta_set) =
    Printf.sprintf " \n <mapping> %s |-> %s </mapping> " (Beta.to_string beta_key) (string_of_eebeta_set beta_set)
  in
  string_of_list aux (BetaMap.bindings graph)
let beta_graph_init = BetaMap.singleton Beta.init [EEBeta.init]

let beta_graph_add beta_key eebeta_target (beta_graph : beta_graph) =
  let rec add new_elem = function
    | [] -> [new_elem]
    | (x::xs) -> if x = new_elem then (x::xs) else
                   if new_elem < x then new_elem::x::xs else x::(add new_elem xs)
  in
  let f x =
    match x with
    | None -> Some [eebeta_target]
    | Some eebeta_set -> Some (add eebeta_target eebeta_set)
  in
  BetaMap.update beta_key f beta_graph
let list_adjacent_betas : Beta.t -> beta_graph -> EEBeta.t list =
  fun beta beta_graph ->
  match BetaMap.find_opt beta beta_graph with
  | None -> failwith (Printf.sprintf "list_adjacent_betas: beta not found: <%s>"
                        (Beta.to_string beta))
  | Some set -> set

(* reachable betas *)
let rec reachable_beta_graph beta (beta_graph : beta_graph) acc_beta_graph =
  (* we just need to see if beta is already a key, because it is unique in beta_graph *)
  if BetaMap.mem beta acc_beta_graph then acc_beta_graph else
    let f acc (eebeta : EEBeta.t) =
      reachable_beta_graph eebeta.beta beta_graph (beta_graph_add beta eebeta acc)
    in
    List.fold_left f acc_beta_graph (list_adjacent_betas beta beta_graph)

(** EXPERIMENTAL **)
(* minimised reachable betas. converst betas to integers. *)
let mini_beta_init = 0
type beta_id_map = int * (int BetaMap.t)
let empty_beta_id_map = (mini_beta_init+1) , (BetaMap.singleton Beta.init mini_beta_init)
type mini_eebeta = {min_e1 : o_cxt option; min_e2 : o_cxt option; min_beta : int}
let mini_eebeta_init = {min_e1=Some Diamond; min_e2=Some Diamond;min_beta=0}
type mini_beta_graph = (mini_eebeta list) IntMap.t
let mini_beta_graph_init = IntMap.singleton mini_beta_init [mini_eebeta_init]
let rec mini_reachable_beta_graph beta (beta_graph : beta_graph) (nxt_id,id_map) acc_beta_graph =
  (* we just need to see if beta is already a key, because it is unique in beta_graph *)
  if BetaMap.mem beta id_map then (nxt_id,id_map),acc_beta_graph else
    let nxt_id',id_map' = nxt_id+1,(BetaMap.add beta nxt_id id_map) in
    let f (acc_id_map,acc_beta_graph) (eebeta : EEBeta.t) = 
      mini_reachable_beta_graph eebeta.beta beta_graph acc_id_map
        (beta_graph_add beta eebeta acc_beta_graph)
    in
    List.fold_left f ((nxt_id',id_map'),acc_beta_graph) (list_adjacent_betas beta beta_graph)
let minimise_beta_graph beta_graph id_map =
  let f beta eebeta_list acc_min_graph =
    let min_beta =
      match BetaMap.find_opt beta id_map with
      | None -> failwith
                  (Printf.sprintf "minimise_beta_graph: beta not found: %s"
                     (Beta.to_string beta))
      | Some x -> x
    in
    let g ({e1;e2;beta}:EEBeta.t) =
      {min_e1=e1;min_e2=e2;
       min_beta=
         match BetaMap.find_opt beta id_map with
         |None ->
           failwith
             (Printf.sprintf "minimise_beta_graph: beta not found: %s"
                (Beta.to_string beta))
         | Some x -> x} in
    let min_eebeta_list = List.map g eebeta_list in
    IntMap.add min_beta min_eebeta_list acc_min_graph
  in
  BetaMap.fold f beta_graph mini_beta_graph_init
(** END OF EXPERIMENTAL **)

(* new component to replace the expression component for stackless games *)
type context_or_term = OContext of o_cxt | PTerm of cek_exp
let apply_context_or_term f1 f2 = function
  | OContext ecxt -> OContext (f1 ecxt)
  | PTerm term -> PTerm (f2 term)
let dummy_ocontext = OContext Diamond

type bound = {call : int ; ret : int; internal : int}

(******************)
(* CONFIGURATIONS *)
(******************)
type config = {g: g_map; s: store; e: context_or_term}
type config_pair =
  {a: abs_set; c1: config option; c2: config option;
   tr: trans list; bound: bound * bound; sigma: sigma * dep_tree;
   beta_graph: beta_graph; beta: Beta.t}

let string_of_cfg {g; s; e} =
  let e_str = match e with
    | OContext ecxt -> (string_of_o_cxt ecxt)
    | PTerm cek_e ->  (string_of_exp (unfocus cek_e))
  in
  Printf.sprintf "<<<===G = %s;\n===s = %s;\n===e = %s>>>"
    (string_of_g g)
    (string_of_s s)
    e_str

let string_of_cfg_pair {a; c1; c2; tr; bound = (bound1,bound2); sigma = (sigma,dtree);
                        beta_graph; beta} =
  let str_of_c c =
    match c with
    | None -> "."
    | Some c -> string_of_cfg c
  in
  Printf.sprintf
    "<<a = %s;\n  tr = %s;\n  c1 = %s;\n  c2 = %s;\n  bound=%s,%s;\n sigma=%s;\n dtree=%s;\n beta_graph=%s;\n beta=%s>>"
    (string_of_int a.next)
    (string_of_trace tr)
    (str_of_c c1)
    (str_of_c c2)
    (Printf.sprintf "(%d,%d,%d)" bound1.call bound1.ret bound1.internal)
    (Printf.sprintf "(%d,%d,%d)" bound2.call bound2.ret bound2.internal)
    (string_of_sigma sigma)
    (string_of_dtree dtree)
    (string_of_beta_graph beta_graph)
    (Beta.to_string beta)

(*************************
 * SWAP ABS_LIST IN CONF *
 *************************)

(* fold_right to apply the last item first. This is because older subs are added
   to the back of the list first. The front is a newer sub that needs to be applied later. *)
let swap_aux_base list_subs f x = List.fold_right (fun (id,new_ls) x -> f id new_ls x) list_subs x

let abslist_swap_ecxt list_subs ecxt =
  let swap_aux f x = swap_aux_base list_subs f x in
  let abslist_swap_eval_frame frame =
    match frame with
    | ArithECxt (op,vs,es,p) ->
       let vs' = List.map (swap_aux abslist_swap_val) vs in
       let es' = List.map (swap_aux abslist_swap_exp) es in
       ArithECxt (op,vs',es',p)
    | AppOpECxt (e,p) -> AppOpECxt (swap_aux abslist_swap_exp e,p)
    | AppRandECxt (v,p) -> AppRandECxt (swap_aux abslist_swap_val v,p)
    | NewRefECxt (l,t,e,p) -> NewRefECxt (l,t,swap_aux abslist_swap_exp e,p)
    | AssignECxt (l,p) -> AssignECxt (l,p)
    | CondECxt (e1,e2,p) -> CondECxt (swap_aux abslist_swap_exp e1,swap_aux abslist_swap_exp e2,p)
    | LetECxt (id,t,e,p) -> LetECxt (id,t,swap_aux abslist_swap_exp e,p)
    | LetTupleECxt (idts,e,p) -> LetTupleECxt (idts,swap_aux abslist_swap_exp e,p)
    | SeqECxt (e,p) -> SeqECxt (swap_aux abslist_swap_exp e,p)
    | TupleECxt (vs,es,p) ->
       TupleECxt (List.map (swap_aux abslist_swap_val) vs,
                  List.map (swap_aux abslist_swap_exp) es,p)
    | TupleProjECxt (i,j,p) -> TupleProjECxt (i,j,p)
    | TupleFstUpdECxt (i,j,e,p) -> TupleFstUpdECxt (i,j,swap_aux abslist_swap_exp e,p)
    | TupleSndUpdECxt (v,i,j,p) -> TupleSndUpdECxt (swap_aux abslist_swap_val v,i,j,p)
    | MatchECxt (t,e2,i1,i2,e3,p) ->
       MatchECxt (t,swap_aux abslist_swap_exp e2,i1,i2,swap_aux abslist_swap_exp e3,p)
  in
  List.map abslist_swap_eval_frame ecxt

let abslist_swap_g list_subs g =
  let swap_aux = swap_aux_base list_subs in
  IntMap.map (fun v -> swap_aux abslist_swap_val v) g

let abslist_swap_k list_subs k =
  List.map (fun (ecxt,t) -> abslist_swap_ecxt list_subs ecxt, t) k

let abslist_swap_s list_subs s =
  let swap_aux = swap_aux_base list_subs in
  StoreMap.map (swap_aux abslist_swap_val) s

let abslist_swap_e list_subs {ecxt;e} =
  let swap_aux = swap_aux_base list_subs in
  let ecxt' = abslist_swap_ecxt list_subs ecxt in
  let e' = swap_aux abslist_swap_exp e in
  {ecxt=ecxt';e=e'}

let abslist_swap_cfg list_subs {g; s; e} =
  let g' = abslist_swap_g list_subs g in
  let s' = abslist_swap_s list_subs s in
  let e' = apply_context_or_term
             (function Cxt (ecxt,t) -> Cxt (abslist_swap_ecxt list_subs ecxt , t) | x -> x)
             (abslist_swap_e list_subs)
             e
  in
  {g=g';s=s';e=e'}

let rec prvalue_of_value v =
  match v with
  | ConstVal _ -> PrConst v
  | FunVal   _ -> failwith "not implemented"
  | AbsCon   _ -> PrConst v
  | AbsFun   _ -> failwith "not implemented"
  | TupleVal ls -> PrTuple (List.map prvalue_of_value ls)
  | ListVal (ls,t) ->
     let ls' = SymList.map2 prvalue_of_value ls in
     PrList(ls',t)

let rec abslist_swap_prval id_to new_ls v =
  match v with
  | PrList(ls,t) ->
     PrList(SymList.map3
               (abslist_swap_prval id_to new_ls)
               (function
                | AbsList id -> if id = id_to then new_ls else AbsList id
                | x -> x) ls, t)
  | PrTuple ls ->
     PrTuple (List.map (abslist_swap_prval id_to new_ls) ls)
  | _ -> v (* We don't have functions. Those are in Gamma.
              Const don't need to be swapped. *)

let rec abslist_swap_prvalue list_subs v =
  let swap_aux = swap_aux_base list_subs in
  match v with
  | PrIndex _ | PrConst _ -> v
  | PrTuple vs -> PrTuple (List.map (abslist_swap_prvalue list_subs) vs)
  | PrList (ls,t) ->
     let ls' =
       swap_aux
         (fun id_to new_ls acc ->
           let prv_ls = SymList.map2 prvalue_of_value new_ls in
           SymList.map3
             (abslist_swap_prval id_to prv_ls)
             (function
              | AbsList id -> if id = id_to then prv_ls else AbsList id
              | x -> x) acc) ls
     in
     PrList (ls',t)

let abslist_swap_label list_subs =
  let swap_aux = swap_aux_base list_subs in
  function
  | PrCall (v, prv) -> PrCall (swap_aux abslist_swap_val v, abslist_swap_prvalue list_subs prv)
  | PrRet prv -> PrRet (abslist_swap_prvalue list_subs prv)
  | x -> x

