open Common
open Stdlib

let show_instances = true
let abbrev_mode = false
       
(** Syntax of expressions *)
type var =
  |Name of string
  |New of string * int
                    
type expr =
  {
    desc : desc;
    pos : Pos.t;
    show : bool;                    
  }
and desc =
  |Var of var
  |Evar of int                                                                    
  |Obj
  |Arr of expr * expr * expr
  |Coh of ps * expr
  |Sub of expr * sub
  |Badsub of expr * var list
and ps =
  |PNil of (var * expr)
  |PCons of ps * (var * expr) * (var * expr)
  |PDrop of ps
and sub = (var * expr) list

(** Maker for expressions *)     
let mk ?pos ?show desc =
  let pos = match pos with
    |None -> Pos.dummy
    |Some pos -> pos
  in
  let show = match show with
    |None -> true
    |Some show -> show
  in
  { desc; pos; show }

    
(** Free variables of an expression (useful for pretty printing) *)    
let rec free_vars e =
  match e.desc with
  |Var x -> [x]
  |Obj -> []
  |Arr (t,u,v) -> List.union (List.union (free_vars t)(free_vars u)) (free_vars v)
  |Coh (ps,expr) -> List.union (ps_vars ps) (free_vars expr)
  |Sub (expr,sub) -> List.concat (List.map
                                    (fun x -> try (free_vars (List.assoc x sub))
                                              with Not_found -> [x])
                                    (free_vars expr))
  |Badsub _ -> assert false
and ps_vars ps =
  match ps with
  |PNil(x,t) -> [x]
  |PCons(ps,(x1,t1),(x2,t2)) -> x1::x2::(ps_vars ps)
  |PDrop ps -> ps_vars ps

let rec evars_of e =
  match e.desc with
  |Var _ -> []
  |Evar i -> i::[]
  |Obj -> []
  |Arr (t,u,v) -> List.union (List.union (evars_of t)(evars_of u)) (evars_of v)
  |Coh (ps,u) -> List.union (ps_evars_of ps) (evars_of u)
  |Sub (u,s) -> List.union (evars_of u) (sub_evars_of s)
and ps_evars_of ps =
  match ps with
  |PNil (x,t) -> evars_of t
  |PCons (ps,(x1,t1),(x2,t2)) -> List.union (List.union (evars_of t1) (evars_of t2)) (ps_evars_of ps)
  |PDrop ps -> ps_evars_of ps
and sub_evars_of s =
  match s with
  |[] -> []
  |(x,t)::q -> List.union (evars_of t) (sub_evars_of q)

                          
(** Printing of an expression *)                     
let string_of_var = function
  |Name s -> s
  |New (s,k) ->
    if show_instances then s^(Printf.sprintf ".%d" k) else s

let rec to_string e =
  match e.desc with
  |Var x -> string_of_var x
  |Obj -> "*"
  |Arr (t,u,v) ->
    if abbrev_mode && (not e.show)
    then Printf.sprintf "%s -> %s" (to_string u) (to_string v)
    else Printf.sprintf "%s | %s -> %s" (to_string t) (to_string u) (to_string v)
  |Coh (c,e) ->
    Printf.sprintf "coh %s => %s" (string_of_ps c) (to_string e)
  |Sub (e,s) ->
    Printf.sprintf "%s [%s] " (to_string e) (string_of_sub s)
  |Badsub _ -> assert false
and string_of_ps ps =
  match ps with
  |PNil (x,t) -> Printf.sprintf "(%s,%s)" (string_of_var x) (to_string t)
  |PCons(ps,(x1,t1),(x2,t2)) ->
    Printf.sprintf "%s (%s,%s) (%s,%s)" (string_of_ps ps) (string_of_var x1) (to_string t1) (string_of_var x2) (to_string t2)
  |PDrop ps -> Printf.sprintf "%s!" (string_of_ps ps)
and string_of_sub s =
  match s with
  |[] -> ""
  |(x,t)::c -> Printf.sprintf "%s (%s/%s)" (string_of_sub c) (string_of_var x) (to_string t)


(** Manipulations on variables *)
let name v =
  match v with
  |(Name s |New (s,_)) -> s
    
let refresh =
  let k = ref 0 in
  function
  | Name x | New(x,_) -> incr k; New(x, !k)

                              
(** Performs all possible substitutions *)
let substitute t s pos show=
  let rec subst t s = 
    match t.desc with
    |Var x ->
      begin
        try
          List.assoc x s
        with
          Not_found -> mk ~pos:pos ~show:show (Var x)
      end
    |Obj -> mk ~pos:pos ~show:show Obj
    |Arr (a,u,v) -> mk ~pos:pos ~show:show (Arr (subst a s, subst u s, subst v s))
    |Coh (c,u) -> mk ~pos:pos ~show:show (Sub (t,s))
    |Sub (u,ss) -> begin let u = subst u ss in
                   match u.desc with
                   |Sub (u,ss) -> mk ~pos:pos ~show:show (Sub (u, compose_sub ss s))
                   |_ -> subst u s
                               end
    |Badsub _ -> assert false
  and compose_sub ss s =
    match ss with
    |[] -> s
    |(x,t)::ss -> (x,(subst t s))::(compose_sub ss s)
in subst t s

let substitute ?pos ?show t s =
  let pos = match pos with
    |Some pos -> pos
    |None -> t.pos
  in
  let show = match show with
    |Some show -> show
    |None -> t.show
  in
  substitute t s pos show
