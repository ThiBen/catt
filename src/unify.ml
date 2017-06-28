open Stdlib
open Common
open Syntax
open Ctx
open PS
       
exception BadUnif
       
(** Normalization of a term, performs the substitutions when possible *)
let rec normalize e env =
  match e.desc with
  |Var x -> let value = (try Ctx.val_var x (fst env) with Error _ -> None) in
            begin match value with
            |None -> e 
            |Some e -> normalize e env
            end
  |Obj -> e
  |Arr (t,u,v) ->
    mk ~pos:e.pos ~show:e.show (Arr (normalize t env, normalize u env, normalize v env))
  |Coh (c,t) ->
    mk ~pos:e.pos ~show:e.show (Coh (normalize_ps c env, normalize t env))
  |Sub (t,s) -> let s = normalize_sub s env in
                let t = normalize t env in
                substitute ~pos:e.pos ~show:e.show t s
  |Badsub (t,l) -> assert false
and normalize_ps c env =
  PS.map (fun (x,t) -> (x,normalize t env)) c
and normalize_sub s env =
  match s with
  |[] -> []
  |(x,t)::s -> (x, normalize t env) :: (normalize_sub s env)



(** Elimination of ill-formed substitutions (syntaxic trick to avoid writing all variables) *)
let rec elim_badsub e env =
  match e.desc with
  |(Var _ | Obj)-> e
  |Arr (t,u,v) -> mk ~pos:e.pos ~show:e.show (Arr(elim_badsub t env, elim_badsub u env, elim_badsub v env))
  |Coh (ps,t) -> let ps = elim_badsub_ps ps env
                 and t = elim_badsub t env in
                 mk ~pos:e.pos ~show:e.show (Coh (ps,t))
  |Sub (t,s) -> let s = elim_badsub_sub s env
                and t = elim_badsub t env in
                mk ~pos:e.pos ~show:e.show (Sub (t,s))
  |Badsub (t,l) -> mk ~pos:e.pos ~show:e.show (Sub (t,PS.create_sub (PS.extract (normalize t env)) l))
and elim_badsub_ps ps env =
  PS.map (fun (x,t) -> (x,elim_badsub t env)) ps
and elim_badsub_sub s env =
  match s with
  |[] -> []
  |(x,e)::s -> (x,elim_badsub e env) :: (elim_badsub_sub s env)
                                         
let isEqual e1 e2 env =
  let rec equal e1 e2 =
    match e1.desc, e2.desc with
    |Var x,Var y -> x = y
    |Obj,Obj -> true
    |Arr(t1,u1,v1),Arr(t2,u2,v2) -> equal t1 t2 && equal u1 u2 && equal v1 v2
    |Coh(c1,t1),Coh(c2,t2) -> equal_ps c1 c2 && equal t1 t2
    |Sub(t1,s1),Sub(t2,s2) -> equal t1 t2 && equal_sub s1 s2
    |(Var _|Obj |Arr _|Coh _|Sub _ | Badsub _),_ -> false
  and equal_ps c1 c2 =
    match c1,c2 with
    |PNil (x1,t1), PNil (x2,t2) -> x1 = x2 && equal t1 t2
    |PCons (ps1,(x1,t1),(y1,u1)), PCons (ps2,(x2,t2),(y2,u2)) -> x1 = x2 && equal t1 t2 && y1 = y2 = equal u1 u2 && equal_ps ps1 ps2
    |PDrop ps1, PDrop ps2 -> equal_ps ps1 ps2
    |(PNil _|PCons _|PDrop _),_ -> false
  and equal_sub s1 s2 =
    match s1,s2 with
    |[],[] -> true
    |(x1,t1)::s1,(x2,t2)::s2 -> x1 = x2 && equal t1 t2 && equal_sub s1 s2
    |([] |(_::_)),_ -> false
  in equal (normalize e1 env) (normalize e2 env)

                      
let checkEqual e1 e2 env =
  if (isEqual e1 e2 env) then () else error ~pos:e1.pos "got %s but %s is expected"
                                            (to_string e1) (to_string e2)

let unify e1 e2 env =
  let res = ref [] in
  let rec unif e1 e2 =
    match e1.desc, e2.desc with
    |Var x,Var y -> if not(x = y) then raise BadUnif 
    |Evar i, _ ->
      begin
        try
          let e1 = List.assoc i !res in unif e1 e2
        with
          Not_found -> if not (List.mem i (evars_of e2)) then res:= ((i,e2)::!res) else raise BadUnif
      end
    |_, Evar i ->
      begin
        try
          let e2 = List.assoc i !res in unif e1 e2
        with
          Not_found -> if not (List.mem i (evars_of e1)) then res:= ((i,e1)::!res) else raise BadUnif
      end
    |Obj,Obj -> ()
    |Arr(t1,u1,v1),Arr(t2,u2,v2) -> unif t1 t2; unif u1 u2; unif v1 v2
    |Coh(c1,t1),Coh(c2,t2) -> unif_ps c1 c2; unif t1 t2
    |Sub(t1,s1),Sub(t2,s2) -> unif t1 t2; unif_sub s1 s2
    |(Var _|Obj |Arr _|Coh _|Sub _ | Badsub _),_ -> raise BadUnif
  and unif_ps c1 c2 =
    match c1,c2 with
    |PNil (x1,t1), PNil (x2,t2) -> if x1 = x2 then unif t1 t2 else raise BadUnif
    |PCons (ps1,(x1,t1),(y1,u1)), PCons (ps2,(x2,t2),(y2,u2)) -> if ((x1 = x2) && (y1 = y2))
                                                                 then
                                                                   (unif t1 t2; unif u1 u2; unif_ps ps1 ps2)
                                                                 else raise BadUnif
    |PDrop ps1, PDrop ps2 -> unif_ps ps1 ps2
    |(PNil _|PCons _|PDrop _),_ -> raise BadUnif
  and unif_sub s1 s2 =
    match s1,s2 with
    |[],[] -> ()
    |(x1,t1)::s1,(x2,t2)::s2 -> if x1 = x2 then (unif t1 t2; unif_sub s1 s2) else raise BadUnif
    |([] |(_::_)),_ -> raise BadUnif
  in unif (normalize e1 env) (normalize e2 env); !res

let checkUnify e1 e2 env =
  try unify e1 e2 env with BadUnif -> error ~pos:e1.pos "got %s but %s is expected (cannot unify the two terms)"
                                            (to_string e1) (to_string e2)
