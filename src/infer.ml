open Stdlib
open Common
open Syntax
open Env
open PS
open Unify


let rec print_vars l = match l with
  |[] -> ";"
  |t::q -> Printf.sprintf "%s %s" (string_of_var t) (print_vars q)
                                            
(** Type inference *)
let rec type_inference e env =
  match e.desc with
  |Var x -> begin try (Env.ty_var x env, env)
                  with Not_found -> error "unknown identifier %s" (string_of_var x)
            end
  |Coh (c,u) -> let env = checkT u (Env.add_rec env (PS.ctx_of_ps c)) in
                (*debug "ps_vars : %s" (print_vars (ps_vars c));
                debug "free_vars : %s" (print_vars (free_vars u));*)
                if List.included (ps_vars c) (free_vars u) then (u,env)
                (** TODO : write the second condition *)
                else error "not algebraic" 
  |Sub(t,s) -> begin match t.desc with
               |Coh(c,_) -> let env = check_sub s (PS.ctx_of_ps c) env in
                            let ty,env = type_inference t env in (mk ~pos:e.pos ~show:e.show (Sub (ty,s)),env)
               |_ ->  assert (false)
               end
  |(Obj |Arr _ |Badsub _) -> error "this expression does not have a type"
and checkT e env =
  match e.desc with
  |Obj -> env
  |Arr (t,u,v) -> let env' = checkType u t env in
                  let env'' = checkType v t env' in
                  (checkT t env'')
  |_ -> error "expression %s is not a valid type" (to_string e) 
and checkType e1 e2 env =
  let ty1,env = type_inference e1 env in
  let sub = checkUnify e2 ty1 env in Env.add_meta sub env
and check_sub s c env =
  match s,c with
  |[],[] -> env
  |(x,t)::s, (y,(None,u))::c when x = y ->
    let env = check_sub s c env in
    let env_temp = checkT u (c, snd env) in
    let env = (fst env, snd env_temp) in
    let ty,env = type_inference t env in
    (fst env, checkUnify (substitute u s) ty env)
  |_,_ -> error "not a correct substitution"
    
                                        
let infer e env = let ty,env = (type_inference (normalize e env) env) in (normalize ty env, env)
    
  
let renew_vars e env =
  match e.desc with
  |Coh(ps,t) -> let ps,s = PS.rename_vars ps in
                (mk ~pos:e.pos ~show:e.show (Coh(ps, substitute t s)), Env.add_rec env (PS.ctx_of_ps ps)) 
  |_ -> (e,env)

