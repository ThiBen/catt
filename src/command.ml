open Syntax
open Common
open Infer
open Env      
open Unify
       
type cmd =
  |Decl of var * expr
  |Hyp of var * expr
  |Check of expr
  |Eval of expr
  |Env

type prog = cmd list

let string_of_cmd env cmd=
  match cmd with
  |Decl (x,e) -> Printf.sprintf "let %s = %s" (string_of_var x) (to_string e)
  |Hyp (x,e) -> Printf.sprintf "hyp %s : %s" (string_of_var x) (to_string e)
  |Check e -> Printf.sprintf "check %s" (to_string e)
  |Eval e -> Printf.sprintf "eval %s" (to_string e) 
  |Env -> Printf.sprintf "Environnement:"

let elim_badsub_cmd cmd env =
  match cmd with
  |Decl (x,e) -> Decl (x, elim_badsub e env)
  |Hyp (x,e) -> Hyp (x, elim_badsub e env)
  |Check e -> Check (elim_badsub e env)
  |Eval e -> Eval (elim_badsub e env)
  |Env -> Env

let exec_cmd env cmd =
  let cmd = elim_badsub_cmd cmd env in 
  command "%s" (string_of_cmd env cmd);
  match cmd with
  | Decl (x,e) ->
     let (e,env) = renew_vars e env in
     let (ty,env) = infer e env in
     answer "%s = %s : %s is defined \n" (string_of_var x) (to_string e) (to_string ty);
     Env.add env x ~value:e ty
  | Hyp (x,e) ->
     answer "%s : %s is assumed \n" (string_of_var x) (to_string e);
     let env = checkT e env in Env.add env x e
  | Check e ->
     let ty,env = infer e env in
     answer "%s : %s \n" (to_string e) (to_string ty);
     env
  | Eval e ->
     answer "%s = %s \n" (to_string e) (to_string (normalize e env));
     env
  | Env ->
     answer "------------- \n%s------------- \n" (Env.to_string env);
     env
             
let exec prog =
  let rec aux env = function
    |[] -> ()
    |(t::l)  -> aux (exec_cmd env t) l
  in aux ([],[]) prog
  
