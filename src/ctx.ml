open Common
open Syntax

module Ctx = struct
  type t = (var * (expr option * expr)) list

  let rec string_of_env (env:t) =
    match env with
    |(x,(Some e, t))::env -> (string_of_env env)^ Printf. sprintf "%s = %s : %s \n" (string_of_var x) (to_string e) (to_string t)
    |(x,(None, t))::env -> (string_of_env env) ^ Printf.sprintf "%s : %s \n" (string_of_var x) (to_string t)
    |[] -> ""

  let to_string = string_of_env

  let add (env:t) x ?value t : t = (x,(value,t))::env                      
                    
  let ty_var x env =
    try
      snd (List.assoc x env)
    with
      Not_found -> error "unknown identifier %s" (string_of_var x) 

  let val_var x env =
    try
      fst (List.assoc x env)
    with
      Not_found -> error "unknown identifier %s" (string_of_var x) 
  let ext x ?value t (env:t) = (x,(value,t))::env                                           
end