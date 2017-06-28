open Common
open Syntax
open Ctx
open Unify
       
module Env = struct
  type t = Ctx.t * ((int * expr) list)

  let to_string (env:t) = Ctx.to_string (fst env)
                                        
  let add (env:t) x ?value t : t =
    match value with
    |Some value -> (Ctx.add (fst env) x ~value:value t, snd env)
    |None -> (Ctx.add (fst env) x t, snd env)

  let add_rec (env1:t) (env2:Ctx.t) : t =
   (Ctx.add_rec (fst env1) env2, snd env1)
                                                          
  let ty_var x (env:t) =
    Ctx.ty_var x (fst env)

  let val_var x (env:t) =
    Ctx.val_var x (fst env)

  let rec add_evar i x env =
    try let y = List.assoc i (snd env) in
        let sub = Unify.checkUnify x y env in
        let env = add_meta sub env in
        (fst env, (i,x)::(snd env))
    with Not_found -> (fst env, (i,x)::(snd env))
  and add_meta l env =
    match l with
    |[] -> env
    |(i,x)::q -> add_meta q (add_evar i x env)


                                                         
                                  
end
