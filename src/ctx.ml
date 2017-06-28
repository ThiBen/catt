open Common
open Syntax

module Ctx = struct
  type t = (var * (expr option * expr)) list

  let rec string_of_ctx ctx =
    match ctx with
    |(x,(Some e, t))::ctx -> (string_of_ctx ctx)^ Printf. sprintf "%s = %s : %s \n" (string_of_var x) (to_string e) (to_string t)
    |(x,(None, t))::ctx -> (string_of_ctx ctx) ^ Printf.sprintf "%s : %s \n" (string_of_var x) (to_string t)
    |[] -> ""

  let to_string = string_of_ctx

  let add (ctx:t) x ?value t : t = (x,(value,t))::ctx                      

  let rec add_rec (ctx1: t) (ctx2: t) : t =
    match ctx2 with
    |[] -> ctx1 
    |(x,(Some a,b))::ctx2 -> add_rec (add ctx1 x ~value:a b) ctx2
    |(x,(None, b))::ctx2 -> add_rec (add ctx1 x b) ctx2

  let ty_var x (ctx:t) =
    try
      snd (List.assoc x ctx)
    with
      Not_found -> error "unknown identifier %s" (string_of_var x) 

  let val_var x (ctx:t) =
    try
      fst (List.assoc x ctx)
    with
      Not_found -> error "unknown identifier %s" (string_of_var x) 
end
