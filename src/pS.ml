open Common
open Syntax
open Ctx
       
module PS = struct
  type t = Syntax.ps

  exception Invalid


  let rename_vars (ps:ps) : ps*sub = 
    let rec aux ps =
    match ps with
    |PNil (x,e)-> let x' = refresh (Name ("_"^(name x))) in
                  (PNil (x',e), [(x,(mk (Var x')))])
    |PCons (q,(x1,e1),(x2,e2)) ->
      let x1' = refresh (Name ("_"^(name x1))) and x2' = refresh (Name ("_"^(name x2))) in
      let renamed,s = aux q in
      let s' = ((x1, (mk (Var x1')))::s) in let s'' = ((x2, (mk (Var x2')))::s') in
      let e1' = substitute e1 s and e2' = substitute e2 s' in
      (PCons(renamed,(x1',e1'),(x2',e2')),s'')
    |PDrop ps -> aux ps
    in aux ps
           
  let extract (e : expr) =
    match e.desc with
    |Coh (ps,_) -> ps
    |(Var _ |Obj |Arr _ |Sub _ |Badsub _) -> error "got %s, but a coherence was expected" (to_string e)
           
  let create_sub (ps : ps) (l : var list) : sub =
    let rec aux ps l =
      match ps,l with
      |PNil (x,t),y::[] -> (x,(mk (Var y)))::[]
      |PCons (ps,(x1,t1),(x2,t2)), y2::y1::l -> (x2,(mk (Var y2)))::(x1,(mk (Var y1)))::(aux ps l)
      |PDrop ps, l -> aux ps l
      |_,_ -> error "application of a coherence must instantiate all the variables"
    in aux ps (List.rev l)

  let rec ctx_of_ps ps  =
    match ps with
    |PNil (x,t) -> Ctx.add [] x t
    |PCons (ps,(x,t),(y,u)) -> Ctx.add (Ctx.add (ctx_of_ps ps) x t) y u
    |PDrop ps -> ctx_of_ps ps

  (** Dangling variable. *)
  let rec marker ps =
    (* Printf.printf "marker: %s\n%!" (to_string ps); *)
    match ps with
    | PNil (x,t) -> x,t
    | PCons (ps,_,f) -> f
    | PDrop ps ->
       let f,tf = marker ps in
       match tf.desc with
       | Arr (_,x,{desc = Var y}) ->
          let t =
            let rec aux = function
              | PNil (x,t) -> assert (x = y); t
              | PCons (ps,(y',ty),(f,tf)) ->
                 if y' = y then ty
                 else if f = y then tf
                 else aux ps
              | PDrop ps -> aux ps
            in
            aux ps
          in
          y,t
       | _ -> raise Invalid

  (** Free variables. *)
  let rec free_vars = function
    | PNil (x,t) -> [x]
    | PCons (ps,(y,_),(f,_)) -> f::y::(free_vars ps)
    | PDrop ps -> free_vars ps

  (** Create from a context. *)
  let make l : t =
    (* Printf.printf "make: %s\n%!" (String.concat_map " " (fun (x,t) -> Printf.sprintf "(%s : %s)" (string_of_var x) (string_of_expr t)) l); *)
    let x0,t0,l =
      match l with
      | (x,t)::l -> assert (t.desc = Obj); x,t,l
      | [] -> error "pasting scheme cannot be empty"
    in
    let rec aux ps = function
      | (y,ty)::(f,tf)::l ->
         begin
           try
             match tf.desc with
             | Arr (_, {desc = Var fx}, {desc = Var fy}) ->
                (* Printf.printf "check: %s:?->%s\n%!" (string_of_var f) (string_of_var y); *)
                if (y <> fy) then error ~pos:tf.pos "not a pasting scheme (following types do not match)";
                let x,tx = marker ps in
                if x = fx then
                  let fvps = free_vars ps in
                  assert (not (List.mem f fvps));
                  assert (not (List.mem y fvps));
                  let ps = PCons (ps,(y,ty),(f,tf)) in
                  aux ps l
                else
                  aux (PDrop ps) ((y,ty)::(f,tf)::l)
             | _ -> error ~pos:tf.pos "not a pasting scheme (types do not match)"
           with
           | Invalid ->
              (* TODO: better position *)
              error ~pos:tf.pos "not a pasting scheme"
         end
      | [x,tx] -> error ~pos:tx.pos "not a pasting scheme (invalid parity)"
      | [] -> ps
    in
    aux (PNil(x0,t0)) l

  (** Height of a pasting scheme. *)
  let rec height = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> height ps + 1
    | PDrop ps -> height ps - 1

  (** Dimension of a pasting scheme. *)
  let rec dim = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> max (dim ps) (height ps + 1)
    | PDrop ps -> dim ps

  (** Source of a pasting scheme. *)
  let source i ps =
    assert (i >= 0);
    let rec aux = function
      | PNil _ as ps -> ps
      | PCons (ps,_,_) when height ps >= i -> aux ps
      | PCons (ps,y,f) -> PCons (aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in
    aux ps

  (** Target of a pasting scheme. *)
  let target i ps =
    assert (i >= 0);
    let replace g = function
      | PNil x -> PNil g
      | PCons (ps,y,f) -> PCons (ps,y,g)
      | _ -> assert false
    in
    let rec aux = function
      | PNil _ as ps -> ps
      | PCons (ps,_,_) when height ps > i -> aux ps
      | PCons (ps,y,f) when height ps = i -> replace y (aux ps)
      | PCons (ps,y,f) -> PCons (aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in
    aux ps

  let rec exists f = function
    | PNil x -> f x
    | PCons (ps,x,y) -> exists f ps || f x || f y
    | PDrop ps -> exists f ps

  let rec map f = function
    | PNil x -> PNil (f x)
    | PCons (ps,x,y) ->
       let ps = map f ps in
       let x = f x in
       let y = f y in
       PCons (ps,x,y)
    | PDrop ps -> PDrop (map f ps)

  let rec fold_left f s = function
    | PNil x -> f s x
    | PCons (ps,x,y) ->
       let s = fold_left f s ps in
       let s = f s x in
       f s y
    | PDrop ps -> fold_left f s ps

  let rec fold_left2 f s ps1 ps2 =
    match ps1, ps2 with
    | PNil x1, PNil x2 -> f s x1 x2
    | PCons (ps1,y1,f1), PCons(ps2,y2,f2) ->
       let s = fold_left2 f s ps1 ps2 in
       let s = f s y1 y2 in
       f s f1 f2
    | PDrop ps1, PDrop ps2 -> fold_left2 f s ps1 ps2
    | (PNil _  | PCons _ | PDrop _), _ -> assert false

  let rec fold_right f ps s =
    match ps with
    | PNil x -> f x s
    | PCons (ps,x,y) ->
       let s = f y s in
       let s = f x s in
       fold_right f ps s
    | PDrop ps -> fold_right f ps s
end
                           
