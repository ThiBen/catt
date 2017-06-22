open Common
open Stdlib

let abbrev_mode = true
let show_category = false
let show_instances = true
      
                            
type var =
  | Name of string
  | New of string * int

type expr =
  {
    desc : desc;
    pos : Pos.t;
    show : bool;
  }
and desc =
  | Var of var
  | Type
  | HomType of expr
  | Cat
  | Obj of expr
  | Arr of expr * expr * expr * expr
  | Pi of var * expr * expr
  | Lambda of var * expr * expr
  | App of expr * expr
  | Coh of string * var * ps * expr
  | Functor of expr * expr
  | Aptor of expr * expr
  | Fcoh of string * var * (var * var) * ps * expr
      (** Fcoh (ex,F,(C,D),(x : * ), Ap(F,id C x)->id D (Ap(F,x))) *)
of and ps =
  | PStart of (var * expr)
  | PExt of ps * (var * expr) * (var * expr)
  | PDrop of ps

let mk ?pos ?show desc=
  let pos = match pos with
    | None -> Pos.dummy
    | Some pos ->  pos
  in
  let show = match show with
    | None -> true
    | Some show -> show
  in
  { desc; pos; show }

 let rec ps_fold_right f ps s =
    match ps with
    | PStart x -> f x s
    | PExt (ps,x,y) ->
       let s = f y s in
       let s = f x s in
       ps_fold_right f ps s
    | PDrop ps -> ps_fold_right f ps s
    
let rec free_vars e =
  match e.desc with
  | Var x -> [x]
  | HomType x -> free_vars x
  | Obj x -> free_vars x
  | Type | Cat -> []
  | Arr (c,t,u,v) -> (free_vars c) @ (free_vars t) @ (free_vars u) @ (free_vars v)
  | Pi (x,t,u) -> (free_vars t) @ (List.remove x (free_vars u))
  | Lambda (x,t,u) -> (free_vars t)@(List.remove x (free_vars u))
  | App (f,x) -> (free_vars f)@(free_vars x)
  | Coh (str,c,ps,t) -> List.remove c (ps_fold_right (fun (x,t) l -> (free_vars t)@(List.remove x l)) ps (free_vars t))
  | Functor (c,d) -> (free_vars c)@(free_vars d)
  | Aptor (f,x) -> (free_vars f)@(free_vars x)
  | Fcoh (str,f,(c,d),ps,t) ->
     List.diff (ps_fold_right (fun (x,t) l -> (free_vars t)@(List.remove x l)) ps (free_vars t)) (c::d::[f])
                                   
let string_of_var = function
  | Name s -> s
  | New (s,k) -> if show_instances then s^(Printf.sprintf ".%d" k) else s

let rec to_string e =
  match e.desc with
  | Var x ->
     string_of_var x
  | Type ->
     "Type"
  | HomType c ->
     Printf.sprintf "HomType.%s" (to_string c)
  | Cat ->
     "Cat"
  | Obj c ->
     Printf.sprintf "*.%s" (to_string c) 
  | Arr (c,t,a,b) ->
     if abbrev_mode
     then
       if e.show
       then Printf.sprintf "%s | %s → %s" (to_string t) (to_string a) (to_string b)
       else Printf.sprintf "%s → %s" (to_string a) (to_string b)
     else Printf.sprintf "%s | %s ->.%s %s" (to_string t) (to_string a) (to_string c) (to_string b)
  | Pi (x,t,e) ->
     if List.mem x (free_vars e)
     then if abbrev_mode
          then Printf.sprintf "∀(%s : %s), %s" (string_of_var x) (to_string t) (to_string e)
          else Printf.sprintf "(%s : %s) => %s" (string_of_var x) (to_string t) (to_string e)
     else Printf.sprintf "%s => %s" (to_string t) (to_string e)
  | Lambda (x,t,e) ->
     if abbrev_mode
     then Printf.sprintf "fun (%s : %s) ↦ %s" (string_of_var x) (to_string t) (to_string e)
     else Printf.sprintf "fun (%s : %s) => %s" (string_of_var x) (to_string t) (to_string e)
  | App (f,e) ->
     let str =
       match e.desc with
       | Var _ -> Printf.sprintf "%s %s" (to_string f) (to_string e)
       | _ ->Printf.sprintf "%s (%s)" (to_string f) (to_string e)
     in
     if not show_category
     then match f.desc
          with
          | Coh _ -> Printf.sprintf "%s" (to_string f)
          | _ -> str
     else str
  | Coh (str,c,ps,t) ->
     if abbrev_mode
     then "Coh_"^str
     else Printf.sprintf "coh %s %s => %s " (string_of_var c)(string_of_ps ps) (to_string t)
  | Functor (e1,e2) ->
     if abbrev_mode
     then Printf.sprintf "%s ⇒ %s" (to_string e1) (to_string e2)
     else Printf.sprintf "Functor(%s,%s)" (to_string e1) (to_string e2)
  | Aptor (f,e) ->
     if abbrev_mode
     then match e.desc with
          | Var _ -> Printf.sprintf "%s.%s" (to_string f) (to_string e)
          | _ -> Printf.sprintf "%s.(%s)" (to_string f) (to_string e)
     else Printf.sprintf "Ap(%s, %s)" (to_string f) (to_string e)
  | Fcoh (str,f,(c,d),ps,t) ->
     if abbrev_mode
     then "Fcoh_"^str
     else Printf.sprintf "Fcoh (%s:%s ⇒ %s) %s => %s " (string_of_var f)(string_of_var c)(string_of_var d)(string_of_ps ps)(to_string t)

and string_of_ps = function
  | PStart (x,t) -> Printf.sprintf "(%s: %s)" (string_of_var x) (to_string t)
  | PExt (ps, (x1, t1), (x2, t2)) -> string_of_ps ps ^ (Printf.sprintf " (%s: %s) (%s: %s)"
                         (string_of_var x1) (to_string t1) (string_of_var x2) (to_string t2)) 
  | PDrop ps -> (string_of_ps ps )^ " ! "

let string_of_expr = to_string


(** Substitutions *)
let refresh =
  let k = ref 0 in
  function
  | Name x | New(x,_) -> incr k; New(x, !k)

let rec subst s e =
  let desc = 
    match e.desc with
    | Var x -> begin try (List.assoc x s).desc with Not_found -> Var x end
    | Type -> Type
    | HomType c -> HomType (subst s c)
    | Cat -> Cat
    | Obj c -> Obj (subst s c)
    | Arr (c,t,a,b) -> Arr (subst s c,subst s t, subst s a, subst s b) 
    | Pi (x,t,e) ->
       let x' = refresh x in
       let s' = ((x, mk ~pos:e.pos (Var x'))::s) in
       Pi (x', subst s t, subst s' e) 
    | Lambda (x,t,e) ->
       let x' = refresh x in
       let s' = ((x, mk ~pos:e.pos (Var x'))::s) in
       Lambda (x', subst s t, subst s' e)
    | App (f,e) -> App (subst s f, subst s e)
    | Coh (str,c,ps,t) ->
       let c' = refresh c in  
       let ps,s = subst_ps ((c, mk (Var c'))::s) ps in
       Coh (str,c',ps,subst s t)
    | Functor (e1, e2) -> Functor (subst s e1, subst s e2)
    | Aptor (f,e) -> Aptor (subst s f, subst s e)
    | Fcoh (str,f,(c,d),ps,t) ->
       let f' = refresh f in
       let ps,s = subst_ps ((f, mk (Var f'))::s) ps in
       Fcoh (str,f',(c,d),ps,subst s t)
  in
  mk ~pos:e.pos desc
and subst_ps s ps =
  let rec aux ps = match ps with   
    | PStart (x,t) -> let x' = refresh x in
                      let is = ((x, mk (Var x'))::s) in
                      (PStart (x', subst s t),is)
    | PExt (ps,(x1,t1),(x2,t2)) -> let x1' = refresh x1 in
                                   let x2' = refresh x2 in
                                   let ps,is = aux ps in
                                   let is' = ((x1, mk (Var x1'))::is) in
                                   let is'' = ((x2, mk (Var x2'))::is') in
                                   (PExt (ps,(x1',subst is t1),(x2',subst is' t2)),is'')
    | PDrop ps -> let ps,is = aux ps in (PDrop ps, is)
  in aux ps
