module type Sig =
sig
  type t
  val tag : t -> int
end

module type S =
sig
  type elt
  type t

  val all : (elt list -> elt list) -> t
  val fold_map_right : ('a -> elt -> ('a * elt list)) -> 'a -> t
  val fold_map_left : ('a -> elt -> ('a * elt list)) -> 'a -> t
  val elt : (elt -> elt list) -> t

  val compose : t -> t -> t
  val apply : t -> elt list -> elt list
  val clear : t -> unit
end

module Make (X : Sig) =
struct
  type elt = X.t

  (* The datastructure for hashconsed list *)
  module L = 
  struct
    type t = (int * elt) list
    let equal a b = 
      match a,b with
        | [], [] -> true
        | [], _ | _, [] -> false
            (* work evenif al and bl are nil *)
        | (_,ae)::al,(_,be)::bl -> X.tag ae = X.tag be && al == bl
    let hash a = 
      match a with
        | [] -> 0
        | (_,ae)::[] -> X.tag ae
        | (_,ae)::(at,_)::_ -> Hashcons.combine (X.tag ae) at
    let tag t = function
        | [] -> []
        | (_,ae)::al -> (t,ae)::al
  end

  module LH = Hashcons.Make(L)

  let empty = []
  let cons e l = LH.hashcons ((0,e)::l)
  let tag_elt = X.tag
  let tag_t = function
    | [] -> -1
    | (t,_)::_ -> t

  (* the memoisation is inside the function *)
  type t = { all : L.t -> L.t;
             clear : unit -> unit;
             memo_to_list : (int,elt list) Hashtbl.t }

  let memo f tag h x =
    try Hashtbl.find h (tag x:int)
    with Not_found -> 
      let r = f x in
      Hashtbl.add h (tag x) r;
      r


  let fold_map_left f_fold v_empty =
    let memo_t = Hashtbl.create 64 in
    let rewind edonev eltss = 
      let edone,_ = List.fold_left 
        (fun (edone,v) (tag,elts) -> 
           let v,l = f_fold v elts in
           let edone = List.fold_left (fun e t -> cons t e) edone l in
           Hashtbl.add memo_t tag (edone,v);
           (edone,v)) edonev eltss in
      edone in
    let rec f acc t1 = 
      match t1 with
        | [] -> rewind (empty,v_empty) acc
        | (tag,e)::t2 -> 
            try 
              let edonev = Hashtbl.find memo_t tag in
              rewind edonev acc
            with Not_found -> f ((tag,e)::acc) t2 
    in
    {all = f [];
     clear = (fun () -> Hashtbl.clear memo_t);
     memo_to_list = Hashtbl.create 16} 

  let elt f_elt = 
    let memo_elt = Hashtbl.create 64 in
    let f_elt () x = (),memo f_elt tag_elt memo_elt x in
    let f = fold_map_left f_elt () in
    {f with clear = fun () -> Hashtbl.clear memo_elt; f.clear ()}

  let fold_map_right f_fold v_empty =
    let rec f (acc,v) t = 
      match t with
        | [] -> List.fold_left (List.fold_left (fun t e -> cons e t)) empty acc
        | (_,e)::t -> 
            let v,res = f_fold v e in
            f (res::acc,v) t in
    let memo_t = Hashtbl.create 16 in
    { all = memo (f ([],v_empty)) tag_t memo_t;
      clear = (fun () -> Hashtbl.clear memo_t);
      memo_to_list = Hashtbl.create 16}

  let to_list =
    let rec aux acc t =
    match t with
      | [] -> acc
      | (_,e)::t -> aux (e::acc) t
    in
    aux []

  let from_list = List.fold_left (fun t e -> cons e t) empty        

  let all f =
    let f x = from_list (f (to_list x)) in
    let memo_t = Hashtbl.create 16 in
    { all = memo f tag_t memo_t;
      clear = (fun () -> Hashtbl.clear memo_t);
      memo_to_list = Hashtbl.create 16}


  let compose f g = {all = (fun x -> g.all (f.all x));
                     clear = (fun () -> f.clear (); g.clear ());
                     memo_to_list = g.memo_to_list}
  let apply f x = 
    let res = f.all (from_list x) in
    memo to_list tag_t f.memo_to_list res

  let clear f = f.clear ();Hashtbl.clear f.memo_to_list

end

open Term
open Ty
open Theory

module SDecl =
  struct
    type t = decl
    let tag x = x.d_tag
  end

module TDecl = Make(SDecl)

module SDecl_or_Use =
  struct
    type t = decl_or_use
    let tag = function
      | Decl d -> -d.d_tag
      | Use t -> 1+t.th_name.Ident.id_tag 
  end

module TDecl_or_Use = Make(SDecl_or_Use)
