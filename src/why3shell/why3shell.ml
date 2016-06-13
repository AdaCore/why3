

module Unix_scheduler = struct

    let idle_handler = ref []

    let insert_idle_handler p f =
      let rec aux l =
        match l with
          | [] -> [p,f]
          | (p1,_) as hd :: rem ->
             if p > p1 then (p,f) :: l else hd :: aux rem
      in
      idle_handler := aux !idle_handler

    let timeout_handler = ref []

    let insert_timeout_handler ms t f =
      let rec aux l =
        match l with
          | [] -> [ms,t,f]
          | (_,t1,_) as hd :: rem ->
             if t < t1 then (ms,t,f) :: l else hd :: aux rem
      in
      timeout_handler := aux !timeout_handler


    let idle ~(prio:int) f = insert_idle_handler prio f

    let timeout ~ms f =
      let ms = float ms /. 1000.0 in
      let time = Unix.gettimeofday () in
      insert_timeout_handler ms (time +. ms) f

     let buf = Bytes.create 256

     let main_loop interp =
       try
         while true do
           (* attempt to run the first timeout handler *)
           let time = Unix.gettimeofday () in
           match !timeout_handler with
             | (ms,t,f) :: rem when t <= time ->
                timeout_handler := rem;
                let b = f () in
                let time = Unix.gettimeofday () in
                if b then insert_timeout_handler ms (ms +. time) f
             | _ ->
                (* attempt to run the first idle handler *)
                match !idle_handler with
                | (p,f) :: rem ->
                   idle_handler := rem;
                   let b = f () in
                   if b then insert_idle_handler p f
                | [] ->
                   (* check stdin for a some delay *)
                   let delay =
                     match !timeout_handler with
                       | [] -> 0.1
                       | (_,t,_) :: _ -> t -. time
                   in
                   let a,_,_ = Unix.select [Unix.stdin] [] [] delay in
                   match a with
                   | [_] -> let n = Unix.read Unix.stdin buf 0 256 in
                            interp (Bytes.sub_string buf 0 (n-1))
                   | [] -> ()
                   | _ -> assert false
         done
       with Exit -> ()

end



(*
module C = Why3.Controller_itp.Make(Unix_scheduler)
 *)

let interp s =
  match s with
    | "a" ->
       let c = ref 10 in
       Unix_scheduler.timeout
         ~ms:1000
         (fun () -> decr c;
                    if !c > 0 then
                      (Format.printf "%d@." !c; true)
                    else
                      (Format.printf "boom!@."; false))
    | "i" ->
       Unix_scheduler.idle
         ~prio:0
         (fun () -> Format.printf "idle@."; false)
    | _ -> Format.printf "unknowm command `%s`@." s



let () =
  Unix_scheduler.main_loop interp
