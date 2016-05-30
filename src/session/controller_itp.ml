open Session_itp

(** State of a proof *)
type proof_attempt_status =
    | Unedited (** editor not yet run for interactive proof *)
    | JustEdited (** edited but not run yet *)
    | Interrupted (** external proof has never completed *)
    | Scheduled (** external proof attempt is scheduled *)
    | Running (** external proof attempt is in progress *)
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)

open Format

let print_status fmt st =
  match st with
  | Unedited -> fprintf fmt "Unedited"
  | JustEdited -> fprintf fmt "JustEdited"
  | Interrupted -> fprintf fmt "Interrupted"
  | Scheduled -> fprintf fmt "Scheduled"
  | Running -> fprintf fmt "Running"
  | Done r -> fprintf fmt "Done(%a)" Call_provers.print_prover_result r
  | InternalFailure e -> fprintf fmt "InternalFailure(%a)" Exn_printer.exn_printer e

type transformation_status =
  | TSscheduled of transID | TSdone of transID | TSfailed

module type Scheduler = sig
  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: (unit -> bool) -> unit
end


module Make(S : Scheduler) = struct

let schedule_proof_attempt s id pr ~timelimit ~callback =
  graft_proof_attempt s id pr ~timelimit;
  callback Scheduled

let schedule_transformations s id name args ~callback =
  let tid = graft_transf s id name args in
  callback (TSscheduled tid)

let read_file env ?format fn =
  let theories = Env.read_file Env.base_language env ?format fn in
  let ltheories =
    Stdlib.Mstr.fold
      (fun name th acc ->
        (* Hack : with WP [name] and [th.Theory.th_name.Ident.id_string] *)
        let th_name =
          Ident.id_register (Ident.id_derive name th.Theory.th_name) in
         match th.Theory.th_name.Ident.id_loc with
           | Some l -> (l,th_name,th)::acc
           | None   -> (Loc.dummy_position,th_name,th)::acc)
      theories []
  in
  let th =  List.sort
      (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
      ltheories
  in
  List.map (fun (_,_,a) -> a) th

let add_file_to_session env s ?format fname =
  let theories = read_file env ?format fname in
  add_file_section s fname theories None

let reload_session_files (_s : session)  =
  failwith "Controller_itp.reload_session_files not yet implemented"

end



let usleep t = ignore (Unix.select [] [] [] t)

module Unix_scheduler = struct

    let idle_handler = ref None
    let timeout_handler = ref None

    let verbose = ref true

     let idle f =
       match !idle_handler with
         | None -> idle_handler := Some f;
         | Some _ -> failwith "Unix_scheduler.idle: already one handler installed"

     let timeout ~ms f =
       match !timeout_handler with
         | None -> timeout_handler := Some(float ms /. 1000.0 ,f);
         | Some _ -> failwith "Unix_scheduler.timeout: already one handler installed"

     let notify_timer_state w s r =
       if !verbose then
         Printf.eprintf "Progress: %d/%d/%d                       \r%!" w s r

     let main_loop () =
       let last = ref (Unix.gettimeofday ()) in
       try while true do
           let time = Unix.gettimeofday () -. !last in
           (* attempt to run timeout handler *)
           let timeout =
             match !timeout_handler with
               | None -> false
               | Some(ms,f) ->
                 if time > ms then
                   let b = f () in
                   if b then true else
                     begin
                       timeout_handler := None;
                       true
                     end
                 else false
           in
           if timeout then
             last := Unix.gettimeofday ()
           else
      (* attempt to run the idle handler *)
             match !idle_handler with
               | None ->
                 begin
                   let ms =
                     match !timeout_handler with
                       | None -> raise Exit
                       | Some(ms,_) -> ms
                   in
                   usleep (ms -. time)
                 end
               | Some f ->
                 let b = f () in
                 if b then () else
                   begin
                     idle_handler := None;
                   end
         done
       with Exit -> ()

end
