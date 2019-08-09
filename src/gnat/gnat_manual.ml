open Why3

type goal = Session_itp.proofNodeID
type attempt = Session_itp.proofAttemptID

let filename_limit = 246

let manual_attempt_of_goal s goal =
  match Gnat_config.manual_prover with
  | None -> None
  | Some p ->
      let proof_attempts = Session_itp.get_proof_attempt_ids s goal in
      Whyconf.Hprover.find_opt proof_attempts p

let is_new_manual_proof session goal =
  manual_attempt_of_goal session goal = None

(* Returns the theory encapsulating the goal *)
let find_goal_theory s goal =
  Session_itp.get_encapsulating_theory s (Session_itp.APn goal)

let get_file_extension filename =
  try
    let name = Filename.chop_extension filename in
    let ext = String.sub filename (String.length name)
                         (String.length filename - String.length name) in
    ext
  with
  | Invalid_argument _ -> ""

(* Return the absolute dir in which we want to put provers file. *)
let prover_files_dir proj wc_prover =
  match Gnat_config.proof_dir with
  | None -> Filename.dirname Gnat_config.filename
  | Some dir ->
     let prover_dir = Filename.concat dir wc_prover.Whyconf.prover_name in
     if not (Sys.file_exists prover_dir) then
       Unix.mkdir prover_dir 0o750;
     let punit_dir = Filename.concat prover_dir proj in
     if not (Sys.file_exists punit_dir) then
       Unix.mkdir punit_dir 0o750;
     punit_dir

let resize_shape sh limit =
  let index = ref 0 in
  let sh_len = String.length sh in
  let separator_re = Str.regexp "__" in
  (try
    while (sh_len - !index) >= limit do
      index := (Str.search_forward separator_re sh !index) + 2
    done;
    String.sub sh !index (sh_len - !index)
  with
  | _ -> "")

let make_filename sl =
  List.fold_left (fun acc x -> Filename.concat acc x) "" sl

let compute_filename s (contain_dir: string) theory goal expl driver =
  let th_name_no_sanit = (Session_itp.theory_name theory).Ident.id_string in
  let task = Session_itp.get_task s goal in
  let why_fn =
    Driver.file_of_task driver
                        th_name_no_sanit
                        (Session_itp.string_of_file_path (Session_itp.file_path (Session_itp.theory_parent s theory)))
                        task in
  let ext = get_file_extension why_fn in
  let thname = (Ident.sanitizer Ident.char_to_alnumus
                                Ident.char_to_alnumus
                                th_name_no_sanit) in
  (* Remove __subprogram_def from theory name *)
  let thname = String.sub thname 0 ((String.length thname) - 16) in

  (* Prevent generated filename from exceeding usual filesystems limit.
     2 character are reserved to differentiate files having name
     collision *)
  let shape = resize_shape expl.Gnat_expl.shape
                           (filename_limit - ((String.length thname)
                                              + (String.length ext) + 2)) in
  let noext = Filename.concat contain_dir
                              (Pp.sprintf "%s__%s" thname shape)
  in
  let num = ref 0 in
  let filename = ref (noext ^ ext) in
  while Sys.file_exists !filename do
    num := !num + 1;
    filename := noext ^ string_of_int !num ^ ext;
  done;
  !filename

let create_prover_file c goal expl prover =
  let s = c.Controller_itp.controller_session in
  let driver = snd (Whyconf.Hprover.find c.Controller_itp.controller_provers prover) in
  let th = find_goal_theory s goal in
  let proj_name = Filename.basename (Session_itp.get_dir s) in
  let filename =
    compute_filename s (prover_files_dir proj_name prover) th goal expl driver in
  make_filename (Sysutil.relativize_filename (Session_itp.get_dir s) filename)
(*
  let cout = open_out filename in
  let fmt = Format.formatter_of_out_channel cout in
  let task = Session_itp.get_task s goal in
  Driver.print_task prover.Session.prover_driver fmt task;
  close_out cout;
  let pa = add_external_proof ~keygen:Gnat_sched.Keygen.keygen ~obsolete:false
                             ~archived:false ~limit:Call_provers.empty_limit
                             ~edit:(Some filename) goal
                             prover.Session.prover_config.Whyconf.prover
                             Unedited in
  pa
*)

(* ??? maybe use a Buffer.t? Isn't there some code already doing this in Why3?
 * *)
let editor_command (prover: Whyconf.prover) fn =
  (* this function loads the editor for a given prover, otherwise returns a
     default value *)
  let editor =
    let config_prover = Whyconf.get_prover_config Gnat_config.config prover in
    try Whyconf.editor_by_id Gnat_config.config
        config_prover.Whyconf.editor
    with Not_found ->
      { Whyconf.editor_name = "";
        editor_command = "";
        editor_options = [] }
  in
  let cmd_line =
    List.fold_left (fun str s -> str ^ " " ^ s)
                  editor.Whyconf.editor_command
                  editor.Whyconf.editor_options in
  Gnat_config.actual_cmd fn cmd_line

let manual_proof_info session pa =
  let pa = Session_itp.get_proof_attempt_node session pa in
  match pa.Session_itp.proof_script with
  | None -> None
  | Some fn ->
      let fn = Filename.concat (Session_itp.get_dir session) fn in
      let fn = Sysutil.relativize_filename (Filename.dirname Gnat_config.filename) fn in
      let base_prover = pa.Session_itp.prover in
      let real_prover =
        List.find (fun p ->
          p = base_prover)
        Gnat_config.provers in
      let fn = make_filename fn in
      Some (fn, editor_command real_prover fn)
