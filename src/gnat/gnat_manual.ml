open Why3
open Session

type goal = int Session.goal

let filename_limit = 246

let manual_attempt_of_goal goal =
  match Gnat_config.manual_prover with
  | None -> None
  | Some p ->
        PHprover.find_opt goal.goal_external_proofs
          p.Gnat_config.prover.Whyconf.prover

let is_new_manual_proof goal =
  manual_attempt_of_goal goal = None

let rec find_goal_theory goal =
  match goal.goal_parent with
  | Parent_theory th -> th
  | Parent_transf tr -> find_goal_theory tr.transf_parent
  | Parent_metas meta -> find_goal_theory meta.metas_parent

let get_file_extention filename =
  try
    let name = Filename.chop_extension filename in
    let ext = String.sub filename (String.length name)
                         (String.length filename - String.length name) in
    ext
  with
  | Invalid_argument _ -> ""

let prover_files_dir proj prover =
  let wc_prover = prover.Gnat_config.prover.Whyconf.prover in
  match Gnat_config.proof_dir with
  | None -> ""
  | Some dir ->
     let prover_dir = (Filename.concat
                         dir
                         wc_prover.Whyconf.prover_name)
     in
     if not (Sys.file_exists prover_dir) then
       Unix.mkdir prover_dir 0o750;
     let punit_dir = Filename.concat prover_dir proj in
     if not (Sys.file_exists punit_dir) then
       Unix.mkdir punit_dir 0o750;
     Sysutil.relativize_filename (Sys.getcwd ()) punit_dir


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


let compute_filename contain_dir theory goal expl prover =
  let why_fn =
    Driver.file_of_task prover.Gnat_config.driver
                        theory.theory_name.Ident.id_string
                        theory.theory_parent.file_name
                        (goal_task goal) in
  let ext = get_file_extention why_fn in
  let thname = (Ident.sanitizer Ident.char_to_alnumus
                                Ident.char_to_alnumus
                                theory.theory_name.Ident.id_string) in
  (* Remove __subprogram_def from theory name *)
  let thname = String.sub thname 0 ((String.length thname) - 16) in

  (* Prevent generated filename from exeding usual filesystems limit.
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

let create_prover_file goal expl prover =
  let th = find_goal_theory goal in
  let proj_name = Filename.basename
                    (get_project_dir (Filename.basename
                                        th.theory_parent.file_name)) in
  let filename =
    compute_filename (prover_files_dir proj_name prover) th goal expl prover in
  let cout = open_out filename in
  let fmt = Format.formatter_of_out_channel cout in
  Driver.print_task prover.Gnat_config.driver fmt (goal_task goal);
  close_out cout;
  let _ = add_external_proof ~keygen:Gnat_sched.Keygen.keygen ~obsolete:false
                             ~archived:false ~limit:Call_provers.empty_limit
                             ~edit:(Some filename) goal
                             prover.Gnat_config.prover.Whyconf.prover
                             Unedited in
  filename

(* ??? maybe use a Buffer.t? Isn't there some code already doing this in Why3?
 * *)
let editor_command prover fn =
  let editor = prover.Gnat_config.editor in
  let cmd_line =
    List.fold_left (fun str s -> str ^ " " ^ s)
                  editor.Whyconf.editor_command
                  editor.Whyconf.editor_options in
  Gnat_config.actual_cmd fn cmd_line

let manual_proof_info pa =
  match pa.proof_edited_as with
  | None -> None
  | Some fn ->
      let base_prover = pa.Session.proof_prover in
      let real_prover =
        List.find (fun p ->
          p.Gnat_config.prover.Whyconf.prover = base_prover)
        Gnat_config.provers in
      Some (fn, editor_command real_prover fn)
