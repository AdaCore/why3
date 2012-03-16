let colon = ':'

let colon_split s =
   let acc : string list ref = ref [] in
   let last_index = ref (String.length s) in
   let cur_index = ref (String.length s - 1) in
   try
      while true do
         cur_index := String.rindex_from s (!cur_index - 1) colon;
         acc :=
            String.sub s (!cur_index + 1) (!last_index - !cur_index - 1):: !acc;
         last_index := !cur_index;
      done;
      !acc
   with Invalid_argument _ | Not_found ->
      String.sub s 0 (!last_index) :: !acc

exception Found of string

let is_dir_sep c =
   c = Filename.dir_sep.[0] ||
   c = '/'

let contains_dir_sep s =
   try
      String.iter (fun c -> if is_dir_sep c then raise Exit) s;
      false
   with Exit -> true


let absolute_exec_name =
   let exec_name = Sys.executable_name in
   if contains_dir_sep exec_name then
      (* The executable name contains a path component, so just render that
         path absolute *)
      List.fold_left
        (fun acc s -> acc ^ Filename.dir_sep ^ s) ""
        (Sysutil.path_of_file exec_name)
   else
      (* The executable_name is just a file name, so we have to search in
         $PATH *)
      let path_list = colon_split (Sys.getenv "PATH") in
      try
         List.iter (fun p ->
            let full_name = Filename.concat p exec_name in
            if Sys.file_exists full_name then
               raise (Found full_name)) path_list;
         raise Not_found
      with Found s -> s

let exec_location =
   Filename.dirname (Filename.dirname (absolute_exec_name))

let libdir =
   Filename.concat
     (Filename.concat exec_location "lib")
     "why3"

let datadir =
   Filename.concat
     (Filename.concat exec_location "share")
     "why3"
