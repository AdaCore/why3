let abort_with_message s =
   Format.eprintf "%s" s;
   Format.eprintf " Aborting.@.";
   exit 1

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

