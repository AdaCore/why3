let cat filter file =
   let cin = open_in file in
   try
      while true do
         let s = input_line cin in
         if filter s then print_endline s
      done
   with End_of_file -> close_in cin

let ends_with s suffix =
   let slen = String.length s in
   let suffixlen = String.length suffix in
   if slen < suffixlen then false
   else
      try
         for i = 1 to suffixlen do
            if s.[slen - i] <> suffix.[suffixlen - i] then raise Exit
         done;
         true
      with Exit -> false

let cmp_timestamps f1 f2 =
   let s1 = Unix.stat f1 in
   let s2 = Unix.stat f2 in
   Pervasives.compare s1.Unix.st_mtime s2.Unix.st_mtime

let abort_with_message s =
   Format.eprintf "%s" s;
   Format.eprintf " Aborting.@.";
   exit 1

let output_buffer buf file =
   let cout = open_out file in
   Buffer.output_buffer cout buf;
   close_out cout

