let exec_location =
   Filename.dirname (Filename.dirname (Sys.executable_name))

let libdir =
   Filename.concat
     (Filename.concat exec_location "lib")
     "why3"

let datadir =
   Filename.concat
     (Filename.concat exec_location "share")
     "why3"
