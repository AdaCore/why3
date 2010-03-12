(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

let channel_contents_buf cin =
  let buf = Buffer.create 1024
  and buff = String.make 1024 ' ' in
  let n = ref 0 in
  while n := input cin buff 0 1024; !n <> 0 do 
    Buffer.add_substring buf buff 0 !n
  done;
  buf

let channel_contents cin = Buffer.contents (channel_contents_buf cin)

let file_contents_buf f =
  try 
    let cin = open_in f in
    let buf = channel_contents_buf cin in
    close_in cin;
    buf
  with _ -> 
    invalid_arg (Printf.sprintf "(cannot open %s)" f)


let file_contents f = Buffer.contents (file_contents_buf f)

let open_temp_file ?(debug=false) filesuffix usefile =
  let file,cout = Filename.open_temp_file "why" filesuffix in
  try
    let res = usefile file cout in
    if not debug then Sys.remove file;
    close_out cout;
    res
  with
    | e ->    
        if not debug then Sys.remove file;
        close_out cout;
        raise e
