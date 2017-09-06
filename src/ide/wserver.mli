(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


val multiplier: int


val main_loop : string option -> int ->
                (Unix.sockaddr * string list -> string ->
                     string -> Format.formatter -> unit) ->
                (string -> unit) -> unit
(** [main_loop addr port callback stdin_callback] starts an elementary
    httpd server at port [port] in the current machine. The variable
    [addr] is [Some the-address-to-use] or [None] for any of the
    available addresses of the present machine. The port number is any
    number greater than 1024 (to create a client < 1024, you must be
    root). At each connection, the function [callback] is called as
    [callback (addr, request) scr cont fmt] where [addr] is the client
    identification socket, [request] the browser request, [scr] the
    script name (extracted from [request]) and [cont] the stdin
    contents. [fmt] is the formatter where the answer should be
    written, it must start by a call to [http_header] below.
    [stdin_callback] is called on any stdin input line received. *)

val timeout: ms:int -> (unit -> bool) -> unit
(** [timeout ~ms f] registers the function [f] as a function to be
    called every [ms] milliseconds. The function is called repeatedly
    until it returns false. the [ms] delay is not strictly guaranteed:
    it is only a minimum delay between the end of the last call and
    the beginning of the next call.  Several functions can be
    registered at the same time. *)

val idle: prio:int -> (unit -> bool) -> unit
(** [idle prio f] registers the function [f] as a function to be
    called whenever there is nothing else to do. Several functions can
    be registered at the same time.  Several functions can be
    registered at the same time. Functions registered with higher
    priority will be called first. *)

val http_header : Format.formatter -> string -> unit
(** [http answer] sends the http header where [answer] represents the
    answer status. If empty string, "200 OK" is assumed. *)

val encode : string -> string
(** [encode s] encodes the string [s] in another string where spaces
    and special characters are coded. This allows to put such strings
    in html links <a href=...>. This is the same encoding done by Web
    browsers in forms. *)

val decode : string -> string
(** [decode s] does the inverse job than [Wserver.code], restoring the
    initial string. *)

val extract_param : string -> char -> string list -> string
(** [extract_param name stopc request] can be used to extract some
    parameter from a browser [request] (list of strings); [name] is a
    string which should match the beginning of a request line, [stopc]
    is a character ending the request line. For example, the string
    request has been obtained by: [extract_param "GET /" ' '].
    Answers the empty string if the parameter is not found. *)

val get_request_and_content : char Stream.t -> string list * string

val string_of_sockaddr : Unix.sockaddr -> string
val sockaddr_of_string : string -> Unix.sockaddr
