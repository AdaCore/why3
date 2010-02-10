
open Term

module M = Map.Make(String)

type env = {
  tysymbols : tysymbol M.t;
  fsymbols  : fsymbol M.t;
  psymbols  : psymbol M.t;
  tyvars    : vsymbol M.t;
  vars      : vsymbol M.t;
}

let empty = {
  tysymbols = M.empty;
  fsymbols  = M.empty;
  psymbols  = M.empty;
  tyvars    = M.empty;
  vars      = M.empty;
}

