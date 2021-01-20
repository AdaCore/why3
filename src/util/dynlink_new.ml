let loadfile name =
  try
    Dynlink.loadfile name
  with
  | Dynlink.Error (Dynlink.Library's_module_initializers_failed e) ->
      Printexc.raise_with_backtrace e (Printexc.get_raw_backtrace ())
