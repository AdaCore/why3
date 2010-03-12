let print_context _ fmt _ = Format.fprintf fmt "helloworld@\n"

let transform_context () = Transform.identity

let () = 
  Driver.register_printer "helloworld" print_context;
  Driver.register_transform "helloworld" transform_context
