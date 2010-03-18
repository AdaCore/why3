let print_context _ fmt _ = Format.fprintf fmt "helloworld@\n"

let transform_context = Register.identity_trans

let () = 
  Driver.register_printer "helloworld" print_context;
  Driver.register_transform "helloworld" transform_context
