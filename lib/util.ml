
let map_fold_left f acc l =
  let acc, rev = 
    List.fold_left 
      (fun (acc, rev) e -> let acc, e = f acc e in acc, e :: rev) 
      (acc, []) l 
  in
  acc, List.rev rev

    
