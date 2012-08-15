let unsome = function
   | Some x -> x
   | None -> raise (Failure "unsome")
