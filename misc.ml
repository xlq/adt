let unsome = function
   | Some x -> x
   | None -> raise (Failure "unsome")

let list_iteri f l =
   let rec loop i = function
      | [] -> ()
      | x::l -> f i x; loop (i+1) l
   in loop 0 l
