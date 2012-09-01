val unsome : 'a option -> 'a

(* list_iteri f [a;b;c;...] = f 0 a; f 1 b; f 2 c; ... *)
val list_iteri : (int -> 'a -> unit) -> 'a list -> unit
