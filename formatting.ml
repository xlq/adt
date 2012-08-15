type formatter = {
    mutable f_bits          : string list;
    mutable f_indent        : int;
    mutable f_line_length   : int;
}

let new_formatter () =
    { f_bits = [];
      f_indent = 0;
      f_line_length = 0 }

let indent fmt =
    fmt.f_indent <- fmt.f_indent + 1

let undent fmt =
    fmt.f_indent <- fmt.f_indent - 1

(* rep lst s 3 = s::s::s::lst *)
let rec rep lst s = function
    | 0 -> lst
    | n -> rep (s::lst) s (n-1)

let puts fmt s =
    if fmt.f_line_length = 0 then begin
        fmt.f_bits <- rep fmt.f_bits "    " fmt.f_indent;
        fmt.f_line_length <- fmt.f_line_length + 4 * fmt.f_indent
    end;
    fmt.f_bits <- s :: fmt.f_bits;
    fmt.f_line_length <- fmt.f_line_length + (String.length s)

let break fmt =
    fmt.f_bits <- "\n" :: fmt.f_bits;
    fmt.f_line_length <- 0

let get_fmt_str fmt =
    String.concat "" (List.rev fmt.f_bits)

let rec fencepost f g = function
   | [] -> ()
   | [x] -> g x
   | x::l -> g x; f (); fencepost f g l
