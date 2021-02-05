
type parse_error =
  | Invalid_integer of string
  | Undeclared_format_param of string
  | Untyped_format_param of string

exception Error of parse_error * Location.t

let error_string = function
  | Invalid_integer s ->
        Printf.sprintf "invalid integer: '%s'" s
  | Undeclared_format_param s ->
        Printf.sprintf "undeclared format param '%s'" s
  | Untyped_format_param s ->
        Printf.sprintf "no type declared for format param '%s'" s
