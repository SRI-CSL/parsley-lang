
type parse_error =
  | Invalid_integer of string

exception Error of parse_error * Location.t

let error_string = function
  | Invalid_integer s ->
        Printf.sprintf "invalid integer: '%s'" s
