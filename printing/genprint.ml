(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Genarg

type ('raw, 'glb, 'top) printer = {
  raw : 'raw -> std_ppcmds;
  glb : 'glb -> std_ppcmds;
  top : 'top -> std_ppcmds;
}

module PrintObj =
struct
  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) printer
  let name = "printer"
  let default wit = match unquote (rawwit wit) with
  | ExtraArgType name ->
    let printer = {
      raw = (fun _ -> str "<genarg:" ++ str name ++ str ">");
      glb = (fun _ -> str "<genarg:" ++ str name ++ str ">");
      top = (fun _ -> str "<genarg:" ++ str name ++ str ">");
    } in
    Some printer
  | _ -> assert false
end

module Print = Register (PrintObj)

let register_print0 wit raw glb top =
  let printer = { raw; glb; top; } in
  Print.register0 wit printer

let raw_print wit v = (Print.obj wit).raw v
let glb_print wit v = (Print.obj wit).glb v
let top_print wit v = (Print.obj wit).top v

let generic_raw_print v = raw_unpack { raw_unpack = raw_print; } v
let generic_glb_print v = glb_unpack { glb_unpack = glb_print; } v
let generic_top_print v = top_unpack { top_unpack = top_print; } v
