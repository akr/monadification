(*
Copyright (C) 2016- National Institute of Advanced Industrial Science and Technology (AIST)

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*)

let () = Mltop.add_known_plugin (fun () ->
  Feedback.msg_info Pp.(str"monadification 0.1"))
  "monadification"
;;

DECLARE PLUGIN "monadification_plugin"

open Monadification

open Stdarg (* for ident(...) *)
open Ltac_plugin
open Extraargs (* for lconstr(...). lconstr accepts "PrintTerm 1 + 1" addition to "PrintTerm (1 + 1)" *)

VERNAC COMMAND EXTEND Monomorphisation CLASSIFIED AS SIDEFF
    | [ "Monadify" "Reset" ] -> [ mona_reset () ]
    | [ "Monadify" "Return" lconstr(c) ] -> [ mona_return_set c ]
    | [ "Monadify" "Bind" lconstr(c) ] -> [ mona_bind_set c ]
    | [ "Monadify" "Type" lconstr(c) ] -> [ mona_type_set c ]
    | [ "Monadify" "Action" global(libref) "=>" lconstr(c) ] -> [ mona_action_add libref c ]
    | [ "Monadify" "Pure" ne_global_list(libref_list) ] -> [ mona_pure_add libref_list ]
    | [ "Monadification" ne_global_list(libref_list) ] -> [ monadification libref_list ]
END;;
