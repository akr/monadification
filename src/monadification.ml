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

open Names
open Globnames
open Pp
open CErrors
open Goptions

open Term
open Constr
open EConstr

let opt_verbose = ref false
let _ = declare_bool_option
        { optdepr  = false;
          optname  = "Monadification Verbose";
          optkey   = ["Monadification";"Verbose"];
          optread  = (fun () -> !opt_verbose);
          optwrite = (:=) opt_verbose }

let array_rev a =
  let n = Array.length a in
  Array.init n (fun i -> a.(n - i - 1))

let iota_ary m n =
  Array.init n (fun i -> m + i)

let iota_list m n =
  Array.to_list (iota_ary m n)

let array_map2 f a1 a2 =
  if Array.length a1 <> Array.length a2 then
    invalid_arg "Array.map2: arrays must have the same length";
  Array.mapi (fun i -> f a1.(i)) a2

let array_for_all f a =
  try Array.iter (fun x -> if f x then () else raise Exit) a; true
  with Exit -> false

let array_exists f a =
  try Array.iter (fun x -> if f x then raise Exit) a; false
  with Exit -> true

exception MonadificationError of string

let string_of_name name =
  match name with
  | Name.Name id -> Id.to_string id
  | Name.Anonymous -> "_"

(* should use prod_appvect.
let rec strip_outer_prods ndecls term =
  if ndecls = 0 then
    ([], term)
  else
    match Term.kind_of_term term with
    | Term.Prod (name, ty, body) ->
        let (decls, innermostbody) = strip_outer_prods (ndecls-1) body in
        ((name, ty) :: decls, innermostbody)
    | _ -> error "prod nesting is not enough"
*)

(* purelevel * rawty * term *)
type monadic = (int * EConstr.types * EConstr.constr)

let pr_monadic monadic =
  let (purelevel, ty, term) = monadic in
  hv 0 (str "monadic" ++ int purelevel ++ spc () ++ Printer.pr_econstr ty ++ spc () ++ Printer.pr_econstr term)

let pr_monadic_env env evd monadic =
  let (purelevel, ty, term) = monadic in
  hv 0 (str "monadic" ++ int purelevel ++ spc () ++ Printer.pr_econstr_env env evd ty ++ spc () ++ Printer.pr_econstr_env env evd term)

let purelevel_of_monadic m =
  let (purelevel, ty, term) = m in purelevel

let rawtype_of_monadic m =
  let (purelevel, ty, term) = m in ty

let rawterm_of_monadic m =
  let (purelevel, ty, term) = m in term

let monadic_is_function evdref m =
  EConstr.isProd !evdref (rawtype_of_monadic m)

let monadic_is_value evdref m = not (monadic_is_function evdref m)

let rec numargs_of_type sigma ty =
  match EConstr.kind sigma ty with
  | Term.Prod (name, ty', body) ->
      1 + numargs_of_type sigma body
  | _ -> 0

let econstr_prod_appvect sigma ty args =
  EConstr.of_constr (Term.prod_appvect (EConstr.to_constr sigma ty) (Array.map (EConstr.to_constr sigma) args))

let rec prod_appvect sigma ty args =
  let numargs = numargs_of_type sigma ty in
  if numargs = 0 then
    user_err (Pp.str "Not enough prod's.")
  else if Array.length args <= numargs then
    econstr_prod_appvect sigma ty args
  else
    let args1 = Array.sub args 0 numargs in
    let args2 = Array.sub args numargs (Array.length args - numargs) in
    prod_appvect sigma (econstr_prod_appvect sigma ty args1) args2

let pr_explain_monadic sigma m =
  let (purelevel, rawty, term) = m in
  let numargs = numargs_of_type sigma rawty in
  (if numargs < purelevel then
    str "is pure"
  else
    str "=>" ++ spc () ++ Printer.pr_econstr term) ++
  spc () ++ str "(purelevel=" ++ int purelevel ++ str ")"

let monadic_is_pure sigma (m : monadic) =
  let (purelevel, ty, term) = m in
  numargs_of_type sigma ty < purelevel

let monadic_constant_id cnst =
  let str = Label.to_string (Constant.label cnst) in
  Id.of_string (str ^ "M")

let push_rec_types (nameary,tyary,funary) env sigma =
  Environ.push_rec_types (nameary, Array.map (EConstr.to_constr sigma) tyary, Array.map (EConstr.to_constr sigma) funary) env

let deanonymize_term env evdref term =
  let rec r env term =
    match EConstr.kind !evdref term with
    | Term.Rel i -> term
    | Term.Var name -> term
    | Term.Meta i -> term
    | Term.Evar (ekey, termary) -> mkEvar (ekey, (Array.map (r env) termary))
    | Term.Sort s -> term
    | Term.Cast (expr, kind, ty) -> mkCast (r env expr, kind, r env ty)
    | Term.Prod (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = EConstr.push_rel decl env in
        Namegen.mkProd_name env !evdref (name, r env ty, r env2 body)
    | Term.Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = EConstr.push_rel decl env in
        Namegen.mkLambda_name env !evdref (name, r env ty, r env2 body)
    | Term.LetIn (name, expr, ty, body) ->
        let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = EConstr.push_rel decl env in
        mkLetIn (Namegen.named_hd env !evdref ty name, r env expr, r env ty, r env2 body)
    | Term.App (f, argsary) -> mkApp (r env f, Array.map (r env) argsary)
    | Term.Const (cnst, u) -> term
    | Term.Ind (ind, u) -> term
    | Term.Construct (cstr, u) -> term
    | Term.Case (ci, tyf, expr, brs) -> mkCase (ci, r env tyf, r env expr, Array.map (r env) brs)
    | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        let nameary2 = array_map2 (Namegen.named_hd env !evdref) tyary nameary in
        mkFix ((ia, i), (nameary2, Array.map (r env) tyary, Array.map (r env2) funary))
    | Term.CoFix (i, (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        let nameary2 = array_map2 (Namegen.named_hd env !evdref) tyary nameary in
        mkCoFix (i, (nameary2, Array.map (r env) tyary, Array.map (r env2) funary))
    | Term.Proj (proj, expr) ->
        mkProj (proj, r env expr)
  in
  r env term

let whd_all env sigma term =
  EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))

let term_explicit_prod env evdref term =
  let rec r env term =
    if isProd !evdref term then
      r2 env term
    else
      let termty = Typing.e_type_of env evdref term in
      if isSort !evdref termty then
        let term' = whd_all env !evdref term in
        if isProd !evdref term' then
          r2 env term'
        else
          r2 env term
      else
        r2 env term
  and r2 env term =
    match EConstr.kind !evdref term with
    | Term.Rel i -> term
    | Term.Var name -> term
    | Term.Meta i -> term
    | Term.Evar (ekey, termary) -> mkEvar (ekey, (Array.map (r env) termary))
    | Term.Sort s -> term
    | Term.Cast (expr, kind, ty) -> mkCast (r env expr, kind, r env ty)
    | Term.Prod (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = push_rel decl env in
        mkProd (name, r env ty, r env2 body)
    | Term.Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = push_rel decl env in
        mkLambda (name, r env ty, r env2 body)
    | Term.LetIn (name, expr, ty, body) ->
        let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = push_rel decl env in
        mkLetIn (name, r env expr, r env ty, r env2 body)
    | Term.App (f, argsary) -> mkApp (r env f, Array.map (r env) argsary)
    | Term.Const (cnst, u) -> term
    | Term.Ind (ind, u) -> term
    | Term.Construct (cstr, u) -> term
    | Term.Case (ci, tyf, expr, brs) -> mkCase (ci, r env tyf, r env expr, Array.map (r env) brs)
    | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        mkFix ((ia, i), (nameary, Array.map (r env) tyary, Array.map (r env2) funary))
    | Term.CoFix (i, (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        mkCoFix (i, (nameary, Array.map (r env) tyary, Array.map (r env2) funary))
    | Term.Proj (proj, expr) ->
        mkProj (proj, r env expr)
  in
  r env term

let type_of env evdref term =
  let ty = Typing.e_type_of env evdref term in
  term_explicit_prod env evdref ty

let delete_univ env evdref term =
  let rec recfun term =
    match EConstr.kind !evdref term with
    | Term.Rel i -> mkRel i
    | Term.Var name -> mkVar name
    | Term.Meta i -> mkMeta i
    | Term.Evar (ekey, termary) -> mkEvar (ekey, (Array.map recfun termary))
    | Term.Sort s ->
        (match ESorts.kind !evdref s with
        | Sorts.Prop _ -> term
        | Sorts.Type _ -> Evarutil.e_new_Type env evdref)
    | Term.Cast (expr, kind, ty) -> mkCast (recfun expr, kind, recfun ty)
    | Term.Prod (name, ty, body) -> mkProd (name, recfun ty, recfun body)
    | Term.Lambda (name, ty, body) -> mkLambda (name, recfun ty, recfun body)
    | Term.LetIn (name, expr, ty, body) -> mkLetIn (name, recfun expr, recfun ty, recfun body)
    | Term.App (f, argsary) -> mkApp (recfun f, Array.map recfun argsary)
    | Term.Const (cnst, u) -> mkConst cnst
    | Term.Ind (ind, u) -> mkInd ind
    | Term.Construct (cstr, u) -> mkConstruct cstr
    | Term.Case (ci, tyf, expr, brs) -> mkCase (ci, recfun tyf, recfun expr, Array.map recfun brs)
    | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
        mkFix ((ia, i), (nameary, Array.map recfun tyary, Array.map recfun funary))
    | Term.CoFix (i, (nameary, tyary, funary)) ->
        mkCoFix (i, (nameary, Array.map recfun tyary, Array.map recfun funary))
    | Term.Proj (proj, expr) ->
        mkProj (proj, recfun expr)
  in
  (*Feedback.msg_debug (str "delete_univ:1:" ++ Printer.pr_econstr_env env !evdref term);*)
  let newterm = recfun term in
  (*Feedback.msg_debug (str "delete_univ:2:" ++ Printer.pr_econstr_env env !evdref newterm);*)
  let _ = Typing.e_type_of env evdref newterm in
  (*Feedback.msg_debug (str "delete_univ:3:" ++ Printer.pr_econstr_env env !evdref newterm);*)
  newterm

let liftn_mterm d c mterm =
  let (purelevel, ty, term) = mterm in (purelevel, Vars.liftn d c ty, Vars.liftn d c term)

let lift_mterm d mterm =
  liftn_mterm d 1 mterm

let mona_return_notset : EConstr.constr option = None
let mona_return_ref = Summary.ref mona_return_notset ~name:"MonadificationReturn"
let mona_return_set constr =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let (term : Term.constr), _ = Constrintern.interp_constr env !evdref constr in
  let (term : EConstr.constr) = EConstr.of_constr term in
  mona_return_ref := Some term;
  Feedback.msg_info (str "monad return operation registered")

let mona_bind_notset : EConstr.constr option = None
let mona_bind_ref = Summary.ref mona_bind_notset ~name:"MonadificationBind"
let mona_bind_set constr =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let (term : Term.constr), _ = Constrintern.interp_constr env !evdref constr in
  let (term : EConstr.constr) = EConstr.of_constr term in
  mona_bind_ref := Some term;
  Feedback.msg_info (str "monad bind operation registered")

(* (orignale_name, (converted_flag, mterm)) *)
let mona_record_empty : (global_reference * (bool * monadic)) list = []
let mona_record_ref = Summary.ref mona_record_empty ~name:"MonadificationRecord"

let mona_action_add libref constr =
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let (term : Term.constr), _ = Constrintern.interp_constr env !evdref constr in
  let (term : EConstr.constr) = EConstr.of_constr term in
  let pureterm =
    match gref with
    | ConstRef cnst -> mkConst cnst
    | ConstructRef cstr -> mkConstruct cstr
    | _ -> user_err (Pp.str "unexpected gref")
  in
  let termty = type_of env evdref pureterm in
  let purelevel = numargs_of_type !evdref termty in
  let m = (purelevel, termty, term) in
  mona_record_ref := (gref, (true, m)) :: !mona_record_ref;
  Feedback.msg_info (hv 0 (str "monadic action registered for" ++ spc () ++ Printer.pr_global gref))

let mona_type_notset : EConstr.constr option = None
let mona_type_ref = Summary.ref mona_type_notset ~name:"MonadificationType"
let mona_type_set constr =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let (term : Term.constr), _ = Constrintern.interp_constr env !evdref constr in
  let (term : EConstr.constr) = EConstr.of_constr term in
  mona_type_ref := Some term;
  Feedback.msg_info (str "monad type registered")

let mona_type0 ty =
  match !mona_type_ref with
  | None -> raise (MonadificationError "Monadify Type not set")
  | Some ret -> mkApp (ret, [| ty |])

let rec convert_type sigma pure_level ty =
  if pure_level = 0 then
    match EConstr.kind sigma ty with
    | Term.Prod (argname, argty, bodyty) ->
        mona_type0 (mkProd (argname, convert_type sigma 1 argty, convert_type sigma 0 bodyty))
    | _ -> mona_type0 ty
  else
    match EConstr.kind sigma ty with
    | Term.Prod (argname, argty, bodyty) ->
        mkProd (argname, convert_type sigma 1 argty, convert_type sigma (pure_level-1) bodyty)
    | _ -> ty

let rec monadify_type sigma purelevel ty =
  (*Feedback.msg_debug (str "monadify_type:" ++ Printer.pr_econstr ty);*)
  let wrap_type ty0 =
    if purelevel = 0 then
      mona_type0 ty0
    else
      ty0
  in
  match EConstr.kind sigma ty with
  | Term.Prod (name, namety, body) ->
      if purelevel = 0 then
        mona_type0 (mkProd (name, monadify_type sigma 1 namety, monadify_type sigma 0 body))
      else
        mkProd (name, monadify_type sigma 1 namety, monadify_type sigma (purelevel - 1) body)
  | Term.Sort _ | Term.Rel _ | Term.Ind _ ->
      wrap_type ty
  | Term.App (f, args) ->
      wrap_type (match EConstr.kind sigma f with
      | Term.Ind (ind, u) ->
          mkApp (mkIndU (ind, u), Array.map (monadify_type sigma 1) args)
      | _ ->
          (Feedback.msg_warning (hv 0
            (str "monadify_type: unexpected type application:" ++ spc () ++ Printer.pr_econstr ty));
            ty))
  | _ ->
      (Feedback.msg_warning (hv 0
        (str "monadify_type: unexpected type:" ++ spc () ++ Printer.pr_econstr ty));
      wrap_type ty)

let mona_return0 ty term =
  match !mona_return_ref with
  | None -> raise (MonadificationError "Monadify Return not set")
  | Some ret -> mkApp (ret, [| ty; term |])

let mona_bind0 ty1 ty2 term1 term2 =
  match !mona_bind_ref with
  | None -> raise (MonadificationError "Monadify Bind not set")
  | Some bind -> mkApp (bind, [| ty1; ty2; term1; term2 |])

(* puredown doesn't convert types. *)
let rec puredown sigma j m =
  let (i, (rawtermty : EConstr.constr), term) = m in
  if i < j then
    user_err ~hdr:"puredown"
      (hv 0 (str "puredown: cannot up purelevel:" ++ spc () ++ pr_monadic m ++ spc () ++ hv 0 (str "to" ++ spc () ++ int j)))
  else if i = j then
    term
  else (* 0 <= j < i *)
    match EConstr.kind sigma rawtermty with
    | Term.Prod (argname', argty', bodyty) ->
        (match EConstr.kind sigma term with
        | Term.Lambda (argname, argty, body) ->
            if j = 0 then
              let body' = puredown sigma 0 (i-1, bodyty, body) in
              mona_return0 (monadify_type sigma 1 rawtermty) (mkLambda (argname, argty, body'))
            else
              let body' = puredown sigma (j-1) (i-1, bodyty, body) in
              mkLambda (argname, argty, body')
        | _ ->
            (* This eta-expansion should not delay side effect
               because 0 < i which means that e has no immediate side effect. *)
            let body' = mkApp (Vars.lift 1 term, [| mkRel 1 |]) in
            puredown sigma j (i, rawtermty, mkLambda (Name.Anonymous, argty', body')))
    | _ ->
        mona_return0 (monadify_type sigma 1 rawtermty) term

let puredown' sigma j m =
  let (i, rawtermty, term) = m in
  (j, rawtermty, puredown sigma j m)

let rec pureapprox sigma term =
  match EConstr.kind sigma term with
  | Term.Lambda (name, ty, body) ->
      1 + pureapprox sigma body
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      pureapprox sigma funary.(i)
  | _ -> 0

let define_constant id term =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  (*Feedback.msg_debug (str "define_constant:1:" ++ Id.print id);*)
  let term = delete_univ env evdref term in
  (*Feedback.msg_debug (str "define_constant:2:" ++ Id.print id);*)
  Declare.declare_definition id (EConstr.to_constr !evdref term, Evd.universe_context_set !evdref)

let rec find_unused_name id =
  if Declare.exists_name id then
    find_unused_name (Id.of_string (Id.to_string id ^ "'"))
  else
    id

let rec type_has_function_argument env evdref ty =
  match EConstr.kind !evdref ty with
  | Term.Prod (name, namety, body) ->
      let decl = Context.Rel.Declaration.LocalAssum (name, namety) in
      let env2 = push_rel decl env in
      if type_has_function_value env evdref namety then
        true
      else
        type_has_function_argument env2 evdref body
  | Term.Sort _ -> false
  | Term.Rel _ -> false
  | Term.Ind _ -> false
  | Term.App (f, args) ->
      (match EConstr.kind !evdref f with
      | Term.Ind _ -> array_exists (type_has_function_argument env evdref) args
      | _ ->
          (Feedback.msg_warning (hv 0
            (str "type_has_function_argument: unexpected type application:" ++
            spc () ++ Printer.pr_econstr_env env !evdref ty));
          false))
  | _ ->
      (Feedback.msg_warning (hv 0
        (str "type_has_function_argument: unexpected type:" ++
        spc () ++ Printer.pr_econstr_env env !evdref ty));
      false)
and type_has_function_value env evdref ty =
  match EConstr.kind !evdref ty with
  | Term.Prod _ -> true
  | Term.Sort _ -> false
  | Term.Rel _ -> false
  | Term.Ind _ -> false
  | Term.App (f, args) ->
      (match EConstr.kind !evdref f with
      | Term.Ind _ -> array_exists (type_has_function_value env evdref) args
      | _ ->
          (Feedback.msg_warning (hv 0
            (str "type_has_function_value: unexpected type application:" ++
            spc () ++ Printer.pr_econstr_env env !evdref ty));
          false))
  | _ ->
      (Feedback.msg_warning (hv 0
        (str "type_has_function_value: unexpected type:" ++
        spc () ++ Printer.pr_econstr_env env !evdref ty));
      false)

let higher_order_function_type_p env evdref ty =
  type_has_function_argument env evdref ty

let mona_pure_def gref =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let term =
    match gref with
    | ConstRef cnst -> mkConst cnst
    | ConstructRef cstr -> mkConstruct cstr
    | _ -> user_err (Pp.str "unexpected gref")
  in
  let termty = type_of env evdref term in
  (if higher_order_function_type_p env evdref termty then
    match gref with
    | ConstRef cnst -> user_err ~hdr:"mona_pure_def"
        (hv 0 (str "higer order function can not considered as pure function:" ++ spc () ++ Printer.pr_global gref))
    | ConstructRef cstr -> user_err ~hdr:"mona_pure_def"
        (hv 0 (str "constructor with higer order function is not supported:" ++ spc () ++ Printer.pr_global gref))
    | _ -> user_err (Pp.str "unexpected gref"));

  (*Feedback.msg_debug (str "mona_pure_def:termty=" ++ Printer.pr_econstr termty);*)
  let numargs = numargs_of_type !evdref termty in
  let v = (numargs+1, termty, term) in
  mona_record_ref := (gref, (false, v)) :: !mona_record_ref;
  v

let mona_pure_add_single libref =
  (let gref = Smartlocate.global_with_alias libref in
  if List.mem_assoc gref !mona_record_ref then
    (let (converted, m) = List.assoc gref !mona_record_ref in
    if converted then
      Feedback.msg_warning (hv 0 (str "converted definition already registered:" ++ spc () ++ Printer.pr_global gref))
    else
      Feedback.msg_info (hv 0 (str "already registered:" ++ spc () ++ Printer.pr_global gref)))
  else
    let _ = mona_pure_def gref in
    Feedback.msg_info (hv 0 (str "pure constant registered:" ++ spc ()  ++ Printer.pr_global gref)))

let mona_pure_add libref_list =
  List.iter mona_pure_add_single libref_list

let beta_app sigma f arg =
  EConstr.of_constr (Reduction.beta_app (EConstr.to_constr sigma f) (EConstr.to_constr sigma arg))

let mona_bind2_internal sigma name m1 m2 =
  let (purelevel1, rawty1, term1) = m1 in
  let (purelevel2, rawty2, term2) = m2 in
  let rawty = econstr_prod_appvect sigma (mkProd (name, rawty1, rawty2)) [| term1 |] in
  if isRelN sigma 1 term2 then
    m1
  else if 0 < purelevel1 then
    (purelevel2, rawty,
      if isRel sigma term1 || Termops.count_occurrences sigma (mkRel 1) term2 <= 1 then
        beta_app sigma (mkLambda (name, (monadify_type sigma 1 rawty1), term2)) (puredown sigma 1 m1)
      else
        mkLetIn (name, (puredown sigma 1 m1), (monadify_type sigma 1 rawty1), term2))
  else
    (0, rawty,
      mona_bind0 (monadify_type sigma 1 rawty1) (monadify_type sigma 1 (Vars.lift (-1) rawty2))
        term1
        (Reductionops.shrink_eta (mkLambda (name, (monadify_type sigma 1 rawty1),
          (puredown sigma 0 m2)))))

let mona_bind2 sigma name m1 m2 =
  let result = mona_bind2_internal sigma name m1 m2 in
  (*Feedback.msg_debug (str "mona_bind2_report0:" ++ spc () ++
    pr_monadic m1 ++ spc () ++ str ">>=" ++ spc () ++
    pr_monadic m2 ++ spc () ++ str "=" ++ spc () ++
    pr_monadic result);*)
  result

let bind_mctx sigma mctx mterm =
  List.fold_left (fun mterm (name, marg) -> mona_bind2 sigma name marg mterm) mterm mctx

let mona_construct_ref env evdref (cstr, u) =
  (*Feedback.msg_debug (str "mona_construct_ref:1:" ++ Printer.pr_constructor env cstr);*)
  let key = ConstructRef cstr in
  if List.mem_assoc key !mona_record_ref then
    (let (converted, m) = List.assoc key !mona_record_ref in
    Feedback.msg_info (hv 0 (str "constructor found:" ++ spc () ++ Printer.pr_constructor env cstr ++ spc () ++ pr_explain_monadic !evdref m));
    m)
  else
    ((*Feedback.msg_debug (str "mona_construct_ref:2:" ++ Printer.pr_constructor env cstr);*)
    let v = mona_pure_def (ConstructRef cstr) in
    Feedback.msg_info (hv 0 (str "monadified constructor:" ++ spc () ++ Printer.pr_constructor env cstr ++ spc () ++ str "is pure" ++
    spc () ++ str "(purelevel=" ++ int (purelevel_of_monadic v) ++ str ")" ));
    v)

let mona_construct_ref_known (cstr, u) =
  let key = ConstructRef cstr in
  List.assoc key !mona_record_ref

let pr_head env evdref mctx mterm =
  let n = List.length mctx in
  let ppcmds_mctx, env2, _ = List.fold_right
    (fun (name, mctx_elt) (prs, e, i) ->
      (*let name = Namegen.named_hd env (rawtype_of_monadic mctx_elt) Name.Anonymous in*)
      let name = if Name.is_anonymous name then Name.Name (Id.of_string ("mctx" ^ string_of_int i)) else name in
      let pr = pr_monadic_env e !evdref mctx_elt in
      let decl = Context.Rel.Declaration.LocalAssum (name, convert_type !evdref 1 (rawtype_of_monadic mctx_elt)) in
      let e2 = push_rel decl e in
      (pr::prs, e2, i - 1))
    mctx
    ([], env, n)
  in
  let ppcmds_mterm = pr_monadic_env env2 !evdref mterm in
  (ppcmds_mctx, ppcmds_mterm)

let feedback_env prefix env =
  let ctx = Environ.rel_context env in
  let num_ctx = List.length ctx in
  List.iteri
    (fun i rel ->
      Feedback.msg_debug (hv 0 (str prefix ++ str ":rel" ++ int (num_ctx - i) ++ str ":" ++ str (string_of_name (Context.Rel.Declaration.get_name rel)))))
    (List.rev ctx)

let feedback_head prefix env evdref mctx mterm =
  (*feedback_env prefix env;*)
  let ppcmds_mctx, ppcmds_mterm = pr_head env evdref mctx mterm in
  let n = List.length mctx in
  List.iteri
    (fun i ppcmds -> Feedback.msg_debug (hv 0 (str prefix ++ str ":mctx" ++ int (n - i) ++ str ":" ++ ppcmds)))
    (List.rev ppcmds_mctx);
  Feedback.msg_debug (hv 0 (str prefix ++ str ":mterm:" ++ ppcmds_mterm))

let make_purelevel_positive (mctx, mterm) =
  let (purelevel, rawty, term) = mterm in
  if purelevel = 0 then
    ((Name.Anonymous, mterm) :: mctx, (1, Vars.lift 1 rawty, mkRel 1))
  else
    (mctx, mterm)

let rec mona_const_ref env evdref (cnst, u) =
  (*Feedback.msg_debug (str "mona_const_ref:1:" ++ Printer.pr_constant env cnst);*)
  let key = ConstRef cnst in
  if List.mem_assoc key !mona_record_ref then
    (let (converted, m) = List.assoc key !mona_record_ref in
    Feedback.msg_info (hv 0 (str "constant found:" ++ spc () ++ Printer.pr_constant env cnst ++ spc () ++ pr_explain_monadic !evdref m));
    m)
  else
    (let id = monadic_constant_id cnst in
    (*Feedback.msg_debug (str "mona_const_ref:2:" ++ Id.print id);*)
    let (term0, uconstraints) =
      match Environ.constant_opt_value env (cnst, u) with
      | Some term_uc -> term_uc
      | None -> user_err ~hdr:"mona_const_ref"
          (hv 0 (str "failed to obtain constant value:" ++ spc () ++ Printer.pr_constant env cnst))
    in
    let (term0 : EConstr.constr) = EConstr.of_constr term0 in
    let term = term_explicit_prod env evdref term0 in
    let termty = type_of env evdref term in
    let higher_order_p = higher_order_function_type_p env evdref termty in
    Feedback.msg_info (hv 0 (str "monadification start:" ++ spc () ++ Printer.pr_constant env cnst ++ (if higher_order_p then spc () ++ str "(higher order function)" else mt ())));
    (if !opt_verbose then
      Feedback.msg_info (hv 2 (hv 0 (str "monadification source:" ++ spc () ++ Printer.pr_constant env cnst ++ spc () ++ str ":=") ++ spc () ++ Printer.pr_econstr_env env !evdref term0)));
    if mona_pure_dependencies_p env evdref term && not higher_order_p then
      (let v = mona_pure_def (ConstRef cnst) in
      Feedback.msg_info (hv 0 (str "monadification end:" ++ spc () ++ Printer.pr_constant env cnst ++ spc () ++ str "is pure" ++
        spc () ++ str "(purelevel=" ++ int (purelevel_of_monadic v) ++ str ")"));
      v)
    else
      let (purelevel, rawty, term) = mona_tail env evdref [] term in
      (* convert types in term? *)
      let term = deanonymize_term env evdref term in
      let id = find_unused_name id in
      (if !opt_verbose then
        Feedback.msg_info (hv 2 (hv 0 (str "monadification generated:" ++ spc () ++ Id.print id ++ spc () ++ str ":=") ++ spc () ++ Printer.pr_econstr_env env !evdref term)));
      (*Feedback.msg_debug (str "mona_const_ref:3:" ++ Id.print id);*)
      let constant = define_constant id term in
      (*Feedback.msg_debug (str "mona_const_ref:4:" ++ Id.print id);*)
      let v = mkConst constant in
      let v = (purelevel, termty, v) in
      mona_record_ref := (key, (true, v)) :: !mona_record_ref;
      Feedback.msg_info (hv 0 (str "monadification end:" ++ spc () ++ Printer.pr_constant env cnst ++ spc () ++ str "=>" ++ spc () ++ Id.print id ++
        spc () ++ str "(purelevel=" ++ int (purelevel_of_monadic v) ++ str ")"));
      v)

and mona_const_ref_known (cnst, u) =
  let key = ConstRef cnst in
  List.assoc key !mona_record_ref

and mona_pure_dependencies_p env evdref term =
  let translated = ref [] in
  let rec recfun env term =
    match EConstr.kind !evdref term with
    | Term.Rel i -> ()
    | Term.Var name -> ()
    | Term.Meta i -> ()
    | Term.Evar (ekey, termary) -> ()
    | Term.Sort s -> ()
    | Term.Cast (expr, kind, ty) -> recfun env expr
    | Term.Prod (name, ty, body) -> ()
    | Term.Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = push_rel decl env in
        recfun env2 body
    | Term.LetIn (name, expr, ty, body) ->
        (let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = push_rel decl env in
        recfun env expr;
        recfun env2 body)
    | Term.App (f, argsary) ->
        (recfun env f;
        Array.iter (recfun env) argsary)
    | Term.Const (cnst, u) ->
        translated := mona_const_ref env evdref (cnst, EInstance.kind !evdref u) :: !translated
    | Term.Ind (ind, u) -> ()
    | Term.Construct (cstr, u) ->
        translated := mona_construct_ref env evdref (cstr, u) :: !translated
    | Term.Case (ci, tyf, expr, brs) ->
        (recfun env expr;
        Array.iter (recfun env) brs)
    | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        Array.iter (recfun env2) funary
    | Term.CoFix (i, (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        Array.iter (recfun env2) funary
    | Term.Proj (proj, expr) ->
        recfun env expr
  in
  (recfun env term;
  List.for_all (monadic_is_pure !evdref) !translated)

and mona_head env evdref rel_purelevels term =
  (* Feedback.msg_debug (hv 0 (str "mona_head:start:" ++ Printer.pr_econstr_env env !evdref term)); *)
  let mctx, mterm = mona_head_internal env evdref rel_purelevels term in
  (* feedback_head "mona_head:result" env evdref mctx mterm; *)
  (mctx, mterm)
and mona_head_internal env evdref rel_purelevels term =
  (*Feedback.msg_debug (str "mona_head:1:" ++ Printer.pr_econstr_env env !evdref term);*)
  let termty = type_of env evdref term in
  (*Feedback.msg_debug (str "mona_head:2:" ++ Printer.pr_econstr_env env !evdref termty);*)
  if isSort !evdref termty then
    ([], (1, termty, monadify_type !evdref 1 term))
  else
    match EConstr.kind !evdref term with
    | Term.Rel i ->
        ([], (List.nth rel_purelevels (i-1), termty, term))
    | Term.Var _ | Term.Meta _ | Term.Evar _ | Term.Sort _ | Term.Prod _ | Term.Ind _ ->
        ([], (1, termty, term))

    | Term.Const (cnst, u) ->
        let (converted, m) = mona_const_ref_known (cnst, u) in
        make_purelevel_positive ([], m)

    | Term.Construct (cstr, u) ->
        let (converted, m) = mona_construct_ref_known (cstr, u) in
        make_purelevel_positive ([], m)

    | Term.Cast (expr, kind, castty) ->
        let mctx, m = mona_head env evdref rel_purelevels expr in
        let nb = List.length mctx in
        ((Name.Anonymous, m) :: mctx,
         (1, Vars.lift (nb+1) termty,
           mkCast (mkRel 1, kind, Vars.lift (nb+1) castty)))

    (* | Term.Proj (proj, expr) -> *)

    | Term.App (f, argary) ->
        let n = Array.length argary in
        let mctxf, mf = mona_head env evdref rel_purelevels f in
        let argary_translated = Array.map (mona_head env evdref rel_purelevels) argary in
        let nshifts = array_rev (Array.of_list (Array.fold_left
          (fun ns (arg_mctx, _) -> (List.length arg_mctx + List.hd ns) :: ns)
          [List.length mctxf]
          argary_translated))
        in
        let mctx_total = nshifts.(Array.length nshifts - 1) in
        let mf2 = lift_mterm (mctx_total - List.length mctxf) mf in
        let mctx = List.concat (List.rev (mctxf :: (Array.to_list (Array.map
          (fun i ->
            let arg_mctx, marg = argary_translated.(i) in
            let nb = List.length arg_mctx in
            let nshift = nshifts.(i) in
            List.mapi (fun j (name, m) -> (name, liftn_mterm nshift (nb - j) m)) arg_mctx)
          (iota_ary 0 n)))))
        in
        let margs = Array.map
          (fun i ->
            let arg_mctx, marg = argary_translated.(i) in
            let nb = List.length arg_mctx in
            let nshift = nshifts.(i) in
            let marg1 = liftn_mterm nshift (nb + 1) marg in
            let marg2 = lift_mterm (mctx_total - nb - nshift) marg1 in
            marg2)
          (iota_ary 0 n)
        in
        let (mf2_purelevel, mf2_rawty, mf2_term) = mf2 in
        let rawargs1, rawargs2 =
          let lifted_argary = Array.map (Vars.lift mctx_total) argary in
          if Array.length argary <= mf2_purelevel then
            (lifted_argary, [| |])
          else
            (Array.sub lifted_argary 0 mf2_purelevel,
             Array.sub lifted_argary mf2_purelevel (Array.length lifted_argary - mf2_purelevel))
        in
        let margs1, margs2 =
          if Array.length margs <= mf2_purelevel then
            (margs, [| |])
          else
            (Array.sub margs 0 mf2_purelevel, Array.sub margs mf2_purelevel (Array.length margs - mf2_purelevel))
        in
        let args1 = Array.map (puredown !evdref 1) margs1 in
        let rawty1 = prod_appvect !evdref mf2_rawty rawargs1 in
        let mterm1 = (mf2_purelevel - Array.length margs1, rawty1, mkApp (mf2_term, args1)) in
        let (mctx, mterm, rawty) =
          Array.fold_left
            (fun (mctx, mterm, rawty) i ->
              let rawarg = rawargs2.(i) in
              let lifted_rawarg = Vars.lift (i+1) rawarg in
              let marg = margs2.(i) in
              let mctx2 = (Name.Anonymous, mterm) :: mctx in
              let lifted_marg = lift_mterm (i+1) marg in
              let args2 = [| puredown !evdref 1 lifted_marg |] in
              let rawty2 = Vars.lift (i+1) (econstr_prod_appvect !evdref rawty [| lifted_rawarg |]) in
              let mterm2 = (0, rawty2, mkApp (mkRel 1, args2)) in
              (mctx2, mterm2, rawty2))
            (mctx, mterm1, rawty1)
            (iota_ary 0 (Array.length margs2))
        in
        make_purelevel_positive (mctx, mterm)

    | Term.LetIn (name, expr, exprty, body) ->
        let decl = Context.Rel.Declaration.LocalDef (name, expr, exprty) in
        let env2 = push_rel decl env in
        let mctx1, m1 = mona_head env evdref rel_purelevels expr in
        let rel_purelevels2 = purelevel_of_monadic m1 :: rel_purelevels in
        let mctx2, m2 = mona_head env2 evdref rel_purelevels2 body in
        let n1 = List.length mctx1 in
        let n2 = List.length mctx2 in
        let mctx3 = List.mapi (fun j (name2, m) -> (name2, liftn_mterm n1 (n2 - j + 1) m)) mctx2 in
        let m3 = liftn_mterm n1 (n2 + 2) m2 in
        make_purelevel_positive (List.concat [mctx3; [name, m1]; mctx1], m3)

    | Term.Case (ci, tyf, expr, brs) ->
        let (name, exprty, bodyty) = destLambda !evdref tyf in

        (*Feedback.msg_debug (str "mona_head:case:" ++ Printer.pr_econstr mtyf);*)
        let mctx_expr, mexpr = mona_head env evdref rel_purelevels expr in
        let n = List.length mctx_expr in
        (*Feedback.msg_debug (str "mona_head:case:n:" ++ int n);*)

        let translated_brs = Array.map
          (fun br ->
            let (br_mctx, br_mterm) = mona_head env evdref rel_purelevels br in
            bind_mctx !evdref br_mctx br_mterm)
          brs
        in

        let cstr_numargs = ci.Constr.ci_cstr_nargs in
        let br_purelevels =
          array_map2
            (fun numargs br_mterm ->
              (if purelevel_of_monadic br_mterm < numargs then
                (* eta-conversion instead of error? *)
                user_err (Pp.str "too small purelevel of match branch"));
              purelevel_of_monadic br_mterm - numargs)
            cstr_numargs
            translated_brs
        in
        let purelevel = Array.fold_left
          (fun n1 n2 -> if n1 < n2 then n1 else n2)
          br_purelevels.(0)
          br_purelevels
        in
        let mtyf = mkLambda (name, exprty, monadify_type !evdref purelevel bodyty) in
        let brs' =
          array_map2
            (fun numargs br_mterm ->
              puredown !evdref (numargs + purelevel) br_mterm)
            cstr_numargs
            translated_brs
        in
        make_purelevel_positive
          ((Name.Anonymous, mexpr) :: mctx_expr,
           (purelevel,
            Vars.lift (n+1) termty,
            mkCase (ci, Vars.lift (n+1) mtyf, mkRel 1, (Array.map (Vars.lift (n+1)) brs'))))

    | Term.Lambda (name, namety, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, namety) in
        let env2 = push_rel decl env in
        let rel_purelevels2 = 1 :: rel_purelevels in
        let (body_purelevel, bodyty, body') = mona_tail env2 evdref rel_purelevels2 body in
        ([],
         (body_purelevel + 1,
          termty,
          mkLambda (name, monadify_type !evdref 1 namety, body')))

    | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        let approx_purelevels = Array.map (pureapprox !evdref) funary in
        let rel_purelevels2 = List.rev_append (Array.to_list approx_purelevels) rel_purelevels in
        let mfunary = Array.map (mona_tail env2 evdref rel_purelevels2) funary in
        let tyary2 = array_map2
          (fun f_purelevel ty -> monadify_type !evdref f_purelevel ty)
          approx_purelevels
          tyary
        in
        let funary2 = Array.map2 (fun mfun i -> puredown !evdref i mfun) mfunary approx_purelevels in
        ([],
         (approx_purelevels.(i),
          termty,
          mkFix ((ia, i), (nameary, tyary2, funary2))))

    | _ -> ([], (1, termty, term))

and mona_tail env evdref rel_purelevels term =
  (*Feedback.msg_debug (hv 0 (str "mona_tail:start:" ++ Printer.pr_econstr_env env !evdref term));*)
  let result = mona_tail_internal env evdref rel_purelevels term in
  (*Feedback.msg_debug (hv 0 (str "mona_tail:result:" ++ pr_monadic_env env !evdref result));*)
  result
and mona_tail_internal env evdref rel_purelevels term =
  let mctx, mterm = mona_head env evdref rel_purelevels term in
  bind_mctx !evdref mctx mterm

let monadification_single libref =
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  match gref with
  | ConstRef cnst ->
      let _ = mona_const_ref env evdref (Univ.in_punivs cnst) in
      ()
  | ConstructRef cstr ->
      let _ = mona_construct_ref env evdref (Univ.in_punivs cstr) in
      ()
  | _ -> user_err (Pp.str "not constant or constructor")

let monadification libref_list =
  List.iter monadification_single libref_list

let mona_reset () =
  mona_return_ref := mona_return_notset;
  mona_bind_ref := mona_bind_notset;
  mona_record_ref := mona_record_empty;
  mona_type_ref := mona_type_notset
