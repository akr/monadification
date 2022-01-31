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
open GlobRef
open Pp
open CErrors
open Goptions

open EConstr

let opt_verbose = ref false
let _ = declare_bool_option
        { optdepr  = false;
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
    | Constr.Prod (name, ty, body) ->
        let (decls, innermostbody) = strip_outer_prods (ndecls-1) body in
        ((name, ty) :: decls, innermostbody)
    | _ -> error "prod nesting is not enough"
*)

(* purelevel * rawty * term *)
type monadic = (int * EConstr.types * EConstr.constr)

let pr_monadic (env : Environ.env) (sigma : Evd.evar_map) (monadic : monadic) : Pp.t =
  let (purelevel, ty, term) = monadic in
  hv 0 (str "monadic" ++
        int purelevel ++ spc () ++
        Printer.pr_econstr_env env sigma ty ++ spc () ++
        Printer.pr_econstr_env env sigma term)

let pr_monadic_env (env : Environ.env) (evd : Evd.evar_map) (monadic : monadic) : Pp.t =
  let (purelevel, ty, term) = monadic in
  hv 0 (str "monadic" ++ int purelevel ++ spc () ++ Printer.pr_econstr_env env evd ty ++ spc () ++ Printer.pr_econstr_env env evd term)

let purelevel_of_monadic (m : monadic) : int =
  let (purelevel, ty, term) = m in purelevel

let rawtype_of_monadic (m : monadic) : EConstr.types =
  let (purelevel, ty, term) = m in ty

let rawterm_of_monadic (m : monadic) : EConstr.t =
  let (purelevel, ty, term) = m in term

let monadic_is_function evdref (m : monadic) : bool =
  EConstr.isProd !evdref (rawtype_of_monadic m)

let monadic_is_value evdref (m : monadic) : bool = not (monadic_is_function evdref m)

let rec numargs_of_type (sigma : Evd.evar_map) (ty : EConstr.t) : int =
  match EConstr.kind sigma ty with
  | Constr.Prod (name, ty', body) ->
      1 + numargs_of_type sigma body
  | _ -> 0

let econstr_prod_appvect (sigma : Evd.evar_map) (ty : EConstr.t) (args : EConstr.t array) : EConstr.t =
  EConstr.of_constr (Term.prod_appvect (EConstr.to_constr sigma ty) (Array.map (EConstr.to_constr sigma) args))

let rec prod_appvect (sigma : Evd.evar_map) (ty : EConstr.t) (args : EConstr.t array) : EConstr.t =
  let numargs = numargs_of_type sigma ty in
  if numargs = 0 then
    user_err (Pp.str "Not enough prod's.")
  else if Array.length args <= numargs then
    econstr_prod_appvect sigma ty args
  else
    let args1 = Array.sub args 0 numargs in
    let args2 = Array.sub args numargs (Array.length args - numargs) in
    prod_appvect sigma (econstr_prod_appvect sigma ty args1) args2

let pr_explain_monadic (env : Environ.env) (sigma : Evd.evar_map) (m : monadic) : Pp.t =
  let (purelevel, rawty, term) = m in
  let numargs = numargs_of_type sigma rawty in
  (if numargs < purelevel then
    str "is pure"
  else
    str "=>" ++ spc () ++ Printer.pr_econstr_env env sigma term) ++
  spc () ++ str "(purelevel=" ++ int purelevel ++ str ")"

let monadic_is_pure sigma (m : monadic) : bool =
  let (purelevel, ty, term) = m in
  numargs_of_type sigma ty < purelevel

let monadic_constant_id (cnst : Constant.t) : Id.t =
  let str = Label.to_string (Constant.label cnst) in
  Id.of_string (str ^ "M")

let push_rec_types ((nameary,tyary,funary) : (EConstr.t, EConstr.t) Constr.prec_declaration) (env : Environ.env) (sigma : Evd.evar_map) : Environ.env =
  Environ.push_rec_types (nameary, Array.map (EConstr.to_constr sigma) tyary, Array.map (EConstr.to_constr sigma) funary) env

let deanonymize_term (env : Environ.env) (evdref : Evd.evar_map ref) (term : EConstr.t) : EConstr.t =
  let rec r env term =
    match EConstr.kind !evdref term with
    | Constr.Rel i -> term
    | Constr.Int n -> term
    | Constr.Float n -> term
    | Constr.Var name -> term
    | Constr.Meta i -> term
    | Constr.Evar (ekey, terms) -> mkEvar (ekey, (List.map (r env) terms))
    | Constr.Sort s -> term
    | Constr.Cast (expr, kind, ty) -> mkCast (r env expr, kind, r env ty)
    | Constr.Prod (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = EConstr.push_rel decl env in
        Namegen.mkProd_name env !evdref (name, r env ty, r env2 body)
    | Constr.Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = EConstr.push_rel decl env in
        Namegen.mkLambda_name env !evdref (name, r env ty, r env2 body)
    | Constr.LetIn (name, expr, ty, body) ->
        let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = EConstr.push_rel decl env in
        mkLetIn (Context.map_annot (Namegen.named_hd env !evdref ty) name, r env expr, r env ty, r env2 body)
    | Constr.App (f, argsary) -> mkApp (r env f, Array.map (r env) argsary)
    | Constr.Const (cnst, u) -> term
    | Constr.Ind (ind, u) -> term
    | Constr.Construct (cstr, u) -> term
    | Constr.Case (ci,u,pms,p,iv,c,bl) ->
        let (ci, tyf, iv, expr, brs) = EConstr.expand_case env !evdref (ci,u,pms,p,iv,c,bl) in
        mkCase (EConstr.contract_case env !evdref (ci, r env tyf, iv, r env expr, Array.map (r env) brs))
    | Constr.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        let nameary2 = array_map2 (fun ty name -> Context.map_annot (Namegen.named_hd env !evdref ty) name) tyary nameary in
        mkFix ((ia, i), (nameary2, Array.map (r env) tyary, Array.map (r env2) funary))
    | Constr.CoFix (i, (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        let nameary2 = array_map2 (fun ty name -> Context.map_annot (Namegen.named_hd env !evdref ty) name) tyary nameary in
        mkCoFix (i, (nameary2, Array.map (r env) tyary, Array.map (r env2) funary))
    | Constr.Proj (proj, expr) ->
        mkProj (proj, r env expr)
    | Constr.Array (u,t,def,ty) -> mkArray (u, Array.map (r env) t, r env def, r env ty)
  in
  r env term

let whd_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))

let e_type_of env evdref term =
  let (sigma2, ty) = Typing.type_of env !evdref term in
  evdref := sigma2;
  ty

let term_explicit_prod (env : Environ.env) (evdref : Evd.evar_map ref) (term : EConstr.t) : EConstr.t =
  let rec r env term =
    if isProd !evdref term then
      r2 env term
    else
      let termty = e_type_of env evdref term in
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
    | Constr.Rel i -> term
    | Constr.Int n -> term
    | Constr.Float n -> term
    | Constr.Var name -> term
    | Constr.Meta i -> term
    | Constr.Evar (ekey, terms) -> mkEvar (ekey, (List.map (r env) terms))
    | Constr.Sort s -> term
    | Constr.Cast (expr, kind, ty) -> mkCast (r env expr, kind, r env ty)
    | Constr.Prod (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = push_rel decl env in
        mkProd (name, r env ty, r env2 body)
    | Constr.Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = push_rel decl env in
        mkLambda (name, r env ty, r env2 body)
    | Constr.LetIn (name, expr, ty, body) ->
        let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = push_rel decl env in
        mkLetIn (name, r env expr, r env ty, r env2 body)
    | Constr.App (f, argsary) -> mkApp (r env f, Array.map (r env) argsary)
    | Constr.Const (cnst, u) -> term
    | Constr.Ind (ind, u) -> term
    | Constr.Construct (cstr, u) -> term
    | Constr.Case (ci,u,pms,p,iv,c,bl) ->
        let (ci, tyf, iv, expr, brs) = EConstr.expand_case env !evdref (ci,u,pms,p,iv,c,bl) in
        mkCase (EConstr.contract_case env !evdref (ci, r env tyf, iv, r env expr, Array.map (r env) brs))
    | Constr.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        mkFix ((ia, i), (nameary, Array.map (r env) tyary, Array.map (r env2) funary))
    | Constr.CoFix (i, (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        mkCoFix (i, (nameary, Array.map (r env) tyary, Array.map (r env2) funary))
    | Constr.Proj (proj, expr) ->
        mkProj (proj, r env expr)
    | Constr.Array (u,t,def,ty) -> mkArray (u, Array.map (r env) t, r env def, r env ty)
  in
  r env term

let type_of (env : Environ.env) (evdref : Evd.evar_map ref) (term : EConstr.t) : EConstr.types =
  let ty = e_type_of env evdref term in
  term_explicit_prod env evdref ty

let e_new_Type evdref =
  let (sigma2, term) = Evarutil.new_Type !evdref in
  evdref := sigma2;
  term

let delete_univ (env : Environ.env) (evdref : Evd.evar_map ref) (term : EConstr.t) : EConstr.t =
  let rec recfun term =
    match EConstr.kind !evdref term with
    | Constr.Rel i -> mkRel i
    | Constr.Int n -> mkInt n
    | Constr.Float n -> mkFloat n
    | Constr.Var name -> mkVar name
    | Constr.Meta i -> mkMeta i
    | Constr.Evar (ekey, terms) -> mkEvar (ekey, (List.map recfun terms))
    | Constr.Sort s ->
        (match ESorts.kind !evdref s with
        | Sorts.Prop | Sorts.SProp | Sorts.Set -> term
        | Sorts.Type _ -> e_new_Type evdref)
    | Constr.Cast (expr, kind, ty) -> mkCast (recfun expr, kind, recfun ty)
    | Constr.Prod (name, ty, body) -> mkProd (name, recfun ty, recfun body)
    | Constr.Lambda (name, ty, body) -> mkLambda (name, recfun ty, recfun body)
    | Constr.LetIn (name, expr, ty, body) -> mkLetIn (name, recfun expr, recfun ty, recfun body)
    | Constr.App (f, argsary) -> mkApp (recfun f, Array.map recfun argsary)
    | Constr.Const (cnst, u) -> mkConst cnst
    | Constr.Ind (ind, u) -> mkInd ind
    | Constr.Construct (cstr, u) -> mkConstruct cstr
    | Constr.Case (ci,u,pms,p,iv,c,bl) ->
        let (ci, tyf, iv, expr, brs) = EConstr.expand_case env !evdref (ci,u,pms,p,iv,c,bl) in
        mkCase (EConstr.contract_case env !evdref (ci, recfun tyf, iv, recfun expr, Array.map recfun brs))
    | Constr.Fix ((ia, i), (nameary, tyary, funary)) ->
        mkFix ((ia, i), (nameary, Array.map recfun tyary, Array.map recfun funary))
    | Constr.CoFix (i, (nameary, tyary, funary)) ->
        mkCoFix (i, (nameary, Array.map recfun tyary, Array.map recfun funary))
    | Constr.Proj (proj, expr) ->
        mkProj (proj, recfun expr)
    | Constr.Array (u,t,def,ty) -> mkArray (EInstance.empty, Array.map recfun t, recfun def, recfun ty)
  in
  (*Feedback.msg_debug (str "delete_univ:1:" ++ Printer.pr_econstr_env env !evdref term);*)
  let newterm = recfun term in
  (*Feedback.msg_debug (str "delete_univ:2:" ++ Printer.pr_econstr_env env !evdref newterm);*)
  let _ = e_type_of env evdref newterm in
  (*Feedback.msg_debug (str "delete_univ:3:" ++ Printer.pr_econstr_env env !evdref newterm);*)
  newterm

let liftn_mterm (d : int) (c : int) (mterm : monadic) : monadic =
  let (purelevel, ty, term) = mterm in (purelevel, Vars.liftn d c ty, Vars.liftn d c term)

let lift_mterm (d : int) (mterm : monadic) : monadic =
  liftn_mterm d 1 mterm

let mona_return_notset : EConstr.constr option = None
let mona_return_ref = Summary.ref mona_return_notset ~name:"MonadificationReturn"
let mona_return_set (constr : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let (term : EConstr.constr), _ = Constrintern.interp_constr env !evdref constr in
  mona_return_ref := Some term;
  Feedback.msg_info (str "monad return operation registered")

let mona_bind_notset : EConstr.constr option = None
let mona_bind_ref = Summary.ref mona_bind_notset ~name:"MonadificationBind"
let mona_bind_set (constr : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let (term : EConstr.constr), _ = Constrintern.interp_constr env !evdref constr in
  mona_bind_ref := Some term;
  Feedback.msg_info (str "monad bind operation registered")

(* (orignale_name, (converted_flag, mterm)) *)
let mona_record_empty : (GlobRef.t * (bool * monadic)) list = []
let mona_record_ref = Summary.ref mona_record_empty ~name:"MonadificationRecord"

let mona_action_add (libref : Libnames.qualid) (constr : Constrexpr.constr_expr) : unit =
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let (term : EConstr.constr), _ = Constrintern.interp_constr env !evdref constr in
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
let mona_type_set (constr : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let (term : EConstr.constr), _ = Constrintern.interp_constr env !evdref constr in
  mona_type_ref := Some term;
  Feedback.msg_info (str "monad type registered")

let mona_type0 (ty : EConstr.t) : EConstr.t =
  match !mona_type_ref with
  | None -> raise (MonadificationError "Monadify Type not set")
  | Some ret -> mkApp (ret, [| ty |])

let rec convert_type (sigma : Evd.evar_map) (pure_level : int) (ty : EConstr.t) : EConstr.t =
  if pure_level = 0 then
    match EConstr.kind sigma ty with
    | Constr.Prod (argname, argty, bodyty) ->
        mona_type0 (mkProd (argname, convert_type sigma 1 argty, convert_type sigma 0 bodyty))
    | _ -> mona_type0 ty
  else
    match EConstr.kind sigma ty with
    | Constr.Prod (argname, argty, bodyty) ->
        mkProd (argname, convert_type sigma 1 argty, convert_type sigma (pure_level-1) bodyty)
    | _ -> ty

let rec monadify_type (env : Environ.env) (sigma : Evd.evar_map) (purelevel : int) (ty : EConstr.t) : EConstr.t =
  (*Feedback.msg_debug (str "monadify_type:" ++ Printer.pr_econstr_env env sigma ty);*)
  let wrap_type ty0 =
    if purelevel = 0 then
      mona_type0 ty0
    else
      ty0
  in
  match EConstr.kind sigma ty with
  | Constr.Prod (name, namety, body) ->
      if purelevel = 0 then
        mona_type0 (mkProd (name, monadify_type env sigma 1 namety, monadify_type env sigma 0 body))
      else
        mkProd (name, monadify_type env sigma 1 namety, monadify_type env sigma (purelevel - 1) body)
  | Constr.Sort _ | Constr.Rel _ | Constr.Ind _ ->
      wrap_type ty
  | Constr.App (f, args) ->
      wrap_type (match EConstr.kind sigma f with
      | Constr.Ind (ind, u) ->
          mkApp (mkIndU (ind, u), Array.map (monadify_type env sigma 1) args)
      | _ ->
          (Feedback.msg_warning (hv 0
            (str "monadify_type: unexpected type application:" ++ spc () ++
              Printer.pr_econstr_env env sigma ty));
            ty))
  | _ ->
      (Feedback.msg_warning (hv 0
        (str "monadify_type: unexpected type:" ++ spc () ++
          Printer.pr_econstr_env env sigma ty));
      wrap_type ty)

let mona_return0 (ty : EConstr.t) (term : EConstr.t) : EConstr.t =
  match !mona_return_ref with
  | None -> raise (MonadificationError "Monadify Return not set")
  | Some ret -> mkApp (ret, [| ty; term |])

let mona_bind0 (ty1 : EConstr.t) (ty2 : EConstr.t) (term1 : EConstr.t) (term2 : EConstr.t) : EConstr.t =
  match !mona_bind_ref with
  | None -> raise (MonadificationError "Monadify Bind not set")
  | Some bind -> mkApp (bind, [| ty1; ty2; term1; term2 |])

(* puredown doesn't convert types. *)
let rec puredown (env : Environ.env) (sigma : Evd.evar_map) (j : int) (m : monadic) : EConstr.t =
  let (i, (rawtermty : EConstr.constr), term) = m in
  if i < j then
    user_err
      (hv 0 (str "puredown: cannot up purelevel:" ++ spc () ++ pr_monadic env sigma m ++ spc () ++ hv 0 (str "to" ++ spc () ++ int j)))
  else if i = j then
    term
  else (* 0 <= j < i *)
    match EConstr.kind sigma rawtermty with
    | Constr.Prod (argname', argty', bodyty) ->
        (match EConstr.kind sigma term with
        | Constr.Lambda (argname, argty, body) ->
            if j = 0 then
              let body' = puredown env sigma 0 (i-1, bodyty, body) in
              mona_return0 (monadify_type env sigma 1 rawtermty) (mkLambda (argname, argty, body'))
            else
              let body' = puredown env sigma (j-1) (i-1, bodyty, body) in
              mkLambda (argname, argty, body')
        | _ ->
            (* This eta-expansion should not delay side effect
               because 0 < i which means that e has no immediate side effect. *)
            let body' = mkApp (Vars.lift 1 term, [| mkRel 1 |]) in
            puredown env sigma j (i, rawtermty, mkLambda (Context.anonR, argty', body')))
    | _ ->
        mona_return0 (monadify_type env sigma 1 rawtermty) term

let puredown' (env : Environ.env) (sigma : Evd.evar_map) (j : int) (m : monadic) : monadic =
  let (i, rawtermty, term) = m in
  (j, rawtermty, puredown env sigma j m)

let rec pureapprox (sigma : Evd.evar_map) (term : EConstr.t) : int =
  match EConstr.kind sigma term with
  | Constr.Lambda (name, ty, body) ->
      1 + pureapprox sigma body
  | Constr.Fix ((ia, i), (nameary, tyary, funary)) ->
      pureapprox sigma funary.(i)
  | _ -> 0

let define_constant (id : Id.t) (term : EConstr.t) : Constant.t =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  (*Feedback.msg_debug (str "define_constant:1:" ++ Id.print id);*)
  let term = delete_univ env evdref term in
  (*Feedback.msg_debug (str "define_constant:2:" ++ Id.print id);*)
  let univs = Evd.univ_entry ~poly:false !evdref in
  let defent = Declare.DefinitionEntry (Declare.definition_entry ~univs:univs (EConstr.to_constr !evdref term)) in
  let kind = Decls.IsDefinition Decls.Definition in
  let declared_ctnt = Declare.declare_constant ~name:id ~kind:kind defent in
  declared_ctnt

let exists_name id =
  try
    Declare.check_exists id;
    false
  with DeclareUniv.AlreadyDeclared _ -> true

let rec find_unused_name (id : Id.t) : Id.t =
  (*Feedback.msg_debug (Pp.str "find_unused_name: " ++ Id.print id);*)
  if exists_name id then
    find_unused_name (Id.of_string (Id.to_string id ^ "'"))
  else
    id

let rec type_has_function_argument (env : Environ.env) (evdref : Evd.evar_map ref) (ty : EConstr.t) : bool =
  (*Feedback.msg_debug (Pp.str "type_has_function_argument");*)
  match EConstr.kind !evdref ty with
  | Constr.Prod (name, namety, body) ->
      let decl = Context.Rel.Declaration.LocalAssum (name, namety) in
      let env2 = push_rel decl env in
      if type_has_function_value env evdref namety then
        true
      else
        type_has_function_argument env2 evdref body
  | Constr.Sort _ -> false
  | Constr.Rel _ -> false
  | Constr.Ind _ -> false
  | Constr.App (f, args) ->
      (match EConstr.kind !evdref f with
      | Constr.Ind _ -> array_exists (type_has_function_argument env evdref) args
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
and type_has_function_value (env : Environ.env) (evdref : Evd.evar_map ref) (ty : EConstr.t) : bool =
  match EConstr.kind !evdref ty with
  | Constr.Prod _ -> true
  | Constr.Sort _ -> false
  | Constr.Rel _ -> false
  | Constr.Ind _ -> false
  | Constr.App (f, args) ->
      (match EConstr.kind !evdref f with
      | Constr.Ind _ -> array_exists (type_has_function_value env evdref) args
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

let higher_order_function_type_p (env : Environ.env) (evdref : Evd.evar_map ref) (ty : EConstr.t) : bool =
  type_has_function_argument env evdref ty

let mona_pure_def (gref : GlobRef.t) : monadic =
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
    | ConstRef cnst -> user_err
        (hv 0 (str "higer order function can not considered as pure function:" ++ spc () ++ Printer.pr_global gref))
    | ConstructRef cstr -> user_err
        (hv 0 (str "constructor with higer order function is not supported:" ++ spc () ++ Printer.pr_global gref))
    | _ -> user_err (Pp.str "unexpected gref"));

  (*Feedback.msg_debug (str "mona_pure_def:termty=" ++ Printer.pr_econstr termty);*)
  let numargs = numargs_of_type !evdref termty in
  let v = (numargs+1, termty, term) in
  mona_record_ref := (gref, (false, v)) :: !mona_record_ref;
  v

let mona_pure_add_single (libref : Libnames.qualid) : unit =
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

let mona_pure_add (libref_list : Libnames.qualid list) : unit =
  List.iter mona_pure_add_single libref_list

let beta_app (sigma : Evd.evar_map) (f : EConstr.t) (arg : EConstr.t) : EConstr.t =
  EConstr.of_constr (Reduction.beta_app (EConstr.to_constr sigma f) (EConstr.to_constr sigma arg))

let mona_bind2_internal (env : Environ.env) (sigma : Evd.evar_map) (name : Name.t Context.binder_annot) (m1 : monadic) (m2 : monadic) : monadic =
  let (purelevel1, rawty1, term1) = m1 in
  let (purelevel2, rawty2, term2) = m2 in
  let rawty = econstr_prod_appvect sigma (mkProd (name, rawty1, rawty2)) [| term1 |] in
  if isRelN sigma 1 term2 then
    m1
  else if 0 < purelevel1 then
    (purelevel2, rawty,
      if isRel sigma term1 || Termops.count_occurrences sigma (mkRel 1) term2 <= 1 then
        beta_app sigma (mkLambda (name, (monadify_type env sigma 1 rawty1), term2)) (puredown env sigma 1 m1)
      else
        mkLetIn (name, (puredown env sigma 1 m1), (monadify_type env sigma 1 rawty1), term2))
  else
    (0, rawty,
      mona_bind0 (monadify_type env sigma 1 rawty1) (monadify_type env sigma 1 (Vars.lift (-1) rawty2))
        term1
        (Reductionops.shrink_eta sigma (mkLambda (name, (monadify_type env sigma 1 rawty1),
          (puredown env sigma 0 m2)))))

let mona_bind2 (env : Environ.env) (sigma : Evd.evar_map) (name : Name.t Context.binder_annot) (m1 : monadic) (m2 : monadic) : monadic =
  let result = mona_bind2_internal env sigma name m1 m2 in
  (*Feedback.msg_debug (str "mona_bind2_report0:" ++ spc () ++
    pr_monadic env sigma m1 ++ spc () ++ str ">>=" ++ spc () ++
    pr_monadic env sigma m2 ++ spc () ++ str "=" ++ spc () ++
    pr_monadic env sigma result);*)
  result

let bind_mctx (env : Environ.env) (sigma : Evd.evar_map) (mctx : (Name.t Context.binder_annot * monadic) list) (mterm : monadic) : monadic =
  List.fold_left (fun mterm (name, marg) -> mona_bind2 env sigma name marg mterm) mterm mctx

let mona_construct_ref (env : Environ.env) (evdref : Evd.evar_map ref) ((cstr, u) : Names.constructor * EInstance.t) =
  (*Feedback.msg_debug (str "mona_construct_ref:1:" ++ Printer.pr_constructor env cstr);*)
  let key = ConstructRef cstr in
  if List.mem_assoc key !mona_record_ref then
    (let (converted, m) = List.assoc key !mona_record_ref in
    Feedback.msg_info (hv 0 (str "constructor found:" ++ spc () ++ Printer.pr_constructor env cstr ++ spc () ++ pr_explain_monadic env !evdref m));
    m)
  else
    ((*Feedback.msg_debug (str "mona_construct_ref:2:" ++ Printer.pr_constructor env cstr);*)
    let v = mona_pure_def (ConstructRef cstr) in
    Feedback.msg_info (hv 0 (str "monadified constructor:" ++ spc () ++ Printer.pr_constructor env cstr ++ spc () ++ str "is pure" ++
    spc () ++ str "(purelevel=" ++ int (purelevel_of_monadic v) ++ str ")" ));
    v)

let mona_construct_ref_known ((cstr, u) : Names.constructor EConstr.puniverses) : bool * monadic =
  let key = ConstructRef cstr in
  List.assoc key !mona_record_ref

let pr_head (env : Environ.env) (evdref : Evd.evar_map ref) (mctx : (Name.t Context.binder_annot * monadic) list) (mterm : monadic) : Pp.t list * Pp.t =
  let n = List.length mctx in
  let ppcmds_mctx, env2, _ = List.fold_right
    (fun (name, mctx_elt) (prs, e, i) ->
      (*let name = Namegen.named_hd env (rawtype_of_monadic mctx_elt) Name.Anonymous in*)
      let name = Context.map_annot (fun name -> if Name.is_anonymous name then Name.Name (Id.of_string ("mctx" ^ string_of_int i)) else name) name in
      let pr = pr_monadic_env e !evdref mctx_elt in
      let decl = Context.Rel.Declaration.LocalAssum (name, convert_type !evdref 1 (rawtype_of_monadic mctx_elt)) in
      let e2 = push_rel decl e in
      (pr::prs, e2, i - 1))
    mctx
    ([], env, n)
  in
  let ppcmds_mterm = pr_monadic_env env2 !evdref mterm in
  (ppcmds_mctx, ppcmds_mterm)

let feedback_env (prefix : string) (env : Environ.env) : unit =
  let ctx = Environ.rel_context env in
  let num_ctx = List.length ctx in
  List.iteri
    (fun i rel ->
      Feedback.msg_debug (hv 0 (str prefix ++ str ":rel" ++ int (num_ctx - i) ++ str ":" ++ str (string_of_name (Context.Rel.Declaration.get_name rel)))))
    (List.rev ctx)

let feedback_head (prefix : string) (env : Environ.env) (evdref : Evd.evar_map ref) (mctx : (Name.t Context.binder_annot * monadic) list) (mterm : monadic) : unit =
  (*feedback_env prefix env;*)
  let ppcmds_mctx, ppcmds_mterm = pr_head env evdref mctx mterm in
  let n = List.length mctx in
  List.iteri
    (fun i ppcmds -> Feedback.msg_debug (hv 0 (str prefix ++ str ":mctx" ++ int (n - i) ++ str ":" ++ ppcmds)))
    (List.rev ppcmds_mctx);
  Feedback.msg_debug (hv 0 (str prefix ++ str ":mterm:" ++ ppcmds_mterm))

let make_purelevel_positive ((mctx, mterm) : (Name.t Context.binder_annot * monadic) list * monadic) : (Name.t Context.binder_annot * monadic) list * monadic  =
  let (purelevel, rawty, term) = mterm in
  if purelevel = 0 then
    ((Context.anonR, mterm) :: mctx, (1, Vars.lift 1 rawty, mkRel 1))
  else
    (mctx, mterm)

let rec mona_const_ref (env : Environ.env) (evdref : Evd.evar_map ref) ((cnst, u) : Names.Constant.t Univ.puniverses) : monadic =
  (*Feedback.msg_debug (str "mona_const_ref:1:" ++ Printer.pr_constant env cnst);*)
  let key = ConstRef cnst in
  if List.mem_assoc key !mona_record_ref then
    (let (converted, m) = List.assoc key !mona_record_ref in
    Feedback.msg_info (hv 0 (str "constant found:" ++ spc () ++ Printer.pr_constant env cnst ++ spc () ++ pr_explain_monadic env !evdref m));
    m)
  else
    (let id = monadic_constant_id cnst in
    (*Feedback.msg_debug (str "mona_const_ref:2:" ++ Id.print id);*)
    let term0 =
      match Environ.constant_opt_value_in env (cnst, u) with
      | Some term-> term
      | None -> user_err
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

and mona_const_ref_known ((cnst, u) : Names.Constant.t EConstr.puniverses) : bool * monadic =
  let key = ConstRef cnst in
  List.assoc key !mona_record_ref

and mona_pure_dependencies_p (env : Environ.env) (evdref : Evd.evar_map ref) (term : EConstr.t) : bool =
  let translated = ref [] in
  let rec recfun env term =
    match EConstr.kind !evdref term with
    | Constr.Rel i -> ()
    | Constr.Int n -> ()
    | Constr.Float n -> ()
    | Constr.Var name -> ()
    | Constr.Meta i -> ()
    | Constr.Evar (ekey, termary) -> ()
    | Constr.Sort s -> ()
    | Constr.Cast (expr, kind, ty) -> recfun env expr
    | Constr.Prod (name, ty, body) -> ()
    | Constr.Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = push_rel decl env in
        recfun env2 body
    | Constr.LetIn (name, expr, ty, body) ->
        (let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = push_rel decl env in
        recfun env expr;
        recfun env2 body)
    | Constr.App (f, argsary) ->
        (recfun env f;
        Array.iter (recfun env) argsary)
    | Constr.Const (cnst, u) ->
        translated := mona_const_ref env evdref (cnst, EInstance.kind !evdref u) :: !translated
    | Constr.Ind (ind, u) -> ()
    | Constr.Construct (cstr, u) ->
        translated := mona_construct_ref env evdref (cstr, u) :: !translated
    | Constr.Case (ci,u,pms,p,iv,c,bl) ->
        let (ci, tyf, iv, expr, brs) = EConstr.expand_case env !evdref (ci,u,pms,p,iv,c,bl) in
        (recfun env expr;
        Array.iter (recfun env) brs)
    | Constr.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        Array.iter (recfun env2) funary
    | Constr.CoFix (i, (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        Array.iter (recfun env2) funary
    | Constr.Proj (proj, expr) ->
        recfun env expr
    | Constr.Array (u,t,def,ty) ->
        (Array.iter (recfun env) t;
        recfun env def)
  in
  (recfun env term;
  List.for_all (monadic_is_pure !evdref) !translated)

and mona_head (env : Environ.env) (evdref : Evd.evar_map ref) (rel_purelevels : int list) (term : EConstr.t) : (Name.t Context.binder_annot * monadic) list * monadic =
  (* Feedback.msg_debug (hv 0 (str "mona_head:start:" ++ Printer.pr_econstr_env env !evdref term)); *)
  let mctx, mterm = mona_head_internal env evdref rel_purelevels term in
  (* feedback_head "mona_head:result" env evdref mctx mterm; *)
  (mctx, mterm)
and mona_head_internal (env : Environ.env) (evdref : Evd.evar_map ref) (rel_purelevels : int list) (term : EConstr.t) : (Name.t Context.binder_annot * monadic) list * monadic =
  (*Feedback.msg_debug (str "mona_head:1:" ++ Printer.pr_econstr_env env !evdref term);*)
  let termty = type_of env evdref term in
  (*Feedback.msg_debug (str "mona_head:2:" ++ Printer.pr_econstr_env env !evdref termty);*)
  if isSort !evdref termty then
    ([], (1, termty, monadify_type env !evdref 1 term))
  else
    match EConstr.kind !evdref term with
    | Constr.Rel i ->
        ([], (List.nth rel_purelevels (i-1), termty, term))
    | Constr.Var _ | Constr.Meta _ | Constr.Evar _ | Constr.Sort _ | Constr.Prod _ | Constr.Ind _ ->
        ([], (1, termty, term))

    | Constr.Const (cnst, u) ->
        let (converted, m) = mona_const_ref_known (cnst, u) in
        make_purelevel_positive ([], m)

    | Constr.Construct (cstr, u) ->
        let (converted, m) = mona_construct_ref_known (cstr, u) in
        make_purelevel_positive ([], m)

    | Constr.Cast (expr, kind, castty) ->
        let mctx, m = mona_head env evdref rel_purelevels expr in
        let nb = List.length mctx in
        ((Context.anonR, m) :: mctx,
         (1, Vars.lift (nb+1) termty,
           mkCast (mkRel 1, kind, Vars.lift (nb+1) castty)))

    (* | Constr.Proj (proj, expr) -> *)

    | Constr.App (f, argary) ->
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
        let args1 = Array.map (puredown env !evdref 1) margs1 in
        let rawty1 = prod_appvect !evdref mf2_rawty rawargs1 in
        let mterm1 = (mf2_purelevel - Array.length margs1, rawty1, mkApp (mf2_term, args1)) in
        let (mctx, mterm, rawty) =
          Array.fold_left
            (fun (mctx, mterm, rawty) i ->
              let rawarg = rawargs2.(i) in
              let lifted_rawarg = Vars.lift (i+1) rawarg in
              let marg = margs2.(i) in
              let mctx2 = (Context.anonR, mterm) :: mctx in
              let lifted_marg = lift_mterm (i+1) marg in
              let args2 = [| puredown env !evdref 1 lifted_marg |] in
              let rawty2 = Vars.lift (i+1) (econstr_prod_appvect !evdref rawty [| lifted_rawarg |]) in
              let mterm2 = (0, rawty2, mkApp (mkRel 1, args2)) in
              (mctx2, mterm2, rawty2))
            (mctx, mterm1, rawty1)
            (iota_ary 0 (Array.length margs2))
        in
        make_purelevel_positive (mctx, mterm)

    | Constr.LetIn (name, expr, exprty, body) ->
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

    | Constr.Case (ci,u,pms,p,iv,c,bl) ->
        let (ci, tyf, iv, expr, brs) = EConstr.expand_case env !evdref (ci,u,pms,p,iv,c,bl) in
        let (name, exprty, bodyty) = destLambda !evdref tyf in

        (*Feedback.msg_debug (str "mona_head:case:" ++ Printer.pr_econstr mtyf);*)
        let mctx_expr, mexpr = mona_head env evdref rel_purelevels expr in
        let n = List.length mctx_expr in
        (*Feedback.msg_debug (str "mona_head:case:n:" ++ int n);*)

        let translated_brs = Array.map
          (fun br ->
            let (br_mctx, br_mterm) = mona_head env evdref rel_purelevels br in
            bind_mctx env !evdref br_mctx br_mterm)
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
        let mtyf = mkLambda (name, exprty, monadify_type env !evdref purelevel bodyty) in
        let brs' =
          array_map2
            (fun numargs br_mterm ->
              puredown env !evdref (numargs + purelevel) br_mterm)
            cstr_numargs
            translated_brs
        in
        make_purelevel_positive
          ((Context.anonR, mexpr) :: mctx_expr,
           (purelevel,
            Vars.lift (n+1) termty,
            mkCase (EConstr.contract_case env !evdref (ci, Vars.lift (n+1) mtyf, iv, mkRel 1, (Array.map (Vars.lift (n+1)) brs')))))

    | Constr.Lambda (name, namety, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, namety) in
        let env2 = push_rel decl env in
        let rel_purelevels2 = 1 :: rel_purelevels in
        let (body_purelevel, bodyty, body') = mona_tail env2 evdref rel_purelevels2 body in
        ([],
         (body_purelevel + 1,
          termty,
          mkLambda (name, monadify_type env !evdref 1 namety, body')))

    | Constr.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = push_rec_types (nameary, tyary, funary) env !evdref in
        let approx_purelevels = Array.map (pureapprox !evdref) funary in
        let rel_purelevels2 = List.rev_append (Array.to_list approx_purelevels) rel_purelevels in
        let mfunary = Array.map (mona_tail env2 evdref rel_purelevels2) funary in
        let tyary2 = array_map2
          (fun f_purelevel ty -> monadify_type env !evdref f_purelevel ty)
          approx_purelevels
          tyary
        in
        let funary2 = Array.map2 (fun mfun i -> puredown env !evdref i mfun) mfunary approx_purelevels in
        ([],
         (approx_purelevels.(i),
          termty,
          mkFix ((ia, i), (nameary, tyary2, funary2))))

    | _ -> ([], (1, termty, term))

and mona_tail (env : Environ.env) (evdref : Evd.evar_map ref) (rel_purelevels : int list) (term : EConstr.t) : monadic =
  (*Feedback.msg_debug (hv 0 (str "mona_tail:start:" ++ Printer.pr_econstr_env env !evdref term));*)
  let result = mona_tail_internal env evdref rel_purelevels term in
  (*Feedback.msg_debug (hv 0 (str "mona_tail:result:" ++ pr_monadic_env env !evdref result));*)
  result
and mona_tail_internal (env : Environ.env) (evdref : Evd.evar_map ref) (rel_purelevels : int list) (term : EConstr.t) : monadic =
  let mctx, mterm = mona_head env evdref rel_purelevels term in
  bind_mctx env !evdref mctx mterm

let monadification_single (libref : Libnames.qualid) : unit =
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  match gref with
  | ConstRef cnst ->
      let _ = mona_const_ref env evdref (Univ.in_punivs cnst) in
      ()
  | ConstructRef cstr ->
      let _ = mona_construct_ref env evdref (cstr, EInstance.empty) in
      ()
  | _ -> user_err (Pp.str "not constant or constructor")

let monadification (libref_list : Libnames.qualid list) : unit =
  List.iter monadification_single libref_list

let mona_reset () : unit =
  mona_return_ref := mona_return_notset;
  mona_bind_ref := mona_bind_notset;
  mona_record_ref := mona_record_empty;
  mona_type_ref := mona_type_notset
