val opt_verbose : bool ref
val array_rev : 'a array -> 'a array
val iota_ary : int -> int -> int array
val iota_list : int -> int -> int list
val array_map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
val array_for_all : ('a -> bool) -> 'a array -> bool
val array_exists : ('a -> bool) -> 'a array -> bool
exception MonadificationError of string
val string_of_name : Names.Name.t -> string
type monadic = int * EConstr.types * EConstr.constr
val pr_monadic : Environ.env -> Evd.evar_map -> monadic -> Pp.t
val pr_monadic_env : Environ.env -> Evd.evar_map -> monadic -> Pp.t
val purelevel_of_monadic : monadic -> int
val rawtype_of_monadic : monadic -> EConstr.types
val rawterm_of_monadic : monadic -> EConstr.t
val monadic_is_function : Evd.evar_map ref -> monadic -> bool
val monadic_is_value : Evd.evar_map ref -> monadic -> bool
val numargs_of_type : Evd.evar_map -> EConstr.t -> int
val econstr_prod_appvect :
  Evd.evar_map -> EConstr.t -> EConstr.t array -> EConstr.t
val prod_appvect : Evd.evar_map -> EConstr.t -> EConstr.t array -> EConstr.t
val pr_explain_monadic : Environ.env -> Evd.evar_map -> monadic -> Pp.t
val monadic_is_pure : Evd.evar_map -> monadic -> bool
val monadic_constant_id : Names.Constant.t -> Names.Id.t
val push_rec_types :
  (EConstr.t, EConstr.t, EConstr.ERelevance.t) Constr.prec_declaration ->
  Environ.env -> Evd.evar_map -> Environ.env
val deanonymize_term :
  Environ.env -> Evd.evar_map ref -> EConstr.t -> EConstr.t
val whd_all : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val e_type_of :
  Environ.env -> Evd.evar_map ref -> EConstr.constr -> EConstr.types
val term_explicit_prod :
  Environ.env -> Evd.evar_map ref -> EConstr.t -> EConstr.t
val type_of : Environ.env -> Evd.evar_map ref -> EConstr.t -> EConstr.types
val e_new_Type : Evd.evar_map ref -> EConstr.constr
val delete_univ : Environ.env -> Evd.evar_map ref -> EConstr.t -> EConstr.t
val liftn_mterm : int -> int -> monadic -> monadic
val lift_mterm : int -> monadic -> monadic
val mona_return_notset : EConstr.constr option
val mona_return_ref : EConstr.constr option ref
val mona_return_set : Constrexpr.constr_expr -> unit
val mona_bind_notset : EConstr.constr option
val mona_bind_ref : EConstr.constr option ref
val mona_bind_set : Constrexpr.constr_expr -> unit
val mona_record_empty : (Names.GlobRef.t * (bool * monadic)) list
val mona_record_ref : (Names.GlobRef.t * (bool * monadic)) list ref
val mona_action_add : Libnames.qualid -> Constrexpr.constr_expr -> unit
val mona_type_notset : EConstr.constr option
val mona_type_ref : EConstr.constr option ref
val mona_type_set : Constrexpr.constr_expr -> unit
val mona_type0 : EConstr.t -> EConstr.t
val convert_type : Evd.evar_map -> int -> EConstr.t -> EConstr.t
val monadify_type :
  Environ.env -> Evd.evar_map -> int -> EConstr.t -> EConstr.t
val mona_return0 : EConstr.t -> EConstr.t -> EConstr.t
val mona_bind0 :
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val puredown : Environ.env -> Evd.evar_map -> int -> monadic -> EConstr.t
val puredown' : Environ.env -> Evd.evar_map -> int -> monadic -> monadic
val pureapprox : Evd.evar_map -> EConstr.t -> int
val define_constant : Names.Id.t -> EConstr.t -> Names.Constant.t
val exists_name : Names.Id.t -> bool
val find_unused_name : Names.Id.t -> Names.Id.t
val type_has_function_argument :
  Environ.env -> Evd.evar_map ref -> EConstr.t -> bool
val type_has_function_value :
  Environ.env -> Evd.evar_map ref -> EConstr.t -> bool
val higher_order_function_type_p :
  Environ.env -> Evd.evar_map ref -> EConstr.t -> bool
val mona_pure_def : Names.GlobRef.t -> monadic
val mona_pure_add_single : Libnames.qualid -> unit
val mona_pure_add : Libnames.qualid list -> unit
val beta_app : Evd.evar_map -> EConstr.t -> EConstr.t -> EConstr.t
val mona_bind2_internal :
  Environ.env ->
  Evd.evar_map ->
  Names.Name.t EConstr.binder_annot -> monadic -> monadic -> monadic
val mona_bind2 :
  Environ.env ->
  Evd.evar_map ->
  Names.Name.t EConstr.binder_annot -> monadic -> monadic -> monadic
val bind_mctx :
  Environ.env ->
  Evd.evar_map ->
  (Names.Name.t EConstr.binder_annot * monadic) list -> monadic -> monadic
val mona_construct_ref :
  Environ.env ->
  Evd.evar_map ref -> Names.constructor * EConstr.EInstance.t -> monadic
val mona_construct_ref_known :
  Names.constructor EConstr.puniverses -> bool * monadic
val pr_head :
  Environ.env ->
  Evd.evar_map ref ->
  (Names.Name.t EConstr.binder_annot * monadic) list ->
  monadic -> Pp.t list * Pp.t
val feedback_env : string -> Environ.env -> unit
val feedback_head :
  string ->
  Environ.env ->
  Evd.evar_map ref ->
  (Names.Name.t EConstr.binder_annot * monadic) list -> monadic -> unit
val make_purelevel_positive :
  (Names.Name.t EConstr.binder_annot * monadic) list * monadic ->
  (Names.Name.t EConstr.binder_annot * monadic) list * monadic
val mona_const_ref :
  Environ.env ->
  Evd.evar_map ref -> Names.Constant.t UVars.puniverses -> monadic
val mona_const_ref_known :
  Names.Constant.t EConstr.puniverses -> bool * monadic
val mona_pure_dependencies_p :
  Environ.env -> Evd.evar_map ref -> EConstr.t -> bool
val mona_head :
  Environ.env ->
  Evd.evar_map ref ->
  int list ->
  EConstr.t -> (Names.Name.t EConstr.binder_annot * monadic) list * monadic
val mona_head_internal :
  Environ.env ->
  Evd.evar_map ref ->
  int list ->
  EConstr.t -> (Names.Name.t EConstr.binder_annot * monadic) list * monadic
val mona_tail :
  Environ.env -> Evd.evar_map ref -> int list -> EConstr.t -> monadic
val mona_tail_internal :
  Environ.env -> Evd.evar_map ref -> int list -> EConstr.t -> monadic
val monadification_single : Libnames.qualid -> unit
val monadification : Libnames.qualid list -> unit
val mona_reset : unit -> unit
