open Names

type binder =
  | Assum of Id.t * EConstr.t
  | Def of Id.t * EConstr.t * EConstr.t

type extraction_record = {
  name : Id.t;
  lemma_type : EConstr.t;
  app_args : EConstr.t list;
}

let table : (Id.t, extraction_record) Hashtbl.t = Hashtbl.create 17

let store record = Hashtbl.replace table record.name record

let find name = Hashtbl.find_opt table name

let error msg = CErrors.user_err Pp.(str msg)

let reject_evars sigma term =
  if Evarutil.has_undefined_evars sigma term then
    error "Extract Goal: unresolved evars are not allowed"

let reject_decl_evars sigma decl =
  Context.Named.Declaration.iter_constr (reject_evars sigma) decl

let build_lemma_type sigma hyps concl =
  reject_evars sigma concl;
  List.iter (reject_decl_evars sigma) hyps;
  EConstr.it_mkNamedProd_or_LetIn sigma concl hyps

let app_args_of_hyps hyps =
  let one decl acc =
    match decl with
    | Context.Named.Declaration.LocalAssum (annot, _) ->
        EConstr.mkVar (Context.binder_name annot) :: acc
    | Context.Named.Declaration.LocalDef _ -> acc
  in
  List.fold_left (fun acc decl -> one decl acc) [] hyps

let print_skeleton env sigma name lemma_type =
  let pp =
    Pp.(str "Lemma " ++ Id.print name ++ str " :" ++ fnl () ++
        Printer.pr_econstr_env env sigma lemma_type ++ str "." ++ fnl () ++
        str "Proof.")
  in
  Feedback.msg_notice pp

let extract_from_goal name goal =
  let env = Proofview.Goal.env goal in
  let sigma = Proofview.Goal.sigma goal in
  let hyps = Proofview.Goal.hyps goal in
  let concl = Proofview.Goal.concl goal in
  let lemma_type = build_lemma_type sigma hyps concl in
  let app_args = app_args_of_hyps hyps in
  let record = { name; lemma_type; app_args } in
  store record;
  print_skeleton env sigma name lemma_type
