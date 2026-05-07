open Names

type binder =
  | Assum of Id.t * EConstr.t
  | Def of Id.t * EConstr.t * EConstr.t

type extraction_record = {
  name : Id.t;
  lemma_type : Constr.t;
  universe_context : Univ.ContextSet.t;
  app_arg_names : Id.t list;
  saved_ref : GlobRef.t option ref;
}

let table : (Id.t, extraction_record) Hashtbl.t = Hashtbl.create 17
let extracted_stack : Id.t list ref = ref []
let saved_stack : Id.t list ref = ref []
let generated_counter = ref 0

let store record =
  Hashtbl.replace table record.name record;
  extracted_stack := record.name :: !extracted_stack

let find name = Hashtbl.find_opt table name

let next_generated_name parent_name =
  incr generated_counter;
  Id.of_string (Id.to_string parent_name ^ "_subgoal_" ^ string_of_int !generated_counter)

let mark_saved name dref =
  match find name with
  | None -> ()
  | Some record ->
      record.saved_ref := Some dref;
      saved_stack := name :: !saved_stack

let last_saved () =
  match !saved_stack with
  | [] -> None
  | name :: _ -> Some name

let last_extracted () =
  match !extracted_stack with
  | [] -> None
  | name :: _ -> Some name

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

let app_arg_names_of_hyps hyps =
  let one decl acc =
    match decl with
    | Context.Named.Declaration.LocalAssum (annot, _) ->
        Context.binder_name annot :: acc
    | Context.Named.Declaration.LocalDef _ -> acc
  in
  List.fold_left (fun acc decl -> one decl acc) [] hyps

let undeclared_universes env levels =
  match UGraph.check_declared_universes (Environ.universes env) levels with
  | Ok () -> Univ.Level.Set.empty
  | Error undeclared -> undeclared

let extract_from_goal name goal =
  let env = Proofview.Goal.env goal in
  let sigma = Proofview.Goal.sigma goal in
  let hyps = Proofview.Goal.hyps goal in
  let concl = Proofview.Goal.concl goal in
  let lemma_type = build_lemma_type sigma hyps concl in
  let closed_lemma_type = EConstr.to_constr sigma lemma_type in
  let used_universes = Vars.universes_of_constr closed_lemma_type in
  let local_universes = undeclared_universes env used_universes in
  let ustate = UState.restrict (Evd.ustate sigma) local_universes in
  let app_arg_names = app_arg_names_of_hyps hyps in
  let record =
    {
      name;
      lemma_type = closed_lemma_type;
      universe_context = UState.context_set ustate;
      app_arg_names;
      saved_ref = ref None;
    }
  in
  store record
