open Names

let error msg = CErrors.user_err Pp.(str msg)

let constant_of_id id =
  let qid = Libnames.qualid_of_ident id in
  Nametab.locate_constant qid

let use_extracted_goal name =
  match Extract_goal.find name with
  | None ->
      error "Use Extracted Goal: no metadata stored for this lemma"
  | Some record ->
      let const = constant_of_id name in
      let lemma = EConstr.UnsafeMonomorphic.mkConst const in
      let term = EConstr.applistc lemma record.Extract_goal.app_args in
      Refine.refine ~typecheck:true (fun sigma -> sigma, term)
