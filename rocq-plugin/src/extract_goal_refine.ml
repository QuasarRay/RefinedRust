open Names

let error msg = CErrors.user_err Pp.(str msg)

let constant_of_id id =
  let qid = Libnames.qualid_of_ident id in
  Nametab.locate_constant qid

let constant_of_record name record =
  match !(record.Extract_goal.saved_ref) with
  | Some (GlobRef.ConstRef const) -> const
  | Some _ -> error "Use Extracted Goal: saved reference is not a constant"
  | None -> constant_of_id name

let use_extracted_goal name =
  Proofview.Goal.enter_one ~__LOC__:"Use Extracted Goal" (fun _goal ->
      match Extract_goal.find name with
      | None ->
          error "Use Extracted Goal: no metadata stored for this lemma"
      | Some record ->
          let const = constant_of_record name record in
          let lemma = EConstr.UnsafeMonomorphic.mkConst const in
          let app_args =
            List.map EConstr.mkVar record.Extract_goal.app_arg_names
          in
          match app_args with
          | [] ->
              Tacticals.tclTHEN (Tactics.eapply lemma)
                (Tacticals.tclTRY Tactics.assumption)
          | app_args ->
              let term = EConstr.applistc lemma app_args in
              Refine.refine ~typecheck:true (fun sigma -> sigma, term))

let use_last_extracted_goal () =
  Proofview.Goal.enter_one ~__LOC__:"Use Last Extracted Goal" (fun _goal ->
      match Extract_goal.last_saved () with
      | None -> error "Use Last Extracted Goal: no extracted goal stored"
      | Some name -> use_extracted_goal name)
