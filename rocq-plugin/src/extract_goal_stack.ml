open Names

let error msg = CErrors.user_err Pp.(str msg)

let save_hook name =
  Declare.Hook.make (fun { Declare.Hook.S.dref; _ } ->
      Extract_goal.mark_saved name dref)

let open_prepared_extracted_proof name =
  match Extract_goal.find name with
  | None -> error "Open Extracted Goal: no metadata stored for this lemma"
  | Some record ->
      let lemma_type = EConstr.of_constr record.Extract_goal.lemma_type in
      let cinfo = Declare.CInfo.make ~name ~typ:lemma_type () in
      let scope = Locality.Global Locality.ImportNeedQualified in
      let info = Declare.Info.make ~kind:Decls.(IsProof Lemma) ~scope ~hook:(save_hook name) () in
      let sigma =
        Evd.from_env (Global.env ())
        |> fun sigma ->
        Evd.merge_context_set Evd.univ_rigid sigma
          record.Extract_goal.universe_context
      in
      Declare.Proof.start ~info ~cinfo sigma

let open_last_prepared_extracted_proof () =
  match Extract_goal.last_extracted () with
  | None -> error "Open Extracted Goal: no extracted goal stored"
  | Some name -> open_prepared_extracted_proof name
