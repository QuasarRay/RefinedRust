open Names

let run_tactic tac =
  Vernactypes.vtmodifyproof (fun ~pstate ->
      let pstate, _solved = Declare.Proof.by tac pstate in
      pstate)

let extract_goal name =
  run_tactic
    (Proofview.Goal.enter_one ~__LOC__:"Extract Goal" (fun goal ->
         Extract_goal.extract_from_goal name goal;
         Proofview.tclUNIT ()))

let extract_goal_auto () =
  Vernactypes.vtmodifyproof (fun ~pstate ->
      let parent_name = Declare.Proof.get_name pstate in
      let name = Extract_goal.next_generated_name parent_name in
      let tactic =
        Proofview.Goal.enter_one ~__LOC__:"Extract Goal" (fun goal ->
            Extract_goal.extract_from_goal name goal;
            Proofview.tclUNIT ())
      in
      let pstate, _solved = Declare.Proof.by tactic pstate in
      pstate)

let use_extracted_goal name =
  run_tactic (Extract_goal_refine.use_extracted_goal name)

let use_last_extracted_goal () =
  run_tactic (Extract_goal_refine.use_last_extracted_goal ())

let open_extracted_goal name =
  Vernactypes.vtopenproof (fun () ->
      Extract_goal_stack.open_prepared_extracted_proof name)

let open_last_extracted_goal () =
  Vernactypes.vtopenproof (fun () ->
      Extract_goal_stack.open_last_prepared_extracted_proof ())

let ident_arg = Extend.TUentry (Genarg.get_arg_tag Stdarg.wit_ident)

let register_extract_goal () =
  Vernacextend.static_vernac_extend
    ~plugin:(Some "refinedrust_extract_goal.plugin")
    ~command:"ExtractGoal"
    ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_proofstep)
    ?entry:None
    [ Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "Extract",
              Vernacextend.TyTerminal
                ( "Goal",
                  Vernacextend.TyTerminal
                    ( "as",
                      Vernacextend.TyNonTerminal (ident_arg, Vernacextend.TyNil) ) ) ),
          (let coqpp_body name () = extract_goal name in
           fun name ?loc:_ ~atts () ->
             coqpp_body name (Attributes.unsupported_attributes atts)),
          None );
      Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "Extract",
              Vernacextend.TyTerminal ( "Goal", Vernacextend.TyNil ) ),
          (let coqpp_body () = extract_goal_auto () in
           fun ?loc:_ ~atts () ->
             coqpp_body (Attributes.unsupported_attributes atts)),
          None ) ]

let register_use_extracted_goal () =
  Vernacextend.static_vernac_extend
    ~plugin:(Some "refinedrust_extract_goal.plugin")
    ~command:"UseExtractedGoal"
    ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_proofstep)
    ?entry:None
    [ Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "Use",
              Vernacextend.TyTerminal
                ( "Extracted",
                  Vernacextend.TyTerminal
                    ( "Goal",
                      Vernacextend.TyNonTerminal (ident_arg, Vernacextend.TyNil) ) ) ),
          (let coqpp_body name () = use_extracted_goal name in
           fun name ?loc:_ ~atts () ->
             coqpp_body name (Attributes.unsupported_attributes atts)),
            None ) ]

let register_use_last_extracted_goal () =
  Vernacextend.static_vernac_extend
    ~plugin:(Some "refinedrust_extract_goal.plugin")
    ~command:"UseLastExtractedGoal"
    ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_proofstep)
    ?entry:None
    [ Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "Use",
              Vernacextend.TyTerminal
                ( "Last",
                  Vernacextend.TyTerminal
                    ( "Extracted",
                      Vernacextend.TyTerminal ( "Goal", Vernacextend.TyNil ) ) ) ),
          (let coqpp_body () = use_last_extracted_goal () in
           fun ?loc:_ ~atts () ->
             coqpp_body (Attributes.unsupported_attributes atts)),
          None ) ]

let register_open_extracted_goal () =
  Vernacextend.static_vernac_extend
    ~plugin:(Some "refinedrust_extract_goal.plugin")
    ~command:"OpenExtractedGoal"
    ~classifier:(fun ~atts:_ _ ->
      Vernacextend.VtStartProof (Vernacextend.Doesn'tGuaranteeOpacity, []))
    ?entry:None
    [ Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "Open",
              Vernacextend.TyTerminal
                ( "Extracted",
                  Vernacextend.TyTerminal
                    ( "Goal",
                      Vernacextend.TyNonTerminal (ident_arg, Vernacextend.TyNil) ) ) ),
          (let coqpp_body name () = open_extracted_goal name in
           fun name ?loc:_ ~atts () ->
             coqpp_body name (Attributes.unsupported_attributes atts)),
          Some (fun name ~atts:_ ->
            Vernacextend.VtStartProof
              (Vernacextend.Doesn'tGuaranteeOpacity, [name])) );
      Vernacextend.TyML
        ( false,
          Vernacextend.TyTerminal
            ( "Open",
              Vernacextend.TyTerminal
                ( "Extracted",
                  Vernacextend.TyTerminal ( "Goal", Vernacextend.TyNil ) ) ),
          (let coqpp_body () = open_last_extracted_goal () in
           fun ?loc:_ ~atts () ->
             coqpp_body (Attributes.unsupported_attributes atts)),
          None ) ]

let () =
  register_extract_goal ();
  register_use_extracted_goal ();
  register_use_last_extracted_goal ();
  register_open_extracted_goal ()
