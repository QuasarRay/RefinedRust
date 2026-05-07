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

let use_extracted_goal name =
  run_tactic (Extract_goal_refine.use_extracted_goal name)

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

let () =
  register_extract_goal ();
  register_use_extracted_goal ()
