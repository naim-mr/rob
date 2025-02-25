open Frontend

(* parsing *)
let parseFile filename =
  let f = open_in filename in
  let lex = Lexing.from_channel f in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = filename };
    let r = Parser.file Lexer.start lex in
    close_in f;
    r
  with
  | Parser.Error ->
      Printf.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Intermediate.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Printf.eprintf "Parse Error (Invalid Token) near %s\n"
          (Intermediate.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parsePropertyString str =
  let lex = Lexing.from_string str in
  try PropertyParser.file PropertyLexer.start lex with
  | PropertyParser.Error ->
      Printf.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Intermediate.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Printf.eprintf "Parse Error (Invalid Token) near %s\n"
          (Intermediate.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseProperty filename =
  let f = open_in filename in
  let lex = Lexing.from_channel f in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = filename };
    let r = PropertyParser.file PropertyLexer.start lex in
    close_in f;
    r
  with
  | PropertyParser.Error ->
      Printf.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Intermediate.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Printf.eprintf "Parse Error (Invalid Token) near %s\n"
          (Intermediate.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseCTLProperty filename =
  let f = open_in filename in
  let lex = Lexing.from_channel f in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = filename };
    let res = CTLPropertyParser.prog CTLPropertyLexer.read lex in
    close_in f;
    CTLProperty.map (fun p -> fst (parsePropertyString p)) res
  with
  | CTLPropertyParser.Error ->
      Printf.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Intermediate.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Printf.eprintf "Parse Error (Invalid Token) near %s\n"
          (Intermediate.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseCTLPropertyString_plain (property : string) =
  let lex = Lexing.from_string property in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = "string" };
    CTLPropertyParser.prog CTLPropertyLexer.read lex
  with
  | CTLPropertyParser.Error ->
      Printf.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Intermediate.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Printf.eprintf "Parse Error (Invalid Token) near %s\n"
          (Intermediate.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseCTLPropertyString (property : string) =
  CTLProperty.map (fun p -> fst (parsePropertyString p))
  @@ parseCTLPropertyString_plain property

let parse_args () =
  let is_keyword = function
    | "-domain" | "-timeout" | "-joinfwd" | "-joinbwd" | "-main" | "-meetbwd"
    | "-minimal" | "-ordinals" | "-refine" | "-retrybwd" | "-tracefwd"
    | "-tracebwd" | "-cda" | "-termination" | "-guarantee" | "-recurrence"
    | "-time" | "-timefwd" | "-timebwd" | "-ctl" | "-ctl-ast" | "-ctl-cfg"
    | "-dot" | "-precondition" | "-ctl_existential_equivalence" | "-noinline"
    | "-vulnerability" | "-output_std" | "-json_output" ->
        true
    | _ -> false
  in
  let rec doit args =
    match args with
    (* General arguments -----------------------------------------------------*)
    | "-domain" :: x :: r ->
        (* abstract domain: boxes|octagons|polyhedra *)
        Config.domain := x;
        doit r
    | "-timeout" :: x :: r ->
        (* analysis timeout *)
        Config.timeout := float_of_string x;
        doit r
    | "-joinfwd" :: x :: r ->
        (* widening delay in forward analysis *)
        Config.joinfwd := int_of_string x;
        doit r
    | "-joinbwd" :: x :: r ->
        (* widening delay in backward analysis *)
        Config.joinbwd := int_of_string x;
        doit r
    | "-main" :: x :: r ->
        (* analyzer entry point *)
        Config.main := x;
        doit r
    | "-meetbwd" :: x :: r ->
        (* dual widening delay in backward analysis *)
        Config.meetbwd := int_of_string x;
        doit r
    | "-minimal" :: r ->
        (* analysis result only *)
        Config.minimal := true;
        Config.minimal := true;
        doit r
    | "-ordinals" :: x :: r ->
        (* ordinal-valued ranking functions *)
        Config.ordinals := true;
        doit r (* Ordinals.max := int_of_string x;*)
    | "-refine" :: r ->
        (* refine in backward analysis *)
        Config.refine := true;
        doit r
    | "-retrybwd" :: x :: r ->
        Config.retrybwd := int_of_string x;
        doit r
    | "-tracefwd" :: r ->
        (* forward analysis trace *)
        Config.tracefwd := true;
        doit r
    | "-tracebwd" :: r ->
        (* backward analysis trace *)
        Config.tracebwd := true;
        (* CFGInterpreter.trace := true;
           CFGInterpreter.trace_states := true; *)
        doit r
    (* Conflict driven analysis arguments -------------------------------------------------*)
    | "-cda" :: x :: r ->
        Config.cda := true;
        Config.size := int_of_string x;
        Config.refine := true;
        doit r
    (* Termination arguments -------------------------------------------------*)
    | "-termination" :: r ->
        (* guarantee analysis *)
        Config.analysis := "termination";
        doit r
    (* Recurrence / Guarantee arguments --------------------------------------*)
    | "-guarantee" :: x :: r ->
        (* guarantee analysis *)
        Config.analysis := "guarantee";
        Config.property := x;
        doit r
    | "-recurrence" :: x :: r ->
        (* recurrence analysis *)
        Config.analysis := "recurrence";
        Config.property := x;
        doit r
    | "-time" :: r ->
        (* track analysis time *)
        Config.time := true;
        doit r
    | "-timefwd" :: r ->
        (* track forward analysis time *)
        Config.timefwd := true;
        doit r
    | "-timebwd" :: r ->
        (* track backward analysis time *)
        Config.timebwd := true;
        doit r
    (* CTL arguments ---------------------------------------------------------*)
    | "-ctl" :: x :: r ->
        (* CTL analysis *)
        Config.analysis := "ctl";
        Config.property := x;
        doit r
    | "-ctl-ast" :: x :: r ->
        (* CTL analysis *)
        Config.analysis := "ctl";
        Config.ctltype := "AST";
        Config.property := x;
        doit r
    | "-ctl-cfg" :: x :: r ->
        (* CTL analysis *)
        Config.analysis := "ctl";
        Config.ctltype := "CFG";
        Config.property := x;
        doit r
    | "-dot" :: r ->
        (* print CFG and decision trees in 'dot' format *)
        Config.dot := true;
        doit r
    | "-precondition" :: c :: r ->
        (* optional precondition that holds
           at the start of the program, default = true *)
        Config.precondition := c;
        doit r
    | "-ctl_existential_equivalence" :: r ->
        (* use CTL equivalence relations to
           convert existential to universal CTL properties *)
        Config.ctl_existential_equivalence := true;
        doit r
    | "-noinline" :: r ->
        (* don't inline function calls, only for CFG based analysis *)
        Config.noinline := true;
        doit r
    | "-vulnerability" :: r ->
        Config.vulnerability := true;
        doit r
    | "-output_std" :: r ->
        Config.output_std := true;
        doit r
    | "-json_output" :: x :: r when not (is_keyword x) ->
        Config.json_output := true;
        Config.output_dir := x;
        Config.time := true
    | "-json_output" :: r ->
        (* guarantee analysis *)
        Config.json_output := true;
        Config.time := true;
        doit r
    | x :: r ->
        Config.filename := x;
        doit r
    | [] -> ()
  in
  doit (List.tl (Array.to_list Sys.argv))
