(***************************************************)
(*                                                 *)
(*                        Main                     *)
(*                                                 *)
(*                  Caterina Urban                 *)
(*     École Normale Supérieure, Paris, France     *)
(*                   2012 - 2015                   *)
(*                                                 *)
(***************************************************)

(* do all *)
open Frontend
open Utils
open Utils.Arg_parser
open Domains
open InvMap
open Language.Ast

(*
   let run_analysis analysis_function program () =
     try

       let start = Sys.time () in
       let terminating = analysis_function program !main in
       Config.result := terminating;
       let stop = Sys.time () in
       Format.fprintf !fmt "Final Analysis Result: ";
       let result = if terminating then "TRUE" else "UNKNOWN" in
       Format.fprintf !fmt "%s\n" result;
       if !time then
         exectime := string_of_float (stop -. start);
         Format.fprintf !fmt "Time: %f s\n" (stop-.start);
       Format.fprintf !fmt "\nDone.\n";
       terminating
     with
     | Config.Timeout ->
       Format.fprintf !fmt "\nThe Analysis Timed Out!\n";
       Format.fprintf !fmt "\nDone.\n";
       false

   let cda_run s : (module Cda.CDA_ITERATOR)=
     let module D = (val s: SEMANTIC) in
     (module Cda.Make(D))


   let termination_iterator (): (module SEMANTIC)=
     let module S =
       (val (match !domain with
       | "boxes" -> if !ordinals then (module TerminationBoxesOrdinals) else (module TerminationBoxes)
       | "octagons" -> if !ordinals then (module TerminationOctagonsOrdinals) else (module TerminationOctagons)
       | "polyhedra" -> if !ordinals then (module TerminationPolyhedraOrdinals) else (module TerminationPolyhedra)
       | _ -> raise (Invalid_argument "Unknown Abstract Domain"))
       : SEMANTIC)
     in
     (module S)

   let guarantee_iterator (): (module SEMANTIC)=
     let module S =
       (val (match !domain with
       | "boxes" -> if !ordinals then (module GuaranteeBoxesOrdinals) else (module GuaranteeBoxes)
       | "octagons" -> if !ordinals then (module GuaranteeOctagonsOrdinals) else (module GuaranteeOctagons)
       | "polyhedra" -> if !ordinals then (module GuaranteePolyhedraOrdinals) else (module GuaranteePolyhedra)
       | _ -> raise (Invalid_argument "Unknown Abstract Domain"))
       : SEMANTIC)
     in
     (module S)



   let recurrence_iterator (): (module SEMANTIC)=
     let module S =
       (val (match !domain with
       | "boxes" -> if !ordinals then (module RecurrenceBoxesOrdinals) else (module RecurrenceBoxes)
       | "octagons" -> if !ordinals then (module RecurrenceOctagonsOrdinals) else (module RecurrenceOctagons)
       | "polyhedra" -> if !ordinals then (module RecurrencePolyhedra) else (module RecurrencePolyhedraOrdinals)
       | _ -> raise (Invalid_argument "Unknown Abstract Domain"))
       : SEMANTIC)
     in
     (module S)


   let ctl_iterator (): (module SEMANTIC)=
     let module S =
       (val (match !domain with
       | "boxes" -> if !ordinals then (module CTLBoxesOrdinals) else (module CTLBoxes)
       | "octagons" -> if !ordinals then (module CTLOctagonsOrdinals) else (module CTLOctagons)
       | "polyhedra" -> if !ordinals then (module CTLPolyhedraOrdinals) else (module CTLPolyhedra)
       | _ -> raise (Invalid_argument "Unknown Abstract Domain"))
       : SEMANTIC)
     in
     (module S)

   let termination (module S: SEMANTIC) program =
     if not !minimal then (
       Format.fprintf !fmt "\nAbstract Syntax:\n" ;
       Ast.prog_print !fmt program ) ;
     let parsedPrecondition = parsePropertyString !precondition in
     let precondition = fst @@ Ast.StringMap.find "" @@ I_to_ast.property_I_to_ast_of_prog program !main parsedPrecondition in
     let analysis_function = S.analyze  ~precondition:(Some precondition) ~property:S.dummy_prop in
     run_analysis  analysis_function program ()


   let guarantee (module S: SEMANTIC) program  property =
     let property =
       match property with
       | None -> raise (Invalid_argument "Unknown Property")
       | Some property -> property
     in
     if not !minimal then
       begin
         Format.fprintf !fmt "\nAbstract Syntax:\n";
         Ast.prog_print !fmt program;
         Format.fprintf !fmt "\nProperty: ";
         Ast.property_print !fmt property;
       end;
     let parsedPrecondition = parsePropertyString !precondition in
     let precondition = fst @@ Ast.StringMap.find "" @@ I_to_ast.property_I_to_ast_of_prog program !main parsedPrecondition in
     let analysis_function  = S.analyze in
     run_analysis (analysis_function ~precondition:(Some precondition) ~property:(Exp property)) program ()

   let recurrence (module S: SEMANTIC) program property =
     let property =
       match property with
       | None -> raise (Invalid_argument "Unknown Property")
       | Some property -> property
     in
     if not !minimal then
       begin
         Format.fprintf !fmt "\nAbstract Syntax:\n";
         Ast.prog_print !fmt program;
         Format.fprintf !fmt "\nProperty: ";
         Ast.property_print !fmt property;
       end;
     let parsedPrecondition = parsePropertyString !precondition in
     let precondition = fst @@ Ast.StringMap.find "" @@ I_to_ast.property_I_to_ast_of_prog program !main parsedPrecondition in
     let analysis_function  = S.analyze in
       run_analysis (analysis_function ~precondition:(Some precondition) ~property:(Exp property)) program ()

   let ctl_ast (module S: SEMANTIC) prog property=
     let starttime = Sys.time () in
     let parsedPrecondition = parsePropertyString !precondition in
     let precondition = fst @@ Ast.StringMap.find "" @@ I_to_ast.property_I_to_ast_of_prog prog !main parsedPrecondition in
     if not !minimal then
       begin
         Format.fprintf !fmt "\nAbstract Syntax:\n";
         Ast.prog_print !fmt prog;
         Format.fprintf !fmt "\n";
       end;
     let analyze = S.analyze
     in
     let result = analyze ~precondition:(Some precondition)  ~property:(Ctl property) prog "" in
     if !time then begin
       let stoptime = Sys.time () in
       exectime := string_of_float (stoptime-.starttime);
       Format.fprintf !fmt "\nTime: %f" (stoptime-.starttime)
     end;
     if result then
       Format.fprintf !fmt "\nFinal Analysis Result: TRUE\n"
     else
       Format.fprintf !fmt "\nFinal Analysis Result: UNKNOWN\n"
     ;
     result
   let ctl_cfg () =
     if !filename = "" then raise (Invalid_argument "No Source File Specified");
     if !property = "" then raise (Invalid_argument "No Property Specifilet s = Lexing.dummy_posed");
     let starttime = Sys.time () in
     let (cfg, getProperty) = Tree_to_cfg.prog (File_parser.parse_file !filename) !main in
     let mainFunc = Cfg.find_func !main cfg in
     let cfg = Cfg.insert_entry_exit_label cfg mainFunc in (* add exit/entry labels to main function *)
     let cfg = if !noinline then cfg else Cfg.inline_function_calls cfg in (* inline all non recursive functions unless -noinline is used *)
     let cfg = Cfg.add_function_call_arcs cfg in (* insert function call edges for remaining function calls *)
     let ctlProperty = CTLProperty.map File_parser.parse_bool_expression @@ parseCTLPropertyString_plain !property in
     let ctlProperty = CTLProperty.map getProperty ctlProperty in
     let precondition = getProperty @@ File_parser.parse_bool_expression !precondition in
     let analyze =
       match !domain with
       | "boxes" -> if !ordinals then CFGCTLBoxesOrdinals.analyze else CFGCTLBoxes.analyze
       | "octagons" -> if !ordinals then CFGCTLOctagonsOrdinals.analyze else CFGCTLOctagons.analyze
       | "polyhedra" -> if !ordinals then CFGCTLPolyhedraOrdinals.analyze else CFGCTLPolyhedra.analyze
       | _ -> raise (Invalid_argument "Unknown Abstract Domain")
     in
     if not !minimal then
       begin
         Format.fprintf !fmt "\nCFG:\n";
         Format.fprintf !fmt "%a" Cfg_printer.print_cfg cfg ;
         Format.fprintf !fmt "\n";
       end;
     if not !minimal && !Config.dot then
       begin
         Format.fprintf !fmt "CFG_DOT:\n %a" Cfg_printer.output_dot cfg;
         Format.fprintf !fmt "\n";
       end;
     let mainFunc = Cfg.find_func !main cfg in
     let possibleLoopHeads = Loop_detection.possible_loop_heads cfg mainFunc in
     let domSets = Loop_detection.dominator cfg mainFunc in
     let result = analyze ~precondition:precondition cfg mainFunc possibleLoopHeads domSets ctlProperty in
     Config.result := result;
     if !time then begin
       let stoptime = Sys.time () in
       Config.exectime := string_of_float (stoptime-.starttime);
       Format.fprintf !fmt "\nTime: %f" (stoptime-.starttime)
     end;
     if result then
       Format.fprintf !fmt "\nAnalysis Result: TRUE\n"
     else
       Format.fprintf !fmt "\nAnalysis Result: UNKNOWN\n"
     ;
     result *)

let doit () =
  let open Config in
  (* Parsing cli args -> into Config ref variables *)
  parse_args ();

  (* Property and filename must be given (except for termination property) *)
  if !filename = "" then raise (Invalid_argument "No Source File Specified");
  (if !property = "" then
     match !analysis with
     | "termination" -> ()
     | _ -> raise (Invalid_argument "No Property File Specified"));

  (* Parsing the property and the file to an ast *)
  let sources = parseFile !filename in
  let program, prop =
    match !analysis with
    | "termination" ->
        let s = Lexing.dummy_pos in
        let p =
          (Intermediate.I_universal (Intermediate.I_TRUE, (s, s)), (s, s))
        in
        let program, property =
          I_to_ast.prog_itoa ~property:(!main, p) sources
        in
        (program, None)
    | "guarantee" | "recurrence" ->
        let program, property =
          I_to_ast.prog_itoa ~property:(!main, parseProperty !property) sources
        in
        (program, property)
    | "ctl" | "ctl-ast" | "ctl-cfg" ->
        let parsedProperty = parseCTLPropertyString !property in
        let program, property =
          I_to_ast.ctl_prog_itoa parsedProperty !main (parseFile !filename)
        in
        (program, None)
    | _ -> raise (Invalid_argument "Unknown Analysis")
  in
  let vars, main, funcs = program in
  (* A program is a map of variable, a bock (see: Ast.ml) and a map of functions *)
  Format.fprintf !fmt "\nAbstract Syntax:\n";
  Ast.prog_print !fmt program;
  Format.fprintf !fmt "\n";
  let module V = Itv.Make  in
  let module P = Apron_numeric.Poly_AP in
  (* let module V = Partition.Make (P) in *)
  let module I = C_fwd.Make (V) in
  let f = Ast.StringMap.find "main" funcs in
  let vars = Ast.StringMap.to_seq f.funcVars |> List.of_seq |> List.map snd in
  let ic,oc = Sig.Query.empty_ichan, Sig.Query.empty_ochan in
  let fwd,_,_= I.exec f.funcBody vars ic oc in
  Format.printf "Forward analysis result \n";
  I.print Format.std_formatter fwd;
  let module B = C_bwd.Make (V) in 
  let fwd = let t = B.top vars in {t with inv = fwd.inv; num_inv = fwd.num_inv} in
  let bwd = B.exec fwd f.funcBody vars ic oc  in
  Format.printf "\n B analysis result \n";
  B.print Format.std_formatter bwd
let _ = doit ()
