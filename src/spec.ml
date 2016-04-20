(****************************************************************************)
(* SPEC                                                                     *)
(* Copyright (C) 2011-2012 Alwen Tiu                                        *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

exception Invalid_command
exception Assertion_failed
exception Read_def_failed 
exception Def_file_missing

let welcome_msg =
  "SPEC: An equivalence checker for the spi-calculus. 

Version 0.2

This software is under GNU Public License.
Copyright (c) 2011-2013 Alwen Tiu

Type `#help;' to display available commands. 
\n"

let usage_msg =
  "SPEC.  
This software is under GNU Public License.
Copyright (c) 2011-2013 Alwen Tiu. 

"

let help_msg =
  "List of commands: 
#help;                               Display this message.
#exit;                               Exit.
#equivariant [on/off];               Enable/disable equivariant.
#reflexive [on/off];                 Enable/disable reflexivity checking. 
#load [file];                        Load a process definition file.
#reset;                              Clears the current session. 
#show_bisim;                         Displays the current bisimulation set. 
#save_bisim [file];                  Save the bisimulation set to a file. 
#save_bisim_latex [file];            Save the current bisimulation set to a file in the LaTeX format. 
#save_bisim_raw [file];              Save the current bisimulation set in the internal Bedwyr syntax. 
#show_def [name]                     Show the definition for an agent. 
#show_defs;                          Show all the definitions. 
#time [on/off]                       Show/hide the execution time of a query.
#trace [on/off]                      Enable/disable debugging information. 
"

let interactive = ref true
let queries     = ref []
let inclfiles   = ref []

(* Flags *)
let var_on = Term.get_var (Term.atom "on") 
let var_off = Term.get_var (Term.atom "off")

(* list of options specific to bisimulation *) 
let options = ref [(Term.atom "trace",false); (Term.atom "reflexive",false)]

(* A simple wrapper function to call Bedwyr prove engine *)
let do_query s f g = 
  Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 g ~success:s ~failure:f

let update_option_clauses () = ()
  (* let v = Term.fresh ~ts:0 ~lts:0 Term.Logic in  *)
  (* let body = List.map (fun (x,y) -> Term.op_eq v x) (List.filter (fun (x,y) -> y=true) (!options)) in *)
  (* let absbody =  *)
  (*    if (body = []) then (Term.abstract v Term.op_false)  *)
  (*    else (Term.abstract v (List.fold_left Term.op_or Term.op_false body)) in  *)
  (* let head = Spi.Process.option in *)
  (*   System.remove_def head ;  *)
  (*   System.add_clause System.Normal head 0 absbody  *)

let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if file = "" then
      "" (* lexbuf information is rarely accurate at the toplevel *)
    else
      Format.sprintf ": file %s, line %d, character %d" file line char

let do_cleanup f x clean =
  try f x ; clean () with e -> clean () ; raise e

(* let clean_tables () =  *)
(*       Hashtbl.iter *)
(*         (fun k v -> match v with *)
(*            | (_,_,Some t) -> Table.reset t *)
(*            | _ -> ()) *)
(*         System.defs *)


let count_bisim = (fun () -> 
      try
        let _,_,_,table,_ = System.get_def Spi.Process.bisim_arity Spi.Process.bisim in
        begin 
         match table with
         | Some table ->              
             Spi.bisim_size table
         | None -> 
             failwith ("No bisimulation set found!\n")
        end
        with
         | Not_found -> raise (System.Missing_declaration (Spi.Process.bisim_str,None))
      )

let prove_bisim a = 
  let t0 = Unix.gettimeofday () in 
  let time =
      (fun () ->
         if !System.time then
           Format.printf "Running time: + %.0fs\n" (Unix.gettimeofday () -. t0))
  in
  let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
  in
  let found = ref false in
  let success = (fun s k -> 
         time () ;
         found := true ;
         Printf.printf "\nThe two processes are bisimilar.\n" ;
         Printf.printf "Size of bisimulation set: %d.  " (count_bisim ()) ;
         Printf.printf "Use #show_bisim to show the set.\n"
    )
  in    
  let failure = (fun () -> 
       time () ; 
       if not !found then Printf.printf "\nThe two processes are not bisimilar.\n"
     ) 
  in 
     do_cleanup (do_query success failure) a reset

let prove_show_def a = 
  let pre_show_def = Input.pre_predconstid (Input.dummy_pos) (Spi.Process.show_def_str) in 
  let d = Input.pre_qstring (Input.dummy_pos) a in 
  let query = System.translate_query (Input.pre_app (Input.dummy_pos) pre_show_def [d]) in 
  let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
  in
  let found = ref false in
  let success = (fun s k -> found := true) in    
  let failure = (fun () -> 
       if not !found then Printf.printf "\nNo definition found for %s.\n" a
     ) 
  in 
     do_cleanup (do_query success failure) query reset
  
let prove_show_defs () =
  List.iter (fun (a,n) -> prove_show_def a) (List.rev !Spi.spi_sig)
  

(* [show_bisim] 
   NOTE: we need to find out the (local) timestamps of the entries in the table. 
   This is because we use a bedwyr program to print (instead of doing it inside
   ocaml), so we need to feed the correct timestamp to the prover. 
*) 

let show_bisim_query n g = 
    Term.app Spi.Process.show_bisim [Term.qstring (string_of_int n) ; g] 

let save_bisim_query f n g = 
    Term.app Spi.Process.save_bisim [f ; Term.qstring (string_of_int n) ; g] 

let save_bisim_latex_query f n g = 
    Term.app Spi.Process.save_bisim_latex [f ; g] 

let save_latex_header fout =
  Printf.fprintf fout "\\documentclass{article}\n"; 
  Printf.fprintf fout "\\usepackage[margin=2cm]{geometry}\n"; 
  Printf.fprintf fout "\\begin{document} \n" ;
  Printf.fprintf fout "\\begin{enumerate} \n" 

let save_latex_footer fout =
  Printf.fprintf fout "\\end{enumerate}\n";
  Printf.fprintf fout "\\end{document} \n" 

let show_bisim query table  = 
  let s = (fun ts k -> ()) in
  let f = (fun () -> ()) in 
  let prv x y g = 
      Prover.prove ~level:Prover.One ~local:x
                   g
                   ~timestamp:y ~success:s ~failure:f 
  in
  let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
  in
  let i = ref 1 in 
  Table.iter_fun table 
    (fun t tag -> 
      let r = Norm.deep_norm (Term.app t [Spi.Process.bisim]) in 
      match tag with
      | Table.Proved -> 
          let (ts,lts) = Spi.get_timestamps r in 
          do_cleanup (prv (lts) (ts)) (query !i r) reset;
          i := !i + 1
      | _ -> ()
    )


let check_def a =
  let a = Term.qstring a in 
  let query = Term.app (Spi.Process.check_def) [a] in
  let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
  in
  let found = ref false in
  let success = (fun s k -> found := true)  in    
  let failure = (fun () -> 
       if not !found then Printf.printf "Query failed.\n"
     ) 
  in 
     do_cleanup (do_query success failure) query reset

let rec process_spi ?(interactive=false) parse lexbuf =
  try while true do try
    if interactive then Format.printf "SPEC> %!" ;
    begin match parse Spilexer.token lexbuf with
      | Spi.Def (agent, n, b) -> (
        try (
           let pred = Spi.Process.agent_def in
           let _,_,_,_,ty = System.get_def 2 pred in 
           let pred_var = Term.get_var pred in 
             Format.printf "Reading spi definition\n" ;  
             Spi.add_spi_sig agent n ; 
     	     (* System.update_def Spi.Process.agent_def b ;  *)
             System.add_clauses [(pred_var,ty)] [b] 
             (* check_def agent *)
         ) 
         with | Not_found ->  
            raise (System.Missing_definition ("agent_def",None))
        )
      | Spi.Query (a,b)       -> 
	  let q = System.translate_query b in
  	    System.clear_tables () ; prove_bisim q 
      | Spi.Command (c,a) -> command lexbuf (c,a)
    end ;
    if interactive then flush stdout
  with
    | Failure "eof" as e -> raise e
    | Parsing.Parse_error ->
        Format.printf "Syntax error%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | Failure "lexing: empty token" ->
        Format.printf "Lexing error%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | Assertion_failed ->
        Format.printf "Assertion failed%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | Spi.Duplicate_agent_def m  ->
        Format.printf "Agent %s was already defined!\n" m ;
        if interactive then Lexing.flush_input lexbuf else raise Read_def_failed
    | Spi.Sig_mismatch (m,n) ->
        Format.printf "Agent %s with arity %d was not defined! \n" m n ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | e when not interactive ->
        Format.printf "Error in %s, line %d: %s\n"
          lexbuf.Lexing.lex_curr_p.Lexing.pos_fname
          lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
          (Printexc.to_string e) ;
        exit 1
    (* | System.Undefined s -> *)
    (*     Format.printf "No definition found for %a !\n%!" Pprint.pp_term s *)
    (* | System.Inconsistent_definition s -> *)
    (*     Format.printf "Inconsistent extension of definition %a !\n" *)
    (*       Pprint.pp_term s *)
    (* | System.Arity_mismatch (s,a) -> *)
    (*     Format.printf "Definition %a doesn't have arity %d !\n%!" *)
    (*       Pprint.pp_term s a *)
    (* | System.Interrupt -> *)
    (*     Format.printf "User interruption.\n%!" *)
    (* | Prover.Level_inconsistency -> *)
    (*     Format.printf "This formula cannot be handled by the left prover!\n%!" *)
    (* | Unify.NotLLambda t -> *)
    (*     Format.printf "Not LLambda unification encountered: %a\n%!" *)
    (*       Pprint.pp_term t *)
    | Invalid_command ->
        Format.printf "Invalid command, or wrong arity!\n%!"
    | Failure s ->
        Format.printf "Error: %s\n" s
    | e ->
        Format.printf "Bedwyr error: %s\n%!" (Printexc.to_string e) ;
        raise e
  done with
  | Failure "eof" -> ()

and input_from_spi_file file = 
 let num_def = List.length !Spi.spi_sig in
 let cwd = Sys.getcwd () in
 let f = open_in file in 
 let lexbuf = Lexing.from_channel f in
    Sys.chdir (Filename.dirname file) ;
    lexbuf.Lexing.lex_curr_p <- {
      lexbuf.Lexing.lex_curr_p with
        Lexing.pos_fname = file } ;
    (
     try 
      input_spi_defs lexbuf 
     with Read_def_failed -> Printf.printf "File loading aborted\n"
    );
    close_in f ; 
    Sys.chdir cwd ;
    Printf.printf "%d process definition(s) read. Use #show_defs to show all definitions\n" 
                  (List.length !Spi.spi_sig - num_def)

and input_spi_defs lexbuf = process_spi Spiparser.input_def lexbuf 
and input_spi_queries ?(interactive=false) lexbuf = 
  process_spi ~interactive Spiparser.input_query lexbuf
and command lexbuf = function
  | "exit",[] -> System.close_all_files () ; exit 0
  | "equivariant",[d] -> 
      let b =
        begin match d with
          | "on" -> 
             (
               Printf.printf "Equivariance checking is enabled.\n" ; 
               true
             )
          | "off" -> 
             (
               Printf.printf "Equivariance checking is disabled.\n" ; 
               false
             )
          | _ -> raise Invalid_command
        end
      in
        Index.eqvt_index := b
  | "reflexive", [d] ->
        begin match d with
          | "on" -> 
             (
               System.update_def (Spi.Process.refl_opt) (Term.lambda 0 (Term.op_true)) ; 
	       Printf.printf "Reflexivity checking is enabled.\n"
             )
          | "off" -> 
             (
               System.update_def (Spi.Process.refl_opt) (Term.lambda 0 (Term.op_false)) ; 
               Printf.printf "Reflexivity checking is disabled.\n"
             )
          | _ -> raise Invalid_command
        end
  | "trace", [d] -> 
        begin match d with
          | "on" -> 
             (
               System.update_def (Spi.Process.trace_opt) (Term.lambda 0 (Term.op_true)) ; 
	       Printf.printf "Trace printing is enabled.\n"
             )
          | "off" -> 
             (
               System.update_def (Spi.Process.trace_opt) (Term.lambda 0 (Term.op_false)) ; 
               Printf.printf "Trace printing is disabled.\n"
             )
          | _ -> raise Invalid_command
        end

  | "help",[] -> Format.printf "%s" help_msg
  | "load",[fname] -> 
       begin try
         input_from_spi_file fname
       with
       | Sys_error e -> Printf.printf "Error: %s \n" e
       end
  | "reset",[] ->
     System.clear_tables () ; 
     Spi.reset_spi_sig () ; 
     System.close_all_files () ;
     System.update_def (Spi.Process.agent_def) (Term.lambda 2 (Term.op_false))
  | "show_bisim",[] -> 
     (
       try
        let _,_,_,table,_ = System.get_def (Spi.Process.bisim_arity) Spi.Process.bisim in
        begin 
         match table with
         | Some table ->              
                show_bisim show_bisim_query table 
         | None ->
             failwith ("No bisimulation set found!\n")
        end
        with
         | Not_found -> raise (System.Missing_definition (Spi.Process.bisim_str,None))
     )
  | "show_table",[] -> 
       System.show_table (Input.dummy_pos,Spi.Process.bisim) 
  | "save_bisim",[name] -> 
    (
      try
	let f = Term.qstring name in 
        let _,_,_,table,_ = System.get_def (Spi.Process.bisim_arity) Spi.Process.bisim in
        let _ = System.open_user_file name in
        begin
         match table with
         | Some table ->
             show_bisim (fun n g -> save_bisim_query f n g) table ;
             System.close_user_file name
         | None ->
             System.close_user_file name ;
             failwith ("No bisimulation set found!\n")
        end
      with
      | Not_found -> raise (System.Missing_definition (Spi.Process.bisim_str,None))
      | Sys_error e -> Printf.printf "Error: %s \n" e ;     
     )

  | "save_bisim_latex",[name] -> 
    (
      try
	let f = Term.qstring name in 
        let _,_,_,table,_ = System.get_def (Spi.Process.bisim_arity) (Spi.Process.bisim) in
        let fout = System.open_user_file name in
        begin
         match table with
         | Some table ->
             save_latex_header fout ;
             show_bisim (fun n g ->
                     Printf.fprintf fout "\\item \n" ;
                     save_bisim_latex_query f n g) table ;
             save_latex_footer fout ;
             System.close_user_file name
         | None ->
             System.close_user_file name ;
             failwith ("No bisimulation set found!\n")
        end
      with
      | Not_found -> raise (System.Missing_definition (Spi.Process.bisim_str,None))
      | Sys_error e -> Printf.printf "Error: %s \n" e ;
   )

  | "save_bisim_raw",[name] -> 
    (
      try
        let _,_,_,table,_ = System.get_def (Spi.Process.bisim_arity) (Spi.Process.bisim) in
        let fout = System.open_user_file name in
        begin
         match table with
         | Some table ->
             Spi.save_bisim_raw fout table ;
             System.close_user_file name
         | None ->
             System.close_user_file name ;
             failwith ("No bisimulation set found!\n")
        end
      with
      | Not_found -> raise (System.Missing_definition (Spi.Process.bisim_str,None))
      | Sys_error e -> Printf.printf "Error: %s \n" e ;
   )

  | "show_def",[a] -> prove_show_def a 
        
  | "show_defs",[] -> prove_show_defs ()

  (* | "set",[o;v] -> () *)
      (* let _ = try List.assoc o !options with Not_found -> raise Invalid_command in *)
      (* let nv =  *)
      (*     begin match Term.observe v with *)
      (*     | Term.Var v when v==var_on -> true *)
      (*     | Term.Var v when v==var_off -> false *)
      (*     | _ -> raise Invalid_command *)
      (*     end  *)
      (* in *)
      (*   options := (o,nv) :: (List.remove_assoc o !options) ;  *)
      (*   update_option_clauses () *)

  | "time",[d] -> 
      System.time :=
        begin match d with
          | "on" -> true
          | "off" -> false
          | _ -> raise Invalid_command
        end

  | _ -> raise Invalid_command

let get_exe_dir () = 
  try 
    let exe_name = Sys.executable_name in 
    let i = String.rindex exe_name '/' in 
     String.sub exe_name 0 (i+1) 
  with
  | Not_found -> "" 
      
let get_def_file () = 
  let file = (get_exe_dir ()) ^ "defs/spec.def" in 
    if Sys.file_exists file then file 
    else raise Def_file_missing 
 
let rec process_def lexbuf =
  try while true do try
    begin match Parser.input_def Lexer.token lexbuf with
      | Input.KKind (l, k) ->
          List.iter
            (fun s -> System.declare_type s k)
            l
      | Input.TType (l, t) ->
          List.iter
            (fun s -> System.declare_const s t)
            l
      (* [AT]: temporary hack: disable ground checking. Why is this check 
         needed anyway? *)
      | Input.Def (decls,defs) ->
          let new_predicates = System.declare_preds decls in
          System.add_clauses new_predicates defs ;          
          ()

      | Input.Query t -> () 
      | Input.Command Input.Include l -> 
          List.iter include_file l 
      | Input.Command c -> () 
      | Input.Theorem thm -> () 
    end 
  with
  | End_of_file -> raise End_of_file 
  | e ->
        Format.printf "[bedwyr] Error in %s, line %d: %s\n"
          lexbuf.Lexing.lex_curr_p.Lexing.pos_fname
          lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
          (Printexc.to_string e) ;
        exit 1
  done with
  | End_of_file -> () 
  | Failure "eof" -> ()

and input_from_file file =
  let cwd = Sys.getcwd () in 
  let lexbuf = Lexing.from_channel (open_in file) in
    Sys.chdir (Filename.dirname file) ;
    lexbuf.Lexing.lex_curr_p <- {
        lexbuf.Lexing.lex_curr_p with
          Lexing.pos_fname = file } ;
    input_defs lexbuf ;
    Sys.chdir cwd
and input_defs lexbuf = process_def lexbuf

and load_session () =
  let def_file = get_def_file () in 
    System.reset_decls () ;
    Input.Typing.clear () ; 
    Spi.reset_spi_sig () ;
    inclfiles := [] ;
    update_option_clauses () ;
    input_from_file def_file

and include_file fname =
  if not (List.mem fname !inclfiles) then begin
    input_from_file fname;
    inclfiles := fname :: !inclfiles
  end

(* and include_def f =  *)
(*   match f with *)
(*   | [g] ->  *)
(*     let g = Term.get_name g in *)
(*     let not_included fname =  *)
(*        if (List.mem fname !inclfiles) then *)
(*         false *)
(*      else ( *)
(*         inclfiles := fname :: !inclfiles ; *)
(*         true *)
(*      ) *)
(*     in *)
(*        if not_included g then input_from_file g else ()  *)
(*   | _ -> assert false *)


let _ =
  load_session () ;
  System.time := true ;
  List.iter (fun s -> input_spi_queries (Lexing.from_string s)) !queries ;
  if !interactive then begin
    Format.printf "%s%!" welcome_msg ;
    input_spi_queries ~interactive:true (Lexing.from_channel stdin)
  end

