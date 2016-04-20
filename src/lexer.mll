(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006-2012 Baelde, Tiu, Ziegler, Heath                      *)
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

{
  open Parser
  open Lexing

  exception Illegal_string of char
  exception Illegal_name of string * string
  exception Unknown_command of string

  (* XXX incrline = new_line in OCaml >= 3.11.0 *)
  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }

  (* == Quoted strings ============================================== *)

  (* keep track of the content of a quoted string
   * across multiple lines *)
  let strbuf = Buffer.create 128
  (* also keep track of the beginning of the string *)
  let strstart = ref dummy_pos

  let escape_table = Hashtbl.create 4
  let _ = List.iter (fun (k,t) -> Hashtbl.add escape_table k t)
            [ (* standard escaping sequences *)
              'b',  '\b';
              't',  '\t';
              'n',  '\n';
              'r',  '\r'
            ]

  let addChar c = Buffer.add_char strbuf c
  let addEscapedChar c = addChar
                           (try Hashtbl.find escape_table c
                            with Not_found -> c)
  let addString s = Buffer.add_string strbuf s

  (* == Comments ==================================================== *)

  (* keep track of the token parsed just before the comment *)
  let prev_token = ref None

  (* == Token tables ================================================ *)

  let command_table = Hashtbl.create 20
  let _ = List.iter (fun (k,t) -> Hashtbl.add command_table k t)
            [ (* Bedwyr meta-commands *)
              "exit",           EXIT;
              "help",           HELP;
              "include",        INCLUDE;
              "reset",          RESET;
              "reload",         RELOAD;
              "session",        SESSION;
              "debug",          DEBUG;
              "time",           TIME;
              "equivariant",    EQUIVARIANT;
              "freezing",       FREEZING;
              "saturation",     SATURATION;
              "env",            ENV;
              "typeof",         TYPEOF;
              "show_table",     SHOW_TABLE;
              "clear_tables",   CLEAR_TABLES;
              "clear_table",    CLEAR_TABLE;
              "save_table",     SAVE_TABLE;
              "assert",         ASSERT;
              "assert_not",     ASSERT_NOT;
              "assert_raise",   ASSERT_RAISE
            ]
  let get_command n =
    try Hashtbl.find command_table n
    with Not_found -> raise (Unknown_command n)

  (* Upper-case tokens *)
  let ub_keyword_t = Hashtbl.create 4
  let _ = List.iter (fun (k,t) -> Hashtbl.add ub_keyword_t k t)
            [ (* Bedwyr upper-case keywords *)
              "Kind",           KKIND;
              "Type",           TTYPE;
              "Define",         DEFINE;
              "Theorem",        THEOREM
            ]
  let ua_keyword_t = Hashtbl.create 9
  let _ = List.iter (fun (k,t) -> Hashtbl.add ua_keyword_t k t)
            [ (* Abella upper-case keywords *)
              "Close",          CLOSE;
              "Qed",            QED;
              "Query",          QUERY;
              "Import",         IMPORT;
              "Specification",  SPECIFICATION;
              "Split",          SSPLIT;
              "Set",            SET;
              "Show",           SHOW;
              "Quit",           QUIT
            ]
  let get_upper n =
    try Hashtbl.find ub_keyword_t n
    with Not_found -> begin
      try Hashtbl.find ua_keyword_t n
      (* free variable in a query, bound variable otherwise *)
      with Not_found -> UPPER_ID n
    end

  (* Lower-case tokens *)
  let lb_keyword_t = Hashtbl.create 3
  let _ = List.iter (fun (k,t) -> Hashtbl.add lb_keyword_t k t)
            [ (* Bedwyr lower-case keywords *)
              "inductive",      INDUCTIVE;
              "coinductive",    COINDUCTIVE;
              "by",             BY
            ]
  let lb_primitive_t = Hashtbl.create 9
  let _ = List.iter (fun (k,t) -> Hashtbl.add lb_primitive_t k t)
            [ (* Bedwyr lower-case primitive operators and constants *)
              "type",           TYPE;
              "prop",           PROP;
              "string",         STRING;
              "nat",            NAT;
              "forall",         FORALL;
              "exists",         EXISTS;
              "nabla",          NABLA;
              "true",           TRUE;
              "false",          FALSE
            ]
  let la_keyword_t = Hashtbl.create 5
  let _ = List.iter (fun (k,t) -> Hashtbl.add la_keyword_t k t)
            [ (* Abella lower-case keywords, except for tactics *)
              "to",             TO;
              "with",           WITH;
              "on",             ON;
              "as",             AS;
              "keep",           KEEP
            ]
  let la_tactic_t = Hashtbl.create 23
  let _ = List.iter (fun (k,t) -> Hashtbl.add la_tactic_t k t)
            [ (* Abella tactics, except for "exists" and "split*" *)
              "induction",      IND_T;
              "coinduction",    COIND_T;
              "intros",         INTROS_T;
              "case",           CASE_T;
              "search",         SEARCH_T;
              "apply",          APPLY_T;
              "backchain",      BACKCHAIN_T;
              "unfold",         UNFOLD_T;
              "assert",         ASSERT_T;
              "split",          SPLIT_T;
              "left",           LEFT_T;
              "right",          RIGHT_T;
              "permute",        PERMUTE_T;
              "inst",           INST_T;
              "cut",            CUT_T;
              "monotone",       MONOTONE_T;
              "undo",           UNDO_T;
              "skip",           SKIP_T;
              "abort",          ABORT_T;
              "clear",          CLEAR_T;
              "abbrev",         ABBREV_T;
              "unabbrev",       UNABBREV_T
            ]
  let lt_keyword_t = Hashtbl.create 6
  let _ = List.iter (fun (k,t) -> Hashtbl.add lt_keyword_t k t)
            [ (* Teyjus lower-case keywords *)
              "sig",            SIG;
              "module",         MODULE;
              "accum_sig",      ACCUMSIG;
              "accumulate",     ACCUM;
              "end",            END;
              "kind",           KIND
            ]
  let get_lower n =
    try Hashtbl.find lb_keyword_t n
    with Not_found -> begin
      try Hashtbl.find lb_primitive_t n
      with Not_found -> begin
        try Hashtbl.find la_keyword_t n
        with Not_found -> begin
          try Hashtbl.find la_tactic_t n
          with Not_found -> begin
            try Hashtbl.find lt_keyword_t n
            (* bound variable, type, prefix constant or predicate *)
            with Not_found -> LOWER_ID n
          end
        end
      end
    end

  (* Internal tokens *)
  let get_intern n =
    (* non-logical predefined constant *)
    INTERN_ID n

  (* Infix-case tokens *)
  let ib_primitive_t = Hashtbl.create 2
  let _ = List.iter (fun (k,t) -> Hashtbl.add ib_primitive_t k t)
            [ (* Bedwyr infix-case primitive operators and constants *)
              "->",             RARROW;
              "=",              EQ
            ]
  let ia_primitive_t = Hashtbl.create 1
  let _ = List.iter (fun (k,t) -> Hashtbl.add ia_primitive_t k t)
            [ (* Abella infix-case primitive operators and constants *)
              "|-",             TURN
            ]
  let it_primitive_t = Hashtbl.create 3
  let _ = List.iter (fun (k,t) -> Hashtbl.add it_primitive_t k t)
            [ (* Teyjus infix-case primitive operators and constants *)
              ":-",             CLAUSEEQ;
              "=>",             IMP;
              "::",             CONS
            ]
  let get_infix n =
    try Hashtbl.find ib_primitive_t n
    with Not_found -> begin
      try Hashtbl.find it_primitive_t n
      (* infix constant *)
      with Not_found -> INFIX_ID n
    end
}

let digit = ['0'-'9']
let number = digit+

let uchar = ['A'-'Z']
let lchar = ['a'-'z']

(* special symbols *)
let prefix_special       = ['?' '`' '\'' '$']
let infix_special_nostar = ['-' '^' '<' '>' '=' '~' '+' '&' ':' '|']
let infix_special        = infix_special_nostar | '*'
let tail_special_noslash = ['_' '@' '#' '!']

let safe_char_noslash =
  uchar | lchar | digit |  prefix_special | tail_special_noslash
let safe_char = safe_char_noslash | '/'

let upper_name  = uchar safe_char*
let lower_name  = (lchar|prefix_special) safe_char*
let infix_name  = infix_special+
let intern_name = '_' safe_char+

let blank = ' ' | '\t' | '\r'

let in_comment = '/' | '*' | [^'/' '*' '\n']+
let in_qstring = [^'\\' '"' '\n']+

rule token = parse
  (* Multi-line and single-line comments *)
  | "/*"                        { comment 0 lexbuf }
  | '%' [^'\n']* '\n'           { incrline lexbuf; token lexbuf }
  | '%' [^'\n']*                { token lexbuf }

  (* Separators *)
  | blank                       { token lexbuf }
  | '\n'                        { incrline lexbuf; token lexbuf }

  | '"'                         { Buffer.clear strbuf ;
                                  strstart := lexbuf.lex_start_p ;
                                  qstring lexbuf }

  (* Punctuation *)
  | ":"                         { COLON }
  | ":="                        { DEFEQ }
  | ";"                         { SEMICOLON }
  | ","                         { COMMA }
  | "."                         { DOT }
  | "("                         { LPAREN }
  | ")"                         { RPAREN }

  (* Bedwyr meta-commands *)
  | '#' (lower_name as n)       { get_command n }

  (* Bedwyr primitive operators and constants *)
  | "/\\"                       { AND }
  | "\\/"                       { OR }
  | "\\"                	{ BSLASH }

  (* Abella tactics *)
  | "split*"                    { SPLITSTAR_T }

  (* Abella primitive operators and constants *)
  | "{"                         { LBRACK }
  | "}"                         { RBRACK }

  (* Upper-case prefix names *)
  | upper_name as n             { get_upper n }
  | (upper_name as n) "/*"      { prev_token := Some (get_upper n) ;
                                  comment 0 lexbuf }

  (* Lower-case prefix names *)
  | lower_name as n             { get_lower n }
  | (lower_name as n) "/*"      { prev_token := Some (get_lower n) ;
                                  comment 0 lexbuf }

  (* Internal prefix names *)
  | intern_name as n            { get_intern n }
  | (intern_name as n) "/*"     { prev_token := Some (get_intern n) ;
                                  comment 0 lexbuf }

  (* Infix-case names *)
  | infix_name as n             { get_infix n }

  (* Placeholder *)
  | '_'                         { UNDERSCORE }
  | "_/*"                       { prev_token := Some (UNDERSCORE) ;
                                  comment 0 lexbuf }

  (* Ambiguous names *)
  | ((safe_char* safe_char_noslash) as n1) (infix_name as n2)
  | (safe_char+ as n1) ((infix_special_nostar infix_special*) as n2)
  | (infix_name as n1) (safe_char+ as n2)
                                { raise (Illegal_name (n1,n2)) }

  | number as n                 { NUM (int_of_string n) }

  (* misc *)
  | '\x04'              (* ctrl-D *)
  | eof                 { EOF }

  | _ as c              { raise (Illegal_string c) }

and comment level = parse
  | in_comment          { comment level lexbuf }
  | "/*"                { comment (level + 1) lexbuf }
  | "*/"                { if level = 0 then
                            match !prev_token with
                              | None -> token lexbuf
                              | Some t -> prev_token := None ; t
                          else
                            comment (level - 1) lexbuf }
  | '\n'                { incrline lexbuf ;
                          comment level lexbuf }
  | eof                 { failwith "comment not closed at end of file" }

and qstring = parse
  | "\\\n"              { incrline lexbuf ;
                          qstring lexbuf }
  | '\\' (_ as c)       { addEscapedChar c ;
                          qstring lexbuf }
  | in_qstring as s     { addString s ;
                          qstring lexbuf }
  | '"'                 { let pos = (!strstart,lexbuf.lex_curr_p) in
                          QSTRING (pos,Buffer.contents strbuf) }
  | '\n'                { addChar '\n' ;
                          incrline lexbuf ;
                          qstring lexbuf }
  | eof                 { failwith "string not closed at end of file" }
