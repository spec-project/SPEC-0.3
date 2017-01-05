(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler               *)
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

(* Modified by Alwen Tiu, Ross Horne for SPEC, 2017 *)

{
  open Spiparser
  open Lexing

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }
}

let name = ('?')?['a' - 'z']['A' - 'Z' 'a'-'z' '_' '0'-'9' ] *
let aname = ['A' - 'Z']['A' - 'Z' 'a'-'z' '_' '0'-'9' ] *
let blank = ' ' | '\t' | '\r'
let instring = [^'"'] *

rule token = parse
| '%' [^'\n'] * '\n' { incrline lexbuf; token lexbuf }
| blank              { token lexbuf }
| '\n'               { incrline lexbuf; token lexbuf }

| "!" { BANG }
| "#" { SHARP }
| "0" { ZERO }
| "1" { DONE }
| "." { DOT }
| "=" { EQ }
| "~=" { NEQ }
| ":=" { DEF }
| "bisim" { BISIM }
| "sim" { SIM }
| "keycycle" { KEYCYCLE }
| "stap" { STAP }
| "absurd" { ABSURD }
| "," { COMMA }
| ";" { SEMICOLON }
| "nu" { NU }
| "case" { CASE }
| "let" { LET }
| "of" { OF }
| "in" { IN }
| "|" { PAR }
| "+" { PLUS }
| "(" { LPAREN }
| ")" { RPAREN }
| "[" { LBRAK }
| "]" { RBRAK }
| "<" { LANGLE }
| ">" { RANGLE }
| "{" { LBRAC }
| "}" { RBRAC }
| "enc" { ENC } 
| "hash" { HASH }
| "aenc" { AENC }
| "pub" { PUB }
| "sign" { SIGN }
| "vk" { VK }
| "mac" { MAC }			(* Sign, Hash, Mac *)
| "blind" { BLIND }		(* Blind *)
| "tau" { TAU } 		(* Add tau *)
| "checksign" { CHECKSIGN }	(* Add CheckSign *)
| "adec" { ADEC } 		(* Asymmetric Decode *)
| "unblind" { UNBLIND }		(* Unblind *)
| "getmsg" { GETMSG }		(* Get Message *)

| name as n { ID n }
| aname as n { AID n} 
| '"' (instring as n) '"'
    { String.iter (function '\n' -> incrline lexbuf | _ -> ()) n ;
      STRING n }

| eof    { failwith "eof" }
