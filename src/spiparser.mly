/***************************************************************************
* SPEC                                                                     *
* Copyright (C) 2011-2012 Alwen Tiu                                        *
*                                                                          *
* This program is free software; you can redistribute it and/or modify     *
* it under the terms of the GNU General Public License as published by     *
* the Free Software Foundation; either version 2 of the License, or        *
* (at your option) any later version.                                      *
*                                                                          *
* This program is distributed in the hope that it will be useful,          *
* but WITHOUT ANY WARRANTY; without even the implied warranty of           *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *
* GNU General Public License for more details.                             *
*                                                                          *
* You should have received a copy of the GNU General Public License        *
* along with this code; if not, write to the Free Software Foundation,     *
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *
****************************************************************************/

%{

  let pos i =
    if i = 0 then
      (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
    else
      (Parsing.rhs_start_pos i, Parsing.rhs_end_pos i)

  let qstring p s = Input.pre_qstring p s 
  let constid p s = Input.pre_predconstid p s   

  let nil_op = constid (pos 0) "nil" 
  let cons_op = constid (pos 0) "cons"
  let def_op =  constid (pos 0) "def" 
  let ct_op = constid (pos 0) "ct"
  let zero_op = constid (pos 0) "zero"
  let par_op = constid (pos 0) "par" 
  let plus_op = constid (pos 0) "plus"
  let nu_op = constid (pos 0) "nu" 
  let in_op = constid (pos 0) "inp" 
  let out_op = constid (pos 0) "outp" 
  let match_op = constid (pos 0) "match" 
  let mismatch_op = constid (pos 0) "mismatch" 
  let case_op = constid (pos 0) "case"
  let let_op = constid (pos 0) "let"
  let bang_op = constid (pos 0) "bang" 
  let pr_op = constid (pos 0) "pr"
  let en_op = constid (pos 0) "en"

  let app s t = Input.pre_app (pos 0) s t 
  let lambda v t = Input.pre_lambda (pos 0) [v] t 


  let nuproc a b = 
    let abs_var x t = app nu_op [lambda x t] in 
        List.fold_right abs_var a b 

  let rec mkpairs l = 
     match l with
     | [] | [_] -> assert false
     | [a;b] -> app pr_op [a;b]
     | x::r -> let t = mkpairs r in app pr_op [x;t] 
            

  let change_freeids t =
    let vs = Input.get_freeids t in
    let sub = List.map (fun s -> (s,app ct_op [qstring (pos 0) s]) ) vs in 
     Input.pre_freeidsubst sub t 

  let mkdef a b = 
    let agentname,vars = a in 
    let proc = constid (pos 0) "defProc" in 
    let abs  = constid (pos 0) "defAbs" in 
    let agent_def = constid (pos 0) "agent_def" in 
    let b = List.fold_right (fun v t -> app abs [Input.pre_lambda (pos 0) [v] t]) vars 
                 (app proc [b]) in 
    let d = change_freeids (app agent_def [(qstring (pos 0) agentname); b]) in 
        Spi.Def (agentname,List.length vars,(pos 0,d,Input.pre_true (pos 0)))   

  let mkquery a b = 
    let q = app (constid (pos 0) "bisim_def") [a;b] in 
    Spi.Query (pos 0, change_freeids q)
%}

%token LPAREN RPAREN LBRAK RBRAK LANGLE RANGLE LBRAC RBRAC SEMICOLON BISIM
%token ZERO DOT EQ NEQ COMMA NU PAR PLUS ENC HASH AENC PUB SIGN VK
%token DEF CASE LET OF IN SHARP BANG
%token <string> ID
%token <string> AID
%token <string> STRING

%right PAR PLUS 
%nonassoc BANG
%nonassoc DOT
%nonassoc RBRAK IN


%start input_def input_query
%type <Spi.input> input_def
%type <Spi.input> input_query


%%
input_def:
| head DEF pexp SEMICOLON { mkdef $1 $3  }
input_query:
| head DEF pexp SEMICOLON { mkdef $1 $3  }
| BISIM LPAREN pexp COMMA pexp RPAREN SEMICOLON  { mkquery $3 $5 }
| SHARP ID SEMICOLON { Spi.Command ($2, [])}
| SHARP ID STRING SEMICOLON { Spi.Command ($2, [$3]) }
| SHARP ID AID SEMICOLON { Spi.Command ($2, [$3] ) }
| SHARP ID ID SEMICOLON { Spi.Command ($2, [$3] ) }
| SHARP ID ID ID SEMICOLON { Spi.Command ($2, [$3 ; $4] ) }

head:
| AID { let was_defined = Spi.find_spi_name $1 in
         if was_defined then 
            raise (Spi.Duplicate_agent_def $1)
         else ($1, []) 
      }
| AID LPAREN sids RPAREN { 
        let was_defined = Spi.find_spi_name $1 in
          if was_defined then 
            raise (Spi.Duplicate_agent_def $1)       
          else ($1,$3) 
      }


pexp:
| agent { $1 }
| ZERO { zero_op }
| outpref { let a,b = $1 in app out_op [a;b;zero_op] }
| inpref { let a,b = $1 in app in_op [a ; lambda b zero_op] }
| pexp PAR pexp { app par_op [$1;$3] }
| pexp PLUS pexp { app plus_op [$1;$3] }
| outpref DOT pexp { let a,b = $1 in app out_op [a;b;$3] }
| inpref DOT pexp { let a,b = $1 in app in_op [a;lambda b $3] }
| nupref DOT pexp { nuproc $1 $3 }
| LBRAK texp EQ texp RBRAK pexp { app match_op [$2;$4;$6] }
| LBRAK texp NEQ texp RBRAK pexp { app mismatch_op [$2;$4;$6] }
| cpref IN pexp { let a,(b,c) = $1 in app case_op [a;c;lambda b $3] }
| lpref IN pexp { let t,(v1,v2) = $1 in app let_op [t; lambda v1 (lambda v2 $3)] }
| BANG pexp { app bang_op [$2] }
| apexp { $1 }

apexp:
| LPAREN pexp RPAREN { $2 }

agent:
| AID { 
   let was_defined = Spi.find_spi_sig $1 0 in 
   if was_defined then 
      Input.pre_app (pos 0) def_op [qstring (pos 0) $1 ; nil_op] 
   else
      raise (Spi.Sig_mismatch ($1,0))
  }
| AID LBRAC lids RBRAC { 
   let n = List.length $3 in 
   let cons x y = app cons_op [x;y] in 
   let was_defined = Spi.find_spi_sig $1 n in 
   if was_defined then 
      let args = List.fold_right (fun x t -> cons x t)  $3 nil_op in 
        Input.pre_app (pos 0) def_op [qstring (pos 0) $1 ; args]
   else
      raise (Spi.Sig_mismatch ($1, n))
  }

inpref:
| name_id LPAREN ID RPAREN { ($1,(pos 0,$3, Input.Typing.fresh_typaram () )) }

outpref:
| name_id LANGLE texp RANGLE { ($1, $3) }

nupref: 
| NU LPAREN sids RPAREN { $3 }

cpref: 
| CASE texp OF encpat { ($2,$4) } 

lpref:
| LET prpat EQ texp { ($4,$2) }

sids: 
| ID  { [(pos 0,$1,Input.Typing.fresh_typaram())] }
| ID COMMA sids { (pos 0,$1,Input.Typing.fresh_typaram()) :: $3 }

lids:
| name_id { [$1] }
| name_id COMMA lids  { $1::$3 }

name_id: 
| ID  { Input.pre_freeid (pos 0) $1 }

encpat:
| ENC LPAREN ID COMMA texp RPAREN { ((pos 0,$3,Input.Typing.fresh_typaram()),$5) }

prpat:
| LANGLE ID COMMA ID RANGLE { ((pos 0,$2,Input.Typing.fresh_typaram()), (pos 0,$4,Input.Typing.fresh_typaram()) ) }

texp: 
| name_id { $1 }
| LANGLE texp COMMA ltexp RANGLE { mkpairs ($2::$4)  }
| ENC LPAREN texp COMMA texp RPAREN { app en_op [$3;$5] }
| atexp { $1 }

ltexp:
| texp { [$1] }
| texp COMMA ltexp { $1::$3 }

atexp:
| LPAREN texp RPAREN { $2 }

%%


