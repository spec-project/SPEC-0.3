/***************************************************************************
* SPEC                                                                     *
* Copyright (C) 2011-2017 Alwen Tiu, Ross Horne                            *
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
  let freeid p s = Input.pre_freeid p s   (* RH: Added in attempt to fix free variable bugs. *)   

  let nil_op = constid (pos 0) "nil"
  let cons_op = constid (pos 0) "cons"
  let def_op =  constid (pos 0) "def" 
  let ct_op = constid (pos 0) "ct"
  let var_op = constid (pos 0) "var"
  let zero_op = constid (pos 0) "zero"
  let done_op = constid (pos 0) "done"
  let par_op = constid (pos 0) "par" 
  let plus_op = constid (pos 0) "plus"
  let nu_op = constid (pos 0) "nu" 
  let in_op = constid (pos 0) "inp" 
  let out_op = constid (pos 0) "outp"
  let tau_op = constid (pos 0) "taup"   (* RH: Added tau *)
  let match_op = constid (pos 0) "match" 
  let mismatch_op = constid (pos 0) "mismatch" 
  let case_op = constid (pos 0) "case"
  let let_op = constid (pos 0) "let"
  let bang_op = constid (pos 0) "bang" 
  let pr_op = constid (pos 0) "pr"
  let en_op = constid (pos 0) "en"
  (* Asymmetric Encryption *)
  let aen_op = constid (pos 0) "aen"
  let pub_op = constid (pos 0) "pub"
  (* Blind *)
  let blind_op = constid (pos 0) "blind"
  (* Sign, Hash, Map *)
  let sign_op = constid (pos 0) "sign"
  let hash_op = constid (pos 0) "hs"
  let mac_op  = constid (pos 0) "mac"
  (* CheckSign *)
  let checksign_op = constid (pos 0) "checksign"
  (* Adec, Unblind, Getmsg *)
  let letadec_op = constid (pos 0) "letadec"
  let letunblind_op = constid (pos 0) "letunblind"
  let letgetmsg_op = constid (pos 0) "letgetmsg"
  let stap_out_op = constid (pos 0) "stap_act_out"
  let stap_in_op  = constid (pos 0) "stap_act_in"
  let absurd_op = constid (pos 0) "absurd"

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

  let get_ctsids t =
    let vs = Input.get_freeids t in
    List.filter ( fun x -> String.get x 0 != '?') vs

  let get_glvids t =
    let vs = Input.get_freeids t in
    List.filter (fun x -> String.get x 0 == '?') vs

  let change_ctids t =
    let vs = get_ctsids t in
    let sub = List.map (fun s -> (s,app ct_op [qstring (pos 0) s]) ) vs in
    Input.pre_freeidsubst sub t

  let abstract_ids tm vars =
    let proc = constid (pos 0) "defProc" in 
    let abs  = constid (pos 0) "defAbs" in 
    List.fold_right (fun v t -> app abs [Input.pre_lambda (pos 0) [pos 0, v, Input.Typing.fresh_typaram ()] t]) vars   (* RH: Builds lambda-abstraction in Bedwyr for each v in vars wrapped with defAbs from proc.def. *)
               (app proc [tm])   (* RH: Base case of fold_right building a process before vars are abstracted.*)

  let mkdef a b = 
    let agentname,vars = a in (* RH: Can now ignore vars on this line, since vars are defined by default. Alternatively check all vars are declared as in MWB. *)
    let vars = List.map (fun (x,y,z) -> y) vars in
    let vars = List.concat [
                 vars;
                 List.sort (fun x y -> if x < y then 0 else 1)
                  (List.filter (fun x -> not (List.mem x vars))
                    (get_glvids b))]
    in
    let agent_def = constid (pos 0) "agent_def" in 
    let b = abstract_ids b vars in
    let d = (app agent_def [(qstring (pos 0) agentname); b]) in 
    Spi.Def (agentname,List.length vars,(pos 0,change_ctids d,Input.pre_true (pos 0)))

  let mkquery a b =
    let vars = get_glvids (app par_op [a;b]) in
    let q = app (constid (pos 0) "bisim_def") [nil_op; abstract_ids a vars; abstract_ids b vars] in 
    Spi.Query (pos 0, change_ctids q)

  (* Key cycle query *)
  let kcquery a =
    let vars = get_glvids (app par_op [a]) in
    let q = app (constid (pos 0) "keycycle_def" ) [abstract_ids a vars] in 
    Spi.QueryKeyCycle (pos 0, change_ctids q)

  (* Symbolic trace analysis *)
  let stap_abstract_ids sa vars =
    let stap_action = constid (pos 0) "defStapAct" in 
    let abs  = constid (pos 0) "defStapActAbs" in 
    List.fold_right (fun v t -> app abs [Input.pre_lambda (pos 0) [pos 0, v, Input.Typing.fresh_typaram ()] t]) vars
               (app stap_action [sa])

  let rec remove_duplicate lst lst' =
    match lst' with
    | [] -> lst
    | h::t -> remove_duplicate (List.filter (fun x -> x <> h) lst) t

  let defStapBody n a b p =
    let vars = get_glvids (app par_op [a;b;p]) in
    let vars' = remove_duplicate vars n in
    app (constid (pos 0) "defStapBody" ) [stap_abstract_ids a vars'; stap_abstract_ids b vars'; abstract_ids p vars']

  let defStapBodyAbs a b = 
    let abs_var x t = app (constid (pos 0) "defStapBodyAbs" ) [lambda x t] in 
        List.fold_right abs_var a b

  let stapquery n a b p =
    let n' = List.map (fun (x,y,z) -> y) n in
    let sb = defStapBody n' a b p in
    let sb' = defStapBodyAbs n sb in
    let q = app (constid (pos 0) "stap_def" ) [sb'] in
    Spi.QueryStap (pos 0, change_ctids q)

  let stapqueryshort a b p =
    let vars = get_glvids (app par_op [a;b;p]) in
    let sb = app (constid (pos 0) "defStapBody" ) [stap_abstract_ids a vars; stap_abstract_ids b vars; abstract_ids p vars] in
    let q = app (constid (pos 0) "stap_def" ) [sb] in
    Spi.QueryStap (pos 0, change_ctids q)

%}


%token LPAREN RPAREN LBRAK RBRAK LANGLE RANGLE LBRAC RBRAC SEMICOLON BISIM SIM KEYCYCLE STAP
%token ZERO DONE DOT EQ NEQ COMMA NU PAR PLUS ENC HASH AENC PUB BLIND SIGN VK MAC TAU ABSURD CHECKSIGN ADEC UNBLIND GETMSG
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
| BISIM LPAREN pexp COMMA pexp RPAREN SEMICOLON  { System.update_def (Spi.Process.sim_opt) (Term.lambda 0 (Term.op_false)) ; mkquery $3 $5 }
| SIM LPAREN pexp COMMA pexp RPAREN SEMICOLON  { System.update_def (Spi.Process.sim_opt) (Term.lambda 0 (Term.op_true)) ; mkquery $3 $5 }
| KEYCYCLE LPAREN pexp RPAREN SEMICOLON { kcquery $3 }
| nupref DOT STAP LPAREN saexp COMMA saexp COMMA pexp RPAREN SEMICOLON { stapquery $1 $5 $7 $9 }
| STAP LPAREN saexp COMMA saexp COMMA pexp RPAREN SEMICOLON { stapqueryshort $3 $5 $7 }
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
| DONE { done_op }
| outpref { let a,b = $1 in app out_op [a;b;zero_op] }
| inpref { let a,b = $1 in app in_op [a ; lambda b zero_op] }
| pexp PAR pexp { app par_op [$1;$3] }
| pexp PLUS pexp { app plus_op [$1;$3] }
| outpref DOT pexp { let a,b = $1 in app out_op [a;b;$3] }
| inpref DOT pexp { let a,b = $1 in app in_op [a;lambda b $3] }
| nupref DOT pexp { nuproc $1 $3 }
| LBRAK texp EQ texp RBRAK pexp { app match_op [$2;$4;$6] }
| LBRAK CHECKSIGN LPAREN texp COMMA texp COMMA texp RPAREN RBRAK pexp { app checksign_op [$4;$6;$8;$11] } /* CheckSign */
| LBRAK texp NEQ texp RBRAK pexp { app mismatch_op [$2;$4;$6] }
| cpref IN pexp { let a,(b,c) = $1 in app case_op [a;c;lambda b $3] }
| lpref IN pexp { let t,(v1,v2) = $1 in app let_op [t; lambda v1 (lambda v2 $3)] }
| ladecpref IN pexp { let (a1,a2),b = $1 in app letadec_op [a1;a2; lambda b $3] }		/* Adec, Unblind, Getmsg */
| lunblindpref IN pexp { let (a1,a2),b = $1 in app letunblind_op [a1;a2; lambda b $3] }		/* Adec, Unblind, Getmsg */
| lgetmsgpref IN pexp { let a1,b = $1 in app letgetmsg_op [a1; lambda b $3] }
| BANG pexp { app bang_op [$2] }
| TAU DOT pexp { app tau_op [$3] }
| TAU { app tau_op [zero_op] }
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

/* Adec, Unblind, Getmsg */
ladecpref:
| LET ID EQ adecpat { ($4, (pos 0,$2,Input.Typing.fresh_typaram()) ) }
lunblindpref:
| LET ID EQ unblindpat { ($4, (pos 0,$2,Input.Typing.fresh_typaram()) ) }
lgetmsgpref:
| LET ID EQ getmsgpat { ($4, (pos 0,$2,Input.Typing.fresh_typaram()) ) }

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

/* Adec, Unblind, Getmsg */
adecpat:
| ADEC LPAREN texp COMMA texp RPAREN { ($3, $5) }
unblindpat:
| UNBLIND LPAREN texp COMMA texp RPAREN { ($3, $5) }
getmsgpat:
| GETMSG LPAREN texp RPAREN { $3 }

prpat:
| LANGLE ID COMMA ID RANGLE { ((pos 0,$2,Input.Typing.fresh_typaram()), (pos 0,$4,Input.Typing.fresh_typaram()) ) }

texp: 
| name_id { $1 } 
| LANGLE texp COMMA ltexp RANGLE { mkpairs ($2::$4)  }
| ENC LPAREN texp COMMA texp RPAREN { app en_op [$3;$5] }
| AENC LPAREN texp COMMA texp RPAREN { app aen_op [$3;$5] }		/* Asymmetric Encryption */
| PUB LPAREN texp RPAREN { app pub_op [$3] }				/* Asymmetric Encryption */
| BLIND LPAREN texp COMMA texp RPAREN { app blind_op[$3;$5] }		/* Blind */
| SIGN LPAREN texp COMMA texp RPAREN { app sign_op [$3; $5] }		/* Sign, Hash, Mac */
| HASH LPAREN texp RPAREN { app hash_op [$3] }				/* Sign, Hash, Mac */
| MAC LPAREN texp COMMA texp RPAREN {app mac_op [$3; $5] }		/* Sign, Hash, Mac */
| atexp { $1 }

ltexp:
| texp { [$1] }
| texp COMMA ltexp { $1::$3 }

atexp:
| LPAREN texp RPAREN { $2 }

/* Stap Action */
saexp:
| name_id LANGLE texp RANGLE { app stap_out_op [$1;$3] }
| name_id LPAREN texp RPAREN { app stap_in_op [$1;$3] }
| ABSURD { absurd_op }
%%


