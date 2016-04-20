/****************************************************************************
 * Bedwyr prover                                                            *
 * Copyright (C) 2006-2012 Baelde, Tiu, Ziegler, Heath                      *
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

%}

/* Punctuation */
%token COLON DEFEQ SEMICOLON COMMA DOT LPAREN RPAREN

/* Bedwyr meta-commands */
%token EXIT HELP INCLUDE RESET RELOAD SESSION
%token DEBUG TIME EQUIVARIANT FREEZING SATURATION
%token ENV TYPEOF SHOW_TABLE CLEAR_TABLES CLEAR_TABLE SAVE_TABLE
%token ASSERT ASSERT_NOT ASSERT_RAISE
/* Bedwyr keywords */
%token KKIND TTYPE DEFINE THEOREM
%token INDUCTIVE COINDUCTIVE BY
%token UNDERSCORE
/* Bedwyr primitives */
%token TYPE PROP STRING NAT FORALL EXISTS NABLA TRUE FALSE
%token RARROW EQ AND OR BSLASH

/* Abella keywords, including tactics, apart from "exists" */
%token CLOSE QED QUERY IMPORT SPECIFICATION SSPLIT SET SHOW QUIT
%token TO WITH ON AS KEEP
%token IND_T COIND_T INTROS_T CASE_T SEARCH_T APPLY_T BACKCHAIN_T UNFOLD_T
%token ASSERT_T SPLIT_T SPLITSTAR_T LEFT_T RIGHT_T PERMUTE_T INST_T CUT_T
%token MONOTONE_T UNDO_T SKIP_T ABORT_T CLEAR_T ABBREV_T UNABBREV_T
/* Abella primitives */
%token TURN LBRACK RBRACK

/* Teyjus keywords */
%token SIG MODULE ACCUMSIG ACCUM END KIND
/* Teyjus primitives */
%token CLAUSEEQ IMP CONS

%token <int> NUM
%token <string> UPPER_ID LOWER_ID INFIX_ID INTERN_ID
%token <(Input.Typing.pos * string)> QSTRING
%token EOF

/* Lower */

%nonassoc LPAREN
%nonassoc RPAREN

%nonassoc COMMA
%right RARROW
%left OR
%left AND

%nonassoc BSLASH
%nonassoc EQ

%right INFIX_ID

/* Higher */

%start input_def input_query
%type <Input.input> input_def
%type <Input.input> input_query

%%

/* commands */

input_def:
  | top_command                         { $1 }
  | meta_command                        { $1 }

input_query:
  | formula DOT                         { Input.Query $1 }
  | meta_command                        { $1 }

top_command:
  | KKIND type_clist ki DOT             { Input.KKind ($2,$3) }
  | TTYPE const_clist ty DOT            { Input.TType ($2,$3) }
  | DEFINE decls BY defs DOT            { Input.Def ($2,$4) }
  | DEFINE decls DOT                    { Input.Def ($2,[]) }
  | THEOREM theorem DOT                 { Input.Theorem $2 }
  | CLOSE                               { failwith "Abella command only" }
  | QED                                 { failwith "Abella command only" }
  | QUERY                               { failwith "Abella command only" }
  | IMPORT                              { failwith "Abella command only" }
  | SPECIFICATION                       { failwith "Abella command only" }
  | SSPLIT                              { failwith "Abella command only" }

meta_command:
  | SET                                 { failwith "Abella command only" }
  | SHOW                                { failwith "Abella command only" }
  | QUIT                                { failwith "Abella command only" }
  | EXIT DOT                            { Input.Command (Input.Exit) }
  | HELP DOT                            { Input.Command (Input.Help) }
  | INCLUDE string_args DOT             { Input.Command (Input.Include $2) }
  | RESET DOT                           { Input.Command (Input.Reset) }
  | RELOAD DOT                          { Input.Command (Input.Reload) }
  | SESSION string_args DOT             { Input.Command (Input.Session $2) }
  | DEBUG opt_bool DOT                  { Input.Command (Input.Debug $2) }
  | TIME opt_bool DOT                   { Input.Command (Input.Time $2) }
  | EQUIVARIANT opt_bool DOT            { Input.Command (Input.Equivariant $2) }
  | FREEZING opt_nat DOT                { Input.Command (Input.Freezing $2) }
  | SATURATION opt_nat DOT              { Input.Command (Input.Saturation $2) }
  | ENV DOT                             { Input.Command (Input.Env) }
  | TYPEOF formula DOT                  { Input.Command (Input.Type_of $2) }
  | SHOW_TABLE lower_id DOT             { Input.Command (Input.Show_table (pos 2,$2)) }
  | CLEAR_TABLES DOT                    { Input.Command (Input.Clear_tables) }
  | CLEAR_TABLE lower_id DOT            { Input.Command (Input.Clear_table (pos 2,$2)) }
  | SAVE_TABLE lower_id QSTRING DOT     { let _,s = $3 in
                                          Input.Command (Input.Save_table (pos 2,$2,s)) }
  | ASSERT formula DOT                  { Input.Command (Input.Assert $2) }
  | ASSERT_NOT formula DOT              { Input.Command (Input.Assert_not $2) }
  | ASSERT_RAISE formula DOT            { Input.Command (Input.Assert_raise $2) }
  | EOF                                 { raise End_of_file }

/* kinds, types */

type_clist:
  | lower_id                            { [pos 1,$1] }
  | lower_id COMMA type_clist           { (pos 1,$1)::$3 }

ki:
  | TYPE RARROW ki                      { Input.Typing.ki_arrow [Input.Typing.ktype] $3 }
  | TYPE                                { Input.Typing.ktype }
  | LPAREN ki RPAREN                    { $2 }

const_clist:
  | const_id                            { [pos 1,$1] }
  | const_id COMMA const_clist          { (pos 1,$1)::$3 }

ty_list:
  | ty_atom                             { [$1] }
  | ty_atom ty_list                     { $1 :: $2 }

ty_atom: 
  | lower_id                            { Input.Typing.tconst $1 }
  | lower_id ty_list                    { Input.Typing.tfunc $1 $2 }
  | PROP                                { Input.Typing.tprop }
  | STRING                              { Input.Typing.tstring }
  | NAT                                 { Input.Typing.tnat }
  | UNDERSCORE                          { Input.Typing.fresh_typaram () }
  | UPPER_ID				{ Input.Typing.get_typaram $1 }
  | LPAREN ty RPAREN                    { $2 }

ty:
  | ty_atom                             { $1 }
  | ty RARROW ty                        { Input.Typing.ty_arrow [$1] $3 }



/* definitions */

decls:
  | decl                                { [$1] }
  | decl COMMA decls                    { $1::$3 }

decl:
  | flavour apred_id                    { let p,name,ty = $2 in ($1,p,name,ty) }

flavour:
  |                                     { Input.Normal      }
  | INDUCTIVE                           { Input.Inductive   }
  | COINDUCTIVE                         { Input.CoInductive }

defs:
  | def                                 { [$1] }
  | def SEMICOLON defs                  { $1::$3 }

def:
  | formula                             { pos 0,$1,Input.pre_true (pos 0) }
  | formula DEFEQ formula               { pos 0,$1,$3 }

theorem:
  | lower_id COLON formula              { pos 1,$1,$3 }

term_list:
  | term_atom                           { $1,[] }
  | term_abs                            { $1,[] }
  | term_atom term_list                 { let t,l = $2 in $1,t::l }

term_atom:
  | TRUE                                { Input.pre_true (pos 0) }
  | FALSE                               { Input.pre_false (pos 0) }
  | LPAREN formula RPAREN               { Input.change_pos (pos 1) $2 (pos 3) }
  | LPAREN term RPAREN                  { $2 }
  | LPAREN INFIX_ID RPAREN              { Input.pre_predconstid (pos 0) $2 }
  | token_id                            { $1 }
  | QSTRING                             { let p,s = $1 in
                                          Input.pre_qstring p s }
  | NUM                                 { Input.pre_nat (pos 1) $1 }

term_abs:
  | abound_id BSLASH term               { Input.pre_lambda (pos 0) [$1] $3 }

term:
  | term_list %prec INFIX_ID            { let t,l = $1 in
                                          Input.pre_app (pos 1) t l }
  | term INFIX_ID term                  { Input.pre_app
                                            (pos 0)
                                            (Input.pre_predconstid (pos 2) $2)
                                            [$1; $3] }

formula:
  | term EQ term                        { Input.pre_eq (pos 0) $1 $3 }
  | formula AND formula                 { Input.pre_and (pos 0) $1 $3 }
  | formula OR formula                  { Input.pre_or (pos 0) $1 $3 }
  | formula RARROW formula              { Input.pre_arrow (pos 0) $1 $3 }
  | binder pabound_list COMMA formula   { Input.pre_binder (pos 0) $1 $2 $4 }
  | term %prec LPAREN                   { $1 }

binder:
  | FORALL                              { Term.Forall }
  | EXISTS                              { Term.Exists }
  | NABLA                               { Term.Nabla }

pabound_list:
  | pabound_id                          { [$1] }
  | pabound_id pabound_list             { $1::$2 }

/* ids */

/* base id types */
upper_id:
  | UPPER_ID                            { $1 }
  | UNDERSCORE                          { "_" }

lower_id:
  | LOWER_ID                            { $1 }
  | IND_T                               { "induction" }
  | COIND_T                             { "coinduction" }
  | INTROS_T                            { "intros" }
  | CASE_T                              { "case" }
  | SEARCH_T                            { "search" }
  | APPLY_T                             { "apply" }
  | BACKCHAIN_T                         { "backchain" }
  | UNFOLD_T                            { "unfold" }
  | ASSERT_T                            { "assert" }
  | SPLIT_T                             { "split" }
  | LEFT_T                              { "left" }
  | RIGHT_T                             { "right" }
  | PERMUTE_T                           { "permute" }
  | INST_T                              { "inst" }
  | CUT_T                               { "cut" }
  | MONOTONE_T                          { "monotone" }
  | UNDO_T                              { "undo" }
  | SKIP_T                              { "skip" }
  | ABORT_T                             { "abort" }
  | CLEAR_T                             { "clear" }
  | ABBREV_T                            { "abbrev" }
  | UNABBREV_T                          { "unabbrev" }

/* shortcuts for other id types */
bound_id:
  | upper_id                            { $1 }
  | lower_id                            { $1 }

const_id:
  | lower_id                            { $1 }
  | INFIX_ID                            { $1 }

any_id:
  | upper_id                            { $1 }
  | lower_id                            { $1 }
  | INFIX_ID                            { $1 }
  | INTERN_ID                           { $1 }

/* annotated id types */
apred_id:
  | lower_id                            { pos 1,$1,Input.Typing.fresh_typaram () }
  | lower_id COLON ty                   { pos 1,$1,$3 }

abound_id:
  | bound_id                            { pos 1,$1,Input.Typing.fresh_typaram () }
  | bound_id COLON ty                   { pos 1,$1,$3 }

pabound_id:
  | bound_id                            { pos 1,$1,Input.Typing.fresh_typaram () }
  | LPAREN bound_id COLON ty RPAREN     { pos 2,$2,$4 }

/* predicate or constant in a term */
token_id:
  | upper_id                            { Input.pre_freeid (pos 1) $1 }
  | lower_id                            { Input.pre_predconstid (pos 1) $1 }
  | INTERN_ID                           { Input.pre_internid (pos 1) $1 }

/* misc (commands) */

string_args:
  |                                     { [] }
  | QSTRING string_args                 { let _,s = $1 in
                                          s::$2 }

opt_bool:
  |                                     { None }
  | any_id                              { Some $1 }
  | ON                                  { Some "on" }
  | TRUE                                { Some "true" }
  | FALSE                               { Some "false" }

opt_nat:
  |                                     { -1 }
  | NUM                                 { $1 }

%%
