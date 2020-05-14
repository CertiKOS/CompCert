
(* This generated code requires the following version of MenhirLib: *)

let () =
  MenhirLib.StaticVersion.require_20170712

module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | WHILE
    | VOLATILE
    | VOID
    | VAR
    | TILDEL
    | TILDE
    | TAILCALL
    | SWITCHL
    | SWITCH
    | STRINGLIT of (
# 368 "backend/CMparser.mly"
       (string)
# 25 "backend/CMparser.ml"
  )
    | STARS
    | STARL
    | STARF
    | STAR
    | STACK
    | SLASHU
    | SLASHS
    | SLASHLU
    | SLASHL
    | SLASHF
    | SLASH
    | SINGLEOFINT
    | SINGLE
    | SEMICOLON
    | RUNTIME
    | RPAREN
    | RETURN
    | READONLY
    | RBRACKET
    | RBRACERBRACE
    | RBRACE
    | PLUSS
    | PLUSL
    | PLUSF
    | PLUS
    | PERCENTU
    | PERCENTLU
    | PERCENTL
    | PERCENT
    | MINUSS
    | MINUSL
    | MINUSGREATER
    | MINUSF
    | MINUS
    | MATCH
    | LPAREN
    | LOOP
    | LONGUOFFLOAT
    | LONGOFINTU
    | LONGOFINT
    | LONGOFFLOAT
    | LONGLIT of (
# 326 "backend/CMparser.mly"
       (int64)
# 71 "backend/CMparser.ml"
  )
    | LONG
    | LESSU
    | LESSLU
    | LESSLESSL
    | LESSLESS
    | LESSL
    | LESSF
    | LESSEQUALU
    | LESSEQUALLU
    | LESSEQUALL
    | LESSEQUALF
    | LESSEQUAL
    | LESS
    | LBRACKET
    | LBRACELBRACE
    | LBRACE
    | INTUOFFLOAT
    | INTOFLONG
    | INTOFFLOAT
    | INTLIT of (
# 306 "backend/CMparser.mly"
       (int32)
# 95 "backend/CMparser.ml"
  )
    | INT8U
    | INT8S
    | INT8
    | INT64
    | INT32
    | INT16U
    | INT16S
    | INT16
    | INT
    | IF
    | IDENT of (
# 295 "backend/CMparser.mly"
       (string)
# 110 "backend/CMparser.ml"
  )
    | GREATERU
    | GREATERLU
    | GREATERL
    | GREATERGREATERU
    | GREATERGREATERLU
    | GREATERGREATERL
    | GREATERGREATER
    | GREATERF
    | GREATEREQUALU
    | GREATEREQUALLU
    | GREATEREQUALL
    | GREATEREQUALF
    | GREATEREQUAL
    | GREATER
    | GOTO
    | FLOATOFLONGU
    | FLOATOFLONG
    | FLOATOFINTU
    | FLOATOFINT
    | FLOATLIT of (
# 275 "backend/CMparser.mly"
       (float)
# 134 "backend/CMparser.ml"
  )
    | FLOAT64
    | FLOAT32
    | FLOAT
    | EXTERN
    | EXIT
    | EQUALEQUALU
    | EQUALEQUALLU
    | EQUALEQUALL
    | EQUALEQUALF
    | EQUALEQUAL
    | EQUAL
    | EOF
    | ELSE
    | DEFAULT
    | COMMA
    | COLON
    | CASE
    | CARETL
    | CARET
    | BUILTIN
    | BARL
    | BAR
    | BANGEQUALU
    | BANGEQUALLU
    | BANGEQUALL
    | BANGEQUALF
    | BANGEQUAL
    | BANG
    | AMPERSANDL
    | AMPERSAND
    | ABSF
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

# 19 "backend/CMparser.mly"
  
open Datatypes
open Camlcoq
open BinNums
open Integers
open AST
open Cminor

(** Parsing external functions *)

type ef_token =
  | EFT_tok of string
  | EFT_int of int32
  | EFT_string of string
  | EFT_chunk of memory_chunk

let mkef sg toks =
  match toks with
  | [EFT_tok "extern"; EFT_string s] ->
      EF_external(coqstring_of_camlstring s, sg)
  | [EFT_tok "builtin"; EFT_string s] ->
      EF_builtin(coqstring_of_camlstring s, sg)
  | [EFT_tok "runtime"; EFT_string s] ->
      EF_runtime(coqstring_of_camlstring s, sg)
  | [EFT_tok "volatile"; EFT_tok "load"; EFT_chunk c] ->
      EF_vload c
  | [EFT_tok "volatile"; EFT_tok "store"; EFT_chunk c] ->
      EF_vstore c
  | [EFT_tok "malloc"] ->
      EF_malloc
  (* | [EFT_tok "free"] -> *)
  (*     EF_free *)
  | [EFT_tok "memcpy"; EFT_tok "size"; EFT_int sz; EFT_tok "align"; EFT_int al] ->
      EF_memcpy(Z.of_sint32 sz, Z.of_sint32 al)
  | [EFT_tok "annot"; EFT_string txt] ->
      EF_annot(coqstring_of_camlstring txt, sg.sig_args)
  | [EFT_tok "annot_val"; EFT_string txt] ->
      if sg.sig_args = [] then raise Parsing.Parse_error;
      EF_annot_val(coqstring_of_camlstring txt, List.hd sg.sig_args)
  | [EFT_tok "inline_asm"; EFT_string txt] ->
      EF_inline_asm(coqstring_of_camlstring txt, sg, [])
  | _ ->
      raise Parsing.Parse_error

(** Naming function calls in expressions *)

type rexpr =
  | Rvar of ident
  | Rconst of constant
  | Runop of unary_operation * rexpr
  | Rbinop of binary_operation * rexpr * rexpr
  | Rload of memory_chunk * rexpr
  | Rcall of signature * rexpr * rexpr list
  | Rbuiltin of signature * ef_token list * rexpr list

let temp_counter = ref 0

let temporaries = ref []

let mktemp () =
  incr temp_counter;
  let n = Printf.sprintf "__t%d" !temp_counter in
  let id = intern_string n in
  temporaries := id :: !temporaries;
  id

let convert_accu = ref []

let rec convert_rexpr = function
  | Rvar id -> Evar id
  | Rconst c -> Econst c
  | Runop(op, e1) -> Eunop(op, convert_rexpr e1)
  | Rbinop(op, e1, e2) ->
      let c1 = convert_rexpr e1 in
      let c2 = convert_rexpr e2 in
      Ebinop(op, c1, c2)
  | Rload(chunk, e1) -> Eload(chunk, convert_rexpr e1)
  | Rcall(sg, e1, el) ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      let t = mktemp() in
      convert_accu := Scall(Some t, sg, c1, cl) :: !convert_accu;
      Evar t
  | Rbuiltin(sg, pef, el) ->
      let ef = mkef sg pef in
      let cl = convert_rexpr_list el in
      let t = mktemp() in
      convert_accu := Sbuiltin(Some t, ef, cl) :: !convert_accu;
      Evar t

and convert_rexpr_list = function
  | [] -> []
  | e1 :: el ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      c1 :: cl

let rec prepend_seq stmts last =
  match stmts with
  | [] -> last
  | s1 :: sl -> prepend_seq sl (Sseq(s1, last))

let mkeval e =
  convert_accu := [];
  match e with
  | Rcall(sg, e1, el) ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Scall(None, sg, c1, cl))
  | Rbuiltin(sg, pef, el) ->
      let ef = mkef sg pef in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Sbuiltin(None, ef, cl))
  | _ ->
      ignore (convert_rexpr e);
      prepend_seq !convert_accu Sskip

let mkassign id e =
  convert_accu := [];
  match e with
  | Rcall(sg, e1, el) ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Scall(Some id, sg, c1, cl))
  | Rbuiltin(sg, pef, el) ->
      let ef = mkef sg pef in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Sbuiltin(Some id, ef, cl))
  | _ ->
      let c = convert_rexpr e in
      prepend_seq !convert_accu (Sassign(id, c))

let mkstore chunk e1 e2 =
  convert_accu := [];
  let c1 = convert_rexpr e1 in
  let c2 = convert_rexpr e2 in
  prepend_seq !convert_accu (Sstore(chunk, c1, c2))

let mkifthenelse e s1 s2 =
  convert_accu := [];
  let c = convert_rexpr e in
  prepend_seq !convert_accu (Sifthenelse(c, s1, s2))

let mkreturn_some e =
  convert_accu := [];
  let c = convert_rexpr e in
  prepend_seq !convert_accu (Sreturn (Some c))

let mktailcall sg e1 el =
  convert_accu := [];
  let c1 = convert_rexpr e1 in
  let cl = convert_rexpr_list el in
  prepend_seq !convert_accu (Stailcall(sg, c1, cl))

let mkwhile expr body =
  Sblock (Sloop (mkifthenelse expr body (Sexit O)))

(** Other constructors *)

let intconst n =
  Rconst(Ointconst(coqint_of_camlint n))

let longconst n =
  Rconst(Olongconst(coqint_of_camlint64 n))

let exitnum n = Nat.of_int32 n

let mkswitch islong convert expr (cases, dfl) =
  convert_accu := [];
  let c = convert_rexpr expr in
  let rec mktable = function
  | [] -> []
  | (key, exit) :: rem ->
      (convert key, exitnum exit) :: mktable rem in
  prepend_seq !convert_accu (Sswitch(islong, c, mktable cases, exitnum dfl))

(***
   match (a) { case 0: s0; case 1: s1; case 2: s2; }  --->

   block {
   block {
   block {
   block {
     switch(a) { case 0: exit 0; case 1: exit 1; default: exit 2; }
   }; s0; exit 2;
   }; s1; exit 1;
   }; s2;
   }

   Note that matches are assumed to be exhaustive
***)

let mkmatch_aux expr cases =
  let ncases = List.length cases in
  let rec mktable n = function
    | [] -> assert false
    | [key, action] -> []
    | (key, action) :: rem ->
        (coqint_of_camlint key, Nat.of_int n)
        :: mktable (n + 1) rem in
  let sw =
    Sswitch(false, expr, mktable 0 cases, Nat.of_int (ncases - 1)) in
  let rec mkblocks body n = function
    | [] -> assert false
    | [key, action] ->
        Sblock(Sseq(body, action))
    | (key, action) :: rem ->
        mkblocks
          (Sblock(Sseq(body, Sseq(action, Sexit (Nat.of_int n)))))
          (n - 1)
          rem in
  mkblocks (Sblock sw) (ncases - 1) cases

let mkmatch expr cases =
  convert_accu := [];
  let c = convert_rexpr expr in
  let s =
    match cases with
    | [] -> Sskip (* ??? *)
    | [key, action] -> action
    | _ -> mkmatch_aux c cases in
  prepend_seq !convert_accu s


# 400 "backend/CMparser.ml"

module Tables = struct
  
  include MenhirBasics
  
  let token2terminal : token -> int =
    fun _tok ->
      match _tok with
      | ABSF ->
          134
      | AMPERSAND ->
          133
      | AMPERSANDL ->
          132
      | BANG ->
          131
      | BANGEQUAL ->
          130
      | BANGEQUALF ->
          129
      | BANGEQUALL ->
          128
      | BANGEQUALLU ->
          127
      | BANGEQUALU ->
          126
      | BAR ->
          125
      | BARL ->
          124
      | BUILTIN ->
          123
      | CARET ->
          122
      | CARETL ->
          121
      | CASE ->
          120
      | COLON ->
          119
      | COMMA ->
          118
      | DEFAULT ->
          117
      | ELSE ->
          116
      | EOF ->
          115
      | EQUAL ->
          114
      | EQUALEQUAL ->
          113
      | EQUALEQUALF ->
          112
      | EQUALEQUALL ->
          111
      | EQUALEQUALLU ->
          110
      | EQUALEQUALU ->
          109
      | EXIT ->
          108
      | EXTERN ->
          107
      | FLOAT ->
          106
      | FLOAT32 ->
          105
      | FLOAT64 ->
          104
      | FLOATLIT _ ->
          103
      | FLOATOFINT ->
          102
      | FLOATOFINTU ->
          101
      | FLOATOFLONG ->
          100
      | FLOATOFLONGU ->
          99
      | GOTO ->
          98
      | GREATER ->
          97
      | GREATEREQUAL ->
          96
      | GREATEREQUALF ->
          95
      | GREATEREQUALL ->
          94
      | GREATEREQUALLU ->
          93
      | GREATEREQUALU ->
          92
      | GREATERF ->
          91
      | GREATERGREATER ->
          90
      | GREATERGREATERL ->
          89
      | GREATERGREATERLU ->
          88
      | GREATERGREATERU ->
          87
      | GREATERL ->
          86
      | GREATERLU ->
          85
      | GREATERU ->
          84
      | IDENT _ ->
          83
      | IF ->
          82
      | INT ->
          81
      | INT16 ->
          80
      | INT16S ->
          79
      | INT16U ->
          78
      | INT32 ->
          77
      | INT64 ->
          76
      | INT8 ->
          75
      | INT8S ->
          74
      | INT8U ->
          73
      | INTLIT _ ->
          72
      | INTOFFLOAT ->
          71
      | INTOFLONG ->
          70
      | INTUOFFLOAT ->
          69
      | LBRACE ->
          68
      | LBRACELBRACE ->
          67
      | LBRACKET ->
          66
      | LESS ->
          65
      | LESSEQUAL ->
          64
      | LESSEQUALF ->
          63
      | LESSEQUALL ->
          62
      | LESSEQUALLU ->
          61
      | LESSEQUALU ->
          60
      | LESSF ->
          59
      | LESSL ->
          58
      | LESSLESS ->
          57
      | LESSLESSL ->
          56
      | LESSLU ->
          55
      | LESSU ->
          54
      | LONG ->
          53
      | LONGLIT _ ->
          52
      | LONGOFFLOAT ->
          51
      | LONGOFINT ->
          50
      | LONGOFINTU ->
          49
      | LONGUOFFLOAT ->
          48
      | LOOP ->
          47
      | LPAREN ->
          46
      | MATCH ->
          45
      | MINUS ->
          44
      | MINUSF ->
          43
      | MINUSGREATER ->
          42
      | MINUSL ->
          41
      | MINUSS ->
          40
      | PERCENT ->
          39
      | PERCENTL ->
          38
      | PERCENTLU ->
          37
      | PERCENTU ->
          36
      | PLUS ->
          35
      | PLUSF ->
          34
      | PLUSL ->
          33
      | PLUSS ->
          32
      | RBRACE ->
          31
      | RBRACERBRACE ->
          30
      | RBRACKET ->
          29
      | READONLY ->
          28
      | RETURN ->
          27
      | RPAREN ->
          26
      | RUNTIME ->
          25
      | SEMICOLON ->
          24
      | SINGLE ->
          23
      | SINGLEOFINT ->
          22
      | SLASH ->
          21
      | SLASHF ->
          20
      | SLASHL ->
          19
      | SLASHLU ->
          18
      | SLASHS ->
          17
      | SLASHU ->
          16
      | STACK ->
          15
      | STAR ->
          14
      | STARF ->
          13
      | STARL ->
          12
      | STARS ->
          11
      | STRINGLIT _ ->
          10
      | SWITCH ->
          9
      | SWITCHL ->
          8
      | TAILCALL ->
          7
      | TILDE ->
          6
      | TILDEL ->
          5
      | VAR ->
          4
      | VOID ->
          3
      | VOLATILE ->
          2
      | WHILE ->
          1
  
  and error_terminal =
    0
  
  and token2value : token -> Obj.t =
    fun _tok ->
      match _tok with
      | ABSF ->
          Obj.repr ()
      | AMPERSAND ->
          Obj.repr ()
      | AMPERSANDL ->
          Obj.repr ()
      | BANG ->
          Obj.repr ()
      | BANGEQUAL ->
          Obj.repr ()
      | BANGEQUALF ->
          Obj.repr ()
      | BANGEQUALL ->
          Obj.repr ()
      | BANGEQUALLU ->
          Obj.repr ()
      | BANGEQUALU ->
          Obj.repr ()
      | BAR ->
          Obj.repr ()
      | BARL ->
          Obj.repr ()
      | BUILTIN ->
          Obj.repr ()
      | CARET ->
          Obj.repr ()
      | CARETL ->
          Obj.repr ()
      | CASE ->
          Obj.repr ()
      | COLON ->
          Obj.repr ()
      | COMMA ->
          Obj.repr ()
      | DEFAULT ->
          Obj.repr ()
      | ELSE ->
          Obj.repr ()
      | EOF ->
          Obj.repr ()
      | EQUAL ->
          Obj.repr ()
      | EQUALEQUAL ->
          Obj.repr ()
      | EQUALEQUALF ->
          Obj.repr ()
      | EQUALEQUALL ->
          Obj.repr ()
      | EQUALEQUALLU ->
          Obj.repr ()
      | EQUALEQUALU ->
          Obj.repr ()
      | EXIT ->
          Obj.repr ()
      | EXTERN ->
          Obj.repr ()
      | FLOAT ->
          Obj.repr ()
      | FLOAT32 ->
          Obj.repr ()
      | FLOAT64 ->
          Obj.repr ()
      | FLOATLIT _v ->
          Obj.repr _v
      | FLOATOFINT ->
          Obj.repr ()
      | FLOATOFINTU ->
          Obj.repr ()
      | FLOATOFLONG ->
          Obj.repr ()
      | FLOATOFLONGU ->
          Obj.repr ()
      | GOTO ->
          Obj.repr ()
      | GREATER ->
          Obj.repr ()
      | GREATEREQUAL ->
          Obj.repr ()
      | GREATEREQUALF ->
          Obj.repr ()
      | GREATEREQUALL ->
          Obj.repr ()
      | GREATEREQUALLU ->
          Obj.repr ()
      | GREATEREQUALU ->
          Obj.repr ()
      | GREATERF ->
          Obj.repr ()
      | GREATERGREATER ->
          Obj.repr ()
      | GREATERGREATERL ->
          Obj.repr ()
      | GREATERGREATERLU ->
          Obj.repr ()
      | GREATERGREATERU ->
          Obj.repr ()
      | GREATERL ->
          Obj.repr ()
      | GREATERLU ->
          Obj.repr ()
      | GREATERU ->
          Obj.repr ()
      | IDENT _v ->
          Obj.repr _v
      | IF ->
          Obj.repr ()
      | INT ->
          Obj.repr ()
      | INT16 ->
          Obj.repr ()
      | INT16S ->
          Obj.repr ()
      | INT16U ->
          Obj.repr ()
      | INT32 ->
          Obj.repr ()
      | INT64 ->
          Obj.repr ()
      | INT8 ->
          Obj.repr ()
      | INT8S ->
          Obj.repr ()
      | INT8U ->
          Obj.repr ()
      | INTLIT _v ->
          Obj.repr _v
      | INTOFFLOAT ->
          Obj.repr ()
      | INTOFLONG ->
          Obj.repr ()
      | INTUOFFLOAT ->
          Obj.repr ()
      | LBRACE ->
          Obj.repr ()
      | LBRACELBRACE ->
          Obj.repr ()
      | LBRACKET ->
          Obj.repr ()
      | LESS ->
          Obj.repr ()
      | LESSEQUAL ->
          Obj.repr ()
      | LESSEQUALF ->
          Obj.repr ()
      | LESSEQUALL ->
          Obj.repr ()
      | LESSEQUALLU ->
          Obj.repr ()
      | LESSEQUALU ->
          Obj.repr ()
      | LESSF ->
          Obj.repr ()
      | LESSL ->
          Obj.repr ()
      | LESSLESS ->
          Obj.repr ()
      | LESSLESSL ->
          Obj.repr ()
      | LESSLU ->
          Obj.repr ()
      | LESSU ->
          Obj.repr ()
      | LONG ->
          Obj.repr ()
      | LONGLIT _v ->
          Obj.repr _v
      | LONGOFFLOAT ->
          Obj.repr ()
      | LONGOFINT ->
          Obj.repr ()
      | LONGOFINTU ->
          Obj.repr ()
      | LONGUOFFLOAT ->
          Obj.repr ()
      | LOOP ->
          Obj.repr ()
      | LPAREN ->
          Obj.repr ()
      | MATCH ->
          Obj.repr ()
      | MINUS ->
          Obj.repr ()
      | MINUSF ->
          Obj.repr ()
      | MINUSGREATER ->
          Obj.repr ()
      | MINUSL ->
          Obj.repr ()
      | MINUSS ->
          Obj.repr ()
      | PERCENT ->
          Obj.repr ()
      | PERCENTL ->
          Obj.repr ()
      | PERCENTLU ->
          Obj.repr ()
      | PERCENTU ->
          Obj.repr ()
      | PLUS ->
          Obj.repr ()
      | PLUSF ->
          Obj.repr ()
      | PLUSL ->
          Obj.repr ()
      | PLUSS ->
          Obj.repr ()
      | RBRACE ->
          Obj.repr ()
      | RBRACERBRACE ->
          Obj.repr ()
      | RBRACKET ->
          Obj.repr ()
      | READONLY ->
          Obj.repr ()
      | RETURN ->
          Obj.repr ()
      | RPAREN ->
          Obj.repr ()
      | RUNTIME ->
          Obj.repr ()
      | SEMICOLON ->
          Obj.repr ()
      | SINGLE ->
          Obj.repr ()
      | SINGLEOFINT ->
          Obj.repr ()
      | SLASH ->
          Obj.repr ()
      | SLASHF ->
          Obj.repr ()
      | SLASHL ->
          Obj.repr ()
      | SLASHLU ->
          Obj.repr ()
      | SLASHS ->
          Obj.repr ()
      | SLASHU ->
          Obj.repr ()
      | STACK ->
          Obj.repr ()
      | STAR ->
          Obj.repr ()
      | STARF ->
          Obj.repr ()
      | STARL ->
          Obj.repr ()
      | STARS ->
          Obj.repr ()
      | STRINGLIT _v ->
          Obj.repr _v
      | SWITCH ->
          Obj.repr ()
      | SWITCHL ->
          Obj.repr ()
      | TAILCALL ->
          Obj.repr ()
      | TILDE ->
          Obj.repr ()
      | TILDEL ->
          Obj.repr ()
      | VAR ->
          Obj.repr ()
      | VOID ->
          Obj.repr ()
      | VOLATILE ->
          Obj.repr ()
      | WHILE ->
          Obj.repr ()
  
  and default_reduction =
