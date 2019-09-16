open GT
open Syntax    
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let rec eval config prg = match prg with
	| []      -> config
	| (p::ps) -> match p, config with 
	  | BINOP op, (y::x::st, (s, i, o)) -> eval ((Syntax.Expr.eval s (Binop (op, Const x, Const y)))::st, (s, i, o)) ps
	  | CONST z,  (st, c)               -> eval (z::st, c) ps
	  | READ,     (st, (s, z::i, o))    -> eval (z::st, (s, i, o)) ps
	  | WRITE,    (z::st, (s, i, o))    -> eval (st, (s, i, o @ [z])) ps
	  | ST x,     (z::st, (s, i, o))    -> eval (st, ((Syntax.Expr.update x z s), i, o)) ps
	  | LD x,     (st, (s, i, o))       -> eval ((s x)::st, (s, i, o)) ps

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile_expression e = match e with
  | Syntax.Expr.Const x            -> [CONST x]
  | Syntax.Expr.Var x              -> [LD x]
  | Syntax.Expr.Binop (op, e1, e2) -> compile_expression e1 @ compile_expression e2 @ [BINOP op]

let rec compile t = match t with 
  | Syntax.Stmt.Read x        -> [READ; ST x]
  | Syntax.Stmt.Write e       -> compile_expression e @ [WRITE]
  | Syntax.Stmt.Assign (x, e) -> compile_expression e @ [ST x]
  | Syntax.Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
