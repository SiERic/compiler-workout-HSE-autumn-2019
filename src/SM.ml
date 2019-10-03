open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env config prg = match prg with
  | []      -> config
  | (p::ps) -> match p, config with 
    | BINOP op, (y::x::st, (s, i, o)) -> eval env ((Language.Expr.eval s (Binop (op, Const x, Const y)))::st, (s, i, o)) ps
    | CONST z,  (st, c)               -> eval env (z::st, c) ps
    | READ,     (st, (s, z::i, o))    -> eval env (z::st, (s, i, o)) ps
    | WRITE,    (z::st, (s, i, o))    -> eval env (st, (s, i, o @ [z])) ps
    | ST x,     (z::st, (s, i, o))    -> eval env (st, ((Language.Expr.update x z s), i, o)) ps
    | LD x,     (st, (s, i, o))       -> eval env ((s x)::st, (s, i, o)) ps
    | LABEL l,   config               -> eval env config ps
    | JMP l,    config                -> eval env config (env#labeled l)
    | CJMP (x, l), (z::st, c)         -> if ((x = "z") = (z = 0)) 
                                         then eval env (z::st, c) (env#labeled l)
                                         else eval env (z::st, c) ps

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

let label_generator =
  object
    val mutable x = 0
    method get_label = x <- x + 1; (Printf.sprintf "label%d" x)
  end

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile_expression e = match e with
  | Expr.Const x            -> [CONST x]
  | Expr.Var x              -> [LD x]
  | Expr.Binop (op, e1, e2) -> compile_expression e1 @ compile_expression e2 @ [BINOP op]

let rec compile t = match t with 
  | Stmt.Read x         -> [READ; ST x]
  | Stmt.Write e        -> compile_expression e @ [WRITE]
  | Stmt.Assign (x, e)  -> compile_expression e @ [ST x]
  | Stmt.Seq (s1, s2)   -> compile s1 @ compile s2
  | Stmt.Skip           -> []
  | Stmt.If (e, s1, s2) -> let l_else = label_generator#get_label in
                             let l_quit = label_generator#get_label in             
                                compile_expression e @ [CJMP ("z", l_else)] @ compile s1 @ 
                                [JMP l_quit; LABEL l_else] @ compile s2 @ [LABEL l_quit]
  | Stmt.While (e, s)   -> let l_start = label_generator#get_label in
                             let l_quit = label_generator#get_label in
                                [LABEL l_start] @ compile_expression e @ [CJMP ("z", l_quit)] @ 
                                compile s @ [JMP l_start; LABEL l_quit]
