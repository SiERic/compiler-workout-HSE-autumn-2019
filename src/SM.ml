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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env config prg = match prg with
  | []      -> config
  | (p::ps) -> match p, config with 
    | BINOP op, (cs, y::x::st, (s, i, o))         -> eval env (cs, (Expr.eval s (Binop (op, Const x, Const y)))::st, (s, i, o)) ps
    | CONST z,  (cs, st, c)                       -> eval env (cs, z::st, c) ps
    | READ,     (cs, st, (s, z::i, o))            -> eval env (cs, z::st, (s, i, o)) ps
    | WRITE,    (cs, z::st, (s, i, o))            -> eval env (cs, st, (s, i, o @ [z])) ps
    | ST x,     (cs, z::st, (s, i, o))            -> eval env (cs, st, ((State.update x z s), i, o)) ps
    | LD x,     (cs, st, (s, i, o))               -> eval env (cs, (State.eval s x)::st, (s, i, o)) ps
    | LABEL l,  config                            -> eval env config ps
    | JMP l,    config                            -> eval env config (env#labeled l)
    | CJMP (x, l), (cs, z::st, c)                 -> if ((x = "z") = (z = 0)) 
                                                     then eval env (cs, z::st, c) (env#labeled l)
                                                     else eval env (cs, z::st, c) ps
    | BEGIN (args, locs), (cs, st, (s, i, o))     -> let rec addVal st1 al vl = 
                                                     (match al, vl with
                                                      | (x :: xs), (y :: ys) -> addVal (State.update x y st1) xs ys
                                                      | [], ys               -> (st1, ys)
                                                     ) in
                                                     let s', st' = addVal (State.push_scope s (args @ locs)) args st in
                                                     eval env (cs, st', (s', i, o)) ps
    | END, (cs, st, (s, i, o))                    -> (match cs with
                                                      | []           -> (cs, st, (s, i, o))
                                                      | (p', s')::cs -> eval env (cs, st, (State.drop_scope s s', i, o)) p') 
    | CALL name, (cs, st, (s, i, o))              -> eval env ((ps, s)::cs, st, (s, i, o)) (env#labeled name) 

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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let label_generator =
  object
    val mutable x = 0
    method get_label = x <- x + 1; (Printf.sprintf "label%d" x)
  end

let rec compile_expr e = match e with
  | Expr.Const x            -> [CONST x]
  | Expr.Var x              -> [LD x]
  | Expr.Binop (op, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op]

let rec compile_stmt t l_end = match t with 
  | Stmt.Read x            -> [READ] @ [ST x]
  | Stmt.Write e           -> compile_expr e @ [WRITE]
  | Stmt.Assign (x, e)     -> compile_expr e @ [ST x]
  | Stmt.Seq (s1, s2)      -> compile_stmt s1 "" @ compile_stmt s2 l_end
  | Stmt.Skip              -> []
  | Stmt.If (e, s1, s2)    -> let l_else = label_generator#get_label in
                              let l_quit = (if l_end = "" then label_generator#get_label else l_end) in             
                                compile_expr e @ [CJMP ("z", l_else)] @ compile_stmt s1 l_quit @ 
                                [JMP l_quit]   @ [LABEL l_else]       @ compile_stmt s2 l_quit @ (if l_end = "" then [LABEL l_quit] else [])
  | Stmt.While (e, s)      -> let l_start = label_generator#get_label in
                              let l_quit  = label_generator#get_label in
                                [LABEL l_start] @ compile_expr e @ [CJMP ("z", l_quit)] @ 
                                compile_stmt s ""  @ [JMP l_start]  @ [LABEL l_quit]
  | Stmt.Call (name, args) -> List.concat (List.map compile_expr args) @ [CALL name]

let rec compile (ds, main) = let rec compile_defs ds = match ds with
                              | []      -> []
                              | (d::ds) -> let (name, (args, locals, body)) = d 
                                           in [LABEL name] @ [BEGIN (args, locals)] @ compile_stmt body "" @ [END] @ compile_defs ds
                             in let l_main = label_generator#get_label
                             in [JMP l_main] @ compile_defs ds @ [LABEL l_main] @ compile_stmt main "" @ [END] 

