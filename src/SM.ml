open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
  let rec eval env conf prg = match prg with
  | []      -> conf
  | (p::ps) -> match p, conf with 
    | BINOP op, (cs, y::x::st, c)                 -> eval env (cs, (Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)))::st, c) ps
    | CONST z, (cs, st, c)                        -> eval env (cs, (Value.of_int z)::st, c) ps
    | STRING s, (cs, st, c)                       -> eval env (cs, (Value.of_string s)::st, c) ps
    | SEXP (x, n), (cs, st, c)                    -> let (ps', st') = split n st in 
                                                     eval env (cs, (Value.of_sexp x (List.rev ps'))::st', c) ps
    | LD x, (cs, st, (s, i, o))                   -> eval env (cs, (State.eval s x)::st, (s, i, o)) ps
    | ST x, (cs, z::st, (s, i, o))                -> eval env (cs, st, ((State.update x z s), i, o)) ps
    | STA (a, n), (cs, st, (s, i, o))             -> let (z::args, st') = split (n + 1) st in
                                                     eval env (cs, st', (Stmt.update s a z (List.rev args), i, o)) ps
    | LABEL l, conf                               -> eval env conf ps
    | JMP l, conf                                 -> eval env conf (env#labeled l)
    | CJMP (x, l), (cs, z::st, c)                 -> if ((x = "z") = ((Value.to_int z) = 0)) 
                                                     then eval env (cs, st, c) (env#labeled l)
                                                     else eval env (cs, st, c) ps
    | BEGIN (_, args, locs), (cs, st, (s, i, o))  -> let rec add_val s1 al vl = 
                                                     (match al, vl with
                                                      | (x :: xs), (y :: ys) -> add_val (State.update x y s1) xs ys
                                                      | [], ys               -> (s1, ys)
                                                     ) in
                                                     let s', st' = add_val (State.enter s (args @ locs)) (List.rev args) st in
                                                     eval env (cs, st', (s', i, o)) ps
    | END, (cs, st, (s, i, o))                    -> (match cs with
                                                      | []            -> (cs, st, (s, i, o))
                                                      | (p', s')::cs' -> eval env (cs', st, (State.leave s s', i, o)) p')
    | CALL (f, n, p), (cs, st, (s, i, o))         -> if (env#is_label f) 
                                                     then eval env ((ps, s)::cs, st, (s, i, o)) (env#labeled f) 
                                                     else eval env (env#builtin conf f n p) ps
    | RET _, (cs, st, (s, i, o))                  -> (match cs with
                                                      | []            -> (cs, st, (s, i, o))
                                                      | (p', s')::cs' -> eval env (cs', st, (State.leave s s', i, o)) p')
    | DROP, (cs, z::st', c)                       -> eval env (cs, st', c) ps
    | DUP, (cs, z::st', c)                        -> eval env (cs, z::z::st', c) ps
    | SWAP, (cs, x::y::st', c)                    -> eval env (cs, y::x::st', c) ps
    | TAG t, (cs, z::st', c)                      -> let Value.Sexp (t', _) = z in 
                                                     let tag = if t' = t then 1 else 0 in 
                                                     eval env (cs, (Value.of_int tag)::st', c) ps
    | ENTER vars, (cs, st, (s, i, o))             -> let vals, st' = split (List.length vars) st in
                                                     let s' = List.fold_left2 (fun ast e var -> State.bind var e ast) State.undefined vals vars in 
                                                     eval env (cs, st', (State.push s s' vars, i, o)) ps                                
    | LEAVE, (cs, st, (s, i, o))                  -> eval env (cs, st, (State.drop s, i, o)) ps 

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if (not p) then stack' else let Some r = r in r::stack' in
           (*Printf.printf "Builtin:\n";*)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

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

let rec compile_expr e = 
  match e with
    | Expr.Const n            -> [CONST n]
    | Expr.Dict d             -> List.flatten (List.map (fun (x, y) -> [CONST x; CONST y]) d) @ [SEXP ("_dict", 2 * (List.length d))] 
    | Expr.Array a            -> List.flatten (List.map compile_expr a) @ [CALL (".array", List.length a, true)]
    | Expr.String s           -> [STRING s]
    | Expr.Sexp (x, ps)       -> List.flatten (List.map compile_expr ps) @ [SEXP (x, List.length ps)]
    | Expr.Var x              -> [LD x]
    | Expr.Binop (op, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op]
    | Expr.Elem (a, i)        -> 
       compile_expr a @ compile_expr i @ [CALL (".elem", 2, true)]
    | Expr.Length a           -> compile_expr a @ [CALL (".length", 1, true)]
    | Expr.Call (name, args)  -> List.fold_left (fun s e -> (compile_expr e) @ s) [CALL ("L" ^ name, List.length args, true)] args

let rec check_pattern p l_false inds = 
  match p with 
    | Stmt.Pattern.Wildcard     -> []
    | Stmt.Pattern.Ident x      -> []
    | Stmt.Pattern.Sexp (x, ps) ->
        [DUP] @ List.flatten (List.map (fun x -> [CONST x; CALL (".elem", 2, true)]) inds) @ [DUP; TAG x; CJMP ("z", l_false); DROP] @
        (let comp, _ = List.fold_left (fun (a, ind) p -> (a @ check_pattern p l_false (inds @ [ind]), ind + 1)) ([], 0) ps 
        in comp)

let rec compile_binding p inds = 
  match p with
    | Stmt.Pattern.Wildcard     -> []
    | Stmt.Pattern.Ident x      -> [DUP] @ List.flatten (List.map (fun x -> [CONST x; CALL (".elem", 2, true)]) inds) @ [SWAP]
    | Stmt.Pattern.Sexp (x, ps) -> let comp, _ = List.fold_left (fun (a, ind) p -> (a @ compile_binding p (inds @ [ind]), ind + 1)) ([], 0) ps in 
        comp

let rec compile_stmt s l_end = 
  match s with 
    | Stmt.Assign (x, [], e) -> compile_expr e @ [ST x]
    | Stmt.Assign (x, es, e) -> List.flatten (List.map compile_expr (es @ [e])) @ [STA (x, List.length es)]
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
    | Stmt.Call (name, args) -> List.fold_left (fun s e -> (compile_expr e) @ s) [CALL ("L" ^ name, List.length args, false)] args
    | Stmt.Return e          -> (match e with
                                  | Some e -> compile_expr e @ [RET true]
                                  | None   -> [RET false])
    | Stmt.Case (e, bs)      -> let rec find_branch l_quit bs = 
                                  (match bs with 
                                    | [] -> []
                                    | b::bs' -> let (p, s) = b in 
                                       let l_false = label_generator#get_label in
                                       check_pattern p l_false [] @ compile_binding p [] @ [DROP] @ [ENTER (Stmt.Pattern.vars p)] @ compile_stmt s "" @ [LEAVE; JMP l_quit] @ (match p with Sexp _ -> [LABEL l_false; DROP] | _ -> []) @ find_branch l_quit bs')
                                    in
                                let l_quit = label_generator#get_label in
                                compile_expr e @ find_branch l_quit bs @ [LABEL l_quit]

let rec compile_defs ds = 
  match ds with
    | []      -> []
    | (d::ds) -> let (name, (args, locals, body)) = d 
                 in [LABEL ("L" ^ name)] @ [BEGIN (("L" ^ name), (List.rev args), locals)] @ compile_stmt body "" @ [END] @ compile_defs ds


let rec compile (defs, p) = compile_stmt p "" @ [END] @ compile_defs defs 