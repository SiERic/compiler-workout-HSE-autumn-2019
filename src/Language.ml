(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Ostap.Combinators

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    let int_to_bool x = x != 0

    let bool_to_int x = if x then 1 else 0

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
    !(Ostap.Util.expr 
             (fun x -> x)
       (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
    `Lefta, ["!!"];
    `Lefta, ["&&"];
    `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
    `Lefta, ["+" ; "-"];
    `Lefta, ["*" ; "/"; "%"];
              |] 
       )
       primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and semantics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env config t = match t, config with
      | Read x, (s, z::i, o)       -> (State.update x z s, i, o)
      | Write e, (s, i, o)         -> (s, i, o @ [Expr.eval s e])
      | Assign (x, e), (s, i, o)   -> (State.update x (Expr.eval s e) s, i, o)
      | Seq (s1, s2), (s, i, o)    -> eval env (eval env (s, i, o) s1) s2
      | Skip, (s, i, o)            -> (s, i, o)
      | If (e, s1, s2), (s, i, o)  -> if (Expr.int_to_bool (Expr.eval s e) == true)
                                      then eval env (s, i, o) s1
                                      else eval env (s, i, o) s2
      | While (e, st), (s, i, o)   -> if (Expr.int_to_bool (Expr.eval s e) == true)
                                      then eval env (s, i, o) (Seq (st, While (e, st)))
                                      else eval env (s, i, o) Skip
      | Call (p, exprs), (s, i, o) -> let args_values = List.map (Expr.eval s) exprs
                                      in let (args, locals, body) = env#definition p
                                      in let s' = State.push_scope s (args @ locals)
                                      in let add = (fun state arg value -> State.update arg value state)
                                      in let s'' = List.fold_left2 add s' args args_values
                                      in let (s', i', o') = eval env (s'', i, o) body
                                      in (State.drop_scope s' s, i', o')

    let negate e = Expr.Binop ("-", Expr.Const 1, e)
                                
    (* Statement parser *)
     ostap (
      expr: !(Expr.parse);

      read:    "read" "(" x:IDENT ")"                   {Read x};
      write:   "write" "(" e:expr ")"                   {Write e};
      assign:  x:IDENT ":=" e:expr                      {Assign (x, e)};
      skip:    "skip"                                   {Skip};
      if_stmt: "if" e:expr "then" s1:stmt s2:else_stmt  {If (e, s1, s2)};

      else_stmt: 
          "fi"                                          {Skip}
        | "else" s2:stmt "fi"                           {s2}
        | "elif" e:expr "then" s1:stmt s2:else_stmt     {If (e, s1, s2)};

      while_stmt:  "while" e:expr "do" s:stmt "od"      {While (e, s)};
      repeat_stmt: "repeat" s:stmt "until" e:expr       {Seq (s, While (negate e, s))};
      for_stmt:    "for" s1:stmt "," e:expr "," s2:stmt "do" s3:stmt "od"
                                                        {Seq (s1, While (e, Seq (s3, s2)))};

      call: fun_name:IDENT "(" args:!(Util.list0By)[ostap (",")][Expr.parse] ")" { Call (fun_name, args) };

      simple_stmt: assign | read | write | skip | if_stmt | while_stmt | repeat_stmt | for_stmt | call;

      stmt: <x::xs> :!(Util.listBy)[ostap (";")][simple_stmt] {List.fold_left (fun s1 s2 -> Seq (s1, s2)) x xs};
      parse: stmt
    )  

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (  
      locals: l:!(ostap("local" names:(!(Util.listBy) [ostap (",")] [ostap(IDENT)]) {names}))? 
          {match l with | Some x -> x | None -> []};
      args: a:(!(Util.listBy) [ostap (",")] [ostap(IDENT)])?
          {match a with | Some x -> x | None -> []};
      def: "fun" name:IDENT "(" args:args ")" locals:locals "{" body:!(Stmt.stmt) "}" 
          {(name, (args, locals, body))};
      parse: def     
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
