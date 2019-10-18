(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
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
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)              

    let bti   = function true -> 1 | _ -> 0
    let itb b = b <> 0

    let get x = match x with
      | Some x -> x
      | _ -> 0

    let to_func op =
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
    
    let rec eval env ((st, i, o, r) as conf) expr =      
      match expr with
      | Const n           -> (st, i, o, Some n)
      | Var   x           -> (st, i, o, Some (State.eval st x))
      | Binop (op, x, y)  -> let (st', i', o', r') = eval env (st, i, o, r) x in
                             let (st'', i'', o'', r'') = eval env (st', i', o', r') y in
                             (st'', i'', o'', Some (to_func op (get r') (get r'')))
      | Call (name, exprs) -> let eval_expr = (fun expr (args, conf) ->
                                               let (st', i', o', r') = eval env conf expr in ((get r')::args, (st', i', o', r'))) in
                              let args, conf = List.fold_right eval_expr exprs ([], conf) in
                              env#definition env name args conf 
         
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
      | name:IDENT "(" args:!(Util.list0By)[ostap (",")][parse] ")" {Call (name, args)} 
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt = 
      let (^) s1 s2 = if (s2 == Skip) then s1 else Seq (s1, s2) in 
      match stmt with
        | Skip              -> if (k == Skip) then conf else eval env conf Skip k
        | Assign (x, e)     -> let (st', i', o', r') = Expr.eval env conf e in
                               eval env (State.update x (Expr.get r') st', i', o', None) Skip k
        | Write e           -> let (st', i', o', r') = Expr.eval env conf e in 
                               eval env (st', i', o' @ [Expr.get r'], None) Skip k
        | Read x            -> let (z::i) = i in 
                               eval env (State.update x z st, i, o, None) Skip k
        | Seq (s1, s2)      -> eval env (st, i, o, r) (s2 ^ k) s1
        | If (e, s1, s2)    -> let (st', i', o', r') = Expr.eval env conf e in 
                               if (Expr.itb (Expr.get r'))
                               then eval env (st', i', o', None) k s1
                               else eval env (st', i', o', None) k s2
        | While (e, s)      -> let (st', i', o', r') = Expr.eval env conf e in
                               if (Expr.itb (Expr.get r'))
                               then eval env (st', i', o', None) ((While (e, s)) ^ k) s 
                               else eval env (st', i', o', None) Skip k
        | Call (name, args) -> eval env (Expr.eval env conf (Expr.Call (name, args))) Skip k
        | Return e          -> (match e with
                                 | Some e -> Expr.eval env conf e
                                 | None   -> conf)

         
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
      repeat_stmt: "repeat" s:stmt "until" e:expr       {Seq (s, While (Expr.Binop ("-", Expr.Const 1, e), s))};
      for_stmt:    "for" s1:stmt "," e:expr "," s2:stmt "do" s3:stmt "od"
                                                        {Seq (s1, While (e, Seq (s3, s2)))};

      call: name:IDENT "(" args:!(Util.list0By)[ostap (",")][Expr.parse] ")" { Call (name, args) };
      return: "return" e:expr? {Return e};

      simple_stmt: assign | read | write | skip | if_stmt | while_stmt | repeat_stmt | for_stmt | call | return;

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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
