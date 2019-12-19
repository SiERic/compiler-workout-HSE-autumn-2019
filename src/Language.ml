(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of bytes | Array of t array | Sexp of string * t list | Dict of (int * int) list (*with show*)

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> Bytes.to_string s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"


    let of_sexp s vs = Sexp (s, vs)
    let of_int     n = Int    n
    let of_string  s = String (Bytes.of_string s)
    let of_array   a = Array  a
    let of_dict    d = Dict d

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a
    let rec update_dict   d i x = match d with 
      | [] -> [(i, x)]
      | (key, value)::ds -> if (key = i) 
                            then (key, x)::ds
                            else (key, value)::(update_dict ds i x)

    let rec dict_get d i = match d with 
      | [] -> failwith "Unknown dict key"
      | (key, value)::ds -> if (key = i) 
                            then value
                            else dict_get ds i

    let string_val v =
      let buf      = Buffer.create 128 in
      let append s = Buffer.add_string buf s in
      let rec inner = function
      | Int    n    -> append (string_of_int n)
      | String s    -> append "\""; append @@ Bytes.to_string s; append "\""
      | Array  a    -> let n = Array.length a in
                       append "["; Array.iteri (fun i a -> (if i > 0 then append ", "); inner a) a; append "]"
      | Sexp (t, a) -> let n = List.length a in
                       append "`"; append t; (if n > 0 then (append " ("; List.iteri (fun i a -> (if i > 0 then append ", "); inner a) a; append ")"))
      in
      inner v;
      Bytes.of_string @@ Buffer.contents buf
                      
  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
                                     | Value.Array    a  -> a.(i)
                                     | Value.Sexp (tag, a) -> if (tag = "_dict")
                                                              then let rec kek xs = (match xs with 
                                                                | [] -> []
                                                                | x::y::xs -> (x, y)::(kek xs))
                                                                in Value.dict_get (kek a) j  
                                                              else List.nth a i
                               )
                    )         
    | ".length"     -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Sexp (_, a) -> List.length a | Value.Array a -> Array.length a | Value.String s -> Bytes.length s)))
    | ".array"      -> (st, i, o, Some (Value.of_array @@ Array.of_list args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))
    | ".stringval"  -> failwith "Not implemented yet"
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const     of int
    (* array              *) | Array     of t list
    (* string             *) | String    of string
    (* S-expressions      *) | Sexp      of string * t list
    (* variable           *) | Var       of string
    (* binary operator    *) | Binop     of string * t * t
    (* element extraction *) | Elem      of t * t
    (* length             *) | Length    of t
    (* string conversion  *) | StringVal of t
                             | Dict      of (int * int) list
    (* function call      *) | Call      of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option

    let bti   = function true -> 1 | _ -> 0
    let itb b = b <> 0

    let get x = match x with
      | Some x -> x
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expression, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
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
    
      let rec eval env ((st, i, o, r) as conf) expr = 
      match expr with
        | Const n            -> (st, i, o, Some (Value.of_int n))
        | Array xs           -> let (st', i', o', r') = eval_list env conf xs in 
                                Builtin.eval (st', i', o', r') r' ".array"
        | Dict d             -> (st, i, o, Some (Value.of_dict d))
        | String s           -> (st, i, o, Some (Value.of_string s))
        | Sexp (x, ps)       -> let (st', i', o', r') = eval_list env conf ps in 
                                (st', i', o', Some (Value.Sexp (x, r')))
        | Var   x            -> (st, i, o, Some (State.eval st x))
        | Binop (op, x, y)   -> let (st', i', o', r') = eval env (st, i, o, r) x in
                                let (st'', i'', o'', r'') = eval env (st', i', o', r') y in
                                (st'', i'', o'', Some (Value.of_int (to_func op (Value.to_int (get r')) (Value.to_int (get r'')))))
        | Elem (a, ind)      -> let (st', i', o', r') = eval env (st, i, o, r) a in 
                                let (st'', i'', o'', r'') = eval env (st', i', o', r') ind in
                                (match r' with 
                                  | Some (Dict d) -> (st'', i'', o'', Some (Value.of_int (Value.dict_get d (Value.to_int (get r'')))))
                                  | _      -> Builtin.eval (st'', i'', o'', r'') [get r'; get r''] ".elem")
        | Length a           -> let (st', i', o', r') = eval env (st, i, o, r) a in
                                Builtin.eval (st', i', o', r') [get r'] ".length"
        | Call (name, exprs) -> let args, conf = List.fold_right 
                                (fun expr (args, conf) -> let (st', i', o', r') = eval env conf expr in ((get r')::args, (st', i', o', r'))) 
                                exprs ([], conf) in
                                env#definition env name args conf
      and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
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
        a:(e:simple_expr es:(-"[" parse -"]")* {List.fold_left (fun a i -> Elem (a, i)) e es})
          l:("." %"length")? {match l with None -> a | Some _ -> Length a}
      | simple_expr;

      dict_elem: key:DECIMAL ":" value:DECIMAL {(key, value)};

      simple_expr:
        name:IDENT "(" args:!(Util.list0)[parse] ")" {Call (name, args)} 
      | n:DECIMAL                    {Const n}
      | -"(" parse -")"
      | c:CHAR                       {Const (Char.code c)}
      | "{" dict:!(Util.listBy)[ostap (";")][dict_elem] "}" {Dict dict}
      | "[" a:!(Util.list parse) "]" {Array a}
      | s:STRING                     {String (String.sub s 1 (String.length s - 2))}
      | x:IDENT                      {Var x}
      | "`" x:IDENT ps:(-"(" !(Util.list)[parse] -")")? 
                                     {Sexp (x, match ps with None -> [] | Some ps -> ps)}
    )    
  end
                    
(* Simple statements: syntax and semantics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (                                      
          parse: 
            "_"     {Wildcard}
          | x:IDENT {Ident x}
          | "`" x:IDENT ps:(-"(" !(Util.list)[parse] -")")? 
                    {Sexp (x, match ps with None -> [] | Some ps -> ps)}
        )
        let vars p = transform(t) (fun f -> object inherit [string list, _] @t[foldl] f method c_Ident s _ name = name::s end) [] p 
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update a.(i) v tl))
           | Value.Dict d                -> Value.Dict   (Value.update_dict d i (Value.to_int v))
           | Value.Sexp (tag, a)         -> if (tag = "_dict") 
                                            then let rec kek xs = (match xs with 
                                                                | [] -> []
                                                                | x::y::xs -> (Value.to_int x, Value.to_int y)::(kek xs))
                                                 in Value.Sexp ("_dict", List.flatten (List.map (fun (x, y) -> [Value.of_int x; Value.of_int y]) (Value.update_dict (kek a) i (Value.to_int v)))) 
                                            else failwith "keks" 
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec pattern_match p v st = 
      match p with 
       | Pattern.Wildcard     -> st
       | Pattern.Sexp (x, ps) -> 
          (match v with Value.Sexp (x', ps') when x = x' -> pattern_match_list ps ps' st | _ -> None)
       | Pattern.Ident x      -> (match st with None -> None | Some st -> Some (State.bind x v st))
       | _                    -> None

    and pattern_match_list ps xs st = 
      match ps, xs with
        | [], []       -> st
        | p::ps, x::xs -> pattern_match_list ps xs (pattern_match p x st)
        | _ -> None

    let rec eval env ((st, i, o, r) as conf) k stmt = 
      let (^) s1 s2 = if (s2 == Skip) then s1 else Seq (s1, s2) in 
      match stmt with
        | Assign (x, es, e) -> let (st', i', o', is) = Expr.eval_list env conf es in
                               let (st'', i'', o'', v) = Expr.eval env (st', i', o', None) e in
                               eval env (update st'' x (Expr.get v) is, i'', o'', None) Skip k
        | Seq (s1, s2)      -> eval env conf (s2 ^ k) s1
        | Skip              -> if (k == Skip) then conf else eval env conf Skip k
        | If (e, s1, s2)    -> let (st', i', o', r') = Expr.eval env conf e in 
                               if (Expr.itb (Value.to_int (Expr.get r')))
                               then eval env (st', i', o', None) k s1
                               else eval env (st', i', o', None) k s2
        | While (e, s)      -> let (st', i', o', r') = Expr.eval env conf e in
                               if (Expr.itb (Value.to_int (Expr.get r')))
                               then eval env (st', i', o', None) ((While (e, s)) ^ k) s 
                               else eval env (st', i', o', None) Skip k
        | Case (e, bs)      -> let (st', i', o', r') = Expr.eval env conf e in
                               let rec find_branch ((st, i, o, r) as conf) bs =
                                 (match bs with
                                  | b::bs -> 
                                    let (p, s) = b in
                                    let st' = pattern_match p (Expr.get r') (Some State.undefined) in
                                    (match st' with 
                                      | Some st' -> eval env (State.push st st' (Pattern.vars p), i, o, None) k (Seq (s, Leave))
                                      | None     -> find_branch conf bs)
                                  | _ -> (st, i, o, None))
                                 in find_branch (st', i', o', r') bs
        | Return e          -> (match e with
                                 | Some e -> Expr.eval env conf e
                                 | None   -> conf)
        | Call (name, args) -> eval env (Expr.eval env conf (Expr.Call (name, args))) Skip k
        | Leave             -> eval env (State.drop st, i, o, r) Skip k
           
    (* Statement parser *)
    ostap (                                      
      expr: !(Expr.parse);

      assign:  x:IDENT is:(-"[" expr -"]")* ":=" e:expr {Assign (x, is, e)};

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

      call: name:IDENT "(" args:!(Util.list0)[Expr.parse] ")" 
                                                        {Call (name, args)};
      return_some: "return" e:expr {Return Some e};
      return_none: "return"        {Return None};

      case: "case" e:expr "of" bs:!(Util.listBy)[ostap ("|")][ostap (!(Pattern.parse) -"->" parse)] "esac" 
                                                        {Case (e, bs)};

      simple_stmt: assign | skip | if_stmt | while_stmt | repeat_stmt | for_stmt | call | return_some | return_none | case;

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
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      = snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
