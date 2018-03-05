(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
open List
    
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval s e = 
      let bool_to_int b = if b then 1 else 0 in
      let int_to_bool i = if i == 0 then false else true in
      let helper binop l r = 
        match binop with
          | "!!"  -> bool_to_int ((int_to_bool l) || (int_to_bool r))
          | "&&"  -> bool_to_int ((int_to_bool l) && (int_to_bool r))
          | "=="  -> bool_to_int (l == r)
          | "!="  -> bool_to_int (l != r)
          | "<"   -> bool_to_int (l < r)
          | "<="  -> bool_to_int (l <= r)
          | ">"   -> bool_to_int (l > r)
          | ">="  -> bool_to_int (l >= r)
          | "+"   -> l + r
          | "-"   -> l - r
          | "*"   -> l * r
          | "/"   -> l / r
          | "%"   -> l mod r
          | _     -> failwith "Wrong binary operator" in
      match e with
        | Const x          -> x
        | Var v            -> s v
        | Binop (op, l, r) -> helper op (eval s l) (eval s r) 


  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval c st = 
      let (state, input, output) = c in
      match st with
        | Read var           -> 
            let (x :: input') = input in
            ((fun y -> if y == var then x else state y), input', output)
        | Write expr         -> (state, input, Expr.eval state expr :: output)
        | Assign (var, expr) -> (
            (fun x -> if x == var then Expr.eval state expr else state x),
            input,
            output
          )
        | Seq (st1, st2)     -> eval (eval c st1) st2    
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
