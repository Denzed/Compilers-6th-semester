(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Opening a library for list operations *)
open List
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty = 
      let undefined s = failwith ("variable " ^ s ^ " undefined in current scope") in
      {
        g     = undefined;
        l     = undefined;
        scope = []
      }

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = 
      let update_inner x v s = fun var -> if var = x then v else s var in
      if mem x s.scope then { 
        s with l = update_inner x v s.l
      } else { 
        s with g = update_inner x v s.g
      }
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {
        empty with g = st.g; scope = xs
      }

    (* Drops a scope *)
    let leave st st' = { 
        st' with g = st.g
      }

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
    let bool_to_int b = if b then 1 else 0
    let int_to_bool i = if i == 0 then false else true
    let get_binop_function binop =
      fun l r ->
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
            | _     -> failwith "Wrong binary operator"

    let rec eval s e = 
      match e with
        | Const x          -> x
        | Var v            -> State.eval s v
        | Binop (op, l, r) -> get_binop_function op (eval s l) (eval s r) 
      
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (
      parse:          !(let make_ops = List.map (fun op -> ostap($(op)), fun l r -> Binop (op, l, r)) in 
                        Ostap.Util.expr
                        (fun x -> x)
                        [|
                          `Lefta, make_ops ["!!"];
                          `Lefta, make_ops ["&&"];
                          `Nona,  make_ops ["=="; "!="; "<="; "<"; ">="; ">"];
                          `Lefta, make_ops ["+"; "-"];
                          `Lefta, make_ops ["*"; "/"; "%"];
                        |]
                        atomic_expr
                      );
      const:          x:DECIMAL { Const x };
      var:            v:IDENT { Var v };
      sub_expr:       -"(" parse -")";
      atomic_expr:    const | var | sub_expr
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read    of string
    (* write the value of an expression *) | Write   of Expr.t
    (* assignment                       *) | Assign  of string * Expr.t
    (* composition                      *) | Seq     of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((state, input, output) as c) st = 
      match st with
        | Read var             -> 
            let (x :: input') = input in
            (State.update var x state, input', output)
        | Write expr           -> (state, input, output @ [Expr.eval state expr])
        | Assign (var, expr)   -> (
            State.update var (Expr.eval state expr) state,
            input,
            output
          )
        | Seq (st1, st2)       -> eval env (eval env c st1) st2
        | Skip                 -> c
        | If (cond, th, el)    -> eval env c (
            if Expr.int_to_bool (Expr.eval state cond) then th else el
          ) 
        | While (cond, body)   -> if Expr.int_to_bool (Expr.eval state cond)
          then eval env (eval env c body) st 
          else c
        | Repeat (body, cond) -> 
          let c' = eval env c body in
          let (state', _, _) = c' in
          if Expr.int_to_bool (Expr.eval state' cond)
            then c'
            else eval env c' st
        | Call (func_name, args) -> 
          let (arg_names, local_names, body) = assoc func_name env in
          let evaluated_args = map (Expr.eval state) args in
          let state_inner = fold_left (fun st (a, v) -> State.update a v st) (State.enter state (arg_names @ local_names)) (combine arg_names evaluated_args) in
          let (state', input', output') = eval env (state_inner, input, output) body in
          (State.leave state' state, input', output')

    (* Statement parser *)
    let st_or_skip st = match st with None -> Skip | Some st -> st
    ostap (
      parse:        st:!(Ostap.Util.expr
                      (fun x -> x)
                      [|
                        `Righta, [ostap(";"), fun l r -> Seq (l, r)]
                      |]
                      atomic_stmt
                    )? { st_or_skip st };
      expr:         !(Expr.parse);
      read:         -"read" -"(" x:IDENT -")" { Read x };
      write:        -"write" -"(" x:expr -")" { Write x };
      assign:       x:IDENT -":=" y:expr { Assign (x, y) };
      if_then:      -"then" parse;
      _if_else:     -"elif" cond:expr th:if_then el:if_else { If (cond, th, el) } | -"else" parse;
      if_else:      el:_if_else? { st_or_skip el };
      _if:          -"if" cond:expr th:if_then el:if_else -"fi" { If (cond, th, el) };
      _while:       -"while" cond:expr -"do" body:parse -"od" { While (cond, body) };
      do_while:     -"repeat" body:parse -"until" cond:expr { Repeat (body, cond) };
      _for:         -"for" init:parse -"," cond:expr -"," step:parse -"do" body:parse -"od" { Seq (init, While (cond, Seq (body, step))) };
      skip:         "skip" { Skip };
      call:         func:IDENT -"(" args:!(Expr.parse)* -")" { Call(func, args) };
      atomic_stmt:  read | write | assign | skip | _if | _while | do_while | _for | call
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: -"fun" name:IDENT -"(" args:IDENT* -")" locals:!(ostap(-"local" IDENT+))? -"{" body:!(Stmt.parse) -"}" { 
        (
          name, 
          (
            args, 
            (match locals with None -> [] | Some locals -> locals), 
            body
          )
        ) 
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
  let (_, _, o) = Stmt.eval defs (State.empty, i, []) body in
  o
                                   
(* Top-level parser *)
let parse = ostap(
  defs:!(Definition.parse)* body:!(Stmt.parse) {
    (defs, body) 
  }
)
