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
       an returns a pair: the return value for the call and the resulting configuration
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
            | _     -> failwith ("Wrong binary operator '" ^ binop ^ "'")

    let rec eval env ((st, i, o, r) as conf) expr = 
      match expr with
        | Const x           -> (st, i, o, Some x)
        | Var v             -> (st, i, o, Some (State.eval st v))
        | Binop (op, l, r)  -> 
          let ((st',  i',  o',  Some rl) as conf') = eval env conf  l in
          let  (st'', i'', o'', Some rr)           = eval env conf' r in
          (st'', i'', o'', Some (get_binop_function op rl rr))
        | Call (func, args) -> 
          let eval_arg arg_expr (conf, args) = 
            let ((_,  _,  _, Some r) as conf') = eval env conf arg_expr in
            (conf', (r :: args)) in
          let (conf', evaluated_args) = fold_right eval_arg args (conf, []) in
          env#definition env func evaluated_args conf'

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
      call:           func:IDENT -"(" args:!(Ostap.Util.list0)[parse] -")" { Call (func, args) };
      sub_expr:       -"(" parse -")";
      atomic_expr:    call | const | var | sub_expr
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((state, input, output, retval) as c) k st = 
      let diamond st k = 
        match k with
        | Skip -> st
        | _    -> Seq (st, k) in
      match st with
        | Read var             -> 
          let (x :: input') = input in
          eval env (State.update var x state, input', output, retval) Skip k
        | Write expr           -> 
          let (state', input', output', Some r) = 
            Expr.eval env c expr in
          eval env (state', input', output' @ [r], retval) Skip k
        | Assign (var, expr)   -> 
          let (state', input', output', Some r) = 
            Expr.eval env c expr in
          eval env (
            State.update var r state',
            input',
            output', 
            retval
          ) Skip k
        | Seq (st1, st2)       -> eval env c (diamond st2 k) st1
        | Skip                 -> 
          (
            match k with
              | Skip -> c
              | _    -> eval env c Skip k
          )
        | If (cond, th, el)    -> 
          let (state', input', output', Some r) = 
            Expr.eval env c cond in
          eval env (state', input', output', retval) k (if Expr.int_to_bool r then th else el)
        | While (cond, body)   -> 
          let (state', input', output', Some r) = 
            Expr.eval env c cond in
          if Expr.int_to_bool r 
            then eval env (state', input', output', retval) (diamond st k) body
            else eval env (state', input', output', retval) Skip k
        | Repeat (body, cond)  -> 
          let cycle = While (Expr.Binop ("==", cond, Expr.Const 0), body) in
          eval env c (diamond cycle k) body
        | Call (func_name, args) -> 
          let c' = Expr.eval env c (Expr.Call (func_name, args)) in
          eval env c' Skip k
        | Return optional_val ->
          (
            match optional_val with
              | Some expr -> Expr.eval env c expr
              | None      -> (state, input, output, None)
          )

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
      read:         %"read" -"(" x:IDENT -")" { Read x };
      write:        %"write" -"(" x:expr -")" { Write x };
      assign:       x:IDENT -":=" y:expr { Assign (x, y) };
      if_then:      %"then" parse;
      _if_else:     %"elif" cond:expr th:if_then el:if_else { If (cond, th, el) } | %"else" parse;
      if_else:      el:_if_else? { st_or_skip el };
      _if:          %"if" cond:expr th:if_then el:if_else %"fi" { If (cond, th, el) };
      _while:       %"while" cond:expr %"do" body:parse %"od" { While (cond, body) };
      do_while:     %"repeat" body:parse %"until" cond:expr { Repeat (body, cond) };
      _for:         %"for" init:parse -"," cond:expr -"," step:parse %"do" body:parse %"od" { Seq (init, While (cond, Seq (body, step))) };
      skip:         %"skip" { Skip };
      return:       %"return" value:expr? { Return value };
      call:         func:IDENT -"(" args:!(Ostap.Util.list0)[Expr.parse] -")" { Call (func, args) };
      atomic_stmt:  read | write | assign | skip | _if | _while | do_while | _for | call | return
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
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
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
