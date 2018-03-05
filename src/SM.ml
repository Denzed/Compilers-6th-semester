open GT
open List
       
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
let eval c p = 
    let eval_binop binop l r = 
        let bool_to_int b = if b then 1 else 0 in
        let int_to_bool i = if i == 0 then false else true in
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
    let eval_insn c ins = 
        let (stack, config) = c in
        let (state, input, output) = config in
        match ins with
            | BINOP op -> 
                let (r :: l :: stack') = stack in 
                (eval_binop op l r :: stack', config)
            | CONST x  -> (x :: stack, config)
            | READ     -> 
                let (x :: input') = input in 
                (x :: stack, (state, input', output))
            | WRITE    -> 
                let (x :: stack') = stack in 
                (stack', (state, input, x :: output))
            | LD var   -> (state var :: stack, (state, input, output))
            | ST var   -> 
                let (x :: stack') = stack in 
                (
                    stack', 
                    (Syntax.Expr.update var x state, input, output)
                ) in
    fold_left eval_insn c p

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

let rec compile st = 
    let rec compile_expr expr = 
        match expr with
            | Syntax.Expr.Const c          -> [CONST c]
            | Syntax.Expr.Var x            -> [LD x]
            | Syntax.Expr.Binop (op, l, r) -> compile_expr l @ compile_expr r @ [BINOP op] in
    match st with
        | Syntax.Stmt.Read var           -> [READ; ST var]
        | Syntax.Stmt.Write expr         -> compile_expr expr @ [WRITE]
        | Syntax.Stmt.Assign (var, expr) -> compile_expr expr @ [ST var]
        | Syntax.Stmt.Seq (st1, st2)     -> compile st1 @ compile st2
