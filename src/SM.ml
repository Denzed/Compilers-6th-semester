open GT       
open Language
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
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let eval c p = 
    let eval_insn c ins = 
        let (stack, config) = c in
        let (state, input, output) = config in
        match ins with
            | BINOP op -> 
                let (r :: l :: stack') = stack in 
                (Language.Expr.get_binop_function op l r :: stack', config)
            | CONST x  -> (x :: stack, config)
            | READ     -> 
                let (x :: input') = input in 
                (x :: stack, (state, input', output))
            | WRITE    -> 
                let (x :: stack') = stack in 
                (stack', (state, input, output @ [x]))
            | LD var   -> (state var :: stack, (state, input, output))
            | ST var   -> 
                let (x :: stack') = stack in 
                (
                    stack', 
                    (Language.Expr.update var x state, input, output)
                ) in
    fold_left eval_insn c p

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile st = 
    let rec compile_expr expr = 
        match expr with
            | Language.Expr.Const c          -> [CONST c]
            | Language.Expr.Var x            -> [LD x]
            | Language.Expr.Binop (op, l, r) -> compile_expr l @ compile_expr r @ [BINOP op] in
    match st with
        | Language.Stmt.Read var           -> [READ; ST var]
        | Language.Stmt.Write expr         -> compile_expr expr @ [WRITE]
        | Language.Stmt.Assign (var, expr) -> compile_expr expr @ [ST var]
        | Language.Stmt.Seq (st1, st2)     -> compile st1 @ compile st2