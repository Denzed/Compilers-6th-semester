open GT       
       
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
let rec eval c p = 
    let bool_to_int b = if b then 1 else 0 in
    let int_to_bool i = if i == 0 then false else true in
    let eval_binop binop l r = 
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
    if length p == 0 then 
        c 
    else 
        let (stack, config@(state, input, output)) = c in
        let (ins :: p') = p in
        let c' = 
            match ins with
                | BINOP op -> let (l :: r :: rest) = stack in (eval_binop op l r :: rest, config)
                | CONST x  -> (x :: stack, config)
                | READ     -> let (x :: rest) = input in (x :: stack, (state, rest, output))
                | WRITE    -> let (x :: rest) = stack in (rest, (state, input, x :: output))
                | LD var   -> (state var :: rest, input, output)
                | ST var   -> let (x :: rest) = stack in (
                        rest, 
                        (fun y -> if y == var then x else state y, input, output)
                    ) in
        eval c' p'

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

let compile st = 
    let compile_expr expr = 
        match expr with
            | Const c          -> [CONST c]
            | Var x            -> [LD x]
            | Binop (op, l, r) -> compile_expr l @ compile_expr r @ [BINOP op] in
    match st with
        | Read var        -> [READ; ST var]
        | Write expr      -> compile_expr expr @ [WRITE]
        | Assign var expr -> compile_expr expr @ [ST var]
        | Seq (st1, st2)  -> compile st1 @ compile st2
