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
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval e c p = 
  let eval_normal ins c = 
    let (cstack, stack, config) = c in
    let (state, input, output) = config in
    match ins with
      | BINOP op -> 
        let (r :: l :: stack') = stack in 
        (cstack, Language.Expr.get_binop_function op l r :: stack', config)
      | CONST x  -> (cstack, x :: stack, config)
      | READ     -> 
        let (x :: input') = input in 
        (cstack, x :: stack, (state, input', output))
      | WRITE    -> 
        let (x :: stack') = stack in 
        (cstack, stack', (state, input, output @ [x]))
      | LD var   -> (cstack, State.eval state var :: stack, (state, input, output))
      | ST var   -> 
        let (x :: stack') = stack in 
        (
          cstack, 
          stack', 
          (State.update var x state, input, output)
        ) in
  let eval_labeled ins c p =
    match ins with
      | LABEL l        -> (c, p)
      | JMP l          -> (c, e#labeled l)
      | CJMP (cond, l) -> 
        let (cstack, x :: stack', config) = c in 
        ((cstack, stack', config), if Expr.int_to_bool x == (cond == "nz") then e#labeled l else p) in
  let eval_control_flow ins e ((cstack, stack, ((state, input, output) as c)) as conf) p = 
    match ins with
      | BEGIN (arg_names, local_names) -> 
        let set_arg arg ((x :: stack), state) = (stack, State.update arg x state) in
        let (stack', state') = fold_right set_arg arg_names (stack, State.enter state (arg_names @ local_names)) in
        eval e (cstack, stack', (state', input, output)) p
      | END                            -> 
        (
          match cstack with
            | []                 -> conf (* END of main *)
            | (frame :: cstack') -> 
              let (p', state') = frame in
              eval e (cstack', stack, (State.leave state state', input, output)) p'
        )
      | CALL func                      -> 
        eval e ((p, state) :: cstack, stack, c) (e#labeled func) in
  match p with
    | []          -> c
    | (ins :: p') -> match ins with
      | LABEL _ | JMP _ | CJMP _ -> 
        let (c'', p'') = eval_labeled ins c p' in
        eval e c'' p''
      | BEGIN _ | END | CALL _   -> eval_control_flow ins e c p'
      | _                        -> eval e (eval_normal ins c) p'

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, st) = 
    let labels = object 
      val mutable id = 0
      method get_new = 
        id <- (id + 1);
        "label" ^ string_of_int id
    end in
    let rec compile_expr expr = 
        match expr with
            | Language.Expr.Const c          -> [CONST c]
            | Language.Expr.Var x            -> [LD x]
            | Language.Expr.Binop (op, l, r) -> compile_expr l @ compile_expr r @ [BINOP op] in
    let rec compile_helper st =
      match st with
          | Language.Stmt.Read var           -> [READ; ST var]
          | Language.Stmt.Write expr         -> compile_expr expr @ [WRITE]
          | Language.Stmt.Assign (var, expr) -> compile_expr expr @ [ST var]
          | Language.Stmt.Seq (st1, st2)     -> compile_helper st1 @ compile_helper st2
          | Language.Stmt.Skip               -> []
          | Language.Stmt.If (cond, th, el)  -> 
            let else_label = labels#get_new in
            let end_label  = labels#get_new in
            compile_expr cond @ 
            [CJMP ("z", else_label)] @ compile_helper th @ 
            [JMP end_label; LABEL else_label] @ compile_helper el @ [LABEL end_label]
          | Language.Stmt.While (cond, body) ->
            let begin_label = labels#get_new in
            let end_label   = labels#get_new in
            [LABEL begin_label] @ compile_expr cond @ [CJMP ("z", end_label)] @ 
            compile_helper body @ [JMP begin_label; LABEL end_label]
          | Language.Stmt.Repeat (body, cond) ->
            let begin_label = labels#get_new in
            [LABEL begin_label] @ compile_helper body @ compile_expr cond @ [CJMP ("z", begin_label)]
          | Language.Stmt.Call (name, args) -> concat (map compile_expr args) @ [CALL name] in
    let compile_def (name, (args, locals, body)) = 
      [LABEL name; BEGIN (args, locals)] @ compile_helper body @ [END] in
    compile_helper st @ [END] @ concat (map compile_def defs)
