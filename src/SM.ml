open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval e c p = 
  let eval_normal ins c = 
    let (cstack, stack, config) = c in
    let (state, input, output) = config in
    match ins with
      | BINOP op       -> 
        let (r :: l :: stack') = stack in 
        let int_l = Value.to_int l in
        let int_r = Value.to_int r in
        let res = Value.of_int (Expr.get_binop_function op int_l int_r) in
        (cstack, res :: stack', config)
      | CONST x        -> (cstack, Value.of_int x :: stack, config)
      | STRING s       -> (cstack, Value.of_string s :: stack, config)
      | LD var         -> 
        (cstack, State.eval state var :: stack, (state, input, output))
      | ST var         -> 
        let (x :: stack') = stack in 
        (
          cstack, 
          stack', 
          (State.update var x state, input, output)
        ) 
      | STA (var, cnt) ->
        let (elems, (v :: stack')) = split cnt stack in
        (cstack, stack', (Stmt.update state var v elems, input, output))
      | _              -> failwith "Not implemented"
      in
  let eval_labeled ins c p =
    match ins with
      | LABEL l        -> (c, p)
      | JMP l          -> (c, e#labeled l)
      | CJMP (cond, l) -> 
        let (cstack, x :: stack', config) = c in 
        let cond_val = Expr.int_to_bool (Value.to_int x) in
        ((cstack, stack', config), if cond_val == (cond == "nz") then e#labeled l else p)
      | _              -> failwith "Not implemented"
      in
  let eval_control_flow ins e ((cstack, stack, ((state, input, output) as c)) as conf) p = 
    match ins with
      | BEGIN (func_name, arg_names, local_names) -> 
        let set_arg arg ((x :: stack), state) = (stack, State.update arg x state) in
        let (stack', state') = fold_right set_arg arg_names (stack, State.enter state (arg_names @ local_names)) in
        eval e (cstack, stack', (state', input, output)) p
      | END | RET _                               -> 
        (
          match cstack with
            | []                 -> conf (* END of main *)
            | (frame :: cstack') -> 
              let (p', state') = frame in
              eval e (cstack', stack, (State.leave state state', input, output)) p'
        )
      | CALL (func, n_args, is_procedure)         -> 
        if e#is_label func 
          then eval e ((p, state) :: cstack, stack, c) (e#labeled func)
          else eval e (e#builtin conf func n_args is_procedure) p
      | _                                         -> failwith "Not implemented"
      in
  match p with
    | []          -> c
    | (ins :: p') -> match ins with
      | LABEL _ | JMP _ | CJMP _ -> 
        let (c'', p'') = eval_labeled ins c p' in
        eval e c'' p''
      | BEGIN _ | END | CALL _ | RET _ -> eval_control_flow ins e c p'
      | _                              -> eval e (eval_normal ins c) p'

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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine statement compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let labels = object 
  val mutable id = 0
  method get_new = 
    id <- (id + 1);
    "label" ^ string_of_int id
end 

let compile_st st = 
    let rec compile_expr expr = 
      match expr with
        | Expr.Const c           -> [CONST c]
        | Expr.String s          -> [STRING s]
        | Expr.Array a           -> 
          (concat @@ map compile_expr a) @ [CALL ("$array", length a, false)]
        | Expr.Elem (e, idxs)    -> 
          compile_expr e @ compile_expr idxs @ [CALL ("$elem", 2, false)]
        | Expr.Length e                   -> 
          compile_expr e @ [CALL ("$length", 1, false)]
        | Expr.Var x             -> [LD x]
        | Expr.Binop (op, l, r)  -> 
          compile_expr l @ compile_expr r @ [BINOP op]
        | Expr.Call (name, args) -> 
          (concat @@ map compile_expr args) @ [CALL (name, length args, false)] 
        | _                      -> failwith "Not implemented"
        in
    let rec compile_helper st =
      match st with
        | Stmt.Assign (var, idxs, expr) -> 
          (
            match idxs with
            | [] -> compile_expr expr @ [ST var]
            | _  -> compile_expr expr 
              @ (rev @@ concat @@ map compile_expr idxs) 
              @ [STA (var, length idxs)]
          )
        | Stmt.Seq (st1, st2)           -> 
          compile_helper st1 @ compile_helper st2
        | Stmt.Skip                     -> []
        | Stmt.If (cond, th, el)        -> 
          let else_label = labels#get_new in
          let end_label  = labels#get_new in
          compile_expr cond @ 
          [CJMP ("z", else_label)] @ compile_helper th @ 
          [JMP end_label; LABEL else_label] @ compile_helper el @ [LABEL end_label]
        | Stmt.While (cond, body)       ->
          let begin_label = labels#get_new in
          let end_label   = labels#get_new in
          [LABEL begin_label] @ compile_expr cond @ [CJMP ("z", end_label)] @ 
          compile_helper body @ [JMP begin_label; LABEL end_label]
        | Stmt.Repeat (body, cond)      ->
          let begin_label = labels#get_new in
          [LABEL begin_label] @ compile_helper body @ compile_expr cond @ [CJMP ("z", begin_label)]
        | Stmt.Call (name, args)        -> 
          concat (map compile_expr args) @ [CALL (name, length args, true)]
        | Stmt.Return optional_val      -> 
          (
            match optional_val with
              | Some expr -> compile_expr expr @ [RET true]
              | _         -> [RET false]
          ) in
    compile_helper st

(* Stack machine function definition compiler

     val compile_defs : Definition.t list -> prg

   Takes a list of Definition's and compiles them to stack machine language
*)
let compile_defs defs = 
  let compile_def (name, (args, locals, body)) = 
    [LABEL name; BEGIN (name, args, locals)] @ compile_st body @ [END] in
  let after_defs = labels#get_new in
  [JMP after_defs] @ concat (map compile_def defs) @ [LABEL after_defs]

(* Stack machine compiler

     val compile : Definition.t list * Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, st) = compile_defs defs @ compile_st st
