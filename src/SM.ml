open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
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
      | BINOP op        -> 
        let (r :: l :: stack') = stack in 
        let int_l = Value.to_int l in
        let int_r = Value.to_int r in
        let res = Value.of_int (Expr.get_binop_function op int_l int_r) in
        (cstack, res :: stack', config)
      | CONST x         -> (cstack, Value.of_int x :: stack, config)
      | STRING s        -> (cstack, Value.of_string s :: stack, config)
      | SEXP (tag, cnt) -> 
        let (elems, stack') = split cnt stack in
        (cstack, Value.sexp tag elems :: stack', config)
      | LD var          -> 
        (cstack, State.eval state var :: stack, (state, input, output))
      | ST var          -> 
        let (x :: stack') = stack in 
        (
          cstack, 
          stack', 
          (State.update var x state, input, output)
        ) 
      | STA (var, cnt)  ->
        let (elems, (v :: stack')) = split cnt stack in
        (cstack, stack', (Stmt.update state var v elems, input, output))
      | _               -> failwith "Not implemented"
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
  let eval_visibility ins (cstack, stack, ((state, input, output) as c)) =
    match ins with
    | DROP           -> (cstack, tl stack, c)
    | DUP            -> (cstack, hd stack :: stack, c)
    | SWAP           -> 
      let (x :: y :: stack') = stack in
      (cstack, y :: x :: stack', c)
    | TAG tag        -> 
      let matched = match hd stack with
      | Value.Sexp (head_tag, _) when head_tag = tag -> 1
      | _                                            -> 0 
      in 
      (cstack, Value.of_int matched :: tl stack, c)
    | ENTER new_vars -> 
      (cstack, stack, (State.push state State.undefined new_vars, input, output))
    | LEAVE          -> (cstack, stack, (State.drop state, input, output))
    in
  match p with
  | []          -> c
  | (ins :: p') -> match ins with
    | DROP | DUP | SWAP | TAG _ | ENTER _ | LEAVE ->
      let c' = eval_visibility ins c in
      eval e c' p'
    | LABEL _ | JMP _ | CJMP _ -> 
      let (c', p'') = eval_labeled ins c p' in
      eval e c' p''
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
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse = function
  | Stmt.Pattern.Wildcard               -> [DROP]
  | Stmt.Pattern.Ident _                -> [DROP]
  | Stmt.Pattern.Sexp (p_tag, sub_pats) -> 
    let add_pat (acc, index) pat =
      (
        acc 
        @ [DUP; CONST index; CALL (".elem", 2, false)] 
        @ pattern lfalse pat
      ), index + 1 in
    let (res, _) = fold_left add_pat ([], 0) sub_pats in
    [DUP; TAG p_tag; CJMP ("z", lfalse)] @ res
  and bindings p = 
    let rec bind = function
    | Stmt.Pattern.Wildcard               -> [DROP]
    | Stmt.Pattern.Ident _                -> [SWAP]
    | Stmt.Pattern.Sexp (_, sub_pats) -> 
      let add_pat (acc, index) pat =
      (
        acc
        @ [DUP; CONST index; CALL (".elem", 2, false)]
        @ bind pat
      ), index + 1 in
      let (res, _) = fold_left add_pat ([], 0) sub_pats in
      res @ [DROP]
    in 
    bind p @ [ENTER (Stmt.Pattern.vars p)]
  and expr = 
  (
    function
    | Expr.Const c           -> [CONST c]
    | Expr.String s          -> [STRING s]
    | Expr.Array a           -> call ".array" a false
    | Expr.Elem (e, idx)     -> call ".elem" [e; idx] false
    | Expr.Length e          -> call ".length" [e] false
    | Expr.Var x             -> [LD x]
    | Expr.Binop (op, l, r)  -> expr l @ expr r @ [BINOP op]
    | Expr.Call (name, args) -> call name args false
    | Expr.Sexp (tag, exprs) -> 
      (concat @@ map expr exprs) @ [SEXP (tag, length exprs)]
  ) in
  let rec compile_stmt l env = 
  (
    function
    | Stmt.Assign (var, [], e) -> (env, false, expr e @ [ST var])
    | Stmt.Assign (var, idxs, e) -> 
      (
        env, 
        false, 
        expr e @ (concat @@ rev @@ map expr idxs) @ [STA (var, length idxs)]
      )
    | Stmt.Seq (st1, st2)        -> 
      let (env', _, c1) = compile_stmt l env st1 in
      let (env'', _, c2) = compile_stmt l env st2 in
      (env'', false, c1 @ c2)
    | Stmt.Skip                  -> (env, false, [])
    | Stmt.If (cond, th, el)     -> 
      let (else_label, env') = env#get_label in
      let (end_label, env'') = env'#get_label in
      let (env3, _, c_th) = compile_stmt l env'' th in
      let (env4, _, c_el) = compile_stmt l env3 el in
      (
        env4, 
        false, 
        expr cond @ [CJMP ("z", else_label)] @ c_th @ 
        [JMP end_label; LABEL else_label] @ c_el @ [LABEL end_label]
      )
    | Stmt.While (cond, body)    ->
      let (begin_label, env') = env#get_label in
      let (end_label, env'') = env'#get_label in
      let (env3, _, c_body) = compile_stmt l env'' body in
      (
        env3, 
        false, 
        [LABEL begin_label] @ expr cond @ [CJMP ("z", end_label)] @ 
        c_body @ [JMP begin_label; LABEL end_label]
      )
    | Stmt.Repeat (body, cond)   ->
      let (begin_label, env') = env#get_label in
      let (env'', _, c_body) = compile_stmt l env' body in
      (
        env'',
        false, 
        [LABEL begin_label] @ c_body @ expr cond @ [CJMP ("z", begin_label)]
      )
    | Stmt.Call (name, args)     -> (env, false, call name args true)
    | Stmt.Leave                 -> (env, false, [LEAVE])
    | Stmt.Return optional_val   -> 
      (
        env, 
        false, 
        match optional_val with
        | Some e -> expr e @ [RET true]
        | _      -> [RET false]
      ) 
    | Stmt.Case (e, cases)       ->
      let rec compile_pat env label is_first end_label = 
      (
        function
        | []                     -> (env, [])
        | ((pat, body) :: pats') ->
          let (env', _, c_body) = compile_stmt l env body in
          let (lfalse, env) = env#get_label in
          let prefix = if is_first then [] else [LABEL label] in
          let (env'', c_tail) = compile_pat env' lfalse false end_label pats' in
          (
            env'', 
            prefix @ pattern lfalse pat @ bindings pat 
            @ c_body @ [LEAVE; JMP end_label] @ c_tail
          )
      ) in
      let (end_label, env') = env#get_label in
      let (env'', c_cases) = compile_pat env' "" true end_label cases in
      (env'', false, expr e @ c_cases @ [LABEL end_label])
  ) in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 