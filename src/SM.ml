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
        (cstack, Value.sexp tag (rev elems) :: stack', config)
      | LD var          -> 
        (cstack, State.eval state var :: stack, config)
      | ST var          -> 
        let (x :: stack') = stack in 
        (
          cstack, 
          stack', 
          (State.update var x state, input, output)
        ) 
      | STA (var, cnt)  ->
        let ((v :: idxs), stack') = split (cnt + 1) stack in
        (cstack, stack', (Stmt.update state var v (rev idxs), input, output))
      | _               -> failwith "Not a basic instruction"
      in
  let eval_labeled ins c p =
    match ins with
    | LABEL l        -> (c, p)
    | JMP l          -> (c, e#labeled l)
    | CJMP (cond, l) -> 
      let (cstack, x :: stack', config) = c in 
      let cond_val = Expr.int_to_bool (Value.to_int x) in
      ((cstack, stack', config), if cond_val == (cond == "nz") then e#labeled l else p)
    | _              -> failwith "Not a labeled instruction"
    in
  let eval_control_flow ins e ((cstack, stack, ((state, input, output) as c)) as conf) p = 
    match ins with
    | BEGIN (_, arg_names, local_names) -> 
      let (arg_vals, stack') = split (length arg_names) stack in
      let state' = State.enter state (arg_names @ local_names) in
      let state'' = fold_right2 State.update (rev arg_names) arg_vals state' in
      eval e (cstack, stack', (state'', input, output)) p
    | END | RET _                               -> 
      (
        match cstack with
        | []                        -> conf (* END of main *)
        | ((p', state') :: cstack') -> 
          eval e (cstack', stack, (State.leave state state', input, output)) p'
      )
    | CALL (func, n_args, is_procedure)         -> 
      if e#is_label func 
        then eval e ((p, state) :: cstack, stack, c) (e#labeled func)
        else eval e (e#builtin conf func n_args is_procedure) p
    | _                                         -> failwith "Not a control flow instruction"
    in
  let eval_scoped ins (cstack, stack, ((state, input, output) as c)) =
    match ins with
    | DROP           -> (cstack, tl stack, c)
    | DUP            -> (cstack, hd stack :: stack, c)
    | SWAP           -> 
      let (x :: y :: stack') = stack in
      (cstack, y :: x :: stack', c)
    | TAG tag        -> 
      let (sexp :: stack') = stack in
      let has_matched = match sexp with
      | Value.Sexp (head_tag, _) -> Expr.bool_to_int (head_tag = tag)
      | _                        -> 0 
      in 
      (cstack, Value.of_int has_matched :: stack', c)
    | ENTER new_vars -> 
      let (new_vals, stack') = split (length new_vars) stack in
      let add_val state var v = State.bind var v state in
      let state' = List.fold_left2 add_val State.undefined new_vars new_vals in
      (
        cstack, 
        stack', 
        (Language.State.push state state' new_vars, input, output)
      )
    | LEAVE          -> 
      (cstack, stack, (State.drop state, input, output))
    | _              -> failwith "Not a scope control instruction"
    in
  match p with
  | []          -> c
  | (ins :: p') -> match ins with
    | DROP | DUP | SWAP | TAG _ | ENTER _ | LEAVE ->
      let c' = eval_scoped ins c in
      eval e c' p'
    | LABEL _ | JMP _ | CJMP _ -> 
      let (c', p'') = eval_labeled ins c p' in
      eval e c' p''
    | BEGIN _ | END | CALL _ | RET _ -> eval_control_flow ins e c p'
    | BINOP _ | CONST _ | STRING _ 
    | SEXP _ | LD _ | ST _ | STA _   -> eval e (eval_normal ins c) p'

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
  let label s = if s.[0] = '.' then s else "L" ^ s in
  let not_sexp = function
    | Stmt.Pattern.Sexp _ -> false
    | _                   -> true 
  in
  let env =
    object
      val mutable ls = 0
      method new_label = ls <- (ls + 1); (label @@ string_of_int ls)
    end
  in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern pat ltrue lfalse = 
    (
      match pat with 
      | Stmt.Pattern.Wildcard             -> [DROP]
      | Stmt.Pattern.Ident _              -> [DROP]
      | Stmt.Pattern.Sexp (tag, sub_pats) ->
        let local_lfalse = env#new_label in
        let cnt = length sub_pats in
        let add_sub index pat = 
          [DUP] @ [CONST index] @ [CALL(".elem", 2, false)] 
            @ pattern pat ltrue local_lfalse
        in
        [DUP] @ [TAG tag] @ [CJMP ("z", lfalse)] 
          @ [DUP] @ [CALL(".length", 1, false)] @ [CONST(length sub_pats)] 
          @ [BINOP ("==")] @ [CJMP ("z", lfalse)] 
          @ (concat @@ mapi add_sub sub_pats) @ [DROP] @ [JMP ltrue] 
          @ (
            if for_all not_sexp sub_pats 
              then []
              else [LABEL local_lfalse] @ [DROP] @ [JMP lfalse]
          )
    )
  and load_nth_var pat n = 
    (
      match pat with
      | Stmt.Pattern.Wildcard           -> []
      | Stmt.Pattern.Ident _            -> []
      | Stmt.Pattern.Sexp (_, sub_pats) ->
        let rec skip_vars skipped pat_index (sub_pat :: sub_pats') = 
          let skipped' = skipped + Stmt.Pattern.cnt_vars sub_pat in
          if skipped' >= n 
            then [CONST pat_index] @ [CALL(".elem", 2, false)] 
              @ (load_nth_var sub_pat (n - skipped)) 
            else skip_vars skipped' (pat_index + 1) sub_pats'
        in
        skip_vars 0 0 sub_pats
    )
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
  let rec compile_stmt st = 
  (
    match st with
    | Stmt.Assign (var, idxs, e) -> 
      (
        match idxs with
        | [] -> expr e @ [ST var]
        | _  -> (concat @@ map expr idxs) @ expr e @ [STA (var, length idxs)]
      )
    | Stmt.Seq (st1, st2)        -> compile_stmt st1 @ compile_stmt st2
    | Stmt.Skip                  -> []
    | Stmt.If (cond, th, el)     -> 
      let else_label = env#new_label in
      let end_label  = env#new_label in
      expr cond @ [CJMP ("z", else_label)] 
        @ compile_stmt th @ [JMP end_label; LABEL else_label]
        @ compile_stmt el @ [LABEL end_label]
    | Stmt.While (cond, body)    ->
      let begin_label = env#new_label in
      let end_label   = env#new_label in
      [LABEL begin_label] @ expr cond @ [CJMP ("z", end_label)] 
        @ compile_stmt body @ [JMP begin_label; LABEL end_label]
    | Stmt.Repeat (body, cond)   ->
      let begin_label = env#new_label in
      [LABEL begin_label] @ compile_stmt body 
        @ expr cond @ [CJMP ("z", begin_label)]
    | Stmt.Call (name, args)     -> call name args true
    | Stmt.Return optional_val   -> 
      (
        match optional_val with
          | Some e -> expr e @ [RET true]
          | _      -> [RET false]
      )
    | Stmt.Leave                 -> [LEAVE]
    | Stmt.Case (matched, cases) ->
      let lend = env#new_label in
      let compile_case (pat, body) =
        let vars = Stmt.Pattern.vars pat in 
        let var_cnt = length vars in
        let ltrue = env#new_label in 
        let lunmatched = env#new_label in
        let helper i = [DUP] @ load_nth_var pat (i + 1) @ [SWAP] in
        [DUP] @ pattern pat ltrue lunmatched 
          @ (if not_sexp pat then [] else [LABEL ltrue])
          @ (concat @@ ListUtils.init var_cnt helper) 
          @ [DROP] @ [ENTER vars] @ compile_stmt body @ [LEAVE] @ [JMP lend] 
          @ if not_sexp pat then [] else [LABEL lunmatched] @ [DROP]
      in
      expr matched @ (concat @@ map compile_case cases) @ [LABEL lend]
  ) in
  let compile_def (name, (args, locals, stmt)) =
    let lend       = env#new_label in
    let name_label = label name in
    let code = compile_stmt stmt in
    [LABEL name_label; BEGIN (name_label, args, locals)] @
    code @
    [LABEL lend; END]
  in
  let def_code =
    List.fold_left
      (fun code (name, others) -> let code' = compile_def (name, others) in code'::code)
      []
      defs
  in
  let lend = env#new_label in
  let code = compile_stmt p in
  code @ [LABEL lend; END] @ (List.concat def_code) 
