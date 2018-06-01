(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

module ListUtils =
  struct
    let init n ~f =
      if n < 0 then raise (Invalid_argument "init");
      let rec loop i accum =
        if i = 0 then accum
        else loop (i-1) (f (i-1) :: accum)
      in
      loop n []
  end

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = 
      ListUtils.init (List.length a) (fun j -> if j = i then x else List.nth a j)
  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
    | name       -> failwith ("no such builtin \"" ^ name ^ "\"")
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

           val eval : env -> config -> t -> int * config


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
        | Const x           -> (st, i, o, Some (Value.of_int x))
        | Var v             -> (st, i, o, Some (State.eval st v))
        | Binop (op, l, r)  -> 
          let ((st',  i',  o',  Some rl) as conf') = eval env conf  l in
          let  (st'', i'', o'', Some rr)           = eval env conf' r in
          let l_int = Value.to_int rl in
          let r_int = Value.to_int rr in
          (st'', i'', o'', Some (Value.of_int (get_binop_function op l_int r_int)))
        | Call (func, args) -> 
          let eval_arg arg_expr (conf, args) = 
            let ((_,  _,  _, Some r) as conf') = eval env conf arg_expr in
            (conf', (r :: args)) in
          let (conf', evaluated_args) = List.fold_right eval_arg args (conf, []) in
          env#definition env func evaluated_args conf'
        | Array l           ->
          let (st', i', o', r') = eval_list env conf l in
          Builtin.eval (st', i', o', None) r' ".array"
        | String s          -> (st, i, o, Some (Value.of_string s))
        | Sexp (tag, exprs) -> 
          let (st', i', o', values) = eval_list env conf exprs in
          (st', i', o', Some (Value.sexp tag values))
        | Elem (e, index_e) -> 
          let (st', i', o', Some index) = eval env conf index_e in
          let (st'', i'', o'', Some v) = eval env (st', i', o', None) e in
          Builtin.eval (st'', i'', o'', None) [v; index] ".elem"
        | Length e          -> 
          let (st', i', o', Some v) = eval env conf e in
          Builtin.eval (st', i', o', None) [v] ".length"
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
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
                        length_expr
                      );
      const:          x:DECIMAL { Const x };
      var:            v:IDENT { Var v };
      str:            s:STRING { String (String.sub s 1 (String.length s - 2)) };
      chr:            c:CHAR { Const (Char.code c) };
      arr:            "[" l:!(Ostap.Util.list0)[parse] "]" { Array l };
      sexp:           "`" tag:IDENT exprs:(-"(" !(Util.list)[parse] -")")? { 
                        Sexp (tag, match exprs with None -> [] | Some r -> r) 
                      };
      single_index:   -"[" parse -"]";
      indexed_expr:   e:atomic_expr indexers:single_index* { 
                        List.fold_left (fun b i -> Elem (b, i)) e indexers
                      };
      length_expr:    e:indexed_expr len:("." %"length")? { 
                        match len with None -> e | _ -> Length e 
                      };
      call:           func:IDENT -"(" args:!(Ostap.Util.list0)[parse] -")" { Call (func, args) };
      sub_expr:       -"(" parse -")";
      atomic_expr:    call | const | var | str | chr | arr | sub_expr | sexp
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse:      wildcard | sexp | identifier;
          wildcard:   "-" { Wildcard };
          sexp:       "`" tag:IDENT exprs:(-"(" !(Util.list)[parse] -")")? { 
            Sexp (tag, match exprs with None -> [] | Some r -> r) 
          };
          identifier: ident:IDENT { Ident ident }
        )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st
    
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
      | Case (e, cases)        ->
        let rec match_pat ((mapped_vars, vars) as frame) value = function
        | Pattern.Wildcard  -> Some frame
        | Pattern.Ident var -> Some (State.bind var value mapped_vars, (var :: vars))
        | Pattern.Sexp (p_tag, sub_pats) -> 
          (
            match value with
            | Value.Sexp (v_tag, sub_exprs) 
              when v_tag = p_tag && List.length sub_pats = List.length sub_exprs -> 
              let match_single maybe_frame (p, e) = (
                match maybe_frame with
                | Some f -> match_pat f e p
                | None   -> None
              ) in
              List.fold_left match_single (Some frame) (List.combine sub_pats sub_exprs)
            | _                                                -> None
          ) in
        let (state', input', output', Some v) = Expr.eval env c e in
        let rec match_cases = function
        | []               -> failwith "no match found"
        | ((p, e) :: following) -> 
          (
            match (match_pat (State.undefined, []) v p) with
            | Some frame -> (frame, e)
            | None       -> match_cases following
          ) in
        let ((matched_values, matched_vars), body) = match_cases cases in
        let c' = ((State.push state' matched_values matched_vars), input', output', None) in
        eval env c' k (diamond body Leave)
      | Assign (var, i_e, e)   -> 
        let (state', input', output', i) = Expr.eval_list env c i_e in
        let (state'', input'', output'', Some v) = Expr.eval env (state', input', output', None) e in
        eval env (
          update state'' var v i,
          input'',
          output'', 
          None
        ) Skip k
      | Seq (st1, st2)         -> eval env c (diamond st2 k) st1
      | Skip                   -> 
        (
          match k with
            | Skip -> c
            | _    -> eval env c Skip k
        )
      | If (cond, th, el)      -> 
        let (state', input', output', Some r) = 
          Expr.eval env c cond in
        eval env (state', input', output', retval) k (if Expr.int_to_bool (Value.to_int r) then th else el)
      | While (cond, body)     -> 
        let (state', input', output', Some r) = 
          Expr.eval env c cond in
        if Expr.int_to_bool (Value.to_int r)
          then eval env (state', input', output', retval) (diamond st k) body
          else eval env (state', input', output', retval) Skip k
      | Repeat (body, cond)    -> 
        let cycle = While (Expr.Binop ("==", cond, Expr.Const 0), body) in
        eval env c (diamond cycle k) body
      | Call (func_name, args) -> 
        let c' = Expr.eval env c (Expr.Call (func_name, args)) in
        eval env c' Skip k
      | Return optional_val    ->
        (
          match optional_val with
            | Some expr -> Expr.eval env c expr
            | None      -> (state, input, output, None)
        )
      | Leave                  -> 
        eval env (State.drop state, input, output, None) Skip k

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
      assign:       x:IDENT indexers:(-"[" !(Expr.parse) -"]")* -":=" y:expr { Assign (x, indexers, y) };
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
      case_entry:   !(Pattern.parse) -"->" parse;
      case:         %"case" e:!(Expr.parse) 
                    %"of" entries:!(Util.listBy)[ostap("|")][case_entry] 
                    %"esac" { Case (e, entries) };
      atomic_stmt:  assign | skip | _if | _while | do_while | _for | call | case | return
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
        method definition env f args ((st, i, o, r) as conf) =
          try
            let xs, locs, s      =  snd @@ M.find f m in
            let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
            let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
            (State.leave st'' st, i', o', r')
          with Not_found -> Builtin.eval conf args f
      end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
