open List

(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string
                                                                            
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let compile env code = 
    let mov f t = match (f, t) with
      | (R _, _) -> [Mov (f, t)]
      | (_, R _) -> [Mov (f, t)]
      | _        -> [Mov (f, eax); Mov (eax, t)] 
    in
    let compile_insn c ins = 
        let (env, instrs) = c in
        match ins with
        | CONST x  -> 
          let (x_addr, env') = env#allocate in
          (env', instrs @ mov (L x) x_addr)
        | LD var   -> 
          let (stack_addr, env') = (env#global var)#allocate in
          (env', instrs @ mov (env#loc var) stack_addr)
        | ST var   -> 
          let (stack_addr, env') = (env#global var)#pop in
          (env', instrs @ mov stack_addr (env#loc var))
        | BINOP op -> 
          let to_bool x = [
            Binop ("^", eax, eax);
            Binop ("cmp", (L 0), x);
            Set ("ne", "%al");
            Mov (eax, x)
            ] in
          let do_binop op l r = mov r eax @ [Binop (op, l, eax)] @ mov eax r in
          let cmp suf l r = mov r edx @ [
            Binop ("^", eax, eax);
            Binop ("cmp", l, edx);
            Set (suf, "%al");
            Mov (eax, r)
            ] in
          let (l, r, env') = env#pop2 in
          let (stack_addr, env'') = env'#allocate in
            (
              env'',
              instrs @ (
                match op with
                | "!!" -> to_bool l @ to_bool r @ do_binop "!!" l r
                | "&&" -> to_bool l @ to_bool r @ do_binop "&&" l r
                | "==" -> cmp "e"  l r
                | "!=" -> cmp "ne" l r
                | "<=" -> cmp "le" l r
                | "<"  -> cmp "l"  l r
                | ">=" -> cmp "ge" l r
                | ">"  -> cmp "g"  l r
                | "+"  -> do_binop "+" l r
                | "-"  -> do_binop "-" l r
                | "*"  -> do_binop "*" l r
                | "/"  -> mov r eax @ [Cltd; IDiv l] @ mov eax r
                | "%"  -> mov r eax @ [Cltd; IDiv l] @ mov edx r
                | _ -> failwith "unexpected binary operator"
              ) @ mov r stack_addr
            )
        | LABEL l     -> 
          (env, instrs @ [Label l])
        | JMP l       -> 
          (env, instrs @ [Jmp l])
        | CJMP (c, l) -> 
          let (stack_addr, env') = env#pop in
          (env, instrs @ [Binop ("cmp", (L 0), stack_addr); CJmp (c, l)])
        | BEGIN (func_name, arg_names, local_names) ->
          let env = env#enter func_name arg_names local_names in
          (env, instrs @ [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ env#lsize), esp)])
        | END ->
          let def_end = [
            Label env#epilogue; 
            Mov (ebp, esp); 
            Pop ebp; 
            Ret; 
            Meta ("\t.set " ^ env#lsize ^ ", " ^ string_of_int (env#allocated * word_size))
          ] in
          (env, instrs @ def_end)
        | CALL (func_name, arg_count, is_procedure) ->
          let push_registers = map (fun reg -> Push reg) env#live_registers in
          let pop_registers = map (fun reg -> Pop reg) (rev env#live_registers) in 
          let rec repeat func times value = if times > 0
            then repeat func (times - 1) (func value)
            else value in
          let get_arg = fun (env, args) -> 
            let (arg, env') = env#pop in 
            (env', arg :: args) in
          let (env', rev_args) = repeat get_arg arg_count (env, []) in
          let args = rev rev_args in
          let push_args = map (fun arg -> Push arg) args in
          
          let (env'', get_returned) = if is_procedure 
            then (env', [])
            else 
              let (stack_addr, env'') = env'#allocate in
              (env'', [Mov (eax, stack_addr)]) in
          let func_call = push_registers @ 
              push_args @ 
              [Call func_name; Binop ("+", L (arg_count * word_size), esp)] @ 
              pop_registers @ 
              get_returned in
          (env'', instrs @ func_call)
        | RET has_value -> if has_value
          then 
            let (stack_addr, env') = env#pop in
            (env', instrs @ [Mov (stack_addr, eax); Jmp env#epilogue])
          else
            (env, instrs @ [Jmp env#epilogue])
        in
    fold_left compile_insn (env, []) code


(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
let make_assoc l = 
  let init n ~f =
  if n < 0 then raise (Invalid_argument "init");
  let rec loop i accum =
    if i = 0 then accum
    else loop (i-1) (f (i-1) :: accum)
  in
  loop n [] in
  List.combine l (init (List.length l) (fun x -> x))
                     
class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
                        
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
	let rec allocate' = function
	| []                                -> ebx     , 0
	| (S n)::_                          -> S (n+1) , n+2
	| (R n)::_ when n + 1 < num_of_regs -> R (n+1) , stack_slots
	| _                                 -> S 0     , 1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
      
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      (SM.compile_defs ds @ ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile_st stmt @ [END]))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
